#!/usr/bin/env python3
"""
Daily refresh for the Dry Cargo Signal Terminal.

Sources
  1. Gmail (primary)  - shipping newsletters, read over IMAP with an app password.
  2. RSS   (backup)   - public feeds; many block GitHub's servers, so failures are expected.

Output
  Rewrites the block between /*SIGNALS_START*/ ... /*SIGNALS_END*/ and
  <!--STATUS_START--> ... <!--STATUS_END--> in index.html.

Privacy / copyright rules (deliberate):
  - Email links are personal tracking / unsubscribe links. They are NEVER published.
  - Email body text is used only to classify. Only the headline is published.

Environment
  GMAIL_USER           your Gmail address                          (GitHub secret)
  GMAIL_APP_PASSWORD   16-character Google app password            (GitHub secret)
  GMAIL_QUERY          optional Gmail search override              (GitHub variable)
"""
import email, email.policy, email.utils, html, imaplib, json, os, re, sys
import urllib.parse, urllib.request
from datetime import datetime, timezone, timedelta
from xml.etree import ElementTree as ET

PAGE       = "index.html"
KEEP_DAYS  = 7      # rolling window shown on the page
MAX_ITEMS  = 80
RSS_HOURS  = 36
MAX_EMAILS = 40

DEFAULT_GMAIL_QUERY = (
    "newer_than:2d {"
    "from:editorial.tradewindsnews.com "
    "from:editor@tradewindsnews.com "
    "from:lngglobal@ghost.io "
    "from:splash247.com "
    "from:lloydslist.com "
    "from:hellenicshippingnews.com"
    "}"
)

FEEDS = [
    ("Splash247",  "https://splash247.com/feed/"),
    ("Splash247",  "https://splash247.com/category/sector/dry-cargo/feed/"),
    ("TradeWinds", "https://services.tradewindsnews.com/api/feed/rss"),
    ("Hellenic",   "https://www.hellenicshippingnews.com/feed/"),
]
UA = ("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0 Safari/537.36")

# --------------------------------------------------------------------------
# Stopford rules (unchanged from the original workflow)
# --------------------------------------------------------------------------
SIG = [
  (-5,"supply",r"\borderbook\b","Orderbook movement — the most reliable forward supply indicator. Fixes tonnage arriving years ahead regardless of what rates do next."),
  (-4,"supply",r"\b(orders?|ordered|ordering|contracted|newbuild\w*)\b.{0,60}\b(bulk\w*|capesize|newcastlemax|kamsarmax|panamax|supramax|ultramax|handysize)","New bulker tonnage contracted. Adds to a fleet already carrying an elevated orderbook; delivery typically two to three years out."),
  (-3,"supply",r"\b(deliver\w+|handover|christen\w+)\b.{0,50}\b(bulk\w*|capesize|newcastlemax|kamsarmax|ultramax)","Tonnage entering service now. Immediate addition to effective supply."),
  (+5,"supply",r"\b(scrap\w+|demolit\w+|recycl\w+|beach\w+)\b","Tonnage leaving the fleet. Demolition has been near zero, so any pickup matters more than most headlines — it is the mechanism that clears a surplus."),
  (+4,"supply",r"\b(laid.?up|lay.?up|cold.?stack\w*)","Tonnage withdrawn from trading. Reduces effective supply without permanent removal."),
  (+3,"supply",r"\b(detain\w+|arrest\w+|banned|blacklist\w+|sanction\w+)\b.{0,50}\b(vessel|ship|tanker|bulk\w*|fleet)","Tonnage removed from compliant trade. Shrinks the available pool."),
  (+5,"cost",  r"\b(red sea|bab.?el.?mandeb|suez|hormuz|panama canal)\b","Chokepoint disruption reroutes voyages and absorbs capacity without any ship leaving the fleet. CHECK DIRECTION — reopening reverses this and expands effective supply."),
  (+4,"cost",  r"\b(congest\w+|queue\w*|berth delay|waiting time|port delay)","Congestion immobilises tonnage. Directly reduces effective supply while it lasts."),
  (+3,"cost",  r"\b(slow.?steam\w*|speed reduction)","Reduced steaming speed withdraws tonne-mile capacity fleet-wide with no change in ship count."),
  (+3,"cost",  r"\b(bunker|vlsfo|hsfo|lsmgo|fuel oil)\b.{0,50}\b(tight|short\w*|scarc\w+|lead time|spike|surge|rally|rise)","Fuel scarcity or cost spike changes optimal steaming speed and forces earlier stems. Slower fleet, less effective supply."),
  (+4,"demand",r"\b(iron ore|coking coal|thermal coal|bauxite|grain|soybean)\b.{0,60}\b(export|import|shipment|volume|demand|surge|record)","Commodity flow change feeding directly into tonne-mile demand."),
  (+3,"demand",r"\b(tonne.?mile|ton.?mile)\b","Direct tonne-mile measure — the actual unit of dry bulk demand."),
  (-4,"demand",r"\b(export ban|import ban|tariff|quota|embargo)\b","Trade restriction removes or reroutes cargo. Check direction — a reroute can lengthen voyages and add tonne-miles."),
]
NOISE = [
  ("NO-CAPACITY-PATH", r"\b(launch\w*|unveil\w*|debut\w*|platform|software|start.?up|AI\b|artificial intelligence|machine learning|digital\w*)","Technology or vendor announcement. Adds, removes and immobilises exactly zero ships."),
  ("NO-CAPACITY-PATH", r"\b(appoint\w+|promot\w+|steps? down|resign\w+|obituar\w+|award\w*|anniversar\w+|conference|webinar|summit|forum)","People, prizes or events. No capacity path."),
  ("NO-CAPACITY-PATH", r"\b(partner\w+|team\w+ up|collaborat\w+|memorandum|MoU)","Commercial partnership. Announces intent, not tonnage."),
  ("WRONG-SECTOR",     r"\b(offshore wind|subsea|seismic|drilling rig|jack.?up|FPSO|cruise|ferry|yacht)","Wrong sector. No dry bulk read-across."),
  ("SINGLE-EVENT",     r"\b(aground|grounded|collision|fire aboard|rescued|refloat\w+|man overboard)","Single-vessel incident. Reclassifies only if it repeats or closes a route for days."),
  ("ALREADY-IN-PRICE", r"\b(BDI|baltic dry index)\b.{0,40}\b(up|down|rose|fell|gained|slipped|point)","The daily index tick — output of the system reported back as though it were an input."),
]
REL = re.compile(r"bulk|bulker|capesize|newcastlemax|kamsarmax|panamax|supramax|ultramax|handysize|dry\s*cargo|iron\s*ore|coal|grain|bauxite|BDI|baltic|freight|charter|tonne.?mile|orderbook|newbuild|shipyard|deliver|scrap|demolit|recycl|bunker|VLSFO|HSFO|fuel\s*oil|congestion|red\s*sea|suez|hormuz|panama\s*canal|houthi|sanction|tariff", re.I)

BOILER = re.compile(r"unsubscribe|newsletter|sign(ed)? up|privacy|view (it )?in (your )?browser|advertis|"
                    r"all newsletters|facebook|linkedin|twitter|preferences|copyright|©|editor-in-chief|"
                    r"you are receiving|manage (your )?subscription|forward to a friend", re.I)
LINK_RX = re.compile(r"\(\s*https?://\S+\s*\)|\[?\s*https?://\S+\s*\]?")

log_lines = []
def log(msg):
    print(msg, flush=True)
    log_lines.append(msg)

def clean(s):
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", s or ""))).strip()

def key(title):
    return re.sub(r"[^a-z0-9]", "", title.lower())[:70]

# --------------------------------------------------------------------------
# Gmail
# --------------------------------------------------------------------------
def publisher(addr, name):
    a = (addr or "").lower()
    for dom, label in (("tradewindsnews", "TradeWinds"), ("lngglobal", "LNG Global"),
                       ("splash247", "Splash247"), ("lloydslist", "Lloyd's List"),
                       ("hellenicshippingnews", "Hellenic Shipping News")):
        if dom in a:
            return label
    return (name or a.split("@")[-1] or "Email").strip()

def html_to_text(h):
    h = re.sub(r"(?is)<(script|style|head)[^>]*>.*?</\1>", " ", h)
    h = re.sub(r"(?is)<a\b[^>]*>(.*?)</a>", r"\n\n\1\n( link )\n\n", h)
    h = re.sub(r"(?i)<br\s*/?>|</(p|div|tr|td|h\d|li|table)>", "\n\n", h)
    h = re.sub(r"<[^>]+>", " ", h)
    return html.unescape(h)

def first_sentence(p, cap=170):
    s = re.split(r"(?<=[.!?])\s+(?=[A-Z\"“])", p, maxsplit=1)[0].strip()
    if len(s) > cap:
        s = s[:cap].rsplit(" ", 1)[0] + "…"
    return s

def items_from_message(msg):
    subject = clean(str(msg.get("subject", "")))
    name, addr = email.utils.parseaddr(str(msg.get("from", "")))
    src = publisher(addr, name)
    try:
        when = email.utils.parsedate_to_datetime(str(msg.get("date")))
        if when.tzinfo is None:
            when = when.replace(tzinfo=timezone.utc)
    except Exception:
        when = datetime.now(timezone.utc)

    text = ""
    part = msg.get_body(preferencelist=("plain",))
    if part is not None:
        try: text = part.get_content()
        except Exception: text = ""
    if not text.strip():
        part = msg.get_body(preferencelist=("html",))
        if part is not None:
            try: text = html_to_text(part.get_content())
            except Exception: text = ""

    paras = [p for p in re.split(r"\n\s*\n", text)]
    out, lead = [], ""
    for i, raw in enumerate(paras):
        p = clean(raw)
        if not p:
            continue
        body = clean(LINK_RX.sub(" ", p)).replace("( link )", "").strip()
        body = re.sub(r"\s*Click here to read\.?\s*$", "", body, flags=re.I).strip()
        if not lead and len(body) > 60 and not BOILER.search(body):
            lead = body
        nxt = clean(paras[i + 1]) if i + 1 < len(paras) else ""
        has_link = bool(LINK_RX.search(p)) or "( link )" in p or nxt.startswith("( http") or nxt == "( link )"
        if has_link and 40 <= len(body) <= 450 and not BOILER.search(body):
            out.append({"t": first_sentence(body), "s": body[:450], "w": when, "src": src, "via": "email"})

    if subject and not BOILER.search(subject):
        out.insert(0, {"t": subject[:170], "s": lead[:450], "w": when, "src": src, "via": "email"})
    return out

def find_all_mail(M):
    typ, boxes = M.list()
    for b in boxes or []:
        s = b.decode("utf-8", "replace")
        if "\\All" in s:
            m = re.search(r'"([^"]+)"\s*$', s) or re.search(r"(\S+)\s*$", s)
            if m:
                return m.group(1)
    return "INBOX"

def gmail_items():
    user = os.environ.get("GMAIL_USER", "").strip()
    pw   = os.environ.get("GMAIL_APP_PASSWORD", "").replace(" ", "").strip()
    if not user or not pw:
        return [], "GMAIL NOT CONFIGURED", "GMAIL_USER / GMAIL_APP_PASSWORD secrets are not set."
    query = (os.environ.get("GMAIL_QUERY", "").strip() or DEFAULT_GMAIL_QUERY).replace('"', "")
    try:
        M = imaplib.IMAP4_SSL("imap.gmail.com", 993, timeout=60)
        M.login(user, pw)
    except Exception as e:
        return [], "GMAIL LOGIN FAILED", "IMAP login failed (%s). Check the app password and that 2-Step Verification is on." % type(e).__name__
    try:
        box = find_all_mail(M)
        M.select('"%s"' % box, readonly=True)
        typ, data = M.search(None, "X-GM-RAW", '"%s"' % query)
        ids = (data[0] or b"").split()[-MAX_EMAILS:]
        log("   OK   %-3d emails  Gmail [%s]  query: %s" % (len(ids), box, query))
        items = []
        for num in ids:
            typ, parts = M.fetch(num, "(BODY.PEEK[])")   # PEEK = do not mark as read
            raw = next((p[1] for p in parts if isinstance(p, tuple)), None)
            if not raw:
                continue
            msg = email.message_from_bytes(raw, policy=email.policy.default)
            got = items_from_message(msg)
            log("        %-3d items  %s — %s" % (len(got), publisher(*reversed(email.utils.parseaddr(str(msg.get('from',''))))), clean(str(msg.get('subject','')))[:70]))
            items.extend(got)
        return items, "GMAIL OK (%d)" % len(ids), None
    except Exception as e:
        return [], "GMAIL ERROR", "Gmail read failed: %s: %s" % (type(e).__name__, e)
    finally:
        try: M.logout()
        except Exception: pass

# --------------------------------------------------------------------------
# RSS (best effort)
# --------------------------------------------------------------------------
def parse_dt(s):
    if not s:
        return None
    try:
        d = email.utils.parsedate_to_datetime(s)
        return d if d.tzinfo else d.replace(tzinfo=timezone.utc)
    except Exception:
        pass
    try:
        return datetime.fromisoformat(s.strip().replace("Z", "+00:00"))
    except Exception:
        return None

def rss_items():
    cutoff = datetime.now(timezone.utc) - timedelta(hours=RSS_HOURS)
    items, ok = [], 0
    for src, url in FEEDS:
        try:
            rq = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/rss+xml, application/xml;q=0.9, */*;q=0.8"})
            root = ET.fromstring(urllib.request.urlopen(rq, timeout=30).read())
            ns = {"a": "http://www.w3.org/2005/Atom"}
            got = []
            for n in root.findall(".//item"):
                got.append({"t": clean(n.findtext("title")), "u": (n.findtext("link") or "").strip(),
                            "s": clean(n.findtext("description"))[:450], "w": parse_dt(n.findtext("pubDate")), "src": src, "via": "rss"})
            for n in root.findall("a:entry", ns):
                lk = n.find("a:link", ns)
                got.append({"t": clean(n.findtext("a:title", None, ns)), "u": lk.get("href") if lk is not None else "",
                            "s": clean(n.findtext("a:summary", None, ns))[:450], "w": parse_dt(n.findtext("a:updated", None, ns)), "src": src, "via": "rss"})
            got = [g for g in got if g["t"] and (g["w"] is None or g["w"] >= cutoff)]
            log("   OK   %-3d items  %s" % (len(got), url))
            ok += 1
            items.extend(got)
        except Exception as e:
            log("   FAIL %-18s %s" % (type(e).__name__, url))
    return items, "RSS %d/%d" % (ok, len(FEEDS))

# --------------------------------------------------------------------------
# Classification
# --------------------------------------------------------------------------
def classify(it):
    blob = it["t"] + " " + it.get("s", "")
    w = it["w"] or datetime.now(timezone.utc)
    if it["via"] == "email":
        url = "https://www.google.com/search?q=" + urllib.parse.quote_plus('"%s" %s' % (it["t"], it["src"]))
    else:
        url = it.get("u", "")
    base = {"t": it["t"], "src": it["src"], "via": it["via"], "d": w.strftime("%d %b %Y"),
            "ts": w.astimezone(timezone.utc).isoformat(timespec="minutes"), "url": url}
    for tag, pat, why in NOISE:
        if re.search(pat, blob, re.I):
            return dict(base, sig=0, s=0, cat="noise", tags=[tag, "RULE-BASED"],
                        why="<b>Rejected — %s.</b> %s" % (tag.replace("-", " ").lower(), why))
    sc, ms, cs = 0, [], []
    for wt, cat, pat, why in SIG:
        if re.search(pat, blob, re.I):
            sc += wt; ms.append(why); cs.append(cat)
    if not ms or abs(sc) < 3:
        return dict(base, sig=0, s=0, cat="noise", tags=["SUB-THRESHOLD", "RULE-BASED"],
                    why="<b>Rejected — below threshold.</b> No supply, demand or effective-supply mechanism matched strongly enough to score.")
    sc = max(-10, min(10, sc))
    cat = max(set(cs), key=cs.count)
    return dict(base, sig=1, s=sc, cat=cat, tags=[cat.upper(), "RULE-BASED", "VERIFY"],
                why="<b>Mechanism:</b> " + " ".join(ms[:2]) + " <b>Matched by keyword, not understood — read the headline yourself.</b>")

# --------------------------------------------------------------------------
# Page I/O
# --------------------------------------------------------------------------
BLOCK_RX  = re.compile(r"/\*SIGNALS_START\*/.*?/\*SIGNALS_END\*/", re.S)
STATUS_RX = re.compile(r"<!--STATUS_START-->.*?<!--STATUS_END-->", re.S)

def load_previous(page):
    m = re.search(r"/\*SIGNALS_START\*/\s*let ARTICLES\s*=\s*(.*?);\s*/\*SIGNALS_END\*/", page, re.S)
    if not m:
        return []
    try:
        return json.loads(m.group(1))
    except Exception:
        return []

def main():
    page = open(PAGE, encoding="utf-8").read()
    if not BLOCK_RX.search(page) or not STATUS_RX.search(page):
        sys.exit("ERROR: index.html is missing the /*SIGNALS_START*/ or <!--STATUS_START--> markers.")

    log(""); log("SOURCES"); log("-" * 66)
    g_items, g_state, g_err = gmail_items()
    if g_err:
        log("!! " + g_err)
    r_items, r_state = rss_items()
    log("-" * 66)

    fresh, seen = [], set()
    for it in g_items + r_items:
        k = key(it["t"])
        if not k or k in seen:
            continue
        # Email items come from newsletters you chose, so keep them all;
        # RSS items must pass the dry-bulk relevance filter.
        if it["via"] == "rss" and not REL.search(it["t"] + " " + it.get("s", "")):
            continue
        seen.add(k)
        fresh.append(classify(it))

    now = datetime.now(timezone.utc)
    cutoff = now - timedelta(days=KEEP_DAYS)
    merged = {key(a["t"]): a for a in load_previous(page) if a.get("ts")}
    for a in fresh:
        merged[key(a["t"])] = a
    arts = []
    for a in merged.values():
        try:
            if datetime.fromisoformat(a["ts"]) >= cutoff:
                arts.append(a)
        except Exception:
            pass
    arts.sort(key=lambda a: (a["ts"], abs(a["s"])), reverse=True)
    arts = arts[:MAX_ITEMS]
    nsig = sum(1 for a in arts if a["sig"])
    log("%d new today -> %d on page (%d signal / %d noise, last %d days)" % (len(fresh), len(arts), nsig, len(arts) - nsig, KEEP_DAYS))

    payload = json.dumps(arts, ensure_ascii=False, indent=1).replace("<", "\\u003c")
    page = BLOCK_RX.sub(lambda m: "/*SIGNALS_START*/\nlet ARTICLES=" + payload + ";\n/*SIGNALS_END*/", page)

    health_ok = g_err is None
    g_col = "#3b6d11" if health_ok else "#a32d2d"
    status = ("<!--STATUS_START-->LIVE FEED &middot; UPDATED " + now.strftime("%d %b %Y %H:%M") + " UTC<br>"
              '<span style="color:' + g_col + '">' + html.escape(g_state) + "</span> &middot; " + html.escape(r_state) + " &middot; "
              + str(len(fresh)) + " new &middot; " + str(nsig) + " signal / " + str(len(arts) - nsig) + " noise (" + str(KEEP_DAYS) + "d)"
              "<!--STATUS_END-->")
    page = STATUS_RX.sub(lambda m: status, page)
    open(PAGE, "w", encoding="utf-8").write(page)
    log("Wrote %s" % PAGE)

    if not health_ok:
        print("::error title=Gmail source failed::" + g_err)
        sys.exit(1)   # page is still written; workflow commits it, run shows red

if __name__ == "__main__":
    main()
