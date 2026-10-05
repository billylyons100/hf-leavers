"""
HF Leavers monitor: Form ADV Schedule A departures for hedge fund advisers.

Standalone repo, fully separate from sec-monitor (the termination monitor). The hedge fund
name filter and email sender are copied verbatim from sec-monitor/main.py as of Oct 2, 2026;
if the filter changes there, copy it here too.

How it works, each run:
  1. Universe: once a month, rebuild the list of advisers to watch from the SEC's
     monthly adviser data files (registered + exempt reporting advisers), keeping
     firms that report private funds and pass main.py's hedge fund name filter.
  2. Change detection: for each firm, read advFilingDate from the IAPD detail JSON.
     A new date means a new ADV filing.
  3. For changed firms, wait until the ADV report PDF has actually been regenerated
     (its ETag changes, usually the morning after the filing), then download it,
     parse the Schedule A table, and diff it against the saved snapshot.
  4. Email any qualifying departures. Firms seen for the first time are only
     baselined (no alerts), a capped number per run.

Modes:
  python leavers.py                     normal run (used by .github/workflows/leavers.yml)
  python leavers.py --test 157813,335438   parse and print Schedule A for these CRDs; no state, no email
  python leavers.py --universe-test     build the universe and print counts/columns; no state, no email
"""

import io
import os
import re
import sys
import json
import time
import zipfile
import logging
from datetime import datetime, timezone, date

import requests
import pdfplumber
from pypdf import PdfReader

import smtplib
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s",
                    datefmt="%Y-%m-%d %H:%M:%S")
log = logging.getLogger("leavers")

# ── Copied verbatim from sec-monitor/main.py (Oct 2, 2026) ────────────────────
EMAIL_SENDER    = os.environ.get("EMAIL_SENDER", "")
EMAIL_PASSWORD  = os.environ.get("EMAIL_PASSWORD", "")
EMAIL_RECIPIENT = os.environ.get("EMAIL_RECIPIENT", "")

IAPD_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json, */*",
    "Referer": "https://www.adviserinfo.sec.gov/",
}

# ── Exact-name whitelist ──────────────────────────────────────────────────────
# Firms here always pass the filter regardless of negative pattern matches.
POSITIVE_NAME_WHITELIST: list[str] = [
    "MY LEGACY ADVISORS, LLC",
    "PLACID SOUND CAPITAL MANAGEMENT, LLC",
    "WAVERTON INVESTMENT MANAGEMENT LIMITED",
    "SENSIBLE FINANCIAL PLANNING AND MANAGEMENT, LLC",
    "THE FINANCIAL ADVISORS, LLC",
]

# ── Strong institutional pattern whitelist ────────────────────────────────────
# Substring match in the normalised firm name → strong positive signal.
# Negative retail terms do NOT override a pattern-whitelist match unless the
# name is explicitly retail-branded (score drops below -15 after all penalties).
POSITIVE_PATTERN_WHITELIST: list[str] = [
    "asset management",
    "capital management",
    "investment management",
    "capital partners",
    "asset management llc",
    "asset management lp",
    "investment management limited",
    "capital management ltd",
    "capital management llc",
    "capital management lp",
    "partners lp",
    "partners llc",
    "partners llp",
    "capital llc",
    "capital lp",
    "capital ltd",
]

# ── Scoring tables (used when no whitelist entry matches) ─────────────────────
# Tier 1 (+15): unambiguous institutional phrases
_TIER1: dict[str, int] = {
    "asset management":             15,
    "capital management":           15,
    "investment management":        15,
    "capital partners":             15,
    "capital advisors":             15,
    "capital adviser":              15,
    "investment counsel":           15,
    "investor solutions":           15,
    "systematic trading":           15,
}

# Tier 2 (+10 or +15): institutional phrase + legal structure
_TIER2: dict[str, int] = {
    "asset management limited":     15,
    "investment management limited":15,
    "capital management limited":   15,
    "capital management lp":        15,
    "capital management llc":       15,
    "capital management llp":       15,
    "capital group":                10,
    "management limited":           10,
    "management lp":                10,
    "management llc":               10,
    "management ltd":               10,
    "management llp":               10,
    "partners lp":                  10,
    "partners llp":                 10,
    "partners limited":             10,
    "investments lp":               10,
    "investments llc":              10,
    "investments llp":              10,
    "capital llc":                  10,
    "capital lp":                   10,
    "capital ltd":                  10,
    "capital limited":              10,
    "capital ag":                   10,
}

# Supporting terms: whole-word matches, total capped at +8
_SUPPORT: dict[str, int] = {
    "capital":      4,
    "asset":        4,
    "investment":   4,
    "investor":     3,
    "management":   3,
    "partners":     3,
    "advisors":     2,
    "adviser":      2,
    "trading":      2,
    "systematic":   2,
    "solutions":    2,
    "counsel":      2,
    "group":        2,
    "investments":  2,
    "ltd":          2,
    "limited":      2,
    "lp":           2,
    "llp":          2,
    "llc":          2,
    "ag":           2,
}

# Negative patterns: each match deducts heavily
_NEGATIVE: dict[str, int] = {
    "wealth management":    -20,
    "financial planning":   -20,
    "financial advisors":   -20,
    "financial advisor":    -20,
    "retirement":           -15,
    "insurance":            -15,
    "brokerage":            -15,
    "personal financial":   -15,
    "private client":       -15,
    "family wealth":        -15,
    "mortgage":             -15,
    "tax planning":         -15,
}

RELEVANCE_THRESHOLD = 10


def _normalise(name: str) -> str:
    """Lower-case, expand abbreviations, strip punctuation."""
    import re
    n = name.lower()
    n = n.replace("l.p.", "lp").replace("l.l.c.", "llc").replace("l.l.p.", "llp")
    n = re.sub(r"[^\w\s]", " ", n)
    n = re.sub(r"\s+", " ", n).strip()
    return n


def _score_firm(firm_name: str) -> tuple[int, str]:
    """Return (raw_score, top_matched_pattern)."""
    n = _normalise(firm_name)
    total = 0
    top_pattern = ""

    for table in (_TIER2, _TIER1):
        for pat in sorted(table, key=len, reverse=True):
            if pat in n:
                total += table[pat]
                if not top_pattern:
                    top_pattern = pat

    for pat, pen in _NEGATIVE.items():
        if pat in n:
            total += pen

    support = 0
    words = set(n.split())
    for term, pts in _SUPPORT.items():
        if term in words:
            support += pts
    total += min(support, 8)

    return total, top_pattern


def _get_match_reason(firm_name: str) -> tuple[bool, int, str]:
    """Return (passes_filter, score, reason_string).

    Priority order:
    1. Exact name whitelist  → always passes, score=999
    2. Pattern whitelist     → passes unless strongly retail-branded (score < -15)
    3. Scoring filter        → passes if score >= RELEVANCE_THRESHOLD
    """
    n = _normalise(firm_name)

    # 1. Exact name whitelist
    for entry in POSITIVE_NAME_WHITELIST:
        if _normalise(entry) == n:
            return True, 999, f"Exact whitelist: {entry}"

    # 2. Pattern whitelist
    matched_pat = None
    for pat in sorted(POSITIVE_PATTERN_WHITELIST, key=len, reverse=True):
        if pat in n:
            matched_pat = pat
            break

    if matched_pat:
        score, _ = _score_firm(firm_name)
        if score < -15:
            # Name is explicitly retail-branded even with the institutional pattern
            neg_hits = [p for p in _NEGATIVE if p in n]
            return False, score, (
                f"Pattern '{matched_pat}' found but overridden by retail indicators: "
                + ", ".join(neg_hits)
            )
        return True, max(score, 10), f"Strong pattern: '{matched_pat}'"

    # 3. Standard scoring
    score, top_pat = _score_firm(firm_name)
    if score >= RELEVANCE_THRESHOLD:
        return True, score, f"Score {score}: {top_pat or 'supporting terms'}"
    neg_hits = [p for p in _NEGATIVE if p in n]
    return False, score, (
        f"Score {score} (threshold {RELEVANCE_THRESHOLD})"
        + (f" — retail indicators: {', '.join(neg_hits)}" if neg_hits else "")
    )


def find_matched_keyword(firm_name: str) -> str:
    """Return the match reason string (used in email body)."""
    _, _, reason = _get_match_reason(firm_name)
    return reason


def is_relevant(firm_name: str) -> bool:
    """Return True if the firm passes the institutional filter."""
    passes, _, _ = _get_match_reason(firm_name)
    return passes


def send_email(subject: str, body: str) -> None:
    if not all([EMAIL_SENDER, EMAIL_PASSWORD, EMAIL_RECIPIENT]):
        log.warning("Email credentials not configured — skipping alert.")
        return
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"]    = EMAIL_SENDER
    msg["To"]      = EMAIL_RECIPIENT
    msg.attach(MIMEText(body, "plain"))
    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as srv:
            srv.login(EMAIL_SENDER, EMAIL_PASSWORD)
            recipients = [r.strip() for r in EMAIL_RECIPIENT.split(",") if r.strip()]
            srv.sendmail(EMAIL_SENDER, recipients, msg.as_string())
        log.info("Email sent to %s", EMAIL_RECIPIENT)
    except smtplib.SMTPException as exc:
        log.error("Failed to send email: %s", exc)
# ── End of copied block ───────────────────────────────────────────────────────

# ── Files ─────────────────────────────────────────────────────────────────────
SNAPSHOT_FILE = "schedule_a_snapshot.json"   # {crd: {...}} saved Schedule A per firm
UNIVERSE_FILE = "leavers_universe.json"      # {"month": "2026-10", "firms": {crd: name}}

# ── Endpoints ─────────────────────────────────────────────────────────────────
IAPD_DETAIL_URL = "https://api.adviserinfo.sec.gov/search/firm/{crd}"
ADV_PDF_URL = "https://reports.adviserinfo.sec.gov/reports/ADV/{crd}/PDF/{crd}.pdf"
IAPD_PROFILE_URL = "https://adviserinfo.sec.gov/firm/summary/{crd}"
SEC_DATA_URL = ("https://www.sec.gov/files/investment/data/other/"
                "information-about-registered-investment-advisers-exempt-reporting-advisers/"
                "ia{mmddyyyy}-{kind}.zip")
# sec.gov requires a declared User-Agent with contact info. Set SEC_USER_AGENT as a repo secret.
SEC_HEADERS = {"User-Agent": os.environ.get("SEC_USER_AGENT", "FLS sec-monitor research")}

# ── Limits ────────────────────────────────────────────────────────────────────
DETAIL_DELAY = 0.25          # seconds between IAPD detail calls
PDF_DELAY = 1.0              # seconds between PDF downloads
BASELINE_PER_RUN = int(os.environ.get("BASELINE_PER_RUN", "2000"))   # per chunk; time budget usually binds first
MAX_RUN_SECONDS = int(os.environ.get("MAX_RUN_SECONDS", str(25 * 60)))  # one chunk; workflow loops chunks and commits between them
RECHECK_AFTER_HOURS = 20       # a firm checked more recently than this is skipped (lets chunks resume)
SAVE_EVERY = 25                # write the snapshot to disk every N firms
PARSE_TIMEOUT = 180            # seconds; a PDF that takes longer is skipped
PARSE_MEMORY_BYTES = 2 * 1024 ** 3   # 2 GB cap per parse so one huge PDF can't take down the runner
MAX_SCAN_PAGES = 200           # pages to search for the Schedule A header before giving up
EXIT_MORE_WORK = 10            # exit code telling the workflow another chunk is needed

# ── Schedule A parsing ────────────────────────────────────────────────────────
TABLE_HDR = re.compile(r"FULL\s+LEGAL\s+NAME\s*\(\s*INDIVIDUALS", re.IGNORECASE)
TABLE_END = re.compile(r"\n\s*Schedule B\b")
ROW = re.compile(
    r"^(?P<name>.+?)\s+(?P<type>DE|FE|I)\s+(?P<title>.*?)\s*"
    r"(?P<date>\d{2}/\d{4})\s*(?P<code>NA|[A-E])\s+(?P<ctrl>[YN])\s+(?P<pr>[YN])"
    r"(?:\s+(?P<crd>\d{3,}))?\s*$"
)

# Ownership codes: NA <5%, A 5-10%, B 10-25%, C 25-50%, D 50-75%, E 75%+
MAJOR_OWNER_CODES = {"C", "D", "E"}
# Titles that are pure ownership, not a management role
PASSIVE_TITLE = re.compile(r"^(LIMITED PARTNER|INVESTOR|MEMBER|SHAREHOLDER|SOLE MEMBER|OWNER)$")


def parse_schedule_a(text: str) -> list[dict]:
    """Parse Schedule A rows out of the ADV report text. Returns [] if the table isn't found."""
    m = TABLE_HDR.search(text)
    if not m:
        return []
    body = text[m.start():]
    end = TABLE_END.search(body)
    body = body[:end.start()] if end else body[:8000]

    rows: list[dict] = []
    for raw_line in body.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        hit = ROW.match(line)
        if hit:
            d = hit.groupdict()
            rows.append({
                "name": d["name"].strip(),
                "type": d["type"],
                "title": d["title"].strip(),
                "acquired": d["date"],
                "code": d["code"],
                "control": d["ctrl"],
                "crd": d["crd"] or "",
            })
        elif rows:
            # Continuation of a wrapped title (e.g. "OFFICER"); header lines come before the first row
            rows[-1]["title"] = (rows[-1]["title"] + " " + line).strip()
    return rows


def row_key(row: dict) -> str:
    return f"crd:{row['crd']}" if row.get("crd") else f"name:{_normalise(row['name'])}"


def qualifies(row: dict) -> bool:
    """Management roles always count; passive owners only at 25%+."""
    title = re.sub(r"\s+", " ", row["title"].upper()).strip(" ,/")
    if PASSIVE_TITLE.match(title):
        return row["code"] in MAJOR_OWNER_CODES
    return True


# ── IAPD access ───────────────────────────────────────────────────────────────
class RateLimited(Exception):
    pass


def get_adv_filing_date(crd: str) -> str | None:
    r = requests.get(IAPD_DETAIL_URL.format(crd=crd),
                     params={"hl": "true", "nrows": 12, "query": "", "r": 25,
                             "sort": "score+desc", "wt": "json"},
                     headers=IAPD_HEADERS, timeout=30)
    if r.status_code == 429:
        raise RateLimited()
    if r.status_code != 200:
        return None
    m = re.search(r'advFilingDate\\?"\s*:\s*\\?"(\d{1,2}/\d{1,2}/\d{4})', r.text)
    return m.group(1) if m else None


def get_pdf_etag(crd: str) -> str | None:
    r = requests.head(ADV_PDF_URL.format(crd=crd), headers=IAPD_HEADERS, timeout=30,
                      allow_redirects=True)
    if r.status_code == 429:
        raise RateLimited()
    return r.headers.get("ETag") if r.status_code == 200 else None


def _parse_worker(path: str, conn) -> None:
    """Runs in a child process with a memory cap, so a huge PDF fails alone instead of
    exhausting the runner's memory (which is what killed the first three runs)."""
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_AS, (PARSE_MEMORY_BYTES, PARSE_MEMORY_BYTES))
    except Exception:
        pass
    try:
        start_page = None
        reader = PdfReader(path)
        for i, p in enumerate(reader.pages):
            if i >= MAX_SCAN_PAGES:
                break
            if TABLE_HDR.search(p.extract_text() or ""):
                start_page = i
                break
        del reader
        if start_page is None:
            conn.send(("ok", []))
            return
        collected = []
        with pdfplumber.open(path) as pdf:
            for page in pdf.pages[start_page:start_page + 15]:
                collected.append(page.extract_text() or "")
                page.close()
                joined = "\n".join(collected)
                hdr = TABLE_HDR.search(joined)
                if hdr and TABLE_END.search(joined[hdr.start():]):
                    break
        conn.send(("ok", parse_schedule_a("\n".join(collected))))
    except MemoryError:
        conn.send(("error", "memory cap hit"))
    except Exception as exc:
        conn.send(("error", repr(exc)[:200]))
    finally:
        conn.close()


def parse_pdf_isolated(content: bytes) -> tuple[list[dict] | None, str]:
    import multiprocessing as mp
    import tempfile
    with tempfile.NamedTemporaryFile(suffix=".pdf", delete=False) as tmp:
        tmp.write(content)
        path = tmp.name
    ctx = mp.get_context("fork")
    parent, child = ctx.Pipe(duplex=False)
    proc = ctx.Process(target=_parse_worker, args=(path, child), daemon=True)
    try:
        proc.start()
        child.close()
        if parent.poll(PARSE_TIMEOUT):
            status, payload = parent.recv()
        else:
            status, payload = "error", f"timed out after {PARSE_TIMEOUT}s"
    except EOFError:
        status, payload = "error", "parser process died"
    finally:
        if proc.is_alive():
            proc.kill()
        proc.join(5)
        parent.close()
        try:
            os.remove(path)
        except OSError:
            pass
    return (payload, "ok") if status == "ok" else (None, payload)


def fetch_schedule_a(crd: str) -> tuple[list[dict] | None, str | None]:
    """Download the ADV report and parse Schedule A in an isolated, memory-capped process."""
    r = requests.get(ADV_PDF_URL.format(crd=crd), headers=IAPD_HEADERS, timeout=120)
    if r.status_code == 429:
        raise RateLimited()
    if r.status_code != 200:
        log.warning("CRD %s: PDF status %s", crd, r.status_code)
        return None, None
    etag = r.headers.get("ETag")
    mb = len(r.content) / 1e6
    rows, note = parse_pdf_isolated(r.content)
    del r
    if rows is None:
        log.warning("CRD %s: parse failed (%s, %.1f MB)", crd, note, mb)
    return rows, etag


# ── Universe ──────────────────────────────────────────────────────────────────
def _find_col(cols: list[str], *needles: str) -> str | None:
    for c in cols:
        flat = re.sub(r"[^a-z0-9]", "", str(c).lower())
        if any(n in flat for n in needles):
            return c
    return None


def build_universe() -> dict[str, str]:
    """Advisers reporting private funds that pass main.py's hedge fund name filter."""
    import pandas as pd

    firms: dict[str, str] = {}
    today = date.today()
    for kind in ("registered", "exempt"):
        frame = None
        for back in range(0, 4):   # try this month, then up to 3 months back
            y, mth = today.year, today.month - back
            while mth <= 0:
                mth += 12
                y -= 1
            url = SEC_DATA_URL.format(mmddyyyy=f"{mth:02d}01{y}", kind=kind)
            r = requests.get(url, headers=SEC_HEADERS, timeout=120)
            if r.status_code == 200:
                z = zipfile.ZipFile(io.BytesIO(r.content))
                name = z.namelist()[0]
                raw = z.read(name)
                if name.lower().endswith((".xlsx", ".xls")):
                    frame = pd.read_excel(io.BytesIO(raw), dtype=str)
                else:
                    frame = pd.read_csv(io.BytesIO(raw), dtype=str, encoding="latin-1")
                log.info("Universe: loaded %s (%d rows)", url, len(frame))
                break
        if frame is None:
            raise RuntimeError(f"Could not download SEC {kind} adviser file")

        cols = list(frame.columns)
        crd_col = _find_col(cols, "organizationcrd", "crd")
        name_col = _find_col(cols, "primarybusinessname", "legalname", "businessname")
        pf_col = _find_col(cols, "7b1", "privatefund")
        log.info("Universe %s columns -> CRD: %s | name: %s | private fund: %s",
                 kind, crd_col, name_col, pf_col)
        if not crd_col or not name_col:
            raise RuntimeError(f"Missing CRD/name column in {kind} file: {cols[:40]}")

        for _, row in frame.iterrows():
            crd = str(row[crd_col]).strip().split(".")[0]
            name = str(row[name_col]).strip()
            if not crd.isdigit() or not name:
                continue
            if pf_col:
                v = str(row[pf_col]).strip().upper()
                has_pf = v in ("Y", "YES") or (v.replace(".", "").isdigit() and float(v) > 0)
                if not has_pf:
                    continue
            if is_relevant(name):
                firms[crd] = name
    return firms


# ── State ─────────────────────────────────────────────────────────────────────
def load(path, default):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError):
        return default


def save(path, data):
    with open(path, "w") as f:
        json.dump(data, f, indent=1, sort_keys=True)


# ── Email ─────────────────────────────────────────────────────────────────────
def build_email(events: list[dict]) -> tuple[str, str]:
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    n = sum(len(e["leavers"]) for e in events)
    subject = f"HF Leavers {today}: {n} departure{'s' if n != 1 else ''} at {len(events)} firm{'s' if len(events) != 1 else ''}"
    lines = [f"Schedule A departures, hedge fund advisers ({today})", ""]
    for e in events:
        lines.append(f"{e['firm']} (CRD {e['crd']}), ADV filed {e['filing_date']}")
        for r in e["leavers"]:
            owner = " [owner]" if PASSIVE_TITLE.match(r["title"].upper()) else ""
            lines.append(f"  LEFT:   {r['name']} | {r['title']}{owner} | code {r['code']} | control {r['control']}")
        for r in e["joiners"]:
            lines.append(f"  JOINED: {r['name']} | {r['title']} | since {r['acquired']}")
        lines.append(f"  {IAPD_PROFILE_URL.format(crd=e['crd'])}")
        lines.append("")
    return subject, "\n".join(lines)


# ── Main run ──────────────────────────────────────────────────────────────────
def _recent(ts: str | None) -> bool:
    if not ts:
        return False
    try:
        age = datetime.now(timezone.utc) - datetime.fromisoformat(ts)
    except ValueError:
        return False
    return age.total_seconds() < RECHECK_AFTER_HOURS * 3600


def run() -> int:
    """One chunk of work. Returns 0 when today's work is done, EXIT_MORE_WORK if time ran out."""
    t0 = time.time()
    snap = load(SNAPSHOT_FILE, {})
    uni = load(UNIVERSE_FILE, {})

    month = date.today().strftime("%Y-%m")
    if uni.get("month") != month or not uni.get("firms"):
        try:
            uni = {"month": month, "firms": build_universe()}
            save(UNIVERSE_FILE, uni)
            log.info("Universe rebuilt: %d firms", len(uni["firms"]))
        except Exception:
            log.exception("Universe rebuild failed; keeping previous list (%d firms)",
                          len(uni.get("firms", {})))
    firms = uni.get("firms", {})
    if not firms:
        log.error("No universe available; stopping.")
        return 1

    # Pass 1: daily checks on baselined firms not yet checked today (oldest first).
    # Pass 2: baseline new firms with the time left. Daily checks always come first.
    known = sorted((c for c in firms if c in snap and not _recent(snap[c].get("checked"))),
                   key=lambda c: snap[c].get("checked", ""))
    unknown = [c for c in firms if c not in snap and not _recent(snap.get("_failed", {}).get(c))]
    events, baselined, checked, parse_failures, errors = [], 0, 0, [], 0
    out_of_time = False
    since_save = 0

    def checkpoint(force=False):
        nonlocal since_save
        since_save += 1
        if force or since_save >= SAVE_EVERY:
            save(SNAPSHOT_FILE, snap)
            since_save = 0

    try:
        for crd in known:
            if time.time() - t0 > MAX_RUN_SECONDS:
                out_of_time = True
                break
            prior = snap[crd]
            try:
                filing = get_adv_filing_date(crd)
                time.sleep(DETAIL_DELAY)
                checked += 1
                if filing and filing != prior.get("filing_date"):
                    # New filing. Only read the PDF once IAPD has regenerated it.
                    etag = get_pdf_etag(crd)
                    if not etag or etag == prior.get("etag"):
                        log.info("CRD %s: new filing %s, report not regenerated yet", crd, filing)
                    else:
                        rows, etag = fetch_schedule_a(crd)
                        time.sleep(PDF_DELAY)
                        if not rows:
                            parse_failures.append(crd)   # never treat a failed parse as everyone leaving
                        else:
                            old = {row_key(r): r for r in prior["rows"]}
                            new = {row_key(r): r for r in rows}
                            leavers = [r for k, r in old.items() if k not in new and qualifies(r)]
                            joiners = [r for k, r in new.items() if k not in old]
                            if leavers:
                                events.append({"firm": firms[crd], "crd": crd, "filing_date": filing,
                                               "leavers": leavers, "joiners": joiners})
                            prior.update({"firm": firms[crd], "filing_date": filing,
                                          "etag": etag, "rows": rows})
            except RateLimited:
                raise
            except Exception as exc:
                errors += 1
                log.warning("CRD %s: check failed (%s); retrying next run", crd, repr(exc)[:150])
                continue
            prior["checked"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
            checkpoint()

        for crd in unknown:
            if out_of_time:
                break
            if time.time() - t0 > MAX_RUN_SECONDS:
                out_of_time = True
                break
            if baselined >= BASELINE_PER_RUN:
                break
            try:
                filing = get_adv_filing_date(crd)
                time.sleep(DETAIL_DELAY)
                rows, etag = fetch_schedule_a(crd)
                time.sleep(PDF_DELAY)
            except RateLimited:
                raise
            except Exception as exc:
                errors += 1
                log.warning("CRD %s: baseline failed (%s); retrying next run", crd, repr(exc)[:150])
                continue
            now = datetime.now(timezone.utc).isoformat(timespec="seconds")
            if rows:
                snap[crd] = {"firm": firms[crd], "filing_date": filing, "etag": etag,
                             "rows": rows, "checked": now}
                baselined += 1
            else:
                # Remember the failure so the same unparseable firm isn't retried every chunk
                snap.setdefault("_failed", {})[crd] = now
                parse_failures.append(crd)
            checkpoint()
    except RateLimited:
        log.warning("IAPD rate limit hit; saving progress, remaining firms roll to next run.")
        out_of_time = False   # don't hammer IAPD with another chunk today
    finally:
        save(SNAPSHOT_FILE, snap)

    done = sum(1 for c in firms if c in snap)
    log.info("Baseline progress: %d of %d firms", done, len(firms))
    log.info("Checked %d | baselined %d | departures at %d firms | parse failures %d | errors %d | %.0fs",
             checked, baselined, len(events), len(parse_failures), errors, time.time() - t0)
    if parse_failures:
        log.warning("Parse failures (CRDs): %s", ", ".join(parse_failures[:50]))
    if events:
        subject, body = build_email(events)
        send_email(subject, body)
    return EXIT_MORE_WORK if out_of_time else 0


def test_crds(crds: list[str]) -> None:
    for crd in crds:
        print("=" * 80)
        filing = get_adv_filing_date(crd)
        etag = get_pdf_etag(crd)
        t = time.time()
        rows, _ = fetch_schedule_a(crd)
        print(f"CRD {crd} | advFilingDate {filing} | ETag {etag} | rows {len(rows or [])} | "
              f"parse {time.time() - t:.1f}s")
        for r in rows or []:
            flag = "ALERT-ELIGIBLE" if qualifies(r) else "ignored"
            print(f"  {r['name']} | {r['title']} | {r['acquired']} | code {r['code']} | "
                  f"control {r['control']} | CRD {r['crd'] or '-'} | {flag}")
        time.sleep(1)


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "--test":
        test_crds([c.strip() for c in sys.argv[2].split(",") if c.strip()])
    elif len(sys.argv) > 1 and sys.argv[1] == "--universe-test":
        u = build_universe()
        print(f"Universe size: {len(u)}")
        for crd in ["157813", "161413", "333746", "335438", "138769"]:
            print(crd, "IN" if crd in u else "MISSING", u.get(crd, ""))
    else:
        sys.exit(run())
