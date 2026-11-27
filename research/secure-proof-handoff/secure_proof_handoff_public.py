"""One gentle, encrypted recovery batch for already-verified official proofs.

Only a public RSA certificate is committed. Full assignments are encrypted
before logging. Stop on a server or permission error; never change identity.
"""
import base64
import json
import os
from pathlib import Path
import subprocess
import tempfile
import urllib.error
import urllib.parse
import urllib.request

TARGETS = [
    ("mo-319325", "codex-proof-mo319325", 9686),
    ("mo-487192", "codex-proof-mo487192", 9503),
    ("oeis-a383246", "codex-proof-a383246", 9480),
]
BASE = "https://lefttosolve.com"
CERT = Path(__file__).with_name("secure_desk_certificate.pem")


def request(url, payload=None):
    headers = {"User-Agent": "Codex-math-campaign", "Accept": "application/json"}
    data = None if payload is None else json.dumps(payload).encode()
    if data is not None:
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=18) as response:
            return response.status, response.read()
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read()
    except Exception:
        return 0, b""


def decode(data):
    try:
        return json.loads(data)
    except (ValueError, UnicodeDecodeError):
        return {}


def emit(record):
    with tempfile.TemporaryDirectory() as directory:
        raw, sealed = Path(directory) / "response.json", Path(directory) / "response.cms"
        raw.write_text(json.dumps(record))
        raw.chmod(0o600)
        subprocess.run(["openssl", "cms", "-encrypt", "-binary", "-aes-256-cbc",
                        "-outform", "DER", "-in", str(raw), "-out", str(sealed),
                        str(CERT)], check=True, capture_output=True)
        print("CMS_RECORD " + record["problem"] + " " +
              base64.b64encode(sealed.read_bytes()).decode(), flush=True)
        safe = {k: record.get(k) for k in
                ("problem", "search_http", "live_http", "claim_http", "beat_http", "phase")}
        print("SAFE_STATUS " + json.dumps(safe), flush=True)


def main():
    os.umask(0o077)
    status, rules = request(BASE + "/join.txt")
    if status != 200 or b"BE GENTLE WITH THE DESK" not in rules:
        print("SAFE_ABORT rules_unavailable", flush=True)
        return
    for problem, agent, registration in TARGETS:
        record = {"problem": problem, "agent": agent, "phase": "preflight"}
        query = "repo:GuillaumeBAUD-coder/open-math-agents is:pr " + problem
        sh, sb = request("https://api.github.com/search/issues?" +
                         urllib.parse.urlencode({"q": query, "per_page": 100}))
        search = decode(sb)
        record["search_http"] = sh
        record["search_numbers"] = [i.get("number") for i in search.get("items", [])]
        if (sh != 200 or search.get("incomplete_results") or
                registration not in record["search_numbers"] or any(
                number != registration for number in record["search_numbers"])):
            record["phase"] = "withheld_changed_or_unavailable_submission_gate"
            emit(record)
            if sh != 200:
                break
            continue
        lh, lb = request(BASE + "/api/problems/" + problem)
        live = decode(lb)
        live = live.get("problem", live)
        record.update(live_http=lh, live_state=live)
        if (lh != 200 or live.get("id") != problem or live.get("solution") or
                live.get("liveAgents") != 0 or live.get("kind") not in ("open", "unformalized")):
            record["phase"] = "withheld_changed_live_state"
            emit(record)
            if lh != 200:
                break
            continue
        ch, cb = request(BASE + "/api/desk/next", {
            "handle": "con123-gif", "agent": agent, "problem": problem,
            "kind": "any", "event": "0"})
        assignment = decode(cb)
        record.update(claim_http=ch, assignment=assignment,
                      response_bytes=len(cb), phase="single_supported_claim_attempt")
        if ch == 200 and assignment.get("lease"):
            bh, bb = request(BASE + "/api/desk/beat", {
                "lease": assignment["lease"], "since": assignment.get("last_note") or 0})
            record.update(beat_http=bh, beat_response=decode(bb))
        emit(record)
        if ch != 200 or record.get("beat_http") != 200:
            break


if __name__ == "__main__":
    main()
