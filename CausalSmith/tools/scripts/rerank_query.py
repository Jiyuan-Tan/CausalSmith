# tools/scripts/rerank_query.py
#
# Client for the warm rerank daemon (scripts/rerank_daemon.py). Reads one or more rerank requests
# as JSONL on stdin — each line {"query": "...", "names": [...]} — and writes a JSON array of
# score arrays (aligned to each request's `names`) to --out. Prefers the warm daemon (spawning it
# on first use); falls back to an inline model load so reranking never hard-fails a caller, on
# any OS (the daemon transport is unix-socket on POSIX, loopback TCP on Windows — daemon_ipc.py).
import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
import sys, argparse, json, struct, time, re
import numpy as np
try:
    import daemon_ipc
except ImportError:  # the inline path below must still work
    daemon_ipc = None

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
META = os.path.join(ROOT, "doc", "retrieval_reranker.meta.json")
MAX_NEIGHBORS = 16


def sock_path():
    return daemon_ipc.endpoint("rerank", ROOT + "|reranker") if daemon_ipc else None


def _recvn(conn, n):
    buf = bytearray()
    while len(buf) < n:
        chunk = conn.recv(min(65536, n - len(buf)))
        if not chunk:
            return None
        buf += chunk
    return bytes(buf)


def one_request(conn, query, names):
    conn.sendall((json.dumps({"query": query, "names": names}) + "\n").encode("utf-8"))
    head = _recvn(conn, 4)
    if head is None or len(head) < 4:
        return None
    (n,) = struct.unpack("<i", head)
    if n < 0 or n != len(names):
        return None
    body = _recvn(conn, n * 4)
    if body is None or len(body) < n * 4:
        return None
    return np.frombuffer(body, dtype=np.float32).tolist()


def via_daemon(reqs, path, spawn_wait=120.0):
    """Score each request over the warm daemon (one connection per request). None → fall back."""
    if daemon_ipc is None or path is None:
        return None
    # Ensure the daemon is up (spawn detached, poll until it answers a health-check).
    try:
        daemon_ipc.connect(path).close()
    except OSError as e:
        # Stale endpoint from a dead daemon: clear it so the new one publishes cleanly.
        if isinstance(e, ConnectionRefusedError):
            daemon_ipc.unlink(path)
        daemon = os.path.join(os.path.dirname(__file__), "rerank_daemon.py")
        if not os.path.exists(daemon):
            return None
        try:
            daemon_ipc.spawn_detached([sys.executable, daemon, path, "1800"])
        except Exception:  # noqa: BLE001
            return None
        deadline = time.time() + spawn_wait
        ok = False
        while time.time() < deadline:
            time.sleep(1.0)
            try:
                daemon_ipc.connect(path).close()
                ok = True
                break
            except OSError:
                continue
        if not ok:
            return None

    out = []
    for req in reqs:
        names = req.get("names", [])
        if not names:
            out.append([])
            continue
        try:
            conn = daemon_ipc.connect(path)
        except OSError:
            return None
        try:
            scores = one_request(conn, req.get("query", ""), names)
        finally:
            try:
                conn.close()
            except OSError:
                pass
        if scores is None:
            return None
        out.append(scores)
    return out


# ── inline fallback (no daemon): build passages from the index + score with the model here ──
def _inline(reqs):
    # encoding is explicit: the index carries Unicode from Lean docstrings, which
    # Windows would otherwise decode with the ANSI code page and crash on.
    with open(META, encoding="utf-8") as fh:
        meta = json.load(fh)
    view = meta.get("passage", "nbr")
    with open(os.path.join(ROOT, "doc", "library_index.json"), encoding="utf-8") as fh:
        ents = json.load(fh)["entries"]
    by = {e["name"]: e for e in ents}

    def humanize(name):
        return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name.split(".")[-1]).replace("_", " ").strip()

    def first_para(doc):
        return (doc or "").split("\n\n")[0].strip()

    present = set(by)
    rev = {}
    for e in ents:
        for r in e.get("refs", []) or []:
            if r in present and r != e["name"]:
                rev.setdefault(r, []).append(e["name"])

    def passage(n):
        e = by.get(n)
        if e is None:
            return humanize(n)
        head, body = humanize(n), first_para(e.get("doc")) or ""
        if view != "nbr":
            return f"{head}. {body or (e.get('statement') or '')}".strip()
        refs = [r for r in (e.get("refs") or []) if r in present and r != n]
        revs = [r for r in rev.get(n, []) if r != n]
        seen, neigh = set(), []
        for r in refs + revs:
            if r in seen:
                continue
            seen.add(r)
            neigh.append(humanize(r))
            if len(neigh) >= MAX_NEIGHBORS:
                break
        tail = (" Related: " + "; ".join(neigh)) if neigh else ""
        return f"{head}. {body}{tail}".strip()

    from sentence_transformers.cross_encoder import CrossEncoder
    model_dir = meta["model"] if os.path.isabs(meta["model"]) else os.path.join(ROOT, meta["model"])
    ce = CrossEncoder(model_dir, max_length=256)
    out = []
    for req in reqs:
        names = req.get("names", [])
        if not names:
            out.append([])
            continue
        pairs = [[req.get("query", ""), passage(n)] for n in names]
        out.append(np.asarray(ce.predict(pairs, batch_size=64, show_progress_bar=False), dtype=np.float32).tolist())
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--no-daemon", action="store_true")
    args = ap.parse_args()
    # See embed_text.py: queries and decl names carry Lean Unicode, and Windows would
    # otherwise decode stdin with the ANSI code page.
    # stderr too: these scripts print temp paths, and a non-ASCII Windows username
    # (C:\\Users\\Мария\\...) would otherwise raise UnicodeEncodeError on a redirected
    # pipe AFTER the work succeeded, turning a good result into a non-zero exit.
    if hasattr(sys.stderr, "reconfigure"):
        try:
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
        except (OSError, ValueError):
            pass  # closed or detached stderr: never let this abort startup
    if hasattr(sys.stdin, "reconfigure"):
        sys.stdin.reconfigure(encoding="utf-8", errors="replace")
    reqs = [json.loads(ln) for ln in sys.stdin if ln.strip()]

    scores = None
    via = "inline"
    if not args.no_daemon and reqs:
        scores = via_daemon(reqs, sock_path())
        if scores is not None:
            via = "daemon"
    if scores is None:
        scores = _inline(reqs)

    with open(args.out, "w", encoding="utf-8") as fh:
        json.dump(scores, fh)
    print(f"reranked {len(reqs)} requests via {via} -> {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
