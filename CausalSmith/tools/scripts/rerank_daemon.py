# tools/scripts/rerank_daemon.py
#
# Warm cross-encoder RERANK daemon (Phase 2c). Holds the fine-tuned bge-reranker in memory and
# builds decl passage text from the library index, so repeated rerank requests pay the model
# load (~10 s) and the passage construction ONCE. Serves scores over a local socket — unix-domain
# on POSIX, loopback TCP on Windows; scripts/daemon_ipc.py picks the transport.
#
# Passage text is built HERE (not on the TS side) from the same make_passage() the reranker was
# trained with — so the query-time passage is byte-identical to the training passage. The client
# sends decl NAMES, not text; the daemon resolves each to its `nbr` passage via the index.
#
# Protocol (one request per connection):
#   client → server : one JSON line  {"query": "...", "names": ["Decl.a", "Decl.b", ...]}\n
#   server → client : 4-byte <int32 n>  then n*4 bytes f32 (scores aligned to `names`)
#                     (n = -1 signals a server-side error; client falls back inline)
#   an empty payload is a health-check → n = 0.
#
# The model + passage view are read from doc/retrieval_reranker.meta.json (committed sidecar).
import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
import sys, socket, json, struct, re
import numpy as np
import daemon_ipc

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
INDEX = os.path.join(ROOT, "doc", "library_index.json")
META = os.path.join(ROOT, "doc", "retrieval_reranker.meta.json")
IDLE_TIMEOUT = 1800.0  # 30 min
MAX_NEIGHBORS = 16


def humanize(name):
    return re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name.split(".")[-1]).replace("_", " ").strip()


def first_para(doc):
    return (doc or "").split("\n\n")[0].strip()


def nl_text(e):
    return f"{humanize(e['name'])}. {first_para(e.get('doc')) or (e.get('statement') or '')}".strip()


def build_nbr_ctx(ents):
    present = {e["name"] for e in ents}
    rev = {}
    for e in ents:
        for r in e.get("refs", []) or []:
            if r in present and r != e["name"]:
                rev.setdefault(r, []).append(e["name"])
    return present, rev


def make_passage(e, view, ctx):
    if view != "nbr":
        return nl_text(e)
    present, rev = ctx
    head = humanize(e["name"])
    body = first_para(e.get("doc")) or ""
    refs = [r for r in (e.get("refs") or []) if r in present and r != e["name"]]
    revs = [r for r in rev.get(e["name"], []) if r != e["name"]]
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


def resolve_dir(model_id):
    cand = model_id if os.path.isabs(model_id) else os.path.join(ROOT, model_id)
    return cand if os.path.isdir(cand) else model_id


def load_ce(model_id, max_len=256):
    from sentence_transformers.cross_encoder import CrossEncoder
    return CrossEncoder(resolve_dir(model_id), max_length=max_len)


def recv_line(conn):
    buf = bytearray()
    while b"\n" not in buf:
        chunk = conn.recv(65536)
        if not chunk:
            break
        buf += chunk
    return bytes(buf)


def main():
    # stderr carries temp paths; a non-ASCII Windows username would otherwise raise
    # UnicodeEncodeError on the ANSI code page when stderr is a pipe.
    if hasattr(sys.stderr, "reconfigure"):
        try:
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
        except (OSError, ValueError):
            pass  # closed or detached stderr: never let this abort startup

    if len(sys.argv) < 2:
        print("usage: rerank_daemon.py <endpoint_path> [idle_timeout_s]", file=sys.stderr)
        sys.exit(2)
    sock_path = sys.argv[1]
    idle = float(sys.argv[2]) if len(sys.argv) > 2 else IDLE_TIMEOUT

    # Already serving? Redundant spawn — exit before the expensive load.
    # (probe_live also clears a stale endpoint left by a dead daemon.)
    if daemon_ipc.probe_live(sock_path):
        return

    # encoding is explicit: the index carries Unicode (σ, ᵐ, ∀) from Lean docstrings,
    # and Windows would otherwise decode it with the ANSI code page and crash.
    with open(META, encoding="utf-8") as fh:
        meta = json.load(fh)
    view = meta.get("passage", "nbr")
    with open(INDEX, encoding="utf-8") as fh:
        ents = json.load(fh)["entries"]
    by = {e["name"]: e for e in ents}
    ctx = build_nbr_ctx(ents)
    passages = {n: make_passage(e, view, ctx) for n, e in by.items()}  # precompute once
    model = load_ce(meta["model"])  # ~10 s, once
    try:
        srv = daemon_ipc.serve(sock_path, backlog=16, idle=idle)
    except daemon_ipc.DaemonAlreadyRunning:
        return  # another daemon claimed the endpoint while we were loading
    print(f"rerank_daemon ready on {sock_path} (view={view}, {len(passages)} decls)", file=sys.stderr)

    while True:
        try:
            conn = srv.accept()
        except socket.timeout:
            break
        if conn is None:
            continue  # peer failed the endpoint token check
        try:
            raw = recv_line(conn).decode("utf-8").strip()
            if not raw:  # health-check
                conn.sendall(struct.pack("<i", 0))
                conn.close()
                continue
            req = json.loads(raw)
            query = req.get("query", "")
            names = req.get("names", [])
            if names:
                pairs = [[query, passages.get(n, humanize(n))] for n in names]
                scores = np.asarray(model.predict(pairs, batch_size=64, show_progress_bar=False), dtype=np.float32)
            else:
                scores = np.zeros((0,), dtype=np.float32)
            conn.sendall(struct.pack("<i", len(scores)))
            conn.sendall(scores.tobytes())
        except Exception as e:  # noqa: BLE001 — never crash on one bad request
            print(f"rerank_daemon request error: {e}", file=sys.stderr)
            try:
                conn.sendall(struct.pack("<i", -1))
            except OSError:
                pass
        finally:
            try:
                conn.close()
            except OSError:
                pass

    srv.close()
    srv.unlink()  # idle exit: release the endpoint, but only if it is still ours


if __name__ == "__main__":
    main()
