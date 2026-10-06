# tools/scripts/embed_library.py
#
# Embed the Causalean library declarations into vectors for the semantic retrieval tier.
#
# MULTI-VIEW (Phase 1 of the retrieval-v2 plan): each decl can be embedded under several
# complementary "views", stored in separate sidecars, and the tier scores a query by the
# MAX cosine over the available views (so a view only ever helps). Views:
#   nl   : humanized name + first doc paragraph        (the original signal; default paths)
#   stmt : the Lean statement (type structure)         → library_embeddings.stmt.{f32,meta.json}
#   nbr  : name + doc + dependency-graph NEIGHBOURHOOD  → library_embeddings.nbr.{f32,meta.json}
#          (humanized names of `refs` + reverse-refs — gives word-poor decls far more
#           surface vocabulary, directly attacking the vocabulary-mismatch "gap" stratum)
#
# Usage: python embed_library.py [--view nl|stmt|nbr|all] [--allow-full] [--max-embed N]
#                                [--index PATH] [--out-dir DIR] [--batch-size N] [--model-path M]
# `all` embeds every view in DEFAULT_VIEWS in ONE process: the index is parsed once and the
# model is imported and loaded at most once. Each view is still encoded by its own `encode`
# call, so its vectors are bit-identical to a single-view run over the same inputs.
# The `nl` view keeps the original unsuffixed paths.
#
# Cost discipline: `sentence_transformers` is imported and the model loaded only when some
# requested view has a declaration to embed; a view whose vectors are all cached keeps its
# .f32 untouched, and its meta is rewritten only when a recorded field changes.
#
# Reuse rule: a view's stored rows are reused only when its meta names the same model, records
# the fingerprint of the weights on disk, and records the content hash of the .f32 next to it.
# Anything else means every declaration of that view needs embedding.
#
# Refusal rule: embedding more than --max-embed declarations in a view takes hours on CPU, so
# without --allow-full the script says why, prints the command, and exits REFUSED before loading
# the model or writing anything. A deliberate full run belongs outside the live doc/ dir:
# `--view all --allow-full --index <snapshot> --out-dir <scratch>` on a GPU node, then move the
# four files into doc/.
import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")        # cluster is offline; load cached weights only
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
import json, hashlib, re, sys, argparse
import numpy as np

DEFAULT_VIEWS = ["nl", "nbr"]  # the views `npm run embed:library` maintains and `lint:embeddings` checks
FP_KEY = "weights_fingerprint"   # meta key: identity of the weights that built the rows
F32_KEY = "f32_sha256"           # meta key: content hash of the vector file the meta describes
MAX_EMBED = 2000                 # per-view ceiling on declarations embedded without --allow-full
REFUSED = 3                      # exit code of the refusal rule
FULL_CMD = ("`npm run embed:library -- --allow-full` (hours on CPU; for a GPU run outside doc/ add "
            "`--index <snapshot> --out-dir <scratch>`)")

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))  # tools/scripts -> repo root = Causalean pkg
INDEX = os.path.join(ROOT, "doc", "library_index.json")
MODEL = "BAAI/bge-large-en-v1.5"   # cached locally (1024-dim); offline-safe. bge needs CLS pooling (below).

MAX_NEIGHBORS = 16  # cap neighbourhood terms so the text stays within the model's context window


def paths(view, out_dir=None):
    """(f32, meta) sidecar paths for a view, in `out_dir` (default: the repo's doc/).
    `nl` keeps the original unsuffixed paths."""
    suffix = "" if view == "nl" else f".{view}"
    d = out_dir or os.path.join(ROOT, "doc")
    return (os.path.join(d, f"library_embeddings{suffix}.f32"),
            os.path.join(d, f"library_embeddings{suffix}.meta.json"))


def humanize(name: str) -> str:
    tail = name.split(".")[-1]
    parts = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", tail).replace("_", " ")
    return parts.strip()


def strip_nl_crosslinks(s):
    # NL↔Lean crosslink markup — `[phrase](hyp:name[,name…])` / `[phrase](goal)` / `[phrase](step:N)`
    # — is a site-only rendering concern; embed the phrase text alone so
    # annotating a docstring does not perturb its embedding. Walks BACK from
    # each closer to the matching `[` counting nesting, so a phrase may itself
    # contain balanced brackets. Mirrors src/shared/nl_crosslinks.ts.
    # Brackets inside code/math spans are content, not structure — neutralize
    # them in a same-length masked copy, scan that, slice the original.
    masked = re.sub(
        r"`[^`\n]+`|\$[^$\n]+\$",
        lambda m: m.group(0).replace("[", "•").replace("]", "•"),
        s,
    )
    out, plain_start = [], 0
    for m in re.finditer(r"\]\((?:hyp:[^()\s]+|goal|step:\d+)\)", masked):
        depth, opener = 0, -1
        for i in range(m.start() - 1, plain_start - 1, -1):
            c = masked[i]
            if c == "]":
                depth += 1
            elif c == "[":
                if depth == 0:
                    opener = i
                    break
                depth -= 1
        if opener < 0:
            continue
        out.append(s[plain_start:opener])
        out.append(s[opener + 1:m.start()])
        plain_start = m.end()
    out.append(s[plain_start:])
    return "".join(out)


def first_para(doc):
    return strip_nl_crosslinks((doc or "").split("\n\n")[0]).strip()


def nl_text(e, _ctx):
    head = humanize(e["name"])
    body = first_para(e.get("doc")) or (e.get("statement") or "")
    return f"{head}. {body}".strip()


def stmt_text(e, _ctx):
    # Lean statement, whitespace-collapsed. Light name context helps the encoder anchor a
    # word-poor type. (Full conclusion/hypothesis normalization is a later enhancement.)
    stmt = re.sub(r"\s+", " ", (e.get("statement") or "")).strip()
    return f"{humanize(e['name'])}. {stmt}".strip(". ").strip() or humanize(e["name"])


def nbr_text(e, ctx):
    # name + doc + humanized names of dependency-graph neighbours (refs = what it is built on,
    # reverse-refs = what uses it). Distinct neighbour words give a terse decl the vocabulary a
    # gap-stratum query shares with it even when its own name/doc do not.
    rev = ctx["rev"]
    present = ctx["present"]
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


BUILDERS = {"nl": nl_text, "stmt": stmt_text, "nbr": nbr_text}


def resolve_model_dir(model_id):
    """A repo-relative model dir (e.g. `doc/retrieval_model_ft`, as stored in the meta) is
    resolved against ROOT; an absolute path or HF name is returned as-is."""
    cand = model_id if os.path.isabs(model_id) else os.path.join(ROOT, model_id)
    return cand if os.path.isdir(cand) and os.path.exists(os.path.join(cand, "modules.json")) else model_id


def load_st_model(model_id):
    """A saved SentenceTransformer dir (e.g. the fine-tuned encoder) carries its own pooling
    config; a raw HF checkpoint (bge) needs CLS pooling set explicitly."""
    from sentence_transformers import SentenceTransformer, models
    resolved = resolve_model_dir(model_id)
    if os.path.isdir(resolved) and os.path.exists(os.path.join(resolved, "modules.json")):
        return SentenceTransformer(resolved)
    word = models.Transformer(resolved)
    pool = models.Pooling(word.get_word_embedding_dimension(), pooling_mode_cls_token=True, pooling_mode_mean_tokens=False)
    return SentenceTransformer(modules=[word, pool])


_FP_CHUNK = 1 << 20   # bytes hashed per sample
_FP_SAMPLES = 16      # evenly spaced samples per large file
# The files that determine an encoding: weights, and the model / tokenizer / pooling configs.
_FP_FILES = sorted([
    "model.safetensors", "pytorch_model.bin",
    "config.json", "modules.json", "config_sentence_transformers.json", "sentence_bert_config.json",
    "tokenizer.json", "tokenizer_config.json", "special_tokens_map.json", "added_tokens.json",
    "vocab.txt", "sentencepiece.bpe.model", "spiece.model",
])
_fp_memo = {}


def weights_fingerprint(model_id):
    """Identity of the weights behind `model_id`, or None when no such model dir exists on this
    machine (a hub name, or a repo-relative dir that is absent here).

    Hashes only _FP_FILES, in the model dir and in the module subdirs its modules.json lists
    (e.g. `1_Pooling`, `2_Dense`): relative path, size, and content — whole for files up to
    _FP_SAMPLES chunks, else _FP_SAMPLES evenly spaced 1 MiB samples including the head and the
    tail. Retraining rewrites the weight tensors throughout, so the samples change; copying,
    moving or symlinking the dir, and stray files inside it, do not. Reads ~16 MiB of a 1.3 GB
    checkpoint. A dangling symlink among the hashed paths is an error."""
    if model_id in _fp_memo:
        return _fp_memo[model_id]
    d = model_id if os.path.isabs(model_id) else os.path.join(ROOT, model_id)

    def need(path):
        if os.path.lexists(path) and not os.path.exists(path):
            sys.exit(f"embed_library: dangling symlink in model dir: {path}")
        return os.path.exists(path)

    fp = None
    if model_id and need(d) and os.path.isdir(d):
        subdirs = {""}
        if need(os.path.join(d, "modules.json")):
            with open(os.path.join(d, "modules.json"), encoding="utf-8") as fh:
                subdirs |= {m.get("path") or "" for m in json.load(fh)}
        h = hashlib.sha256()
        for sub in sorted(subdirs):
            if not (need(os.path.join(d, sub)) and os.path.isdir(os.path.join(d, sub))):
                continue
            for name in _FP_FILES:
                f = os.path.join(d, sub, name)
                if not need(f) or not os.path.isfile(f):
                    continue
                size = os.path.getsize(f)
                h.update(f"{sub}/{name}\0{size}\0".encode())
                with open(f, "rb") as fh:
                    if size <= _FP_CHUNK * _FP_SAMPLES:
                        h.update(fh.read())
                    else:
                        for i in range(_FP_SAMPLES):
                            fh.seek((size - _FP_CHUNK) * i // (_FP_SAMPLES - 1))
                            h.update(fh.read(_FP_CHUNK))
        fp = "sha256s:" + h.hexdigest()
    _fp_memo[model_id] = fp
    return fp


def file_sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def default_model(out_dir=None):
    """The model that built the current embeddings (so `embed:library` refreshes stay on the
    fine-tuned encoder); falls back to the base bge name when no embeddings exist yet."""
    for d in ([out_dir] if out_dir else []) + [None]:
        try:
            with open(paths("nl", d)[1], encoding="utf-8") as fh:
                model = json.load(fh).get("model")
            if model:
                return model
        except Exception:
            pass
    return MODEL


def build_context(ents):
    present = {e["name"] for e in ents}
    rev = {}
    for e in ents:
        for r in e.get("refs", []) or []:
            if r in present and r != e["name"]:
                rev.setdefault(r, []).append(e["name"])
    return {"present": present, "rev": rev}


def stored_rows(view, f32, meta_path, model_id=None):
    """Whether the stored rows of `view` can be trusted: (meta, reason, fingerprint).

    `reason` is None when they can, else a short phrase saying why not; `meta` is the parsed
    meta when it is well formed, else None; `fingerprint` is that of the weights on disk (None
    when the model dir is absent here, in which case the recorded one cannot be checked and is
    taken on trust). `model_id` None means "the model the meta names" (the lint's question)."""
    fp = weights_fingerprint(model_id) if model_id else None
    if not os.path.exists(meta_path) and not os.path.exists(f32):
        return None, "cold start: no stored vectors", fp
    if not os.path.exists(meta_path):
        return None, "the meta file is missing", fp
    if not os.path.exists(f32):
        return None, "the .f32 file is missing", fp
    try:
        with open(meta_path, encoding="utf-8") as fh:
            old = json.load(fh)
        names, hashes, dim = old["names"], old["hashes"], old["dim"]
        ok = (isinstance(names, list) and isinstance(hashes, list) and len(names) == len(hashes)
              and isinstance(dim, int) and dim > 0 and isinstance(old["model"], str)
              and old.get("view", "nl") == view)
    except Exception:
        ok = False
    if not ok:
        return None, "the meta is unreadable or from another schema", fp
    if model_id and old["model"] != model_id:
        return old, f"model string changed ({old['model']} → {model_id})", fp
    fp = weights_fingerprint(old["model"])
    if not isinstance(old.get(FP_KEY), str):
        return old, "the meta records no weights fingerprint", fp
    if fp is not None and old[FP_KEY] != fp:
        return old, f"weights fingerprint mismatch at {old['model']} (the model was retrained or replaced)", fp
    if os.path.getsize(f32) != len(names) * dim * 4:
        return old, "the .f32 and its meta disagree (row count)", fp
    if old.get(F32_KEY) != file_sha256(f32):
        return old, "the .f32 and its meta disagree (content hash)", fp
    return old, None, fp


def plan_view(view, ents, ctx, model_id, index_commit, out_dir):
    """Decide what `view` needs, without touching the model: `reuse` maps a declaration to its
    row in the stored .f32, `todo` lists the declarations to encode, `reason` says why the
    stored rows are unusable (None when they are usable)."""
    f32, meta_path = paths(view, out_dir)
    builder = BUILDERS[view]
    texts = {e["name"]: builder(e, ctx) for e in ents}
    names = list(texts.keys())
    hashes = [hashlib.sha1(texts[n].encode()).hexdigest() for n in names]
    old, reason, fp = stored_rows(view, f32, meta_path, model_id)
    reuse = {}
    if reason is None:
        cur = dict(zip(names, hashes))
        reuse = {n: i for i, n in enumerate(old["names"]) if old["hashes"][i] == cur.get(n)}
    todo = [n for n in names if n not in reuse]
    if fp is None:
        # no model dir here: keep the recorded identity; a model loaded by hub name is its own
        recorded = (old or {}).get(FP_KEY)
        fp = recorded if isinstance(recorded, str) and reason is None else f"hub:{model_id}"
        if reason is None:
            print(f"[view={view}] model dir {model_id} is not on this machine: recorded weights fingerprint "
                  f"kept, not verified", file=sys.stderr)
    meta = {"model": model_id, "view": view, "dim": old["dim"] if reuse else None, "count": len(names),
            "index_commit": index_commit, "names": names, "hashes": hashes, FP_KEY: fp,
            F32_KEY: old.get(F32_KEY) if reason is None else None}
    # the vector file is already exactly what a rewrite would produce
    f32_current = reason is None and not todo and old["names"] == names
    return {"view": view, "f32": f32, "meta_path": meta_path, "texts": texts, "names": names, "old": old,
            "reason": reason, "reuse": reuse, "todo": todo, "meta": meta, "f32_current": f32_current}


def write_view(p, vecs):
    """Write the view's pair. Both files are staged next to their targets and then renamed,
    .f32 first, so a reader never sees a partial file; a crash between the two renames leaves
    a pair whose recorded F32_KEY does not match, which `stored_rows` rejects."""
    view, meta = p["view"], p["meta"]
    staged = []
    if not p["f32_current"]:
        old_mat = None
        if p["reuse"]:
            old_mat = np.fromfile(p["f32"], dtype=np.float32).reshape(-1, p["old"]["dim"])
        dim = old_mat.shape[1] if old_mat is not None else vecs[p["todo"][0]].shape[0]
        mat = np.zeros((len(p["names"]), dim), dtype=np.float32)
        for i, n in enumerate(p["names"]):
            mat[i] = old_mat[p["reuse"][n]] if n in p["reuse"] else vecs[n]
        meta["dim"] = int(dim)
        meta[F32_KEY] = hashlib.sha256(mat.data).hexdigest()
        mat.tofile(p["f32"] + ".tmp")
        staged.append(p["f32"])
    if meta != p["old"]:
        with open(p["meta_path"] + ".tmp", "w", encoding="utf-8") as fh:
            json.dump(meta, fh)
        staged.append(p["meta_path"])
    for path in staged:
        os.replace(path + ".tmp", path)
        print(f"[view={view}] wrote {path}", file=sys.stderr)
    if not staged:
        print(f"[view={view}] up to date; nothing written", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--view", default="nl", choices=sorted(BUILDERS.keys()) + ["all"])
    ap.add_argument("--model-path", default=None, help="HF name or model dir (default: the model that built the current embeddings)")
    ap.add_argument("--index", default=INDEX, help="library index to embed (default: doc/library_index.json)")
    ap.add_argument("--out-dir", default=None, help="directory holding the library_embeddings.* files (default: doc/)")
    ap.add_argument("--max-embed", type=int, default=MAX_EMBED, help="per-view ceiling on declarations embedded without --allow-full")
    ap.add_argument("--allow-full", action="store_true", help="permit embedding more than --max-embed declarations")
    ap.add_argument("--batch-size", type=int, default=32)
    args = ap.parse_args()
    views = DEFAULT_VIEWS if args.view == "all" else [args.view]
    model_id = args.model_path or default_model(args.out_dir)

    # encoding is explicit: the index carries Unicode from Lean docstrings, which
    # Windows would otherwise decode with the ANSI code page and crash on.
    with open(args.index, encoding="utf-8") as fh:
        lib = json.load(fh)
    ents = lib["entries"]
    if not ents:
        print("index has no entries; nothing to embed", file=sys.stderr)
        return 0
    ctx = build_context(ents)

    plans = [plan_view(v, ents, ctx, model_id, lib.get("commit"), args.out_dir) for v in views]
    for p in plans:
        print(f"[view={p['view']}] {len(ents)} decls; reusing {len(p['reuse'])} cached, embedding {len(p['todo'])}", file=sys.stderr)
    over = [p for p in plans if len(p["todo"]) > args.max_embed]
    if over and not args.allow_full:
        for p in over:
            print(f"REFUSED [view={p['view']}]: {len(p['todo'])} declarations to embed (limit {args.max_embed}) — "
                  f"{p['reason'] or 'that many are new or changed'}. Nothing loaded or written. "
                  f"To do it deliberately: {FULL_CMD}", file=sys.stderr)
        return REFUSED

    model = None
    for p in plans:
        vecs = {}
        if p["todo"]:
            if model is None:
                model = load_st_model(model_id)
                print(f"model {model_id} on device {model.device}, batch size {args.batch_size}", file=sys.stderr)
            emb = model.encode([p["texts"][n] for n in p["todo"]], normalize_embeddings=True,
                               batch_size=args.batch_size, show_progress_bar=True)
            for n, v in zip(p["todo"], emb):
                vecs[n] = np.asarray(v, dtype=np.float32)
        write_view(p, vecs)
    return 0


if __name__ == "__main__":
    sys.exit(main())
