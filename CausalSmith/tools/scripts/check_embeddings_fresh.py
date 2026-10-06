import json, hashlib, sys, argparse
# reuse the exact per-view text logic and stored-row checks of the embedder
from embed_library import BUILDERS, INDEX, DEFAULT_VIEWS, FULL_CMD, paths, build_context, stored_rows

VIEWS = DEFAULT_VIEWS  # the views `npm run embed:library` produces


def check_view(view, ents, ctx, out_dir):
    f32, meta_path = paths(view, out_dir)
    # Rows the embedder would refuse to reuse are stale whatever the text hashes say.
    meta, reason, fingerprint = stored_rows(view, f32, meta_path)
    if reason:
        print(f"STALE embeddings [{view}]: {reason} — every declaration needs embedding: {FULL_CMD}", file=sys.stderr)
        return False
    builder = BUILDERS[view]
    cur = {e["name"]: hashlib.sha1(builder(e, ctx).encode()).hexdigest() for e in ents}
    old = dict(zip(meta["names"], meta["hashes"]))
    added = [n for n in cur if n not in old]
    removed = [n for n in old if n not in cur]
    changed = [n for n in cur if n in old and cur[n] != old[n]]
    if added or removed or changed:
        print(f"STALE embeddings [{view}]: +{len(added)} -{len(removed)} ~{len(changed)} vs meta "
              f"— run `npm run embed:library`", file=sys.stderr)
        for n in (added[:5] + removed[:5] + changed[:5]):
            print("  ", n, file=sys.stderr)
        return False
    weights = "" if fingerprint else f"; weights not verified — {meta['model']} is not on this machine"
    print(f"embeddings fresh [{view}] ({len(cur)} decls{weights})")
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--index", default=INDEX)
    ap.add_argument("--out-dir", default=None, help="directory holding the library_embeddings.* files (default: doc/)")
    args = ap.parse_args()
    with open(args.index, encoding="utf-8") as fh:
        ents = json.load(fh)["entries"]
    ctx = build_context(ents)
    results = [check_view(v, ents, ctx, args.out_dir) for v in VIEWS]  # eager: report every view, not just the first stale one
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
