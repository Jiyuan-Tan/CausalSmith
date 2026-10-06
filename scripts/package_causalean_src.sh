#!/usr/bin/env bash
# Package the Causalean library alone, for use without the CausalSmith pipeline: the library
# sources, its two vendored dependencies and the Lake files, from one commit.
#
#   scripts/package_causalean_src.sh [OUT.tar.zst] [REV]     # default: causalean-src-<sha>.tar.zst, HEAD
#
# The archive unpacks to `causalean/`. With the prebuilt oleans of the same commit
# (`scripts/fetch_build_cache.sh`, run inside it) the library is usable without compiling.
# CI publishes it next to the olean asset on the `build-cache` release.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REV="${2:-HEAD}"
SHA="$(git -C "$ROOT" rev-parse "$REV")"
OUT="${1:-causalean-src-$SHA.tar.zst}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
# Everything the root Lake package names: the library, the index executable's two roots, the
# vendored path dependencies, and the files the olean fetcher reads.
paths=()
for p in Causalean Causalean.lean LibraryIndex.lean LibraryIndexCore.lean third_party \
         lakefile.toml lake-manifest.json lean-toolchain .cache-epoch LICENSE NOTICE \
         scripts/fetch_build_cache.sh doc/API.md doc/TACTICS.md; do
  if git -C "$ROOT" cat-file -e "$SHA:$p" 2>/dev/null; then paths+=("$p"); fi
done
git -C "$ROOT" archive --format=tar --prefix=causalean/ "$SHA" -- "${paths[@]}" | tar -xf - -C "$tmp"
[ -f "$tmp/causalean/lakefile.toml" ] && [ -d "$tmp/causalean/Causalean" ] \
  || { echo "package_causalean_src: $SHA lacks the library or its Lake file" >&2; exit 1; }
printf '%s\n' "$SHA" > "$tmp/causalean/.source-commit"
cat > "$tmp/causalean/README.md" <<README
# Causalean

A Lean 4 library formalizing causal inference: graphs and d-separation, structural causal
models, potential outcomes, identification, partial identification, estimation theory,
experimental design and panel methods. This archive is the library alone, from commit
\`$SHA\` of https://github.com/Jiyuan-Tan/CausalSmith; the agentic research pipeline, the
papers and the website are in that repository.

    lake exe cache get              # Mathlib's prebuilt oleans
    scripts/fetch_build_cache.sh    # Causalean's prebuilt oleans for this commit
    lake build                      # should rebuild little or nothing

To depend on it from your own project, add to your \`lakefile.toml\`:

    [[require]]
    name = "Causalean"
    path = "path/to/causalean"

\`doc/API.md\` orients by module; every declaration's docstring opens with a plain-English
statement. Licensed under Apache 2.0 (see \`LICENSE\`, \`NOTICE\`); the two vendored libraries under
\`third_party/\` keep their own licenses.
README
tar -C "$tmp" -cf - causalean | zstd -q -T0 -19 -f -o "$OUT"
echo "package_causalean_src: $OUT ($(du -h "$OUT" | cut -f1), $(find "$tmp/causalean" -type f | wc -l) files)"
