#!/usr/bin/env bash
# Download the prebuilt Causalean oleans (a GitHub release asset) into .lake/build so
# `lake build` is minutes, not hours. Safe to run at any commit: Lake trusts a cached
# object only when its recorded input hashes still match, so anything that differs from
# the cached commit is rebuilt and nothing stale is ever used.
#
#   lake exe cache get          # Mathlib's cache first
#   scripts/fetch_build_cache.sh
#   lake build                  # now only the delta since the cached commit
#
# Assets live on the rolling release tag `build-cache` of the public repository:
#   causalean-build-<sha>.tar.zst      exact commit
#   causalean-build-latest.tar.zst     newest main build (fallback)
#   causalean-build-latest.json        {sha, lean, mathlib}
set -euo pipefail
REPO="${CAUSALEAN_CACHE_REPO:-Jiyuan-Tan/CausalSmith}"
TAG="${CAUSALEAN_CACHE_TAG:-build-cache}"
BASE="https://github.com/$REPO/releases/download/$TAG"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
for tool in curl tar zstd; do
  command -v "$tool" >/dev/null || { echo "fetch_build_cache: $tool is required" >&2; exit 1; }
done

sha="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
lean="$(tr -d '[:space:]' < lean-toolchain)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

fetch() { curl -fsSL --retry 3 -o "$2" "$1"; }

if fetch "$BASE/causalean-build-$sha.tar.zst" "$tmp/build.tar.zst" 2>/dev/null; then
  echo "fetch_build_cache: exact build for $sha"
else
  fetch "$BASE/causalean-build-latest.json" "$tmp/latest.json" \
    || { echo "fetch_build_cache: no build cache published at $BASE" >&2; exit 1; }
  cached_sha="$(sed -n 's/.*"sha": *"\([0-9a-f]*\)".*/\1/p' "$tmp/latest.json")"
  cached_lean="$(sed -n 's/.*"lean": *"\([^"]*\)".*/\1/p' "$tmp/latest.json")"
  if [ "$cached_lean" != "$lean" ]; then
    echo "fetch_build_cache: latest cache was built with $cached_lean but this checkout pins $lean; refusing (a toolchain change invalidates every olean)" >&2
    exit 1
  fi
  echo "fetch_build_cache: no exact build for $sha; using latest ($cached_sha) — lake rebuilds the delta"
  fetch "$BASE/causalean-build-latest.tar.zst" "$tmp/build.tar.zst"
fi

mkdir -p .lake
# The archive holds `build/`; extracting over an existing tree is fine (same-commit
# objects are byte-identical, others get rebuilt by their traces).
tar --use-compress-program=unzstd -xf "$tmp/build.tar.zst" -C .lake
echo "fetch_build_cache: unpacked $(find .lake/build/lib -name '*.olean' | wc -l) oleans into .lake/build; run: lake build"
