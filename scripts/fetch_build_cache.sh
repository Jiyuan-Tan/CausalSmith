#!/usr/bin/env bash
# Download prebuilt oleans (GitHub release assets) so `lake build` is minutes, not hours.
# Safe to run at any commit: Lake trusts a cached object only when its recorded input
# hashes still match, so anything that differs from the cached commit is rebuilt and
# nothing stale is ever used.
#
#   lake exe cache get                     # Mathlib's cache first
#   scripts/fetch_build_cache.sh           # Causalean oleans -> .lake/build
#   lake build                             # now only the delta since the cached commit
#
# Optional: the Lean code of the existing CausalSmith papers. The pipeline does not need
# it to start a new run, so it is opt-in. The CausalSmith Lean project keeps its own
# copy of Mathlib, so fetch Mathlib's cache from inside that directory too:
#
#   (cd CausalSmith && lake exe cache get)
#   scripts/fetch_build_cache.sh --causalsmith   # CausalSmith oleans -> CausalSmith/.lake/build
#   lake -d CausalSmith build <run barrel>       # e.g. CausalSmith.Stat.STAT_Foo_Research
#
# --causalsmith fetches ONLY the CausalSmith archive; run the plain form first for Causalean.
#
# Assets live on the rolling release tag `build-cache` of the public repository:
#   causalean-build-<sha>.tar.zst        exact commit          (-> .lake/build)
#                                        plus the vendored packages' oleans
#                                        (-> third_party/<pkg>/.lake/build)
#   causalean-build-latest.tar.zst       newest main build (fallback)
#   causalean-build-latest.json          {sha, lean, cache_key, mathlib}
#   causalsmith-build-<sha>.tar.zst      exact commit          (-> CausalSmith/.lake/build)
#   causalsmith-build-latest.tar.zst     newest main build (fallback)
#   causalsmith-build-latest.json        {sha, lean, cache_key, mathlib, complete}
#
# A CausalSmith archive with "complete": false came from a CI build that hit its time
# limit or a module error. CI strips every module it did not finish, so the archive holds
# only fully built modules; lake builds the rest.
#
# Manual check: after changing the cache-key inputs, point CAUSALEAN_CACHE_REPO
# at a release with the old `cache_key`; this script must refuse its latest
# fallback before extracting the archive.
set -euo pipefail
REPO="${CAUSALEAN_CACHE_REPO:-Jiyuan-Tan/CausalSmith}"
TAG="${CAUSALEAN_CACHE_TAG:-build-cache}"
BASE="https://github.com/$REPO/releases/download/$TAG"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

WITH_CAUSALSMITH=0
for arg in "$@"; do
  case "$arg" in
    --causalsmith) WITH_CAUSALSMITH=1 ;;
    -h|--help) sed -n '2,35p' "$0"; exit 0 ;;
    *) echo "fetch_build_cache: unknown argument $arg (usage: fetch_build_cache.sh [--causalsmith])" >&2; exit 2 ;;
  esac
done

for tool in curl tar zstd; do
  command -v "$tool" >/dev/null || { echo "fetch_build_cache: $tool is required" >&2; exit 1; }
done

sha="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
lean="$(tr -d '[:space:]' < lean-toolchain)"
cache_key="${lean}-$(sha256sum .cache-epoch | cut -d' ' -f1)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

fetch() { curl -fsSL --retry 3 -o "$2" "$1"; }
json_field() { sed -n "s/.*\"$1\": *\"\{0,1\}\([^\",}]*\)\"\{0,1\}.*/\1/p" "$2"; }

# fetch_archive <asset prefix> <destination .lake dir>
# Unpacks <prefix>-<sha> when published, else <prefix>-latest after checking that it was
# built with this checkout's toolchain and cache epoch.
fetch_archive() {
  local prefix="$1" dest="$2"
  rm -f "$tmp/build.tar.zst" "$tmp/latest.json"
  if fetch "$BASE/$prefix-$sha.tar.zst" "$tmp/build.tar.zst" 2>/dev/null; then
    echo "fetch_build_cache: $prefix: exact build for $sha"
  else
    fetch "$BASE/$prefix-latest.json" "$tmp/latest.json" \
      || { echo "fetch_build_cache: $prefix: no build cache published at $BASE" >&2; return 1; }
    local cached_sha cached_lean cached_cache_key
    cached_sha="$(json_field sha "$tmp/latest.json")"
    cached_lean="$(json_field lean "$tmp/latest.json")"
    cached_cache_key="$(json_field cache_key "$tmp/latest.json")"
    if [ "$cached_lean" != "$lean" ]; then
      echo "fetch_build_cache: $prefix: latest cache was built with $cached_lean but this checkout pins $lean; refusing (a toolchain change invalidates every olean)" >&2
      return 1
    fi
    if [ "$cached_cache_key" != "$cache_key" ]; then
      echo "fetch_build_cache: $prefix: latest cache key $cached_cache_key does not match this checkout's $cache_key; refusing (a cache epoch change invalidates every olean)" >&2
      return 1
    fi
    echo "fetch_build_cache: $prefix: no exact build for $sha; using latest ($cached_sha) — lake rebuilds the delta"
    if [ "$(json_field complete "$tmp/latest.json")" = "false" ]; then
      echo "fetch_build_cache: $prefix: note — this archive is a partial CI build; lake builds the missing modules" >&2
    fi
    fetch "$BASE/$prefix-latest.tar.zst" "$tmp/build.tar.zst"
  fi
  mkdir -p "$dest"
  # The archive holds `build/`; extracting over an existing tree is fine (same-commit
  # objects are byte-identical, others get rebuilt by their traces).
  tar --use-compress-program="zstd -d" -xf "$tmp/build.tar.zst" -C "$dest"
  # The Causalean archive also carries the vendored packages' oleans as vendored/<pkg>/build.
  # Lake keeps a path dependency's outputs in that package's own .lake, so without them the
  # vendored code is recompiled and every Causalean module above it rebuilds.
  if [ -d "$dest/vendored" ]; then
    for v in "$dest"/vendored/*/build; do
      [ -d "$v" ] || continue
      pkg="$(basename "$(dirname "$v")")"
      [ -d "third_party/$pkg" ] || continue
      mkdir -p "third_party/$pkg/.lake"
      rm -rf "third_party/$pkg/.lake/build"
      mv "$v" "third_party/$pkg/.lake/build"
      echo "fetch_build_cache: $prefix: placed vendored $pkg oleans in third_party/$pkg/.lake/build"
    done
    rm -rf "$dest/vendored"
  fi
  echo "fetch_build_cache: $prefix: unpacked $(find "$dest/build/lib" -name '*.olean' | wc -l) oleans into $dest/build"
}

if [ "$WITH_CAUSALSMITH" -eq 1 ]; then
  fetch_archive causalsmith-build CausalSmith/.lake
  echo "fetch_build_cache: next: (cd CausalSmith && lake exe cache get), then lake -d CausalSmith build <run barrel>"
else
  fetch_archive causalean-build .lake
  echo "fetch_build_cache: next: lake build"
fi
