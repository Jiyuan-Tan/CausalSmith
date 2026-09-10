#!/usr/bin/env bash
# Download the fine-tuned retrieval models (gitignored weight directories, ~2.3 GB) that
# power `npm run search --semantic` and `npm run embed:library`:
#   doc/retrieval_model_ft       bi-encoder (BAAI/bge-large-en-v1.5 fine-tune)
#   doc/retrieval_reranker_ft    cross-encoder reranker
# Both are release assets on the `build-cache` tag. Without them the tooling falls back
# to the off-the-shelf checkpoint (see README, "Retrieval tooling").
set -euo pipefail
REPO="${CAUSALEAN_CACHE_REPO:-Jiyuan-Tan/CausalSmith}"
TAG="${CAUSALEAN_CACHE_TAG:-build-cache}"
BASE="https://github.com/$REPO/releases/download/$TAG"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/doc"
for tool in curl tar zstd; do
  command -v "$tool" >/dev/null || { echo "fetch_retrieval_models: $tool is required" >&2; exit 1; }
done
for name in retrieval_model_ft retrieval_reranker_ft; do
  if [ -d "$name" ] && [ "${FORCE:-0}" != 1 ]; then
    echo "fetch_retrieval_models: doc/$name exists; skipping (FORCE=1 to replace)"; continue
  fi
  echo "fetch_retrieval_models: downloading $name.tar.zst"
  curl -fL --retry 3 -o "$name.tar.zst" "$BASE/$name.tar.zst"
  rm -rf "$name"
  tar --use-compress-program=unzstd -xf "$name.tar.zst"
  rm -f "$name.tar.zst"
done
echo "fetch_retrieval_models: done; next: cd CausalSmith/tools && npm run embed:library"
