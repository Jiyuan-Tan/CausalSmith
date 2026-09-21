#!/usr/bin/env bash
# Download the fine-tuned retrieval models (gitignored weight directories, ~2.4 GB) that
# power `npm run search --semantic` and `npm run embed:library`:
#   doc/retrieval_model_ft       bi-encoder (BAAI/bge-large-en-v1.5 fine-tune)
#   doc/retrieval_reranker_ft    cross-encoder reranker (BAAI/bge-reranker-base fine-tune)
# They are published, with a model card, at https://huggingface.co/jytan12/causalean-retrieval
# (retriever at the repository root, reranker under reranker/). Without them the tooling falls
# back to the off-the-shelf checkpoint (see README, "Retrieval tooling").
#
#   CAUSALEAN_MODELS_REV=<tag|branch|commit>   pin a revision (default: main). Revisions are
#                                              tagged with the library commit they were trained
#                                              against, e.g. causalean-c0073d5.
#   FORCE=1                                    replace directories that already exist.
#
# If Hugging Face cannot be reached, the script falls back to the older copies kept as release
# assets on the `build-cache` tag (that path needs tar and zstd); they are not refreshed on retrain.
set -euo pipefail
HF_REPO="${CAUSALEAN_MODELS_REPO:-jytan12/causalean-retrieval}"
HF_REV="${CAUSALEAN_MODELS_REV:-main}"
REPO="${CAUSALEAN_CACHE_REPO:-Jiyuan-Tan/CausalSmith}"
TAG="${CAUSALEAN_CACHE_TAG:-build-cache}"
BASE="https://github.com/$REPO/releases/download/$TAG"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/doc"
command -v curl >/dev/null || { echo "fetch_retrieval_models: curl is required" >&2; exit 1; }

want=()
for name in retrieval_model_ft retrieval_reranker_ft; do
  if [ -d "$name" ] && [ "${FORCE:-0}" != 1 ]; then
    echo "fetch_retrieval_models: doc/$name exists; skipping (FORCE=1 to replace)"
  else
    want+=("$name")
  fi
done
[ "${#want[@]}" -gt 0 ] || { echo "fetch_retrieval_models: nothing to do"; exit 0; }

tmp="$(mktemp -d "$ROOT/doc/.fetch_models.XXXXXX")"; trap 'rm -rf "$tmp"' EXIT

# The repository's file list, from the Hub API: every "path" that is not a directory.
hf_files() {
  local json="$tmp/tree.json"
  curl -fsSL --retry 3 -o "$json" "https://huggingface.co/api/models/$HF_REPO/tree/$HF_REV?recursive=true" || return 1
  grep -o '"path":"[^"]*"' "$json" | sed 's/^"path":"//; s/"$//' | sort > "$tmp/all.txt"
  grep -o '"type":"directory"[^}]*"path":"[^"]*"' "$json" | sed 's/.*"path":"//; s/"$//' | sort > "$tmp/dirs.txt"
  comm -23 "$tmp/all.txt" "$tmp/dirs.txt"
}

# Which repository paths belong to a model directory, and where they land inside it.
belongs() {  # <name> <repo path>  ->  prints the path inside doc/<name>, or fails
  case "$1:$2" in
    retrieval_reranker_ft:reranker/*) printf '%s\n' "${2#reranker/}" ;;
    retrieval_model_ft:reranker/*|retrieval_model_ft:README.md|retrieval_model_ft:.gitattributes) return 1 ;;
    retrieval_model_ft:*) printf '%s\n' "$2" ;;
    *) return 1 ;;
  esac
}

from_hub() {
  local files; files="$(hf_files)" || return 1
  [ -n "$files" ] || return 1
  for name in "${want[@]}"; do
    local n=0
    while IFS= read -r path; do
      local rel; rel="$(belongs "$name" "$path")" || continue
      mkdir -p "$tmp/$name/$(dirname "$rel")"
      echo "fetch_retrieval_models: $name/$rel"
      curl -fL --retry 3 -sS -o "$tmp/$name/$rel" "https://huggingface.co/$HF_REPO/resolve/$HF_REV/$path" || return 1
      n=$((n + 1))
    done <<<"$files"
    [ -f "$tmp/$name/config.json" ] && [ -f "$tmp/$name/model.safetensors" ] \
      || { echo "fetch_retrieval_models: $HF_REPO@$HF_REV has no complete $name" >&2; return 1; }
    echo "fetch_retrieval_models: $name: $n files from $HF_REPO@$HF_REV"
  done
  for name in "${want[@]}"; do rm -rf "$name"; mv "$tmp/$name" "$name"; done
}

from_release() {
  for tool in tar zstd; do
    command -v "$tool" >/dev/null || { echo "fetch_retrieval_models: $tool is required for the release fallback" >&2; return 1; }
  done
  for name in "${want[@]}"; do
    echo "fetch_retrieval_models: downloading $name.tar.zst from the $TAG release"
    curl -fL --retry 3 -o "$tmp/$name.tar.zst" "$BASE/$name.tar.zst" || return 1
    rm -rf "$name"
    tar --use-compress-program="zstd -d" -xf "$tmp/$name.tar.zst"
  done
}

if from_hub; then :
else
  echo "fetch_retrieval_models: Hugging Face download failed; falling back to the release assets (older models)" >&2
  from_release || { echo "fetch_retrieval_models: could not download the models" >&2; exit 1; }
fi
echo "fetch_retrieval_models: done; next: cd CausalSmith/tools && npm run embed:library"
