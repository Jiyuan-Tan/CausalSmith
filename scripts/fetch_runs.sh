#!/usr/bin/env bash
# Download run records from the run-record dataset and unpack them where the pipeline keeps them.
# The repository carries only a one-file summary per shelved run; the raw records (stage logs,
# derivation history, reviews, topic-selection rounds, study records) live in the dataset
# https://huggingface.co/datasets/jytan12/causalsmith-runs as one archive per run.
#
#   scripts/fetch_runs.sh --list                 # what is available
#   scripts/fetch_runs.sh accepted               # every run of a group
#   scripts/fetch_runs.sh failed/<id> study/<slug> topics/<round>
#   scripts/fetch_runs.sh --all
#
# Groups: accepted, downgraded, failed (-> CausalSmith/doc/research/_bank/<group>/<id>/),
# study (-> CausalSmith/doc/study/<slug>/), topics (-> CausalSmith/doc/research/_topics/...).
# Each archive is checked against the sha256 in CausalSmith/doc/research/run_archive_manifest.jsonl.
# Files already present are kept unless FORCE=1. Machine paths and operator identities in the
# records are replaced by placeholders such as <repo-root>.
#
#   CAUSALSMITH_RUNS_REPO=<owner/name>   another dataset (default: jytan12/causalsmith-runs)
#   CAUSALSMITH_RUNS_REV=<revision>      pin a dataset revision (default: main)
#   HF_TOKEN=<token>                     needed only while the dataset is private
#
# Runs on Linux, macOS (its stock bash 3.2 and BSD tools) and Windows under Git Bash; needs curl,
# tar and zstd.
set -euo pipefail
HF_REPO="${CAUSALSMITH_RUNS_REPO:-jytan12/causalsmith-runs}"
HF_REV="${CAUSALSMITH_RUNS_REV:-main}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RESEARCH="$ROOT/CausalSmith/doc/research"
MANIFEST="$RESEARCH/run_archive_manifest.jsonl"
for tool in curl tar zstd; do
  command -v "$tool" >/dev/null || { echo "fetch_runs: $tool is required" >&2; exit 1; }
done
if command -v sha256sum >/dev/null; then sha256() { sha256sum "$1" | cut -d' ' -f1; }
elif command -v shasum >/dev/null; then sha256() { shasum -a 256 "$1" | cut -d' ' -f1; }
else echo "fetch_runs: sha256sum or shasum is required" >&2; exit 1; fi
[ -f "$MANIFEST" ] || { echo "fetch_runs: missing $MANIFEST" >&2; exit 1; }
[ $# -gt 0 ] || { sed -n '2,23p' "$0" | sed 's/^# \{0,1\}//'; exit 1; }
BASE="https://huggingface.co/datasets/$HF_REPO/resolve/$HF_REV"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
tmp_rows="$tmp/rows"; : > "$tmp_rows"

# manifest rows as "<group>/<id> <sha256> <bytes>"
rows() { sed -E 's/.*"tier":"([^"]+)","id":"([^"]+)".*"sha256":"([0-9a-f]+)","bytes":([0-9]+).*/\1\/\2 \3 \4/' "$MANIFEST"; }

if [ "$1" = "--list" ]; then
  rows | awk '{split($1,a,"/"); n[a[1]]++; b[a[1]]+=$3} END{for (g in n) printf "%-11s %5d archives  %7.1f MB\n", g, n[g], b[g]/1e6}' | sort
  echo "name one as <group>/<id>; ids: grep -o '\"id\":\"[^\"]*\"' $MANIFEST"
  exit 0
fi

# The rows wanted, one per line (no arrays of rows: bash 3.2 has no mapfile).
want="$tmp_rows"
for arg in "$@"; do
  case "$arg" in
    --all) rows >> "$want" ;;
    */*)   rows | awk -v k="$arg" '$1==k' > "$want.one"
           [ -s "$want.one" ] || { echo "fetch_runs: no archive named $arg" >&2; exit 1; }
           cat "$want.one" >> "$want" ;;
    *)     rows | awk -v g="$arg" 'index($1, g "/")==1' > "$want.one"
           [ -s "$want.one" ] || { echo "fetch_runs: no archives in group $arg" >&2; exit 1; }
           cat "$want.one" >> "$want" ;;
  esac
done

dest_of() {  # <group> <id> -> parent directory and the directory name inside the archive
  case "$1" in
    accepted|downgraded|failed) echo "$RESEARCH/_bank/$1" ;;
    study) echo "$ROOT/CausalSmith/doc/study" ;;
    topics) case "$2" in *__*) echo "$RESEARCH/_topics/${2%%__*}" ;; *) echo "$RESEARCH/_topics" ;; esac ;;
    *) return 1 ;;
  esac
}

n=0
while read -r unit sha bytes; do
  group="${unit%%/*}"; id="${unit#*/}"
  # Names come from the manifest; refuse anything that could leave the target folders.
  case "$unit" in *..*|/*|*//*) echo "fetch_runs: unsafe archive name $unit" >&2; exit 1 ;; esac
  parent="$(dest_of "$group" "$id")" || { echo "fetch_runs: unknown group in $unit" >&2; exit 1; }
  arc="$tmp/a.tar.zst"; out="$tmp/x"; rm -rf "$out"; mkdir -p "$out"
  if [ -n "${HF_TOKEN:-}" ]; then
    curl -fL --retry 3 -sS -H "Authorization: Bearer $HF_TOKEN" -o "$arc" "$BASE/$unit.tar.zst"
  else
    curl -fL --retry 3 -sS -o "$arc" "$BASE/$unit.tar.zst"
  fi || { echo "fetch_runs: download failed for $unit (private dataset? set HF_TOKEN)" >&2; exit 1; }
  [ "$(sha256 "$arc")" = "$sha" ] || { echo "fetch_runs: checksum mismatch for $unit" >&2; exit 1; }
  # Unpack beside the download, then copy into place: `cp -n` keeps files that already exist on
  # GNU, BSD and Git Bash alike, where tar's own keep-existing flags differ.
  tar --use-compress-program="zstd -d" -xf "$arc" -C "$out"
  [ -z "$(find "$out" -type l -print | head -n 1)" ] || { echo "fetch_runs: $unit contains a symbolic link; refusing" >&2; exit 1; }
  mkdir -p "$parent"
  top="$(ls "$out" | head -n 1)"
  [ -n "$top" ] || { echo "fetch_runs: $unit unpacked to nothing" >&2; exit 1; }
  # Without FORCE, `cp -n` skips files that exist; some versions report that as a failure, so the
  # copy is judged by whether the run's folder is there afterwards.
  if [ "${FORCE:-0}" = 1 ]; then cp -R "$out"/. "$parent"/; else cp -Rn "$out"/. "$parent"/ 2>"$tmp/cp.err" || true; fi
  [ -d "$parent/$top" ] || { cat "$tmp/cp.err" >&2 2>/dev/null; echo "fetch_runs: could not write $parent/$top" >&2; exit 1; }
  n=$((n + 1)); echo "fetch_runs: $unit"
done < "$want"
echo "fetch_runs: $n archive(s) unpacked"
