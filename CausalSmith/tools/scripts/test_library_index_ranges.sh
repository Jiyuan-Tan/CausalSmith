#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
fixture_dir="$repo_root/CausalSmith/tools/test/fixtures/library_index"
probe_tmp="$(mktemp -d /tmp/library-index-integration-probe.XXXXXX)"
trap 'rm -rf "$probe_tmp"' EXIT

# `python3` is not a program name on Windows, and there it can also resolve to the
# App Store stub that exits without running anything — probe each candidate.
PY_BIN=""
for py in python3 python py; do
  if command -v "$py" >/dev/null 2>&1 && "$py" -c 'import sys; sys.exit(0 if sys.version_info[0] == 3 else 1)' >/dev/null 2>&1; then
    PY_BIN="$py"; break
  fi
done
[ -n "$PY_BIN" ] || { echo "test_library_index_ranges: no working python3 found" >&2; exit 1; }

mkdir -p "$probe_tmp/ExtractorRangeFixture"
cp "$fixture_dir/ExtractorFixtureBase.lean" "$probe_tmp/ExtractorRangeFixture/Base.lean"
cp "$fixture_dir/ExtractorFixtureExtension.lean" "$probe_tmp/ExtractorRangeFixture/Extension.lean"
cp "$fixture_dir/ExtractorFixtureDriver.lean" "$probe_tmp/ExtractorFixtureDriver.lean"

cd "$repo_root"
lake build LibraryIndexCore
lake env bash -c '
  set -euo pipefail
  probe_tmp="$1"
  lean -R "$probe_tmp" -o "$probe_tmp/ExtractorRangeFixture/Base.olean" "$probe_tmp/ExtractorRangeFixture/Base.lean"
  LEAN_PATH="$probe_tmp:$LEAN_PATH" lean -R "$probe_tmp" -o "$probe_tmp/ExtractorRangeFixture/Extension.olean" "$probe_tmp/ExtractorRangeFixture/Extension.lean"
  LEAN_PATH="$probe_tmp:$LEAN_PATH" lean -R "$probe_tmp" --run "$probe_tmp/ExtractorFixtureDriver.lean" "$probe_tmp" "$probe_tmp/index.json"
' bash "$probe_tmp"

"$PY_BIN" - "$probe_tmp/index.json" <<'PY'
import json
import sys

entries = json.load(open(sys.argv[1], encoding="utf-8"))["entries"]
names = {entry["name"] for entry in entries}
required = {
    "ExtractorRangeFixture.Alias",
    "ExtractorRangeFixture.Alias.authored",
    "ExtractorRangeFixture.Alias.extension",
    "ExtractorRangeFixture.recurse",
    "ExtractorRangeFixture.Direction",
    "ExtractorRangeFixture.instReprDirection",
    "ExtractorRangeFixture.DocumentedDirection",
    "ExtractorRangeFixture.instReprDocumentedDirection",
}
missing = sorted(required - names)
forbidden_prefixes = (
    "ExtractorRangeFixture.recurse.go",
    "ExtractorRangeFixture.instReprDirection.repr",
    "ExtractorRangeFixture.instReprDocumentedDirection.repr",
)
forbidden = sorted(name for name in names if name.startswith(forbidden_prefixes))
if missing or forbidden:
    raise SystemExit(f"extractor range probe failed: missing={missing}, forbidden={forbidden}")
print(f"extractor range probe passed: {len(entries)} entries; authored nested defs retained; generated workers omitted")
PY
