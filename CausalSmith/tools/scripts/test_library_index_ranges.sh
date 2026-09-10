#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
fixture_dir="$repo_root/CausalSmith/tools/test/fixtures/library_index"
probe_tmp="$(mktemp -d /tmp/library-index-integration-probe.XXXXXX)"
trap 'rm -rf "$probe_tmp"' EXIT

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

python3 - "$probe_tmp/index.json" <<'PY'
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
