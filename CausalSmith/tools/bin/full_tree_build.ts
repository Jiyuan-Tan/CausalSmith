#!/usr/bin/env -S npx tsx
// `npm run build:full-tree` — sweep every CausalSmith module, including the research
// modules outside the root import graph that a plain `lake build` never reaches.
//
// A launcher for `scripts/full_tree_build.sh` rather than `bash scripts/…` in the npm
// script itself: npm runs scripts through cmd.exe on Windows, where Git for Windows
// puts no `bash.exe` on PATH and `C:\Windows\System32\bash.exe` is the WSL launcher —
// which sees a different filesystem entirely and would sweep a tree that is not there.
// `bashBinary()` resolves the configured git-bash; the script body itself is portable.
import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { bashBinary } from "../src/local_config.js";

const TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const SCRIPT = path.join(TOOLS_ROOT, "scripts", "full_tree_build.sh");

const result = spawnSync(
  bashBinary(),
  // Forward slashes: git-bash accepts them on Windows, backslashes it would escape.
  [SCRIPT.split(path.sep).join("/")],
  { cwd: TOOLS_ROOT, stdio: "inherit" },
);

// A spawn that never started reports `error`, not a status — the commonest case being
// no git-bash on Windows. Say so instead of exiting 1 with an empty console.
if (result.error) {
  console.error(`build:full-tree: could not launch ${bashBinary()}: ${result.error.message}`);
  process.exit(1);
}

process.exit(result.status ?? 1);
