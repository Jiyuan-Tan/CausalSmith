#!/usr/bin/env -S npx tsx
// `npm run lint:kb:strict` — run BOTH strict KB checks and fail if EITHER failed,
// rather than short-circuiting on the first.
//
// This is TypeScript because the npm script it replaces was POSIX shell
// (`… --strict; a=$?; … --strict; b=$?; exit $(( a || b ))`). npm runs scripts through
// cmd.exe on Windows, which cannot parse `a=$?` or `$(( ))` — so the lint did not
// merely report differently there, it could not run at all.
import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";

const TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
// Launched as `node <tsx cli>`: the `node_modules/.bin/tsx` shim is a `.cmd` on
// Windows, which spawnSync cannot launch without a shell.
const TSX_CLI = path.join(TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");

const CHECKS = ["check_bank_crosswalks.ts", "check_kb_consistency.ts"];

let failed = false;
for (const check of CHECKS) {
  const result = spawnSync(
    process.execPath,
    [TSX_CLI, path.join(TOOLS_ROOT, "bin", check), "--strict"],
    { cwd: TOOLS_ROOT, stdio: "inherit" },
  );
  // A spawn that never started reports `error`, not a status; without this the check
  // would count as failed with nothing on the console explaining why.
  if (result.error) {
    console.error(`lint:kb:strict: could not launch ${check}: ${result.error.message}`);
  }
  if (result.error || result.status !== 0) failed = true;
}

process.exit(failed ? 1 : 0);
