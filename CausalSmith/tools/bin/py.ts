#!/usr/bin/env -S npx tsx
/** Run one of the Python retrieval scripts with the interpreter this machine actually
 * has, forwarding stdio and the exit code.
 *
 * The npm scripts used to invoke `python3 scripts/…` directly, which cannot work on
 * Windows (no such program name). Routing them through here keeps ONE interpreter
 * resolver — src/shared/python.ts — shared with the TS call sites, so a `pythonPath`
 * set in local.json applies to `npm run embed:library` as much as to the pipeline.
 *
 * Usage: py.ts <script.py> [args…]
 */
import process from "node:process";
import { spawnSync } from "node:child_process";
import { pythonCommand } from "../src/shared/python.js";

const [script, ...rest] = process.argv.slice(2);
if (!script) {
  console.error("usage: py.ts <script.py> [args...]");
  process.exit(2);
}
const cmd = pythonCommand(); // throws with install guidance when no Python 3 is found
const res = spawnSync(cmd.bin, [...cmd.prefixArgs, script, ...rest], { stdio: "inherit" });
if (res.error) {
  console.error(`py.ts: failed to run ${cmd.bin}: ${res.error.message}`);
  process.exit(1);
}
process.exit(res.status ?? 1);
