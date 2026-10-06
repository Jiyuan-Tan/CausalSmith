#!/usr/bin/env -S npx tsx
/**
 * The promotion gate: a promotion only adds to Causalean.
 *
 * Promotion copies a helper of a banked run into Causalean (stated generally where that is
 * faithful) and never edits the run: no declaration of the run is moved, deleted, restated or
 * re-proved, and no existing library declaration is changed. Banking at the accepted tier
 * (`bin/bank_entry.ts`) records a snapshot in the entry (`promotion_snapshot.json`). After the
 * promotion and a FULL build:
 *
 *   npm run promotion:invariance -- check --entry <bank entry dir>
 *
 * It exits 0 iff (1) the run's Lean files are byte-identical to what was banked, (2) every
 * declaration of the run states what it stated, and (3) every declaration outside the run that
 * the run's statements use states what it stated (`src/substrate/invariance.ts`). Declarations the
 * run's statements do not use are not compared. It exits 1 with one line per file or declaration,
 * each naming the next step, and never writes anything.
 *
 * `--entry` is the bank entry folder, `CausalSmith/doc/research/_bank/accepted/<qid>_<spec>`:
 * absolute, or relative to the repository root or to where the command is typed.
 *
 * An entry with no snapshot cannot be checked. The operator records one on the committed, not yet
 * promoted run (the verb refuses a run directory that differs from its commit, and an entry that
 * already has a snapshot):
 *
 *   npm run promotion:invariance -- snapshot --entry <bank entry dir>
 */
import process from "node:process";
import path from "node:path";
import { existsSync } from "node:fs";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { checkEntry, entryLeanDir, gitState, recordSnapshot } from "../src/substrate/invariance.js";

const USAGE = "usage: promotion_invariance check --entry <bank entry dir>\n"
  + "       promotion_invariance snapshot --entry <bank entry dir>";

/** `npm run` moves to `tools/`: relative paths are read from where the command was typed. */
const START = process.env.INIT_CWD ?? process.cwd();

async function main(): Promise<number> {
  const verb = process.argv[2];
  const i = process.argv.indexOf("--entry");
  const entryArg = i >= 0 ? process.argv[i + 1] : undefined;
  if (!entryArg || (verb !== "check" && verb !== "snapshot")) {
    console.log(USAGE);
    return verb === "--help" || verb === "-h" ? 0 : 2;
  }
  // The package this tool belongs to, wherever the command is typed.
  const pkgRoot = findCausalSmithRoot(import.meta.dirname);
  // The entry: as typed, or relative to the repository root (the parent of the package).
  const entryDir = [path.resolve(START, entryArg), path.resolve(pkgRoot, "..", entryArg)].find((d) => existsSync(d));
  if (!entryDir) {
    throw new Error(`${entryArg} does not exist: --entry is the bank entry folder, CausalSmith/doc/research/_bank/accepted/<qid>_<spec>, absolute or relative to the repository root or to where the command is typed`);
  }
  if (verb === "snapshot") {
    const leanDir = await entryLeanDir(entryDir, pkgRoot);
    const git = await gitState(leanDir);
    if (git.lean_differs_from_commit !== false) {
      throw new Error(`${leanDir} ${git.commit ? "has uncommitted changes" : "is not in a git checkout"}: a snapshot is recorded only on the committed run, before any promotion.`);
    }
    const snap = await recordSnapshot({ entryDir, leanDir });
    console.log(`snapshot at ${snap.commit!.slice(0, 12)}: ${Object.keys(snap.files).length} run files, ${Object.keys(snap.run).length} run declarations, ${Object.keys(snap.used).length} declarations outside the run that its statements use`);
    return 0;
  }
  const r = await checkEntry({ entryDir, pkgRoot });
  const s = r.snapshot;
  console.log(`snapshot recorded at commit ${s.commit ?? "(unknown)"}${s.lean_differs_from_commit ? " (the run's Lean had uncommitted changes then)" : ""}`);
  if (r.failures.length > 0) {
    for (const line of r.failures) console.error(line);
    console.error(`promotion check FAILED: ${r.failures.length} line(s) above, each with its next step. Nothing was written.`);
    return 1;
  }
  console.log(`promotion check passed: ${Object.keys(s.files).length} run files are byte-identical, ${Object.keys(s.run).length} run declarations and the ${Object.keys(s.used).length} declarations their statements use state what they stated at banking`);
  return 0;
}

main().then((code) => process.exit(code), (err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exit(2);
});
