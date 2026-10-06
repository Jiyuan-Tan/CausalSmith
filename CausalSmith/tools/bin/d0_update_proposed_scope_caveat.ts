#!/usr/bin/env -S npx tsx
/** Guarded orchestrator writer for one stale accepted-scope caveat in proposal state. */
import process from "node:process";
import { appendEntry } from "../src/decision_log.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { loadState, saveState } from "../src/state.js";

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const label = cli.value("--label");
  const expectBoundClaim = cli.value("--expect-bound-claim");
  const caveat = cli.value("--caveat");
  const boundClaim = cli.value("--bound-claim");
  const check = cli.bool("--check");
  if (!qid || !spec || !label || !expectBoundClaim || !caveat || !boundClaim) {
    throw new Error(
      "Usage: d0_update_proposed_scope_caveat.ts <qid> <spec> --label <label> " +
      "--expect-bound-claim <old> --caveat <new> --bound-claim <new> [--check]",
    );
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const pf = state.proposed_from;
  if (!pf) throw new Error("missing proposed_from state");
  const rows = pf.accepted_scope_caveats;
  if (!rows) throw new Error("missing proposed_from.accepted_scope_caveats");
  const matches = rows.filter((row) => row.label === label && row.bound_claim === expectBoundClaim);
  if (matches.length !== 1) {
    throw new Error(`expected exactly one matching caveat, found ${matches.length}`);
  }
  const before = structuredClone(state);
  const row = matches[0];
  const receipt = {
    label,
    before: { caveat: row.caveat, bound_claim: row.bound_claim },
    after: { caveat, bound_claim: boundClaim },
  };
  row.caveat = caveat;
  row.bound_claim = boundClaim;
  const beforeSans = structuredClone(before);
  const afterSans = structuredClone(state);
  const beforeRow = beforeSans.proposed_from!.accepted_scope_caveats!.find((x) => x.label === label)!;
  const afterRow = afterSans.proposed_from!.accepted_scope_caveats!.find((x) => x.label === label)!;
  beforeRow.caveat = afterRow.caveat = "<guarded>";
  beforeRow.bound_claim = afterRow.bound_claim = "<guarded>";
  if (JSON.stringify(beforeSans) !== JSON.stringify(afterSans)) {
    throw new Error("scope-caveat writer changed another state field; refusing save");
  }
  if (check) {
    console.log(JSON.stringify({ check: true, ...receipt }, null, 2));
    return;
  }
  await saveState(repoRoot, qid, spec, state);
  appendEntry(repoRoot, qid, {
    type: "command",
    from: "D",
    phase: "D",
    stage: "D0.5",
    cmd: "update-proposed-scope-caveat",
    target: label,
    note: "Guarded synchronization of a stale accepted-scope caveat; no theorem or stage field changed.",
  }, spec);
  console.log(JSON.stringify(receipt, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_update_proposed_scope_caveat: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
