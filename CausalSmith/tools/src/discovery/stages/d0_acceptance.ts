/** Exact-artifact receipt for a complete typed D0.5 pass.
 *
 * Proposal review (D-0.5) and typed core review (D0.5) are different gates, so
 * F-entry uses an authority emitted by D0.5 itself. Every full D0.5 pass writes
 * this receipt, binding the pass to the proposal revision, the graph's main
 * commit, and the exact rendered core bytes the panel read.
 */
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import path from "node:path";
import type { PipelineContext, StateJson } from "../../types.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { coreJsonPath } from "./d0_core.js";
import { proposalRevision } from "../proposal_revision.js";
import { MAIN_REF, VcsStore } from "../vcs/store.js";

interface D05AcceptanceReceipt {
  schema_version: 2;
  kind: "accepted-d05-store";
  proposal_revision: string;
  main_commit: string;
  core_sha256: string;
}

export function d05AcceptanceReceiptPath(ctx: PipelineContext): string {
  return path.join(path.dirname(coreJsonPath(ctx)), "d05_acceptance_receipt.json");
}

async function sha256File(filePath: string): Promise<string> {
  return createHash("sha256").update(await readFile(filePath)).digest("hex");
}

async function currentReceipt(ctx: PipelineContext, state: StateJson): Promise<D05AcceptanceReceipt | null> {
  const revision = proposalRevision(state);
  // Legacy/non-propose fixtures have no proposal cursor and are outside the
  // revision-coherence guard. Do not make their otherwise-valid D0.5 pass fail.
  if (!revision) return null;
  const main = await VcsStore.at(ctx).readRef(MAIN_REF);
  if (main === null) return null;
  return {
    schema_version: 2,
    kind: "accepted-d05-store",
    proposal_revision: revision,
    main_commit: main,
    core_sha256: await sha256File(coreJsonPath(ctx)),
  };
}

/** Called only after the complete typed D0.5 panel and novelty gate pass. */
export async function writeD05AcceptanceReceipt(ctx: PipelineContext, state: StateJson): Promise<void> {
  const receipt = await currentReceipt(ctx, state);
  if (receipt) {
    await writeJsonAtomic(d05AcceptanceReceiptPath(ctx), receipt);
    return;
  }
  if (proposalRevision(state)) {
    throw new Error("refusing to record typed D0.5 acceptance: the run has no graph store main commit");
  }
}

/** Exact validation; malformed/stale receipts are simply not authority. */
export async function hasValidD05AcceptanceReceipt(ctx: PipelineContext, state: StateJson): Promise<boolean> {
  try {
    const recorded = JSON.parse(await readFile(d05AcceptanceReceiptPath(ctx), "utf8")) as D05AcceptanceReceipt;
    const current = await currentReceipt(ctx, state);
    if (!current) return false;
    // `main_commit` is provenance: a reset back to the accepted tree is a new commit
    // that renders the same bytes, and the bytes are what the panel accepted.
    return recorded.schema_version === 2 && recorded.kind === "accepted-d05-store" &&
      recorded.proposal_revision === current.proposal_revision &&
      recorded.core_sha256 === current.core_sha256;
  } catch {
    return false;
  }
}
