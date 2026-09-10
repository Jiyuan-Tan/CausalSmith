import path from "node:path";
import type { NoveltyTarget } from "../novelty.js";
import { formalizationDir } from "../paths.js";
import type { PipelineContext, StateJson, UpgradeFrom } from "../types.js";

/** Persist and rehydrate the proposal invocation (`--propose <topic>`, tier, upgrade
 * lineage) so a bare `--resume` after a halt still knows it is a proposal run.
 * Stage numbers alone cannot say that: a halt between D-1.1 and D-1.2 leaves no
 * `proposed_from`, and before this record existed such a resume skipped straight
 * into D0 with no proposal. Legacy runs migrate from `proposed_from`. Returns
 * whether the run carries an intent (the caller persists it). */
export async function ensurePreD0Intent(ctx: PipelineContext, state: StateJson): Promise<boolean> {
  let intent = state.pre_d0_intent;
  if (!intent && ctx.proposeTopic) {
    intent = {
      cursor_version: 1,
      topic: ctx.proposeTopic,
      novelty_target: ctx.noveltyTarget ?? "field",
      upgrade_from: ctx.upgradeFrom,
    };
  } else if (!intent && state.proposed_from) {
    intent = {
      cursor_version: 1,
      topic: state.proposed_from.topic,
      novelty_target: state.proposed_from.novelty_target,
      upgrade_from: state.proposed_from.upgrade_from,
    };
  } else if (!intent && ctx.resume && state.gaps) {
    throw new Error(
      `resume has no durable pre_d0_intent; write that field in ${path.join(formalizationDir(ctx.repoRoot, ctx.qid), "state.json")} before retrying`,
    );
  }
  if (!intent) return false;

  if (ctx.proposeTopic !== undefined && ctx.proposeTopic !== intent.topic) {
    throw new Error("proposal topic conflicts with the durable pre-D0 intent; start a new run or use the proposal-angle workflow");
  }
  if (ctx.upgradeFrom !== undefined && JSON.stringify(ctx.upgradeFrom) !== JSON.stringify(intent.upgrade_from)) {
    throw new Error("upgrade context conflicts with the durable pre-D0 intent");
  }
  // The CLI flag is the operator's tier decision (`--downgrade-tier` re-passes
  // D0.5 at a lower floor): it updates the intent rather than being overwritten.
  if (ctx.noveltyTarget !== undefined) intent.novelty_target = ctx.noveltyTarget;
  state.pre_d0_intent = intent;
  (ctx as { proposeTopic?: string }).proposeTopic = intent.topic;
  (ctx as { noveltyTarget?: NoveltyTarget }).noveltyTarget = intent.novelty_target;
  if (intent.upgrade_from) (ctx as { upgradeFrom?: UpgradeFrom }).upgradeFrom = intent.upgrade_from;
  return true;
}
