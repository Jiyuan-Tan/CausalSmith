import type { PipelineContext, Stage, StageResult, StateJson } from "./types.js";
import { formatStageLabel } from "./constants.js";
import { defaultDeps } from "./pipeline_support.js";
import { runDiscoveryStage } from "./discovery/dispatcher.js";
import { runFormalizationStage } from "./formalization/dispatcher.js";

export type StageHandler = (args: {
  ctx: PipelineContext;
  state: StateJson;
  stage: Stage;
}) => Promise<StageResult>;

export const dryRunStageHandler: StageHandler = async ({ ctx, stage }) => {
  const { setTimeout: delay } = await import("node:timers/promises");
  await delay(1);
  return {
    stage,
    status: "completed",
    message: `dry-run completed stage ${stage} for ${ctx.qid}_${ctx.specialization}`,
  };
};

export const liveStageHandler: StageHandler = async ({ ctx, state, stage }) => {
  const deps = defaultDeps(ctx, stage, state);
  const discoveryResult = await runDiscoveryStage({ ctx, state, stage, deps });
  if (discoveryResult !== null) return discoveryResult;
  const formalizationResult = await runFormalizationStage({ ctx, state, stage, deps });
  if (formalizationResult !== null) return formalizationResult;
  throw new Error(`liveStageHandler: unhandled stage ${formatStageLabel(stage)}`);
};
