// Stage 0 core path.
//
// The math solver owns the decomposition end-to-end (the solve round in
// `vcs/round.ts`). This module exports the shared path of the solved core
// `core.json`, consumed by D0-SOLVE / D0-RENDER / D0.R / D0.5.
import { artifactPath } from "../../paths.js";
import type { PipelineContext } from "../../types.js";

/** Filesystem path for `core.json` (the solved core), alongside the .tex artifacts;
 *  a run saved under the `<qid>_core.json` name resolves to that file. */
export function coreJsonPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "core.json", [`${ctx.qid}_core.json`]);
}
