import type { PaperStage } from "./types.js";
import type { PaperDeps } from "./pipeline.js";
import {
  appendTokenUsageRecord,
  markTokenUsageIncomplete,
  type ModelTokenUsage,
} from "../token_usage.js";

async function recordCall(
  runDir: string,
  stage: PaperStage,
  provider: "codex" | "claude",
  model: string,
  durationMs: number,
  success: boolean,
  usage: ModelTokenUsage | null,
): Promise<void> {
  await appendTokenUsageRecord(runDir, {
    timestamp: new Date().toISOString(),
    provider,
    model,
    stage,
    duration_ms: durationMs,
    success,
    usage,
  }).catch(async (err) => {
    console.warn(`[token-usage] could not append presentation call record: ${String(err)}`);
    await markTokenUsageIncomplete(runDir, String(err)).catch((markerErr) => {
      console.warn(`[token-usage] could not mark presentation accounting incomplete: ${String(markerErr)}`);
    });
  });
}

/** Attach one presentation stage to every model call made while that stage runs. */
export function withPresentationTokenUsage(
  deps: PaperDeps,
  runDir: string,
  stage: PaperStage,
): PaperDeps {
  return {
    ...deps,
    runCodex: async (args) => {
      const started = Date.now();
      let usage: ModelTokenUsage | null = null;
      try {
        const out = await deps.runCodex({
          ...args,
          onUsage: (value) => {
            usage = value;
            args.onUsage?.(value);
          },
        });
        await recordCall(
          runDir,
          stage,
          "codex",
          args.model ?? deps.codexModel ?? "?",
          Date.now() - started,
          true,
          usage,
        );
        return out;
      } catch (err) {
        await recordCall(
          runDir,
          stage,
          "codex",
          args.model ?? deps.codexModel ?? "?",
          Date.now() - started,
          false,
          usage,
        );
        throw err;
      }
    },
    runClaude: async (args) => {
      const started = Date.now();
      let resolvedModel: string | undefined;
      let usage: ModelTokenUsage | null = null;
      try {
        const out = await deps.runClaude({
          ...args,
          onResolvedModel: (model) => {
            resolvedModel = model;
            args.onResolvedModel?.(model);
          },
          onUsage: (value) => {
            usage = value;
            args.onUsage?.(value);
          },
        });
        await recordCall(
          runDir,
          stage,
          "claude",
          resolvedModel ?? args.model,
          Date.now() - started,
          true,
          usage,
        );
        return out;
      } catch (err) {
        await recordCall(
          runDir,
          stage,
          "claude",
          resolvedModel ?? args.model,
          Date.now() - started,
          false,
          usage,
        );
        throw err;
      }
    },
  };
}
