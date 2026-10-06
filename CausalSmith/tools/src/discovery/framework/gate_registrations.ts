// Explicit D-stage gate declarations. Runtime call sites import the gate they
// execute; no global registry or import-order side effect is involved.
import { defineGate, type GateViolation } from "./gates.js";
import { runStructuralGate } from "../core/gate.js";
import { runProposalGate } from "../core/proposal_gate.js";
import { checkProseConsistency } from "../core/prose_consistency.js";
import type { Core } from "../core/schema.js";

function toViolations(
  gateId: string,
  vs: Array<{ code: string; where: string; message: string }>,
): GateViolation[] {
  return vs.map((v) => ({ gateId, detail: `[${v.code}] ${v.where}: ${v.message}` }));
}

/** G1–G7 structural gate over a (possibly not-yet-schema-valid) core.
 *  `requireDischarged` defaults to false; the D0 final assembly and the D0.R
 *  post-edit re-check pass `requireDischarged: true` at their call sites. */
export const structuralGate = defineGate<{ core: unknown; requireDischarged?: boolean }>({
  id: "structural-gate",
  tier: "hard",
  stages: ["-1.2", "0", "0.5"],
  evidence:
    "D0_CORE_REDESIGN.md G1–G7; PIPELINE_NOTES 2026-07-18 (G1 free-symbol escape discovered only after a paid solve round) and 2026-07-20 (G2 over-broad 'standard' token ban exhausted the proposal-gate retries)",
  check: ({ core, requireDischarged }) =>
    toViolations("structural-gate", runStructuralGate(core, { requireDischarged: requireDischarged ?? false }).violations),
});

/** GP1 (standardness tags) + GP2 (all-to-prove) + GP3 (prose fields present),
 *  layered over the structural gate, for the D-1.2 authored proposal core. */
export const proposalGate = defineGate<unknown>({
  id: "proposal-gate",
  tier: "hard",
  stages: ["-1.2"],
  evidence:
    "D0_CORE_REDESIGN.md §12 (single-artifact producer: gate runs inside the author, loud by design); PIPELINE_NOTES 2026-07-18 (grouped free_symbols exhausted the retry budget — gate feedback must be re-authorable)",
  check: (core) => toViolations("proposal-gate", runProposalGate(core).violations),
});

// (Retired, Phase 1 of the store consolidation: the `proposal-closure` gate.
// The published core is `assembleCore(proto, working)`, so
// `ids(core) ⊆ ids(proto) ∪ ids(working)` holds by construction — the state the
// gate policed is unrepresentable. See test/discovery/assemble.test.ts.)

/** Prose↔formal drift lint (PROSE-DANGLING-REF / PROSE-OPEN-OVERCLAIM). */
export const proseConsistencyGate = defineGate<Core>({
  id: "prose-consistency",
  tier: "warn",
  stages: ["0"],
  evidence:
    "PIPELINE_NOTES 2026-07-15 (solver could prove a reframe but not synchronize its prose) + 6b37bdb9 (stop flagging a well-scoped open question)",
  check: (core) =>
    checkProseConsistency(core).map((w) => ({ gateId: "prose-consistency", detail: `[${w.code}] ${w.field}: ${w.message}` })),
});
