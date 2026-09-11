// Stage -1.2 author (single artifact) — the WHOLE D-1.2 producer in one dispatch.
//
// One agent authors the typed proposal core: formal fields (symbols, pure-condition
// assumptions, class/construction definitions, to-prove statements) AND prose fields
// (tldr, project_justification gap→niche→fill, related_work, per-statement
// justification/gap/consumer). The core is the single source of truth AND the sole
// artifact: discovery consumers (the D-0.5 reviewer, D0-CORE) read the proto_core JSON
// directly, so NO proposal .tex is rendered here (the D0 derivation .tex — F3 roadmap —
// is rendered later by D0-RENDER). Flow: dispatch → write core.json → proposal gate
// (G1–G7 + GP1/GP2/GP3) → schema-validate. Proposal metadata is harvested from
// that core into the -0.5 handoff. Stdout is only a disposition receipt; it is
// never a second authority for proposal metadata. See D0_CORE_REDESIGN.md §12.
import { existsSync } from "node:fs";
import { mkdir, readFile, rm } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { MODEL_PLAN } from "../../constants.js";
import { artifactPath } from "../../paths.js";
import { discoveryBrief, readPrompt, type StageDeps } from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { clusterFor } from "../cluster_setup.js";
import { CoreSchema } from "../core/schema.js";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairCoreLatexSerialization,
} from "../core/latex_serialization.js";
import { runGates } from "../framework/gates.js";
import { dispatchAgent } from "../../framework/agent_dispatch.js";
import { proposalGate } from "../framework/gate_registrations.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { stableJson } from "../../shared/stable_json.js";
import { loadParentEntry } from "../../upgrade.js";
import {
  extensionEditBasePath,
  sealPendingExtensionSource,
} from "./d0_cross_boundary_rewind.js";

/** Filesystem path for `<qid>_proto_core.json` (the D-1-authored proposal core). */
export function protoCoreJsonPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "proto_core.json", [`${ctx.qid}_proto_core.json`]);
}

/** The five producer modes; each maps to `stage_neg1_2_proto_head_<mode>.txt`. */
export type Neg1_2Mode = "cold-start" | "revise" | "pivot" | "kernel-replace" | "draft-rebuild";

export interface StageNeg1_2ProtoCoreResult {
  /** `needs-pivot` = the author could not author this mode (revise can't fix in
   * place / no surviving seed); the dual producer records it on proposed_from so
   * the -0.5 orchestrator drives the pivot. No core is written in that case. */
  status: "completed" | "needs-pivot";
  message: string;
  protoCoreJsonPath: string;
  /** The author's stdout receipt merged with ideation metadata from the validated
   * proto core. The core is authoritative because the final stdout contract is a
   * deliberately small status receipt and may omit seeds / literature metadata. */
  handoff: Record<string, unknown>;
}

function containsSubstantiveText(value: unknown): boolean {
  if (typeof value === "string") return value.trim() !== "";
  if (Array.isArray(value)) return value.some(containsSubstantiveText);
  if (value !== null && typeof value === "object") {
    return Object.values(value as Record<string, unknown>).some(containsSubstantiveText);
  }
  return false;
}

const nonempty = z.string().trim().min(1);
/** The stdout receipt: a disposition plus a nonempty message. Unknown keys are
 * STRIPPED, not rejected — a model that also echoes checklist / upgrade metadata
 * on stdout is harmless (the core is the only authority) and must not cost a
 * re-author round. `artifacts` is advisory: the core path is orchestrator-owned. */
const AuthorReceiptSchema = z.object({
  status: z.enum(["completed", "needs-pivot", "failed"]),
  message: nonempty,
  artifacts: z.array(nonempty).optional(),
});
const substantiveRecord = z.record(z.unknown()).refine(containsSubstantiveText, "must contain substantive text");
const IdeationMetadataSchema = z.object({
  seeds: z.array(nonempty).min(1),
  seed_details: z.array(substantiveRecord).min(1),
  literature_map: z.union([nonempty, substantiveRecord, z.array(substantiveRecord).min(1)]),
});
const LiteratureChecklistRowSchema = z.object({
  author: nonempty,
  year: z.union([z.number().finite(), nonempty]),
  venue: nonempty,
  bibkey: nonempty,
  one_line: nonempty,
  relevant_to: nonempty,
}).strict();
const UpgradeMetadataSchema = z.object({
  upgrade_mode: z.literal(true).optional(),
  parent_qid: nonempty.optional(),
  parent_spec: nonempty.optional(),
  upgrade_axis: z.enum(["computation", "estimation", "generalization", "mechanism"]).optional(),
  delta_summary: nonempty.optional(),
  reused_bibkeys: z.array(nonempty).optional(),
  new_bibkeys: z.array(nonempty).min(1).optional(),
});

function authoredMetadataSchema(
  upgrade: NonNullable<StateJson["proposed_from"]>["upgrade_from"],
  core: Record<string, unknown>,
  /** Cold-start is the only mode whose prompt runs seed generation; every other
   * mode carries the ideation substrate in `proposed_from`, so there the keys are
   * harvested when present and never required. */
  requireIdeation: boolean,
) {
  const ideation = requireIdeation ? IdeationMetadataSchema : IdeationMetadataSchema.partial();
  return ideation.merge(z.object({
    literature_checklist: z.array(LiteratureChecklistRowSchema).min(4).max(10),
    novelty_justification: z.union([
      nonempty,
      z.record(z.unknown()).refine(containsSubstantiveText, "must contain substantive text")
        .transform((value) => stableJson(value)),
    ]),
  })).merge(UpgradeMetadataSchema).superRefine((metadata, ctx) => {
    const statementIds = new Set(
      Array.isArray(core.statements)
        ? core.statements.flatMap((statement) =>
          typeof statement === "object" && statement !== null &&
              typeof (statement as Record<string, unknown>).id === "string"
            ? [(statement as Record<string, unknown>).id as string]
            : [])
        : [],
    );
    const bibliographyEntries = Array.isArray(core.bibliography)
      ? core.bibliography.flatMap((entry) => {
        if (typeof entry !== "object" || entry === null) return [];
        const row = entry as Record<string, unknown>;
        return typeof row.key === "string" ? [{ key: row.key }] : [];
      })
      : [];
    const bibliographyKeys = new Set(bibliographyEntries.map(({ key }) => key));
    if (bibliographyKeys.size !== bibliographyEntries.length) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["bibliography"],
        message: "bibliography keys must be unique for unambiguous metadata joins",
      });
    }
    for (const [index, row] of metadata.literature_checklist.entries()) {
      if (!statementIds.has(row.relevant_to)) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["literature_checklist", index, "relevant_to"],
          message: "must name a current statement id",
        });
      }
      if (!bibliographyKeys.has(row.bibkey)) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["literature_checklist", index, "bibkey"],
          message: "must name a current bibliography key",
        });
      }
    }
    if (!upgrade) return;
    const expected: Record<string, unknown> = {
      upgrade_mode: true,
      parent_qid: upgrade.parent_qid,
      parent_spec: upgrade.parent_spec,
      upgrade_axis: upgrade.upgrade_axis,
    };
    for (const [key, value] of Object.entries(expected)) {
      if (metadata[key as keyof typeof metadata] !== value) {
        ctx.addIssue({ code: z.ZodIssueCode.custom, path: [key], message: `must equal ${JSON.stringify(value)}` });
      }
    }
    for (const key of ["delta_summary", "reused_bibkeys", "new_bibkeys"] as const) {
      if (metadata[key] === undefined) {
        ctx.addIssue({ code: z.ZodIssueCode.custom, path: [key], message: "required in upgrade mode" });
      }
    }
    const reused = metadata.reused_bibkeys ?? [];
    const added = metadata.new_bibkeys ?? [];
    if (new Set(reused).size !== reused.length || reused.length < 3) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["reused_bibkeys"],
        message: "must contain at least three unique parent bibliography keys",
      });
    }
    if (new Set(added).size !== added.length) {
      ctx.addIssue({ code: z.ZodIssueCode.custom, path: ["new_bibkeys"], message: "must contain unique keys" });
    }
    for (const key of [...reused, ...added]) {
      if (!bibliographyKeys.has(key)) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: [reused.includes(key) ? "reused_bibkeys" : "new_bibkeys"],
          message: `${JSON.stringify(key)} must name a current bibliography key`,
        });
      }
    }
    for (const key of added) {
      if (reused.includes(key)) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["new_bibkeys"],
          message: `${JSON.stringify(key)} must be disjoint from reused_bibkeys`,
        });
      }
    }
  });
}

function parseAuthorReceipt(
  stdout: string,
): { receipt: z.infer<typeof AuthorReceiptSchema>; error: null } | { receipt: null; error: string } {
  try {
    const normalized = normalizeRawModelJson(stdout).trim();
    return { receipt: AuthorReceiptSchema.parse(JSON.parse(normalized)), error: null };
  } catch (error) {
    return {
      receipt: null,
      error: `Stage -1.2 producer receipt is invalid: ${error instanceof Error ? error.message : String(error)}`,
    };
  }
}

/** Upgrade-provenance contract read from the banked parent. `null` when the
 * parent cannot supply one (pre-rollout `.tex` proposal, stale identity, too
 * few keys): the run then keeps the core-side upgrade checks (three unique
 * reused keys, all keys present in the current bibliography, reused/new
 * disjoint) and skips only the parent-membership join. Halting an upgrade run
 * over bank-side metadata would make every legacy parent un-upgradable. */
async function loadParentContract(
  repoRoot: string,
  upgradeFrom: NonNullable<NonNullable<StateJson["proposed_from"]>["upgrade_from"]>,
): Promise<{ bibliography: Set<string>; cluster: string } | null> {
  const parent = await loadParentEntry(repoRoot, upgradeFrom);
  const skip = (why: string): null => {
    console.warn(`[D-1.2] upgrade provenance: parent-membership check skipped — ${why}`);
    return null;
  };
  let parentCore: Record<string, unknown>;
  try {
    parentCore = JSON.parse(normalizeRawModelJson(parent.proposal_tex)) as Record<string, unknown>;
  } catch {
    return skip("the banked parent proposal is not a typed core (pre-rollout .tex entry)");
  }
  const parsed = CoreSchema.safeParse(parentCore);
  if (!parsed.success) return skip("the banked parent core does not parse as CoreSchema");
  const typedParent = parsed.data;
  if (typedParent.qid !== upgradeFrom.parent_qid || typedParent.specialization !== upgradeFrom.parent_spec) {
    return skip("the banked parent core identity does not match the requested upgrade parent");
  }
  if (!typedParent.cluster) return skip("the banked parent core declares no cluster");
  if (parent.cluster && typedParent.cluster !== parent.cluster) {
    return skip("the banked parent core cluster does not match the bank metadata");
  }
  const keys = (typedParent.bibliography ?? []).map((entry) => entry.key);
  const bibliography = new Set(keys);
  if (bibliography.size !== keys.length) return skip("the banked parent bibliography keys are not unique");
  if (bibliography.size < 3) return skip("the banked parent bibliography has fewer than three keys");
  return { bibliography, cluster: typedParent.cluster };
}

export function assembleNeg1_2AuthorPrompt(parts: {
  head: string;
  core: string;
  brief: string;
  contextBlocks?: string;
  modeBlock?: string;
  corePath: string;
}): string {
  return [
    parts.head,
    "",
    parts.core,
    "",
    parts.brief,
    parts.contextBlocks ? `\n${parts.contextBlocks}` : "",
    parts.modeBlock ? `\n${parts.modeBlock}` : "",
    "",
    `Write the typed proposal core JSON to this path (create it): ${parts.corePath}`,
    'Return only the disposition receipt on stdout: {"status":"completed"|"needs-pivot","message":"...","artifacts":["<proto_core.json>"]}. Put all proposal, literature, novelty, and upgrade metadata in the typed proposal core, never in this receipt.',
  ].join("\n");
}

/** Ideation-metadata keys preserved verbatim from the raw authored core at the
 * persist boundary (everything else outside CoreSchema is dropped — see the
 * persist comment in `runStageNeg1_2ProtoCore`). Exported so the prompt↔schema
 * contract test can prove every prompt-mandated field survives persistence. */
/** Upgrade metadata is authored in the core and preserved at its validation
 * boundary. Stdout may repeat it, but the receipt is never consulted for these
 * fields. */
export const UPGRADE_CORE_KEYS = [
  "upgrade_mode",
  "parent_qid",
  "parent_spec",
  "upgrade_axis",
  "delta_summary",
  "reused_bibkeys",
  "new_bibkeys",
] as const;

export const CORE_HANDOFF_KEYS = [
  "seeds",
  "seed_details",
  "literature_map",
  "cluster",
  "novelty_justification",
  "literature_checklist",
  ...UPGRADE_CORE_KEYS,
] as const;

/** Preserve the small stdout status receipt while sourcing proposal metadata
 * from the single validated artifact. This prevents an emitted-to-persisted
 * drop when the model follows the final minimal stdout instruction exactly. */
function mergeCoreHandoff(
  core: Record<string, unknown>,
  stdoutHandoff: Record<string, unknown>,
): Record<string, unknown> {
  const merged = projectStdoutReceipt(stdoutHandoff);
  for (const key of CORE_HANDOFF_KEYS) {
    if (Object.prototype.hasOwnProperty.call(core, key)) merged[key] = core[key];
  }
  return merged;
}

function projectStdoutReceipt(stdoutHandoff: Record<string, unknown>): Record<string, unknown> {
  const receipt: Record<string, unknown> = {};
  // Failure diagnostics are part of the disposition receipt: D-0.5 uses them
  // to distinguish an unworkable angle from a provider/sandbox failure. They
  // are not proposal or reviewer metadata.
  for (const key of ["status", "message", "artifacts", "blocking_reason", "error", "failure_reason"] as const) {
    if (Object.prototype.hasOwnProperty.call(stdoutHandoff, key)) receipt[key] = stdoutHandoff[key];
  }
  return receipt;
}

/**
 * Build the MODE-SPECIFIC input block: the prior core to edit (revise /
 * kernel-replace / draft-rebuild), the surviving seed list (pivot), and the prior
 * reviewer verdict (every non-cold-start mode). Cold-start has none. The prior
 * core is read from `corePath` BEFORE the author overwrites it.
 */
async function modeInputBlock(mode: Neg1_2Mode, state: StateJson, corePath: string): Promise<string> {
  const pf = state.proposed_from;
  const blocks: string[] = [];
  const editsPrior = mode === "revise" || mode === "kernel-replace" || mode === "draft-rebuild";
  if (editsPrior && existsSync(corePath)) {
    blocks.push(
      "=== PRIOR CORE EDIT BASE (preserve it and re-emit the FULL revised proposal to the requested output path) ===",
      await readFile(corePath, "utf8"),
      "=== END PRIOR CORE EDIT BASE ===",
    );
  }
  if (mode === "pivot") {
    blocks.push(
      "=== PIVOT CONTEXT (the prior cursor is exhausted — obey any explicit carry-forward directive before choosing a new seed) ===",
      `seed_list: ${JSON.stringify(pf?.seed_list ?? [])}`,
      `exhausted_angles: ${JSON.stringify(pf?.exhausted_angles ?? [])}`,
      "=== END PIVOT CONTEXT ===",
    );
  }
  if (mode !== "cold-start" && typeof pf?.last_reviewer_verdict === "string" && pf.last_reviewer_verdict.length > 0) {
    blocks.push(
      "=== PRIOR REVIEWER VERDICT (load-bearing — address the flagged items) ===",
      pf.last_reviewer_verdict,
      "=== END PRIOR REVIEWER VERDICT ===",
    );
  }
  return blocks.join("\n");
}

export async function runStageNeg1_2ProtoCore(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  /** Producer mode — selects the head prompt + the mode-specific input block. */
  mode: Neg1_2Mode;
  /** Optional extra prompt blocks (D-1.1 gaps / motif library / flagship directive)
   * assembled by the caller; appended to the prompt. Mode-specific inputs (prior
   * core / seeds / reviewer verdict) are assembled HERE, not by the caller. */
  contextBlocks?: string;
}): Promise<StageNeg1_2ProtoCoreResult> {
  const corePath = protoCoreJsonPath(args.ctx);
  // The author writes here; only a core that passed schema, gates and reviewer-
  // metadata validation is renamed onto the canonical path, so a malformed
  // receipt or a rejected draft can never displace the last validated core.
  const attemptPath = `${corePath}.next`;
  await mkdir(path.dirname(corePath), { recursive: true });

  // An additive F→D extension is based on the accepted D0 core, which may
  // contain nodes D0 added after the original proposal. Seal that source before
  // dispatch and use it for the first draft only; later revisions edit the
  // immediately prior extension proto in the ordinary way.
  await sealPendingExtensionSource({ ctx: args.ctx, state: args.state });
  const editBasePath = extensionEditBasePath({
    ctx: args.ctx,
    state: args.state,
    ordinaryProtoPath: corePath,
  });

  const headName = `stage_neg1_2_proto_head_${args.mode.replace(/-/g, "_")}.txt`;
  const modeBlock = await modeInputBlock(args.mode, args.state, editBasePath);

  const basePrompt = assembleNeg1_2AuthorPrompt({
    head: await readPrompt(args.ctx, headName),
    core: await readPrompt(args.ctx, "stage_neg1_2_proto_core.txt"),
    brief: discoveryBrief(args.ctx, args.state),
    contextBlocks: args.contextBlocks,
    modeBlock,
    corePath: attemptPath,
  });
  const upgradeFrom = args.state.pre_d0_intent?.upgrade_from ?? args.state.proposed_from?.upgrade_from ?? args.ctx.upgradeFrom;
  const parentContract = upgradeFrom ? await loadParentContract(args.ctx.repoRoot, upgradeFrom) : null;

  // The proposal gate (G1–G7 + GP1–GP3) can reject the authored core (e.g. prose
  // in an atomic `condition`/target field). Re-author with the violations fed back
  // — bounded by a small budget — instead of aborting the whole run on the first
  // miss (this is the "fix and re-author" path the gate throw-site names).
  const REAUTHOR_BUDGET = 3;
  let lastGateFeedback = "";

  for (let attempt = 1; attempt <= REAUTHOR_BUDGET; attempt++) {
    const prompt = lastGateFeedback
      ? `${basePrompt}\n\n── PRIOR ATTEMPT REJECTED BY THE PROPOSAL GATE ──\n` +
        `Your previous core failed these structural checks:\n${lastGateFeedback}\n` +
        `Fix every listed structural violation and re-author the COMPLETE corrected core JSON. ` +
        `Then re-audit the original reviewer flags and orchestrator directives: a structural-gate ` +
        `repair does not discharge or narrow those substantive obligations. Atomic ` +
        `fields (an assumption \`condition\`, formal target/objective expressions) must ` +
        `hold ONLY formal symbolic content — move any explanatory prose into the ` +
        `designated prose/description fields.`
      : basePrompt;

    // The staging path is fixed, so a leftover from a declined / failed / killed
    // earlier attempt must never pass for this author's output.
    await rm(attemptPath, { force: true });
    const out = await dispatchAgent({
      ctx: args.ctx,
      deps: args.deps,
      stage: "-1.2",
      label: `D-1.2 proto-core author (mode=${args.mode}, attempt ${attempt}/${REAUTHOR_BUDGET})`,
      prompt,
      promptSources: [
        `prompts/D-1/${headName}`,
        "prompts/D-1/stage_neg1_2_proto_core.txt",
        ...(args.contextBlocks ? ["caller-context-blocks"] : []),
        ...(modeBlock ? ["mode-input-block"] : []),
        ...(lastGateFeedback ? ["gate-feedback"] : []),
      ],
      model: MODEL_PLAN.stageNeg1_2_draft.codex.model,
      reasoningEffort: MODEL_PLAN.stageNeg1_2_draft.codex.effort,
      inactivityTimeoutMs: 40 * 60 * 1000,
    });
    const parsedReceipt = parseAuthorReceipt(out.stdout);
    if (parsedReceipt.receipt === null) {
      // A malformed receipt is a fixable output defect, not a dead angle: spend a
      // bounded re-author round on it (the core is rewritten with the receipt).
      if (attempt === REAUTHOR_BUDGET) throw new Error(parsedReceipt.error);
      lastGateFeedback = `  [RECEIPT] ${parsedReceipt.error} — the final stdout line must be exactly ` +
        `{"status":"completed"|"needs-pivot"|"failed","message":"<nonempty>","artifacts":["<core path>"]}`;
      continue;
    }
    const parsedOut = parsedReceipt.receipt;
    if (parsedOut.status === "failed") {
      throw new Error(
        `Stage -1.2 author reported status "failed": ${parsedOut.message ?? "(no message)"} — ` +
          `the proposal is not authorable as posed; pivot or revise the angle.`,
      );
    }
    // needs-pivot declines this mode without authoring proposal state. Never
    // harvest a diagnostic `.next`: only a fully gated canonical core may be a
    // source of proposal metadata.
    if (parsedOut.status === "needs-pivot") {
      const handoff = projectStdoutReceipt(parsedOut);
      return {
        status: "needs-pivot",
        message: parsedOut.message ?? "Stage -1.2 author returned needs-pivot",
        protoCoreJsonPath: corePath,
        handoff,
      };
    }
    if (!existsSync(attemptPath)) {
      if (attempt === REAUTHOR_BUDGET) {
        throw new Error(`Stage -1.2 author completed without writing the required core at ${attemptPath}`);
      }
      lastGateFeedback = `  [WRITE] ${attemptPath}: author completed without writing the core file`;
      continue;
    }

    let core: unknown;
    try {
      // Pre-parse raw-byte normalization: repair under-escaped TeX backslashes
      // while the raw bytes still distinguish them from intended control escapes.
      core = JSON.parse(normalizeRawModelJson(await readFile(attemptPath, "utf8")));
    } catch (e) {
      if (attempt === REAUTHOR_BUDGET) {
        throw new Error(`Stage -1.2 author wrote a core at ${attemptPath} that is not valid JSON: ${String(e)}`);
      }
      lastGateFeedback = `  [JSON] ${attemptPath}: not valid JSON (${String(e)})`;
      continue;
    }

    // Proposal gate: G1–G7 + GP1 (tag content) + GP2 (nothing proven) + GP3 (prose
    // fields present). One call — the prose lives in the core, so there is no second
    // artifact and no \coreref coverage to check.
    const gateViolations = runGates([proposalGate], core).hard;
    if (gateViolations.length > 0) {
      lastGateFeedback = gateViolations.map((v) => `  ${v.detail}`).join("\n");
      if (attempt === REAUTHOR_BUDGET) {
        throw new Error(
          `Stage -1.2 author fails the proposal gate after ${REAUTHOR_BUDGET} attempts — last violations:\n${lastGateFeedback}`,
        );
      }
      continue;
    }

    // Schema-validate and canonicalize at the producer boundary. Leaving decoded
    // JSON control escapes in proto_core makes every later exact-echo comparison
    // disagree with a solver that correctly re-emits the intended LaTeX.
    // No .tex is rendered: the proto_core JSON is the sole discovery artifact.
    const typedCore = CoreSchema.parse(core);
    // Run identity and cluster are fixed by the orchestrator (the brief names
    // them). A mismatch is a model slip the author can correct, so it is fed
    // back like a gate violation rather than halting the run.
    const identityViolations: string[] = [];
    if (typedCore.qid !== args.ctx.qid) {
      identityViolations.push(`  [IDENTITY] Stage -1.2 authored core qid must equal ${args.ctx.qid}`);
    }
    if (typedCore.specialization !== args.ctx.specialization) {
      identityViolations.push(`  [IDENTITY] Stage -1.2 authored core specialization must equal ${args.ctx.specialization}`);
    }
    const expectedCluster = clusterFor(args.ctx, args.state);
    if (!typedCore.cluster) {
      identityViolations.push("  [IDENTITY] Stage -1.2 authored core must declare cluster");
    } else if (expectedCluster && typedCore.cluster !== expectedCluster) {
      identityViolations.push(`  [IDENTITY] Stage -1.2 authored core cluster must equal run cluster ${expectedCluster}`);
    } else if (parentContract && typedCore.cluster !== parentContract.cluster) {
      identityViolations.push(`  [IDENTITY] Stage -1.2 upgrade core cluster must equal parent cluster ${parentContract.cluster}`);
    }
    if (identityViolations.length > 0) {
      if (attempt === REAUTHOR_BUDGET) throw new Error(identityViolations.join("\n").trim());
      lastGateFeedback = identityViolations.join("\n");
      continue;
    }
    repairCoreLatexSerialization(typedCore);
    // Backstop: any control character surviving normalization + repair is an
    // escaping error the model must fix; feed it back as a re-author round
    // instead of persisting silently corrupted TeX.
    try {
      assertNoDecodedControlChars(typedCore, "Stage -1.2 proposal core");
    } catch (e) {
      if (attempt === REAUTHOR_BUDGET) throw e;
      lastGateFeedback = `  [ESCAPE] ${e instanceof Error ? e.message : String(e)}`;
      continue;
    }
    CoreSchema.parse(typedCore);
    // Persist the canonicalized core plus ONLY the allowlisted authored metadata
    // (seeds, literature metadata, upgrade metadata): CoreSchema strips unknown keys,
    // and both the cold-start harvest below and post-interrupt rehydration read
    // those keys from this object / the persisted file. A blanket raw-core spread
    // would let the author persist arbitrary non-schema keys that later flow
    // verbatim into the D-0.5 reviewer prompt (audit finding: prompt injection /
    // payload bloat), so everything outside the allowlist is dropped here.
    const rawCore = core as Record<string, unknown>;
    if (!upgradeFrom) {
      // Stray upgrade keys outside an upgrade run carry no meaning downstream;
      // strip them (visibly) instead of failing a core that is otherwise valid.
      const stray = UPGRADE_CORE_KEYS.filter((key) => rawCore[key] !== undefined);
      if (stray.length > 0) {
        console.warn(`[D-1.2] dropped upgrade metadata authored outside upgrade mode: ${stray.join(", ")}`);
        for (const key of stray) delete rawCore[key];
      }
    }
    const metadataParse = authoredMetadataSchema(upgradeFrom, rawCore, args.mode === "cold-start").safeParse(rawCore);
    const metadataViolations: string[] = metadataParse.success
      ? []
      : metadataParse.error.issues.map((issue) => {
        // A union failure hides the branch messages (e.g. the substantive-text
        // refinement) behind "Invalid input"; surface them so the feedback is actionable.
        const nested = issue.code === z.ZodIssueCode.invalid_union
          ? issue.unionErrors.flatMap((e) => e.issues.map((i) => i.message))
          : [];
        const detail = nested.length > 0 ? `${issue.message} (${[...new Set(nested)].join("; ")})` : issue.message;
        return `  [METADATA] ${issue.path.join(".")}: ${detail}`;
      });
    if (metadataParse.success && parentContract) {
      // Parent-membership join. Citation TEXT is deliberately not compared: a
      // reformatted citation under a reused key is not a provenance defect.
      const reused = metadataParse.data.reused_bibkeys ?? [];
      const added = metadataParse.data.new_bibkeys ?? [];
      const mislabeledReused = reused.filter((key) => !parentContract.bibliography.has(key));
      const mislabeledNew = added.filter((key) => parentContract.bibliography.has(key));
      if (mislabeledReused.length > 0 || mislabeledNew.length > 0) {
        metadataViolations.push(
          `  [METADATA] upgrade provenance does not match the banked parent bibliography: ` +
            `reused-not-parent=[${mislabeledReused.join(", ")}], new-already-parent=[${mislabeledNew.join(", ")}]`,
        );
      }
    }
    if (metadataViolations.length > 0) {
      const summary = `Stage -1.2 authored metadata is invalid:\n${metadataViolations.join("\n")}`;
      if (attempt === REAUTHOR_BUDGET) throw new Error(summary);
      lastGateFeedback = metadataViolations.join("\n");
      continue;
    }
    if (!metadataParse.success) throw new Error("unreachable: metadata violations were handled above");
    const authoredMetadata = metadataParse.data;
    const persistedCore: Record<string, unknown> = { ...typedCore, ...authoredMetadata };
    // The filesystem path is orchestrator-owned and already fixed in the author
    // prompt. Treat stdout only as a disposition/message receipt: a model typo in
    // its echoed path must not reject a valid artifact or leak the deleted staging
    // path into downstream state. Existence, JSON, gates, schema, and run identity
    // above are the authority; publish the canonical path deterministically.
    const stdoutHandoff = { ...parsedOut, artifacts: [corePath] };
    // The authored artifact is the sole authority for every reviewer metadata
    // field. The stdout object is merely a disposition/message/artifact receipt:
    // even a well-formed conflicting value must not rewrite validated core data.
    // Emitted-vs-persisted visibility (computed AFTER the folds so a key with a
    // persistence home is never falsely reported): the drop is intentional, but
    // it must never be SILENT — a prompt-mandated field missing from every
    // allowlist otherwise vanishes here and is only discovered rounds later as
    // a reviewer <MISSING> (the comparator_promise_table incident).
    const droppedKeys = Object.keys(rawCore).filter(
      (key) => !Object.prototype.hasOwnProperty.call(persistedCore, key),
    );
    if (droppedKeys.length > 0) {
      console.warn(
        `[D-1.2] persist boundary dropped non-schema key(s) from the authored core: ` +
          `${droppedKeys.join(", ")} — if the prompt mandates one of these, give it a home in ` +
          `CoreSchema or CORE_HANDOFF_KEYS (contract: prompt_schema_contract.test.ts)`,
      );
    }
    await writeJsonAtomic(corePath, persistedCore);
    await rm(attemptPath, { force: true });
    core = persistedCore;

    const handoff = mergeCoreHandoff(core as Record<string, unknown>, stdoutHandoff);

    return {
      status: "completed",
      message: parsedOut.message ?? "Stage -1.2 authored the proposal core",
      protoCoreJsonPath: corePath,
      handoff,
    };
  }

  // Unreachable: every iteration returns or throws (the budget-th attempt throws).
  throw new Error("Stage -1.2 author re-author loop exhausted without resolution");
}
