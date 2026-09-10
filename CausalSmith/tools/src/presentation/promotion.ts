import { readFile } from "node:fs/promises";
import { join } from "node:path";
import type { StageIO } from "./pipeline.js";
import { MODELS } from "../models.js";
import { bankAcceptedDir } from "./paths.js";

/** Marker P2 puts on the proof-audit failure so the pipeline can distinguish
 *  "proofs need helper lemmas" from every other P2 error. */
export const PROOF_AUDIT_FAILURE_MARKER = "P2 proof equivalence audit failed";
/** The judge left only rendering/citation defects (no `[missing-step]`): promotion cannot help,
 *  so P2 halts for adjudication under a marker the pipeline never promotes on. */
export const PROOF_AUDIT_RENDERING_MARKER = "P2 proof audit: rendering defects remain";

/**
 * Marks a halt asking the ORCHESTRATOR whether to promote again.
 *
 * The first promotion round runs automatically: a proof failing for want of a citable step is the
 * common case and the round is cheap. A SECOND round is a judgement call the pipeline cannot make.
 * Whether promoting again converges depends on WHY the proof failed — a genuine derivation gap
 * closes with another lemma, while a rendering defect (leaked conventions, mis-attribution, an
 * omitted conjunct) promotes for ever without closing anything, and that distinction lives in the
 * auditor's findings rather than in any property of the failing node. So the run halts here and
 * the orchestrator, which reads those findings, decides: re-run with `--promote-again` to grant
 * another round, or adjudicate the proof directly.
 */
export const PROMOTION_ESCALATION_MARKER = "P2 promotion decision required";

/**
 * PROMOTION ROUND (user-approved feature, kept deliberately simple — see the
 * lemma-promotion-round design note): when the P2 proof judge still reports a
 * `[missing-step]` after the renderer's repair rounds, that step's content needs
 * to become a citable auxiliary lemma — a journal paper's answer to a derivation
 * too long to inline. One agent call authors the bank-graph nodes; the caller
 * then re-runs P1 (delta: only the new statements render/audit) and retries P2
 * once. Selection needs no separate judge: the tagged issues ARE the criterion
 * (a rendering-only residual never reaches this path).
 *
 * Hard rules baked into the prompt (each one bought with an incident tonight):
 * every node must be backed by an existing proved Lean decl (never invented);
 * statement-uses edges identify actual mathematical prerequisites, not shared variable
 * spellings; authored outline homes place helpers before consumers; NL uses paper notation.
 */
export async function runPromotionRound(io: StageIO, failureDetail: string): Promise<string> {
  const graphPath = join(bankAcceptedDir(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec), "graph.json");
  const before = new Set(
    (JSON.parse(await readFile(graphPath, "utf8")).nodes as { id: string }[]).map((n) => n.id),
  );
  const prompt = `You are resolving a CausalSmith P2 proof-audit failure by PROMOTING helper content to paper lemmas.

The audit failure (each item names proof content that must become a citable auxiliary lemma, or a
small prose fix — promote ONLY [missing-step] items whose demanded derivation is substantive; leave
one-line fixes to the renderer's repair by not promoting them):
${failureDetail}

Bank graph to EDIT: ${graphPath}
Bundle (outline EDIT, proofs/layer READ): ${io.outDir}
Lean sources: resolve existing nodes' lean.file paths under ${join(io.ctx.repoRoot, io.bank.leanSubdir)}.

Method (follow exactly):
1. Map each substantive audit item to ONE existing Lean declaration via the failing proofs'
   \`% lean:\` tags (bundle proofs/*.tex) and the Lean sources. NEVER invent a declaration;
   grep each decl in the sources and confirm it is proved (no sorry).
2. For each, add a graph node copying the exact schema of an existing node whose id starts with
   "lem:" and has nl.frozen absent-or-true (use one added recently as template): id "lem:<kebab>",
   kind "lemma", provenance "from-note", nl {statement: faithful one-paragraph NL in the paper's
   notation (bundle outline.md # Notation), tex_anchor: "", frozen: true}, lean {decl_name
   fully-qualified, file relative}, review {status "matched", passed_hash: sha1 of the statement
   via the repo convention — run: cd ${join(io.ctx.repoRoot, "tools")} && npx tsx -e "import {statementHash} from './src/graph/hash.js'; console.log(statementHash(process.argv[1]))" '<statement>'
   , note: honest one-line mapping note}, proof {state "complete", sorry_count: 0}.
3. MANDATORY EDGES: add a "statement-uses" edge (source "declared") from each consumer (the failing
   proof's env id) to the new lemma, AND from the new lemma to definitions of named mathematical
   objects actually used in its statement. Resolve object identity from explicit references and
   meaning; a shared bound-variable spelling alone does not establish a dependency.
4. Outline: preserve every existing section and authored home. Insert each new id into the
   appendix home_objs line immediately BEFORE its first consumer (use objs only for a legacy
   section without home_objs). Also update that section's resolved objs line. P1 plans from
   home_objs, so editing only resolved objs loses the new placement.
5. Validate: graph.json parses; no duplicate ids; every edge endpoint exists; every graph paper
   object occurs exactly once across the authored home_objs lines (or legacy objs), and each
   resolved objs id is unique. Then STOP — do not run the pipeline.
Report: the mapping table (audit item -> decl -> node id), files changed, items NOT promoted and why.`;
  // DELIBERATE TRUST ESCALATION, visible here at the call site: unlike every other
  // runClaude usage (read-only judges), the promotion agent must edit the bank graph
  // and the bundle outline, and run the statementHash helper. Scope is still bounded
  // by the prompt's file list and the post-hoc node-count validation below.
  await io.ctx.deps.runClaude({
    prompt,
    model: MODELS.claudeMain,
    cwd: io.ctx.repoRoot,
    allowedTools: ["Read", "Glob", "Grep", "Edit", "Write", "Bash"],
  });
  const after = (JSON.parse(await readFile(graphPath, "utf8")).nodes as { id: string }[]).map((n) => n.id);
  const added = after.filter((id) => !before.has(id));
  if (added.length === 0) {
    throw new Error(`promotion round added no nodes; the original audit failure stands:\n${failureDetail}`);
  }
  return added.join(", ");
}
