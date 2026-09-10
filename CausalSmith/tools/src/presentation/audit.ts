import { readFile, writeFile, appendFile, mkdir } from "node:fs/promises";

import { join } from "node:path";
import { stripTexComments } from "../shared/tex_text.js";
import type { StageIO } from "./pipeline.js";
import { PRESENTATION_PROSE_POLICY_VERSION, presentationPrompt, promptFingerprint } from "./prompt_io.js";
import { notationForArtifact, parseOutline } from "./stage_util.js";
import { canonicalizeProofTitle, hashEnvBody, parseAnchoredEnvs, repairObjRefs, type AnchoredEnv, type LintProblem } from "./tex_anchors.js";
import { FormalLayerSource, type FormalBlock } from "./formal_layer.js";
import { bankAcceptedDir } from "./paths.js";
import { saveGraph, graphPath } from "../graph/store.js";
import { extractDeclSnippet, extractFullDeclSource } from "./lean_extract.js";
import { parseLeanDecls } from "../formalization/crosswalk.js";
import { ensureComponentsForEnvs, assembleComponentText, componentSignature, buildModuleDeclIndex } from "./components.js";
import { helperDeclarationsFor, sectionContextBefore } from "./lean_one_hop.js";
import { parseNoteBlocks } from "./note_parser.js";
import { writeJsonAtomic, writeTextAtomic } from "./json_io.js";
import { loadJsonCache } from "./cache.js";
import { proofFilePath } from "./proof_files.js";
import { resolveLeanDeclaration, resolvedLeanAbsolutePath } from "./declaration_resolver.js";
export { resolveLeanDeclaration } from "./declaration_resolver.js";
import { parseJsonLoose, mapLimit, type StatementCheck } from "./gates.js";

/**
 * Per-artifact Lean-equivalence audits, co-located with the stage that PRODUCES the artifact
 * (design: "the review of a produced artifact belongs directly after that stage"):
 *   • `judgeStatements` runs inside P1's render loop — the moment the statements are rendered — and
 *     judges each paper env body against its Lean declaration; P1 feeds a drift verdict back to its
 *     renderer and freezes faithful bodies onto the graph (`nl.frozen_body`) once the layer settles.
 *   • `runProofAudit` runs at P2 — the moment the appendix proofs are rendered — and judges each
 *     proof's prose against its machine-verified Lean proof; an unfaithful proof is re-rendered by
 *     P2's own renderer with the judge's issues as defects.
 * P3 keeps only the WHOLE-PAPER gates (overclaim, citation support, anchor lint, rubric).
 */

const MAX_ROUNDS = 2;
/** Max concurrent codex audits. Each statement/proof is checked against its OWN Lean decl, so the
 *  audits (and the judge → repair loops) are independent and run concurrently. */
const AUDIT_CONCURRENCY = 6;

/** Claims about algorithms, computability, or complexity are especially easy for a
 * batched reviewer to credit to a nearby sibling theorem instead of the declaration
 * actually mapped to the paper environment. Give those statements an individual,
 * source-reading audit so declaration-local support remains the criterion. */
export function requiresIndividualStatementAudit(body: string): boolean {
  return /\b(?:comput(?:able|ability|ation)|algorithm(?:ic)?|complexity|operation(?:-count|s)?|running\s+time|runtime)\b|O\s*\(/i.test(body);
}

/** Content key for one statement's equivalence verdict. One definition for BOTH the pre-audit
 *  lookup and the verdict stamp.
 *  why: Lean edits, trust-boundary edits, or a verdict-POLICY change (v2 = over-assumption is
 *  drift) must invalidate verdicts; citation-erasure-v1 covers the cited-dependency prompt. */
export function equivalenceAuditKey(parts: {
  envBody: string; mapping: string; leanStatement: string; refDefs: string; citedDependencies: string;
}): string {
  // (2026-08-21, no bump) IMPLEMENTATION PACKAGING clause added to both equivalence prompts:
  // it only widens FAITHFUL, and the cache short-circuits faithful verdicts only, so replay
  // of cached verdicts is sound — a bump would just re-buy ~all faithful verdicts.
  // Missing-coverage only distinguishes a mapping failure from drift; neither approves
  // a statement. Keep existing faithful receipts under the same acceptance criterion.
  // equivalence-v3: the statement auditor now receives the contract DIGEST instead of
  // the full authoring contracts (with a small added flag-in-schema remit) — a
  // deliberate one-time re-audit sweep per bundle at its next P1 entry. This key has
  // NO prompt fingerprint: future contract_digest.txt edits self-invalidate only
  // proof_audit and the P1 notation cache; statement-equivalence (and the P3 gate
  // caches, which deliberately did not sweep for this change) need a hand bump here.
  return hashEnvBody(`${parts.envBody}|${parts.mapping}|${parts.leanStatement}|${parts.refDefs}|citation-erasure-v1|equivalence-v3|${parts.citedDependencies}`);
}

/** Keyed on the audit PROMPT (and prose policy version): the verdict depends on what the auditor
 *  is asked to check, so widening the gate — by prompt edit or policy bump — must not read a
 *  verdict cached under the narrower standard; an unchanged proof would silently keep its stale
 *  `faithful`. The prompt fingerprint makes prompt-only widenings self-invalidating (same pattern
 *  as P1's promptFp), removing the "did any run execute since the bump?" timing dependence.
 *  `formalContext` is `proofAuditFormalContext` — the statements the verdict can depend on (the
 *  target, the environments the proof cites, and every definition/assumption), order-independent —
 *  so a promoted lemma, a re-rendered theorem elsewhere, or a P1 order repair keeps approvals. */
export function proofAuditCacheKey(parts: {
  proofTex: string; leanPointer: string; leanProofCacheSource: string; notationTable: string; auditPromptFp: string;
  formalContext: string;
}): string {
  return hashEnvBody(`${PRESENTATION_PROSE_POLICY_VERSION}|${parts.auditPromptFp}|${parts.formalContext}|${parts.proofTex}|${parts.leanPointer}|${parts.leanProofCacheSource}|${proofAuditSemanticNotation(parts.notationTable)}`);
}

/** The key formula before the closure-keyed context (whole `formal_layer.tex` hash, target body,
 *  absolute Lean path). Read-only transition: a row stamped with it is honoured and re-stamped
 *  under the current key, so the key change itself never re-judges a proof. Delete once every
 *  live bundle has re-entered P2 (2026-09). */
function legacyProofAuditCacheKey(parts: {
  proofTex: string; leanPointer: string; leanProofCacheSource: string; notationTable: string; auditPromptFp: string;
  targetStatement: string; formalSource: string;
}): string {
  return hashEnvBody(`${PRESENTATION_PROSE_POLICY_VERSION}|${parts.auditPromptFp}|${hashEnvBody(parts.formalSource)}|${parts.targetStatement}|${parts.proofTex}|${parts.leanPointer}|${parts.leanProofCacheSource}|${proofAuditSemanticNotation(parts.notationTable)}`);
}

/** Fingerprints of `proof_audit` before a prompt edit that only ADDED deterministic context
 *  (the helper declarations the Lean proof names, 2026-09-10). Such an edit cannot narrow a
 *  verdict, so a row stamped under one of these is honoured once and re-stamped. Delete once the
 *  live bundles have re-entered P2. */
export const LEGACY_PROOF_AUDIT_PROMPT_FPS = ["c4ed03d34c039a4c6b10e632b2946bda021f718b38a0ed22b5c47671a827db67"];

/** Proof validity depends on symbol spelling and reader-facing meaning, not on
 * notation-table row placement or the outline section that owns the symbol. */
export function proofAuditSemanticNotation(notationTable: string): string {
  const semanticRows: string[] = [];
  for (const raw of notationTable.split("\n")) {
    const line = raw.trim();
    if (!line) continue;
    if (line.startsWith("|") && line.endsWith("|")) {
      const cells = line.slice(1, -1).split("|").map((cell) => cell.replace(/\s+/g, " ").trim());
      if (cells.length >= 4 && !/^[-: ]+$/.test(cells.join("")) &&
          cells[1].toLowerCase() !== "paper notation")
        semanticRows.push(`${cells[1]}|${cells[0]}|${cells[2]}`);
    }
  }
  return semanticRows.sort((a, b) => a.localeCompare(b)).join("\n");
}

const ask = async (out: Promise<{ stdout: string; stderr: string }>) =>
  parseJsonLoose((await out).stdout);

/** A cached Lean-source reader (one read per file across an audit run). */
function leanSourceReader(repoRoot: string, leanSubdir: string) {
  const cache = new Map<string, string>();
  return async (file: string) => {
    if (!cache.has(file)) cache.set(file, await readFile(join(repoRoot, leanSubdir, file), "utf8"));
    return cache.get(file)!;
  };
}

/**
 * One-hop definition index for a judge or renderer: the actual definition bodies its Lean statement
 * references (e.g. `clipBias`'s formula), not just a name to self-fetch. Returns `unfold(leanText)`.
 */
async function buildRefDefUnfolder(
  repoRoot: string,
  leanSubdir: string,
  leanSource: (file: string) => Promise<string>,
): Promise<(leanText: string) => Promise<string>> {
  const inlineKinds = new Set(["def", "abbrev", "structure"]);
  const refDeclByName = new Map<string, { file: string; line: number; declKind: string }>();
  try {
    for (const d of await parseLeanDecls(join(repoRoot, leanSubdir), {})) {
      if (inlineKinds.has(d.declKind) && !refDeclByName.has(d.name)) {
        refDeclByName.set(d.name, { file: d.file, line: d.line, declKind: d.declKind });
      }
    }
  } catch {
    /* best-effort: the judge still has lean-lsp to self-fetch */
  }
  return async (leanText: string): Promise<string> => {
    const names = new Set(leanText.match(/[A-Za-z_][A-Za-z0-9_']*/g) ?? []);
    const inlined: string[] = [];
    for (const nm of names) {
      if (inlined.length >= 12) break;
      const loc = refDeclByName.get(nm);
      if (!loc) continue;
      try {
        const snip = extractDeclSnippet(await leanSource(loc.file), nm, loc.line);
        if (snip) inlined.push(`-- ${nm} (${loc.declKind}) in ${loc.file}\n${snip}`);
      } catch {
        /* skip a decl whose body can't be extracted */
      }
    }
    return inlined.join("\n\n");
  };
}

/** Append a human-readable repair report (the judge found the proof unfaithful; the renderer re-wrote it). */
async function appendDriftReport(
  outDir: string,
  objId: string,
  before: string,
  after: string,
  rounds: number,
  faithful: boolean,
): Promise<void> {
  const dir = join(outDir, "logs");
  await mkdir(dir, { recursive: true });
  await appendFile(
    join(dir, "graph_nl_drift.md"),
    `\n## ${objId} — re-rendered toward Lean in ${rounds} round(s); final verdict ${faithful ? "faithful" : "UNFAITHFUL"}\n` +
      `\n**Before:**\n\n\`\`\`\n${before.trim()}\n\`\`\`\n\n**After:**\n\n\`\`\`\n${after.trim()}\n\`\`\`\n`,
    "utf8",
  );
}

/** One statement's Lean counterpart as resolved for the judge — reusable by a renderer that
 *  must repair a drifting body toward it. */
export interface StatementLeanContext {
  leanStatement: string;
  leanPointer: string;
  refDefs: string;
  citedDependencies: string;
}
export interface StatementJudgement {
  verdict: "faithful" | "drift" | "missing-coverage";
  detail?: string;
}
export interface StatementJudgeOutcome {
  /** obj_id → verdict, for every env-bearing block with a Lean counterpart (presentation-
   *  synthesized and undelivered blocks have none and are not judged). */
  verdicts: Map<string, StatementJudgement>;
  contexts: Map<string, StatementLeanContext>;
}

/**
 * Freeze audit-faithful bodies onto the bank graph (`nl.frozen_body` / `frozen_title`) so a
 * re-run reuses them verbatim. P1 calls this ONCE, after the notation reviewer, the Lean judge
 * and the order check agree on the same bodies — never mid-flight, so a halted run leaves no
 * half-frozen layer behind.
 */
export async function persistFrozenBodies(
  io: StageIO,
  faithful: ReadonlyMap<string, { body: string; title: string | null }>,
): Promise<number> {
  let n = 0;
  for (const [objId, { body, title }] of faithful) {
    const node = io.bank.graph.nodes.find((x) => x.id === objId);
    if (!node || node.delivery?.status === "undelivered") continue;
    const trimmed = body.trim();
    if (node.nl.frozen_body === trimmed && node.nl.frozen_title === title) continue;
    node.nl.frozen_body = trimmed;
    node.nl.frozen_title = title;
    n += 1;
  }
  if (n > 0) {
    await saveGraph(graphPath(bankAcceptedDir(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec), io.ctx.qid, io.ctx.spec), io.bank.graph);
    io.state.notes.push(`P1: persisted ${n} audit-faithful statement body/bodies to the bank graph (nl.frozen_body) — a re-run reuses them verbatim instead of re-rendering.`);
  }
  return n;
}

/** Judge the persisted layer, freeze what is faithful, report drift (P1 internals and tests). */
export async function runStatementAudit(io: StageIO): Promise<LintProblem[]> {
  const out = await auditStatements(io);
  await persistFrozenBodies(io, out.faithful);
  return out.problems;
}

/** Judge `formal_layer.json` as it stands: drift verdicts as `equivalence` problems, faithful
 *  bodies as freeze candidates. Read-only on the layer. */
export async function auditStatements(io: StageIO): Promise<{ problems: LintProblem[]; faithful: Map<string, { body: string; title: string | null }> }> {
  const layer = FormalLayerSource.parse(JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")));
  const { verdicts } = await judgeStatements(io, layer.blocks);
  const problems: LintProblem[] = [];
  const faithful = new Map<string, { body: string; title: string | null }>();
  for (const b of layer.blocks) {
    const v = verdicts.get(b.obj_id);
    if (!v) continue;
    if (v.verdict === "faithful") faithful.set(b.obj_id, { body: b.body.trim(), title: b.title ?? null });
    else problems.push({ gate: v.verdict === "missing-coverage" ? "lean-coverage" : "equivalence",
      objId: b.obj_id, detail: `${b.obj_id}: ${v.detail ?? v.verdict}` });
  }
  await mkdir(join(io.outDir, "logs"), { recursive: true });
  await appendFile(join(io.outDir, "logs", "reviews.jsonl"), JSON.stringify({ kind: "equivalence", problems }) + "\n", "utf8");
  return { problems, faithful };
}

/**
 * P1 STATEMENT EQUIVALENCE JUDGE — verdict only. Every env-bearing block with a Lean
 * counterpart is compared against it: a tiered batch pre-audit (lemmas ≤3 at high effort,
 * definitions/assumptions ≤5 at medium) and an individual high-effort audit for theorems and
 * for anything the batch did not answer. Verdicts are content-keyed in `equivalence_cache.json`
 * (faithful and missing-coverage verdicts are reused across runs; drift is re-asked) and in `memo` within
 * a run. Nothing is rewritten or frozen here: P1 hands a drift verdict back to its renderer as
 * a defect and freezes faithful bodies once the whole layer has settled.
 */
export async function judgeStatements(
  io: StageIO,
  blocks: readonly FormalBlock[],
  memo: Map<string, StatementJudgement> = new Map(),
): Promise<StatementJudgeOutcome> {
  const { deps, repoRoot } = io.ctx;
  const leanSubdir = io.bank.leanSubdir;
  const leanSource = leanSourceReader(repoRoot, leanSubdir);
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  const citedTextByObjId = new Map(blocks.map((b) => [
    b.obj_id,
    b.cited_dependencies.length === 0
      ? "(none — no Lean premise may be erased)"
      : b.cited_dependencies.map((d) =>
          `- ${d.node_id}: ${d.statement.replace(/\s+/g, " ").trim()} [${d.cite_id}; ${d.locator ?? "locator unavailable"}; status ${d.status}]`,
        ).join("\n"),
  ] as const));
  // An undelivered node prints an open-direction remark, not a statement of its Lean target.
  const envs: AnchoredEnv[] = blocks
    .filter((b) => b.env && b.status !== "undelivered")
    .map((b, i) => ({ env: b.env!, obj_id: b.obj_id, title: b.title, body: b.body, order: i }));
  const verdicts = new Map<string, StatementJudgement>();
  const contexts = new Map<string, StatementLeanContext>();
  if (envs.length === 0) return { verdicts, contexts };

  // Verdict cache keyed by (env body, decl pointer, referenced defs, trust boundary): a body
  // already judged faithful is skipped unless any of those changed.
  const cachePath = join(io.outDir, "equivalence_cache.json");
  const cache = await loadJsonCache<Record<string, { key: string; verdict: string; detail?: string }>>(cachePath);

  // Component sets (shared cache with P4): a bundled / hypothesis-only assumption is verified against
  // ALL its Lean pieces, not the single first-wins crosswalk anchor. Graph-first discovery (matches P4).
  const aliasToNodeId = new Map<string, string>();
  for (const n of io.bank.graph.nodes) if (n.obj_id) aliasToNodeId.set(n.obj_id, n.id);
  const { components: componentsMap, complete: componentReceipts, moduleDecls } = await ensureComponentsForEnvs({
    envs,
    crosswalk: io.bank.crosswalk,
    repoRoot,
    leanSubdir,
    cachePath: join(io.outDir, "components_cache.json"),
    deps,
    noteBlocks: new Map(
      parseNoteBlocks(io.bank.noteMd).map((b) => [aliasToNodeId.get(b.obj_id) ?? b.obj_id, b.body]),
    ),
    graph: io.bank.graph,
  });
  const unfoldReferencedDefs = await buildRefDefUnfolder(repoRoot, leanSubdir, leanSource);
  // What the judge used to fetch by hand: the unfolded definitions the statement names and the
  // section context in scope at the declaration. Prompt-only (the key already carries refDefs).
  const referencedContext = new Map<string, string>();

  const equivalence = async (s: StatementCheck): Promise<StatementJudgement> => {
    const v = (await ask(
      deps.runCodex({
        prompt: await presentationPrompt("statement_equivalence", {
          obj_id: s.obj_id,
          env_body: s.envBody,
          lean_statement: s.leanStatement,
          lean_pointer: s.leanPointer,
          notation_table: notation,
          cited_dependencies: s.citedDependencies ?? "(none — no Lean premise may be erased)",
          referenced_definitions: referencedContext.get(s.obj_id) ?? "(none resolved)",
        }),
        cwd: repoRoot,
        // Theorems/lemmas carry the quantifier/rate/witness structure where deep reasoning pays;
        // definitions/assumptions are short structural comparisons — medium suffices (cost economy).
        reasoningEffort: s.isMainResult ? "high" : "medium",
        leanLsp: true,
      }),
    )) as { verdict?: string; detail?: string } | null;
    if (v?.verdict === "faithful" || v?.verdict === "missing-coverage") {
      return { verdict: v.verdict, detail: v.detail };
    }
    return { verdict: "drift", detail: v?.detail ?? "unparseable auditor output" };
  };

  // A block that is NOT a bank object (a definition P1 rendered from the Lean declaration that
  // defines its symbols) is anchored by its own Lean pointer; a bank object is anchored by its
  // crosswalk row only, so a row without a Lean anchor still fails loudly below.
  const blockLean = new Map(blocks.flatMap((b) => b.lean ? [[b.obj_id, { file: b.lean.file, decl: b.lean.decl, line: 0 }] as const] : []));
  const statements: (StatementCheck & { cacheKey: string; env: string })[] = [];
  for (const e of envs) {
    const cw = io.bank.crosswalk.find((c) => c.obj_id === e.obj_id);
    const anchor = cw ? cw.lean : blockLean.get(e.obj_id);
    const comps = componentsMap[e.obj_id] ?? [];
    const componentReceipt = componentReceipts[e.obj_id] === true;
    if (comps.length > 0 && !componentReceipt) {
      throw new Error(`P1 component mapping for ${e.obj_id} is missing its completeness receipt`);
    }
    let leanStatement: string | null = null;
    let leanPointer = "";
    let mapping = "";
    // Pre-2026-09-09 keys carried source LINE numbers; a docstring edit above a declaration then
    // re-judged every statement in the file although the snippet hash already keys its content.
    // A row stamped with the line-carrying key is honoured once and re-stamped. Delete this
    // fallback once every live bundle has re-entered P1.
    let legacyMapping = "";
    if (comps.length > 0) {
      const assembled = await assembleComponentText({
        specs: comps,
        crosswalk: io.bank.crosswalk,
        moduleDecls,
        repoRoot,
        leanSubdir,
      });
      if (assembled.text) {
        leanStatement = assembled.text;
        mapping = `components:${componentSignature(comps)}:` + assembled.resolved
          .map((r) => `${r.file}:${r.decl}:${hashEnvBody(r.snippet)}`).sort().join("|");
        legacyMapping = `components:${componentSignature(comps)}:` + assembled.resolved
          .map((r) => `${r.file}:${r.decl}:${r.line}:${hashEnvBody(r.snippet)}`).sort().join("|");
        leanPointer =
          `Formalized by ${comps.length} Lean piece(s) — ` +
          comps
            .map((c) => (c.type === "decl" ? c.decl : `hypotheses {${c.binders.join(", ")}} of ${c.theorem}`))
            .join("; ") +
          `. Read each in ${leanSubdir} before judging; every paper clause must map to SOME piece.`;
      }
    }
    if (leanStatement === null && anchor) {
      const resolved = await resolveLeanDeclaration(repoRoot, leanSubdir, anchor);
      leanStatement = resolved.snippet;
      mapping = `${resolved.file}:${resolved.decl}`;
      legacyMapping = `${resolved.file}:${resolved.decl}:${resolved.line}`;
      const abs = await resolvedLeanAbsolutePath(repoRoot, resolved.file);
      leanPointer = `file: ${abs}\ndeclaration: ${resolved.decl} (around line ${resolved.line})\nThe section context and referenced definitions are supplied below; read the file only for what they lack.`;
      const scope = sectionContextBefore(await readFile(abs, "utf8").catch(() => ""), resolved.line);
      if (scope) referencedContext.set(e.obj_id, `-- section context in scope at ${resolved.decl}\n${scope}`);
      if (resolved.relocated) {
        io.state.notes.push(
          `P1: resolved re-exported Lean declaration for ${e.obj_id}: ${anchor.file}:${anchor.decl} -> ` +
          `${resolved.file}:${resolved.decl}:${resolved.line} (${resolved.resolution})`,
        );
      }
    }
    if (leanStatement === null) {
      const graphNode = io.bank.graph.nodes.find((n) => n.id === e.obj_id || n.obj_id === e.obj_id);
      // Presentation-synthesized definitions have no bank crosswalk/graph identity and
      // are legitimately prose-only. A bank-backed formal object is never silently
      // downgraded to note-only because discovery returned [] or a stale partial cache.
      if (cw || graphNode) {
        const receipt = componentReceipt ? "complete component discovery returned no pieces" : "no complete component discovery receipt";
        throw new Error(`P1 formal object ${e.obj_id} has neither a resolved Lean declaration nor nonempty resolved components (${receipt})`);
      }
      continue;
    }
    const refDefs = await unfoldReferencedDefs(leanStatement);
    if (refDefs) referencedContext.set(e.obj_id, [referencedContext.get(e.obj_id), refDefs].filter(Boolean).join("\n\n"));
    const citedDependencies = citedTextByObjId.get(e.obj_id) ?? "(none — no Lean premise may be erased)";
    contexts.set(e.obj_id, { leanStatement, leanPointer, refDefs, citedDependencies });
    const key = equivalenceAuditKey({ envBody: e.body, mapping, leanStatement, refDefs, citedDependencies });
    const remembered = memo.get(key);
    if (remembered) {
      verdicts.set(e.obj_id, remembered);
      continue;
    }
    const hit = cache[e.obj_id];
    if (hit && hit.key !== key && hit.key === equivalenceAuditKey({ envBody: e.body, mapping: legacyMapping, leanStatement, refDefs, citedDependencies })) {
      hit.key = key;
      await writeJsonAtomic(cachePath, cache);
    }
    // An unchanged coverage failure cannot be repaired by paying the same judge again.
    // Correcting mapped declarations changes this key and permits a fresh audit.
    if (hit?.key === key && (hit.verdict === "faithful" || hit.verdict === "missing-coverage")) {
      verdicts.set(e.obj_id, { verdict: hit.verdict, detail: hit.detail });
      memo.set(key, verdicts.get(e.obj_id)!);
      continue;
    }
    statements.push({
      obj_id: e.obj_id,
      envBody: e.body,
      leanStatement,
      leanPointer,
      isMainResult: e.env === "theoremv" || e.env === "lemmav",
      cacheKey: key,
      env: e.env,
      citedDependencies,
    });
  }

  // Tiered batch pre-audit (mirrors the F2.5 reviewer). THEOREMS get individual high-effort calls.
  // LEMMAS batch ≤3 at HIGH effort. DEFINITIONS/ASSUMPTIONS batch ≤5 at MEDIUM. A batch verdict
  // pre-empts the individual call; anything missing falls through to its own individual call.
  const LEMMA_BATCH = 3;
  const SHALLOW_BATCH = 5;
  const batchVerdicts = new Map<string, StatementJudgement>();
  const groupsOf = <T>(arr: T[], size: number): T[][] => {
    const out: T[][] = [];
    for (let i = 0; i < arr.length; i += size) {
      const g = arr.slice(i, i + size);
      if (g.length >= 2) out.push(g); // a singleton is cheaper as an individual call
    }
    return out;
  };
  const batchJobs: { group: typeof statements; effort: "high" | "medium" }[] = [
    ...groupsOf(statements.filter((s) => s.env === "lemmav" && !s.citedDependencies?.startsWith("- ")), LEMMA_BATCH).map((group) => ({ group, effort: "high" as const })),
    ...groupsOf(statements.filter((s) =>
      !s.isMainResult &&
      !s.citedDependencies?.startsWith("- ") &&
      !requiresIndividualStatementAudit(s.envBody)
    ), SHALLOW_BATCH).map((group) => ({ group, effort: "medium" as const })),
  ];
  const remember = (s: { obj_id: string; cacheKey: string }, v: StatementJudgement) => {
    verdicts.set(s.obj_id, v);
    memo.set(s.cacheKey, v);
    cache[s.obj_id] = { key: s.cacheKey, verdict: v.verdict, detail: v.detail };
  };
  await mapLimit(batchJobs, AUDIT_CONCURRENCY, async ({ group, effort }) => {
    const block = group
      .map(
        (s) =>
          `--- ${s.obj_id} ---\nPaper environment body:\n${s.envBody}\n\nLean statement:\n${s.leanStatement}\n\nLean source location:\n${s.leanPointer}`,
      )
      .join("\n\n");
    try {
      const parsed = (await ask(
        deps.runCodex({
          prompt: await presentationPrompt("statement_equivalence_batch", { statements_block: block, notation_table: notation }),
          cwd: repoRoot,
          reasoningEffort: effort,
          leanLsp: true,
        }),
      )) as { results?: { obj_id?: string; verdict?: string; detail?: string }[] } | null;
      let adopted = 0;
      for (const r of parsed?.results ?? []) {
        if (r.obj_id && (r.verdict === "faithful" || r.verdict === "drift" || r.verdict === "missing-coverage")) {
          const st = group.find((x) => x.obj_id === r.obj_id);
          if (!st) continue;
          batchVerdicts.set(r.obj_id, { verdict: r.verdict, detail: r.detail });
          remember(st, { verdict: r.verdict, detail: r.detail });
          adopted += 1;
        }
      }
      // Persist each batch's verdicts as they land (atomic write; concurrent workers are safe):
      // an interruption must not lose hours of paid audits.
      await writeJsonAtomic(cachePath, cache);
      // A systematically misparsed batch doubles the audit cost with no trace but agent_calls.log.
      if (adopted === 0) {
        console.error(`[statement-equivalence] batch reply contributed no verdicts (${group.length} statement(s) fall through to individual audits)`);
      }
    } catch (e) {
      console.error(`[statement-equivalence] batch dispatch failed (${(e as Error).message?.slice(0, 80)}) — ${group.length} statement(s) fall through to individual audits`);
    }
  });
  // Individual audits in PARALLEL (each statement vs its own Lean is independent).
  await mapLimit(statements.filter((s) => !batchVerdicts.has(s.obj_id)), AUDIT_CONCURRENCY, async (s) => {
    remember(s, await equivalence(s));
    await writeJsonAtomic(cachePath, cache); // incremental persistence — see the batch loop note
  });
  await writeJsonAtomic(cachePath, cache); // why: the equivalence cache is the P4 trust anchor — a corrupt write must not survive.
  return { verdicts, contexts };
}

/** Re-render a proof with the judge's issues as defects (P2 supplies it: the same `p2_proof` prompt
 *  that wrote the proof, given the prior proof and the tagged issues). `null` = the renderer could
 *  produce a valid repair; the prior proof then stands and halts. */
export type ProofRenderHook = (objId: string, priorProof: string, issues: string[], previousIssues: readonly string[]) => Promise<string | null>;

/** A proof still unfaithful after repair. `promotable` iff the judge tagged an issue
 *  `[missing-step]` — content the Lean derives that no paper environment supplies, the one
 *  case a promoted helper lemma can fix; rendering/citation defects never promote. */
export interface ProofAuditProblem extends LintProblem {
  issues: string[];
  promotable: boolean;
}

export const isMissingStepIssue = (issue: string): boolean => /^\s*\[missing-step\]/i.test(issue);

/**
 * Deterministic missing-citation check: paper result envs whose realized Lean declaration the
 * proof's own Lean source DIRECTLY invokes, but whose environment the rendered proof never
 * `\cref`s. The p2_proof rule ("a route step realized by a paper env is rendered as a citation,
 * never an inline re-derivation") is otherwise enforced only by prompt; this closes the common
 * direct-invocation case from ground truth (the decl source), leaving transitive helper-mediated
 * uses to the isolated-lemma assembly gate. Matching is by the declaration's final name segment as
 * a whole word — Lean call sites use the open-namespace short name. A per-proof AUDIT issue (the
 * renderer adds the citation) rather than a hard gate: the bank's `proof-uses` edges are heuristic
 * and a textual match can over-trigger; a wasted repair round is cheap, a false halt is not.
 */
export function missingRealizedCitations(
  leanProofSource: string,
  proofTex: string,
  citables: readonly { objId: string; decl: string }[],
  selfObjId: string,
): { objId: string; decl: string }[] {
  if (!leanProofSource) return [];
  const out: { objId: string; decl: string }[] = [];
  for (const c of citables) {
    if (c.objId === selfObjId || !c.decl) continue;
    const short = c.decl.split(".").pop()!;
    if (!short) continue;
    // Trailing boundary includes ?/! — `get?`/`find!` are ordinary Lean names, and a citable whose
    // final segment is their prefix must not match them (mirrors dead_helpers.ts).
    const wordRe = new RegExp(`(?<![A-Za-z0-9_'])${short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![A-Za-z0-9_?!'])`);
    if (!wordRe.test(leanProofSource)) continue;
    if (proofTex.includes(`obj:${c.objId}`)) continue;
    out.push(c);
  }
  return out;
}

/** The statements a proof's translation is judged against: the one it proves and the ones it
 *  cites by `\cref` — a citation asserts that the cited statement supplies a fact, which is checked
 *  against that statement's printed text. One hop only: what a cited statement itself rests on is
 *  that statement's own faithfulness to its Lean, settled at P1. */
export function proofDirectStatements(envs: readonly AnchoredEnv[], objId: string, proof: string): AnchoredEnv[] {
  const wanted = new Set([objId]);
  for (const match of stripTexComments(proof).matchAll(/\\(?:Cref|cref|ref)\{([^}]+)\}/g)) {
    for (const label of match[1].split(",").map(s => s.trim())) {
      if (label.startsWith("obj:")) wanted.add(label.slice(4));
    }
  }
  return envs.filter(env => wanted.has(env.obj_id));
}

/** Exact current statements the judge checks the proof against, from the same formal-layer text
 * the verdict key hashes. Any other environment stays retrievable from the source file. */
export function proofAuditPaperContext(envs: readonly AnchoredEnv[], objId: string, proof: string): string {
  return [
    "Exact statement excerpts from that source (the result this proof proves and the statements it cites; retrieve any other object needed):",
    ...proofDirectStatements(envs, objId, proof).map(env =>
      `--- ${env.obj_id} (${env.env}${env.title ? `: ${env.title}` : ""}) ---\n${env.body}`),
  ].join("\n\n");
}

/**
 * The formal context a proof verdict is keyed on: the target statement and the statements the
 * proof cites, as sorted `id|env|title|body` lines (layer ORDER never enters). The audit judges
 * whether the prose faithfully renders the Lean proof; a definition, assumption, remark or result
 * the proof does not name cannot change that verdict — if its content is wrong, that is its own
 * statement's faithfulness problem, settled at P1 — so it does not invalidate the approval.
 */
export function proofAuditFormalContext(envs: readonly AnchoredEnv[], objId: string, proof: string): string {
  return proofDirectStatements(envs, objId, proof)
    .map(env => `${env.obj_id}|${env.env}|${env.title ?? ""}|${env.body.replace(/\s+/g, " ").trim()}`)
    .sort()
    .join("\n");
}

/**
 * P2 PROOF EQUIVALENCE AUDIT — one writer, one judge. Each rendered appendix proof is judged
 * against its machine-verified Lean proof (`proof_audit`, verdict cached per proof body); an
 * unfaithful proof is RE-RENDERED by the same renderer that wrote it, with the judge's tagged
 * issues as defects, and judged again (≤MAX_ROUNDS). There is no separate "refiner": a second
 * writer that only deleted prose could never supply a step the judge said was missing, and its
 * deletions had to be guarded and discarded (the 2026-08-22/25/26 loops). Persists the last
 * proof per target to `proofs/<obj_id>.tex`; returns the final text for EVERY proof (assembly
 * uses it) plus the residual problems, each marked `promotable` when a `[missing-step]` issue
 * remains — the only case in which P2's promotion round can help.
 */
export async function runProofAudit(
  io: StageIO,
  proofTargets: { obj_id: string; isMain: boolean; lean: { file: string; decl: string } }[],
  render: ProofRenderHook,
  repairContextKeys: ReadonlyMap<string, string> = new Map(),
): Promise<{ refined: Map<string, string>; problems: ProofAuditProblem[] }> {
  const { deps, repoRoot } = io.ctx;
  const leanSubdir = io.bank.leanSubdir;
  const notation = parseOutline(await readFile(join(io.outDir, "outline.md"), "utf8")).notation;
  const declByNode = new Map((io.bank.graph?.nodes ?? [])
    .filter((n) => n.lean?.decl_name)
    .map((n) => [n.id, n.lean!.decl_name] as const));
  // The SOURCE of truth for statements is formal_layer.json (formal_layer.tex is a derived view that
  // an in-flight P1 or a hand edit can leave stale): the judge's excerpts, the reference check and
  // the approval key all read the blocks. Read once so every worker keys on the same snapshot.
  const allLayerBlocks = (JSON.parse(await readFile(join(io.outDir, "formal_layer.json"), "utf8")).blocks ?? []) as
    { obj_id: string; env: string | null; title?: string | null; body: string }[];
  const formalEnvs: AnchoredEnv[] = allLayerBlocks.flatMap((b, i) =>
    b.env ? [{ env: b.env as AnchoredEnv["env"], obj_id: b.obj_id, title: b.title ?? null, body: b.body, order: i }] : []);
  const layerIds = new Set(formalEnvs.map((e) => e.obj_id));
  // Only the pre-closure legacy key hashed the derived .tex; read it just to honour those rows.
  const formalSource = await readFile(join(io.outDir, "formal_layer.tex"), "utf8").catch(() => "");
  const reviewsPath = join(io.outDir, "logs", "reviews.jsonl");
  await mkdir(join(io.outDir, "logs"), { recursive: true });

  // Verdict cache keyed by (proof body, decl pointer): a proof already judged faithful is skipped.
  const cachePath = join(io.outDir, "proof_audit_cache.json");
  const cache = await loadJsonCache<Record<string, {
    key: string; verdict: string; issues?: string[];
    repairStoppedKey?: string;
  }>>(cachePath);
  const saveCache = () => writeJsonAtomic(cachePath, cache); // why: workers save concurrently under mapLimit — interleaved plain writes can corrupt the cache.

  const auditPromptFp = await promptFingerprint("proof_audit");
  const repairPromptFp = await promptFingerprint("p2_proof");
  // Lemma envs with a realized decl — the deterministic missing-citation check's citable set.
  // Lemmas only, matching the isolated-lemma rule this check upstreams (a proof invoking a
  // paper LEMMA's decl must cite it); theorem-to-theorem citation stays the judge's call.
  const resultCitables = allLayerBlocks
    .filter((b) => b.env === "lemmav")
    .flatMap((b) => {
      const decl = declByNode.get(b.obj_id);
      return decl ? [{ objId: b.obj_id, decl }] : [];
    });
  // UNFILTERED lookup: propositionv proofs are judged too and the citable list excludes them —
  // a filtered lookup would leave their targetStatement permanently "".
  const targetStatementFor = (objId: string): string =>
    allLayerBlocks.find((b) => b.obj_id === objId)?.body ?? "";
  type JudgeInput = { obj_id: string; proofTex: string; leanPointer: string; leanKeyPointer: string; leanProofSource: string; leanProofCacheSource: string; notationTable: string; tier: "main" | "auxiliary"; helperDeclarations: string };
  const auditKey = (p: JudgeInput) => proofAuditCacheKey({
    proofTex: p.proofTex, leanPointer: p.leanKeyPointer, leanProofCacheSource: p.leanProofCacheSource,
    notationTable: p.notationTable, auditPromptFp, formalContext: proofAuditFormalContext(formalEnvs, p.obj_id, p.proofTex),
  });
  const proofAudit = async (p: JudgeInput) => {
    const key = auditKey(p);
    // Deterministic citation hint, merged at RETURN time (never persisted — the citable set is
    // not in the cache key, so a baked-in "cite X" would replay after X stops being a lemma).
    const detIssues = missingRealizedCitations(p.leanProofSource, p.proofTex, resultCitables, p.obj_id).map(
      (c) =>
        `[citation] the Lean route invokes ${c.decl.split(".").pop()}, which the paper states as ${c.objId} — ` +
        `cite \\cref{obj:${c.objId}} at that step instead of re-deriving it`,
    );
    // The hint joins the judge's issues only when the judge already found the proof unfaithful
    // (the repair render then adds the citation). When the judge affirms — freshly, from cache,
    // or by operator adjudication (flip `verdict`, keep `key`) — the hint is an advisory note:
    // one behaviour on every run, and P4's isolated-lemma gate remains the hard guard on
    // uncited lemmas.
    const withHint = (verdict: string, issues: string[]): { verdict: string; issues: string[] } => {
      if (detIssues.length === 0) return { verdict, issues };
      if (verdict !== "faithful") return { verdict, issues: [...issues, ...detIssues] };
      const note = `P2: ${p.obj_id} — ${detIssues.length} missing-citation hint(s) noted on a judge-faithful proof (advisory; uncited lemmas remain guarded by the P4 isolated-lemma gate)`;
      if (!io.state.notes.includes(note)) io.state.notes.push(note);
      return { verdict, issues };
    };
    const hit = cache[p.obj_id];
    const cacheable = p.leanProofCacheSource.length > 0;
    // A row stamped under the pre-closure key is the same verdict on a superset of this context.
    if (cacheable && hit && hit.key !== key && hit.key === legacyProofAuditCacheKey({
      proofTex: p.proofTex, leanPointer: p.leanPointer, leanProofCacheSource: p.leanProofCacheSource,
      notationTable: p.notationTable, auditPromptFp, targetStatement: targetStatementFor(p.obj_id), formalSource,
    })) {
      hit.key = key;
      await saveCache();
    }
    // A row stamped under the prompt as it read before deterministic context was added.
    if (cacheable && hit && hit.key !== key && LEGACY_PROOF_AUDIT_PROMPT_FPS.some((fp) => hit.key === proofAuditCacheKey({
      proofTex: p.proofTex, leanPointer: p.leanKeyPointer, leanProofCacheSource: p.leanProofCacheSource,
      notationTable: p.notationTable, auditPromptFp: fp, formalContext: proofAuditFormalContext(formalEnvs, p.obj_id, p.proofTex),
    }))) {
      hit.key = key;
      await saveCache();
    }
    // A cached UNFAITHFUL verdict without issues (a pre-change cache) cannot drive a repair —
    // treat it as a miss and re-judge.
    if (cacheable && hit?.key === key && (hit.verdict === "faithful" || (hit.issues?.length ?? 0) > 0)) {
      return withHint(hit.verdict, hit.issues ?? []);
    }
    // A reply with no verdict, or a non-faithful verdict with no issue to repair, is a mechanical
    // failure: retried once in place, then thrown — never a writer round, never cached.
    let v: { verdict?: string; issues?: string[] } | null = null;
    for (let attempt = 0; attempt < 2; attempt++) {
      v = (await ask(
      deps.runCodex({
        prompt: await presentationPrompt("proof_audit", {
          obj_id: p.obj_id,
          proof_tex: p.proofTex,
          lean_proof_source: `${p.leanPointer.replace("Read the file with your tools; do not guess its contents.",
            p.leanProofSource ? "The exact declaration is supplied below, and every run or library declaration it names is supplied under HELPER DECLARATIONS; no file read is needed for them." :
              "Read the declaration from this source file.")}\n\nLean excerpt:\n${p.leanProofSource || "(snippet unavailable — read the file via tools)"}\n\nOnly a helper ABSENT from the supplied list is read from source: rg -n -g '*.lean' for its declaration head under ${join(repoRoot, leanSubdir)} (Causalean at ${join(repoRoot, '..', 'Causalean')}), then read that declaration only. Never dump directory inventories, .olean/.ilean files, or the .lake tree.`,
          helper_declarations: p.helperDeclarations,
          notation_table: p.notationTable,
          // Check 6 audits claims the proof makes ABOUT other objects, which can only be judged by
          // opening those environments.
          paper_path: `${join(io.outDir, "formal_layer.json")}\n\n${proofAuditPaperContext(formalEnvs, p.obj_id, p.proofTex)}\n\nThe supplied excerpts are the current statements this proof proves and cites, taken from that JSON file (the "blocks" array; each block's "body" is the printed statement). When another statement is needed, select its block by exact obj_id from that file; do not read the whole file. The complete notation table is available at ${join(io.outDir, "outline.md")}.`,
        }),
        cwd: repoRoot,
        reasoningEffort: p.tier === "main" ? "high" : "medium",
        leanLsp: true,
      }),
      )) as { verdict?: string; issues?: string[] } | null;
      if (typeof v?.verdict === "string" && (v.verdict === "faithful" || (v.issues?.length ?? 0) > 0)) break;
      v = null;
    }
    if (v === null) throw new Error(`P2 proof judge returned no usable verdict for ${p.obj_id} twice — see agent_calls.log and re-run P2`);
    const out = { verdict: v.verdict!, issues: v.issues ?? [] };
    if (cacheable) {
      cache[p.obj_id] = { key, ...out };
      await saveCache();
    }
    return withHint(out.verdict, out.issues);
  };

  type Target = { obj_id: string; proofTex: string; leanPointer: string; leanKeyPointer: string; leanProofSource: string; leanProofCacheSource: string; isMain: boolean; helperDeclarations: string };
  const targets: Target[] = [];
  const runIndex = await buildModuleDeclIndex(repoRoot, leanSubdir);
  const readRunFile = leanSourceReader(repoRoot, leanSubdir);
  const libraryMemo = new Map<string, string | null>();
  for (const pt of proofTargets) {
    const proofTex = await readFile(proofFilePath(io.outDir, pt.obj_id), "utf8").catch(() => null);
    if (proofTex === null) continue; // statement-only / no rendered proof
    const resolved = await resolveLeanDeclaration(repoRoot, leanSubdir, { ...pt.lean, line: 0 });
    const resolvedPath = await resolvedLeanAbsolutePath(repoRoot, resolved.file);
    const leanPointer = `file: ${resolvedPath}\ndeclaration: ${resolved.decl}\nRead the file with your tools; do not guess its contents.`;
    // Keyed on the workspace-relative declaration, so a checkout path is not a cache input.
    const leanKeyPointer = `${resolved.file}:${resolved.decl}`;
    let leanProofSource = "";
    try {
      leanProofSource = extractFullDeclSource(await readFile(resolvedPath, "utf8"), resolved.decl, resolved.line);
    } catch {
      /* the judge still has lean-lsp to self-fetch */
    }
    targets.push({
      obj_id: pt.obj_id,
      proofTex: canonicalizeProofTitle(pt.obj_id, proofTex.trim()),
      leanPointer,
      leanKeyPointer,
      leanProofSource,
      leanProofCacheSource: leanProofSource,
      isMain: pt.isMain,
      helperDeclarations: leanProofSource
        ? await helperDeclarationsFor({ proofSource: leanProofSource, targetDecl: resolved.decl, runIndex, readRunFile, repoRoot, libraryMemo })
        : "(snippet unavailable — read helpers from source)",
    });
  }

  const refined = new Map<string, string>();
  const problems: ProofAuditProblem[] = [];
  // Each worker owns its proof file. Complete in-flight persistence before propagating errors.
  try {
    await mapLimit(targets, AUDIT_CONCURRENCY, async (pt) => {
      // Only the notation rows the judge can encounter in THIS candidate's material (the full table
      // averaged 32-42% of every proof_audit input). Computed per candidate: the filtered table is in
      // the verdict cache key, so a repaired proof must be keyed on ITS rows, or every re-run
      // re-judges it (and a stochastic flip re-repairs it).
      const judgeInput = (proofTex: string): JudgeInput => ({
        obj_id: pt.obj_id, proofTex, leanPointer: pt.leanPointer, leanKeyPointer: pt.leanKeyPointer, leanProofSource: pt.leanProofSource,
        leanProofCacheSource: pt.leanProofCacheSource, tier: pt.isMain ? "main" as const : "auxiliary" as const, helperDeclarations: pt.helperDeclarations,
        notationTable: notationForArtifact(notation, `${proofTex}\n${pt.leanProofSource}\n${targetStatementFor(pt.obj_id)}`),
      });
      const judge = (proofTex: string) => proofAudit(judgeInput(proofTex));
      const proofPath = proofFilePath(io.outDir, pt.obj_id);
      // Cross-reference targets are checked deterministically before any judge call: a dropped
      // kind prefix is repaired in place (the assembly repair, applied earlier); a target with no
      // environment is a defect the writer repairs once, without paying the judge to find it.
      const resolveRefs = (proofTex: string): { proof: string; dangling: string[] } => {
        const { tex, problems } = repairObjRefs(proofTex, new Set([...layerIds, pt.obj_id])); // the title cites the target itself
        return {
          proof: tex === proofTex ? proofTex : canonicalizeProofTitle(pt.obj_id, tex),
          dangling: problems.map((q) => `[rendering] ${q.detail}`),
        };
      };
      let { proof, dangling } = resolveRefs(pt.proofTex);
      if (proof !== pt.proofTex) await writeTextAtomic(proofPath, proof + "\n");
      const danglingVerdict = (issues: string[]) => ({ verdict: "unfaithful", issues });
      let verdict: { verdict: string; issues: string[] } = dangling.length > 0 ? danglingVerdict(dangling) : await judge(proof);
      let rounds = 0;
      // Bounded by MAX_ROUNDS (one more when the first defect was a dangling reference found
      // without a judge call, so a proof keeps its judged repair budget): retain earlier findings
      // so a later repair cannot forget a correction merely because the current judge reports a
      // different issue.
      const maxRounds = MAX_ROUNDS + (dangling.length > 0 ? 1 : 0);
      const previousIssues = new Set<string>();
      // A terminal failed attempt stays stopped on unchanged re-entry. The caller supplies
      // every renderer input; changed proof, diagnosis or context releases this receipt.
      const stoppedKey = () => {
        const renderContext = repairContextKeys.get(pt.obj_id);
        return renderContext === undefined || !pt.leanProofCacheSource ? undefined : hashEnvBody(JSON.stringify([
          renderContext, repairPromptFp, verdict.issues, auditKey(judgeInput(proof)),
        ]));
      };
      while (verdict.verdict !== "faithful" && rounds < maxRounds) {
        const key = stoppedKey();
        if (key !== undefined && cache[pt.obj_id]?.repairStoppedKey === key) break;
        rounds++;
        const next = await render(pt.obj_id, proof, verdict.issues,
          [...previousIssues].filter(issue => !verdict.issues.includes(issue)));
        for (const issue of verdict.issues) previousIssues.add(issue);
        const canon = next === null ? null : resolveRefs(canonicalizeProofTitle(pt.obj_id, next.trim()));
        if (canon === null || canon.proof === proof) break; // the renderer could not do better — halt with what stands
        proof = canon.proof;
        // Persist the candidate before judging: a failed judge or sibling cannot erase paid work.
        await writeTextAtomic(proofPath, proof + "\n");
        verdict = canon.dangling.length > 0 ? danglingVerdict(canon.dangling) : await judge(proof);
      }
      if (verdict.verdict !== "faithful") {
        const key = stoppedKey();
        if (key !== undefined) {
          // A proof halted before any judge call (unresolvable references) has no verdict row yet;
          // the receipt still needs a home so an unchanged re-entry does not re-pay the writer.
          cache[pt.obj_id] = { ...(cache[pt.obj_id] ?? { key: "", verdict: verdict.verdict, issues: verdict.issues }), repairStoppedKey: key };
          await saveCache();
        }
      }
      refined.set(pt.obj_id, proof);
      const faithful = verdict.verdict === "faithful";
      if (proof !== pt.proofTex) {
        await appendDriftReport(io.outDir, `${pt.obj_id} (proof)`, pt.proofTex, proof, rounds, faithful);
      }
      await appendFile(
        reviewsPath,
        JSON.stringify({ kind: "proof-refine", obj_id: pt.obj_id, rounds, faithful, issues: faithful ? [] : verdict.issues }) + "\n",
        "utf8",
      );
      if (!faithful) {
        const promotable = verdict.issues.some(isMissingStepIssue);
        problems.push({
          gate: "proof-audit",
          objId: pt.obj_id,
          detail: `${pt.obj_id}: ${verdict.issues.join("; ") || "unfaithful"}`,
          issues: verdict.issues,
          promotable,
        });
        io.state.notes.push(
          `P2: proof ${pt.obj_id} re-rendered against the judge's issues (${rounds} round(s)); STILL ${verdict.verdict} — ` +
            (promotable ? "a missing derivation remains (promotion-eligible)" : "rendering defects remain (adjudicate or delete the proof file for <id> under proofs/, colon spelled --, to re-render)"),
        );
      }
    });
  } finally {
    await saveCache();
  }
  return { refined, problems };
}
