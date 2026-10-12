// F4 convergence receipts: what a dual-model verdict certifies, and when a later F4 round may
// reuse it instead of re-reviewing.
//
// Why: F4 used to re-review the FULL frozen surface with both peers on every entry — and an
// escalation-fix-resume cycle re-enters F4 several times per run, so each headline theorem was
// re-judged 5–10× at byte-identical text. Measured over five runs, a re-read of an unchanged,
// already dual-passed target flipped to a finding <2% of the time, while a SINGLE peer missed a
// third of all findings. So the safety lives in the second model, not in the repetition: keep the
// dual review, cache its result — but bind the cached verdict to everything that could change
// what the reviewer saw, and require BOTH peers at the same evidence before skipping.
//
// Evidence for a node target = reviewer rubric + the node's NL + its typed-core entry + its Lean
// anchor + the CLOSURE HASH of the declaration the anchor names (`statement_fingerprints.ts`: what
// Lean elaborated for it and for every declaration of Causalean, CausalSmith or a vendored package
// its statement reaches — agent-introduced and untagged helpers included, which the graph's
// `statement-uses` edges deliberately stop short of) + the build basis (toolchain, Mathlib) +
// the gated substrate hypotheses shown to the reviewer. Nothing of the source TEXT is hashed: an
// `open`, a notation, a `variable`, an instance or an option changes a receipt only through the
// term it makes Lean elaborate; a proof, a comment, a docstring (F5 writes them after F4), an
// import or a binder name never does. The rubric slot is the hand-bumped REVIEW_STANDARD token,
// NOT a hash of the prompt text or of the reviewer's source: a wording clarification or a refactor
// must not re-open every receipt. Bump it only when the review standard tightens.
//
// A target whose anchor names no fingerprinted declaration — the scan could not run, or Lean
// elaborated no such declaration — has NO evidence (null): it is reviewed and never current, and
// no receipt is written for it. A receipt issued under the textual scheme that preceded the
// fingerprints (`convergence_evidence_legacy.ts`) still clears its target while that scheme's hash
// is current on the tree as it stands; `receiptsAt` re-issues it at the fingerprint evidence.
//
// Not cached here: undelivered (delivery-role) targets and `cited` gates — they already carry
// their own hash-bound per-peer receipts in state.json (`delivery_audit.ts`) and are re-reviewed
// every round; and symbol clusters with no `@realizes` member (the tag-reroute machinery owns them).

import { readFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../discovery/core/schema.js";
import { statementHash } from "../graph/hash.js";
import { convergenceTargets } from "../graph/review_scope.js";
import {
  CONVERGENCE_PEERS,
  isUndeliveredNode,
  ConvergenceLedgerSchema,
  type ConvergenceLedger,
  type ConvergenceReceipt,
  type FormalizationGraph,
  type GraphNode,
} from "../graph/types.js";
import { buildSymbolClusters, type SymbolClusterMember } from "./crosswalk_semantics.js";
import { symbolInScope, verdictClass } from "./reviewer_verdicts.js";
import { closureHash, declsInFile, resolveDecls, type StatementFingerprints } from "./statement_fingerprints.js";
import { legacyEvidence } from "./convergence_evidence_legacy.js";

// ---------------------------------------------------------------------------
// Evidence hashes
// ---------------------------------------------------------------------------

/** The reviewer standard a convergence receipt is issued under — an opaque version token, hashed
 *  into every node/symbol evidence hash. It replaced a hash of the reviewer prompt text and the
 *  reviewer's own source, which re-opened every verdict on a wording tweak or a refactor.
 *  Initial value is the hash the receipts carried on 2026-09-12 so existing receipts stay valid;
 *  bump to any new literal only when the review standard tightens (a receipt issued under the old
 *  standard would be wrong); prompt wording and code changes never bump it. */
export const REVIEW_STANDARD = "16865e36da9271bbf0e9906def5868e43c1ec0d8";

export function coreEntry(core: Core | null, nodeId: string): unknown {
  if (!core) return null;
  return (
    core.statements.find((s) => s.id === nodeId) ??
    core.definitions.find((d) => d.id === nodeId) ??
    core.assumptions.find((a) => a.id === nodeId) ??
    null
  );
}

/** The registered `gated` substrate hypotheses the reviewer is told to exempt for `nodeId`. */
export function gatedDeps(graph: FormalizationGraph, nodeId: string): [string, string | null, string][] {
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  const out: [string, string | null, string][] = [];
  for (const e of graph.edges) {
    if (e.from !== nodeId || (e.kind !== "proof-uses" && e.kind !== "statement-uses")) continue;
    const g = byId.get(e.to);
    if (!g || g.kind !== "gate" || g.gate?.gate_class !== "gated") continue;
    out.push([g.id, g.lean.decl_name, g.nl.statement.trim()]);
  }
  return out.sort();
}

/** The rows a target's evidence hashes: each declaration under its name with its closure hash,
 *  in name order. */
const fingerprintRows = (fp: StatementFingerprints, names: readonly string[]): [string, string][] =>
  [...new Set(names)].sort().map((n) => [n, closureHash(fp, n)]);

/** A node target's evidence hash; null when it has none (see the header). */
export function nodeConvergenceEvidence(args: {
  graph: FormalizationGraph;
  fingerprints: StatementFingerprints | null;
  core: Core | null;
  rubricHash: string;
  nodeId: string;
}): string | null {
  const n = args.graph.nodes.find((x) => x.id === args.nodeId);
  if (!n) throw new Error(`convergence evidence: node ${JSON.stringify(args.nodeId)} is not in the graph`);
  const fp = args.fingerprints;
  if (!fp) return null;
  const decls = n.lean.decl_name ? resolveDecls(fp, n.lean.decl_name, n.lean.file) : [];
  if (n.lean.decl_name && decls.length === 0) return null;
  return statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: n.id,
    kind: n.kind,
    provenance: n.provenance,
    nl: n.nl.statement.trim(),
    core: coreEntry(args.core, n.id),
    lean: n.lean,
    decls: fingerprintRows(fp, decls),
    basis: fp.basis,
    gated: gatedDeps(args.graph, n.id),
  }));
}

// ---------------------------------------------------------------------------
// Symbol-cluster rows (the `sym:<symbol>` review surface)
// ---------------------------------------------------------------------------

export interface SymbolReviewRow {
  id: string;
  /** The prompt row shown to the reviewer. */
  row: string;
  /** Hash of `evidenceRow` — the delta-mode `symbolReview` staleness key. */
  hash: string;
  /** The members' statement fingerprints with `evidenceRow`, when the tree's fingerprints know
   *  every member: compared instead of `hash` by a delta pass that has the tree's fingerprints
   *  too, so a member's body change moves the row where the member list alone cannot see it. */
  fingerprintHash?: string;
  /** Stable semantic row used by convergence receipts. The human-facing row includes optional
   *  hints and source line labels, both of which F5 documentation may change without changing
   *  the realization carrier. */
  evidenceRow: string;
  empty: boolean;
  members: SymbolClusterMember[];
}

/** Build the complete synthetic symbol-review surface once (reviewer + banking audit share it). */
export async function buildSymbolReviewRows(
  leanDir: string,
  symbols: { name?: string; space?: string; type?: string; role?: string }[],
  /** The statement fingerprints of the built tree: each row then also carries `fingerprintHash`. */
  fingerprints: StatementFingerprints | null = null,
): Promise<SymbolReviewRow[]> {
  const syms = symbols
    .filter(symbolInScope)
    .map((s) => ({ name: s.name as string, space: (s.space || s.type) as string }));
  if (!syms.length) return [];
  const clusters = await buildSymbolClusters(leanDir, syms);
  return clusters.map((c) => {
    const head = `- sym:${c.symbol} : ${c.space ?? "(no space)"}`;
    const row = !c.members.length
      ? `${head}\n    realized_by: (UNTAGGED — no \`@realizes ${c.symbol}\` tag found. There is NO member to verify against, so the ONLY valid verdict is \`untagged\`: NEVER \`matched\`/\`equivalent\` (that is "verified against nothing", even for a computed quantity — def-by-construction needs a TAGGED def member) and NEVER \`drift\` (a missing tag is a tagging gap, not a mismatch). In your \`note\`, you MUST NAME the specific Lean decl that realizes this symbol — SEARCH the Lean dir (Grep/lean-lsp) for the \`def\` that computes it, the structure field that carries it, or the theorem/def binder/parameter that introduces it, and state the file + decl name. The scaffolder tags EXACTLY what you name, so a vague note ("tag the decls realizing X") is unactionable.)`
      : `${head}\n    realized_by (judge the CONJUNCTION of these):\n${c.members
          .map((m) => `      • ${m.decl} (${m.declKind}) in ${m.file}${m.hint ? `  — ${m.hint}` : ""}`)
          .join("\n")}`;
    const evidenceRow = JSON.stringify({
      symbol: c.symbol,
      space: c.space ?? null,
      members: c.members.map((m) => ({
        decl: m.declKind === "variable" ? "variable" : m.decl,
        declKind: m.declKind,
        file: m.file,
        codeAnchor: m.codeAnchor ?? null,
      })),
    });
    const fingerprinted = fingerprints && c.members.length ? memberFingerprints(fingerprints, c.members) : null;
    return {
      id: `sym:${c.symbol}`,
      row,
      hash: statementHash(evidenceRow),
      ...(fingerprinted ? { fingerprintHash: statementHash(JSON.stringify({ row: evidenceRow, decls: fingerprinted, basis: fingerprints!.basis })) } : {}),
      evidenceRow,
      empty: !c.members.length,
      members: c.members,
    };
  });
}

/** The fingerprint rows of a cluster's members; null when a member names no fingerprinted
 *  declaration. A standalone `variable` carrier is no declaration: it is read through every
 *  declaration of its file, whose statements are where its binder lands. */
function memberFingerprints(fp: StatementFingerprints, members: readonly SymbolClusterMember[]): [string, string][] | null {
  const decls: string[] = [];
  for (const m of members) {
    const found = m.declKind === "variable" ? declsInFile(fp, m.file) : resolveDecls(fp, m.decl, m.file);
    if (found.length === 0) return null;
    decls.push(...found);
  }
  return fingerprintRows(fp, decls);
}

/** A tagged symbol cluster's evidence hash; null when a member names no fingerprinted declaration.
 *  A standalone `variable` carrier is no declaration: it is read through every declaration of its
 *  file, whose statements are where its binder lands. */
export function symbolConvergenceEvidence(args: {
  fingerprints: StatementFingerprints | null;
  rubricHash: string;
  row: SymbolReviewRow;
}): string | null {
  const fp = args.fingerprints;
  if (!fp) return null;
  const decls = memberFingerprints(fp, args.row.members);
  if (!decls) return null;
  return statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: args.row.id,
    row: args.row.evidenceRow,
    decls,
    basis: fp.basis,
  }));
}

/** The delta-tier pass predicate for a stored symbol verdict (`untagged` clears the delta gate's
 *  "is there work?" check but is NOT a faithfulness pass). */
export const symbolVerdictPasses = (v: string): boolean => verdictClass(v) === "pass" && !/untagged/i.test(v);

// ---------------------------------------------------------------------------
// Receipts
// ---------------------------------------------------------------------------

/** Where a convergence pass keeps the dual receipts it has issued so far (`runs/<slug>/`): a pass
 *  that dies part-way (a worker timeout, a kill) leaves them for the next pass to reuse. */
export function partialReceiptsPath(runDir: string): string {
  return path.join(runDir, "convergence_partial.json");
}

/** The entries of `ledger` both peers passed (`matched`, on the same evidence): the only ones a
 *  later pass may reuse. Pure. */
export function dualMatchedReceipts(ledger: ConvergenceLedger): ConvergenceLedger {
  return Object.fromEntries(Object.entries(ledger).filter(([, r]) =>
    r.codex?.verdict === "matched" && r.claude?.verdict === "matched" && r.codex.evidence_hash === r.claude.evidence_hash));
}

/** The dual receipts an unfinished pass left behind; `{}` when there is no readable file. Each is
 *  bound to its evidence hash, so one issued on an older statement is simply never current. */
export async function loadPartialReceipts(runDir: string): Promise<ConvergenceLedger> {
  try {
    return dualMatchedReceipts(ConvergenceLedgerSchema.parse(JSON.parse(await readFile(partialReceiptsPath(runDir), "utf8"))));
  } catch {
    return {};
  }
}


/**
 * The dual receipts that clear `id` at `evidence`, or undefined. A pair issued at one of the
 * `legacy` hashes — the textual scheme's, computed on the tree as it stands — counts too: the text
 * it bound is unchanged, so the statement is, and the pair is returned re-issued at `evidence`.
 * Nothing clears a target with no evidence.
 */
export function receiptsAt(
  ledger: ConvergenceLedger | undefined,
  id: string,
  evidence: string | null,
  legacy: readonly string[] = [],
): ConvergenceLedger[string] | undefined {
  if (evidence === null) return undefined;
  if (dualClearedAt(ledger, id, evidence)) return ledger![id];
  if (!legacy.some((h) => dualClearedAt(ledger, id, h))) return undefined;
  const entry = ledger![id];
  return Object.fromEntries(CONVERGENCE_PEERS.map((peer) => [peer, { ...entry[peer]!, evidence_hash: evidence }])) as ConvergenceLedger[string];
}

/** True iff BOTH peers hold a `matched` receipt for `id` at exactly `evidenceHash`; never for a
 *  target with no evidence. */
export function dualClearedAt(ledger: ConvergenceLedger | undefined, id: string, evidenceHash: string | null): boolean {
  const entry = ledger?.[id];
  if (!entry || evidenceHash === null) return false;
  return CONVERGENCE_PEERS.every((peer) => {
    const r: ConvergenceReceipt | undefined = entry[peer];
    return r !== undefined && r.verdict === "matched" && r.evidence_hash === evidenceHash;
  });
}

/**
 * The textual-scheme hashes of every governed target (`legacyEvidence`), for `receiptsAt` —
 * computed only when the ledger holds a dual pass at some hash, since only such a receipt can be
 * carried over; otherwise every target maps to no hash.
 */
export async function legacyHashes(args: {
  ledger: ConvergenceLedger | undefined;
  graph: FormalizationGraph;
  leanDir: string;
  core: Core | null;
  rubricHash: string;
  nodeIds: readonly string[];
  rows: readonly SymbolReviewRow[];
}): Promise<(id: string) => readonly string[]> {
  const map = Object.keys(dualMatchedReceipts(args.ledger ?? {})).length > 0 ? await legacyEvidence(args) : new Map<string, readonly string[]>();
  return (id) => map.get(id) ?? [];
}

/** The F4 node targets this ledger governs: the full convergence surface minus the targets that
 *  carry their own state.json receipts (undelivered nodes, `cited` gates). */
export function ledgerNodeTargets(graph: FormalizationGraph): string[] {
  const t = convergenceTargets(graph);
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  const cited = (id: string): boolean => {
    const n = byId.get(id);
    return !!n && n.kind === "gate" && n.gate?.gate_class === "cited";
  };
  return [...t.statementTargets, ...t.definitionTargets, ...t.lemmaTargets, ...t.assumptionTargets].filter((id) => !cited(id));
}

export interface ConvergenceAuditFinding {
  code: "convergence-review";
  node_id?: string;
  message: string;
}

/**
 * Re-verify the F4 ledger against the CURRENT tree: every governed node target must be delta-
 * `matched` and dual-receipted at its current evidence, and every tagged symbol cluster must be
 * delta-passed at its current row and dual-receipted at its current evidence. Run at F5 and at
 * accepted banking, so a skipped F4 target is never banked on a receipt the tree has outgrown.
 * `fingerprints` takes those of the tree as built now (`takeStatementFingerprints`; called only
 * when there is a target to verify); without them no receipt can be verified, and every governed
 * target is a finding.
 */
export async function auditConvergenceReview(args: {
  graph: FormalizationGraph;
  leanDir: string;
  core: Core;
  promptFile: string;
  fingerprints: () => Promise<StatementFingerprints | null>;
}): Promise<ConvergenceAuditFinding[]> {
  const findings: ConvergenceAuditFinding[] = [];
  const nodeTargets = ledgerNodeTargets(args.graph);
  const rows = await buildSymbolReviewRows(args.leanDir, args.core.symbols ?? []);
  const taggedRows = rows.filter((row) => !row.empty);
  if (nodeTargets.length === 0 && taggedRows.length === 0) return findings;
  try {
    // A reviewer with no prompt cannot review: an unreadable prompt fails closed on every
    // governed target.
    await readFile(args.promptFile, "utf8");
  } catch (err) {
    const why = `reviewer rubric unreadable (${args.promptFile}): ${err instanceof Error ? err.message : String(err)}`;
    return [...nodeTargets, ...taggedRows.map((row) => row.id)].map((id) => ({ code: "convergence-review" as const, node_id: id, message: why }));
  }
  const rubricHash = REVIEW_STANDARD;
  const fingerprints = await args.fingerprints();
  const ledger = args.graph.convergenceReview;
  const legacy = await legacyHashes({ ledger, graph: args.graph, leanDir: args.leanDir, core: args.core, rubricHash, nodeIds: nodeTargets, rows: taggedRows });
  const byId = new Map(args.graph.nodes.map((n) => [n.id, n] as const));
  for (const id of nodeTargets) {
    const n = byId.get(id) as GraphNode;
    if (isUndeliveredNode(n)) continue;
    if (n.review.status !== "matched") {
      findings.push({ code: "convergence-review", node_id: id, message: `review status is ${n.review.status}, not matched` });
      continue;
    }
    const evidence = nodeConvergenceEvidence({ graph: args.graph, fingerprints, core: args.core, rubricHash, nodeId: id });
    if (!receiptsAt(ledger, id, evidence, legacy(id))) {
      findings.push({ code: "convergence-review", node_id: id, message: describeMissing(ledger, id, evidence, fingerprints, n.lean.decl_name) });
    }
  }
  for (const row of taggedRows) {
    const prior = args.graph.symbolReview?.[row.id];
    if (!prior || prior.hash !== row.hash || !symbolVerdictPasses(prior.verdict)) {
      findings.push({ code: "convergence-review", node_id: row.id, message: `symbol cluster is not delta-cleared at its current realization` });
      continue;
    }
    const evidence = symbolConvergenceEvidence({ fingerprints, rubricHash, row });
    if (!receiptsAt(ledger, row.id, evidence, legacy(row.id))) {
      findings.push({ code: "convergence-review", node_id: row.id, message: describeMissing(ledger, row.id, evidence, fingerprints, row.members.map((m) => m.decl).join(", ")) });
    }
  }
  return findings;
}

function describeMissing(ledger: ConvergenceLedger | undefined, id: string, evidence: string | null, fingerprints: StatementFingerprints | null, decls: string | null): string {
  const rerun = "re-run F4 (`--resume --from-stage F2.5`)";
  if (!fingerprints) return `no statement fingerprints for the built tree (statement_scan did not run; see the [f4] log line) — build the run's modules if a source changed after the last build, then ${rerun}`;
  if (evidence === null) return `Lean elaborated no declaration its anchor names (${decls ?? "no anchor"}): the receipt cannot be bound — repair the anchor, then ${rerun}`;
  const entry = ledger?.[id];
  const parts = CONVERGENCE_PEERS.map((peer) => {
    const r = entry?.[peer];
    if (!r) return `${peer}: no F4 receipt`;
    if (r.verdict !== "matched") return `${peer}: ${r.verdict}${r.note ? ` (${r.note})` : ""}`;
    if (r.evidence_hash !== evidence) return `${peer}: receipt is stale for the current statement/dependency/rubric evidence`;
    return `${peer}: ok`;
  });
  return `${parts.join("; ")} — ${rerun}`;
}
