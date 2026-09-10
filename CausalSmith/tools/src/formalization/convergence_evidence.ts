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
// anchor + the comment-stripped Lean text of its own declaration (statement only for a
// theorem/lemma — the proof does not change what the statement means; whole declaration for a
// def/structure/instance — the body IS the meaning) + the same for every declaration reachable
// from it by identifier reference inside the run's Lean dir (transitive; agent-introduced and
// untagged helpers included — the graph's `statement-uses` edges deliberately stop at tagged
// nodes, which is exactly the blind spot a cache must not inherit) + each touched file's
// top-level commands (`variable`/`open`/`notation`… change a statement's meaning without
// touching its text — so their identifiers are also followed into the closure, and anonymous
// `instance`s, which the declaration scanner cannot name, are hashed with them) + the gated
// substrate hypotheses shown to the reviewer. The rubric is the prompt file AND the reviewer's own
// source (`proof_reviewer.ts` embeds framing text the model reads), so a reviewer edit re-opens
// every receipt — the cost of a full round, which is what every round cost before receipts.
//
// Not cached here: undelivered (delivery-role) targets and `cited` gates — they already carry
// their own hash-bound per-peer receipts in state.json (`delivery_audit.ts`) and are re-reviewed
// every round; and symbol clusters with no `@realizes` member (the tag-reroute machinery owns them).

import { readFile, readdir } from "node:fs/promises";
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import { isPaperTmpPath } from "../paths.js";
import type { Core } from "../discovery/core/schema.js";
import { stripLeanComments } from "../graph/extractor.js";
import { statementHash } from "../graph/hash.js";
import { convergenceTargets } from "../graph/review_scope.js";
import {
  CONVERGENCE_PEERS,
  isUndeliveredNode,
  type ConvergenceLedger,
  type ConvergenceReceipt,
  type FormalizationGraph,
  type GraphNode,
} from "../graph/types.js";
import { parseAllDecls, statementText } from "./crosswalk_parse.js";
import { buildSymbolClusters, commentInsensitiveLeanLayout, type SymbolClusterMember } from "./crosswalk_semantics.js";
import { symbolInScope, verdictClass } from "./reviewer_verdicts.js";

// ---------------------------------------------------------------------------
// Lean evidence index
// ---------------------------------------------------------------------------

interface DeclEvidence {
  name: string;
  short: string;
  kind: string;
  file: string;
  /** sha1 of the comment-stripped, whitespace-normalized evidence text. */
  hash: string;
  /** Identifier tokens of the evidence text (resolved lazily against `byShort`). */
  refs: string[];
}

export interface LeanEvidenceIndex {
  /** Last name segment → every declaration in the tree carrying it (namespaces are not tracked
   *  by the whole-tree scanner, so resolution is deliberately over-inclusive: a stale receipt is
   *  the safe error). */
  byShort: Map<string, DeclEvidence[]>;
  /** Every file's top-level non-declaration commands (`variable`/`open`/`notation`/…) and
   *  anonymous `instance`s, hashed. Global: a notation or instance in ANY file of the run can
   *  change what a statement elsewhere means, so every evidence hash carries all of them. */
  commandsHash: string;
  /** Comment/docstring-insensitive hash of every run-local Lean file. Used for standalone
   * variable carriers, whose types may depend on macros/elaborators with no named declaration. */
  runCodeHash: string;
}

const STATEMENT_ONLY_KINDS = new Set(["theorem", "lemma"]);
const IDENT_RE = /[\p{L}_][\p{L}\p{N}_'.]*/gu;
const COMMAND_RE =
  /^\s*(?:variable|open|universe|set_option|notation|infix[lr]?|prefix|postfix|local|scoped|attribute|namespace|section|end|omit|include|macro|macro_rules|syntax|elab|export|import|noncomputable\s+section)\b/;
/** An `instance` header with NO name: invisible to `DECL_HEADER_SCAN_RE`, which requires one. */
const ANON_INSTANCE_RE =
  /^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+|partial\s+|unsafe\s+|nonrec\s+)*instance\s*(?:\{|\[|\(|:)/;
const ANY_HEADER_RE =
  /^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+|partial\s+|unsafe\s+|nonrec\s+)*(?:def|abbrev|structure|theorem|lemma|instance|class|inductive|opaque|axiom|constant)\b/;

/** The command lines of a comment-stripped file plus its anonymous-instance spans — the text whose
 *  meaning every declaration in the run implicitly depends on. */
function fileCommandText(stripped: string): string {
  const lines = stripped.split(/\r?\n/);
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    if (COMMAND_RE.test(lines[i])) {
      out.push(lines[i]);
      continue;
    }
    if (!ANON_INSTANCE_RE.test(lines[i])) continue;
    let end = i + 1;
    while (end < lines.length && !ANY_HEADER_RE.test(lines[end]) && !COMMAND_RE.test(lines[end])) end++;
    out.push(lines.slice(i, end).join("\n"));
    i = end - 1;
  }
  return out.join("\n");
}

function lastSegment(ident: string): string {
  const parts = ident.split(".").filter(Boolean);
  return parts[parts.length - 1] ?? "";
}

/** Drop trailing blank / attribute-only lines: `parseAllDecls` spans run to the NEXT header, so
 *  the next declaration's `@[…]` line (and, before comment stripping, its docstring and `@node`
 *  tag) sits at the tail of this one's text. Comments are already stripped by the caller. */
function trimTrailingNonCode(text: string): string {
  const lines = text.split("\n");
  while (lines.length > 0) {
    const last = lines[lines.length - 1];
    if (last.trim() === "" || /^\s*@\[[^\]]*\]\s*$/.test(last)) lines.pop();
    else break;
  }
  return lines.join("\n");
}

/** Parse the run's Lean dir once into hash + reference form. */
export async function buildLeanEvidenceIndex(leanDir: string): Promise<LeanEvidenceIndex> {
  const byShort = new Map<string, DeclEvidence[]>();
  const decls = await parseAllDecls(leanDir);
  // Command text per file, and the identifiers it names: a section `variable (M : ModelClass)` or a
  // `notation "ATE" => ateNaive` binds names a statement uses WITHOUT spelling them, so every
  // declaration in that file follows those names into its closure.
  // Enumerate EVERY file, not just those with a named declaration: a `Notation.lean` holding only
  // notation/instances would otherwise be invisible. Cross-file notation and instances are global, so
  // every declaration follows every file's command identifiers (over-inclusive; `import` lines are
  // hashed but not followed — their segments name modules, not run declarations).
  const commandTextByFile = new Map<string, string>();
  const codeHashByFile = new Map<string, string>();
  const rawSourceByFile = new Map<string, string>();
  const commandRefs = new Set<string>();
  const files = existsSync(leanDir)
    ? (await readdir(leanDir, { recursive: true })).map(String).filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f)).sort()
    : [];
  for (const file of files) {
    const raw = await readFile(`${leanDir}/${file}`, "utf8");
    rawSourceByFile.set(file, raw);
    const text = fileCommandText(stripLeanComments(raw));
    commandTextByFile.set(file, text);
    codeHashByFile.set(file, createHash("sha1").update(commentInsensitiveLeanLayout(raw)).digest("hex"));
    const followed = text.split(/\r?\n/).filter((ln) => !/^\s*import\b/.test(ln)).join("\n");
    for (const id of followed.match(IDENT_RE) ?? []) commandRefs.add(lastSegment(id));
  }
  for (const d of decls) {
    const stripped = trimTrailingNonCode(stripLeanComments(d.text));
    const evidenceText = STATEMENT_ONLY_KINDS.has(d.kind) ? statementText(stripped) : stripped;
    const short = lastSegment(d.name);
    const ownRefs = [...new Set(evidenceText.match(IDENT_RE) ?? [])].map(lastSegment);
    const entry: DeclEvidence = {
      name: d.name,
      short,
      kind: d.kind,
      file: d.file,
      hash: statementHash(evidenceText),
      refs: [...new Set([...ownRefs, ...commandRefs])].filter((s) => s && s !== short),
    };
    if (!byShort.has(short)) byShort.set(short, []);
    byShort.get(short)!.push(entry);
  }
  const commandsHash = statementHash(
    JSON.stringify([...commandTextByFile].sort().map(([file, text]) => [file, statementHash(text)])),
  );
  // A macro/elaborator that observes syntax positions makes even comments and blank lines
  // semantic. Fail conservatively to an exact whole-run hash when those APIs occur anywhere.
  const positionSensitive = [...rawSourceByFile.values()].some((raw) =>
    // Any custom syntax/elaboration may observe source locations directly or through helpers;
    // exact hashing avoids an inevitably incomplete API-name allowlist.
    /\b(?:syntax|macro|macro_rules|elab)\b/.test(raw) ||
    /\b(?:getPos|getTailPos|getRange|getSourceInfo|getHeadInfo|getFileMap)\??\b/.test(raw),
  );
  const runCodeHash = createHash("sha1").update(JSON.stringify(
    positionSensitive ? [...rawSourceByFile].sort() : [...codeHashByFile].sort(),
  )).digest("hex");
  return { byShort, commandsHash, runCodeHash };
}

/** Resolve a graph node's / cluster member's Lean anchor to index entries. Exact declared name
 *  first (or a namespace-qualified anchor ending in the declared name), then the same file's
 *  short-name matches; an anchor with no file keeps every short-name match. */
function resolveAnchor(index: LeanEvidenceIndex, declName: string, file: string | null): DeclEvidence[] {
  const candidates = index.byShort.get(lastSegment(declName)) ?? [];
  const exact = candidates.filter(
    (c) => (c.name === declName || declName.endsWith(`.${c.name}`) || c.name.endsWith(`.${declName}`)) && (!file || c.file === file),
  );
  if (exact.length > 0) return exact;
  return file ? candidates.filter((c) => c.file === file) : candidates;
}

/** Transitive identifier closure inside the run's Lean dir, starting from `roots` (excluded). */
function dependencyClosure(index: LeanEvidenceIndex, roots: DeclEvidence[]): DeclEvidence[] {
  const seen = new Set<DeclEvidence>(roots);
  const out: DeclEvidence[] = [];
  const stack = [...roots];
  while (stack.length > 0) {
    const cur = stack.pop()!;
    for (const ref of cur.refs) {
      for (const dep of index.byShort.get(ref) ?? []) {
        if (seen.has(dep)) continue;
        seen.add(dep);
        out.push(dep);
        stack.push(dep);
      }
    }
  }
  return out;
}

function declRows(decls: DeclEvidence[]): [string, string, string, string][] {
  return decls.map((d) => [d.file, d.kind, d.name, d.hash] as [string, string, string, string]).sort();
}


// ---------------------------------------------------------------------------
// Evidence hashes
// ---------------------------------------------------------------------------

/** The reviewer rubric a receipt was issued under: the prompt file PLUS the reviewer's own source,
 *  which embeds framing the model reads (target blocks, gated-exemption text, symbol header). Either
 *  changing re-opens every verdict. Fails closed if the reviewer source cannot be found. */
export async function reviewerRubricHash(promptText: string): Promise<string> {
  const here = fileURLToPath(new URL(".", import.meta.url));
  let reviewerSource: string | null = null;
  for (const name of ["proof_reviewer.ts", "proof_reviewer.js"]) {
    try {
      reviewerSource = await readFile(`${here}${name}`, "utf8");
      break;
    } catch {
      /* try the next candidate */
    }
  }
  if (reviewerSource === null) throw new Error(`convergence rubric: reviewer source not found next to ${here}`);
  return statementHash(JSON.stringify([promptText, reviewerSource]));
}

function coreEntry(core: Core | null, nodeId: string): unknown {
  if (!core) return null;
  return (
    core.statements.find((s) => s.id === nodeId) ??
    core.definitions.find((d) => d.id === nodeId) ??
    core.assumptions.find((a) => a.id === nodeId) ??
    null
  );
}

/** The registered `gated` substrate hypotheses the reviewer is told to exempt for `nodeId`. */
function gatedDeps(graph: FormalizationGraph, nodeId: string): [string, string | null, string][] {
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

export function nodeConvergenceEvidence(args: {
  graph: FormalizationGraph;
  index: LeanEvidenceIndex;
  core: Core | null;
  rubricHash: string;
  nodeId: string;
}): string {
  const n = args.graph.nodes.find((x) => x.id === args.nodeId);
  if (!n) throw new Error(`convergence evidence: node ${JSON.stringify(args.nodeId)} is not in the graph`);
  const self = n.lean.decl_name ? resolveAnchor(args.index, n.lean.decl_name, n.lean.file) : [];
  const closure = dependencyClosure(args.index, self);
  return statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: n.id,
    kind: n.kind,
    provenance: n.provenance,
    nl: n.nl.statement.trim(),
    core: coreEntry(args.core, n.id),
    lean: n.lean,
    self: declRows(self),
    closure: declRows(closure),
    commands: args.index.commandsHash,
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
    return {
      id: `sym:${c.symbol}`,
      row,
      hash: statementHash(evidenceRow),
      evidenceRow,
      empty: !c.members.length,
      members: c.members,
    };
  });
}

export function symbolConvergenceEvidence(args: {
  index: LeanEvidenceIndex;
  rubricHash: string;
  row: SymbolReviewRow;
}): string {
  const namedMembers = args.row.members.flatMap((m) => resolveAnchor(args.index, m.decl, m.file));
  // Standalone variable carriers have no declaration anchor of their own. Bind them to every
  // declaration in the run: resolving only identifier tokens misses escaped names (`«Carrier x»`)
  // and macro-expanded dependencies. This is deliberately over-inclusive (a safe stale receipt),
  // while comments/docstrings remain excluded by the declaration evidence index.
  const variableDeps = args.row.members.some((m) => m.declKind === "variable" && m.codeAnchor)
    ? [...new Set([...args.index.byShort.values()].flat())]
    : [];
  const members = [...new Set([...namedMembers, ...variableDeps])];
  const closure = dependencyClosure(args.index, members);
  return statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: args.row.id,
    row: args.row.evidenceRow,
    members: declRows(members),
    closure: declRows(closure),
    commands: args.index.commandsHash,
    runCode: args.row.members.some((m) => m.declKind === "variable") ? args.index.runCodeHash : null,
  }));
}

/** The delta-tier pass predicate for a stored symbol verdict (`untagged` clears the delta gate's
 *  "is there work?" check but is NOT a faithfulness pass). */
export const symbolVerdictPasses = (v: string): boolean => verdictClass(v) === "pass" && !/untagged/i.test(v);

// ---------------------------------------------------------------------------
// Receipts
// ---------------------------------------------------------------------------

/** True iff BOTH peers hold a `matched` receipt for `id` at exactly `evidenceHash`. */
export function dualClearedAt(ledger: ConvergenceLedger | undefined, id: string, evidenceHash: string): boolean {
  const entry = ledger?.[id];
  if (!entry) return false;
  return CONVERGENCE_PEERS.every((peer) => {
    const r: ConvergenceReceipt | undefined = entry[peer];
    return r !== undefined && r.verdict === "matched" && r.evidence_hash === evidenceHash;
  });
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
 */
export async function auditConvergenceReview(args: {
  graph: FormalizationGraph;
  leanDir: string;
  core: Core;
  promptFile: string;
}): Promise<ConvergenceAuditFinding[]> {
  const findings: ConvergenceAuditFinding[] = [];
  const nodeTargets = ledgerNodeTargets(args.graph);
  const rows = await buildSymbolReviewRows(args.leanDir, args.core.symbols ?? []);
  const taggedRows = rows.filter((row) => !row.empty);
  if (nodeTargets.length === 0 && taggedRows.length === 0) return findings;
  let promptText: string;
  try {
    promptText = await readFile(args.promptFile, "utf8");
  } catch (err) {
    // No rubric ⇒ no receipt can be verified against it. Fail closed on every governed target.
    const why = `reviewer rubric unreadable (${args.promptFile}): ${err instanceof Error ? err.message : String(err)}`;
    return [...nodeTargets, ...taggedRows.map((row) => row.id)].map((id) => ({ code: "convergence-review" as const, node_id: id, message: why }));
  }
  const rubricHash = await reviewerRubricHash(promptText);
  const index = await buildLeanEvidenceIndex(args.leanDir);
  const ledger = args.graph.convergenceReview;
  const byId = new Map(args.graph.nodes.map((n) => [n.id, n] as const));
  for (const id of nodeTargets) {
    const n = byId.get(id) as GraphNode;
    if (isUndeliveredNode(n)) continue;
    if (n.review.status !== "matched") {
      findings.push({ code: "convergence-review", node_id: id, message: `review status is ${n.review.status}, not matched` });
      continue;
    }
    const evidence = nodeConvergenceEvidence({ graph: args.graph, index, core: args.core, rubricHash, nodeId: id });
    if (!dualClearedAt(ledger, id, evidence)) {
      findings.push({ code: "convergence-review", node_id: id, message: describeMissing(ledger, id, evidence) });
    }
  }
  for (const row of taggedRows) {
    const prior = args.graph.symbolReview?.[row.id];
    if (!prior || prior.hash !== row.hash || !symbolVerdictPasses(prior.verdict)) {
      findings.push({ code: "convergence-review", node_id: row.id, message: `symbol cluster is not delta-cleared at its current realization` });
      continue;
    }
    const evidence = symbolConvergenceEvidence({ index, rubricHash, row });
    if (!dualClearedAt(ledger, row.id, evidence)) {
      findings.push({ code: "convergence-review", node_id: row.id, message: describeMissing(ledger, row.id, evidence) });
    }
  }
  return findings;
}

function describeMissing(ledger: ConvergenceLedger | undefined, id: string, evidence: string): string {
  const entry = ledger?.[id];
  const parts = CONVERGENCE_PEERS.map((peer) => {
    const r = entry?.[peer];
    if (!r) return `${peer}: no F4 receipt`;
    if (r.verdict !== "matched") return `${peer}: ${r.verdict}${r.note ? ` (${r.note})` : ""}`;
    if (r.evidence_hash !== evidence) return `${peer}: receipt is stale for the current statement/dependency/rubric evidence`;
    return `${peer}: ok`;
  });
  return `${parts.join("; ")} — re-run F4 (\`--resume --from-stage F4\`)`;
}
