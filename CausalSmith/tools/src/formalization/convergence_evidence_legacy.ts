// The TEXTUAL evidence scheme, kept for one purpose: a receipt issued under it is carried over to
// the fingerprint scheme (`receiptsAt` in `convergence_evidence.ts`) when its hash is still current
// on the tree as it stands — unchanged text elaborates to an unchanged statement, so the dual pass
// it records still holds. Nothing issues or audits a receipt under this scheme. Delete this module
// once no live or banked run holds such a receipt.
//
// Evidence here = reviewer rubric + the node's NL + its typed-core entry + its Lean anchor + the
// comment-stripped text of its own declaration (statement only for a theorem/lemma; whole
// declaration otherwise) + the same for every declaration reachable from it by identifier inside
// the run's Lean dir + the top-level commands (`variable`/`open`/`notation`/…) and anonymous
// instances of the files it sits in and imports — or of every file of the run, the scheme's earlier
// form — + the gated substrate hypotheses. Both forms are reported, so a receipt from either is
// recognised.

import { readFile, readdir } from "node:fs/promises";
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { isPaperTmpPath } from "../paths.js";
import type { Core } from "../discovery/core/schema.js";
import { stripLeanComments } from "../graph/extractor.js";
import { statementHash } from "../graph/hash.js";
import {
  LEAN_ANON_INSTANCE_HEADER_RE,
  LEAN_COMMAND_RE,
  LEAN_DECL_HEADER_RE,
  isLeanImportLine,
} from "../shared/lean_syntax.js";
import type { FormalizationGraph } from "../graph/types.js";
import { parseAllDecls, statementText } from "./crosswalk_parse.js";
import { commentInsensitiveLeanLayout } from "./crosswalk_semantics.js";
import { coreEntry, gatedDeps, type SymbolReviewRow } from "./convergence_evidence.js";

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
   *  anonymous `instance`s, hashed: the fallback of `commandsHashFor` for a target with no
   *  declaration to place it in a file. */
  commandsHash: string;
  /** Per file: the hash of its command text, and the run's files it imports. A notation or
   *  instance changes what a statement means only in the files that (transitively) import it. */
  commandHashByFile: Map<string, string>;
  importsByFile: Map<string, string[]>;
  /** Comment/docstring-insensitive hash of every run-local Lean file. Used for standalone
   * variable carriers, whose types may depend on macros/elaborators with no named declaration. */
  runCodeHash: string;
}

const STATEMENT_ONLY_KINDS = new Set(["theorem", "lemma"]);
const IDENT_RE = /[\p{L}_][\p{L}\p{N}_'.]*/gu;

/** The command lines of a comment-stripped file plus its anonymous-instance spans — the text whose
 *  meaning every declaration in the run implicitly depends on. */
function fileCommandText(stripped: string): string {
  const lines = stripped.split(/\r?\n/);
  const out: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    if (LEAN_COMMAND_RE.test(lines[i])) {
      out.push(lines[i]);
      continue;
    }
    if (!LEAN_ANON_INSTANCE_HEADER_RE.test(lines[i])) continue;
    let end = i + 1;
    while (end < lines.length && !LEAN_DECL_HEADER_RE.test(lines[end]) && !LEAN_COMMAND_RE.test(lines[end])) end++;
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

/** A command that defines custom syntax or an elaborator. These are reserved keywords (never
 *  identifiers), so a word match on comment-stripped code finds them wherever they occur. */
const SYNTAX_COMMAND_RE = /\b(?:syntax|macro|macro_rules|elab|elab_rules|declare_syntax_cat)\b/;
/** An elaborator or macro registered through an attribute (`@[…]` or `attribute […]`). */
const ELAB_ATTRIBUTE_RE = /(?:@|\battribute\s*)\[[^\n]*?\b(?:\w+_elab|macro|tactic)\b/;

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
  // Both the file keys and the bytes are normalized here because they are HASHED into
  // the F4 convergence receipts: `readdir` yields `\` on Windows and a checkout with
  // core.autocrlf yields CRLF, so without this a receipt recorded on Linux misses on
  // Windows (and vice versa) and every resumed run re-pays a full review.
  const files = existsSync(leanDir)
    ? (await readdir(leanDir, { recursive: true })).map(String).map((f) => f.replace(/\\/g, "/"))
        .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f)).sort()
    : [];
  for (const file of files) {
    const raw = (await readFile(`${leanDir}/${file}`, "utf8")).replace(/\r\n/g, "\n");
    rawSourceByFile.set(file, raw);
    const text = fileCommandText(stripLeanComments(raw));
    commandTextByFile.set(file, text);
    codeHashByFile.set(file, createHash("sha1").update(commentInsensitiveLeanLayout(raw)).digest("hex"));
    const followed = text.split(/\r?\n/).filter((ln) => !isLeanImportLine(ln)).join("\n");
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
  // Detection reads CODE only: prose such as a docstring's "macro-cube" is not a macro, and
  // matching it would make every docstring edit invalidate the variable-carrier receipts.
  const positionSensitive = [...rawSourceByFile.values()].map(stripLeanComments).some((code) =>
    // Any custom syntax/elaboration may observe source locations directly or through helpers;
    // exact hashing avoids an inevitably incomplete API-name allowlist.
    SYNTAX_COMMAND_RE.test(code) || ELAB_ATTRIBUTE_RE.test(code) ||
    /\b(?:getPos|getTailPos|getRange|getSourceInfo|getHeadInfo|getFileMap)\??\b/.test(code),
  );
  const runCodeHash = createHash("sha1").update(JSON.stringify(
    positionSensitive ? [...rawSourceByFile].sort() : [...codeHashByFile].sort(),
  )).digest("hex");
  // `import A.B.C` names a file of the run when the module path ends with that file's path.
  const fileOfModule = (module: string): string | null => {
    let best: string | null = null;
    for (const f of files) {
      const suffix = f.slice(0, -".lean".length).replace(/\//g, ".");
      if ((module === suffix || module.endsWith(`.${suffix}`)) && (best === null || f.length > best.length)) best = f;
    }
    return best;
  };
  const commandHashByFile = new Map([...commandTextByFile].map(([file, text]) => [file, statementHash(text)] as const));
  // Imports are read from the whole file with comments removed, not from its command lines: an
  // import may put the module name on the line after the keyword.
  const importsByFile = new Map([...rawSourceByFile].map(([file, raw]) => [
    file,
    [...new Set([...stripLeanComments(raw).matchAll(/(?:^|\s)import\s+(?:all\s+)?((?:«[^»\n]*»|[^\s«»])+)/gu)]
      .map((m) => fileOfModule(m[1].replace(/[«»]/g, "")))
      .filter((f): f is string => f !== null && f !== file))].sort(),
  ] as const));
  return { byShort, commandsHash, commandHashByFile, importsByFile, runCodeHash };
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

/**
 * The command evidence of a target whose declarations sit in `files`: the command text of those
 * files and of every run file they import, transitively — the only places a notation, an `open`
 * or an instance that changes the target's meaning can live. A change in a file none of them
 * imports (a new helper, an import added elsewhere) leaves it untouched. With no file to start
 * from, every file counts.
 */
function commandsHashFor(index: LeanEvidenceIndex, files: Iterable<string>): string {
  const seen = new Set<string>();
  const stack = [...new Set(files)].filter((f) => index.commandHashByFile.has(f));
  if (stack.length === 0) return index.commandsHash;
  while (stack.length > 0) {
    const f = stack.pop()!;
    if (seen.has(f)) continue;
    seen.add(f);
    for (const dep of index.importsByFile.get(f) ?? []) if (!seen.has(dep)) stack.push(dep);
  }
  return statementHash(JSON.stringify([...seen].sort().map((f) => [f, index.commandHashByFile.get(f)])));
}

function declRows(decls: DeclEvidence[]): [string, string, string, string][] {
  return decls.map((d) => [d.file, d.kind, d.name, d.hash] as [string, string, string, string]).sort();
}

// ---------------------------------------------------------------------------
// The two hashes a legacy receipt may carry
// ---------------------------------------------------------------------------

/** A node target's textual evidence: with the command text of the files it imports, and with
 *  that of every file of the run. */
export function legacyNodeEvidence(args: {
  graph: FormalizationGraph;
  index: LeanEvidenceIndex;
  core: Core | null;
  rubricHash: string;
  nodeId: string;
}): [string, string] {
  const n = args.graph.nodes.find((x) => x.id === args.nodeId);
  if (!n) throw new Error(`convergence evidence: node ${JSON.stringify(args.nodeId)} is not in the graph`);
  const self = n.lean.decl_name ? resolveAnchor(args.index, n.lean.decl_name, n.lean.file) : [];
  const closure = dependencyClosure(args.index, self);
  const at = (commands: string): string => statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: n.id,
    kind: n.kind,
    provenance: n.provenance,
    nl: n.nl.statement.trim(),
    core: coreEntry(args.core, n.id),
    lean: n.lean,
    self: declRows(self),
    closure: declRows(closure),
    commands,
    gated: gatedDeps(args.graph, n.id),
  }));
  return [at(commandsHashFor(args.index, [...self, ...closure].map((d) => d.file))), at(args.index.commandsHash)];
}

/** A tagged symbol cluster's textual evidence, in the same two forms. */
export function legacySymbolEvidence(args: {
  index: LeanEvidenceIndex;
  rubricHash: string;
  row: SymbolReviewRow;
}): [string, string] {
  const namedMembers = args.row.members.flatMap((m) => resolveAnchor(args.index, m.decl, m.file));
  const variableDeps = args.row.members.some((m) => m.declKind === "variable" && m.codeAnchor)
    ? [...new Set([...args.index.byShort.values()].flat())]
    : [];
  const members = [...new Set([...namedMembers, ...variableDeps])];
  const closure = dependencyClosure(args.index, members);
  const at = (commands: string): string => statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: args.row.id,
    row: args.row.evidenceRow,
    members: declRows(members),
    closure: declRows(closure),
    commands,
    runCode: args.row.members.some((m) => m.declKind === "variable") ? args.index.runCodeHash : null,
  }));
  return [at(commandsHashFor(args.index, [...members, ...closure].map((d) => d.file))), at(args.index.commandsHash)];
}

/**
 * The textual hashes of every governed target, computed on the tree as it stands: what a receipt
 * issued under this scheme would carry if nothing it bound has changed since.
 */
export async function legacyEvidence(args: {
  graph: FormalizationGraph;
  leanDir: string;
  core: Core | null;
  rubricHash: string;
  nodeIds: readonly string[];
  rows: readonly SymbolReviewRow[];
}): Promise<Map<string, readonly string[]>> {
  const index = await buildLeanEvidenceIndex(args.leanDir);
  const out = new Map<string, readonly string[]>();
  for (const nodeId of args.nodeIds) out.set(nodeId, legacyNodeEvidence({ graph: args.graph, index, core: args.core, rubricHash: args.rubricHash, nodeId }));
  for (const row of args.rows) out.set(row.id, legacySymbolEvidence({ index, rubricHash: args.rubricHash, row }));
  return out;
}
