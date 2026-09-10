/**
 * Build-time enrichment of a paper bundle's Lean drawer payload.
 *
 * The drawer used to show only what the pipeline explicitly attached to a
 * statement: the anchor declaration plus whatever "components" P4 mapped to
 * formulas in that statement's own prose. That set is not closed. Definition 9
 * of the discrete-ATE minimax paper shows `hybridEstimator`, whose body is
 * `max (-1) (min 1 (heavyContribution sample + lightContribution sample))` —
 * and neither contribution appeared anywhere in the drawer, so a reader could
 * not actually check the definition without opening the Lean sources.
 *
 * This module closes that gap at BUILD time. For each crosswalk entry it walks
 * the statement-level references of everything shown, transitively, and
 * classifies each declaration it reaches:
 *
 *   - `anchor`     — the entry's own declaration;
 *   - `env`        — a piece the pipeline already mapped into this statement;
 *   - `paper`      — a declaration the reader can check at ITS OWN paper block
 *                    (another numbered definition/lemma), so it is linked, not
 *                    inlined, and the walk stops there;
 *   - `lean_only`  — a helper with no paper block, inlined in full and recursed
 *                    through.
 *
 * Identifiers that are NOT paper declarations (Mathlib, Causalean) are ignored:
 * the client-side highlighter already links those out to the library explorer.
 *
 * It also produces a hypotheses/conclusions view of theorem-like statements,
 * reusing the library page's binder parser (`leanStatement.ts`) rather than
 * forking it. That parser is deliberately conservative and so is this: any
 * uncertainty omits `structured` entirely and the UI falls back to the raw
 * statement. A structured view is never allowed to silently drop content —
 * every emitted view is checked, token by token, against the original source.
 */

import { isCanonicalSourceDeclaration } from "../../../tools/src/presentation/lean_decl_name.js";
import { rowToken, segmentToken, type NlBlock, type NlDisplayLink } from "./nlLinks.js";
import {
  identifierTokens,
  normAwareDepths,
  scanPropDefinitionSignature,
  scanTheoremSignature,
  stripLeanComments,
} from "./leanStatement.js";
import {
  allHypRows,
  isDefinitionLike,
  isInductiveLike,
  isInstanceLike,
  isPropRecord,
  isRecordLike,
  structureDataRecordView,
  structureDefinitionView,
  structureInductiveView,
  structureInstanceView,
  markCitedHyps,
  structurePropRecordView,
  structureStatementView,
  type ConclusionCard,
  type HypRow,
  type StructuredView,
} from "./leanCards.js";

export { structurePropRecordView, structureStatementView, type ConclusionCard, type HypRow, type StructuredView };

/**
 * One declaration's source, held ONCE per paper in `Bundle.declSources` rather
 * than inlined into every drawer that reaches it. The same helper is pulled in
 * by dozens of statements — inlining it multiplied the payload roughly threefold.
 */
export interface DeclSource {
  file: string;
  line: number;
  /** Verbatim source: a theorem/lemma's docstring and signature through its
   *  goal (proof dropped — see `tableStatement`); any other kind's full text. */
  statement: string;
  /** Only for theorem/lemma-kind statements. */
  structured?: StructuredView;
  /** Verification status, straight from the module index and carried through
   *  as-is: `true` = proved only up to `sorry`, `false` = proved, ABSENT =
   *  unknown (an older or partial index that does not record it). The three
   *  states are kept distinct on purpose — reporting an unrecorded status as
   *  "proved" would present an unverified helper as clean. Never inferred from
   *  `statement`: a theorem's proof is trimmed away, so a `sorry` in it is
   *  invisible there. */
  usesSorry?: boolean;
}

export interface ComponentView {
  /** Short display name (the declaration's last dotted segment). */
  decl: string;
  /** Fully-qualified key into `declSources`. Absent only for a component the
   *  module index does not know, which then carries its text inline below. */
  key?: string;
  /**
   * How this declaration relates to the block.
   *
   * - `anchor`    — the entry's own declaration;
   * - `env`       — a formula in THIS statement's prose links to it (earned by
   *                 crosslink evidence, never assumed);
   * - `paper`     — stated at its own block; a chip pointing there;
   * - `cited`     — an assumed external result;
   * - `lean_only` — everything else the drawer shows: reached through the
   *                 reference closure, or attached to the statement without any
   *                 formula here linking it.
   */
  cls: "anchor" | "cited" | "env" | "paper" | "lean_only";
  /** 0 = anchor or an already-attached component; 1+ = pulled by the closure. */
  depth: number;
  /** `cls === "paper"`: the crosswalk obj_id whose block carries this declaration. */
  paperObjId?: string;
  /** `cls === "paper"`: that block's number, e.g. "Definition 7". */
  paperLabel?: string;
  /** Space-separated NL↔Lean crosslink ids landing on this piece. */
  xl?: string;
  /** The declaration is UPSTREAM (Causalean or Mathlib), harvested from the
   *  index's `extRefs`. It has no source in this bundle, so the card renders as
   *  a name plus a link out rather than an inlined statement. */
  external?: true;
  /** `external` only: the fully-qualified upstream name. The UI resolves it
   *  through `/library/names.json` — the same map the drawer's Lean highlighter
   *  already loads — to `${base}/library/${a}#${n}`. */
  fullName?: string;
  /** `external` only: the upstream module the reference came from. */
  module?: string;
  /** `external` only: an absolute doc URL, when the module is Mathlib-family
   *  (Mathlib/Std/Lean/Init/Batteries) and so has no page in this explorer. */
  docUrl?: string;
  // ---- inline fallbacks, populated ONLY when `key` is absent ----
  file?: string;
  line?: number;
  statement?: string;
  structured?: StructuredView;
}

export interface SnippetEnrichment {
  structured?: StructuredView;
  componentViews?: ComponentView[];
  /** Set when some helper this statement pulls in (an `env` or `lean_only`
   *  view) is itself proved only up to `sorry` — the statement is then not
   *  fully verified, however clean its own proof is. */
  closureHasSorry?: boolean;
  /** How many pulled-in helpers have NO recorded verification status. Not the
   *  same as clean: the index simply does not say, and the reader is told that
   *  rather than shown an unearned tick. */
  closureSorryUnknown?: number;
  /** How many further declarations the reference walk left unexplored when it
   *  hit the depth cap. Absent when the closure is complete. */
  closureTruncated?: number;
}

export interface EnrichmentResult {
  /** Per-crosswalk-entry drawer enrichment, keyed by obj_id. */
  snippets: Record<string, SnippetEnrichment>;
  /** Shared source table, keyed by fully-qualified declaration name. Holds
   *  exactly the declarations some `ComponentView.key` points at. */
  declSources: Record<string, DeclSource>;
  /** Artifact rows the enrichment could not act on — reported once per bundle
   *  by the loader, never fatal. */
  linkProblems: LinkProblem[];
}

/** An artifact assignment the structured tree does not account for. */
export interface LinkProblem {
  objId: string;
  reason: string;
}

/**
 * Envs whose crosswalk entries are web-only — surfaced in the Formal-layer
 * panel, deliberately NOT anchored in the paper body. A declaration owned only
 * by one of these has no block for the reader to jump to, so it can never be
 * classified `paper`. (Same list the bundle integrity gate exempts.)
 */
export const WEB_ONLY_ENVS = ["citedv", "auxiliary", "symbol"];

/**
 * How deep the reference closure is allowed to run from the seed set.
 *
 * Raised from 4 to 6: a definition's own NL text can state a quantity that sits
 * five or six references down (`dA`, displayed in Definition 9's prose, is at
 * depth 5), and a reader who is shown the formula but no Lean for it anywhere
 * is exactly the gap this module exists to close. `closureTruncated` still
 * reports whatever is left beyond the cap.
 */
const MAX_DEPTH = 6;

// ---------------------------------------------------------------------------
// input shapes (structural, so this module stays independent of bundles.ts)
// ---------------------------------------------------------------------------

export interface PaperLeanEntry {
  obj_id: string;
  env: string;
  paper_label: string;
  lean: { decl: string; decl_kind?: string } | null;
  status?: string;
}

export interface PaperLeanSnippet {
  decl: string;
  file: string;
  line: number;
  statement: string;
  components?: { label: string; statement: string }[] | null;
}

/** One `paper_library_index.json` entry (only the fields this module reads). */
export interface PaperLibDecl {
  name: string;
  kind: string;
  file: string;
  line: number;
  source: string;
  refs: string[];
  proofRefs: string[];
  /** `undefined` when the index does not record it — see `DeclSource`. */
  usesSorry: boolean | undefined;
  /** Upstream declarations this one mentions: `{n: name, m: module}`. They are
   *  NOT index entries and have no source in the bundle. */
  extRefs: { n: string; m: string }[];
}

function asPaperLibDecls(raw: readonly unknown[] | null | undefined): PaperLibDecl[] {
  if (!Array.isArray(raw)) return [];
  const out: PaperLibDecl[] = [];
  for (const item of raw) {
    if (!item || typeof item !== "object") continue;
    const e = item as Record<string, unknown>;
    if (typeof e.name !== "string" || !e.name) continue;
    out.push({
      name: e.name,
      kind: typeof e.kind === "string" ? e.kind : "",
      file: typeof e.file === "string" ? e.file : "",
      line: typeof e.line === "number" ? e.line : 0,
      source: typeof e.source === "string" ? e.source : "",
      refs: Array.isArray(e.refs) ? e.refs.filter((r): r is string => typeof r === "string") : [],
      proofRefs: Array.isArray(e.proofRefs)
        ? e.proofRefs.filter((r): r is string => typeof r === "string")
        : [],
      // Tri-state: anything that is not an actual boolean is UNKNOWN, not
      // false. Collapsing a missing field to "proved" is how an unverified
      // helper would come to look clean.
      usesSorry: typeof e.usesSorry === "boolean" ? e.usesSorry : undefined,
      extRefs: Array.isArray(e.extRefs)
        ? (e.extRefs as unknown[])
            .filter(
              (r): r is { n: string; m: string } =>
                Boolean(r) &&
                typeof r === "object" &&
                typeof (r as { n?: unknown }).n === "string" &&
                typeof (r as { m?: unknown }).m === "string",
            )
            .map((r) => ({ n: r.n, m: r.m }))
        : [],
    });
  }
  return out;
}

const THEOREM_KINDS = new Set(["theorem", "lemma", "example"]);

function isTheoremKind(kind: string): boolean {
  return THEOREM_KINDS.has(kind);
}

/** Last dotted segment — the name the reader sees inside the paper's namespace. */
export function shortName(name: string): string {
  const i = name.lastIndexOf(".");
  return i >= 0 ? name.slice(i + 1) : name;
}

// ---------------------------------------------------------------------------
// name resolution against the paper module index
// ---------------------------------------------------------------------------

/** Resolves a snippet label / source identifier to a paper declaration. */
class DeclIndex {
  private readonly bySuffix = new Map<string, PaperLibDecl[]>();
  /** `statementRefs` memo — every entry's closure re-walks the same shared
   *  helpers, and the biggest bundles have ~900 declarations across ~800
   *  drawers. Keyed by declaration name; the answer depends only on the index. */
  readonly refCache = new Map<string, string[]>();
  readonly byName = new Map<string, PaperLibDecl>();

  constructor(decls: readonly PaperLibDecl[]) {
    for (const d of decls) {
      if (this.byName.has(d.name)) continue; // first wins; the index is deduped upstream
      this.byName.set(d.name, d);
      const parts = d.name.split(".");
      // Every dotted SUFFIX of the name, so both `Obs` and
      // `CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs` resolve.
      for (let i = parts.length - 1; i >= 0; i--) {
        const key = parts.slice(i).join(".");
        const bucket = this.bySuffix.get(key);
        if (bucket) bucket.push(d);
        else this.bySuffix.set(key, [d]);
      }
    }
  }

  resolve(label: string): PaperLibDecl | null {
    const trimmed = label.trim();
    if (!trimmed) return null;
    const exact = this.byName.get(trimmed);
    if (exact) return exact;
    const bucket = this.bySuffix.get(trimmed);
    // An ambiguous suffix is no resolution at all: guessing would attach the
    // wrong source to a component, which is worse than showing one fewer.
    return bucket && bucket.length === 1 ? bucket[0] : null;
  }
}

// ---------------------------------------------------------------------------
// statement-level references
// ---------------------------------------------------------------------------

/**
 * The text a reader is shown as the declaration's STATEMENT.
 *
 * For a theorem/lemma that is the signature only (binders + goal); the proof is
 * not part of the claim. For everything else — `def`, `abbrev`, `structure`,
 * `inductive`, `instance` — the body IS the statement, so the whole source
 * counts. Comments are blanked (position-preservingly) so a docstring's prose
 * can never be read as a reference.
 */
function statementText(decl: PaperLibDecl): string {
  const cleaned = stripLeanComments(decl.source);
  if (!isTheoremKind(decl.kind)) return cleaned;
  const scan = scanTheoremSignature(decl.source);
  if (!scan) return cleaned;
  return scan.cleaned.slice(0, scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd);
}

/**
 * Names bound by the declaration's own parameter telescope — excluded from the
 * identifier sweep so a parameter that happens to share a paper declaration's
 * short name can't pull that declaration in.
 *
 * Only the SIGNATURE is scanned (up to the first depth-0 `:` or `:=`). Inside a
 * body the same `(names : type)` shape is a type ASCRIPTION, not a binder —
 * `(splitCellCount sample 1 k 1 1 : ℝ)` would otherwise register
 * `splitCellCount` as a bound variable and suppress a real reference.
 */
function boundNames(decl: PaperLibDecl): Set<string> {
  const names = new Set<string>();
  const cleaned = stripLeanComments(decl.source);
  const header = cleaned.slice(0, signatureHeaderEnd(cleaned));
  for (const m of header.matchAll(/[({[⦃]([^:(){}[\]⦃⦄]*):/g)) {
    for (const tok of m[1].split(/\s+/)) if (tok) names.add(tok);
  }
  return names;
}

/** Index of the first depth-0 `:` or `:=` — where the parameter telescope ends
 *  and the result type or body begins. */
function signatureHeaderEnd(cleaned: string): number {
  const depths = normAwareDepths(cleaned);
  for (let i = 0; i < cleaned.length; i++) {
    if (depths[i] === 0 && cleaned[i] === ":") return i;
  }
  return cleaned.length;
}

/**
 * Declarations referenced by `decl`'s STATEMENT, as fully-qualified paper
 * names.
 *
 * The index's own `refs` is the elaborated TYPE's references and `proofRefs`
 * the value/proof's — verified empirically: `hybridEstimator`'s `refs` holds
 * only `Obs` (its type) while `heavyContribution`/`lightContribution` (its
 * body, i.e. its definition) sit in `proofRefs`. So `proofRefs` counts as
 * statement-level for definition-like kinds and must be ignored for theorems.
 *
 * Neither list is complete on its own: a `structure`'s field types and
 * `extends` parents appear in neither (`ControlZeroClass` lists only
 * `DiscreteLaw`, not `ExperimentClass`/`outcomeMean`). So the shown statement
 * text is also tokenized and matched against the paper index — which is, in any
 * case, exactly the set of names the reader can see.
 */
function statementRefs(decl: PaperLibDecl, index: DeclIndex): string[] {
  const cached = index.refCache.get(decl.name);
  if (cached) return cached;
  const out = new Set<string>();
  const add = (name: string) => {
    const r = index.resolve(name);
    if (r && r.name !== decl.name) out.add(r.name);
  };
  for (const r of decl.refs) add(r);
  if (!isTheoremKind(decl.kind)) for (const r of decl.proofRefs) add(r);
  const bound = boundNames(decl);
  const self = shortName(decl.name);
  for (const tok of identifierTokens(statementText(decl))) {
    if (tok === self || bound.has(tok)) continue;
    add(tok);
  }
  const refs = [...out];
  index.refCache.set(decl.name, refs);
  return refs;
}

// ---------------------------------------------------------------------------
// closure + classification
// ---------------------------------------------------------------------------

interface Owner {
  objId: string;
  label: string;
}

/** Which paper block (if any) a declaration belongs to, as anchor or component. */
interface Ownership {
  anchors: Map<string, Owner>;
  /** Declarations belonging to a `citedv` entry — an external result this
   *  paper ASSUMES rather than proves. It has no body block, but it does have a
   *  Formal-layer panel the reader can open. */
  cited: Map<string, Owner>;
}

function hasBodyBlock(entry: PaperLeanEntry): boolean {
  return !WEB_ONLY_ENVS.includes(entry.env) && entry.status !== "presentation-synthesized";
}

function buildOwnership(
  entries: readonly PaperLeanEntry[],
  snippets: Record<string, PaperLeanSnippet>,
  index: DeclIndex,
): Ownership {
  const anchors = new Map<string, Owner>();
  const cited = new Map<string, Owner>();
  for (const e of entries) {
    // `citedv` is web-only, so it has no body block — but it is precisely the
    // set of results the paper ASSUMES, which the reader must be able to tell
    // apart from machinery the paper builds. (`auxiliary`/`symbol` stay out:
    // those are agent-introduced helpers and notation clusters, not inputs.)
    const isCited = e.env === "citedv";
    if (!isCited && !hasBodyBlock(e)) continue;
    const owner: Owner = { objId: e.obj_id, label: e.paper_label };
    const snip = snippets[e.obj_id];
    const anchorName = resolveAnchor(e, snip, index);
    const claim = (name: string, into: Map<string, Owner>) => {
      // First entry in crosswalk order wins, so ownership is deterministic when
      // two entries claim the same declaration.
      if (!into.has(name)) into.set(name, owner);
    };
    if (anchorName) claim(anchorName, isCited ? cited : anchors);
    // A composite block's COMPONENTS confer no ownership: a supporting definition one block lists
    // among its pieces (a helper `def` several statements use) is not that block's subject, so
    // another block that uses it shows the helper's own source inline rather than sending the
    // reader to a definition that is not about it. Only an assumed external result claims its
    // components, since those are inputs the paper does not build.
    if (isCited) {
      for (const c of snip?.components ?? []) {
        const r = index.resolve(c.label);
        if (r) claim(r.name, cited);
      }
    }
  }
  return { anchors, cited };
}

function resolveAnchor(
  entry: PaperLeanEntry,
  snippet: PaperLeanSnippet | undefined,
  index: DeclIndex,
): string | null {
  // A composite object (or a `@realizes` symbol cluster) has no single anchor:
  // its `decl` is a parenthesised placeholder — "(composite)", "(symbol)" —
  // and its content lives entirely in `components`.
  for (const label of [entry.lean?.decl, snippet?.decl]) {
    if (!label || label.startsWith("(")) continue;
    const r = index.resolve(label);
    if (r) return r.name;
  }
  return null;
}

interface Reached {
  decl: PaperLibDecl;
  depth: number;
}

function walkClosure(
  seeds: readonly string[],
  index: DeclIndex,
  stop: (name: string) => boolean,
): { reached: Reached[]; truncated: number } {
  const seen = new Map<string, number>();
  const reached: Reached[] = [];
  let frontier: string[] = [];
  for (const s of seeds) {
    if (seen.has(s)) continue;
    const decl = index.byName.get(s);
    if (!decl) continue;
    seen.set(s, 0);
    reached.push({ decl, depth: 0 });
    if (!stop(s)) frontier.push(s);
  }
  for (let depth = 1; depth <= MAX_DEPTH && frontier.length > 0; depth++) {
    const next: string[] = [];
    for (const name of frontier) {
      const decl = index.byName.get(name);
      if (!decl) continue;
      for (const ref of statementRefs(decl, index)) {
        if (seen.has(ref)) continue; // cycle guard: a name is expanded at most once
        const refDecl = index.byName.get(ref);
        if (!refDecl) continue;
        seen.set(ref, depth);
        reached.push({ decl: refDecl, depth });
        // A declaration the reader can check at its own numbered block is a
        // link, not an inline: the walk stops there rather than dragging that
        // block's whole helper tree into this drawer.
        if (!stop(ref)) next.push(ref);
      }
    }
    frontier = next;
  }
  // Hitting the cap with a live frontier means the drawer is INCOMPLETE — the
  // very failure this module exists to fix. Count what was left unexplored so
  // the reader is told rather than shown a silently truncated set.
  const unexplored = new Set<string>();
  for (const name of frontier) {
    const decl = index.byName.get(name);
    if (!decl) continue;
    for (const ref of statementRefs(decl, index)) {
      if (!seen.has(ref) && index.byName.has(ref)) unexplored.add(ref);
    }
  }
  return { reached, truncated: unexplored.size };
}

/**
 * What the shared table stores for a declaration.
 *
 * The drawer's job is a CHECKABLE STATEMENT, so a theorem/lemma keeps its
 * docstring and signature through the goal and drops the proof: the proofs of
 * helpers a reader was pulled into are noise, the verification badges already
 * say they went through, and each row carries file+line to the real source. A
 * `def`/`abbrev`/`structure`/`instance`/`inductive` keeps its whole source,
 * because there the body IS the statement.
 */
function tableStatement(decl: PaperLibDecl): string {
  if (!isTheoremKind(decl.kind)) return decl.source;
  const scan = scanTheoremSignature(decl.source);
  if (!scan || scan.conclusionEnd < 0) return decl.source; // can't locate the proof — keep it all
  return decl.source.slice(0, scan.conclusionEnd).replace(/\s+$/, "");
}

/** Structures `source` only when it is a theorem-like declaration. */
function structureIfTheorem(
  source: string,
  kind: string | undefined,
  citedNames: ReadonlySet<string>,
): StructuredView | undefined {
  if (!source) return undefined;
  const propRecord = (kind === "structure" || kind === "class") && isPropRecord(source);
  if (kind === "def" || (kind === undefined && isDefinitionLike(source))) {
    return structureDefinitionView(source) ?? undefined;
  }
  if (((kind === "structure" || kind === "class") && !propRecord) || (kind === undefined && isRecordLike(source) && !isPropRecord(source))) {
    return structureDataRecordView(source) ?? undefined;
  }
  if (kind === "instance" || (kind === undefined && isInstanceLike(source))) return structureInstanceView(source) ?? undefined;
  if (kind === "inductive" || (kind === undefined && isInductiveLike(source))) return structureInductiveView(source) ?? undefined;
  if (kind && !isTheoremKind(kind) && !propRecord) return undefined;
  return structureStatementView(source, citedNames) ?? structurePropRecordView(source) ?? undefined;
}

// ---------------------------------------------------------------------------
// NL↔Lean crosslinks: the Lean half
// ---------------------------------------------------------------------------

/**
 * Applies the artifact's row→prose assignments to the artifact's own structured
 * view: each assigned row gets the crosslink token the body transform writes
 * into `data-xl`, and a row the paper never states is marked `unstated`.
 *
 * There is nothing to search for here. The pipeline parsed the statement, gave
 * every row a stable id, and said which rows the prose states; the site is only
 * copying that across. Returns the ids the assignments named but the tree does
 * not contain — an artifact/tree mismatch worth reporting.
 */
function applyAssignments(objId: string, block: NlBlock, view: StructuredView): string[] {
  const byId = new Map<string, HypRow | ConclusionCard>();
  const note = (row: HypRow | ConclusionCard) => {
    if (row.id !== undefined && !byId.has(row.id)) byId.set(row.id, row);
  };
  const walk = (card: ConclusionCard) => {
    card.hyps.forEach(note);
    note(card);
    for (const sub of card.sub ?? []) walk(sub);
  };
  view.sharedHyps.forEach(note);
  if (view.defRow) note(view.defRow);
  for (const card of view.conclusions) walk(card);

  const missing: string[] = [];
  for (const a of block.assignments) {
    const row = byId.get(a.row);
    if (!row) {
      missing.push(a.row);
      continue;
    }
    if (a.unstated) row.unstated = true;
    else if (a.segments.length > 0) row.xl = rowToken(objId, a.row);
  }
  return missing;
}

/**
 * Reclassifies a pulled-in helper as `env` when a display formula in this
 * block's prose is that helper.
 *
 * The closure calls a declaration `lean_only` — "Lean only, not stated in the
 * paper" — purely because no crosswalk entry anchors it. A `displayLink`
 * naming it says otherwise: the paper displays it right here, so it belongs
 * unfolded among the components. Only `lean_only` is promoted — a `paper` view
 * is stated at its own block and stays a chip pointing there, an `anchor` is
 * already the statement, and a `cited` result is an assumption. Depth is
 * untouched, so ordering is unchanged.
 */
/**
 * Adds `token` to a space-separated id list, HTML-class style. A component can
 * be shown by more than one display formula, and the UI word-matches
 * (`[data-xl~="…"]`), so the ids live side by side.
 */
function addXlToken(current: string | undefined, token: string): string {
  if (!current) return token;
  return current.split(" ").includes(token) ? current : `${current} ${token}`;
}

/**
 * Keeps only the display links whose declaration really exists in this paper,
 * normalising each surviving `decl` to its fully-qualified name.
 *
 * This runs BEFORE either half of the crosslink is built, for the same reason
 * `validateBlocks` does: the prose span and the Lean-side token must be emitted
 * from the same set. Filtering later would leave a `data-xl` (and a
 * `data-xl-decl`) on a formula whose counterpart was never minted — a token
 * that lights nothing, which reads to a reader as a broken link rather than an
 * absent one.
 */
/** One upstream declaration a paper module mentions. */
interface ExternalDecl {
  name: string;
  module: string;
}

/**
 * The upstream declarations this paper's modules reference, keyed by their full
 * name and — where unambiguous — their short name.
 *
 * Signature extRefs and resolved public snippet targets form the same catalogue
 * as P4. Imported proof helpers may occur only in snippets, outside signatures.
 */
function harvestExternals(
  decls: readonly PaperLibDecl[],
  snippets: Record<string, PaperLeanSnippet> = {},
): Map<string, ExternalDecl> {
  const byName = new Map<string, ExternalDecl>();
  const byShort = new Map<string, ExternalDecl | null>();
  for (const d of decls) {
    for (const r of d.extRefs) {
      if (!byName.has(r.n)) byName.set(r.n, { name: r.n, module: r.m });
      const short = shortName(r.n);
      if (short === r.n) continue;
      const seen = byShort.get(short);
      if (seen === undefined) byShort.set(short, { name: r.n, module: r.m });
      else if (seen && seen.name !== r.n) byShort.set(short, null); // ambiguous
    }
  }
  // Snippet labels are already canonical: do not introduce new short aliases.
  // Existing extRefs retain their module metadata and alias behavior.
  for (const snippet of Object.values(snippets)) {
    const pieces = [{ label: snippet.decl, statement: snippet.statement }, ...(snippet.components ?? [])];
    for (const piece of pieces) {
      if (!byName.has(piece.label) && isCanonicalSourceDeclaration(piece.label, piece.statement)) {
        byName.set(piece.label, { name: piece.label, module: "" });
      }
    }
  }
  const out = new Map(byName);
  // Short names are a tolerance, never a shadow: a full-name key always wins.
  for (const [short, decl] of byShort) if (decl && !out.has(short)) out.set(short, decl);
  return out;
}

/**
 * Absolute docs URL for an upstream module that has no page in THIS explorer.
 * A Causalean declaration does have one, but its path needs the full library
 * index (area + directory-file layout) which a paper bundle does not carry — so
 * those are resolved client-side through `/library/names.json`, the same map
 * the drawer's Lean highlighter already loads.
 */
function upstreamDocUrl(name: string, module: string): string | undefined {
  const root = module.split(".")[0];
  if (!["Mathlib", "Std", "Lean", "Init", "Batteries"].includes(root)) return undefined;
  return `https://leanprover-community.github.io/mathlib4_docs/${module.replace(/\./g, "/")}.html#${name}`;
}

export function resolveDisplayLinks(
  blocks: Record<string, NlBlock>,
  paperLibEntries?: readonly unknown[] | null,
  snippets: Record<string, PaperLeanSnippet> = {},
): { blocks: Record<string, NlBlock>; problems: LinkProblem[] } {
  const decls = asPaperLibDecls(paperLibEntries);
  const index = new DeclIndex(decls);
  const externals = harvestExternals(decls, snippets);
  const out: Record<string, NlBlock> = {};
  const problems: LinkProblem[] = [];
  for (const [objId, block] of Object.entries(blocks)) {
    const kept: NlDisplayLink[] = [];
    for (const link of block.displayLinks) {
      if (!link.decl) {
        kept.push(link); // presentation-only: nothing to resolve
        continue;
      }
      // v3 producers normalize displayLink decls to FULLY-QUALIFIED names, so
      // the consumer contract is an exact byName match — the suffix-capable
      // resolve would be looser than what the producer guarantees, and the two
      // ends of the contract must agree exactly.
      const decl = index.byName.get(link.decl);
      if (decl) {
        kept.push({ ...link, decl: decl.name });
        continue;
      }
      // A formula may show an UPSTREAM declaration — one this paper builds on
      // but does not define. Those have no index entry, only an `extRef`, so a
      // paper-entries-only lookup would throw away a perfectly good link.
      const external = externals.get(link.decl);
      if (external) {
        kept.push({ ...link, decl: external.name });
        continue;
      }
      // Only this link is dropped, never the block: one formula naming
      // something unknown says nothing about the rest of the block.
      problems.push({
        objId,
        reason: `displayLink names "${link.decl}", which is neither a declaration of this paper nor an upstream reference of it`,
      });
    }
    out[objId] = kept.length === block.displayLinks.length ? block : { ...block, displayLinks: kept };
  }
  return { blocks: out, problems };
}

function applyDisplayLinks(
  objId: string,
  block: NlBlock,
  views: ComponentView[],
  index: DeclIndex,
  externals: Map<string, ExternalDecl>,
  intern: (decl: PaperLibDecl) => string,
  declSources: Record<string, DeclSource>,
): LinkProblem[] {
  const problems: LinkProblem[] = [];
  let minted = false;

  for (const link of block.displayLinks) {
    if (!link.decl) continue;
    // One token per SEGMENT, not per link: a formula showing three constants
    // lights all three cards, and each of them lights that one formula.
    const token = segmentToken(objId, link.segment);
    const matches = views.filter((v) => v.decl === link.decl || v.key === link.decl);
    if (matches.length > 0) {
      for (const v of matches) {
        // The Lean-side half of the pair. It goes on whatever the component is
        // — an anchor or a cited assumption can be what a display formula shows
        // just as much as a helper can — so hovering either side lights the
        // other. Only a `lean_only` view is RECLASSIFIED: the closure called it
        // "Lean only, not stated in the paper" purely because no crosswalk
        // entry anchors it, and a display link says the paper shows it here. A
        // `paper` view is stated at its own block and stays a chip pointing
        // there, an `anchor` is already the statement, a `cited` one is an
        // assumption.
        v.xl = addXlToken(v.xl, token);
        if (v.cls === "lean_only") v.cls = "env";
      }
      continue;
    }

    // A displayed formula may name any declaration of the paper module, not
    // only one the reference closure happened to reach — a definition can be
    // displayed in prose without appearing in any statement this block builds
    // on. So the view is minted rather than the link discarded.
    const decl = index.resolve(link.decl);
    if (!decl) {
      // An UPSTREAM declaration: this paper builds on it but does not define
      // it, so there is no source to inline. The card carries its name and a
      // way out to the library rather than a statement — and the same token, so
      // the two-sided highlight works exactly as it does for anything else.
      const external = externals.get(link.decl);
      if (external) {
        const existing = views.find((v) => v.external && v.fullName === external.name);
        if (existing) {
          existing.xl = addXlToken(existing.xl, token);
          continue;
        }
        const view: ComponentView = {
          decl: shortName(external.name),
          cls: "env",
          depth: 1,
          external: true,
          fullName: external.name,
          module: external.module,
          xl: token,
        };
        const url = upstreamDocUrl(external.name, external.module);
        if (url) view.docUrl = url;
        views.push(view);
        minted = true;
        continue;
      }
      // Only this link is dropped, not the block: the rest of the block's
      // crosslinks are unaffected by one formula naming something unknown.
      problems.push({
        objId,
        reason: `displayLink names "${link.decl}", which is neither a declaration of this paper nor an upstream reference of it`,
      });
      continue;
    }
    const already = views.find((v) => v.key === decl.name);
    if (already) {
      already.xl = addXlToken(already.xl, token);
      if (already.cls === "lean_only") already.cls = "env";
      continue;
    }
    // Depth 1, not `1 + max`: depth is closure distance, and this has none —
    // but the block DISPLAYS it, which makes it as immediate as anything the
    // statement names directly. Burying it below the whole closure would rank
    // it by a distance it does not have.
    views.push({ decl: shortName(decl.name), key: intern(decl), cls: "env", depth: 1, xl: token });
    minted = true;
  }

  if (minted) sortComponentViews(views, declSources);
  return problems;
}

/**
 * Demotes `env` views that no formula here actually links to.
 *
 * `env` says "↔ a formula in this statement". The legacy component list
 * attaches pieces to a statement without that being true of each one — a reader
 * saw `Obs` labelled as a formula in a statement whose prose contains no such
 * formula. Under v3 the label is EARNED, and a piece the block's crosslinks
 * never touch is just one more declaration the drawer shows without the paper
 * stating it: `lean_only`, the same as anything else in that position. HOW it
 * came to be attached is pipeline provenance, which a reader needs no class for.
 *
 * Only applied where there IS link evidence to earn the label against. A bundle
 * with no artifact keeps its legacy labelling: demoting everything there would
 * over-claim in the other direction, asserting the paper states none of it on
 * exactly as little evidence.
 */
function demoteUnlinkedComponents(views: ComponentView[]): void {
  for (const v of views) {
    if (v.cls === "env" && v.xl === undefined) v.cls = "lean_only";
  }
}

/**
 * Orders the cards the way the paper reads: by where in the prose the formula
 * that links each one appears. A reader scanning the block top to bottom meets
 * the cards in the same order. Views no formula links keep the structural
 * order (closure depth, then source position) and follow after. The anchor is
 * the statement itself, so it stays first whatever links to it.
 */
function sortByPaperOrder(
  objId: string,
  block: NlBlock,
  views: ComponentView[],
  declSources: Record<string, DeclSource>,
): void {
  const startOf = new Map(block.segments.map((seg) => [segmentToken(objId, seg.id), seg.start]));
  const linkPos = (v: ComponentView): number | undefined => {
    const starts = (v.xl ?? "")
      .split(" ")
      .map((t) => startOf.get(t))
      .filter((n): n is number => n !== undefined);
    return starts.length > 0 ? Math.min(...starts) : undefined;
  };
  const where = (v: ComponentView) => {
    const src = v.key ? declSources[v.key] : undefined;
    return { file: src?.file ?? v.file ?? "", line: src?.line ?? v.line ?? 0 };
  };
  const rank = (v: ComponentView) => (v.cls === "anchor" ? 0 : linkPos(v) !== undefined ? 1 : 2);
  views.sort((a, b) => {
    const [ra, rb] = [rank(a), rank(b)];
    if (ra !== rb) return ra - rb;
    if (ra === 1) return linkPos(a)! - linkPos(b)! || a.decl.localeCompare(b.decl);
    const [wa, wb] = [where(a), where(b)];
    return a.depth - b.depth || wa.file.localeCompare(wb.file) || wa.line - wb.line || a.decl.localeCompare(b.decl);
  });
}

/** Shallowest first, then source order — the same order `componentViews`
 *  establishes, reapplied after a minted view joins the list. */
function sortComponentViews(views: ComponentView[], declSources: Record<string, DeclSource>): void {
  const where = (v: ComponentView) => {
    const src = v.key ? declSources[v.key] : undefined;
    return { file: src?.file ?? v.file ?? "", line: src?.line ?? v.line ?? 0 };
  };
  views.sort((a, b) => {
    const [wa, wb] = [where(a), where(b)];
    return a.depth - b.depth || wa.file.localeCompare(wb.file) || wa.line - wb.line || a.decl.localeCompare(b.decl);
  });
}

/** Proposition carried by a composite entry with no direct anchor. The first
 * component is the producer's principal declaration; if it is not a Prop, a
 * sole proposition among the components is still unambiguous. Anything else
 * stays unstructured rather than guessing and hiding part of the claim. */
function compositeProposition(
  snippet: PaperLeanSnippet,
  index: DeclIndex,
): { source: string; kind: string | undefined } | null {
  const candidates = (snippet.components ?? []).map((component) => {
    const decl = index.resolve(component.label);
    return { source: decl?.source || component.statement || "", kind: decl?.kind };
  });
  const isProposition = (candidate: { source: string; kind: string | undefined }) =>
    (candidate.kind !== undefined && isTheoremKind(candidate.kind)) ||
    scanPropDefinitionSignature(candidate.source) !== null ||
    isPropRecord(candidate.source);
  if (candidates[0] && isProposition(candidates[0])) return candidates[0];
  const propositions = candidates.filter(isProposition);
  if (propositions.length === 1) return propositions[0];
  // A composite definition block is stated by its principal (first) component.
  const first = candidates[0];
  if (propositions.length === 0 && first && (isDefinitionLike(first.source) || isRecordLike(first.source) || isInstanceLike(first.source) || isInductiveLike(first.source))) return first;
  return null;
}

// ---------------------------------------------------------------------------
// entry point
// ---------------------------------------------------------------------------

export interface EnrichArgs {
  entries: readonly PaperLeanEntry[];
  snippets: Record<string, PaperLeanSnippet>;
  /** `paper_library_index.json`'s `entries`; absent/empty simply limits the
   *  enrichment to what the snippet already carries. */
  paperLibEntries?: readonly unknown[] | null;
  /** `nl_links.json`'s `blocks` (obj_id → its structure, segments and
   *  assignments); absent for the many bundles that predate the artifact. */
  nlLinks?: Record<string, NlBlock> | null;
}

/**
 * Per-obj_id drawer enrichment — a structured view of each entry's own
 * statement and the transitive set of paper declarations its statements
 * reference — plus the shared source table those references point into.
 */
export function enrichSnippets(args: EnrichArgs): EnrichmentResult {
  const decls = asPaperLibDecls(args.paperLibEntries);
  const index = new DeclIndex(decls);
  const ownership = buildOwnership(args.entries, args.snippets, index);
  const externals = harvestExternals(decls, args.snippets);
  // Names of the paper's assumed external results, short and fully-qualified,
  // so a hypothesis mentioning one can be chipped as the assumption it is.
  const citedNames = new Set<string>();
  for (const name of ownership.cited.keys()) {
    citedNames.add(name);
    citedNames.add(shortName(name));
  }
  const out: Record<string, SnippetEnrichment> = {};
  const declSources: Record<string, DeclSource> = {};
  const linkProblems: LinkProblem[] = [];

  /** Records a declaration in the shared table (once) and returns its key. */
  const intern = (decl: PaperLibDecl): string => {
    if (!declSources[decl.name]) {
      const entry: DeclSource = { file: decl.file, line: decl.line, statement: tableStatement(decl) };
      const structured = structureIfTheorem(decl.source, decl.kind, citedNames);
      if (structured) entry.structured = structured;
      // Straight from the index — never scanned out of `statement`, which for a
      // theorem has had its proof (and any `sorry` in it) trimmed away. Carried
      // through as-is, so "unknown" stays distinguishable from "proved".
      if (decl.usesSorry !== undefined) entry.usesSorry = decl.usesSorry;
      declSources[decl.name] = entry;
    }
    return decl.name;
  };

  for (const entry of args.entries) {
    const snippet = args.snippets[entry.obj_id];
    if (!snippet) continue;
    const enrichment: SnippetEnrichment = {};

    const anchorName = resolveAnchor(entry, snippet, index);
    const anchorDecl = anchorName ? index.byName.get(anchorName) ?? null : null;
    const composite = !anchorDecl && !snippet.statement.trim() ? compositeProposition(snippet, index) : null;
    const anchorKind = anchorDecl?.kind ?? entry.lean?.decl_kind ?? composite?.kind;
    const anchorSource = anchorDecl?.source || snippet.statement || composite?.source || "";
    const block = args.nlLinks?.[entry.obj_id];

    // The artifact's own structured view wins where there is one: it is what
    // the row ids and assignments refer to, and re-deriving it here could only
    // disagree. The site's parser is the fallback for blocks and bundles with
    // no artifact — those simply carry no crosslink tokens.
    let structured: StructuredView | undefined;
    if (block?.structured) {
      structured = block.structured;
      for (const rowId of applyAssignments(entry.obj_id, block, structured)) {
        linkProblems.push({
          objId: entry.obj_id,
          reason: `assignment names row "${rowId}", absent from the artifact's structured view`,
        });
      }
      // Chipping a hypothesis that assumes a cited result is the site's call,
      // not the artifact's — it depends on this bundle's crosswalk.
      markCitedHyps(allHypRows(structured), citedNames);
    } else {
      structured = structureIfTheorem(anchorSource, anchorKind, citedNames);
    }
    if (structured) enrichment.structured = structured;

    const { views, truncated } = componentViews(entry, snippet, index, ownership, anchorName, intern);
    // Before anything reads `cls`: a helper this block DISPLAYS is part of the
    // statement, not a "Lean only" aside — and may not be in the closure at all.
    if (block) {
      linkProblems.push(
        ...applyDisplayLinks(entry.obj_id, block, views, index, externals, intern, declSources),
      );
      demoteUnlinkedComponents(views);
      sortByPaperOrder(entry.obj_id, block, views, declSources);
    }
    if (views.length > 0) enrichment.componentViews = views;
    if (truncated > 0) enrichment.closureTruncated = truncated;
    // A statement whose helpers are only proved up to `sorry` is not verified,
    // whatever its own proof says — surface that at the statement, not buried
    // in one component's badge. Helpers whose status the index does not record
    // are counted separately: unknown is not clean.
    // Upstream declarations are excluded: their verification is the upstream
    // library's business, and counting them as "status unknown" would report
    // this paper as less verified than it is.
    const pulled = views.filter((v) => !v.external && (v.cls === "env" || v.cls === "lean_only"));
    const statusOf = (v: ComponentView) => (v.key ? declSources[v.key]?.usesSorry : undefined);
    if (pulled.some((v) => statusOf(v) === true)) enrichment.closureHasSorry = true;
    const unknown = pulled.filter((v) => statusOf(v) === undefined).length;
    if (unknown > 0) enrichment.closureSorryUnknown = unknown;

    if (enrichment.structured || enrichment.componentViews) out[entry.obj_id] = enrichment;
  }
  return { snippets: out, declSources, linkProblems };
}

function componentViews(
  entry: PaperLeanEntry,
  snippet: PaperLeanSnippet,
  index: DeclIndex,
  ownership: Ownership,
  anchorName: string | null,
  intern: (decl: PaperLibDecl) => string,
): { views: ComponentView[]; truncated: number } {
  const ownComponents = new Set<string>();
  const unresolved: { label: string; statement: string }[] = [];
  for (const c of snippet.components ?? []) {
    const r = index.resolve(c.label);
    if (r) ownComponents.add(r.name);
    else unresolved.push(c);
  }

  const classify = (name: string): { cls: ComponentView["cls"]; owner?: Owner } => {
    if (name === anchorName) return { cls: "anchor" };
    // An assumed external result outranks every other reading: it is neither
    // this paper's machinery nor a result stated elsewhere in it, and calling
    // it "Lean only" would suggest formalized infrastructure rather than an
    // input the theorem depends on.
    const citedOwner = ownership.cited.get(name);
    if (citedOwner && citedOwner.objId !== entry.obj_id) return { cls: "cited", owner: citedOwner };
    const anchorOwner = ownership.anchors.get(name);
    if (anchorOwner && anchorOwner.objId !== entry.obj_id) return { cls: "paper", owner: anchorOwner };
    if (ownComponents.has(name)) return { cls: "env" };
    return { cls: "lean_only" };
  };

  const seeds = [...(anchorName ? [anchorName] : []), ...ownComponents];
  // Neither a result stated at its own block nor an assumed external one drags
  // its helper tree in: the reader checks the first at that block, and the
  // second is an assumption, not something to unfold.
  const stops = new Set<ComponentView["cls"]>(["paper", "cited"]);
  const { reached, truncated } = walkClosure(seeds, index, (name) => stops.has(classify(name).cls));

  // Sorted on the declaration's own position, which the slimmed-down view no
  // longer carries once its source lives in the shared table.
  const rows: { view: ComponentView; file: string; line: number }[] = reached.map(({ decl, depth }) => {
    const { cls, owner } = classify(decl.name);
    const view: ComponentView = { decl: shortName(decl.name), key: intern(decl), cls, depth };
    if (owner) {
      view.paperObjId = owner.objId;
      view.paperLabel = owner.label;
    }
    return { view, file: decl.file, line: decl.line };
  });

  // A component the pipeline attached but the module index doesn't know (an
  // older bundle, or a declaration outside the paper's own modules) has no
  // entry in the shared table, so it keeps carrying its own text inline —
  // showing one fewer piece would be a regression.
  for (const c of unresolved) {
    rows.push({
      view: {
        decl: shortName(c.label),
        cls: "env",
        depth: 0,
        file: snippet.file,
        line: 0,
        statement: c.statement,
      },
      file: snippet.file,
      line: 0,
    });
  }

  // Deterministic: shallowest first (what the statement itself names), then
  // source order, so a rebuild of the same bundle emits byte-identical JSON.
  rows.sort(
    (a, b) =>
      a.view.depth - b.view.depth ||
      a.file.localeCompare(b.file) ||
      a.line - b.line ||
      a.view.decl.localeCompare(b.view.decl),
  );
  return { views: rows.map((r) => r.view), truncated };
}
