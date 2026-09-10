/**
 * The library page's structured view of ONE declaration, for every kind the
 * explorer shows — the same "one row per binder" layout theorems have had,
 * extended to definitions and assumption bundles so a reader can see, in the
 * same place on every card, what a declaration takes and what it says:
 *
 *   theorem     hypotheses → conclusion (nested cards)
 *   definition  parameters → def (name applied to its parameters : type)
 *                          → given by (the `:=` body, let-steps as rows)
 *   propdef     parameters → def (… : Prop) → given by (the proposition, split
 *                          into cards exactly as a theorem's conclusion is)
 *   assumption  parameters → assumes (one clause per field of a Prop-valued
 *                          structure, each with its own docstring)
 *   record      parameters → fields (a data-carrying structure/class)
 *
 * The conclusion / given-by side reuses the paper drawer's card builder
 * (`leanCards.ts`): a leading `∀ …`/`premise →` telescope becomes hypothesis
 * rows, an `∃` run is hoisted, and conjunctions split into nested cards,
 * recursively — a theorem whose conclusion is itself a proposition with its
 * own hypotheses expands level by level rather than sitting in one block.
 *
 * Section variables (`variable (S : Sys)` above a `def`) never appear in the
 * authored source; they are recovered from the index's elaborated binder list
 * (`LibDecl.params`) and shown as parameter rows tagged "section".
 *
 * Conservative like everything under it: any shape it does not confidently
 * understand yields `null` and the caller keeps the flat rendering.
 */

import {
  breakLines,
  classifyChip,
  extractComment,
  formatBody,
  isBinderRow,
  isChain,
  mergeAttachedInstances,
  parseBinderGroup,
  scanDefinitionSignature,
  scanInductiveSignature,
  scanInstanceSignature,
  scanPropDefinitionSignature,
  splitWhereFields,
  scanTheoremSignature,
  stripLeadingQuantifier,
  stripLeanComments,
  structureRecordSource,
  type BinderRow,
  type DefinitionScan,
  type SignatureScan,
  type StatementItem,
  type StmtBody,
  type StmtLine,
} from "./leanStatement.js";
import {
  buildCard,
  conjunctsOf,
  leadingImplicationIndex,
  dedent,
  isPropRecord,
  liftTelescope,
  matchedCloseIndex,
  numberedClauses,
  squash,
  stripLetRun,
  topLevelColonIndex,
  type ConclusionCard,
  type HypRow,
} from "./leanCards.js";
import { linkifyStatement, type Library } from "./library.js";

export type DeclRole = "theorem" | "definition" | "propdef" | "assumption" | "record" | "instance" | "inductive";

/** One elaborated binder of a declaration's type (see `ParamEntry` in
 *  LibraryIndexCore.lean). */
export interface LibParam {
  n: string;
  t: string;
  bi: "explicit" | "implicit" | "inst" | "strict" | string;
}

/** A conclusion / given-by clause, recursively fine-grained (the library-page
 *  twin of `leanCards.ConclusionCard`, with display-ready bodies). */
export interface ViewCard {
  /** `∀` binders and `premise →` prefixes lifted at this level. */
  hyps: StatementItem[];
  /** A leading `∃ …,` run that scopes the split below (branching cards only). */
  intro?: StmtLine[];
  /** Leaf statement. */
  code?: StmtBody;
  /** Nested split of a conjunction. */
  sub?: ViewCard[];
  /** Hover tokens: `⊢` always, plus `⊢N` for the N-th TOP-LEVEL card (a
   *  docstring's `[phrase](step:N)`); nested cards inherit their parent's. */
  token: string;
}

export interface DefRow {
  /** `name arg₁ arg₂ …` — the declaration applied to its explicit parameters. */
  head: string;
  /** Its type (`Measure ℝ`, `Prop`, …). */
  type: StmtBody;
}

export interface DeclView {
  role: DeclRole;
  /** Hypotheses (theorem) or parameters (everything else), in source order,
   *  with any `-- section` comment the author placed between them. */
  rows: StatementItem[];
  /** Record fields / assumption clauses; null for the other roles. */
  fields: StatementItem[] | null;
  /** The `def` row; null for theorems and records. */
  defRow: DefRow | null;
  /** Conclusion (theorem) / given-by (definition, propdef) cards; null when
   *  the clause side did not split, in which case `flat` carries it. */
  cards: ViewCard[] | null;
  /** The clause side as plain lines when `cards` is null; `[]` when there is
   *  nothing to show (records, assumptions). */
  flat: StmtBody;
  /** A quiet footnote under the clauses (an inductive's `deriving …`). */
  note?: string;
}

// ---------------------------------------------------------------------------
// rows
// ---------------------------------------------------------------------------

/** Binder groups + interleaved comments → rows. `null` if any group fails. */
function groupRows(rawSource: string, scan: SignatureScan): StatementItem[] | null {
  const rows: StatementItem[] = [];
  let prevEnd = scan.telescopeStart;
  for (const g of scan.groups) {
    const comment = extractComment(rawSource.slice(prevEnd, g.start));
    if (comment) rows.push({ kind: "comment", text: comment });
    const row = parseBinderGroup(g.raw);
    if (!row) return null;
    rows.push({ kind: "binder", ...row });
    prevEnd = g.end;
  }
  return rows;
}

/** A hypothesis row lifted out of a goal / body by the card builder: a `∀`
 *  header (`∀ (x : ℝ) (hx : 0 < x)` → one row per group; `∀ x y : ℝ` → one
 *  row), a `premise →` (nameless row), or a `let x := v` step. */
function liftedRows(h: HypRow): StatementItem[] {
  return liftedRowsRaw(h).map((r) => (r.kind === "binder" ? { ...r, origin: "lifted" as const } : r));
}

function liftedRowsRaw(h: HypRow): StatementItem[] {
  const code = h.code.trim();
  if (/^∀(?![ᵐᶠ])/.test(code)) {
    const body = code.replace(/^∀/, "").trim();
    if (body.startsWith("(") || body.startsWith("{") || body.startsWith("[") || body.startsWith("⦃")) {
      const out: StatementItem[] = [];
      let rest = body;
      while (rest) {
        const close = matchedCloseIndex(rest);
        if (close < 0) break;
        const row = parseBinderGroup(rest.slice(0, close + 1));
        if (!row) break;
        out.push({ kind: "binder", ...row });
        rest = rest.slice(close + 1).trim();
      }
      if (out.length > 0 && !rest) return out;
    }
    const colon = topLevelColonIndex(body);
    if (colon > 0) {
      return [
        {
          kind: "binder",
          names: body.slice(0, colon).trim(),
          chip: h.chip === "cited" ? "hyp" : h.chip,
          body: formatBody(body.slice(colon + 1)),
          bracketKind: "explicit",
        },
      ];
    }
    // `∀ x, …` with no type: the name alone, no type text to show.
    return [{ kind: "binder", names: body, chip: "decl", body: [], bracketKind: "explicit" }];
  }
  if (/^let\b/.test(code)) {
    const m = code.match(/^let\s+([^\s:=]+)([\s\S]*?):=\s*([\s\S]*)$/);
    if (m) {
      const [, name, typePart, value] = m;
      const t = typePart.trim().replace(/^:\s*/, "");
      const text = t ? `${value.trim()}   (: ${t})` : value.trim();
      return [{ kind: "binder", names: name, chip: "decl", body: formatBody(text), bracketKind: "explicit" }];
    }
  }
  return [
    {
      kind: "binder",
      names: "",
      chip: h.chip === "cited" ? "hyp" : h.chip,
      body: formatBody(code),
      bracketKind: "explicit",
    },
  ];
}

// ---------------------------------------------------------------------------
// cards
// ---------------------------------------------------------------------------

/** `numbers` maps a NUMBERED card (see `numberedClauses`) to its index; a card
 *  inherits its nearest numbered ancestor's token, everything else is `⊢`. */
function toViewCard(c: ConclusionCard, numbers: Map<ConclusionCard, number>, inherited = "⊢"): ViewCard {
  const n = numbers.get(c);
  const token = n !== undefined ? `⊢ ⊢${n}` : inherited;
  const out: ViewCard = { hyps: c.hyps.flatMap(liftedRows), token };
  if (c.intro) out.intro = breakLines(c.intro, 0);
  if (c.code !== undefined) out.code = formatBody(c.code);
  if (c.sub) out.sub = c.sub.map((s) => toViewCard(s, numbers, token));
  return out;
}

/** `named` — the view has a def/instance/inductive row that the `(goal)`
 *  phrase pairs with, so numbered clauses carry ONLY their own `⊢N`: hovering
 *  one clause must not light the phrase naming the whole object. A theorem has
 *  no such row, so its conclusion cards keep `⊢` too (the `(goal)` phrase
 *  covers all of them). */
function toViewCards(cards: ConclusionCard[], named = false): ViewCard[] {
  const numbers = new Map<ConclusionCard, number>();
  numberedClauses(cards).forEach((c, i) => numbers.set(c, i + 1));
  const out = cards.map((c) => toViewCard(c, numbers));
  if (named) {
    const strip = (c: ViewCard) => {
      if (/⊢\d/.test(c.token)) c.token = c.token.replace(/(^| )⊢( |$)/, " ").trim();
      for (const sc of c.sub ?? []) strip(sc);
    };
    out.forEach(strip);
  }
  return out;
}

interface ClauseSplit {
  lifted: StatementItem[];
  cards: ViewCard[] | null;
  flat: StmtBody;
}

/**
 * A proposition (a theorem's goal, a Prop-definition's body) as lifted rows +
 * cards. Losslessness is checked token-by-token as in the paper drawer; on
 * any doubt the whole clause is kept flat and nothing is lifted.
 */
function splitProposition(goal: string, named = false): ClauseSplit {
  const flatOnly: ClauseSplit = { lifted: [], cards: null, flat: formatBody(goal) };
  const outer = liftTelescope(goal);
  const parts = conjunctsOf(outer.inner) ?? [outer.inner];
  const built = parts.map((p) => buildCard(p, 0));
  if (built.some((b) => b === null)) return flatOnly;
  const recon = outer.prefix + built.map((b) => b!.recon).join("∧") + outer.suffix;
  if (squash(recon) !== squash(goal)) return flatOnly;
  const cards = toViewCards(built.map((b) => b!.card), named);
  // A lone unconditional leaf is the flat rendering — no card chrome needed;
  // the lifted rows are still worth having.
  const lone = cards.length === 1 && cards[0].hyps.length === 0 && !cards[0].intro && !cards[0].sub;
  return {
    lifted: outer.hyps.flatMap(liftedRows),
    cards: lone ? null : cards,
    flat: lone ? cards[0].code! : [],
  };
}

/** Source lines kept as authored (indentation preserved), for a `where`
 *  block whose layout IS its structure. */
function rawLines(text: string): StmtLine[] {
  const lines = dedent(text).split("\n");
  return lines
    .filter((l) => l.trim().length > 0)
    .map((l) => ({ indent: Math.round((l.match(/^ */)![0].length) / 2), text: l.trim() }));
}

/** A definition's value side by how it is given (see `DefScan.body`). */
function splitDefBody(body: DefinitionScan["body"]): ClauseSplit {
  if (body === null) return { lifted: [], cards: null, flat: [] };
  if (body.kind === "value") return splitValue(body.text);
  if (body.kind === "where") {
    const fields = splitWhereFields(body.text);
    if (!fields) return { lifted: [], cards: null, flat: rawLines(body.text) };
    return {
      lifted: [],
      cards: fields.map((f, i) => ({ hyps: [], code: formatBody(`${f.head} := ${f.value}`), token: `⊢${i + 1}` })),
      flat: [],
    };
  }
  // Equation alternatives: one card per `| pattern => value`.
  const alts: string[] = [];
  for (const line of dedent(body.text).split("\n")) {
    if (/^\s*\|/.test(line) || alts.length === 0) alts.push(line.trim());
    else alts[alts.length - 1] += " " + line.trim();
  }
  return {
    lifted: [],
    cards: alts.map((a, i) => ({ hyps: [], code: formatBody(a), token: `⊢${i + 1}` })),
    flat: [],
  };
}

/** A definition's `:=` body: a run of `let` steps becomes rows, the final
 *  expression the leaf. Anything else is one leaf, line-broken by width. */
function splitValue(body: string): ClauseSplit {
  const lets = stripLetRun(body);
  if (lets) {
    return {
      lifted: [],
      cards: [{ hyps: lets.rows.flatMap(liftedRows), code: formatBody(lets.rest), token: "⊢ ⊢1" }],
      flat: [],
    };
  }
  return { lifted: [], cards: null, flat: formatBody(dedent(body)) };
}

// ---------------------------------------------------------------------------
// definitions
// ---------------------------------------------------------------------------

/** Names bound by a row, in order (`(x y : T)` → x, y; anonymous `[C]` → ""). */
function rowNames(r: BinderRow): string[] {
  return r.names ? r.names.split(/\s+/).filter(Boolean) : [""];
}

/**
 * Section-variable rows: the elaborated binders that PRECEDE the authored
 * telescope. The authored names are located as a contiguous run inside the
 * elaborated list (anonymous binders match anything); everything before that
 * run was introduced by `variable`. No match → nothing is prepended.
 */
function sectionRows(rows: StatementItem[], params: readonly LibParam[] | undefined): StatementItem[] {
  return splitParams(rows, params).section;
}

/** The elaborated binders around the authored telescope: those BEFORE it
 *  (section variables, as rows) and those AFTER it (binders of the type). */
/** How many of `trailing` `peelTypeBinders` would consume from `typeText`
 *  (rows may bind several names, so this counts binders, not rows). */
function countBound(trailing: readonly LibParam[], typeText: string): number {
  const peeled = peelTypeBinders(typeText, trailing);
  return peeled.rows.filter(isBinderRow).reduce((n, r) => n + (r.names ? rowNames(r).length : 1), 0);
}

function splitParams(
  rows: StatementItem[],
  params: readonly LibParam[] | undefined,
  typeText = "",
): { section: StatementItem[]; trailing: LibParam[] } {
  if (!params || params.length === 0) return { section: [], trailing: [] };
  const authored = rows.filter(isBinderRow).flatMap(rowNames);
  const matches = (k: number) =>
    authored.every((n, j) => {
      const p = params[k + j];
      // An authored anonymous binder (`[C]`) matches an elaborated anonymous
      // one; a NAMED authored binder must match by name — an elaborated
      // anonymous binder is never a wildcard for it, or `[inst] [inst_1]`
      // would absorb the first two named binders and hide section variables.
      return p !== undefined && (n === "" ? p.n === "" : p.n === n);
    });
  let k = -1;
  if (authored.length === 0) {
    // No authored binders: the elaborated list is section variables followed
    // by whatever the TYPE itself binds (`: ∀ n, …`, `: (k : ℕ) → …`). The
    // longest suffix the type text can account for is the type's; the rest
    // is the section's.
    let m = 0;
    if (typeText) {
      for (let cand = params.length; cand >= 1; cand--) {
        if (countBound(params.slice(params.length - cand), typeText) === cand) {
          m = cand;
          break;
        }
      }
    }
    k = params.length - m;
  } else {
    // Section variables precede the authored telescope, so when an anonymous
    // authored instance binder could match several elaborated `[inst]`s, the
    // LAST feasible position is the authored run (earlier ones are section
    // instances).
    for (let i = params.length - authored.length; i >= 0; i--) {
      if (matches(i)) {
        k = i;
        break;
      }
    }
  }
  if (k < 0) return { section: [], trailing: [] };
  const trailing = params.slice(k + authored.length);
  const out: StatementItem[] = [];
  for (const p of params.slice(0, k)) {
    if (!p.n) continue;
    out.push({
      kind: "binder",
      names: p.n,
      chip: "decl",
      body: formatBody(p.t),
      bracketKind: p.bi === "explicit" ? "explicit" : "implicit",
      origin: "section",
    });
  }
  return { section: out, trailing };
}

/**
 * A definition's TYPE may bind further parameters — `(k : ℕ) → k ≤ n → …`,
 * `∀ v : SV, SX v` — which Lean treats exactly like telescope binders (the
 * index's elaborated `params` lists them after the authored run). They become
 * parameter rows too, and the def row's type is what remains. `trailing` is the
 * elaborated binder list AFTER the authored telescope; peeling stops at the
 * first binder the text and the list disagree on.
 */
function peelTypeBinders(
  typeText: string,
  trailing: readonly LibParam[],
): { rows: StatementItem[]; type: string } {
  const rows: StatementItem[] = [];
  let t = typeText.trim();
  let i = 0;
  while (i < trailing.length) {
    if (t.startsWith("∀")) {
      const q = stripLeadingQuantifier(t);
      if (!q) break;
      const header = q.header.replace(/^∀/, "").trim();
      const groups: StatementItem[] = [];
      if (/^[({[⦃]/.test(header)) {
        let rest = header;
        while (rest) {
          const close = matchedCloseIndex(rest);
          const row = close > 0 ? parseBinderGroup(rest.slice(0, close + 1)) : null;
          if (!row) break;
          groups.push({ kind: "binder", ...row });
          rest = rest.slice(close + 1).trim();
        }
        if (rest) break;
      } else {
        const colon = topLevelColonIndex(header);
        const names = (colon >= 0 ? header.slice(0, colon) : header).trim();
        const ty = colon >= 0 ? header.slice(colon + 1).trim() : "";
        groups.push({ kind: "binder", names, chip: "decl", body: ty ? formatBody(ty) : [], bracketKind: "explicit" });
      }
      const bound = groups.flatMap((g) => (isBinderRow(g) ? rowNames(g) : []));
      const expect = trailing.slice(i, i + bound.length).map((p) => p.n);
      if (bound.length === 0 || bound.some((n, j) => expect[j] !== n)) break;
      rows.push(...groups);
      i += bound.length;
      t = q.rest.trim();
      continue;
    }
    const arrow = leadingImplicationIndex(t);
    if (arrow < 0) break;
    const head = t.slice(0, arrow).trim();
    const p = trailing[i];
    if (/^[({[⦃]/.test(head) && matchedCloseIndex(head) === head.length - 1) {
      // `(k : ℕ) →` / `(T C : Finset V) →` — a named Pi binder group
      const row = parseBinderGroup(head);
      if (!row) break;
      const bound = rowNames({ kind: "binder", ...row });
      const expect = trailing.slice(i, i + bound.length).map((q) => q.n);
      if (bound.some((n, j) => expect[j] !== n)) break;
      rows.push({ kind: "binder", ...row });
      i += bound.length;
    } else {
      // `k ≤ n →` — an anonymous premise becomes a hypothesis row; an anonymous
      // DATA arrow (`P.Ω → …`) stays in the type: a nameless data row reads
      // like a stray hypothesis, while `P.Ω → ValuesOn Y P.X` reads as intended.
      if (p.n !== "") break;
      const isPremise = classifyChip("", "explicit", head) === "hyp";
      // …unless a NAMED binder follows it in the type: rows must keep the
      // type's order, so the arrow is then shown as a nameless data row.
      const namedLater = trailing.slice(i + 1).some((q) => q.n !== "");
      if (!isPremise && !namedLater) break;
      rows.push({ kind: "binder", names: "", chip: isPremise ? "hyp" : "decl", body: formatBody(head), bracketKind: "explicit" });
      i += 1;
    }
    t = t.slice(arrow + 1).trim();
  }
  return { rows, type: t };
}

function defHead(name: string, rows: StatementItem[]): string {
  const args = rows
    .filter(isBinderRow)
    .filter((r) => r.bracketKind === "explicit" && r.names)
    .flatMap(rowNames);
  const leaf = name.split(".").pop() ?? name;
  return [leaf, ...args].join(" ");
}

// ---------------------------------------------------------------------------
// assembly
// ---------------------------------------------------------------------------

/** Attach each `/-- doc -/` comment row to the field it documents. */
function attachFieldDocs(items: StatementItem[]): StatementItem[] {
  const out: StatementItem[] = [];
  let pending: string | null = null;
  for (const it of items) {
    if (it.kind === "comment") {
      pending = pending ? `${pending} ${it.text}` : it.text;
      continue;
    }
    if (pending) it.doc = pending;
    pending = null;
    out.push(it);
  }
  return out;
}

function buildTheorem(rawSource: string, params: readonly LibParam[] | undefined): DeclView | null {
  const scan = scanTheoremSignature(rawSource);
  if (!scan) return null;
  const rows = groupRows(rawSource, scan);
  if (!rows) return null;
  const split = splitProposition(scan.conclusionText);
  return {
    role: "theorem",
    rows: mergeAttachedInstances([...sectionRows(rows, params), ...rows, ...split.lifted]),
    fields: null,
    defRow: null,
    cards: split.cards,
    flat: split.flat,
  };
}

function buildDefinition(
  rawSource: string,
  params: readonly LibParam[] | undefined,
  result: string | undefined,
): DeclView | null {
  const propScan = scanPropDefinitionSignature(rawSource);
  const def = scanDefinitionSignature(rawSource);
  if (!def) return null;
  const authored = groupRows(rawSource, def.scan);
  if (!authored) return null;
  const { section, trailing } = splitParams(authored, params, propScan ? "" : def.scan.conclusionText);
  const peeled = propScan || !def.scan.conclusionText ? { rows: [], type: def.scan.conclusionText } : peelTypeBinders(def.scan.conclusionText, trailing);
  // Type-level binders are shown as rows but, like lifted goal binders, are
  // not part of the authored telescope a docstring must cover.
  const typeRows = peeled.rows.map((r) => (r.kind === "binder" ? { ...r, origin: "lifted" as const } : r));
  const rows = [...section, ...authored, ...typeRows];
  const head = defHead(def.name, rows);
  if (propScan) {
    const split = splitProposition(propScan.conclusionText, true);
    return {
      role: "propdef",
      rows: mergeAttachedInstances([...rows, ...split.lifted]),
      fields: null,
      defRow: { head, type: [{ indent: 0, text: "Prop" }] },
      cards: split.cards,
      flat: split.flat,
    };
  }
  const value = splitDefBody(def.body);
  return {
    role: "definition",
    rows: mergeAttachedInstances(rows),
    fields: null,
    defRow: { head, type: formatBody(peeled.type || result || "") },
    cards: value.cards,
    flat: value.flat,
  };
}

function buildInstance(rawSource: string, params: readonly LibParam[] | undefined, leafName: string): DeclView | null {
  const inst = scanInstanceSignature(rawSource);
  if (!inst) return null;
  const authored = groupRows(rawSource, inst.scan);
  if (!authored) return null;
  const { section, trailing } = splitParams(authored, params, inst.scan.conclusionText);
  // `instance foo : ∀ sn, Fintype (swigΩ sn)` binds parameters in its type,
  // exactly as a definition may — same peeling, same `lifted` marking.
  const peeled = peelTypeBinders(inst.scan.conclusionText, trailing);
  const typeRows = peeled.rows.map((r) => (r.kind === "binder" ? { ...r, origin: "lifted" as const } : r));
  const rows = [...section, ...authored, ...typeRows];
  const head = defHead(inst.name || leafName, rows);
  const value: ClauseSplit = inst.body?.kind === "value" ? splitValue(inst.body.text) : splitDefBody(inst.body);
  return {
    role: "instance",
    rows: mergeAttachedInstances(rows),
    fields: null,
    defRow: { head, type: formatBody(peeled.type || inst.scan.conclusionText) },
    cards: value.cards,
    flat: value.flat,
  };
}

function buildInductive(rawSource: string, params: readonly LibParam[] | undefined, result: string | undefined): DeclView | null {
  const ind = scanInductiveSignature(rawSource);
  if (!ind) return null;
  const authored: StatementItem[] = [];
  let prevEnd = ind.telescopeStart;
  for (const g of ind.groups) {
    const comment = extractComment(rawSource.slice(prevEnd, g.start));
    if (comment) authored.push({ kind: "comment", text: comment });
    const row = parseBinderGroup(g.raw);
    if (!row) return null;
    authored.push({ kind: "binder", ...row });
    prevEnd = g.end;
  }
  const { section } = splitParams(authored, params);
  const rows = [...section, ...authored];
  const head = defHead(ind.name, rows);
  const ctors: StatementItem[] = ind.constructors.map((c) => ({
    kind: "binder",
    names: c.name,
    chip: "decl",
    body: c.sig ? formatBody(c.sig.replace(/^:\s*/, "")) : [],
    bracketKind: "explicit",
    ...(c.doc ? { doc: c.doc } : {}),
  }));
  const view: DeclView = {
    role: "inductive",
    rows: mergeAttachedInstances(rows),
    fields: ctors,
    defRow: { head, type: formatBody(ind.sort || result || "Type") },
    cards: null,
    flat: [],
  };
  if (ind.deriving) view.note = `deriving ${ind.deriving}`;
  return view;
}

function buildRecord(rawSource: string, params: readonly LibParam[] | undefined): DeclView | null {
  const rec = structureRecordSource(rawSource);
  if (!rec) return null;
  const assumption = isPropRecord(rawSource);
  return {
    role: assumption ? "assumption" : "record",
    rows: [...sectionRows(rec.rows.filter((r) => !(isBinderRow(r) && r.names === "extends")), params), ...rec.rows],
    fields: assumption ? attachFieldDocs(rec.fields ?? []) : rec.fields,
    defRow: null,
    cards: null,
    flat: [],
  };
}

/**
 * Structures a declaration's authored source (docstring stripped) by kind.
 * `params` / `result` are the index's elaborated binder list and result type,
 * used only for definitions (section variables; the type of an unannotated
 * `abbrev`). Returns `null` when the source is not confidently understood —
 * the caller keeps its flat rendering.
 */
export function buildDeclView(
  rawSource: string,
  kind: string,
  params?: readonly LibParam[],
  result?: string,
  /** The index's leaf name — the head of an anonymous instance's row. */
  leafName?: string,
): DeclView | null {
  switch (kind) {
    case "theorem":
    case "lemma":
      return buildTheorem(rawSource, params);
    case "def":
    case "abbrev":
      return buildDefinition(rawSource, params, result);
    case "structure":
    case "class":
      return buildRecord(rawSource, params);
    case "instance":
      return buildInstance(rawSource, params, leafName ?? "instance");
    case "inductive":
      return buildInductive(rawSource, params, result);
    default:
      return null;
  }
}

// ---------------------------------------------------------------------------
// linkification — one pass over every line, then redistributed
// ---------------------------------------------------------------------------

function bodyLines(b: StmtBody, out: StmtLine[]): void {
  if (Array.isArray(b)) {
    out.push(...b);
    return;
  }
  if (b.header) out.push(...b.header);
  for (const p of b.premises) out.push(...p);
  out.push(...b.conclusion);
}

function cardLines(c: ViewCard, out: StmtLine[]): void {
  for (const h of c.hyps) if (isBinderRow(h)) bodyLines(h.body, out);
  if (c.intro) out.push(...c.intro);
  if (c.code) bodyLines(c.code, out);
  for (const s of c.sub ?? []) cardLines(s, out);
}

/** Every binder-bound name in the view, so `linkifyStatement` treats them as
 *  local variables rather than library references. */
function boundNames(v: DeclView): string[] {
  const names: string[] = [];
  const fromRows = (items: StatementItem[]) => {
    for (const r of items) if (isBinderRow(r) && r.names) names.push(r.names);
  };
  fromRows(v.rows);
  if (v.fields) fromRows(v.fields);
  const walk = (c: ViewCard) => {
    fromRows(c.hyps);
    for (const s of c.sub ?? []) walk(s);
  };
  for (const c of v.cards ?? []) walk(c);
  return names;
}

const CELL_DELIM = " ";

/** Fills each line's `html` with declaration links (see `linkifyStructured`
 *  in leanStatement.ts for why the bound names are fed in as a preamble). */
export function linkifyDeclView(v: DeclView, lib: Library, base: string, selfNames?: Set<string>): void {
  const lines: StmtLine[] = [];
  for (const r of v.rows) if (isBinderRow(r)) bodyLines(r.body, lines);
  for (const r of v.fields ?? []) if (isBinderRow(r)) bodyLines(r.body, lines);
  if (v.defRow) bodyLines(v.defRow.type, lines);
  for (const c of v.cards ?? []) cardLines(c, lines);
  bodyLines(v.flat, lines);
  if (lines.length === 0) return;
  const preamble = boundNames(v)
    .map((n) => `${n} : `)
    .join(" ");
  const combined = [preamble, ...lines.map((l) => l.text)].join(CELL_DELIM);
  const html = linkifyStatement(combined, lib, base, selfNames);
  const parts = html.split(CELL_DELIM);
  lines.forEach((l, i) => {
    l.html = parts[i + 1] ?? l.text;
  });
}

/** Builds + linkifies in one call; `null` when structuring isn't confident. */
export function declViewAndLinkify(
  rawSource: string,
  kind: string,
  lib: Library,
  base: string,
  params?: readonly LibParam[],
  result?: string,
  selfNames?: Set<string>,
  leafName?: string,
): DeclView | null {
  const v = buildDeclView(rawSource, kind, params, result, leafName);
  if (!v) return null;
  linkifyDeclView(v, lib, base, selfNames);
  return v;
}

/** Whether the clause side has anything to render. */
export function hasClause(v: DeclView): boolean {
  return (v.cards !== null && v.cards.length > 0) || isChain(v.flat) || v.flat.length > 0;
}

/** The `∃`-headed / side-condition classification the drawer uses, exposed
 *  for the renderer: a leaf with no hyps, intro, or sub. */
export function isSideCondition(c: ViewCard): boolean {
  return c.hyps.length === 0 && !c.intro && !c.sub && c.code !== undefined;
}

/** The `⊢N` tokens the rendered clause side carries — the clauses a docstring's
 *  `[phrase](step:N)` may address. A flat (unsplit) clause is `⊢1`. */
export function numberedTokens(v: DeclView): Set<string> {
  const out = new Set<string>();
  const walk = (c: ViewCard) => {
    for (const t of c.token.split(" ")) if (/^⊢\d+$/.test(t)) out.add(t);
    for (const s of c.sub ?? []) walk(s);
  };
  for (const c of v.cards ?? []) walk(c);
  if (!v.cards && hasClause(v)) out.add("⊢1");
  if (v.role === "inductive") (v.fields ?? []).filter(isBinderRow).forEach((_, i) => out.add(`⊢${i + 1}`));
  return out;
}
