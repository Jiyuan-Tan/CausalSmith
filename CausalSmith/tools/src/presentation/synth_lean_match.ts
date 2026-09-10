// Lean-first resolution of the symbols P1's notation reviewer reports as undefined. Before any
// presentation-only definition is written, each symbol is looked up in the run's Lean: a symbol
// the Lean already realizes gets a definition RENDERED FROM that declaration (linked, judged
// against it, opened by the site) instead of a prose definition the writer reconstructs from
// usage — the same object would otherwise appear twice (an unlinked printed definition and an
// "auxiliary" Lean declaration nobody can reach from the statement).
//
// Two sources, both deterministic, zero-false-link:
// 1. `@realizes <sym>` tags (the scaffolder's own symbol↔decl assignment), compared at the
//    notation level (`realizedNotationKey`).
// 2. A def-like declaration whose name, as a concept key, EQUALS the symbol's text
//    (`\operatorname{summaryRadius}` ↔ `summaryRadius`, `\text{gap-scale domain}` ↔
//    `GapScaleDomain`), unique among the paper's modules. A plural/singular or synonym gap
//    resolves nothing — the symbol then goes to the definition writer (the honest state).
import type { SymbolCluster } from "../formalization/crosswalk.js";
import { realizedNotationKey } from "../formalization/crosswalk.js";

/** Def-like Lean kinds a definition may be homed by. Lemmas/theorems are proof helpers, never
 *  the formal object a definition introduces. */
const DEF_LIKE_KINDS = new Set(["def", "abbrev", "structure", "instance", "class", "inductive"]);

/** Minimum normalized-key length for a name match. Guards against trivial/ambiguous collisions
 *  (`mse`, `obs`) that a 2–3 char key would produce. */
const MIN_KEY_LEN = 6;

/** Normalize a title/symbol/decl-name to its comparison key: text-font wrappers keep their
 *  content, the rest of the LaTeX is dropped, and only lowercase alphanumerics remain.
 *  `\operatorname{summaryRadius}`, `Summary radius` and `summaryRadius` all key to
 *  `summaryradius`. */
export function conceptKey(raw: string): string {
  const prose = raw
    .replace(/\\(?:operatorname\*?|mathrm|mathsf|mathtt|text|textrm|textsf)\s*\{([^{}]*)\}/g, " $1 ")
    .replace(/\$[^$]*\$/g, " ") // inline $...$
    .replace(/\\\([\s\S]*?\\\)/g, " ") // inline \(...\)
    .replace(/\\\[[\s\S]*?\\\]/g, " ") // display \[...\]
    .replace(/\\[a-zA-Z]+/g, " "); // residual LaTeX commands
  return prose.toLowerCase().replace(/[^a-z0-9]/g, "");
}

/** The short (unqualified) name of a possibly dotted Lean decl name. */
export function shortDeclName(name: string): string {
  const i = name.lastIndexOf(".");
  return i < 0 ? name : name.slice(i + 1);
}

export interface DeclLoc {
  file: string;
  line: number;
  kind?: string;
}

/** One Lean declaration that defines one or more requested symbols (a structure realizes all of
 *  its fields' symbols at once, so they are defined together, journal style). `decl` is the key
 *  under which the module index lists the declaration. */
export interface SymbolLeanHome {
  decl: string;
  file: string;
  line: number;
  decl_kind: string;
  symbols: string[];
}

const isDefLike = (kind: string | undefined): boolean => kind !== undefined && DEF_LIKE_KINDS.has(kind);

/**
 * Resolve requested symbols to the Lean declarations that already define them. `homes` groups
 * the resolved symbols by declaration (input order preserved); `unresolved` are the symbols no
 * tag and no unique same-named def-like declaration covers — those go to the definition writer.
 */
export function resolveSymbolHomes(
  symbols: readonly string[],
  clusters: readonly SymbolCluster[],
  moduleDecls: ReadonlyMap<string, DeclLoc>,
  /** Declarations some paper environment already presents (short or qualified names): a symbol
   *  they define is never given a second definition — it is left unresolved for the caller. */
  presented: ReadonlySet<string> = new Set(),
): { homes: SymbolLeanHome[]; unresolved: string[]; presentedBy: Map<string, string> } {
  const homes = new Map<string, SymbolLeanHome>();
  const unresolved: string[] = [];
  const presentedBy = new Map<string, string>();
  const presentedShort = new Set([...presented].map(shortDeclName));
  const claim = (symbol: string, decl: string, loc: DeclLoc): void => {
    if (presentedShort.has(shortDeclName(decl))) {
      presentedBy.set(symbol, decl);
      unresolved.push(symbol);
      return;
    }
    const home = homes.get(decl) ?? { decl, file: loc.file, line: loc.line, decl_kind: loc.kind ?? "def", symbols: [] };
    home.symbols.push(symbol);
    homes.set(decl, home);
  };
  for (const symbol of symbols) {
    // A use with arguments (`\Gamma(\mathcal M;p)`) names the family `\Gamma`.
    const stem = symbol.trim().replace(/\s*\([^()]*\)\s*$/, "");
    const tagged = realizedHome(stem, clusters, moduleDecls);
    if (tagged) {
      claim(symbol, tagged.decl, tagged.loc);
      continue;
    }
    const named = namedHome(conceptKey(stem), moduleDecls);
    if (named) claim(symbol, named.decl, named.loc);
    else unresolved.push(symbol);
  }
  return { homes: [...homes.values()], unresolved, presentedBy };
}

/** The first indexed def-like member of the `@realizes` cluster whose symbol spells the requested
 *  one. Clusters are case-sensitive (`pi` and `Pi` are different symbols), so the comparison keeps
 *  case; a member the module index cannot name is skipped (P1's judge and P4 resolve declarations
 *  by the index's own name). */
function realizedHome(
  symbol: string,
  clusters: readonly SymbolCluster[],
  moduleDecls: ReadonlyMap<string, DeclLoc>,
): { decl: string; loc: DeclLoc } | null {
  const key = realizedNotationKey(symbol, { preserveCase: true });
  if (!key) return null;
  const matching = clusters.filter((c) => realizedNotationKey(c.symbol, { preserveCase: true }) === key);
  if (matching.length !== 1) return null; // two tags spelling one symbol are ambiguous, never first-wins
  const cluster = matching[0];
  for (const m of cluster.members) {
    if (!isDefLike(m.declKind)) continue;
    const indexed = indexedDecl(m.decl, moduleDecls);
    if (indexed) return indexed;
  }
  return null;
}

/** The unique def-like declaration whose short name keys to `key`. The index may list one
 *  declaration under its short and its qualified name (one location, the qualified key wins);
 *  two declarations at different locations sharing the key are ambiguous. */
function namedHome(key: string, moduleDecls: ReadonlyMap<string, DeclLoc>): { decl: string; loc: DeclLoc } | null {
  if (key.length < MIN_KEY_LEN) return null;
  const byLocation = new Map<string, { decl: string; loc: DeclLoc }>();
  for (const [name, loc] of moduleDecls) {
    if (!isDefLike(loc.kind) || conceptKey(shortDeclName(name)) !== key) continue;
    const at = `${loc.file}:${loc.line}`;
    const prior = byLocation.get(at);
    if (!prior || name.length > prior.decl.length) byLocation.set(at, { decl: name, loc });
  }
  return byLocation.size === 1 ? [...byLocation.values()][0] : null;
}

/** A cluster member (the header name as written, usually short) under the module index's longest
 *  key for that declaration — the qualified name when the index has it, which is the name the
 *  judge's resolver and P4 look up. Null when the index does not name it unambiguously. */
function indexedDecl(decl: string, moduleDecls: ReadonlyMap<string, DeclLoc>): { decl: string; loc: DeclLoc } | null {
  const short = shortDeclName(decl);
  const byLocation = new Map<string, { decl: string; loc: DeclLoc }>();
  for (const [name, loc] of moduleDecls) {
    if (shortDeclName(name) !== short) continue;
    const at = `${loc.file}:${loc.line}`;
    const prior = byLocation.get(at);
    if (!prior || name.length > prior.decl.length) byLocation.set(at, { decl: name, loc });
  }
  const exact = moduleDecls.get(decl);
  const at = exact ? `${exact.file}:${exact.line}` : null;
  if (at) return byLocation.get(at) ?? { decl, loc: exact! };
  return byLocation.size === 1 ? [...byLocation.values()][0] : null;
}
