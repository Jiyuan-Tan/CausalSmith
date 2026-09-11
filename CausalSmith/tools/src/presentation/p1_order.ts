// P1's ONE notion of order — the paper order — computed deterministically and never judged
// by a model. The outline's per-section `objs` lines give the reader's order of the graph
// environments; each synthesized definition is inserted before its first user; then
// explicit prerequisites are placed before their consumers. P1 is
// the only judge of definition order: P2 lays sections out in this order and P3/P4 merely assert
// the layer was not reordered (`lintEnvOrder`), so nothing downstream re-judges what P1 settled.
import type { P1Env } from "./p1_loop.js";
import { parseOutline, type Outline } from "./stage_util.js";
import { stripTexComments } from "../shared/tex_text.js";
import { usesSymbolUndecorated, type LintProblem } from "./tex_anchors.js";

export const isSynthId = (id: string): boolean => /^synth_\d+$/.test(id);

/** Graph environments in the outline's reader order (sections in order, `objs` within each).
 *  Synth ids in the outline are ignored — synths are placed by `insertSynths`. An env the outline
 *  does not place (cannot happen after `validateOutline`, kept fail-safe) is appended in input order. */
export function paperOrder(outline: Outline, graphEnvs: readonly P1Env[]): P1Env[] {
  const byId = new Map(graphEnvs.map((e) => [e.id, e] as const));
  const out: P1Env[] = [];
  const seen = new Set<string>();
  for (const s of outline.sections) {
    for (const id of s.objs) {
      const e = byId.get(id);
      if (e && !seen.has(id)) {
        out.push(e);
        seen.add(id);
      }
    }
  }
  for (const e of graphEnvs) if (!seen.has(e.id)) out.push(e);
  return out;
}

const textOf = (e: P1Env, titleById: ReadonlyMap<string, string>): string =>
  `${titleById.get(e.id) ?? ""} ${e.body}`;

/** A symbol as requested (`\Gamma_{x,y}(\mathcal M;p)`) and its family stem (`\Gamma_{x,y}`): a use
 *  of the family with other arguments is still a use of the synthesized definition. */
export function symbolCandidates(symbol: string): string[] {
  const stem = symbol.trim().replace(/\s*\([^()]*\)\s*$/, "");
  return stem && stem !== symbol.trim() ? [symbol, stem] : [symbol];
}
const usesAny = (text: string, symbols: readonly string[]): boolean =>
  symbols.some((sym) => symbolCandidates(sym).some((c) => usesSymbolUndecorated(text, c)));

/** Synths ordered so that a synth whose body mentions another synth's symbol comes after it
 *  (topological by mention; a mention cycle is broken by numeric id, never thrown — mutual
 *  mention between two definitions is ordinary prose; the repair reports it once). */
export function sortSynthsByMention(
  synths: readonly P1Env[],
  symbolsBySynthId: ReadonlyMap<string, readonly string[]>,
  titleById: ReadonlyMap<string, string>,
): P1Env[] {
  const num = (e: P1Env) => Number(e.id.slice("synth_".length));
  const prereqs = new Map(synths.map((s) => [s.id, new Set<string>()] as const));
  for (const provider of synths) {
    const provided = symbolsBySynthId.get(provider.id) ?? [];
    for (const consumer of synths) {
      if (provider.id === consumer.id) continue;
      if (usesAny(textOf(consumer, titleById), provided)) {
        prereqs.get(consumer.id)!.add(provider.id);
      }
    }
  }
  const out: P1Env[] = [];
  const done = new Set<string>();
  const pending = [...synths].sort((a, b) => num(a) - num(b));
  while (pending.length > 0) {
    const i = pending.findIndex((s) => [...prereqs.get(s.id)!].every((p) => done.has(p)));
    const next = pending.splice(i >= 0 ? i : 0, 1)[0]; // i < 0: a cycle — take the lowest id
    out.push(next);
    done.add(next.id);
  }
  return out;
}

/** Insert each synthesized definition immediately before the first environment that uses any
 *  of its symbols (title or body). A synth nothing visibly uses is ballast, or its symbol is
 *  spelled differently at the use site: it goes at the END of the setup region (before the first
 *  result) and is reported through `orphans`, never at the head of the paper — printed first it
 *  drags its own providers to the front and the paper opens with machinery nothing has motivated.
 *  Consumers are inserted before their providers, so a provider's first-use scan finds its
 *  consumer in place and lands right before it. */
export function insertSynths(
  ordered: readonly P1Env[],
  synths: readonly P1Env[],
  symbolsBySynthId: ReadonlyMap<string, readonly string[]>,
  titleById: ReadonlyMap<string, string>,
  orphans?: Set<string>,
): P1Env[] {
  const out = [...ordered];
  for (const synth of sortSynthsByMention(synths, symbolsBySynthId, titleById).reverse()) {
    const symbols = symbolsBySynthId.get(synth.id) ?? [];
    const firstUse = out.findIndex((e) => e.id !== synth.id && usesAny(textOf(e, titleById), symbols));
    if (firstUse >= 0) { out.splice(firstUse, 0, synth); continue; }
    orphans?.add(synth.id);
    const firstResult = out.findIndex((e) => !movable(e) && !isSynthId(e.id));
    out.splice(firstResult >= 0 ? firstResult : out.length, 0, synth);
  }
  return out;
}

/** Definitions and assumptions precede explicit consumers. Supporting results retain their
 * planned homes: a mathematical dependency does not require printing its proof apparatus first. */
const movable = (e: P1Env): boolean =>
  e.env === "definitionv" || e.env === "algorithmv" || e.env === "assumptionv";

/** Solve prerequisites from explicit graph dependencies and paper references. A coincidentally
 * shared variable spelling is not evidence that two environments refer to the same object.
 * Synthesized definitions still carry their own symbol-use constraints. The stable solve pulls
 * prerequisites forward from planned homes and reports cycles without inventing dependencies. */
export function repairDefinitionOrder(
  ordered: readonly P1Env[],
  dependencies: ReadonlyMap<string, ReadonlySet<string>>,
  titleById: ReadonlyMap<string, string>,
  symbolsBySynthId: ReadonlyMap<string, readonly string[]>,
): { envs: P1Env[]; problems: LintProblem[] } {
  const index = new Map(ordered.map((e, i) => [e.id, i] as const));
  const envById = new Map(ordered.map((e) => [e.id, e] as const));
  type Constraint = { symbol: string; tableHome: string; homes: string[]; user: string };
  const constraints: Constraint[] = [];
  for (const e of ordered) {
    const refs = new Set(dependencies.get(e.id));
    // A synthesized definition's cross-references are prose ("used in …"), not prerequisites: a
    // fresh synthesis has opened with a \cref to every object in the paper, and treating those as
    // dependencies hoisted ~30 environments and emptied whole sections (twice, live). Its real
    // prerequisites are the homes of the symbols its body uses, handled below.
    if (!isSynthId(e.id)) {
      for (const m of stripTexComments(e.body).matchAll(/\\(?:Cref|cref|ref)\{([^}]+)\}/g)) {
        for (const label of m[1].split(",").map((s) => s.trim())) {
          if (label.startsWith("obj:")) refs.add(label.slice(4));
        }
      }
    }
    for (const home of [...refs].filter((id) => id !== e.id && index.has(id) && movable(envById.get(id)!)).sort((a, b) => index.get(a)! - index.get(b)!)) {
      constraints.push({ symbol: home, tableHome: home, homes: [home], user: e.id });
    }
  }
  for (const s of ordered) {
    if (!isSynthId(s.id)) continue;
    for (const symbol of symbolsBySynthId.get(s.id) ?? []) {
      for (const e of ordered) {
        if (e.id !== s.id && usesAny(textOf(e, titleById), [symbol])) constraints.push({ symbol, tableHome: s.id, homes: [s.id], user: e.id });
      }
    }
  }
  const byUser = new Map<string, Constraint[]>();
  for (const c of constraints) if (c.homes.length > 0) (byUser.get(c.user) ?? byUser.set(c.user, []).get(c.user)!).push(c);

  const done = new Set<string>();
  const onStack = new Set<string>();
  const out: P1Env[] = [];
  const dropped: Constraint[] = [];
  const pending = (c: Constraint) => c.homes.filter((h) => !done.has(h));
  /** Whether placing `x` requires `target` to be placed first: `x` has a constraint every
   *  remaining home of which (transitively) needs `target`. */
  const needs = (x: string, target: string, memo = new Map<string, boolean>()): boolean => {
    if (x === target) return true;
    const known = memo.get(x);
    if (known !== undefined) return known;
    memo.set(x, false); // in progress: a cycle back to x adds nothing to this search
    const result = (byUser.get(x) ?? []).some((c) => {
      const hs = pending(c);
      return hs.length > 0 && hs.every((h) => needs(h, target, memo));
    });
    memo.set(x, result);
    return result;
  };
  const place = (u: string): void => {
    if (done.has(u)) return;
    onStack.add(u);
    for (const c of byUser.get(u) ?? []) {
      if (c.homes.some((h) => done.has(h))) continue;
      const home = c.homes.find((h) => !onStack.has(h) && !needs(h, u));
      if (home === undefined) dropped.push(c);
      else place(home);
    }
    onStack.delete(u);
    done.add(u);
    out.push(envById.get(u)!);
  };
  for (const e of ordered) place(e.id);

  const problems: LintProblem[] = [];
  // One advisory per (home, user) pair, listing every symbol left violated between them.
  const droppedByPair = new Map<string, Constraint[]>();
  for (const c of dropped) (droppedByPair.get(`${c.tableHome}|${c.user}`) ?? droppedByPair.set(`${c.tableHome}|${c.user}`, []).get(`${c.tableHome}|${c.user}`)!).push(c);
  for (const cs of droppedByPair.values()) {
    const { tableHome, user } = cs[0];
    const symbols = [...new Set(cs.map((c) => c.symbol))].join(", ");
    const pair = [tableHome, user].sort().join(" ↔ ");
    problems.push({
      gate: "notation-mutual-definition",
      objId: user,
      detail: `${pair}: cyclic prerequisites (${symbols} used in ${user} before ${tableHome}); ` +
        `no order satisfies every dependency. Check the graph edges and paper references`,
    });
  }
  return { envs: out, problems };
}

/**
 * Section assignment for a repaired flat order. A graph env keeps its outline section unless a
 * repair moved it earlier, in which case it takes the section of the env now following it; a
 * synth takes the section of the next graph env. Sections are then monotone along the order, so
 * the outline's `objs` lines are exactly this order partitioned by section.
 */
export function sectionObjs(outline: Outline, ordered: readonly P1Env[]): Map<string, string[]> {
  const names = outline.sections.map((s) => s.name);
  const origIndex = new Map<string, number>();
  outline.sections.forEach((s, i) => { for (const id of s.objs) if (!origIndex.has(id)) origIndex.set(id, i); });
  const firstWithObjs = outline.sections.findIndex((s) => s.objs.length > 0);
  const fallback = firstWithObjs >= 0 ? firstWithObjs : 0;
  const sec = new Array<number | undefined>(ordered.length);
  // Right to left: a graph env takes min(own section, section of the next graph env) — a
  // repair only ever moves an env EARLIER, so `own` is too late exactly when it exceeds what
  // follows; a synth takes the section of the next graph env.
  let following: number | undefined;
  for (let i = ordered.length - 1; i >= 0; i--) {
    const own = isSynthId(ordered[i].id) ? undefined : origIndex.get(ordered[i].id);
    if (own !== undefined) {
      sec[i] = following === undefined ? own : Math.min(own, following);
      following = sec[i];
    } else {
      sec[i] = following;
    }
  }
  // Trailing synths (nothing graph-backed follows them) join the preceding env's section.
  for (let i = 0; i < ordered.length; i++) sec[i] ??= i > 0 ? sec[i - 1] : fallback;
  const out = new Map<string, string[]>(names.map((n) => [n, []]));
  ordered.forEach((e, i) => out.get(names[sec[i]!])!.push(e.id));
  return out;
}

/** Recover the planner's order before each P1 entry or replan. The resolved layout must never
 * become the next solve's starting point: otherwise a hoisted prerequisite cannot return home. */
export function outlineForPlanning(outlineMd: string): string {
  const outline = parseOutline(outlineMd);
  if (!outline.sections.some((s) => s.homeObjs !== undefined)) return outlineMd;
  const homes = new Map(outline.sections.map((s) => [s.name, s.homeObjs ?? s.objs]));
  return rewriteOutlineObjs(outlineMd, homes).replace(/^home_objs:[^\n]*(?:\n|$)/gm, "").trimEnd();
}

/** Rewrite every section's `objs:` line from `objsBySection` (a section with no envs reads
 *  `objs: none`; a section lacking the line gets one after its heading). Everything else in the
 *  outline is byte-preserved. P1 also records the planner homes before replacing its layout. */
export function rewriteOutlineObjs(
  outlineMd: string, objsBySection: ReadonlyMap<string, readonly string[]>,
  homeObjsBySection?: ReadonlyMap<string, readonly string[]>,
): string {
  const lines = outlineMd.split("\n");
  const out: string[] = [];
  let section: string | null = null;
  let wrote = false;
  let wroteHomes = false;
  const homeLine = (name: string) => `home_objs: ${homeObjsBySection?.get(name)?.join(", ") || "none"}`;
  const objsLine = (name: string) => {
    const ids = objsBySection.get(name) ?? [];
    return `objs: ${ids.length > 0 ? ids.join(", ") : "none"}`;
  };
  const flush = () => {
    if (section !== null && !wrote) out.push(objsLine(section));
    if (section !== null && homeObjsBySection && !wroteHomes) out.push(homeLine(section));
  };
  for (const line of lines) {
    const heading = line.match(/^## section:\s*(.+)$/);
    if (heading || /^# /.test(line)) {
      flush();
      section = heading ? heading[1].trim() : null;
      wrote = false;
      wroteHomes = false;
      out.push(line);
      continue;
    }
    if (section !== null && homeObjsBySection && /^home_objs:/.test(line)) {
      if (!wroteHomes) out.push(homeLine(section));
      wroteHomes = true;
      continue;
    }
    if (section !== null && /^objs:\s*/.test(line)) {
      out.push(objsLine(section));
      wrote = true;
      continue;
    }
    out.push(line);
  }
  flush();
  return out.join("\n");
}
