import { createHash } from "node:crypto";
import { extractBalancedEnv, stripTexComments } from "../shared/tex_text.js";

/**
 * Parser + linter for obj_id-anchored formal environments in paper tex.
 * The anchor chain's enforcement point: every formal environment must carry a
 * crosswalk obj_id, and after the P1 freeze its body must not drift.
 */

export interface AnchoredEnv {
  env: "theoremv" | "assumptionv" | "lemmav" | "definitionv" | "citedv" | "propositionv" | "remarkv" | "algorithmv";
  obj_id: string;
  title: string | null;
  body: string;
  order: number; // appearance order, used for paper numbering ("Theorem 2")
}

export interface LintProblem {
  gate: string;
  detail: string;
  /** The environment this problem is attributable to (for the readability revise loop). */
  objId?: string;
}

const ENV_BEGIN_RE =
  /\\begin\{(theoremv|assumptionv|lemmav|definitionv|citedv|propositionv|remarkv|algorithmv)\}\{([^}]+)\}/g;
const BARE_RE = /\\begin\{(theorem|assumption|lemma|definition|proposition|corollary|algorithm)\}/g;

interface EnvMatch extends AnchoredEnv {
  scopeMarked: boolean;
  start: number;
  bodyStart: number;
  bodyEnd: number;
  end: number;
  raw: string;
}

/** Read a LaTeX optional argument `[…]` starting at `pos` (bracket-balanced, `\[`/`\]` escaped).
 *  Returns `{title: null, end: pos}` when there is none. Shared with the proof-citation parser so
 *  `\begin{proof}[Proof of \cref{obj:X}]` heads are read by the same code as env titles. */
export function readOptionalTitle(tex: string, pos: number): { title: string | null; end: number } {
  if (tex[pos] !== "[") return { title: null, end: pos };
  let depth = 1;
  for (let i = pos + 1; i < tex.length; i++) {
    if (tex[i] === "\\") {
      i++; // why: escaped brackets in titles are display text, not delimiters.
    } else if (tex[i] === "[") {
      depth++;
    } else if (tex[i] === "]") {
      depth--;
      if (depth === 0) return { title: tex.slice(pos + 1, i), end: i + 1 };
    }
  }
  return { title: null, end: pos };
}

function scanAnchoredEnvs(tex: string): EnvMatch[] {
  const out: EnvMatch[] = [];
  let order = 0;
  ENV_BEGIN_RE.lastIndex = 0;
  let m: RegExpExecArray | null;
  while ((m = ENV_BEGIN_RE.exec(tex))) {
    // A commented-out `% \begin{…}` is not an environment: scanning it swallows the text up to
    // the next real `\end`, and every consumer (normalize, reorder, lint) then corrupts the section.
    const lineStart = tex.lastIndexOf("\n", m.index) + 1;
    if (/(?<!\\)(?:\\\\)*%/.test(tex.slice(lineStart, m.index))) continue; // an unescaped % earlier on the line
    const env = m[1] as AnchoredEnv["env"];
    const afterId = ENV_BEGIN_RE.lastIndex;
    const title = readOptionalTitle(tex, afterId);
    // A star after the optional title is presentation metadata: the environment macro places a
    // generated verification-footnote mark in the theorem heading. It is deliberately excluded
    // from the parsed/frozen body, just like the obj-id and title.
    const scopeMarked = tex[title.end] === "*";
    const bodyStart = title.end + (scopeMarked ? 1 : 0);
    const endTag = `\\end{${env}}`;
    const bodyEnd = tex.indexOf(endTag, bodyStart);
    if (bodyEnd < 0) continue;
    const end = bodyEnd + endTag.length;
    out.push({
      env,
      obj_id: m[2],
      title: title.title,
      body: tex.slice(bodyStart, bodyEnd),
      order: order++,
      scopeMarked,
      start: m.index,
      bodyStart,
      bodyEnd,
      end,
      raw: tex.slice(m.index, end),
    });
    ENV_BEGIN_RE.lastIndex = end;
  }
  return out;
}

function replaceAnchoredEnvs(tex: string, f: (e: EnvMatch) => string): string {
  const envs = scanAnchoredEnvs(tex);
  let out = tex;
  for (let i = envs.length - 1; i >= 0; i--) out = out.slice(0, envs[i].start) + f(envs[i]) + out.slice(envs[i].end);
  return out;
}

/** Append deterministic material immediately after selected anchored environments. */
export function appendAfterAnchoredEnvs(tex: string, suffixById: Map<string, string>): string {
  return replaceAnchoredEnvs(tex, (e) => {
    const suffix = suffixById.get(e.obj_id);
    return suffix ? `${e.raw}\n${suffix}` : e.raw;
  });
}

/** Ensure exactly the selected anchored environments carry the generated heading-footnote mark. */
export function normalizeAnchoredEnvScopeMarkers(tex: string, markedIds: Set<string>): string {
  return replaceAnchoredEnvs(tex, (e) => {
    const markerStart = e.bodyStart - e.start - (e.scopeMarked ? 1 : 0);
    const afterMarker = markerStart + (e.scopeMarked ? 1 : 0);
    return `${e.raw.slice(0, markerStart)}${markedIds.has(e.obj_id) ? "*" : ""}${e.raw.slice(afterMarker)}`;
  });
}

function stripAnchoredEnvBlocks(tex: string): string {
  return replaceAnchoredEnvs(tex, () => " ");
}

const PROSE_HEADING_RE = /\\(section|subsection|subsubsection)\*?\{([^}]*)\}/g;
const LIMITATION_HEADING_RE = /\b(?:limitations?|future work|future research|open questions?)\b/i;

/** Mask sections where explicit non-coverage statements are legitimate reader-facing content. */
function maskLimitationSections(tex: string): string {
  const headings: { start: number; level: number; title: string }[] = [];
  PROSE_HEADING_RE.lastIndex = 0;
  for (let m = PROSE_HEADING_RE.exec(tex); m; m = PROSE_HEADING_RE.exec(tex)) {
    headings.push({
      start: m.index,
      level: m[1] === "section" ? 1 : m[1] === "subsection" ? 2 : 3,
      title: m[2],
    });
  }
  const chars = tex.split(""); // preserve UTF-16 offsets reported by RegExp.index
  for (let i = 0; i < headings.length; i++) {
    const h = headings[i];
    if (!LIMITATION_HEADING_RE.test(h.title)) continue;
    const next = headings.slice(i + 1).find((x) => x.level <= h.level);
    const end = next?.start ?? tex.length;
    for (let j = h.start; j < end; j++) if (chars[j] !== "\n" && chars[j] !== "\r") chars[j] = " ";
  }
  return chars.join("");
}

const CONTRIBUTION_SUBJECT =
  "(?:this|the)\\s+(?:paper|work|article|study|analysis|result|theorem|lemma|bound|construction|method|approach|estimator|criterion|comparison|contribution|framework|rate|term|object|scope|target)|" +
  "our\\s+(?:paper|work|study|analysis|result|theorem|bound|construction|method|approach|estimator|contribution|framework)|we";
const NEGATIVE_CONTRIBUTION_RE = [
  new RegExp(`\\b(?:${CONTRIBUTION_SUBJECT})\\s+(?:do(?:es)?|is|are|has|have|can|could|will|would)\\s+not\\b`, "gi"),
  new RegExp(`\\b(?:${CONTRIBUTION_SUBJECT})\\s+(?:provide|offer|give|make|claim|establish|prove|derive|characterize|address|attempt|pursue)s?\\s+no\\b`, "gi"),
  /\b(?:this|it)\s+(?:is|was|are|were)\s+not\b/gi,
  /\b(?:the|these|our)\s+(?:results?|analysis|method|approach|construction|criterion|comparison|contribution|framework|rate|term|object|scope|target)\s+(?:is|are|was|were)\b[^.!?\n]{0,120},\s*not\b/gi,
  /\bno\s+(?:new\s+)?(?:estimator|test|procedure|algorithm|inference|standard errors?|finite-sample result|identification theorem|optimality claim)\s+(?:is|are|was|were)\s+(?:provided|proposed|proved|established|derived|developed|claimed)\b/gi,
  /\b(?:the|a|one)\s+(?:(?:key|main|important|central|major|primary)\s+)?(?:caveat|limitation|shortcoming|weakness|restriction)\s+(?:is|was|comes?\s+from|concerns?|lies?\s+in)\b/gi,
  /\b(?:the|these|our)\s+(?:results?|guarantees?|conclusions?|claims?|rates?|bounds?)\s+(?:hold|apply|are\s+(?:proved|shown|established|available))\s+only\b/gi,
  /\b(?:the|this|our)\s+(?:result|guarantee|claim|rate|bound|analysis|construction|method|estimator|schedule|design)\s+(?:is|was)\s+only\s+(?:proved|shown|established|derived|available)\b/gi,
  /\b(?:left|remains?|is|are|was|were)\s+(?:as\s+)?(?:an?\s+)?(?:open|unresolved)\s+(?:design\s+|research\s+)?(?:question|problem|issue|frontier)\b/gi,
  /\b(?:open|unresolved)\s+(?:design\s+|research\s+)?(?:question|problem|issue|frontier)\b/gi,
];

const OPEN_QUESTION_OBJECT_RE = /(?:\\(?:[cC]ref|ref)\{obj:oeq:[^}]+\}|\\label\{obj:oeq:[^}]+\}|\bobj:oeq:[A-Za-z0-9:_-]+)/gi;
const OPEN_QUESTION_DISCLOSURE_RE = /\b(?:open|unresolved)\s+(?:design\s+|research\s+)?(?:question|problem|issue|frontier)\b/i;

function isLinkedOpenQuestionDisclosure(prose: string, matchIndex: number, matchText: string): boolean {
  if (!OPEN_QUESTION_DISCLOSURE_RE.test(matchText)) return false;
  const boundary = Math.max(
    prose.lastIndexOf("\n", matchIndex),
    prose.lastIndexOf(".", matchIndex),
    prose.lastIndexOf(";", matchIndex),
    prose.lastIndexOf("!", matchIndex),
    prose.lastIndexOf("?", matchIndex),
  );
  const prefix = prose.slice(boundary + 1, matchIndex);
  const refs = [...prefix.matchAll(OPEN_QUESTION_OBJECT_RE)];
  const ref = refs.at(-1);
  if (!ref || ref.index === undefined) return false;
  const subject = prefix.slice(0, ref.index);
  const subjectParts = /^\s*(?:the|an?)\s+(?:(.*?)\s+)?(?:item|object|question|problem|frontier)\s+(?:in|at)\s*$/i.exec(subject);
  const refId = /obj:oeq:([^}]+)/i.exec(ref[0])?.[1] ?? "";
  const normalizeName = (value: string): string => value.toLowerCase().replace(/[^a-z0-9]+/g, " ").trim();
  const descriptor = subjectParts?.[1];
  const linkedSubject = /^\s*$/.test(subject)
    || (subjectParts !== null && (descriptor === undefined || normalizeName(descriptor) === normalizeName(refId)));
  if (!linkedSubject) return false;
  const bridge = prefix.slice(ref.index + ref[0].length);
  const disclosureAt = matchText.search(OPEN_QUESTION_DISCLOSURE_RE);
  const relation = bridge + matchText.slice(0, Math.max(0, disclosureAt));
  return /^\s*(?:(?:is|are|was|were)\s+(?:recorded|described|stated|posed|identified|listed|marked|treated|left)\s+as|(?:recorded|described|stated|posed|identified|listed|marked|treated|left)\s+as|remains?|stays?|is|are|was|were)\s+(?:an?\s+)?$/i.test(relation);
}

/**
 * Reader-facing contribution prose should lead with delivered results. Negative scope framing is
 * allowed only in explicitly labelled limitations/future-work sections. Frozen statements, proofs,
 * and generated verification disclosures are excluded because their negation can be mathematical or
 * mechanically required rather than editorial framing.
 */
export function lintNegativeContributionFraming(tex: string): LintProblem[] {
  let prose = maskLimitationSections(tex);
  prose = stripAnchoredEnvBlocks(prose)
    .replace(/% CAUSALSMITH-CITED-SCOPE-BEGIN[^\n]*[\s\S]*?% CAUSALSMITH-CITED-SCOPE-END[^\n]*/g, " ");
  // Balanced proof removal (a lazy regex left the tail of a proof containing a
  // nested `\begin{proof}[Proof of Claim 1]` in the linted prose), then a
  // parity-aware comment strip (`\\%` after a row break IS a comment).
  for (let block = extractBalancedEnv(prose, "proof"); block !== null; block = extractBalancedEnv(prose, "proof")) {
    prose = prose.replace(block, () => " ");
  }
  prose = stripTexComments(prose);
  const hits = new Map<number, LintProblem>();
  for (const re of NEGATIVE_CONTRIBUTION_RE) {
    re.lastIndex = 0;
    for (let m = re.exec(prose); m; m = re.exec(prose)) {
      const left = Math.max(prose.lastIndexOf("\n", m.index), prose.lastIndexOf(". ", m.index)) + 1;
      const period = prose.indexOf(". ", m.index + m[0].length);
      const newline = prose.indexOf("\n", m.index + m[0].length);
      const candidates = [period < 0 ? prose.length : period + 1, newline < 0 ? prose.length : newline];
      const right = Math.min(...candidates.filter((x) => x >= m.index));
      const excerpt = prose.slice(left, right).replace(/\s+/g, " ").trim().slice(0, 320);
      // An explicitly linked OEQ is a delivered disclosure, not contribution-minimizing prose.
      // Require a direct disclosure relation so a nearby OEQ reference cannot hide a different claim.
      if (isLinkedOpenQuestionDisclosure(prose, m.index, m[0])) continue;
      const line = prose.slice(0, m.index).split("\n").length;
      hits.set(left, {
        gate: "negative-contribution-framing",
        detail: `line ${line}: "${excerpt}" — state the delivered contribution/scope affirmatively, or move genuine non-coverage to an explicitly titled Limitations/Future Work/Open Questions section`,
      });
    }
  }
  return [...hits.values()];
}

export function parseAnchoredEnvs(tex: string): AnchoredEnv[] {
  return scanAnchoredEnvs(tex).map(({ env, obj_id, title, body, order }) => ({ env, obj_id, title, body, order }));
}

function atSentenceStart(source: string, offset: number): boolean {
  const prior = source.slice(0, offset).trimEnd();
  return prior.length === 0 || /[.!?]\s*$/.test(prior);
}

/** One-time-safe canonicalization used before authored text is frozen or emitted. It removes a
 * manually asserted reference kind and upgrades every legacy `\ref` command to target-typed
 * cleveref. Running it repeatedly is idempotent; label ids and mathematical content are unchanged. */
export function normalizeCrefs(tex: string): string {
  let out = tex.replace(
    /\b(?:Appendix|Appendices|Chapters?|Sections?|Figures?|Tables?|Equations?|Theorems?|Lemmas?|Definitions?|Assumptions?|Propositions?|Remarks?|Algorithms?|Cited results?)\s*~?\s*\\(?:Cref|cref|autoref|eqref|ref)\{([^}]+)\}/gi,
    (_whole, label: string, offset: number, source: string) =>
      `\\${atSentenceStart(source, offset) ? "Cref" : "cref"}{${label}}`,
  );
  out = out.replace(/\\(?:auto|eq)?ref\{([^}]+)\}/g, (_whole, label: string, offset: number, source: string) =>
    `\\${atSentenceStart(source, offset) ? "Cref" : "cref"}{${label}}`);
  // cleveref reads `\cref{a, b}` as the labels `a` and ` b` (the second prints as ??): one label
  // list separator, no whitespace.
  out = out.replace(/\\(Cref|cref)\{([^}]*,[^}]*)\}/g, (_whole, command: string, labels: string) =>
    `\\${command}{${labels.split(",").map((x) => x.trim()).join(",")}}`);
  return unwrapReferenceOnlyInlineMath(out);
}

/** `\\cref` expands to prose, not a mathematical atom. Keep math delimiters only
 * when the group contains actual math; a reference list by itself is emitted as
 * ordinary text so the HTML converter never passes it to KaTeX. Single-dollar
 * inline math gets the same treatment as `\\(...\\)`: both are valid TeX inline
 * delimiters and both otherwise produce the same broken web rendering. */
function unwrapReferenceOnlyInlineMath(tex: string): string {
  const referencesOnly = (content: string): boolean => {
    const reference = /\\[cC]ref\{[^{}]+\}/g;
    const separator = /^[\s,;:~()\-–—]*$/;
    let end = 0;
    let count = 0;
    for (let match = reference.exec(content); match; match = reference.exec(content)) {
      if (!separator.test(content.slice(end, match.index))) return false;
      end = match.index + match[0].length;
      count += 1;
    }
    return count > 0 && separator.test(content.slice(end));
  };
  const unwrap = (whole: string, content: string) => referencesOnly(content) ? content : whole;
  let out = tex.replace(/\\\(([\s\S]*?)\\\)/g, unwrap);
  // Do not treat escaped dollars or either half of `$$...$$` as inline delimiters.
  out = out.replace(/(?<![\\$])\$(?!\$)([\s\S]*?)(?<![\\$])\$(?!\$)/g, unwrap);
  return out;
}

/**
 * Repair + lint `\cref{obj:…}`/`\Cref{obj:…}` cross-references against the labels actually defined in the paper
 * (every anchored-env argument becomes a `\label{obj:<arg>}`). Drafting models sometimes drop a
 * kind prefix from an env id (e.g. `\cref{obj:oracle-regime-reduction}` for an env anchored at
 * `prop:oracle-regime-reduction`), which LaTeX renders as a silent `??`. This deterministically
 * rewrites such a ref to its unique prefixed label, and reports any `obj:` ref that still resolves
 * to no defined env (a dangling `??`) so the stage fails loud instead of shipping the broken link.
 *
 * Only the `obj:` label namespace is touched. The command is preserved; syntax canonicalization is
 * handled separately by `normalizeCrefs` before a body freezes.
 * `definedIds` is the set of env-argument ids present in the paper (use `parseAnchoredEnvs`).
 */
export function repairObjRefs(tex: string, definedIds: Set<string>): { tex: string; problems: LintProblem[] } {
  const problems: LintProblem[] = [];
  const out = tex.replace(/\\(Cref|cref|ref)\{([^}]+)\}/g, (whole, command: string, rawLabels: string) => {
    const labels = rawLabels.split(",").map((x) => x.trim());
    if (!labels.some((x) => x.startsWith("obj:"))) return whole;
    let changed = false; // byte-preserving unless a label is actually repaired (this runs on frozen bodies)
    const repaired = labels.map((label) => {
      if (!label.startsWith("obj:")) return label;
      const id = label.slice(4);
      if (definedIds.has(id)) return label;
      // A unique env whose id is `<kind>:<id>` (the drafter dropped the kind prefix) → repair.
      const matches = [...definedIds].filter((d) => d.endsWith(`:${id}`));
      if (matches.length === 1) { changed = true; return `obj:${matches[0]}`; }
      problems.push({
        gate: "undefined-ref",
        detail:
          matches.length === 0
            ? `\\${command}{obj:${id}} resolves to no defined environment (renders as "??"); point it at an existing env label`
            : `\\${command}{obj:${id}} is ambiguous — matches ${matches.map((d) => `obj:${d}`).join(", ")}; use the full label`,
      });
      return label;
    });
    return changed ? `\\${command}{${repaired.join(",")}}` : whole;
  });
  return { tex: out, problems };
}

/**
 * Obj ids are plumbing: prose reaches a statement through `\\cref{obj:<id>}` (the env macros
 * define the labels), never through the bare id. Models that see `\\cref{obj:thm:main}` in a
 * sentence sometimes "clean" the prefix away when they quote or rewrite it, or name the id bare;
 * neither is a label LaTeX can resolve. Both repairs are fully determined (a known id can only
 * mean its `obj:` label), so this rewrites them instead of a lint rejecting the text:
 *  - a label list of `\\cref`/`\\Cref`/`\\ref` naming a known id bare gets the `obj:` prefix;
 *  - a bare known id in prose outside frozen env blocks, references, labels and comments becomes
 *    `\\cref{obj:<id>}`.
 * Byte-preserving otherwise.
 */
export function canonicalizeObjRefs(tex: string, knownIds: ReadonlySet<string>): string {
  if (knownIds.size === 0) return tex;
  const restoreRef = (ref: string): string =>
    ref.replace(/^\\(Cref|cref|ref)\{([^}]+)\}$/, (whole, command: string, rawLabels: string) => {
      let changed = false;
      const labels = rawLabels.split(",").map((x) => x.trim()).map((label) => {
        if (label.startsWith("obj:") || !knownIds.has(label)) return label;
        changed = true;
        return `obj:${label}`;
      });
      return changed ? `\\${command}{${labels.join(",")}}` : whole;
    });
  const alternation = [...knownIds]
    .sort((x, y) => y.length - x.length)
    .map((id) => id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"))
    .join("|");
  const bareId = new RegExp(`(?<![\\w:-])(${alternation})(?![\\w-])`, "g");
  // references get their prefix restored; leanref/cite/label arguments are opaque and left alone
  const protectedSpan = /(\\(?:Cref|cref|ref|label|leanref|cite[A-Za-z]*)\s*(?:\[[^\]]*\]\s*){0,2}\{[^}]*\})/;
  const fixProse = (span: string): string =>
    span.split("\n").map((line) => {
      // parity-aware comment cut: `\%` is a literal percent, `\\%` (row break, then %) a comment
      const cut = line.search(/(?<!\\)(?:\\\\)*%/);
      const at = cut < 0 ? -1 : cut + (line.slice(cut).match(/^(?:\\\\)*/)?.[0].length ?? 0);
      const code = at < 0 ? line : line.slice(0, at);
      const comment = at < 0 ? "" : line.slice(at);
      return code.split(protectedSpan).map((part, i) => (i % 2 === 1 ? restoreRef(part) : part.replace(bareId, "\\cref{obj:$1}"))).join("") + comment;
    }).join("\n");
  let out = "";
  let pos = 0;
  for (const e of scanAnchoredEnvs(tex)) {
    out += fixProse(tex.slice(pos, e.start)) + e.raw;
    pos = e.end;
  }
  return out + fixProse(tex.slice(pos));
}

/** Whitespace-insensitive canonical form: reflowing prose is not drift, changing tokens is. */
function normalizeBody(body: string): string {
  return body.replace(/\s+/g, " ").trim();
}

/** Whitespace-insensitive: reflowing prose is not drift, changing tokens is. */
export function hashEnvBody(body: string): string {
  return createHash("sha256").update(normalizeBody(body)).digest("hex");
}

/**
 * Reject inline/display math delimiters nested inside a display block. LaTeX may
 * compile some malformed variants, but Pandoc preserves the nested delimiters
 * and the site's KaTeX pass then exposes the raw TeX as a rendering error.
 */
export function lintNestedMathDelimiters(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  // `\text{...}` temporarily enters text mode, so `\text{\(P\) ...}` is a
  // legitimate text-to-math re-entry rather than math nested directly in math.
  // Track balanced arguments (including nested formatting braces) and exempt
  // only delimiters wholly inside those arguments.
  const textRanges: Array<{ start: number; end: number }> = [];
  for (const startMatch of tex.matchAll(/\\text\s*\{/g)) {
    const start = startMatch.index!;
    const brace = start + startMatch[0].lastIndexOf("{");
    let depth = 1;
    for (let i = brace + 1; i < tex.length; i++) {
      const escaped = i > 0 && (() => {
        let slashes = 0;
        for (let j = i - 1; j >= 0 && tex[j] === "\\"; j--) slashes++;
        return slashes % 2 === 1;
      })();
      if (escaped) continue;
      if (tex[i] === "{") depth++;
      else if (tex[i] === "}" && --depth === 0) {
        textRanges.push({ start: brace + 1, end: i });
        break;
      }
    }
  }
  const textMathEndpoints = new Set<number>();
  for (const range of textRanges) {
    let opener: number | null = null;
    for (const m of tex.slice(range.start, range.end).matchAll(/(\\+)([()])/g)) {
      if (m[1].length % 2 === 0) continue;
      const at = range.start + m.index! + m[1].length - 1;
      if (m[2] === "(" && opener === null) opener = at;
      else if (m[2] === ")" && opener !== null) {
        textMathEndpoints.add(opener);
        textMathEndpoints.add(at);
        opener = null;
      }
    }
  }
  // Backslash-RUN parity, not a single-char lookbehind: an ODD run before the
  // bracket is a delimiter, an even run is a row break/literal. The lookbehind
  // version got runs ≥ 2 wrong in both directions — `\\[1.1em]` (row break with
  // spacing) as a false opener, and `d \\\]` (row break directly before a real
  // close) as a missed close that swallowed the following prose into a false
  // nested-math report.
  let openAt: number | null = null;
  let reported = false;
  const lineOf = (at: number) => tex.slice(0, at).split("\n").length;
  for (const m of tex.matchAll(/(\\+)([\[\](])/g)) {
    if (m[1].length % 2 === 0) continue;
    const at = m.index! + m[1].length - 1;
    const delim = m[2];
    if ((delim === "(" || delim === ")") && textMathEndpoints.has(at)) continue;
    if (openAt == null) {
      if (delim === "[") {
        openAt = at;
        reported = false;
      }
      continue;
    }
    if (delim === "]") {
      const body = tex.slice(openAt + 2, at);
      if (body.includes("\\begin{array}{p{")) {
        problems.push({
          gate: "web-incompatible-math",
          detail: `display math beginning on line ${lineOf(openAt)} uses an array with paragraph columns; use a table/tabular environment so KaTeX does not expose raw TeX`,
        });
      }
      openAt = null;
      continue;
    }
    if (!reported) {
      problems.push({
        gate: "nested-math-delimiter",
        detail: `display math beginning on line ${lineOf(openAt)} contains a nested \\(...\\) or \\[...\\] delimiter; move prose outside the display and keep only bare math inside`,
      });
      reported = true;
    }
  }
  return problems;
}

/** Re-sequence the anchored environments of one section so they appear in `order` (the outline's
 *  `objs` for that section, restricted to the envs the text contains). The i-th env slot receives
 *  the i-th env of the target order; prose between slots is untouched. Returns `tex` unchanged
 *  when the sequence already agrees or the env sets differ (that is `validatePlacement`'s job).
 *  Rationale: P1 computed the paper order so that every definition precedes its first use; a
 *  drafter that emits the envs of a section in another order would make P3's frozen-layer order
 *  gate fail with a P1 repair instruction for an order P1 never produced. */
export function reorderAnchoredEnvs(tex: string, order: readonly string[]): string {
  const blocks = scanAnchoredEnvs(tex);
  const present = new Set(blocks.map((b) => b.obj_id));
  const target = order.filter((id) => present.has(id));
  const current = blocks.map((b) => b.obj_id);
  if (target.length !== current.length || current.every((id, i) => id === target[i])) return tex;
  if ([...target].sort().join("\n") !== [...current].sort().join("\n")) return tex;
  const rawById = new Map(blocks.map((b) => [b.obj_id, b.raw] as const));
  let out = "";
  let at = 0;
  blocks.forEach((b, i) => {
    out += tex.slice(at, b.start) + rawById.get(target[i])!;
    at = b.end;
  });
  return out + tex.slice(at);
}

/**
 * Place a section's frozen environments mechanically. P1's order is total and the frozen text is
 * identical wherever it is printed, so every repair here has exactly one outcome: a duplicate
 * keeps its first copy; an environment the outline places in another section is removed; the
 * remaining blocks are permuted into `order` (prose stays where the drafter put it); a missing
 * environment is inserted right after its nearest present P1 predecessor (before the first present
 * successor when nothing precedes it; at the end of the section when the section prints none).
 * Returns the repaired tex and one line per repair, for the stage's notes. Nothing else changes.
 */
export function placeFrozenEnvs(
  tex: string, order: readonly string[], canonical: ReadonlyMap<string, string>,
): { tex: string; repairs: string[] } {
  const repairs: string[] = [];
  const wanted = new Set(order);
  const firstCopy = new Map<string, number>();
  for (const e of scanAnchoredEnvs(tex)) if (!firstCopy.has(e.obj_id)) firstCopy.set(e.obj_id, e.order);
  const seen = new Set<string>();
  let out = replaceAnchoredEnvs(tex, (e) => { // visits blocks last-to-first; decisions are by first copy
    if (!wanted.has(e.obj_id)) {
      repairs.unshift(`${e.obj_id}: removed — ${canonical.has(e.obj_id) ? "the outline places it in another section" : "it is not a frozen environment of this paper"}`);
      return "";
    }
    if (firstCopy.get(e.obj_id) !== e.order) {
      repairs.unshift(`${e.obj_id}: duplicate copy removed`);
      return "";
    }
    seen.add(e.obj_id);
    return e.raw;
  });
  const reordered = reorderAnchoredEnvs(out, order);
  if (reordered !== out) {
    repairs.push(`re-sequenced ${[...seen].length} environment(s) into the P1 order`);
    out = reordered;
  }
  for (const id of order) {
    if (seen.has(id)) continue;
    const block = canonical.get(id);
    if (block === undefined) continue; // not a frozen environment (prose-only object) — nothing to place
    const present = scanAnchoredEnvs(out);
    const rank = new Map(order.map((x, i) => [x, i] as const));
    const predecessor = [...present].reverse().find((e) => rank.get(e.obj_id)! < rank.get(id)!);
    const successor = present.find((e) => rank.get(e.obj_id)! > rank.get(id)!);
    if (predecessor) out = `${out.slice(0, predecessor.end)}\n\n${block}${out.slice(predecessor.end)}`;
    else if (successor) out = `${out.slice(0, successor.start)}${block}\n\n${out.slice(successor.start)}`;
    else out = `${out.replace(/\n+$/, "")}\n\n${block}\n`;
    seen.add(id);
    repairs.push(`${id}: inserted at its P1 position (the draft omitted it)`);
  }
  return { tex: out, repairs };
}

/**
 * Replaces every anchored env block with its canonical frozen text (keyed by
 * obj_id). Drafting models occasionally paraphrase a body while "copying" it
 * into a section; the frozen layer is the trust anchor, so the mechanical
 * substitution — not the model's copy — is what reaches the paper. Blocks with
 * an obj_id missing from the canonical map are left as-is (the lint flags them).
 */
export function normalizeFrozenEnvs(tex: string, canonical: Map<string, string>): string {
  return replaceAnchoredEnvs(tex, (e) => canonical.get(e.obj_id) ?? e.raw);
}

/**
 * Drops \label{obj:...} from inside anchored env bodies. The env macro already
 * defines that label; drafting models sometimes add it anyway, which would be
 * a duplicate label in LaTeX and reads as frozen-drift to the linter.
 */
export function stripRedundantEnvLabels(tex: string): string {
  return replaceAnchoredEnvs(tex, (e) =>
    tex.slice(e.start, e.bodyStart) + e.body.replace(/[ \t]*\\label\{obj:[^}]*\}\n?/g, "") + tex.slice(e.bodyEnd, e.end),
  );
}

/**
 * Self-containedness gate. A named assumption/condition label invoked as
 * hypothesis shorthand (e.g. "Assumptions A1--A4", "Assumption~A5") must have a
 * defining environment — the label token must appear inside some
 * definitionv/assumptionv body or title. A label used only inside theorem
 * hypotheses with no definition anywhere is a defect the reader cannot resolve
 * (the A1–A5 / law-class miss). Ranges are expanded (A1--A4 → A1,A2,A3,A4) and
 * connectors (`--`, `,`, `and`, `to`) are followed. Returns one problem per
 * distinct undefined label.
 */
export function lintSelfContainment(tex: string): LintProblem[] {
  const defined = new Set<string>();
  for (const e of parseAnchoredEnvs(tex)) {
    if (e.env === "definitionv" || e.env === "algorithmv" || e.env === "assumptionv") {
      for (const t of `${e.title ?? ""} ${e.body}`.match(/\b[A-Z]\d+\b/g) ?? []) defined.add(t);
    }
  }
  const problems: LintProblem[] = [];
  const seen = new Set<string>();
  const clauseRe =
    /\bAssumptions?\b[~\s]*([A-Z]\d+(?:\s*(?:--|–|-|,|;|and|to|through|~|\s)+[A-Z]?\d+)*)/g;
  let m: RegExpExecArray | null;
  while ((m = clauseRe.exec(tex))) {
    const grp = m[1].replace(
      /([A-Z])(\d+)\s*(?:--|–|-|to|through)\s*([A-Z]?)(\d+)/g,
      (whole, L: string, a: string, L2: string, b: string) => {
        const lo = +a;
        const hi = +b;
        if ((L2 === "" || L2 === L) && hi >= lo && hi - lo < 50) {
          const xs: string[] = [];
          for (let i = lo; i <= hi; i++) xs.push(L + i);
          return xs.join(" ");
        }
        return whole;
      },
    );
    for (const lab of grp.match(/[A-Z]\d+/g) ?? []) {
      if (defined.has(lab) || seen.has(lab)) continue;
      seen.add(lab);
      problems.push({
        gate: "undefined-assumption",
        detail: `named assumption "${lab}" is referenced but has no defining environment (definitionv/assumptionv) — a reader cannot resolve it; give it a defining env or fold it into the law-class definition`,
      });
    }
  }
  return problems;
}

/**
 * Readability gate (the clarity check the equivalence gate cannot do: it verifies
 * statements MATCH the Lean, never that they READ as a paper). Two defect classes
 * in the displayed statement bodies, both reader-facing:
 *
 *  1. `lean-identifier` — a raw Lean declaration name leaking into displayed math.
 *     Lean decls are multi-word camelCase/PascalCase (≥3 segments) like
 *     `smoothedInverseWeightRegression`, `CrossFitNuisancesRandom`,
 *     `LowerClassWitnessClosure`. A statement must render these as mathematical
 *     notation (per the notation table), never the identifier. (Single-word names,
 *     all-caps acronyms like AIPW/DML, and `\command`s are NOT flagged.)
 *  2. `formalization-leak` — formalization-procedure / "Lean-side" phrasing in a
 *     statement body ("Assume the following Lean-side inputs", "checks have shown
 *     that…"). A statement states the mathematics, not how it was machine-checked.
 *
 * Catches the leak no matter which stage authored the env (P1 touch-up OR an
 * orchestrator re-freeze that bypassed the touch-up prompt). Runs before the P1
 * freeze so the producer must clean it.
 */
const LEAN_IDENT_RE = /(?<![\\A-Za-z0-9])[A-Za-z][a-z0-9]*(?:[A-Z][a-z0-9]+){2,}\b/g;
const FORMALIZATION_PHRASING: { re: RegExp; what: string }[] = [
  { re: /\bLean\b/i, what: `Lean implementation framing` },
  { re: /\bchecks have shown\b/i, what: `proof-procedure phrasing ("checks have shown")` },
  { re: /analytic shape and scale checks/i, what: `proof-procedure phrasing ("…shape and scale checks…")` },
];
export function lintClarity(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  for (const e of parseAnchoredEnvs(tex)) {
    const idents = new Set<string>();
    let m: RegExpExecArray | null;
    // BibTeX keys are opaque identifiers by design and often look like PascalCase Lean names
    // (`BochnakCosteRoy1998`). They are citation provenance, not displayed mathematical prose.
    // Text-font math arguments (`\mathrm{VarPlusBias}`, `\text{…}`, `\operatorname{…}`) are
    // DISPLAYED notation, not leaked Lean identifiers — drop their contents too.
    const proseBody = e.body
      .replace(/\\cite[A-Za-z]*\s*(?:\[[^\]]*\]\s*){0,2}\{[^}]*\}/g, "")
      .replace(/\\(?:mathrm|mathsf|mathtt|text|operatorname\*?)\s*\{[^{}]*\}/g, "");
    LEAN_IDENT_RE.lastIndex = 0;
    while ((m = LEAN_IDENT_RE.exec(proseBody))) idents.add(m[0]);
    for (const id of idents) {
      problems.push({
        gate: "lean-identifier",
        objId: e.obj_id,
        detail: `${e.obj_id}: Lean declaration name "${id}" appears in the displayed statement — render it as mathematical notation (per the notation table), never the raw identifier`,
      });
    }
    for (const p of FORMALIZATION_PHRASING) {
      if (p.re.test(e.body)) {
        problems.push({
          gate: "formalization-leak",
          objId: e.obj_id,
          detail: `${e.obj_id}: ${p.what} in the statement body — state the mathematical condition, not how it was formalized/checked`,
        });
      }
    }
    // Mangled-word guard: a bare single-letter word in PROSE (outside math, refs,
    // and macros) is almost always a symbol missing \(..\) or a word clobbered by
    // a careless per-env rename (observed 2026-08-20: an operator risk→u rename
    // turned "(ACE fixed-code risk.)" into "(ACE fixed-code u.)" inside a frozen
    // body, invisible to every gate until the P5 referee). Articles/pronouns
    // (a/A/I/i) and parenthesized list markers "(b)" are excluded. Frozen bodies
    // reach this lint via the assembled layer at P1 and unfiltered via P4's paper
    // scan, so an operator freeze cannot ship a mangled word past emit.
    const noMath = e.body
      .replace(/\\\[[\s\S]*?\\\]/g, " ")
      .replace(/\\\((?:[^\\]|\\[^)])*?\\\)/g, " ")
      .replace(/\$[^$]*\$/g, " ")
      .replace(/\\(?:cref|Cref|ref|label|cite[A-Za-z]*|leanref)\s*(?:\[[^\]]*\]\s*){0,2}\{[^}]*\}(?:\{[^}]*\})?/g, " ")
      .replace(/\\[A-Za-z]+/g, " ");
    for (const w of noMath.matchAll(/(?:^|[\s~])((?![aAiI])[A-Za-z])(?=[\s.,;:!?]|$)/g)) {
      problems.push({
        gate: "mangled-word",
        objId: e.obj_id,
        detail: `${e.obj_id}: bare single-letter word "${w[1]}" in prose — a math symbol missing \\(..\\), or a word corrupted by a bad rename; fix the source text`,
      });
    }
  }
  // PROOF blocks get the same reader-facing gate: "Lean proves …" inside a prose
  // proof is exactly as much of a formalization leak as in a statement body, and
  // no other lint ever scanned proofs. Balanced extraction (proofs nest — "Proof
  // of Claim 1"); `% lean: <decl>` provenance comments are legitimate machinery,
  // so strip comments BEFORE scanning; \cite/text-font-math spans drop as above.
  let rest = tex;
  for (let block = extractBalancedEnv(rest, "proof"); block !== null; block = extractBalancedEnv(rest, "proof")) {
    rest = rest.replace(block, () => " ");
    // Label from the proof's TITLE bracket only — a body \cref must not name the proof.
    const title = /^\\begin\{proof\}\[([^\]]*)\]/.exec(block)?.[1] ?? "";
    const label = /\\cref\{obj:([^}]*)\}/.exec(title)?.[1] ?? "proof";
    const proofProse = stripTexComments(block)
      .replace(/\\cite[A-Za-z]*\s*(?:\[[^\]]*\]\s*){0,2}\{[^}]*\}/g, "")
      .replace(/\\(?:mathrm|mathsf|mathtt|text|operatorname\*?)\s*\{[^{}]*\}/g, "");
    for (const p of FORMALIZATION_PHRASING) {
      if (p.re.test(proofProse)) {
        problems.push({
          gate: "formalization-leak",
          objId: label,
          detail: `proof of ${label}: ${p.what} in the prose proof — give the mathematical argument, not how it was formalized/checked`,
        });
      }
    }
  }
  return problems;
}

/**
 * Assumption A-labels (the "(A_k)" in titles) must be consecutive and agree with the printed
 * Assumption order — never A1,A2,A4,… (a gap at A3). Advisory: reader-facing, judged by the
 * referee, never a halt. Cross-reference form is not linted: `normalizeCrefs` rewrites every
 * authored text to target-typed cleveref before it is assembled.
 */
interface NotationHome {
  symbol: string;
  home: string;
}

/** The reviewer copy of a paper: TeX comments (`% lean:` provenance, scope sentinels,
 *  drafting notes) never render, waste prompt tokens, and have produced findings against
 *  text no reader sees. Strip them for READ-ONLY reviewers (P5 referee, P3 rubric) only —
 *  the artifact and every editing path keep their comments, because a patch-applying
 *  reviser must see the file as it really is. Comment-only lines collapse so the copy has
 *  no runs of blank lines. */
export function reviewerTexFor(paperTex: string): string {
  return unwrapLeanrefs(stripTexComments(paperTex)).replace(/\n[ \t]*\n(?:[ \t]*\n)+/g, "\n\n");
}

/** `\leanref{<id>}{<display>}` → `<display>`: the PDF prints only the display text (the macro is
 *  `\newcommand{\leanref}[2]{#2}`), so a reviewer shown the wrapper reports the internal id as a
 *  reader-visible placeholder — a recurring false finding. Balanced-brace scan; a malformed wrapper
 *  is left as written. */
export function unwrapLeanrefs(tex: string): string {
  const MARK = "\\leanref{";
  let out = "";
  let i = 0;
  for (;;) {
    const at = tex.indexOf(MARK, i);
    if (at < 0) { out += tex.slice(i); return out; }
    out += tex.slice(i, at);
    const idEnd = closingBrace(tex, at + MARK.length - 1);
    const dispOpen = idEnd >= 0 ? idEnd + 1 : -1;
    const dispEnd = dispOpen >= 0 && tex[dispOpen] === "{" ? closingBrace(tex, dispOpen) : -1;
    if (dispEnd < 0) { out += MARK; i = at + MARK.length; continue; }
    out += tex.slice(dispOpen + 1, dispEnd);
    i = dispEnd + 1;
  }
}

/** Every `\leanref` must carry two balanced brace groups; an unterminated one makes LaTeX scan to
 *  the end of the file ("File ended while scanning use of \leanref") — caught at P4 compile after
 *  P3's gates were paid. Assembly catches it first, and names the spot. */
export function lintLeanrefs(tex: string): LintProblem[] {
  const MARK = "\\leanref{";
  const problems: LintProblem[] = [];
  let i = 0;
  for (;;) {
    const at = tex.indexOf(MARK, i);
    if (at < 0) return problems;
    const idEnd = closingBrace(tex, at + MARK.length - 1);
    const dispOpen = idEnd >= 0 ? idEnd + 1 : -1;
    const dispEnd = dispOpen >= 0 && tex[dispOpen] === "{" ? closingBrace(tex, dispOpen) : -1;
    if (dispEnd < 0) {
      problems.push({ gate: "unterminated-leanref", detail: `\\leanref without two balanced brace groups at: ${tex.slice(at, at + 60).replace(/\s+/g, " ")}` });
      i = at + MARK.length;
      continue;
    }
    i = dispEnd + 1;
  }
}

/** Index of the `}` matching the `{` at `open`, honouring nesting and `\{`/`\}`; -1 if unbalanced. */
function closingBrace(tex: string, open: number): number {
  let depth = 0;
  for (let j = open; j < tex.length; j++) {
    const ch = tex[j];
    if (ch === "\\") { j++; continue; }
    if (ch === "{") depth++;
    else if (ch === "}") { depth--; if (depth === 0) return j; }
  }
  return -1;
}

/** Parse the P1 notation table rows that assign a paper symbol to an anchored home. */
export function notationHomes(notation: string): NotationHome[] {
  const out: NotationHome[] = [];
  for (const line of notation.split("\n")) {
    // Split on UNESCAPED pipes only: a math cell containing `\|` (a TeX norm,
    // doubling as the markdown escape for a literal pipe) must not add columns —
    // `| $\|\beta\|_1$ | … |` used to shatter into six bogus cells and the row
    // was silently dropped from the definition-order check.
    const parts = line.split(/(?<!\\)\|/);
    const edged = /^\s*\|/.test(line) && /(?<!\\)\|\s*$/.test(line);
    const cells = (edged ? parts.slice(1, -1) : parts).map((x) => x.trim());
    if (cells.length < 4 || cells[0].toLowerCase() === "note symbol" || /^-+$/.test(cells[0])) continue;
    const home = cells[3].replace(/^`|`$/g, "").trim();
    if (!/^[A-Za-z0-9:_-]+$/.test(home) || home === "notation_gaps") continue;
    let symbol = cells[1]
      .replace(/^\\\(|\\\)$/g, "")
      .replace(/^\$|\$$/g, "")
      .trim();
    // A scalar declaration such as `K_-=2m+1` names `K_-`; the right side is its definition.
    // By contrast, a composite relation such as `Phi(theta)=Phi(eta)` is not a new atomic symbol
    // and its row's "home" describes the relation, not either already-defined operand.
    if (symbol.includes("=")) {
      const lhs = symbol.split("=")[0].trim();
      // An `=` inside a brace/bracket group (`\mathbb{E}[Y \mid X=x]`, `\sum_{i=1}^n`)
      // is not a scalar declaration: truncating at it produced an unmatchable
      // garbage symbol. Skip such rows like other composite relations.
      const balanced = (open: string, close: string) => lhs.split(open).length === lhs.split(close).length;
      if (/[()]/.test(lhs) || !balanced("{", "}") || !balanced("[", "]")) continue;
      symbol = lhs;
    }
    // A one-letter ASCII symbol is retained ONLY as explicit structured
    // metadata. It cannot own anything by itself: P1 independently requires
    // the named definitionv body to certify this exact symbol.
    if (!symbol || /(?:\\ldots|\\dots)/.test(symbol)) continue;
    out.push({ symbol, home });
  }
  return out;
}

function notationSearchText(tex: string): string {
  return (
    stripTexComments(tex)
      .replace(/\\(?:Cref|cref|ref|label|pageref)\{[^}]*\}/g, "")
      // The first argument is metadata, not a displayed use (`sym:u_j` must not count as `u_j`).
      .replace(/\\leanref\{[^{}]*\}/g, "")
      .replace(/\\ensuremath\s*\{/g, "{")
      // Unescaped math delimiters only: `\\[1em]` is a row break — stripping its
      // `\[` left the mangled `\1em]` in the search text.
      .replace(/(?<!\\)(?:\\[()[\]]|\$)/g, "")
      // Canonicalize a single-char braced argument (`\mathcal{H}` ≡ `\mathcal H`)
      // and keep a control-word/argument boundary (`\Delta t`): both collapse to
      // the same sentinel-separated form, so the two spellings match each other
      // and plain whitespace removal cannot glue `\Delta t` into `\Deltat`.
      .replace(/(\\[A-Za-z]+)\s*\{([A-Za-z0-9])\}(?![A-Za-z0-9])/g, "$1\u0001$2")
      .replace(/(\\[A-Za-z]+)\s+(?=[A-Za-z])/g, "$1\u0001")
      .replace(/\s+/g, "")
  );
}

export function containsNotation(tex: string, symbol: string): boolean {
  const haystack = notationSearchText(tex);
  const needle = notationSearchText(symbol);
  if (!needle) return false;
  // Single-letter parameters must be tokens: `m` must not match the `m` in `\mathrm`.
  if (/^[A-Za-z]$/.test(needle)) {
    for (let at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + 1)) {
      const before = haystack[at - 1] ?? "";
      const after = haystack[at + 1] ?? "";
      if (!/[A-Za-z0-9\\]/.test(before) && !/[A-Za-z0-9_^]/.test(after)) return true;
    }
    return false;
  }
  // A TeX control word ends before the next non-letter (`\delta` must not match a longer command).
  if (/^\\[A-Za-z]+$/.test(needle)) {
    for (let at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + 1)) {
      if (!/[A-Za-z]/.test(haystack[at + needle.length] ?? "")) return true;
    }
    return false;
  }
  return haystack.includes(needle);
}

/** TRUE iff `text` uses `symbol` AS ITSELF, not merely as the base of a LABELLED variant.
 *  `containsNotation` is substring-based for multi-character needles, so a bare `N_k` matches
 *  inside `N_k^{(1)}`. For placement and for the definition-order check that is wrong: the
 *  split count `N_k^{(1)}` is a different object owned by a different definition, so counting
 *  it as a use drags the bare symbol's definition into the wrong section (or hard-fails the
 *  paper for a move placement just made).
 *
 *  Only a LABEL-like superscript forms a new object: a parenthesized index (`^{(1)}`) or a
 *  text-font tag (`^{\mathrm{loc}}`, `^{\text{...}}`, `^{\mathsf{...}}`). Arithmetic and
 *  operator superscripts — `^2`, `^{-1}`, `^{1/2}`, `^\top`, `^*`, `^T` — decorate the SAME
 *  object, so `N_k^2` before its home is still a genuine early use and must stay detected;
 *  treating every `^` as object-forming traded a loud failure for silent under-detection.
 *  Kept as a separate predicate rather than tightening `containsNotation`, whose substring
 *  semantics the notation lints rely on. Known (harmless) gaps: an operator written INSIDE a
 *  text-font macro — `^{\mathrm{-1}}`, `^{\mathrm{\top}}` — still reads as a label; nobody
 *  writes those, and the ordinary `^{-1}` / `^\top` spellings are handled. Anything else the
 *  pattern fails to recognize counts as a use, the conservative direction. Single-character
 *  symbols never reach this logic: `containsNotation` already applies a stricter word-boundary
 *  test for one-char needles, so `X` does not match inside `X^2`. */
export function usesSymbolUndecorated(text: string, symbol: string): boolean {
  if (!containsNotation(text, symbol)) return false;
  const esc = symbol.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  // Label-like superscript: `^{(...)}`, `^(...)`, or `^{\mathrm|\text|\mathsf|\mathit{...}}`.
  // A text-font tag must be at least TWO characters: `X^{\mathsf{T}}` / `X^{\mathrm{T}}` is
  // transpose — the same object, exactly like `^\top` — not a label naming a new one. Anything
  // this pattern fails to recognize (e.g. `\operatorname{...}`, nested braces) falls through to
  // "counts as a use", the conservative direction.
  const label = String.raw`\^\s*(?:\((?:[^()]*)\)|\{\s*(?:\([^()]*\)|\\(?:mathrm|text|mathsf|mathit|mathbf)\s*\{\s*[^{}\s]{2,}[^{}]*\})\s*\})`;
  const labelled = new RegExp(`${esc}\\s*${label}`);
  if (!labelled.test(text)) return true;
  // Some occurrence must be unlabelled: strip every labelled occurrence and re-test.
  return containsNotation(text.replace(new RegExp(`${esc}\\s*${label}`, "g"), " "), symbol);
}

/**
 * TRUE iff some anchored environment DISPLAYS a defining equality for `symbol`: an
 * occurrence of the symbol immediately followed by `=`, `:=`, `\coloneqq`, or `\equiv`
 * (whitespace/thin-space insensitive; an alignment `&` may intervene). This is the
 * deterministic "the paper shows what this symbol IS" signal used to decide whether a
 * Lean-realized symbol still needs a paper-side definition: an `@realizes` tag makes a
 * symbol machine-resolvable (the web drawer), but a PDF reader can resolve it only from
 * a printed defining display. RHS-only appearances (`\frac{\mu_Y}{\mu_D}=\theta`)
 * deliberately do NOT count — an identification theorem that equates a ratio TO an
 * otherwise-undefined symbol is exactly the failure this check exists to surface.
 */
export function displaysDefiningEquality(tex: string, symbol: string): boolean {
  // Thin spaces and single-char script braces are display sugar; erase them the same
  // way in haystack and needle so `\mu_{n}\,=` still matches the needle `\mu_n` and
  // `\mu^{*}` matches `\mu^*` (the braced token may be any single non-brace char).
  const canon = (s: string) =>
    notationSearchText(s)
      .replace(/\\[,;!:]/g, "")
      .replace(/([_^])\{([^{}])\}/g, "$1$2");
  // A display defines the DECORATED variant, not the base symbol: `\hat\theta_T = …`
  // defines the estimator of θ_T, not θ_T itself (the audit's "one hat away" re-ship
  // of the θ_T defect), and `w_\pi = …` / `x^\theta = …` embed the symbol as a script.
  const ACCENT_BEFORE_RE =
    /\\(?:hat|widehat|bar|overline|underline|tilde|widetilde|dot|ddot|vec|overrightarrow|check|breve|acute|grave|mathring|bm|boldsymbol|mathbf)\{?$/;
  const needle = canon(symbol);
  if (!needle) return false;
  const haystack = canon(tex);
  for (let at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + 1)) {
    // Token boundary before: a plain-letter needle must not match the tail of a longer
    // identifier or a command argument (`\hat t_n`, whose canon form carries the U+0001 command/argument sentinel, must not define `t_n`).
    const before = haystack[at - 1] ?? "";
    if (/^[A-Za-z]/.test(needle) && /[A-Za-z0-9\\\u0001]/.test(before)) continue;
    // Script/accent context (ANY needle, including command words): skip one opening
    // brace, then reject a subscript/superscript position or a preceding accent command.
    if (/[_^]$/.test(haystack.slice(0, at).replace(/\{$/, "")) || ACCENT_BEFORE_RE.test(haystack.slice(0, at))) continue;
    // A primed occurrence is the DERIVED symbol: `\theta' = …` does not define `\theta`,
    // so primes are NOT skipped before requiring the equality sign.
    const rest = haystack.slice(at + needle.length).replace(/^&/, "");
    // A command-word needle ends before the next letter (`\mu` must not match `\muY`).
    if (/\\[A-Za-z]+$/.test(needle) && /^[A-Za-z]/.test(rest)) continue;
    if (/^(?::?=|\\coloneqq(?![A-Za-z])|\\equiv(?![A-Za-z]))/.test(rest)) return true;
  }
  return false;
}

/** Like `displaysDefiningEquality`, but treats a function's displayed argument list as
 * incidental to the notation home. Thus `\Psi_{t,x}(h)=...` is a home for a reviewer
 * request spelled `\Psi_{t,x}(h_n)`, while the decorated-symbol protections above still
 * prevent an estimator equality from defining its undecorated target. */
export function displaysDefiningEqualityFamily(tex: string, symbol: string): boolean {
  if (displaysDefiningEquality(tex, symbol)) return true;
  const canon = (s: string) =>
    notationSearchText(s)
      .replace(/\\[,;!:]/g, "")
      .replace(/([_^])\{([^{}])\}/g, "$1$2");
  const full = canon(symbol);
  // A reviewer may name the operator (`\psi_B`) or one displayed application
  // (`\Psi(h_n)`). In both cases the definition home may use another bound argument.
  const stem = full.replace(/\([^()]*\)$/, "");
  if (!stem) return false;
  const haystack = canon(tex);
  const accentBefore =
    /\\(?:hat|widehat|bar|overline|underline|tilde|widetilde|dot|ddot|vec|overrightarrow|check|breve|acute|grave|mathring|bm|boldsymbol|mathbf)\{?$/;
  for (let at = haystack.indexOf(stem); at >= 0; at = haystack.indexOf(stem, at + 1)) {
    const before = haystack[at - 1] ?? "";
    if (/^[A-Za-z]/.test(stem) && /[A-Za-z0-9\\\u0001]/.test(before)) continue;
    if (/[_^]$/.test(haystack.slice(0, at).replace(/\{$/, "")) || accentBefore.test(haystack.slice(0, at))) continue;
    let rest = haystack.slice(at + stem.length);
    if (/\\[A-Za-z]+$/.test(stem) && /^[A-Za-z]/.test(rest)) continue;
    if (!rest.startsWith("(")) continue;
    let depth = 0;
    let end = -1;
    for (let i = 0; i < rest.length; i++) {
      if (rest[i] === "(") depth++;
      else if (rest[i] === ")" && --depth === 0) { end = i + 1; break; }
    }
    if (end < 0) continue;
    rest = rest.slice(end).replace(/^&/, "");
    if (/^(?::?=|\\coloneqq(?![A-Za-z])|\\equiv(?![A-Za-z]))/.test(rest)) return true;
  }
  return false;
}



/** Parse atomic left-hand sides of top-level defining equalities in displayed/inline
 * mathematics. Equality signs inside binders (`i=1`) are ignored by bracket depth. */
export function definingNotationLhses(tex: string): string[] {
  const spans = [
    ...[...tex.matchAll(/\\\[([\s\S]*?)\\\]/g)].map((m) => m[1]),
    ...[...tex.matchAll(/\\\((.*?)\\\)/g)].map((m) => m[1]),
    ...[...tex.matchAll(/(?<!\\)\$([^$\n]+)(?<!\\)\$/g)].map((m) => m[1]),
  ];
  const out = new Set<string>();
  for (const span0 of spans) {
    const span = span0.replace(/\\begin\{(?:aligned|gathered|split|array)\}(?:\{[^}]*\})?/g, "")
      .replace(/\\end\{(?:aligned|gathered|split|array)\}/g, "");
    for (const row0 of span.split(/\\\\|\n/)) {
      const row = row0.trim();
      let round = 0, square = 0, curly = 0;
      let at = -1;
      for (let i = 0; i < row.length; i++) {
        const c = row[i];
        if (c === "(") round++; else if (c === ")") round--;
        else if (c === "[") square++; else if (c === "]") square--;
        else if (c === "{") curly++; else if (c === "}") curly--;
        if (round || square || curly) continue;
        if (row.startsWith("\\coloneqq", i) || row.startsWith("\\equiv", i) || row.startsWith(":=", i) || c === "=") { at = i; break; }
      }
      if (at < 0) continue;
      let lhs = row.slice(0, at).replace(/&/g, "").trim();
      lhs = lhs.replace(/^.*?(?:\\text\{[^}]*\}\s*)+/, "").trim();
      if (!lhs || lhs.length > 180 || /(?:\\(?:le|ge|in|subset|sim)\b|[<>≤≥∈])/.test(lhs)) continue;
      // Reject prose/composite arithmetic; retain decorated identifiers, calls, and classes.
      if (/\s(?:and|or|for|when)\s/i.test(lhs) || /\s[+\-*/]\s/.test(lhs)) continue;
      out.add(lhs);
    }
  }
  return [...out];
}

/** TRUE iff `body` INTRODUCES `symbol` with an introducing clause: the symbol is the WHOLE math
 *  atom between an introducing verb and its complement ("let \\(b\\) denote …", "write \\(u\\) for …",
 *  "denote … by \\(b\\)"), or it is the left-hand side of a defining equality inside such a clause
 *  ("define \\(A(x) := …\\)"). Stricter than `proseDefinesNotation` (any defining word or `=` within
 *  100 characters), which is the right looseness for a table-designated home but reads
 *  "we define \\(B:=A\\)" as introducing `A`, and "let \\(x\\in\\mathcal X\\)" as introducing `\\mathcal X`.
 *  Whitespace inside the symbol is ignored; a spelling the regexes miss is the conservative
 *  direction (the use stays flagged). */
export function introducesNotation(body: string, symbol: string): boolean {
  const sym = symbol.trim().replace(/[.*+?^${}()|[\]\\]/g, "\\$&").replace(/\s+/g, "\\s*");
  const flat = body.replace(/\s+/g, " ");
  const open = String.raw`(?:\\\(|\$)\s*`;
  const close = String.raw`\s*(?:\\\)|\$)`;
  const verb = String.raw`\b(?:let|denote|define|defining|write|put|set|call|introduce)\b`;
  // A clause whose complement is a cross-reference ("let \\(C\\) be the constant of \\cref{…}") is a
  // forward reference to a definition elsewhere, not an introduction.
  const notRef = String.raw`(?![^.;:]{0,40}\\[cC]?ref\{)`;
  const wholeAtom = new RegExp(
    `${verb}[^.;:]{0,40}?${open}${sym}${close}\\s*(?:denote|denotes|be|as|by|for|the|is)\\b${notRef}`, "i");
  const definingLhs = new RegExp(
    `${verb}[^;]{0,60}?${open}${sym}\\s*(?::=|=|\\\\coloneqq|\\\\equiv)`, "i"); // `[^;]`: "…, i.e. \\(C := 2L\\)" crosses a period
  const denotedBy = new RegExp(
    String.raw`\b(?:denote|write)\b[^.;:]{0,60}?\bby\s*` + open + sym + close + notRef, "i");
  return wholeAtom.test(flat) || definingLhs.test(flat) || denotedBy.test(flat);
}

export function proseDefinesNotation(prose: string, symbol: string): boolean {
  const flat = prose.replace(/\s+/g, " ");
  for (let i = 0; i < flat.length; i++) {
    const tail = flat.slice(i);
    if (!containsNotation(tail, symbol)) break;
    // Locate approximately in the original prose; this deliberately accepts only explicit
    // introduction language, not a symbol merely appearing in a diagram or motivation sentence.
    const raw = notationSearchText(symbol);
    const compactAt = notationSearchText(tail).indexOf(raw);
    if (compactAt < 0) break;
    const context = tail.slice(Math.max(0, compactAt - 100), compactAt + symbol.length + 100);
    if (/\b(?:define|denote|let|write|fix|put|set|where)\b/i.test(context) || /:=|=/u.test(context)) return true;
    i += Math.max(1, compactAt + symbol.length);
  }
  return false;
}

/** One reader-order violation: `symbol`'s notation-table `home` introduces it, but `firstUse`
 *  displays it earlier in the text. */
export interface DefinitionOrderViolation {
  symbol: string;
  home: string;
  firstUse: string;
}

/**
 * The paper's frozen environments must appear in the ORDER P1 settled (`formal_layer.json` block
 * order): P1 is the one judge of definition order (it repairs what can be repaired and records
 * what cannot), P2 lays the sections out in that order, and P3/P4 only assert that nothing has
 * omitted or reordered the layer since. Pass only environment-bearing IDs, excluding prose-only blocks.
 * Environments outside the layer (proofs) are ignored.
 */
export function lintEnvOrder(tex: string, layerOrder: readonly string[]): LintProblem[] {
  const rank = new Map(layerOrder.map((id, i) => [id, i] as const));
  const problems: LintProblem[] = [];
  const seen = new Set<string>();
  let maxRank = -1;
  let maxId = "";
  for (const e of scanAnchoredEnvs(tex)) {
    const r = rank.get(e.obj_id);
    if (r === undefined) continue;
    if (seen.has(e.obj_id)) {
      problems.push({ gate: "frozen-layer-order", objId: e.obj_id, detail: `${e.obj_id} appears twice in the paper; a frozen environment is printed once, at its P1 position` });
      continue;
    }
    seen.add(e.obj_id);
    if (r < maxRank) {
      problems.push({
        gate: "frozen-layer-order",
        objId: e.obj_id,
        detail: `${e.obj_id} appears after ${maxId} in the paper but before it in the frozen layer (P1 order); restore the P1 order`,
      });
      continue;
    }
    maxRank = r;
    maxId = e.obj_id;
  }
  for (const objId of layerOrder) {
    if (!seen.has(objId)) problems.push({
      gate: "frozen-layer-order", objId,
      detail: `${objId} is missing from the paper; every frozen environment must appear at its P1 position`,
    });
  }
  return problems;
}

/** One reader-order constraint: some environment in `homes` must precede `user`, an environment
 *  that uses `symbol` freely. `homes[0]` is the notation table's witnessed home; the rest are
 *  definition-kind environments that visibly introduce the symbol themselves (a displayed
 *  defining equality or an introducing clause) — for the reader either resolves the symbol. */
export interface DefinitionOrderEdge { symbol: string; homes: string[]; user: string }

const INTRODUCER_ENVS = new Set(["definitionv", "algorithmv", "assumptionv", "lemmav"]);

/**
 * The definition-order constraints the notation table imposes on the anchored environments of
 * `tex`: for every row whose home visibly INTRODUCES its symbol (a definition env, a displayed
 * defining equality, defining prose, or an existential binder — a home that merely mentions the
 * symbol is metadata drift, not a constraint), one edge per environment that uses the symbol
 * freely (a decorated variant, a local existential binder, or an introducing clause is not a
 * use). Order-independent: P1's repair solves these (`repairDefinitionOrder`); the same table
 * yields the same constraints whatever order the environments are in.
 */
export function definitionOrderConstraints(tex: string, notation: string): DefinitionOrderEdge[] {
  const envs = scanAnchoredEnvs(tex);
  const byId = new Map(envs.map((e) => [e.obj_id, e]));
  const escapeRe = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const existentiallyIn = (body: string, symbol: string) =>
    new RegExp(String.raw`there\s+(?:exists?|is|are)\b[^.;]{0,80}?` + escapeRe(symbol), "i").test(body);
  const text = (e: AnchoredEnv) => `${e.title ?? ""} ${e.body}`;
  const edges: DefinitionOrderEdge[] = [];
  const seen = new Set<string>();
  for (const { symbol, home } of notationHomes(notation)) {
    const homeEnv = byId.get(home);
    if (!homeEnv || !usesSymbolUndecorated(text(homeEnv), symbol)) continue;
    const witnessed = homeEnv.env === "definitionv" || homeEnv.env === "algorithmv" ||
      displaysDefiningEqualityFamily(homeEnv.body, symbol) ||
      proseDefinesNotation(homeEnv.body, symbol) ||
      existentiallyIn(homeEnv.body.replace(/\s+/g, " "), symbol);
    if (!witnessed) continue;
    const introducers = envs
      .filter((e) => e.obj_id !== home && INTRODUCER_ENVS.has(e.env) &&
        (displaysDefiningEqualityFamily(e.body, symbol) || introducesNotation(e.body, symbol)))
      .map((e) => e.obj_id);
    for (const e of envs) {
      if (e.obj_id === home || introducers.includes(e.obj_id) || !usesSymbolUndecorated(text(e), symbol)) continue;
      if (existentiallyIn(e.body.replace(/\s+/g, " "), symbol) || introducesNotation(e.body, symbol)) continue;
      const key = `${symbol}|${home}|${e.obj_id}`;
      if (seen.has(key)) continue;
      seen.add(key);
      edges.push({ symbol, homes: [home, ...introducers], user: e.obj_id });
    }
  }
  return edges;
}

/** The constraints the current order of `tex` violates (no home precedes the user). Reported
 *  against the table home. */
export function definitionOrderViolations(tex: string, notation: string): DefinitionOrderViolation[] {
  const order = new Map(scanAnchoredEnvs(tex).map((e) => [e.obj_id, e.order] as const));
  return definitionOrderConstraints(tex, notation)
    .filter((e) => e.homes.every((h) => order.get(e.user)! < order.get(h)!))
    .map(({ symbol, homes, user }) => ({ symbol, home: homes[0], firstUse: user }));
}

/** Presentation floor for theorem/lemma STATEMENTS — enforces the two `p1_touchup` formatting rules
 *  the executor sometimes ignores for hypothesis-heavy results, which then ship because the body is
 *  hash-frozen (P2/P3/P4 cannot reformat a frozen statement). A finding makes the P1 router RE-RENDER
 *  before the freeze. Flags: (1) a `\ref`'d assumption whose content is RESTATED inline
 *  ("…\cref{obj:ass:…}, explicitly/namely …") — a `\cref` is sufficient and P3 accepts it as faithful,
 *  so the inline copy is dead weight; (2) several hypothesis conditions run together inline with no
 *  `\begin{itemize}` list. */
export function lintHypothesisPresentation(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  // condition markers: an assumption ref, or a prose hypothesis introducer.
  const COND = /\\(?:Cref|cref|ref)\{[^}]*obj:ass:|\b(?:Assume|Fix|satisfying|provided|such that|eventually in)\b/gi;
  for (const e of parseAnchoredEnvs(tex)) {
    if (e.env !== "theoremv" && e.env !== "lemmav") continue;
    if (/\\(?:Cref|cref|ref)\{[^}]*obj:ass:[^}]*\}[^.]{0,40}?\b(?:explicitly|namely|i\.e\.|that is|which (?:states|requires|reads))\b/i.test(e.body)) {
      problems.push({
        gate: "hypothesis-restated",
        objId: e.obj_id,
        detail: `${e.obj_id}: a referenced assumption is RESTATED inline (e.g. "…\\cref{obj:ass:…}, explicitly …") — reference it by \\cref only and delete the duplicated content; P3 accepts a \\cref'd assumption as faithful.`,
      });
    }
    const conds = (e.body.match(COND) ?? []).length;
    if (conds >= 4 && !/\\begin\{itemize\}/.test(e.body)) {
      problems.push({
        gate: "hypothesis-not-itemized",
        objId: e.obj_id,
        detail: `${e.obj_id}: ${conds} hypothesis conditions are run together inline with no list — set the hypotheses as a \\begin{itemize} (one \\item per condition) before the conclusion.`,
      });
    }
  }
  return problems;
}

export function lintReferences(tex: string): LintProblem[] {
  const problems: LintProblem[] = [];
  const aLabels: number[] = [];
  for (const e of parseAnchoredEnvs(tex)) {
    if (e.env !== "assumptionv") continue;
    const m = (e.title ?? "").match(/\(A(\d+)\)/);
    if (m) aLabels.push(Number(m[1]));
  }
  for (let k = 1; k < aLabels.length; k++) {
    if (aLabels[k] !== aLabels[k - 1] + 1) {
      problems.push({
        gate: "assumption-numbering",
        detail: `assumption A-labels are non-consecutive (…A${aLabels[k - 1]}, A${aLabels[k]}…): the gap makes the printed "Assumption k" disagree with its "(A_j)" label; renumber the assumptions consecutively`,
      });
      break;
    }
  }
  return problems;
}

export function lintCrossRefs(
  tex: string, expected: Map<string, Set<string>>, available: ReadonlySet<string>,
): LintProblem[] {
  const problems: LintProblem[] = [];
  for (const e of parseAnchoredEnvs(tex)) {
    const want = expected.get(e.obj_id) ?? new Set<string>();
    const refs = new Set<string>();
    for (const m of e.body.matchAll(/\\(?:Cref|cref|ref)\{([^}]+)\}/g)) {
      for (const label of m[1].split(",").map((x) => x.trim())) {
        if (label.startsWith("obj:")) refs.add(label.slice(4));
      }
    }
    for (const r of refs) {
      if (!available.has(r)) {
        problems.push({
          gate: "xref-dangling",
          objId: e.obj_id,
          detail: `${e.obj_id}: \\cref{obj:${r}} has no environment in the current paper`,
        });
      }
    }
    for (const t of want) {
      if (!refs.has(t)) {
        // A statement-uses dependency on an ASSUMPTION is a load-bearing hypothesis that MUST be
        // surfaced via \ref (so it is clickable AND so a reader can trace the env's full assumption
        // set) — emit the ENFORCED gate. A missing ref to a def/lemma/theorem may just be named in
        // prose, so it stays advisory (`xref-missing`). This is what makes a bundling definition such
        // as `def:law-class` actually list its constituent assumptions before the body is frozen.
        problems.push({
          gate: t.startsWith("ass:") ? "xref-missing-assumption" : "xref-missing",
          objId: e.obj_id,
          detail: `${e.obj_id}: depends on ${t} (statement-uses) but never references \\cref{obj:${t}}`,
        });
      }
    }
  }
  return problems;
}

export function lintAnchors(
  tex: string,
  knownObjIds: Set<string>,
  frozenBodies: Map<string, string> | null, // obj_id → canonical body; null before the P1 freeze
): LintProblem[] {
  // An anchored environment whose `\end{…v}` is missing is skipped by the scanner, so every
  // consumer would otherwise ignore it while LaTeX runs the environment to the end of the file.
  const opened = [...tex.matchAll(/\\begin\{(theoremv|assumptionv|lemmav|definitionv|citedv|propositionv|remarkv|algorithmv)\}\{([^}]+)\}/g)]
    .filter((m) => !/(?<!\\)(?:\\\\)*%/.test(tex.slice(tex.lastIndexOf("\n", m.index) + 1, m.index)));
  const scanned = scanAnchoredEnvs(tex);
  const unterminated: LintProblem[] = opened.length === scanned.length ? [] : opened
    .filter((m) => !scanned.some((e) => e.start === m.index))
    .map((m) => ({ gate: "unterminated-env", objId: m[2], detail: `${m[2]}: \\begin{${m[1]}} has no matching \\end{${m[1]}}` }));

  const problems: LintProblem[] = [...unterminated];
  BARE_RE.lastIndex = 0;
  let b: RegExpExecArray | null;
  while ((b = BARE_RE.exec(tex))) {
    problems.push({
      gate: "bare-env",
      detail: `unanchored \\begin{${b[1]}} — use ${b[1]}v with an obj_id`,
    });
  }
  for (const e of parseAnchoredEnvs(tex)) {
    if (!knownObjIds.has(e.obj_id)) {
      problems.push({ gate: "unknown-objid", detail: `${e.env}{${e.obj_id}} not in bank crosswalk` });
    }
    if (frozenBodies) {
      const canonical = frozenBodies.get(e.obj_id);
      if (canonical === undefined) {
        problems.push({ gate: "not-frozen", detail: `${e.obj_id} absent from frozen layer` });
      } else if (normalizeBody(canonical) !== normalizeBody(e.body)) {
        problems.push({ gate: "frozen-drift", detail: `${e.obj_id} body differs from frozen layer` });
      }
    }
  }
  return problems;
}

/** Canonical proof-title line: the paper (and the proof-placement lint) identify a proof by
 *  `\\begin{proof}[Proof of \\cref{obj:<id>}]`. Renderers and refiners sometimes emit a
 *  free-form, prefixless, or missing title, leaving a proof a READER cannot attribute —
 *  normalize deterministically at every path that persists proof text. */
export function canonicalizeProofTitle(objId: string, proof: string): string {
  return proof.replace(/^\s*\\begin\{proof\}(\[[^\]]*\])?/, `\\begin{proof}[Proof of \\cref{obj:${objId}}]`);
}
