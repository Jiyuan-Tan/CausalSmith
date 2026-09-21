/**
 * Lean surface-syntax patterns shared by every tool that reads Lean source with regexes.
 *
 * Single source of truth for the module-system keyword set: the `module` header line,
 * `public`/`meta` import modifiers, `public section`, and `@[expose]`. Under `module`, a
 * declaration with no modifier is PRIVATE unless it sits inside a `public section`; in a
 * legacy (non-module) file it is public unless marked `private`. Every parser that used to
 * hand-roll `noncomputable|private|protected|...` must import these instead, so the keyword
 * set changes in one place.
 */

export const LEAN_DECL_KEYWORDS =
  "def|abbrev|structure|theorem|lemma|class|instance|inductive|irreducible_def|opaque|axiom|constant|example";

/** Declaration modifiers that may precede a declaration keyword (module-system aware). */
export const LEAN_DECL_MODIFIERS =
  "noncomputable|private|protected|public|meta|scoped|local|partial|unsafe|nonrec";

/** Zero or more `@[...]` attribute groups (covers `@[expose]`, `@[simp]`, ...). */
export const LEAN_ATTRS_PREFIX_SRC = String.raw`(?:@\[[^\]]*\][ \t\r\n]*)*`;

/** Zero or more modifier words, each followed by whitespace. */
export const LEAN_MODIFIERS_PREFIX_SRC = String.raw`(?:(?:${LEAN_DECL_MODIFIERS})\s+)*`;

/** Anchored declaration header: attrs, modifiers, then the keyword in group 1. */
export const LEAN_DECL_HEADER_SRC = String.raw`^[ \t]*${LEAN_ATTRS_PREFIX_SRC}${LEAN_MODIFIERS_PREFIX_SRC}(${LEAN_DECL_KEYWORDS})\b`;

export const LEAN_DECL_HEADER_RE = new RegExp(LEAN_DECL_HEADER_SRC);
export const LEAN_DECL_HEADER_RE_GM = new RegExp(LEAN_DECL_HEADER_SRC, "gm");

/** An anonymous `instance` header: unlike a named declaration, the next token is a binder or `:`. */
export const LEAN_ANON_INSTANCE_HEADER_SRC =
  String.raw`^[ \t]*${LEAN_ATTRS_PREFIX_SRC}${LEAN_MODIFIERS_PREFIX_SRC}instance\s*(?:\{|\[|\(|:)`;
export const LEAN_ANON_INSTANCE_HEADER_RE = new RegExp(LEAN_ANON_INSTANCE_HEADER_SRC);

/** One import line; group 1 = module name. Accepts `import`, `public import`, `meta import`,
 * `public meta import`, `import all`. */
// A module name is dot-separated components; a component is either a bare identifier or a
// guillemet-quoted `«…»` run, which may contain spaces and dots.
export const LEAN_IMPORT_SRC = String.raw`^[ \t]*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?((?:«[^»\n]*»|[\p{L}\p{N}_'!?])+(?:\.(?:«[^»\n]*»|[\p{L}\p{N}_'!?])+)*)`;
export const LEAN_IMPORT_RE = new RegExp(LEAN_IMPORT_SRC, "u");
export const LEAN_IMPORT_RE_GM = new RegExp(LEAN_IMPORT_SRC, "gmu");

/** `section` / `noncomputable section` / `public section` / `@[expose] public section`. */
export const LEAN_SECTION_SRC = String.raw`^[ \t]*${LEAN_ATTRS_PREFIX_SRC}(?:public\s+)?(?:noncomputable\s+)?section\b`;
export const LEAN_SECTION_RE = new RegExp(LEAN_SECTION_SRC);

/** Top-level commands whose text can affect elaboration of later declarations. Imports and
 * sections use their dedicated shared patterns so module-system modifiers cannot drift. */
export const LEAN_COMMAND_SRC = String.raw`(?:${LEAN_SECTION_SRC}|${LEAN_IMPORT_SRC}|^[ \t]*(?:module|variable|open|universe|set_option|notation|infix[lr]?|prefix|postfix|local|scoped|attribute|namespace|end|omit|include|macro|macro_rules|syntax|elab|export)\b)`;
export const LEAN_COMMAND_RE = new RegExp(LEAN_COMMAND_SRC, "u");

/** A bare `module` header line (optionally with a trailing `--` comment). */
export const LEAN_MODULE_LINE_RE = /^[ \t]*module[ \t]*(?:--.*)?$/;

export interface LeanImport {
  module: string;
  isPublic: boolean;
  isMeta: boolean;
  importAll: boolean;
}

/** Parse one line as an import; null when it is not an import line. */
export function parseLeanImport(line: string): LeanImport | null {
  const m = LEAN_IMPORT_RE.exec(line);
  if (!m) return null;
  const head = line.slice(0, m.index + m[0].length);
  return {
    module: m[1],
    isPublic: /\bpublic\s+(?:meta\s+)?import\b/.test(head),
    isMeta: /\bmeta\s+import\b/.test(head),
    importAll: /\bimport\s+all\s/.test(head),
  };
}

export function isLeanImportLine(line: string): boolean {
  return LEAN_IMPORT_RE.test(line);
}

/** Extended-regexp pattern for `git grep -E` declaration candidate searches. */
export function leanDeclarationGrepPattern(name: string): string {
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return `^(@\\[[^]]*\\] *)*((${LEAN_DECL_MODIFIERS}) )*(${LEAN_DECL_KEYWORDS}) ${escaped}\\b`;
}

/** True when the file opts into the module system: its first non-blank, non-comment line is
 * `module`. Handles a leading `/- ... -/` block comment and `--` line comments. */
export function isLeanModuleFile(source: string): boolean {
  let i = 0;
  const n = source.length;
  while (i < n) {
    while (i < n && /\s/.test(source[i])) i++;
    if (source.startsWith("/-", i)) {
      let depth = 0;
      while (i < n) {
        if (source.startsWith("/-", i)) { depth++; i += 2; continue; }
        if (source.startsWith("-/", i)) { depth--; i += 2; if (depth === 0) break; continue; }
        i++;
      }
      continue;
    }
    if (source.startsWith("--", i)) {
      while (i < n && source[i] !== "\n") i++;
      continue;
    }
    break;
  }
  const lineEnd = source.indexOf("\n", i);
  const line = source.slice(i, lineEnd === -1 ? n : lineEnd);
  return LEAN_MODULE_LINE_RE.test(line);
}

/** True iff `offset` lies inside a `public section` frame, a blanket unclosed one counting to EOF. */
export function publicSectionAt(source: string, offset: number): boolean {
  const frames: Array<{ kind: "namespace" | "section"; public: boolean }> = [];
  for (const line of source.slice(0, Math.max(0, offset)).split(/\r?\n/)) {
    if (/^[ \t]*namespace\b/.test(line)) {
      frames.push({ kind: "namespace", public: false });
      continue;
    }
    const section = LEAN_SECTION_RE.exec(line);
    if (section) {
      frames.push({ kind: "section", public: /(?:^|\s)public\s/.test(section[0]) });
      continue;
    }
    if (/^[ \t]*end\b/.test(line)) frames.pop();
  }
  return frames.some((frame) => frame.kind === "section" && frame.public);
}

/** Visibility of a declaration given its modifier words, whether the file is a module file, and
 * whether the declaration sits inside a `public section`. */
export function isPublicDecl(
  modifiers: string,
  opts: { moduleFile: boolean; inPublicSection: boolean },
): boolean {
  const mods = modifiers.split(/\s+/).filter(Boolean);
  if (mods.includes("private")) return false;
  if (!opts.moduleFile) return true;
  return mods.includes("public") || opts.inPublicSection;
}
