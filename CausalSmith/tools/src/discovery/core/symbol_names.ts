// Symbol-name normalization shared by every place that compares a node's declared
// `free_symbols` against `symbols[].name`: the G1 structural gate (`core/gate.ts`),
// symbol invalidation (`vcs/validity.contentClosure`) and the PR converter.

/** Strip the `\( \)` / `$ $` delimiters and surrounding space so `\(t_\pi\)` and
 *  `t_\pi` compare equal. Exported because symbol invalidation
 *  (`vcs/validity.contentClosure`) must compare a node's declared `free_symbols`
 *  against `symbols[].name` under exactly this equality — cores really do declare the
 *  same symbol in both styles, and a delimiter-only mismatch there would silently
 *  UNDER-invalidate. */
export function normalizeSymbol(raw: string): string {
  return raw
    .trim()
    .replace(/^\\\(|\\\)$/g, "")
    .replace(/^\$+|\$+$/g, "")
    .trim();
}
