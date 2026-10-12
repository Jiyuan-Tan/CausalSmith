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

/** Whether a declared symbol visibly occurs in TeX text, by its name or its normalized form.
 * A one- or two-letter alphanumeric name (`n`, `p`, `X1`) occurs inside almost any TeX string,
 * so it matches only as a standalone token (a following `_` subscript still counts). */
export function symbolOccursIn(text: string, name: string): boolean {
  const occurs = (needle: string): boolean => {
    if (needle.length === 0) return false;
    if (needle.length > 2 || !/^[A-Za-z0-9]+$/.test(needle)) return text.includes(needle);
    return new RegExp(`(?<![A-Za-z0-9\\\\])${needle}(?![A-Za-z0-9])`).test(text);
  };
  return occurs(name) || occurs(normalizeSymbol(name));
}
