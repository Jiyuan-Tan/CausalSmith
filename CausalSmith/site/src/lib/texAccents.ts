/**
 * TeX accents → the Unicode letter, for plain text. BibTeX keeps the accent
 * macro verbatim instead; only the reading form resolves it (audit r4).
 */
const ACCENTS: Record<string, string> = {
  '"a': "\u00e4", '"o': "\u00f6", '"u': "\u00fc", '"A': "\u00c4", '"O': "\u00d6", '"U': "\u00dc",
  '"e': "\u00eb", '"i': "\u00ef", '"y': "\u00ff",
  "'a": "\u00e1", "'e": "\u00e9", "'i": "\u00ed", "'o": "\u00f3", "'u": "\u00fa", "'y": "\u00fd",
  "'A": "\u00c1", "'E": "\u00c9", "'I": "\u00cd", "'O": "\u00d3", "'U": "\u00da", "'c": "\u0107",
  "`a": "\u00e0", "`e": "\u00e8", "`i": "\u00ec", "`o": "\u00f2", "`u": "\u00f9",
  "`A": "\u00c0", "`E": "\u00c8", "`O": "\u00d2",
  "^a": "\u00e2", "^e": "\u00ea", "^i": "\u00ee", "^o": "\u00f4", "^u": "\u00fb",
  "~n": "\u00f1", "~a": "\u00e3", "~o": "\u00f5", "~N": "\u00d1",
  "=a": "\u0101", "=e": "\u0113", "=o": "\u014d", "=u": "\u016b",
  ".z": "\u017c", ".e": "\u0117",
  "cc": "\u00e7", "cC": "\u00c7", "cs": "\u015f",
  "vs": "\u0161", "vc": "\u010d", "vz": "\u017e", "vS": "\u0160", "vC": "\u010c", "vZ": "\u017d",
  "ua": "\u0103", "ug": "\u011f", "Ho": "\u0151", "Hu": "\u0171",
  "ra": "\u00e5", "rA": "\u00c5", "ka": "\u0105", "ke": "\u0119", "lL": "\u0141",
};

/** `\"o` / `\"{o}` / `\c{c}` → the accented letter, or null. */
export function accentedLetter(src: string, i: number): { text: string; end: number } | null {
  const m = /^\\([`'^"~=.]|[uvHcdbkrt])\s*(?:\{([A-Za-z])\}|([A-Za-z]))/.exec(src.slice(i));
  if (!m) return null;
  const letter = m[2] ?? m[3];
  const mapped = ACCENTS[`${m[1]}${letter}`];
  return mapped ? { text: mapped, end: i + m[0].length } : null;
}

/** Resolves every TeX accent macro in a run of `.tex`-sourced prose. */
export function texAccents(s: string): string {
  return s.replace(/\\(?:[`'^"~=.]|[uvHcdbkrt])\s*(?:\{[A-Za-z]\}|[A-Za-z])/g, (m) => accentedLetter(m, 0)?.text ?? m);
}
