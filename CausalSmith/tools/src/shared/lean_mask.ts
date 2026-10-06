// Import-free on purpose: the public site bundles `presentation/lean_decl_name.ts`, and any
// import chain from there into `graph/types.ts` drags zod into the site build, which does not
// declare it (the CI build broke on exactly that, 2026-09-10).
/**
 * Mask Lean comments, strings, and character literals with spaces while preserving byte offsets
 * and newlines. Parser-like consumers can safely scan the result for declaration/delimiter tokens
 * without being fooled by `"/-"`, `"def fake"`, `-- :=`, or brackets in comments.
 */
export function maskLeanCommentsAndStrings(s: string): string {
  let out = "";
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (depth > 0) {
      if (ch === "/" && s[i + 1] === "-") {
        depth++;
        out += "  ";
        i++;
      } else if (ch === "-" && s[i + 1] === "/") {
        depth--;
        out += "  ";
        i++;
      } else out += ch === "\n" ? "\n" : " ";
      continue;
    }
    if (ch === "/" && s[i + 1] === "-") {
      depth = 1;
      out += "  ";
      i++;
      continue;
    }
    if (ch === "-" && s[i + 1] === "-") {
      out += "  ";
      i++;
      while (i + 1 < s.length && s[i + 1] !== "\n") {
        out += " ";
        i++;
      }
      continue;
    }
    if (ch === '"') {
      out += " ";
      for (i++; i < s.length; i++) {
        const q = s[i];
        out += q === "\n" ? "\n" : " ";
        if (q === "\\" && i + 1 < s.length) {
          i++;
          out += s[i] === "\n" ? "\n" : " ";
        } else if (q === '"') break;
      }
      continue;
    }
    if (ch === "'") {
      const escaped = s[i + 1] === "\\" && s[i + 3] === "'";
      const plain = s[i + 1] !== "\\" && s[i + 1] !== undefined && s[i + 2] === "'";
      if (escaped || plain) {
        const end = escaped ? i + 3 : i + 2;
        out += " ".repeat(end - i + 1);
        i = end;
        continue;
      }
    }
    out += ch;
  }
  return out;
}
