/** Serialize typed artifacts for model prompts without ambiguous JSON short
 * control escapes. A raw JSON `\n` immediately followed by source text `u` is
 * visually indistinguishable from the TeX command `\nu`; the same ambiguity
 * applies to `\f`/`\frac`. Unicode escapes remain valid JSON and round-trip to
 * exactly the same strings, while making the control boundary explicit. */
export function jsonForModelPrompt(value: unknown): string {
  const json = JSON.stringify(value);
  if (json === undefined) throw new Error("cannot serialize undefined prompt artifact");
  const controlEscapes: Record<string, string> = {
    b: "\\u0008",
    f: "\\u000C",
    n: "\\u000A",
    r: "\\u000D",
    t: "\\u0009",
  };
  let out = "";
  for (let i = 0; i < json.length;) {
    if (json[i] !== "\\") {
      out += json[i++];
      continue;
    }
    let end = i;
    while (json[end] === "\\") end += 1;
    const run = end - i;
    const replacement = controlEscapes[json[end]];
    if (run % 2 === 1 && replacement !== undefined) {
      out += "\\".repeat(run - 1) + replacement;
      i = end + 1;
    } else {
      out += "\\".repeat(run);
      i = end;
    }
  }
  return out;
}
