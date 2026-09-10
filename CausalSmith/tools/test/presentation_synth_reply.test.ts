import { describe, it, expect } from "vitest";
import { parseSynthReply } from "../src/presentation/synth_reply.js";

describe("parseSynthReply", () => {
  it("reads delimited blocks with raw LaTeX, where JSON escaping would have mangled \\ne", () => {
    const out = parseSynthReply([
      "Here are the definitions.",
      "@@@DEF@@@", "SYMBOLS: c; \\mathcal C_K", "TITLE: Zero-sum contrasts", "@@@BODY@@@",
      "A contrast is a vector \\(c \\ne 0\\) with \\(\\sum_k c_k = 0\\).", "@@@END@@@",
      "@@@DEF@@@", "SYMBOLS: \\tau_c", "@@@BODY@@@", "Write \\(\\tau_c := \\langle c, \\mu\\rangle\\).", "@@@END@@@",
    ].join("\n"));
    expect(out).toEqual([
      { symbols: ["c", "\\mathcal C_K"], title: "Zero-sum contrasts", body: "A contrast is a vector \\(c \\ne 0\\) with \\(\\sum_k c_k = 0\\)." },
      { symbols: ["\\tau_c"], title: undefined, body: "Write \\(\\tau_c := \\langle c, \\mu\\rangle\\)." },
    ]);
  });
  it("still accepts a JSON array from a reply that ignored the format, and rejects anything else", () => {
    expect(parseSynthReply('[{"symbols":["x"],"body":"b"}]')).toEqual([{ symbols: ["x"], title: undefined, body: "b" }]);
    expect(parseSynthReply("no definitions here")).toBeNull();
    expect(parseSynthReply("@@@DEF@@@\nSYMBOLS: x\n@@@BODY@@@\ncut @@@END@@@ here\n@@@END@@@")).toBeNull(); // a sentinel in a body never ships truncated
  });
});
