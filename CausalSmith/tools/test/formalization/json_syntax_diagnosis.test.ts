import { describe, expect, it } from "vitest";
import { describeJsonSyntaxError } from "../../src/formalization/stage1.js";

describe("describeJsonSyntaxError", () => {
  it("names the mismatched pair by line, ignoring brackets inside strings", () => {
    const text = '{\n  "a": "x ] y",\n  "nodes": {\n    "n1": {"k": 1}\n  ],\n  "b": 2\n}';
    expect(describeJsonSyntaxError(text)).toBe("opened `{` at line 3, closed by `]` at line 5");
  });
  it("returns null when brackets balance", () => {
    expect(describeJsonSyntaxError('{"a": [1, 2, {"b": "}"}]}')).toBeNull();
  });
  it("reports an unclosed opener", () => {
    expect(describeJsonSyntaxError('{"a": [1, 2')).toBe("unclosed `[` opened at line 1");
  });
});
