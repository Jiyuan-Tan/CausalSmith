import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { describe, expect, it } from "vitest";
import { parseLeanDecls } from "../../src/formalization/crosswalk.js";

describe("parseLeanDecls declaration inventory", () => {
  it("detects attributed and non-theorem declarations used by omission guards", async () => {
    const dir = await mkdtemp(join(tmpdir(), "crosswalk-decls-"));
    try {
      await writeFile(join(dir, "Basic.lean"), [
        "@[simp] theorem exactRealAtlas : True := by trivial",
        "class AtlasWitness where",
        "  ok : True",
        "instance atlasWitness : AtlasWitness where",
        "  ok := trivial",
        "opaque hiddenAtlas : Prop",
        "axiom assumedAtlas : Prop",
        "theorem",
        "  multilineAtlas : True := by trivial",
        "theorem «quotedAtlas» : True := by trivial",
      ].join("\n"));
      await mkdir(join(dir, "tmp"));
      await writeFile(join(dir, "tmp", "Main.lean"), "theorem disposableProbe : True := by trivial");
      const names = (await parseLeanDecls(dir, { includeLemmas: true })).map((decl) => decl.name);
      expect(names).toEqual(expect.arrayContaining([
        "exactRealAtlas", "AtlasWitness", "atlasWitness", "hiddenAtlas", "assumedAtlas",
        "multilineAtlas", "quotedAtlas",
      ]));
      expect(names).not.toContain("disposableProbe");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("parses every declaration under a module public section", async () => {
    const dir = await mkdtemp(join(tmpdir(), "crosswalk-module-decls-"));
    try {
      await writeFile(join(dir, "Basic.lean"), [
        "module",
        "/-! Module-style fixture. -/",
        "@[expose] public section",
        "def p1_model : Nat := 1",
        "theorem t1_main : True := by trivial",
        "lemma l1_step : True := by trivial",
      ].join("\n"));
      const decls = await parseLeanDecls(dir, { includeLemmas: true });
      expect(decls).toHaveLength(3);
      expect(decls.map((decl) => decl.name)).toEqual(["p1_model", "t1_main", "l1_step"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
