import { describe, expect, it } from "vitest";
import { firstDeclaredLeaf, leanNameLeaf, isPrivateDeclarationSource, leanSourceDeclarations, autoInstanceName } from "../src/presentation/lean_decl_name.js";

describe("firstDeclaredLeaf", () => {
  it("keeps Unicode subscript suffixes that distinguish neighbouring declarations", () => {
    expect(firstDeclaredLeaf("theorem studentizedBaseline_lambda₁ : True := by trivial\n"))
      .toBe("studentizedBaseline_lambda₁");
    expect(firstDeclaredLeaf("theorem studentizedBaseline_lambda₂ : True := by trivial\n"))
      .toBe("studentizedBaseline_lambda₂");
  });

  it("accepts Unicode letters, combining marks, and qualified names", () => {
    expect(firstDeclaredLeaf("noncomputable def Model.α₂ : Nat := 2\n")).toBe("α₂");
    expect(firstDeclaredLeaf("lemma cafe\u0301₃ : True := by trivial\n")).toBe("cafe\u0301₃");
  });

  it("keeps quoted identifiers whole and skips a leading block comment", () => {
    const source = "/-- neighbouring documentation -/\ntheorem «name with spaces₄» : True := by trivial\n";
    expect(firstDeclaredLeaf(source)).toBe("«name with spaces₄»");
  });

  it("splits qualified names only at dots outside quoted components", () => {
    expect(firstDeclaredLeaf("theorem «name.with.dot» : True := by trivial\n")).toBe("«name.with.dot»");
    expect(firstDeclaredLeaf("theorem Model.«name with spaces₄» : True := by trivial\n"))
      .toBe("«name with spaces₄»");
    expect(leanNameLeaf("Outer.«inner.with.dot»")).toBe("«inner.with.dot»");
  });

  it("recognizes repeated attributes and a name on the next line", () => {
    expect(firstDeclaredLeaf("@[simp] @[aesop safe] theorem marked₂ : True := by trivial\n"))
      .toBe("marked₂");
    expect(firstDeclaredLeaf("theorem\n  nextLine₃ : True := by trivial\n")).toBe("nextLine₃");
  });

  it("skips comments between the command and declaration name", () => {
    expect(firstDeclaredLeaf("theorem /- ownership note -/ between₂ : True := by trivial\n"))
      .toBe("between₂");
    expect(firstDeclaredLeaf("theorem -- ownership note\n afterLineComment₃ : True := by trivial\n"))
      .toBe("afterLineComment₃");
  });

  it("recognizes nonrec declarations, axioms, and constants", () => {
    expect(firstDeclaredLeaf("nonrec theorem shadowed₄ : True := by trivial\n")).toBe("shadowed₄");
    expect(firstDeclaredLeaf("axiom citedGate₅ : True\n")).toBe("citedGate₅");
    expect(firstDeclaredLeaf("constant population₆ : Type\n")).toBe("population₆");
  });
});


describe("isPrivateDeclarationSource", () => {
  it("recognizes private modifiers through documentation, attributes and other modifiers", () => {
    expect(isPrivateDeclarationSource("/-- Source-local helper. -/\n@[simp] private noncomputable def hidden : Nat := 1")).toBe(true);
    expect(isPrivateDeclarationSource("noncomputable private def hidden : Nat := 1")).toBe(true);
    expect(isPrivateDeclarationSource("private lemma helper : True := by trivial")).toBe(true);
  });
  it("does not infer privacy from comments, attributes or quoted commands", () => {
    expect(isPrivateDeclarationSource("/-- Calls a private helper. -/\n@[privateHint] protected def visible : Nat := 1")).toBe(false);
    expect(isPrivateDeclarationSource("def quoted := `(private def hidden : Nat := 1)")).toBe(false);
    expect(isPrivateDeclarationSource("/-- private def hidden -/")).toBe(false);
  });
});

describe("anonymous instances carry Lean's auto-generated name", () => {
  it("names an instance from the constants of its result type, skipping binder variables", () => {
    const src = [
      "namespace M",
      "instance {n : ℕ} {G : Causalean.DAG (Fin n)} : TopologicalSpace (Mechanism n G) :=",
      "  TopologicalSpace.induced mechanismC2Coordinates inferInstance",
      "instance : Fintype (Fin n × Bool) := inferInstance",
      "noncomputable instance named : Inhabited ℝ := ⟨0⟩",
      "end M",
    ].join("\n");
    expect(leanSourceDeclarations(src).map((d) => [d.name, d.line, d.kind])).toEqual([
      ["instTopologicalSpaceMechanism", 2, "instance"],
      ["instFintypeProdFinBool", 4, "instance"],
      ["named", 5, "instance"],
    ]);
  });
  it("suffixes a repeated auto name the way Lean does", () => {
    const src = "instance : Inhabited Foo := ⟨a⟩\ninstance : Inhabited Foo := ⟨b⟩\n";
    expect(leanSourceDeclarations(src).map((d) => d.name)).toEqual(["instInhabitedFoo", "instInhabitedFoo_1"]);
  });
  it("returns nothing for an instance whose result type it cannot read", () => {
    expect(autoInstanceName("instance := foo", "instance".length)).toBeNull();
  });
});
