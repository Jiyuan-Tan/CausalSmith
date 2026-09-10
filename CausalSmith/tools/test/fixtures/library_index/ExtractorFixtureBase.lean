namespace ExtractorRangeFixture

/-- An authored alias used as a namespace in this module and another module. -/
def Alias := Nat

namespace Alias

/-- An authored declaration nested under a definition namespace. -/
def authored : Nat := 7

end Alias

/-- A function whose local recursion generates a contained `recurse.go` worker. -/
def recurse (xs : List Nat) : Nat :=
  let rec go (ys : List Nat) : Nat :=
    match ys with
    | [] => 0
    | _ :: tail => go tail
  go xs

/-- Derivation creates an instance and its nested representation worker. -/
inductive Direction where
  | left
  | right
  deriving Repr

/-- A second derivation whose rangeless match worker later receives only an `add_decl_doc` range. -/
inductive DocumentedDirection where
  | north
  | south
  deriving Repr

/-- This must not turn the generated match worker into an authored declaration. -/
add_decl_doc instReprDocumentedDirection.repr.match_1

end ExtractorRangeFixture
