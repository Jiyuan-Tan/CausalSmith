import LibraryIndexCore

/-! # Statement-scan exe (the promotion gate's statement fingerprints)

Prints, for every declaration of the scanned modules, a structural fingerprint of what it STATES —
a theorem's type; a definition's type and value; a structure's or inductive's type, constructor
types and field names — and the declarations of the scanned packages that statement mentions.
Two scans agree on a declaration's fingerprint exactly when it says the same thing, however it is
proved. `tools/src/substrate/invariance.ts` compares a scan taken when a run is banked with one
taken after a promotion, over the run's declarations and everything their statements use.

    lake exe statement_scan -- --modules M1,M2,… --prefixes P1,P2,… --out <file>

`--modules` are imported (with everything they import); a declaration is reported when its module
name starts with one of `--prefixes`. Output: one JSON object per line,
`{name, kind, stmt_hash, module, deps}`. Run from `CausalSmith/` after the modules are built: the
scan reads compiled modules, at the private level, so the value of a definition that is not exposed
is fingerprinted too.

**Names and dependencies coincide.** A statement mentions a constant either BY NAME or BY CONTENT.
By name: a declaration that has a row of its own under that name (or a constructor or projection
of one); the fingerprint then holds only the name, and `deps` lists the row to look at, so a
change behind the name is found by following `deps`. By content: everything else — a
compiler-generated auxiliary (a matcher, an abstracted proof), a private declaration, a
declaration named like an auxiliary; its own statement is folded into the fingerprint, and what it
mentions is treated the same way. Every in-package constant read by name is therefore a `deps`
entry that has a row; the exe fails if one has none. Constants outside `--prefixes` (Mathlib, core)
are read by name with no entry: the toolchain and Mathlib revision pin them.

The fingerprint sees binder kinds, the order and number of hypotheses, universe levels (by position,
not by name), definition bodies, structure field names and whether a statement is proved or assumed
as an axiom; it does not see binder names, docstrings, attributes, notation, or how a theorem is
proved (a proof by an unfinished placeholder reads like any other: `#print axioms` shows that). -/

open Lean

namespace StatementScan

/-- The user-facing name of a (possibly private) declaration. -/
def userNameOf (n : Name) : Name := (privateToUserName? n).getD n

/-- Whether `n` or a name it sits under is compiler-generated (`f.match_1.splitter`). -/
def hasInternalPrefix : Name → Bool
  | .anonymous => false
  | n@(.str p _) => n.isInternalDetail || hasInternalPrefix p
  | .num _ _ => true

/-- The declaration a constant belongs to: a constructor's inductive, a projection's structure,
otherwise itself. -/
def ownerOf (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) => v.induct
  | _ =>
    match env.getProjectionFnInfo? n with
    | some info =>
      match env.find? info.ctorName with
      | some (.ctorInfo v) => v.induct
      | _ => n
    | none => n

/-- Whether a statement reads `n` by name: its owner is a declaration with a row of its own that
no other declaration can share. See the module docstring. -/
def readByName (env : Environment) (n : Name) : Bool :=
  let o := ownerOf env n
  let u := userNameOf o
  !(isPrivateName o || isAuxiliary u || hasInternalPrefix u ||
      isSyntheticCompanionLeaf (declarationLeaf u) || env.isConstructor o.getPrefix) &&
    match env.find? o with
    | some (.inductInfo _) | some (.defnInfo _) | some (.thmInfo _)
    | some (.axiomInfo _) | some (.opaqueInfo _) => true
    | _ => false

structure Ctx where
  env : Environment
  /-- Whether a constant is declared in one of the scanned packages. -/
  inScope : Name → Bool

structure St where
  /-- Content fingerprints of the constants read by content so far, with what each mentions. -/
  aux : NameMap (UInt64 × NameSet) := {}
  /-- Constants being expanded (a self-referential one is read by name). -/
  busy : NameSet := {}
  /-- Fingerprints of the subterms of the expression in hand, by address. -/
  seen : Std.HashMap USize UInt64 := {}
  /-- The in-scope declarations the statement in hand reads by name. -/
  deps : NameSet := {}

abbrev M := ReaderT Ctx (StateM St)

/-- A universe level, its parameters read by position in `ps`. -/
def levelHash (ps : List Name) : Level → UInt64
  | .zero => 11
  | .succ l => mixHash 13 (levelHash ps l)
  | .max a b => mixHash 17 (mixHash (levelHash ps a) (levelHash ps b))
  | .imax a b => mixHash 19 (mixHash (levelHash ps a) (levelHash ps b))
  | .param n => mixHash 23 (hash (ps.idxOf n))
  | .mvar _ => 29

mutual

/-- A structural fingerprint of `e`: binder kinds count, binder names do not. -/
unsafe def exprHash (ps : List Name) (e : Expr) : M UInt64 := do
  let key := ptrAddrUnsafe e
  if let some h := (← get).seen[key]? then return h
  let h ← match e with
    | .bvar i => pure (mixHash 2 (hash i))
    | .fvar id => pure (mixHash 3 (hash id.name))
    | .mvar id => pure (mixHash 5 (hash id.name))
    | .sort l => pure (mixHash 7 (levelHash ps l))
    | .const n ls => do
      let hn ← constHash n
      pure (ls.foldl (fun a l => mixHash a (levelHash ps l)) (mixHash 31 hn))
    | .app f a => do pure (mixHash 37 (mixHash (← exprHash ps f) (← exprHash ps a)))
    | .lam _ t b bi => do pure (mixHash 41 (mixHash (hash bi) (mixHash (← exprHash ps t) (← exprHash ps b))))
    | .forallE _ t b bi => do pure (mixHash 43 (mixHash (hash bi) (mixHash (← exprHash ps t) (← exprHash ps b))))
    | .letE _ t v b _ => do pure (mixHash 47 (mixHash (← exprHash ps t) (mixHash (← exprHash ps v) (← exprHash ps b))))
    | .lit l => pure (mixHash 53 (hash l))
    | .mdata _ b => exprHash ps b
    | .proj s i b => do
      pure (mixHash 59 (mixHash (← constHash s) (mixHash (hash i) (← exprHash ps b))))
  modify fun s => { s with seen := s.seen.insert key h }
  return h

/-- A constant as a statement mentions it: by name, recording the dependency, or by content. -/
unsafe def constHash (n : Name) : M UInt64 := do
  let env := (← read).env
  let u := userNameOf n
  let byName := hash u
  if readByName env n then
    if (← read).inScope n then modify fun s => { s with deps := s.deps.insert (ownerOf env n) }
    return byName
  if let some (h, d) := (← get).aux.find? n then
    modify fun s => { s with deps := d.foldl (fun acc x => acc.insert x) s.deps }
    return h
  if (← get).busy.contains n then return byName
  let some ci := env.find? n | return byName
  let outer := (← get).deps
  modify fun s => { s with busy := s.busy.insert n, deps := {} }
  let content ← declHash ci
  let h := if u.isInternalDetail then content else mixHash byName content
  let d := (← get).deps
  modify fun s => { s with busy := s.busy.erase n, aux := s.aux.insert n (h, d),
                           deps := d.foldl (fun acc x => acc.insert x) outer }
  return h

/-- What `ci` states: a theorem's type; an axiom's type, marked as assumed; an inductive's type,
parameter count, constructor types and field names; otherwise the type and, when there is one, the
value. -/
unsafe def declHash (ci : ConstantInfo) : M UInt64 := do
  let outer := (← get).seen
  modify fun s => { s with seen := {} }
  let ps := ci.levelParams
  let one (e : Expr) : M UInt64 := do
    -- addresses are only comparable inside one expression read under one `ps`
    modify fun s => { s with seen := {} }
    exprHash ps e
  let ty ← one ci.type
  let h ← match ci with
    | .thmInfo _ => pure ty
    | .axiomInfo _ => pure (mixHash 61 ty)
    | .inductInfo v => do
      let mut acc := mixHash ty (hash v.numParams)
      for k in v.ctors do
        if let some kci := (← read).env.find? k then
          modify fun s => { s with seen := {} }
          acc := mixHash acc (← exprHash kci.levelParams kci.type)
      -- a structure's field names and default values are part of what it says
      for f in (getStructureInfo? (← read).env v.name).map (·.fieldNames) |>.getD #[] do
        acc := mixHash acc (hash f)
        if let some dci := (← read).env.find? (v.name ++ f ++ `_default) then
          acc := mixHash acc (← declHash dci)
      pure acc
    | _ => match ci.value? (allowOpaque := true) with
      | some v => do pure (mixHash ty (← one v))
      | none => pure ty
  modify fun s => { s with seen := outer }
  return mixHash (hash ps.length) h

end

/-- Whether `n` is a declaration the scan reports on its own (not an auxiliary, constructor,
projection or compiler-generated companion). -/
def isReported (env : Environment) (n : Name) (ci : ConstantInfo) : CoreM (Option String) := do
  let u := userNameOf n
  if isAuxiliary u || hasInternalPrefix u || env.isConstructor n || env.isProjectionFn n || env.isConstructor n.getPrefix then
    return none
  if isSyntheticCompanionLeaf (declarationLeaf u) && (← findDeclarationRanges? n).isNone then
    return none
  kindOf env n ci

def splitNames (s : String) : Array Name :=
  s.splitOn "," |>.filterMap (fun x =>
    let t := x.trimAscii.toString
    if t.isEmpty then none else some t.toName) |>.toArray

end StatementScan

open StatementScan in
unsafe def main (args : List String) : IO Unit := do
  let get (flag : String) : Option String := do
    let i ← args.idxOf? flag
    args[i + 1]?
  let usage := "usage: statement_scan --modules m1,m2,… --prefixes p1,p2,… --out <path>"
  let some out := get "--out" | throw <| IO.userError usage
  let some mods := get "--modules" | throw <| IO.userError usage
  let some pfxs := get "--prefixes" | throw <| IO.userError usage
  let imports := splitNames mods
  let prefixes := splitNames pfxs
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- The default level is private: definition bodies are read whether or not they are exposed.
  let env ← importModules (imports.map fun m => { module := m : Import }) {} (trustLevel := 0) (loadExts := true)
  let modNames := env.header.moduleNames
  let inScope (n : Name) : Bool :=
    match moduleNameOf? modNames env n with
    | some m => prefixes.any (·.isPrefixOf m)
    | none => false
  let ctx : Core.Context := { fileName := "<statement_scan>", fileMap := default, maxHeartbeats := 0 }
  let run : CoreM (Array (Name × String × ConstantInfo × Name)) := do
    let mut rows := #[]
    for (n, ci) in env.constants.toList do
      if !inScope n then continue
      let some m := moduleNameOf? modNames env n | continue
      let some kind ← isReported env n ci | continue
      rows := rows.push (n, kind, ci, m)
    return rows
  let (rows, _) ← run.toIO ctx { env }
  let rows := rows.qsort fun a b => (userNameOf a.1).toString < (userNameOf b.1).toString
  let rowNames : NameSet := rows.foldl (fun acc r => acc.insert r.1) {}
  let mut st : St := {}
  let mut lines : Array String := #[]
  for (n, kind, ci, m) in rows do
    let (h, st') := (declHash ci).run { env, inScope } |>.run { st with deps := {} }
    st := st'
    let deps := st.deps.toArray.filter (· != n)
    -- names and dependencies coincide: whatever was read by name has a row to follow
    if let some d := deps.find? (!rowNames.contains ·) then
      throw <| IO.userError s!"statement_scan: {n} reads {d} by name, but {d} has no row"
    lines := lines.push <| (Json.mkObj [
      ("name", Json.str (toString (userNameOf n))),
      ("kind", Json.str kind),
      ("stmt_hash", Json.str (toString h)),
      ("module", Json.str m.toString),
      ("deps", toJson (deps.map (toString ∘ userNameOf) |>.qsort (· < ·)))]).compress
  if let some parent := (System.FilePath.mk out).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"statement_scan: {lines.size} declarations -> {out}"
