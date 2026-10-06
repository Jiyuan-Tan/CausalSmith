import Lean

/-! # Library-index extractor core

Shared by the Causalean `library_index` exe and the CausalSmith `paper_index`
exe: walks an elaborated environment and produces `DeclEntry` records (statement,
source, docstring, refs, axioms) for every non-auxiliary declaration under a
module prefix. -/

open Lean

/-- External (non-Causalean) constant referenced by a statement: name + defining
module, so the site can deep-link into the official Mathlib docs. -/
structure ExtRef where
  n : String
  m : String
  deriving ToJson, FromJson

/-- One binder of a declaration's type, read off the elaborated `Expr` rather
than the pretty-printed statement: the pretty-printer erases the names of
non-dependent explicit binders (`(S : Sys) → …` prints as `Sys → …`), and a
`variable`-introduced section parameter never appears in the authored source
at all. `n` is `""` for a genuinely anonymous binder; `bi` is one of
`explicit` / `implicit` / `inst` / `strict`. -/
structure ParamEntry where
  n : String
  t : String
  bi : String
  deriving ToJson, FromJson

structure DeclEntry where
  name : String
  kind : String
  module : String
  file : String
  line : Nat
  statement : String
  /-- Verbatim source of the declaration: for a `def` the construction after `:=`
  IS the definition; for theorems the slice includes the proof, rendered behind
  an expandable link. Capped at `sourceSliceCap` lines. -/
  source : Option String
  doc : Option String
  refs : Array String
  proofRefs : Array String
  /-- Mathlib/core constants in the statement, for external doc links. -/
  extRefs : Array ExtRef
  axioms : Array String
  usesSorry : Bool
  /-- The type's leading binders in order (see `ParamEntry`). The site uses them
  to show a definition's section variables as parameter rows. -/
  params : Array ParamEntry
  /-- The type's result after all leading binders (a definition's codomain,
  a theorem's goal) — what an authored `abbrev Foo (V) := …` leaves implicit. -/
  result : String
  deriving ToJson, FromJson

def auxSuffixes : List String :=
  ["mk", "rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "ndrec",
   "noConfusion", "noConfusionType", "injEq", "sizeOf_spec", "toCtorIdx",
   "ofNat", "ctorIdx", "ctorElim", "ctorElimType", "ofNat_ctorIdx"]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Column width for pretty-printing statements into the library index. Kept
generous because the site renders statements in a horizontally-scrollable block:
a wide budget keeps logical lines intact instead of collapsing deeply-nested
statements to one or two symbols per line. -/
def stmtPPWidth : Nat := 1000

def moduleToFile (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

def nameComponentStrings : Name → List String
  | .anonymous => []
  | .str p s => nameComponentStrings p ++ [s]
  | .num p n => nameComponentStrings p ++ [toString n]

def declarationLeaf (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => ""

def isAuxiliary (n : Name) : Bool :=
  n.isInternalDetail ||
  n.hasMacroScopes ||
  (nameComponentStrings n |>.any (fun s => s.startsWith "_" || auxSuffixes.contains s)) ||
  match n with
  | .str _ s =>
      auxSuffixes.contains s || s.startsWith "proof_" || s.startsWith "match_"
  | _ => true

def isLibModule (pfx : Name) (m : Name) : Bool :=
  pfx.isPrefixOf m

/-- Module names by module index. `EnvironmentHeader.moduleNames` rebuilds this
array on every call, so the walk computes it once and passes it down. -/
abbrev ModuleNames := Array Name

def moduleNameOf? (mods : ModuleNames) (env : Environment) (n : Name) : Option Name := do
  let midx ← env.getModuleIdxFor? n
  mods[midx.toNat]?

def isLibDecl (mods : ModuleNames) (pfx : Name) (env : Environment) (n : Name) : Bool :=
  match moduleNameOf? mods env n with
  | some m => isLibModule pfx m
  | none => false

def shouldSkipDeclOther (env : Environment) (n : Name) : Bool :=
  isAuxiliary n ||
  env.isConstructor n ||
  env.isProjectionFn n ||
  -- compiler-generated companions namespaced under a constructor (e.g. `BBDir.fromChild.elim`)
  env.isConstructor n.getPrefix

/-- Leaf names of compiler-synthesized companion theorems: `<decl>.congr_simp`
(from `@[congr]`) and the on-demand equation lemmas `<decl>.eq_def`,
`<decl>.eq_unfold`, `<decl>.eq_<i>`.  They have no authored declaration range
or source; the declaration they support is indexed.  Callers that admit
hand-written declarations reusing one of these reserved leaves must pair this
with a declaration-range check (see `entryFor?`). -/
def isSyntheticCompanionLeaf (s : String) : Bool :=
  s == "congr_simp" || s == "eq_def" || s == "eq_unfold" ||
  -- `deriving Fintype, DecidableEq` on a structure emits `<S>.proxyType` /
  -- `<S>.proxyTypeEquiv` with no declaration range; indexing them tripped the
  -- strict paper-index lint (line-zero / null-source) on a correct bundle
  -- (2026-08-26).  Mirrored in `SYNTHETIC_COMPANION_RE` (paper_index_orphans.ts).
  s == "proxyType" || s == "proxyTypeEquiv" ||
  -- functional induction / cases principles that Lean 4.33 realizes for recursive
  -- definitions (`<f>.induct`, `<f>.induct_unfolding`, `<f>.mutual_induct`, `<f>.fun_cases`):
  -- no declaration range or source; surfaced by the module-system migration (2026-09-15).
  s == "induct" || s == "induct_unfolding" || s == "mutual_induct" ||
  s == "fun_cases" || s == "fun_cases_unfolding" ||
  (s.startsWith "eq_" && !(s.drop 3).isEmpty && (s.drop 3).all Char.isDigit)

def shouldSkipDecl (env : Environment) (n : Name) : Bool :=
  -- Private declarations are mangled as `_private.<Module>.0.<Name>` and must never be indexed.
  Lean.isPrivateName n ||
  shouldSkipDeclOther env n ||
  isSyntheticCompanionLeaf (declarationLeaf n)

def uniqueSortedStrings (xs : Array String) : Array String :=
  xs.foldl
      (fun acc x =>
        if acc.contains x then acc else acc.push x)
      #[] |>.qsort (· < ·)

def directUsedConstants (ci : ConstantInfo) : Array Name :=
  let bodyConsts :=
    match ci.value? (allowOpaque := true) with
    | some value => value.getUsedConstants
    | none => #[]
  let inductCtors :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  ci.type.getUsedConstants ++ bodyConsts ++ inductCtors

/-- Non-Causalean statement constants with their defining modules (Mathlib, Std,
Lean core …), deduplicated, skipping auxiliaries and instances. -/
def extRefsFor (mods : ModuleNames) (pfx : Name) (env : Environment) (type : Expr) : Array ExtRef :=
  let seen := type.getUsedConstants.foldl (init := (#[], ({} : NameSet))) fun (acc, s) c =>
    if s.contains c || isAuxiliary c then (acc, s)
    else match moduleNameOf? mods env c with
      | some m =>
        if isLibModule pfx m then (acc, s.insert c)
        else ((acc.push { n := c.toString, m := m.toString }), s.insert c)
      | none => (acc, s.insert c)
  seen.1

def refsFor (mods : ModuleNames) (pfx : Name) (env : Environment) (self : Name) (type : Expr) :
    Array String :=
  type.getUsedConstants.filterMap (fun n =>
    if n == self || shouldSkipDecl env n then
      none
    else
      match moduleNameOf? mods env n with
      | some m =>
          if isLibModule pfx m then
            some n.toString
          else
            none
      | none => none)
  |> uniqueSortedStrings

def proofRefsFor (mods : ModuleNames) (pfx : Name) (env : Environment) (self : Name)
    (stmtRefs : Array String) (val? : Option Expr) : Array String :=
  match val? with
  | none => #[]
  | some v =>
      Id.run do
        let mut out := #[]
        for n in v.getUsedConstantsAsSet do
          if n != self && !shouldSkipDecl env n then
            match moduleNameOf? mods env n with
            | some m =>
                let r := n.toString
                if isLibModule pfx m && !stmtRefs.contains r then
                  out := out.push r
            | none => pure ()
        return uniqueSortedStrings out

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : CoreM (Option String) := do
  match ci with
  | .inductInfo _ =>
      if isClass env n then
        return some "class"
      else if isStructure env n then
        return some "structure"
      else
        return some "inductive"
  | .defnInfo _ =>
      if ← Meta.isInstance n then
        return some "instance"
      else
        return some "def"
  | .thmInfo _ =>
      -- Prop-valued instances compile to theorems; classify them as instances too.
      if ← Meta.isInstance n then
        return some "instance"
      else
        return some "theorem"
  | .axiomInfo _ => return some "axiom"
  | .opaqueInfo _ => return some "opaque"
  | .ctorInfo _ => return none
  | .recInfo _ => return none
  | .quotInfo _ => return none

def lineOfDecl (n : Name) : CoreM Nat := do
  match ← findDeclarationRanges? n with
  | some ranges => return ranges.range.pos.line
  | none => return 0

/-- Source-line cache per module file (read once, sliced per declaration). -/
abbrev FileCache := IO.Ref (NameMap (Array String))

def sourceSliceCap : Nat := 250

/-- Verbatim source slice of a declaration, from its declaration range.

Lean's declaration range starts at the declaration keyword when the declaration
is undocumented, and at the attached doc-comment when it is documented.
Deliberately do not scan backwards for a documentation block here: an undocumented
declaration following a documented neighbour would otherwise inherit that
neighbour's source and docstring.  Docstrings come independently from the
elaborated environment in `entryFor?`. -/
def sourceFor (cache : FileCache) (modName : Name) (srcRoot file : String) (n : Name) :
    CoreM (Option String) := do
  let some ranges ← findDeclarationRanges? n | return none
  let lines ← do
    if let some ls := (← cache.get).find? modName then
      pure ls
    else
      let ls ← (do
        let content ← IO.FS.readFile (srcRoot ++ "/" ++ file)
        pure (content.splitOn "\n").toArray) <|> pure #[]
      cache.modify (·.insert modName ls)
      pure ls
  if lines.isEmpty then return none
  let declLo := ranges.range.pos.line - 1      -- 1-indexed → 0-indexed
  let lo := declLo
  let hi := min ranges.range.endPos.line lines.size
  if lo ≥ hi then return none
  let slice := (Array.range (hi - lo)).map (fun i => lines[lo + i]!)
  let slice := if slice.size > sourceSliceCap then
      (slice.take sourceSliceCap).push "  -- … truncated; follow the source link for the rest …"
    else slice
  return some ("\n".intercalate slice.toList)

/-- `add_decl_doc` installs its command range on an otherwise rangeless declaration.
Such a range documents a generated constant; it is not an authored declaration. -/
def isAddedDocRangeSource (source : String) : Bool :=
  match source.splitOn "\n" |>.reverse |>.find? (fun line => line.trimAscii.toString != "") with
  | some line => line.trimAscii.toString.startsWith "add_decl_doc "
  | none => false

/-- Non-standard axioms `n` depends on through library declarations, with the
depth of the shallowest declaration on the current path that the walk was cut
at (`none` when no cut reached above `n`). Dependency cycles exist (an inductive
and its constructors), so a result is memoized only when it is complete, that
is, when no cut beneath `n` points strictly above `n`; a result truncated by a
cut is valid for the current path alone. -/
partial def axiomStringsGo (mods : ModuleNames) (pfx : Name)
    (cache : IO.Ref (NameMap (Array String))) (path : NameMap Nat) (n : Name) :
    CoreM (Array String × Option Nat) := do
  if let some cached := (← cache.get).find? n then
    return (cached, none)
  if let some depth := path.find? n then
    return (#[], some depth)
  let env ← getEnv
  let depth := path.size
  let (result, cut) ←
    match env.find? n with
    | none => pure (#[], none)
    | some (.axiomInfo _) =>
        if standardAxioms.contains n then
          pure (#[], none)
        else
          pure (#[n.toString], none)
    | some ci =>
        if !isLibDecl mods pfx env n then
          pure (#[], none)
        else
          let mut out := #[]
          let mut cut : Option Nat := none
          for used in directUsedConstants ci do
            let (xs, c) ← axiomStringsGo mods pfx cache (path.insert n depth) used
            out := out ++ xs
            cut := match cut, c with
              | some a, some b => some (min a b)
              | some a, none => some a
              | none, c => c
          pure (uniqueSortedStrings out, cut)
  -- A cut at `n` itself or below it is closed within `n`'s own walk.
  let above := cut.filter (· < depth)
  if above.isNone then
    cache.modify (·.insert n result)
  return (result, above)

def axiomStringsFor (mods : ModuleNames) (pfx : Name)
    (cache : IO.Ref (NameMap (Array String))) (n : Name) : CoreM (Array String) :=
  return (← axiomStringsGo mods pfx cache {} n).1

/-- The fields of an entry that are expensive to derive. `entryFor?` takes them
from the previous run for a declaration whose module key (`moduleKeys`) is
unchanged, and derives them here otherwise. -/
structure DerivedFields where
  statement : String
  params : Array ParamEntry
  result : String
  axioms : Array String
  refs : Array String
  proofRefs : Array String
  extRefs : Array ExtRef

/-- Entries of the previous run whose module key still matches, by declaration name. -/
abbrev ReuseMap := Std.HashMap String DeclEntry

def derivedFieldsFor (mods : ModuleNames) (pfx : Name)
    (axiomCache : IO.Ref (NameMap (Array String))) (ci : ConstantInfo) : CoreM DerivedFields := do
  let env ← getEnv
  let n := ci.name
  let fmt ← Meta.MetaM.run' <|
    withOptions
      (fun opts =>
        opts
          |>.setBool `pp.deepTerms true
          |>.set `pp.maxSteps (200000 : Nat))
      (Meta.ppExpr ci.type)
  -- Pretty-print at a generous width: the site shows statements in a
  -- horizontally-scrollable block, so we want the pretty-printer to keep each
  -- logical line intact rather than break deeply-nested statements down to one
  -- or two symbols per line (indentation alone exhausts a narrow width).
  let statement := fmt.pretty (width := stmtPPWidth)
  let statement ←
    if statement.contains '⋯' then
      let fmt ← Meta.MetaM.run' <|
        withOptions
          (fun opts =>
            opts
              |>.setBool `pp.deepTerms true
              |>.set `pp.maxSteps (200000 : Nat)
              |>.set `pp.proofs.threshold (200000 : Nat))
          (Meta.ppExpr ci.type)
      pure (fmt.pretty (width := stmtPPWidth))
    else
      pure statement
  -- Fail-safe: a binder whose type resists pretty-printing must not cost the
  -- whole index; the site degrades to "no section variables" for that decl.
  let params ← try
      Meta.MetaM.run' <|
        withOptions
          (fun opts => opts |>.setBool `pp.deepTerms true |>.set `pp.maxSteps (200000 : Nat)) <|
          Meta.forallTelescope ci.type fun fvars _ => do
            fvars.mapM fun fv => do
              let decl ← fv.fvarId!.getDecl
              let t ← Meta.ppExpr decl.type
              let name := decl.userName
              pure { n := if name.hasMacroScopes then "" else name.toString
                     t := t.pretty (width := stmtPPWidth)
                     bi := match decl.binderInfo with
                       | .default => "explicit"
                       | .implicit => "implicit"
                       | .instImplicit => "inst"
                       | .strictImplicit => "strict" : ParamEntry }
    catch _ => pure #[]
  let result ← try
      Meta.MetaM.run' <|
        withOptions
          (fun opts => opts |>.setBool `pp.deepTerms true |>.set `pp.maxSteps (200000 : Nat)) <|
          Meta.forallTelescope ci.type fun _ body => do
            pure ((← Meta.ppExpr body).pretty (width := stmtPPWidth))
    catch _ => pure ""
  let axioms ← axiomStringsFor mods pfx axiomCache n
  let refs := refsFor mods pfx env n ci.type
  let proofRefs := proofRefsFor mods pfx env n refs ci.value?
  return { statement, params, result, axioms, refs, proofRefs
           extRefs := extRefsFor mods pfx env ci.type }

def entryFor? (mods : ModuleNames) (pfx : Name) (srcRoot : String)
    (axiomCache : IO.Ref (NameMap (Array String))) (fileCache : FileCache)
    (reuse : ReuseMap) (ci : ConstantInfo) : CoreM (Option DeclEntry) := do
  let env ← getEnv
  let n := ci.name
  if !isLibDecl mods pfx env n || shouldSkipDeclOther env n then
    return none
  let isSynthetic := isSyntheticCompanionLeaf (declarationLeaf n)
  if isSynthetic && (← findDeclarationRanges? n).isNone then
    return none
  let some moduleName := moduleNameOf? mods env n
    | return none
  let some kind ← kindOf env n ci
    | return none
  let nestedDefinition := (kind == "def" || kind == "instance") &&
    match env.find? n.getPrefix with
    | some (.defnInfo _) => true
    | _ => false
  if nestedDefinition then
    -- A type alias can also be an authored namespace. Only a missing range or
    -- a range inside the parent declaration identifies a generated/local worker.
    let some child ← findDeclarationRanges? n | return none
    if moduleNameOf? mods env n.getPrefix == some moduleName then
      if let some parent ← findDeclarationRanges? n.getPrefix then
        if !Position.lt child.range.pos parent.range.pos &&
            !Position.lt parent.range.endPos child.range.endPos then
          return none
  let file := moduleToFile moduleName
  let source ← sourceFor fileCache moduleName srcRoot file n
  if isSynthetic || nestedDefinition then
    if let some text := source then
      -- add_decl_doc supplies a range for a generated constant, not authorship.
      if isAddedDocRangeSource text then return none
  let d ← match reuse[n.toString]? with
    | some e =>
        if e.module == moduleName.toString then
          pure { statement := e.statement, params := e.params, result := e.result
                 axioms := e.axioms, refs := e.refs, proofRefs := e.proofRefs
                 extRefs := e.extRefs : DerivedFields }
        else derivedFieldsFor mods pfx axiomCache ci
    | none => derivedFieldsFor mods pfx axiomCache ci
  return some {
    name := n.toString
    kind := kind
    module := moduleName.toString
    file := file
    line := ← lineOfDecl n
    statement := d.statement
    source := source
    doc := ← liftM <| findDocString? env n
    refs := d.refs
    proofRefs := d.proofRefs
    extRefs := d.extRefs
    axioms := d.axioms
    usesSorry := d.axioms.contains "sorryAx"
    params := d.params
    result := d.result
  }

def buildEntries (pfx : Name) (srcRoot : String) (reuse : ReuseMap := {}) :
    CoreM (Array DeclEntry) := do
  let env ← getEnv
  let mods := env.header.moduleNames
  let axiomCache ← liftM <| IO.mkRef ({} : NameMap (Array String))
  let fileCache : FileCache ← liftM <| IO.mkRef ({} : NameMap (Array String))
  let mut entries := #[]
  for (_, ci) in env.constants.toList do
    match ← entryFor? mods pfx srcRoot axiomCache fileCache reuse ci with
    | some entry =>
      entries := entries.push entry
      -- Progress on stderr: callers bound this exe by output inactivity, and a
      -- full walk runs far longer than that bound.
      if entries.size % 500 == 0 then
        liftM (m := IO) <| IO.eprintln s!"library_index: {entries.size} declarations indexed"
    | none => pure ()
  return entries.qsort (fun a b => a.name < b.name)

def gitCommit : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  if out.exitCode == 0 then
    return out.stdout.trimAscii.toString
  else
    throw <| IO.userError s!"git rev-parse HEAD failed: {out.stderr.trimAscii.toString}"

def gitCommitIn (dir : String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"], cwd := dir }
  if out.exitCode == 0 then
    return out.stdout.trimAscii.toString
  else
    throw <| IO.userError s!"git rev-parse HEAD failed: {out.stderr.trimAscii.toString}"

/-! ## Incremental runs

A run with a cache file reuses the derived fields of every declaration whose
module key is unchanged since the previous run. The key of a module combines
the hashes of its own build artifacts (all three olean parts, so a proof-only
or a range-only change counts) and its Lake dependency hash with the keys of
every library module it imports, so it changes whenever anything in the
module's import closure does. The cache is also bound to the extractor binary
and the toolchain. Two things lie outside the key and reach an unchanged
module only on a full run (`LIBRARY_INDEX_FULL` set): pretty-printing reads the
whole environment, so a notation or name alias declared outside a module's
import closure; and a proof-only edit in a non-library dependency, which leaves
that dependency's public olean, and so every dependency hash, unchanged. -/

/-- Lake's recorded hashes for one built module: the three olean parts and the
trace's dependency hash. `none` when any is unreadable. -/
def moduleArtifactKey? (m : Name) (started : Option IO.FS.SystemTime) : IO (Option String) := do
  try
    let olean ← findOLean m
    let base := olean.toString
    let traceFile := (olean.withExtension "trace").toString
    -- The environment was imported after `started`. An artifact written since
    -- then may be newer than what was imported, and keying old content under
    -- its new hashes would keep that content alive; such a module gets no key.
    if let some t0 := started then
      for p in [base, base ++ ".hash", traceFile] do
        if (← System.FilePath.metadata p).modified.sec ≥ t0.sec then return none
    let mut parts := #[]
    for sfx in [".hash", ".server.hash", ".private.hash"] do
      -- A non-`module` file has a single olean; its absent parts key as "-".
      let p := base ++ sfx
      if ← System.FilePath.pathExists p then
        parts := parts.push (← IO.FS.readFile p).trimAscii.toString
      else if sfx == ".hash" then return none
      else parts := parts.push "-"
    let trace ← IO.FS.readFile traceFile
    let .ok j := Json.parse trace | return none
    let .ok dep := j.getObjValAs? String "depHash" | return none
    return some ("|".intercalate (parts.push dep).toList)
  catch _ => return none

/-- Server-clock time at the start of a run: the modification time of a marker
file written next to the cache, so it is comparable with artifact times on the
same filesystem. -/
def startMark (cachePath : String) : IO IO.FS.SystemTime := do
  if let some parent := (System.FilePath.mk cachePath).parent then
    IO.FS.createDirAll parent
  let marker := cachePath ++ ".started"
  -- Fresh content each run, so the write always advances the modification time.
  IO.FS.writeFile marker (toString (← IO.monoNanosNow))
  return (← System.FilePath.metadata marker).modified

/-- Key of every library module: its own artifact key joined with the keys of
the library modules it imports. A module without a key leaves every module that
imports it without one. -/
def moduleKeys (pfx : Name) (env : Environment) (started : Option IO.FS.SystemTime) :
    IO (NameMap String) := do
  let names := env.header.moduleNames
  let mut keys : NameMap String := {}
  -- `moduleNames` lists a module after everything it imports.
  for i in [0:names.size] do
    let m := names[i]!
    if !isLibModule pfx m then continue
    let some own ← moduleArtifactKey? m started | continue
    let mut acc := some own
    let imports := (env.header.moduleData[i]!.imports.map (·.module)).qsort
      (·.toString < ·.toString)
    for imp in imports do
      if isLibModule pfx imp then
        match acc, keys.find? imp with
        | some a, some k => acc := some (toString (mixHash (hash a) (hash k)))
        | _, _ => acc := none
    if let some a := acc then
      keys := keys.insert m (own ++ "|" ++ a)
  return keys

/-- Identity of this extractor: toolchain plus the bytes of the running binary. -/
def extractorStamp : IO String := do
  let bytes ← IO.FS.readBinFile (← IO.appPath)
  return s!"{Lean.versionString}/{hash bytes}/{bytes.size}"

structure CachedModule where
  key : String
  entries : Array DeclEntry
  deriving ToJson, FromJson

structure IndexCache where
  stamp : String
  pfx : String
  modules : Array (String × CachedModule)
  deriving ToJson, FromJson

/-- The reusable entries of the cache at `path`: those of modules whose key is
unchanged. Empty when the cache is absent, unreadable, or from another extractor. -/
def loadReuse (path : String) (pfx : Name) (stamp : String) (keys : NameMap String) :
    IO ReuseMap := do
  if (← IO.getEnv "LIBRARY_INDEX_FULL").isSome then return {}
  let text ← try IO.FS.readFile path catch _ => return {}
  let .ok j := Json.parse text | return {}
  let .ok (c : IndexCache) := fromJson? j | return {}
  if c.stamp != stamp || c.pfx != pfx.toString then return {}
  let mut reuse : ReuseMap := {}
  for (m, cm) in c.modules do
    if keys.find? m.toName == some cm.key then
      for e in cm.entries do
        if e.module == m then reuse := reuse.insert e.name e
  return reuse

def saveCache (path : String) (pfx : Name) (stamp : String) (keys : NameMap String)
    (entries : Array DeclEntry) : IO Unit := do
  let mut byModule : Std.HashMap String (Array DeclEntry) := {}
  for e in entries do
    byModule := byModule.insert e.module ((byModule.getD e.module #[]).push e)
  let modules := keys.foldl (init := #[]) fun acc m k =>
    acc.push (m.toString, { key := k, entries := byModule.getD m.toString #[] : CachedModule })
  let c : IndexCache := { stamp, pfx := pfx.toString, modules }
  if let some parent := (System.FilePath.mk path).parent then
    IO.FS.createDirAll parent
  let tmp := path ++ s!".tmp{← IO.monoNanosNow}"
  IO.FS.writeFile tmp (toJson c).compress
  IO.FS.rename tmp path

/-- Shared driver: import `importRoot`, index every declaration under `pfx`, and
write the JSON index (entries + per-module docs) to `outPath`. -/
-- `extraModules` are imported alongside `importRoot`. For per-paper indexing
-- the paper's own modules are passed here so the index does NOT depend on the
-- paper being wired into `importRoot`'s import graph — an accepted paper that
-- was never added to the package root would otherwise index to 0 declarations
-- (silent empty Formalization page).
unsafe def runIndex (importRoot pfx : Name) (srcRoot outPath : String)
    (extraModules : Array Name := #[]) (cachePath : Option String := none) : IO Unit := do
  initSearchPath (← findSysroot)
  -- Load persistent env extensions (instance attribute, module docs) — without
  -- this every instance classifies as a plain def/theorem.
  enableInitializersExecution
  -- When the paper's own modules are given, import THOSE only — not the package
  -- root, whose import graph may pull in other (possibly unbuilt) papers'
  -- modules and abort the load. The paper modules transitively bring their deps.
  let roots := if extraModules.isEmpty then #[importRoot] else extraModules
  let imports := roots.map (fun m => { module := m : Import })
  -- Taken before the import so `moduleKeys` can tell which artifacts moved under it.
  let started ← match cachePath with
    | some p => some <$> startMark p
    | none => pure none
  let env ← importModules imports {} (trustLevel := 0) (loadExts := true)
  -- Heartbeats count from process start and the default budget is per
  -- elaboration task, not per indexing run: with binder telescopes added the
  -- run exceeds it after a few thousand declarations. Unlimited is right for a
  -- batch exe whose work is bounded by the environment it walks.
  let ctx : Core.Context :=
    { fileName := "<library_index>", fileMap := default, maxHeartbeats := 0 }
  let cstate : Core.State := { env }
  let (stamp, keys, reuse) ← match cachePath with
    | some p => do
        let stamp ← extractorStamp
        let keys ← moduleKeys pfx env started
        pure (stamp, keys, ← loadReuse p pfx stamp keys)
    | none => pure ("", {}, {})
  let (entries, _) ← (buildEntries pfx srcRoot reuse).toIO ctx cstate
  if let some p := cachePath then
    saveCache p pfx stamp keys entries
    let reused := entries.foldl (fun k e => if reuse.contains e.name then k + 1 else k) 0
    IO.eprintln s!"library_index: reused {reused} of {entries.size} declarations"
  let moduleDocs : List (String × Json) :=
    env.header.moduleNames.toList.filterMap fun m =>
      if isLibModule pfx m then
        let doc := (Lean.getModuleDoc? env m).bind (·[0]?) |>.map (·.doc.trimAscii.toString)
        some (m.toString, match doc with | some s => Json.str s | none => Json.null)
      else none
  let json := Json.mkObj [
    ("commit", toJson (← gitCommitIn ".")),
    ("toolchain", toJson s!"leanprover/lean4:v{Lean.versionString}"),
    ("modules", Json.mkObj moduleDocs),
    ("entries", toJson entries)
  ]
  if let some parent := (System.FilePath.mk outPath).parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outPath (json.pretty ++ "\n")
  IO.println s!"library_index: {entries.size} declarations -> {outPath}"
