import CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier_Research.Basic.Completion
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Combinatorics.SimpleGraph.Hall

/-!
# Deletion-rank frontiers and exact certificate output

The exact-real cost model counts field operations and scalar output writes after an exact mixing
matrix has been supplied. It deliberately contains no operation for recovering that matrix from a
probability law.
-/

namespace CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier

open Set
open scoped BigOperators

-- @env: S3
variable {p n : ℕ}
  (C : MixingMatrix p n) (x : Fin p)

-- @node: def:admissible-source-set
noncomputable def admissibleSources (C : MixingMatrix p n) (x : Fin p) : Finset (Fin n) :=
  Finset.univ.filter fun j => C x j ≠ 0 ∧ (deleteRowCol C x j).rank = p - 1
  -- @realizes Jx(Jx = nonzero treatment loading and deletion rank p-1)

-- @node: def:effect-frontier
def effectFrontier (C : MixingMatrix p n) (x y : Fin p) : Set ℝ :=
  {z | ∃ j ∈ admissibleSources C x, z = C y j / C x j}
  -- @realizes Rxy(effect ratios indexed by Jx)

-- @node: def:response-vector-frontier
def responseFrontier (C : MixingMatrix p n) (x : Fin p) :
    Set ({i : Fin p // i ≠ x} → ℝ) :=
  {z | ∃ j ∈ admissibleSources C x, z = fun i => C i.1 j / C x j}
  -- @realizes Vfront(response vectors indexed by one common j in Jx)

def IsRationalMatrix {a b : ℕ} (A : MixingMatrix a b) : Prop :=
  ∀ i j, ∃ q : ℚ, A i j = q

def rowPermutationMatrix {n : ℕ} (pi : Equiv.Perm (Fin n)) : SquareMatrix n :=
  fun i j => if pi i = j then 1 else 0

noncomputable def inverseDiagonalMatrix {n : ℕ} (d : Fin n → ℝ) : SquareMatrix n :=
  Matrix.diagonal fun i => (d i)⁻¹

def singleEntryMatrix {n : ℕ} (row col : Fin n) (a : ℝ) : SquareMatrix n :=
  fun i j => if i = row ∧ j = col then a else 0

/-- An edge of the bipartite nonzero-pattern graph of the columns of `W₀` other than `x`. -/
def NonzeroPatternEdge {p n : ℕ} {hpn : p ≤ n} {x : Fin p} (W0 : SquareMatrix n)
    (row : Fin n) (column : {k : Fin n // k ≠ Fin.castLE hpn x}) : Prop :=
  W0 row column.1 ≠ 0

/-- The shared column-saturating matching and alternating forest computed once from `W₀`. -/
structure SharedMatchingTrace {p n : ℕ} (hpn : p ≤ n) (x : Fin p)
    (W0 : SquareMatrix n) where
  assignedRow : {k : Fin n // k ≠ Fin.castLE hpn x} → Fin n
  injective : Function.Injective assignedRow
  patternEdge : ∀ k, W0 (assignedRow k) k.1 ≠ 0
  unmatchedRow : Fin n
  unmatched : ∀ k, assignedRow k ≠ unmatchedRow
  alternatingParent : Fin n → Option (Fin n)
  alternatingParentColumn : Fin n → Option {k : Fin n // k ≠ Fin.castLE hpn x}
  rootParent : alternatingParent unmatchedRow = none
  parent_pattern : ∀ child parent,
    alternatingParent child = some parent →
      ∃ column, alternatingParentColumn child = some column ∧
        assignedRow column = child ∧ NonzeroPatternEdge W0 parent column

def ConsecutiveInPath {α : Type*} (path : List α) (a b : α) : Prop :=
  ∃ pre suffix, path = pre ++ a :: b :: suffix

def AlternatingForestStep {p n : ℕ} {hpn : p ≤ n} {x : Fin p}
    {W0 : SquareMatrix n} (shared : SharedMatchingTrace hpn x W0)
    (parent child : Fin n) : Prop :=
  shared.alternatingParent child = some parent ∧
    ∃ column, shared.alternatingParentColumn child = some column ∧
      shared.assignedRow column = child ∧ NonzeroPatternEdge W0 parent column

def AlternatingPathInSharedForest {p n : ℕ} {hpn : p ≤ n} {x : Fin p}
    {W0 : SquareMatrix n} (shared : SharedMatchingTrace hpn x W0)
    (path : List (Fin n)) : Prop :=
  path.head? = some shared.unmatchedRow ∧
    path.IsChain (AlternatingForestStep shared)

def MatchingFlipAlongPath {p n : ℕ} {hpn : p ≤ n} {x : Fin p}
    {W0 : SquareMatrix n} (shared : SharedMatchingTrace hpn x W0)
    (j : Fin n) (path : List (Fin n)) (flipped : Equiv.Perm (Fin n)) : Prop :=
  AlternatingPathInSharedForest shared path ∧ path.getLast? = some j ∧
    flipped (Fin.castLE hpn x) = j ∧
    (∀ k : {k : Fin n // k ≠ Fin.castLE hpn x}, W0 (flipped k.1) k.1 ≠ 0) ∧
    (∀ k : {k : Fin n // k ≠ Fin.castLE hpn x},
      flipped k.1 = shared.assignedRow k ∨
        ∃ parent child, ConsecutiveInPath path parent child ∧
          shared.alternatingParentColumn child = some k ∧
          shared.assignedRow k = child ∧ flipped k.1 = parent) ∧
    (∀ parent child, ConsecutiveInPath path parent child →
      ∃ k : {k : Fin n // k ≠ Fin.castLE hpn x},
        shared.alternatingParentColumn child = some k ∧
          shared.assignedRow k = child ∧ flipped k.1 = parent)

abbrev AdmissibleSourceIndex {p n : ℕ} (C : MixingMatrix p n) (x : Fin p) :=
  {j : Fin n // j ∈ admissibleSources C x}

/-- Formal trace of the prescribed shear, matching flip, and displayed `Q_j,H_j` formulas. -/
structure CompletionConstructionTrace {p n : ℕ} (C : MixingMatrix p n) (x : Fin p)
    (hpn : p ≤ n) (T0 W0 : SquareMatrix n) (shared : SharedMatchingTrace hpn x W0)
    (j : AdmissibleSourceIndex C x) where
  flippedAssignment : Equiv.Perm (Fin n)
  alternatingPath : List (Fin n)
  matchingFlip : MatchingFlipAlongPath shared j.1 alternatingPath flippedAssignment
  shearRow : Option {ell : Fin n // p ≤ ell.1}
  shearedBasis : SquareMatrix n
  shearedInverse : SquareMatrix n
  noShear_iff : shearRow = none ↔ W0 j (Fin.castLE hpn x) ≠ 0
  noShear_spec : W0 j (Fin.castLE hpn x) ≠ 0 →
    shearedBasis = T0 ∧ shearedInverse = W0
  guardedShear_spec : W0 j (Fin.castLE hpn x) = 0 →
    ∃ ell : {ell : Fin n // p ≤ ell.1}, shearRow = some ell ∧ W0 j ell.1 ≠ 0 ∧
      shearedBasis = (1 + singleEntryMatrix ell.1 (Fin.castLE hpn x) 1) * T0 ∧
      shearedInverse = W0 * (1 - singleEntryMatrix ell.1 (Fin.castLE hpn x) 1)
  diagonal : Fin n → ℝ
  diagonal_spec : diagonal = fun i =>
    (rowPermutationMatrix flippedAssignment * shearedInverse) i i
  diagonal_nonzero : ∀ i, diagonal i ≠ 0
  Q : SquareMatrix n
  H : SquareMatrix n
  Q_formula : Q = inverseDiagonalMatrix diagonal *
    rowPermutationMatrix flippedAssignment * shearedInverse
  H_formula : H = inverseDiagonalMatrix diagonal * rowPermutationMatrix flippedAssignment

/-- Specification data for the shared basis extension, inverse, matching, and all completion
outputs used by the certificate. -/
structure CertificateData (C : MixingMatrix p n) (x : Fin p) where
  dim_le : p ≤ n
  basisExtension : SquareMatrix n -- @realizes T0(invertible extension of observed rows)
  inverseBasis : SquareMatrix n -- @realizes W0(W0 = T0 inverse)
  inverse_eq : inverseBasis = basisExtension⁻¹
  observedRows : ∀ i j, basisExtension (Fin.castLE dim_le i) j = C i j
  sharedMatching : SharedMatchingTrace dim_le x inverseBasis
  trace : (j : AdmissibleSourceIndex C x) →
    CompletionConstructionTrace C x dim_le basisExtension inverseBasis
    sharedMatching j
  completion : AdmissibleSourceIndex C x → SquareMatrix n × SquareMatrix n
    -- @realizes Cert(one traced pair Qj,Hj for each j in Jx)
  completion_trace : ∀ j, completion j = ((trace j).Q, (trace j).H)
  valid : ∀ j, CompletionFiber C dim_le x (completion j).1 (completion j).2
  assigned : ∀ j,
    assignedSource (completion j).2 (valid j).monomial (Fin.castLE dim_le x) = j.1

lemma certificateData_nonempty (C : MixingMatrix p n) (hC : FullRowRank C) (x : Fin p) :
    Nonempty (CertificateData C x) := by sorry

/-- The shear-and-alternating-matching certificate, selected once so its basis extension, inverse,
matching, and alternating-reachability data are shared across all admissible sources. -/
-- @node: def:witness-algorithm
noncomputable def certifiedCompletion (C : MixingMatrix p n) (x : Fin p)
    (D : CertificateData C x) (j : Fin n) (hj : j ∈ admissibleSources C x) :
    SquareMatrix n × SquareMatrix n :=
  D.completion ⟨j, hj⟩

/-- Register-machine instructions for uniform exact-real computation. Registers may only be made
from entries of the exact input, explicitly supplied shared basis/inverse entries, constants
`0,1`, earlier registers, and exact zero tests. -/
inductive ExactArithmeticInstruction (p n : ℕ) where
  | inputMixing (i : Fin p) (j : Fin n)
  | inputSharedBasis (i j : Fin n)
  | inputSharedInverse (i j : Fin n)
  | zero
  | one
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | mul (a b : ℕ)
  | inv (a : ℕ)
  | isZero (a : ℕ)
  | select (test ifZero ifNonzero : ℕ)

def exactRegisterAt? : List ℝ → ℕ → Option ℝ
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, k + 1 => exactRegisterAt? rest k

noncomputable def ExactArithmeticInstruction.eval {p n : ℕ}
    (C : MixingMatrix p n) (T0 W0 : SquareMatrix n) (registers : List ℝ) :
    ExactArithmeticInstruction p n → Option ℝ
  | .inputMixing i j => some (C i j)
  | .inputSharedBasis i j => some (T0 i j)
  | .inputSharedInverse i j => some (W0 i j)
  | .zero => some 0
  | .one => some 1
  | .add a b => match exactRegisterAt? registers a, exactRegisterAt? registers b with
      | some va, some vb => some (va + vb)
      | _, _ => none
  | .sub a b => match exactRegisterAt? registers a, exactRegisterAt? registers b with
      | some va, some vb => some (va - vb)
      | _, _ => none
  | .mul a b => match exactRegisterAt? registers a, exactRegisterAt? registers b with
      | some va, some vb => some (va * vb)
      | _, _ => none
  | .inv a => (exactRegisterAt? registers a).map Inv.inv
  | .isZero a => (exactRegisterAt? registers a).map fun z => if z = 0 then 1 else 0
  | .select test ifZero ifNonzero =>
      match exactRegisterAt? registers test, exactRegisterAt? registers ifZero,
          exactRegisterAt? registers ifNonzero with
      | some t, some vz, some vn => some (if t = 0 then vz else vn)
      | _, _, _ => none

noncomputable def executeExactFrom {p n : ℕ} (C : MixingMatrix p n)
    (T0 W0 : SquareMatrix n) :
    List (ExactArithmeticInstruction p n) → List ℝ → Option (List ℝ)
  | [], registers => some registers
  | op :: ops, registers =>
      match op.eval C T0 W0 registers with
      | none => none
      | some value => executeExactFrom C T0 W0 ops (registers ++ [value])

noncomputable def executeExact {p n : ℕ} (C : MixingMatrix p n)
    (T0 W0 : SquareMatrix n) (program : List (ExactArithmeticInstruction p n)) :
    Option (List ℝ) :=
  executeExactFrom C T0 W0 program []

/-- A uniform program has fixed code and output-register addresses for each dimension and treatment;
none of these fields may inspect the numerical entries of `C`. -/
structure ExactArithmeticProgram (p n : ℕ) where
  code : List (ExactArithmeticInstruction p n)
  admissibleRegister : Fin n → ℕ
  scalarRatioRegister : Fin p → Fin n → ℕ
  vectorRatioRegister : Fin p → Fin n → ℕ
  witnessQRegister : Fin n → Fin n → Fin n → ℕ
  witnessHRegister : Fin n → Fin n → Fin n → ℕ

def ExactArithmeticProgram.usesOnlyMixingInput (program : ExactArithmeticProgram p n) : Prop :=
  ∀ op ∈ program.code, match op with
    | .inputSharedBasis .. => False
    | .inputSharedInverse .. => False
    | _ => True

noncomputable def ExactArithmeticProgram.outputWrites (_program : ExactArithmeticProgram p n)
    (C : MixingMatrix p n) (x : Fin p) : ℕ :=
  n + p * (admissibleSources C x).card + (p - 1) * (admissibleSources C x).card +
    2 * (admissibleSources C x).card * n * n

noncomputable def ExactArithmeticProgram.cost (program : ExactArithmeticProgram p n)
    (C : MixingMatrix p n) (x : Fin p) : ℕ :=
  program.code.length + program.outputWrites C x

/-- Data-dependent execution/output relation. Every advertised index, ratio, and dense witness
entry must be read from a register produced from the exact input by the uniform program.  The
valid witness family is existentially execution-linked and is the same shared certificate run
whose outputs are exposed by `certifiedCompletion`. -/
def ExactArithmeticProgram.ComputesCertificate (program : ExactArithmeticProgram p n)
    (C : MixingMatrix p n) (_hC : FullRowRank C) (x : Fin p)
    (D : CertificateData C x) : Prop :=
  ∃ registers,
    executeExact C D.basisExtension D.inverseBasis program.code = some registers ∧
    (∀ j, exactRegisterAt? registers (program.admissibleRegister j) =
      some (if j ∈ admissibleSources C x then 1 else 0)) ∧
    (∀ y j (_hj : j ∈ admissibleSources C x),
      exactRegisterAt? registers (program.scalarRatioRegister y j) = some (C y j / C x j)) ∧
    (∀ i j (_hj : j ∈ admissibleSources C x),
      exactRegisterAt? registers (program.vectorRatioRegister i j) = some (C i j / C x j)) ∧
    (∀ j (hj : j ∈ admissibleSources C x),
      (∀ row col,
        exactRegisterAt? registers (program.witnessQRegister j row col) =
            some ((D.completion ⟨j, hj⟩).1 row col) ∧
        exactRegisterAt? registers (program.witnessHRegister j row col) =
            some ((D.completion ⟨j, hj⟩).2 row col)) ∧
      CompletionFiber C D.dim_le x (D.completion ⟨j, hj⟩).1
        (D.completion ⟨j, hj⟩).2 ∧
      assignedSource (D.completion ⟨j, hj⟩).2 (D.valid ⟨j, hj⟩).monomial
        (Fin.castLE D.dim_le x) = j)

structure UniformExactCertificateAlgorithm where
  program : ∀ (p n : ℕ), Fin p → ExactArithmeticProgram p n

def UniformExactCertificateAlgorithm.ComputesCertificate
    (algorithm : UniformExactCertificateAlgorithm) (C : MixingMatrix p n)
    (hC : FullRowRank C) (x : Fin p) (D : CertificateData C x) : Prop :=
  (algorithm.program p n x).ComputesCertificate C hC x D

noncomputable def UniformExactCertificateAlgorithm.cost
    (algorithm : UniformExactCertificateAlgorithm)
    (C : MixingMatrix p n) (x : Fin p) : ℕ :=
  (algorithm.program p n x).cost C x

def IsUniformlyCubicCertificateAlgorithm (algorithm : UniformExactCertificateAlgorithm) : Prop :=
  ∃ c n0 : ℕ, 0 < c ∧ ∀ {p n : ℕ} (C : MixingMatrix p n)
      (_hdim : ValidPopulationDimensions p n) (hC : FullRowRank C)
      (x : Fin p), n0 ≤ n → ∃ D : CertificateData C x,
      (algorithm.program p n x).usesOnlyMixingInput ∧
        algorithm.ComputesCertificate C hC x D ∧
        algorithm.cost C x ≤ c * n ^ 3

/-- The same uniform exact-real cost model restricted to irreducible mixing representatives.
This is the domain used by the law-level sharp-frontier theorem. -/
def IsUniformlyCubicIrreducibleCertificateAlgorithm
    (algorithm : UniformExactCertificateAlgorithm) : Prop :=
  ∃ c n0 : ℕ, 0 < c ∧ ∀ {p n : ℕ} (C : MixingMatrix p n)
      (_hdim : ValidPopulationDimensions p n) (hC : FullRowRank C)
      (_hC0 : NonzeroColumns C) (_hCdir : DistinctDirections C)
      (x : Fin p), n0 ≤ n → ∃ D : CertificateData C x,
      (algorithm.program p n x).usesOnlyMixingInput ∧
        algorithm.ComputesCertificate C hC x D ∧
        algorithm.cost C x ≤ c * n ^ 3

/-- Exact-input conditional cubic all-witness enumeration. The program family is uniform, its
outputs are execution-linked to `C`, and the asymptotic constant and threshold are global. -/
def CubicExactCertificateEnumeration {p n : ℕ} (C : MixingMatrix p n)
    (_hdim : ValidPopulationDimensions p n) (hC : FullRowRank C)
    (x : Fin p) (D : CertificateData C x) : Prop :=
  ∃ algorithm : UniformExactCertificateAlgorithm,
    IsUniformlyCubicCertificateAlgorithm algorithm ∧
    (algorithm.program p n x).usesOnlyMixingInput ∧
    algorithm.ComputesCertificate C hC x D

/-- Exact-input cubic enumeration on the irreducible domain used by the sharp law-level
frontier theorem. -/
def CubicExactIrreducibleCertificateEnumeration {p n : ℕ} (C : MixingMatrix p n)
    (_hdim : ValidPopulationDimensions p n) (hC : FullRowRank C)
    (_hC0 : NonzeroColumns C) (_hCdir : DistinctDirections C) (x : Fin p)
    (D : CertificateData C x) : Prop :=
  ∃ algorithm : UniformExactCertificateAlgorithm,
    IsUniformlyCubicIrreducibleCertificateAlgorithm algorithm ∧
    (algorithm.program p n x).usesOnlyMixingInput ∧
    algorithm.ComputesCertificate C hC x D

/-- Scalar-output cost for two dense witness pairs once the shared basis and inverse are available.
The four dense matrices contribute one charged write per scalar entry. -/
def ExactArithmeticProgram.pairCost (program : ExactArithmeticProgram p n) : ℕ :=
  program.code.length + 4 * n * n

/-- Execution-linked production of two particular valid witnesses.  Unlike all-witness
enumeration, this relation permits the shared basis and inverse as exact inputs. -/
def ExactArithmeticProgram.ComputesWitnessPair (program : ExactArithmeticProgram p n)
    (C : MixingMatrix p n) (_hdim : ValidPopulationDimensions p n) (_hC : FullRowRank C)
    (x : Fin p) (D : CertificateData C x) (j k : Fin n) (hj : j ∈ admissibleSources C x)
    (hk : k ∈ admissibleSources C x) : Prop :=
  ∃ registers,
    executeExact C D.basisExtension D.inverseBasis program.code = some registers ∧
    (∀ row col,
      exactRegisterAt? registers (program.witnessQRegister j row col) =
          some ((D.completion ⟨j, hj⟩).1 row col) ∧
      exactRegisterAt? registers (program.witnessHRegister j row col) =
          some ((D.completion ⟨j, hj⟩).2 row col) ∧
      exactRegisterAt? registers (program.witnessQRegister k row col) =
          some ((D.completion ⟨k, hk⟩).1 row col) ∧
      exactRegisterAt? registers (program.witnessHRegister k row col) =
          some ((D.completion ⟨k, hk⟩).2 row col)) ∧
    CompletionFiber C D.dim_le x (D.completion ⟨j, hj⟩).1 (D.completion ⟨j, hj⟩).2 ∧
    CompletionFiber C D.dim_le x (D.completion ⟨k, hk⟩).1 (D.completion ⟨k, hk⟩).2 ∧
    assignedSource (D.completion ⟨j, hj⟩).2 (D.valid ⟨j, hj⟩).monomial
      (Fin.castLE D.dim_le x) = j ∧
    assignedSource (D.completion ⟨k, hk⟩).2 (D.valid ⟨k, hk⟩).monomial
      (Fin.castLE D.dim_le x) = k

structure UniformExactPairAlgorithm where
  program : ∀ (p n : ℕ), Fin p → Fin n → Fin n → ExactArithmeticProgram p n
  run : ∀ {p n : ℕ} (C : MixingMatrix p n), FullRowRank C →
    NonzeroColumns C → DistinctDirections C → (x : Fin p) → CertificateData C x

/-- A universal exact-real cubic bound for producing two witnesses after the shared inverse,
restricted to the irreducible mixing domain claimed in the paper. -/
def IsUniformlyCubicPairAfterSharedInverse (algorithm : UniformExactPairAlgorithm) : Prop :=
  ∃ c n0 : ℕ, 0 < c ∧ ∀ {p n : ℕ} (C : MixingMatrix p n)
      (hdim : ValidPopulationDimensions p n) (hC : FullRowRank C)
      (hC0 : NonzeroColumns C) (hCdir : DistinctDirections C) (x : Fin p)
      (j k : Fin n) (hj : j ∈ admissibleSources C x) (hk : k ∈ admissibleSources C x),
      n0 ≤ n →
      let D := algorithm.run C hC hC0 hCdir x
      (algorithm.program p n x j k).ComputesWitnessPair C hdim hC x D j k hj hk ∧
      (algorithm.program p n x j k).pairCost ≤ c * n ^ 3

/-- Exact pair-cost certificate for the particular countermodel witnesses selected in a failed
vector-identification branch. -/
def CubicWitnessPairAfterSharedInverse {p n : ℕ} (C : MixingMatrix p n)
    (hdim : ValidPopulationDimensions p n) (hC : FullRowRank C)
    (_hC0 : NonzeroColumns C) (_hCdir : DistinctDirections C) (x : Fin p)
    (D : CertificateData C x) (j k : Fin n)
    (hj : j ∈ admissibleSources C x) (hk : k ∈ admissibleSources C x) : Prop :=
  ∃ algorithm : UniformExactPairAlgorithm,
    IsUniformlyCubicPairAfterSharedInverse algorithm ∧
    D = algorithm.run C hC _hC0 _hCdir x ∧
    (algorithm.program p n x j k).ComputesWitnessPair C hdim hC x D j k hj hk

/-- Dense Vandermonde instances: all sources are admissible and all response vectors are
distinct. -/
def DenseVandermondeInstance {p n : ℕ} (C : MixingMatrix p n) (x : Fin p) : Prop :=
  ∃ t : Fin n → ℚ, Function.Injective t ∧ (∀ j, 0 < t j) ∧
    (∀ i j, C i j = ((t j : ℚ) : ℝ) ^ i.1) ∧
    admissibleSources C x = Finset.univ ∧
    Function.Injective (fun j : Fin n => fun i : {i : Fin p // i ≠ x} =>
      C i.1 j / C x j)

/-- Worst-case output optimality in the same model, certified by a rational dense-output
Vandermonde family. Every correct all-witness run must perform at least `2 n^3` scalar writes and
hence at least that many exact-real operations. -/
def WorstCaseDenseOutputOptimal : Prop :=
  ∀ algorithm : UniformExactCertificateAlgorithm, ∀ n : ℕ, 2 ≤ n →
    ∃ (C : MixingMatrix 2 n) (x : Fin 2),
    IsRationalMatrix C ∧ FullRowRank C ∧ NonzeroColumns C ∧ DistinctDirections C ∧
      DenseVandermondeInstance C x ∧
    ∀ (hC : FullRowRank C) (D : CertificateData C x),
      algorithm.ComputesCertificate C hC x D →
      2 * n ^ 3 ≤ algorithm.cost C x

end CausalSmith.ExactID.EID_SourceminCyclicEffectRankfrontier
