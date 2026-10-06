module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Basic
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.MeasureTheory.Function.Floor

/-! # Rational engines and Borel dyadic naming policies

Primitive image and excess contracts are distinct from statistical budget conclusions.
Bounded stateful rational register programs certify the recurrence requirement;
arbitrary operation-count metadata alone does not certify a computation.
-/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- Instructions of a finite rational register machine. Registers carry state between steps;
comparisons may branch or jump back to an earlier instruction. Integer operations act
on the nonnegative part of the floor, except `floor` and `ceil`, which retain the sign. -/
inductive RationalInstruction where
  | constant : ℕ → ℚ → RationalInstruction
  | copy : ℕ → ℕ → RationalInstruction
  | add : ℕ → ℕ → ℕ → RationalInstruction
  | sub : ℕ → ℕ → ℕ → RationalInstruction
  | mul : ℕ → ℕ → ℕ → RationalInstruction
  | div : ℕ → ℕ → ℕ → RationalInstruction
  | min : ℕ → ℕ → ℕ → RationalInstruction
  | max : ℕ → ℕ → ℕ → RationalInstruction
  | floor : ℕ → ℕ → RationalInstruction
  | ceil : ℕ → ℕ → RationalInstruction
  | factorial : ℕ → ℕ → RationalInstruction
  | integerSqrt : ℕ → ℕ → RationalInstruction
  | clogTwo : ℕ → ℕ → RationalInstruction
  | natPow : ℕ → ℕ → ℕ → RationalInstruction
  | branchLe : ℕ → ℕ → ℕ → ℕ → RationalInstruction
  | jump : ℕ → RationalInstruction
  | halt : RationalInstruction
/-- A fixed finite instruction list, with no access to real inputs or external oracles. -/
abbrev RationalProgram := List RationalInstruction
/-- Program counter, rational registers, and halt flag. -/
abbrev RationalState := ℕ × (ℕ → ℚ) × Bool
/-- Initialize registers from the supplied rational arguments, and all others to zero. -/
def RationalProgram.initial (xs : List ℚ) : RationalState :=
  (0, fun i => xs[i]?.getD 0, false)
/-- One stateful rational step. Falling off the finite code also halts. -/
def RationalProgram.step (code : RationalProgram) (s : RationalState) : RationalState :=
  if s.2.2 then s else
    let pc := s.1
    let r := s.2.1
    let write := fun dst value => (pc + 1, Function.update r dst value, false)
    match code[pc]? with
    | none => (pc, r, true)
    | some (.constant dst v) => write dst v
    | some (.copy dst a) => write dst (r a)
    | some (.add dst a b) => write dst (r a + r b)
    | some (.sub dst a b) => write dst (r a - r b)
    | some (.mul dst a b) => write dst (r a * r b)
    | some (.div dst a b) => write dst (r a / r b)
    | some (.min dst a b) => write dst (min (r a) (r b))
    | some (.max dst a b) => write dst (max (r a) (r b))
    | some (.floor dst a) => write dst (⌊r a⌋ : ℤ)
    | some (.ceil dst a) => write dst (⌈r a⌉ : ℤ)
    | some (.factorial dst a) => write dst (Nat.factorial (⌊r a⌋ : ℤ).toNat)
    | some (.integerSqrt dst a) => write dst (Nat.sqrt (⌊r a⌋ : ℤ).toNat)
    | some (.clogTwo dst a) => write dst (Nat.clog 2 (⌊r a⌋ : ℤ).toNat)
    | some (.natPow dst a b) => write dst (r a ^ (⌊r b⌋ : ℤ).toNat)
    | some (.branchLe a b yes no) => (if r a ≤ r b then yes else no, r, false)
    | some (.jump target) => (target, r, false)
    | some .halt => (pc, r, true)
/-- General state-carrying iteration for a specified public number of steps.
In particular, repeated `natPow` instructions can generate towers of input-dependent height. -/
def RationalProgram.run (code : RationalProgram) : ℕ → RationalState → RationalState
  | 0, s => s
  | fuel + 1, s => code.run fuel (code.step s)
/-- Allowable public iteration-count functions are all total functions of rational
arguments computed by a fixed finite rational register program. The computation of
this bound must itself halt on every input; no elementary-growth restriction is imposed. -/
def PublicIterationBound (bound : List ℚ → ℕ) : Prop :=
  ∃ code : RationalProgram, ∀ xs : List ℚ, ∃ fuel : ℕ,
    (code.run fuel (RationalProgram.initial xs)).2.2 = true ∧
    (code.run fuel (RationalProgram.initial xs)).2.1 0 = (bound xs : ℚ)
/-- A general bounded stateful rational program with its specified public bound.
Registers zero and one are the returned endpoints. The bound and program are fixed
independently of exponents, samples, laws, naming policies, and evaluation radii. -/
structure BoundedRationalProgram where
  code : RationalProgram
  iterationBound : List ℚ → ℕ
  public_bound : PublicIterationBound iterationBound
  halts : ∀ xs, (code.run (iterationBound xs) (RationalProgram.initial xs)).2.2 = true
/-- Execute the certified finite state recurrence and read its rational endpoints. -/
def BoundedRationalProgram.eval (program : BoundedRationalProgram) (xs : List ℚ) : ℚ × ℚ :=
  let s := program.code.run (program.iterationBound xs) (RationalProgram.initial xs)
  (s.2.1 0, s.2.1 1)
/-- Endpoint ordering is enforced without any real input. -/
def rationalBox (lo hi : ℚ) : RatInterval := ⟨min lo hi, max lo hi, min_le_max⟩
/-- Fixed primitive index. -/
inductive PrimitiveKind where
  | pi | exp | cos | log | sqrt | power
/-- Independently fixed deterministic maps over rational data only. -/
structure ArithmeticEngine where
  piBox : ℕ → RatInterval -- @realizes \mathsf E(fixed engine; rational-only primitive data)
  expBox : ℕ → RatInterval → RatInterval
  cosBox : ℕ → RatInterval → RatInterval
  logBox : ℕ → RatInterval → RatInterval
  sqrtBox : ℕ → RatInterval → RatInterval
  powBox : ℕ → ℕ → RatInterval → RatInterval
/-- Precision error. -/
def precisionError (q : ℕ) : ℝ := (2 : ℝ) ^ (-(q : ℤ))
/-- Image containment and outward endpoint excess for a monotone primitive. -/
def MonotoneContract (F : ℝ → ℝ) (q : ℕ) (I J : RatInterval) : Prop :=
  (∀ x, I.Contains x → J.Contains (F x)) ∧
  0 ≤ F I.lo - J.lo ∧ F I.lo - J.lo ≤ precisionError q ∧
  0 ≤ (J.hi : ℝ) - F I.hi ∧ (J.hi : ℝ) - F I.hi ≤ precisionError q
/-- Every primitive is a general bounded stateful rational program, with a public
iteration bound computed solely from precision, rational range bounds, and the integer
base when present. The finite register language permits unrestricted state-carrying
loops within that bound, including non-elementary output growth. -/
def RationalRecurrences (E : ArithmeticEngine) : Prop :=
  ∃ code : PrimitiveKind → BoundedRationalProgram,
    (∀ q, E.piBox q = let v := (code .pi).eval [q]; rationalBox v.1 v.2) ∧
    (∀ q I, E.expBox q I = let v := (code .exp).eval [q,I.lo,I.hi]; rationalBox v.1 v.2) ∧
    (∀ q I, E.cosBox q I = let v := (code .cos).eval [q,I.lo,I.hi]; rationalBox v.1 v.2) ∧
    (∀ q I, E.logBox q I = let v := (code .log).eval [q,I.lo,I.hi]; rationalBox v.1 v.2) ∧
    (∀ q I, E.sqrtBox q I = let v := (code .sqrt).eval [q,I.lo,I.hi]; rationalBox v.1 v.2) ∧
    (∀ q b I, E.powBox q b I = let v := (code .power).eval [q,b,I.lo,I.hi]; rationalBox v.1 v.2)
-- @node: def:arithmetic-engine
/-- Primitive contracts and finite rational computation, with no budget conclusion. -/
def ArithmeticEngine.Admissible (E : ArithmeticEngine) : Prop :=
  RationalRecurrences E ∧
  (∀ q, (E.piBox q).Contains Real.pi ∧
    3 ≤ (E.piBox q).lo ∧ (E.piBox q).hi ≤ 4 ∧
    Real.pi - (E.piBox q).lo ≤ precisionError q ∧
    (E.piBox q).hi - Real.pi ≤ precisionError q) ∧
  (∀ q I, MonotoneContract Real.exp q I (E.expBox q I) ∧ 0 < (E.expBox q I).lo) ∧
  (∀ q I, 0 < I.lo → MonotoneContract Real.log q I (E.logBox q I)) ∧
  (∀ q I, 0 ≤ I.lo → MonotoneContract Real.sqrt q I (E.sqrtBox q I) ∧ 0 ≤ (E.sqrtBox q I).lo) ∧
  (∀ q (b : ℕ) I, 1 ≤ b → -3 ≤ I.lo → I.hi ≤ 3 →
    MonotoneContract (fun v => (b : ℝ) ^ v) q I (E.powBox q b I) ∧ 0 < (E.powBox q b I).lo) ∧
  (∀ q I, let m : ℝ := ((I.lo : ℝ) + I.hi) / 2
    let w : ℝ := ((I.hi : ℝ) - I.lo) / 2
    (∀ x, I.Contains x → (E.cosBox q I).Contains (Real.cos x)) ∧
    ∃ a b : ℚ, (a : ℝ) ≤ Real.cos m ∧ Real.cos m ≤ b ∧
      Real.cos m - a ≤ precisionError q ∧ (b : ℝ) - Real.cos m ≤ precisionError q ∧
      -1 ≤ a ∧ b ≤ 1 ∧
      (E.cosBox q I).lo = max (-1) (a - (I.hi - I.lo) / 2) ∧
      (E.cosBox q I).hi = min 1 (b + (I.hi - I.lo) / 2) ∧
      ((E.cosBox q I).width : ℝ) ≤ 2 * w + 2 * precisionError q)

/-- A name is a precision-indexed rational interval. -/
abbrev DyadicName := ℕ → RatInterval
/-- Dyadic rational endpoint. -/
def IsDyadic (v : ℚ) : Prop := ∃ z : ℤ, ∃ q : ℕ, v = (z : ℚ) / 2 ^ q
/-- Validity at every precision, with nesting and literal containment. -/
def IsValidName (v : ℝ) (name : DyadicName) : Prop :=
  (∀ q, IsDyadic (name q).lo ∧ IsDyadic (name q).hi ∧
    (name q).Contains v ∧ ((name q).width : ℝ) ≤ precisionError q) ∧
  (∀ q, (name (q + 1)).Subinterval (name q))
/-- Public names are fixed without the sample; covariate names may depend on it. -/
structure NamingPolicy where
  alphaName : ℕ → ℝ → ℝ → DyadicName -- @realizes \mathsf N(public exponent names precede sampling)
  betaName : ℕ → ℝ → ℝ → DyadicName
  covariateName : (n : ℕ) → ℝ → ℝ → (Fin n → Record) → Fin n → DyadicName
-- @node: def:dyadic-name-convention
/-- Every selected name is valid, and every rational response is Borel. -/
def NamingPolicy.Admissible (N : NamingPolicy) : Prop :=
  (∀ n α β, IsValidName α (N.alphaName n α β) ∧ IsValidName β (N.betaName n α β)) ∧
  (∀ n α β o i, IsValidName (covariate (o i)) (N.covariateName n α β o i)) ∧
  (∀ n q, Measurable (fun ab : ℝ × ℝ =>
    ((N.alphaName n ab.1 ab.2 q).lo, (N.alphaName n ab.1 ab.2 q).hi)) ∧
    Measurable (fun ab : ℝ × ℝ =>
    ((N.betaName n ab.1 ab.2 q).lo, (N.betaName n ab.1 ab.2 q).hi))) ∧
  (∀ n i q, Measurable (fun abo : (ℝ × ℝ) × (Fin n → Record) =>
    ((N.covariateName n abo.1.1 abo.1.2 abo.2 i q).lo,
     (N.covariateName n abo.1.1 abo.1.2 abo.2 i q).hi)))
/-- Ordered endpoints of the dyadic-floor response. [the stated conclusion](goal) holds. -/
-- @node: dyadic_floor_order
lemma dyadic_floor_order (v : ℝ) (q : ℕ) :
    ((⌊(2 : ℝ)^q * v⌋ : ℤ) : ℚ) / 2^q ≤
    (((⌊(2 : ℝ)^q * v⌋ : ℤ) : ℚ) + 1) / 2^q := by
  apply div_le_div_of_nonneg_right
  · exact le_add_of_nonneg_right zero_le_one
  · positivity
/-- The exact prescribed dyadic-floor name, including dyadic inputs. -/
def dyadicFloorName (v : ℝ) (q : ℕ) : RatInterval :=
  ⟨((⌊(2 : ℝ)^q * v⌋ : ℤ) : ℚ) / 2^q,
    (((⌊(2 : ℝ)^q * v⌋ : ℤ) : ℚ) + 1) / 2^q, dyadic_floor_order v q⟩
/-- One concrete policy, with the literal dyadic-floor responses. -/
def dyadicFloorPolicy : NamingPolicy where -- @realizes \mathsf N_0(dyadic-floor policy)
  alphaName := fun _ α _ => dyadicFloorName α
  betaName := fun _ _ β => dyadicFloorName β
  covariateName := fun _ _ _ o i => dyadicFloorName (covariate (o i))
/-- The literal floor boxes contain their input with the prescribed width. [the stated conclusion](goal) holds. -/
-- @node: dyadicFloorName_valid
lemma dyadicFloorName_valid (v : ℝ) : IsValidName v (dyadicFloorName v) := by
  constructor
  · intro q
    refine ⟨⟨⌊(2 : ℝ)^q*v⌋, q, rfl⟩, ?_, ?_, ?_⟩
    · refine ⟨⌊(2 : ℝ)^q*v⌋ + 1, q, ?_⟩
      simp [dyadicFloorName]
    · simp only [dyadicFloorName, RatInterval.Contains]
      push_cast
      constructor
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^q)).2
        simpa [mul_comm] using Int.floor_le ((2 : ℝ)^q*v)
      · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2^q)).2
        simpa [mul_comm] using (Int.lt_floor_add_one ((2 : ℝ)^q*v)).le
    · simp only [dyadicFloorName, RatInterval.width]
      push_cast
      simp only [precisionError, zpow_neg, zpow_natCast]
      apply le_of_eq
      field_simp
      ring
  · intro q
    have hlo : 2 * ⌊(2 : ℝ)^q*v⌋ ≤ ⌊(2 : ℝ)^(q+1)*v⌋ := by
      apply Int.le_floor.mpr
      push_cast
      have := Int.floor_le ((2 : ℝ)^q*v)
      rw [pow_succ]
      linarith
    have hhi : ⌊(2 : ℝ)^(q+1)*v⌋ < 2 * (⌊(2 : ℝ)^q*v⌋ + 1) := by
      apply Int.floor_lt.mpr
      push_cast
      have := Int.lt_floor_add_one ((2 : ℝ)^q*v)
      rw [pow_succ]
      linarith
    change ((⌊(2 : ℝ)^q*v⌋ : ℤ) : ℚ) / 2^q ≤
        ((⌊(2 : ℝ)^(q+1)*v⌋ : ℤ) : ℚ) / 2^(q+1) ∧
      (((⌊(2 : ℝ)^(q+1)*v⌋ : ℤ) : ℚ)+1) / 2^(q+1) ≤
        (((⌊(2 : ℝ)^q*v⌋ : ℤ) : ℚ)+1) / 2^q
    rw [pow_succ]
    constructor
    · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hl : (2 : ℚ) * ⌊(2 : ℝ)^q*v⌋ ≤ ⌊(2 : ℝ)^(q+1)*v⌋ := by exact_mod_cast hlo
      simp only [pow_succ] at hl ⊢
      nlinarith [show (0 : ℚ) < 2^q by positivity]
    · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hh : (⌊(2 : ℝ)^(q+1)*v⌋ : ℚ)+1 ≤ 2 * (⌊(2 : ℝ)^q*v⌋+1) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hhi)
      simp only [pow_succ] at hh ⊢
      nlinarith [show (0 : ℚ) < 2^q by positivity]

/-- At each fixed precision the two rational floor endpoints are Borel. [the stated conclusion](goal) holds. -/
-- @node: dyadicFloorName_measurable
lemma dyadicFloorName_measurable (q : ℕ) :
    Measurable (fun v : ℝ => ((dyadicFloorName v q).lo, (dyadicFloorName v q).hi)) := by
  unfold dyadicFloorName
  fun_prop

/-- The explicit floor policy meets all validity and Borel contracts. [the stated conclusion](goal) holds. -/
-- @node: dyadicFloorPolicy_admissible
lemma dyadicFloorPolicy_admissible : NamingPolicy.Admissible dyadicFloorPolicy := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n α β
    exact ⟨dyadicFloorName_valid α, dyadicFloorName_valid β⟩
  · intro n α β o i
    exact dyadicFloorName_valid _
  · intro n q
    exact ⟨(dyadicFloorName_measurable q).comp measurable_fst,
      (dyadicFloorName_measurable q).comp measurable_snd⟩
  · intro n i q
    apply (dyadicFloorName_measurable q).comp
    unfold covariate
    fun_prop
end CausalSmith.Stat.LogoddsLowsmoothFrontier
