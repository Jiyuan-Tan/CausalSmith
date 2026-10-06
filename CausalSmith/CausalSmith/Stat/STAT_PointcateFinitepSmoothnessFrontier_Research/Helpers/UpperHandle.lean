module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Kernels
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Finite-moment point-CATE frontier: Helpers/UpperHandle. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


variable (κ : Params)
/-- Effective propensity exponent for public tuning. -/
def effectiveA : ℝ := min κ.α ((κ.p-1)/2)
/-- Effective sum of regularities. -/
def effectiveS : ℝ := effectiveA κ+κ.β
/-- The positive exponent governing the uncapped geometric ledger. -/
def effectiveD : ℝ := qExp κ-effectiveA κ*(2-κ.p)/κ.p
/-- Effective interaction tuning exponent. -/
def effectiveR : ℝ := 2*effectiveS κ/(1+effectiveS κ/κ.γ+2*effectiveA κ+κ.β/qExp κ)
/-- Public localization. -/
def upperH (n : ℕ) : ℝ := rate κ n ^ (1/κ.γ)
/-- Public nonnegative floor-rounded resolution. -/
def upperJ (n : ℕ) : ℕ := Int.toNat ⌊Real.logb 2 (upperH κ n / rate κ n ^ (1/effectiveS κ))⌋
/-- Coarse threshold and capped level-specific thresholds. -/
def upperT (n : ℕ) (j : Fin (upperJ κ n+1)) : ℝ :=
  if j.val = 0 then ((n : ℝ)*upperH κ n)^(1/κ.p)
  else min (((n : ℝ)*upperH κ n)^(1/κ.p))
    (((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j.val ^ (1+2*effectiveA κ))^(1/κ.p))
/-- The first floor(n/2) fixed indices form the treatment block. -/
def treatmentBlock (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < n/2)
/-- The remaining indices form the outcome block. -/
def outcomeBlock (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => n/2 ≤ i.val)
/-- Binary treatment encoded as a real number. -/
def bit (a : Bool) : ℝ := if a then 1 else 0
/-- The real encoding of a binary treatment is Borel. -/
-- @node: measurable_bit
@[fun_prop] lemma measurable_bit : Measurable bit := by
  fun_prop
/-- The observable linear-minus-bilinear numerator with original responses. -/
def numeratorHat (n : ℕ) (o : Dataset n) : ℝ :=
  (((outcomeBlock n).card : ℝ)*upperH κ n)⁻¹ *
    (∑ i ∈ outcomeBlock n, if X (o i) ∈ window (upperH κ n) then bit (A (o i))*trunc (upperT κ n 0) (Y (o i)) else 0)
  - (((treatmentBlock n).card : ℝ)*(outcomeBlock n).card)⁻¹ *
    (∑ t ∈ treatmentBlock n, ∑ i ∈ outcomeBlock n,
      heavyKernel (upperH κ n) (upperJ κ n) (upperT κ n) (o t) (o i))
/-- The observable finite numerator is Borel in the dataset. -/
-- @node: measurable_numeratorHat
@[fun_prop] lemma measurable_numeratorHat (n : ℕ) : Measurable (numeratorHat κ n) := by
  unfold numeratorHat
  apply Measurable.sub
  · apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact measurableSet_Icc.preimage (by unfold X; fun_prop)
    · unfold A Y
      fun_prop
    · fun_prop
  · fun_prop
/-- The observable linear-minus-bilinear denominator. -/
def denominatorHat (n : ℕ) (o : Dataset n) : ℝ :=
  (((outcomeBlock n).card : ℝ)*upperH κ n)⁻¹ *
    (∑ i ∈ outcomeBlock n, if X (o i) ∈ window (upperH κ n) then bit (A (o i)) else 0)
  - (((treatmentBlock n).card : ℝ)*(outcomeBlock n).card*upperH κ n)⁻¹ *
    (∑ t ∈ treatmentBlock n, ∑ i ∈ outcomeBlock n,
      bit (A (o t))*bit (A (o i))*projKernel (upperH κ n) (upperJ κ n) (X (o t)) (X (o i)))
/-- The observable finite denominator is Borel in the dataset. -/
-- @node: measurable_denominatorHat
@[fun_prop] lemma measurable_denominatorHat (n : ℕ) : Measurable (denominatorHat κ n) := by
  unfold denominatorHat
  apply Measurable.sub
  · apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact measurableSet_Icc.preimage (by unfold X; fun_prop)
    · unfold A
      fun_prop
    · fun_prop
  · unfold A X
    fun_prop
/-- Range projection onto the target interval. -/
def clip (x : ℝ) : ℝ := max (-1/2) (min x (1/2))
/-- Projection onto the target range is Borel. -/
-- @node: measurable_clip
@[fun_prop] lemma measurable_clip : Measurable clip := by
  unfold clip
  fun_prop
/-- One total original-record ratio procedure, with a fixed denominator safeguard and range projection. -/
def upperEstimator (n : ℕ) (z : Dataset n × unitInterval × Unit) : ℝ :=
  if 3/32 ≤ denominatorHat κ n z.1 then clip (numeratorHat κ n z.1/denominatorHat κ n z.1) else 0
/-- Public positive geometric denominators. -/
def constantA : ℝ := 1-(2 : ℝ)^(-effectiveA κ)
/-- Uncapped geometric denominator. -/
def constantE : ℝ := 1-(2 : ℝ)^(-effectiveD κ)
/-- Squared truncation-bias geometric denominator. -/
def constantF : ℝ := 1-(2 : ℝ)^(-2*qExp κ)
/-- The explicit moment-only projection constant. -/
def cG : ℝ := 3*(10 : ℝ)^(2/κ.p)
/-- The finite public bias ledger. -/
def cBias : ℝ := 1635+400/constantA κ+1600/constantE κ
/-- The finite public standard-deviation ledger. -/
def cNoise : ℝ :=
  Real.sqrt 30*(1+40/constantA κ)+Real.sqrt (3*(cG κ+200/constantF κ))+
    Real.sqrt (90*(1+(1-(2 : ℝ)^(-2*effectiveA κ))⁻¹+16*(1-(2 : ℝ)^(-2*effectiveD κ))⁻¹))
/-- Deterministic public absolute-risk certificate. -/
def cPub : ℝ := 16*(cBias κ+cNoise κ+20)
/-- A bounded closed interval code, or the empty code if the proposed endpoints are invalid. -/
def closedInterval (lo hi : ℝ) : IntervalCode :=
  if h : -1/2 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1/2 then .inr ⟨(lo,hi,true,true),h⟩ else .inl ()
/-- Clipping endpoints into a valid interval code is a Borel operation. -/
-- @node: measurable_closedInterval
@[fun_prop] lemma measurable_closedInterval :
    Measurable (fun lh : ℝ × ℝ => closedInterval lh.1 lh.2) := by
  unfold closedInterval
  apply Measurable.dite
    (s := {lh : ℝ × ℝ | -1/2 ≤ lh.1 ∧ lh.1 ≤ lh.2 ∧ lh.2 ≤ 1/2})
    (f := fun lh => Sum.inr (⟨(lh.1.1, lh.1.2, true, true), lh.2⟩ : Endpoints))
    (g := fun _ => Sum.inl ())
  · fun_prop
  · fun_prop
  · exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
/-- A deterministic public radius; the max provides a total off-domain extension. -/
def upperRadius (n : ℕ) : ℝ := max 0 (10*cPub κ*rate κ n)
/-- The closed connected interval built around the same estimator. -/
def upperInterval (n : ℕ) (z : Dataset n × unitInterval × Unit) : IntervalCode :=
  closedInterval (max (-1/2) (upperEstimator κ n z-upperRadius κ n))
    (min (1/2) (upperEstimator κ n z+upperRadius κ n))
/-- The original estimator is Borel and target-range-valued on its whole decision domain. -/
-- @node: upperEstimator_total
lemma upperEstimator_total (n : ℕ) : Measurable (upperEstimator κ n) ∧ ∀ z, upperEstimator κ n z ∈ Icc (-1/2) (1/2) := by
  constructor
  · unfold upperEstimator
    first
    | fun_prop
    | apply Measurable.ite (measurableSet_le measurable_const (by fun_prop)) <;> fun_prop
  · intro z
    unfold upperEstimator
    split
    · unfold clip
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_right _ _)
    · constructor <;> norm_num
/-- The reported bounded interval is Borel on its whole domain. -/
-- @node: measurable_upperInterval
@[fun_prop] lemma measurable_upperInterval (n : ℕ) : Measurable (upperInterval κ n) := by
  unfold upperInterval
  have ht := (upperEstimator_total κ n).1
  fun_prop
/-- Bundled original-record estimator. -/
def upperDecision (n : ℕ) : Estimator n := ⟨upperEstimator κ n, upperEstimator_total κ n⟩
/-- Bundled original-record interval decision. -/
def upperIntervalDecision (n : ℕ) : IntervalProc n Unit := ⟨upperInterval κ n, measurable_upperInterval κ n⟩

/-- A two-block truncated ratio with public tuning, a positive denominator safeguard and final clipping. -/
def tunedRatio (n : ℕ) (BT BY : Finset (Fin n)) (h : ℝ) (J : ℕ)
    (T : Fin (J+1) → ℝ) (cutoff : ℝ) (z : Experiment n) : ℝ :=
  let N := ((BY.card : ℝ)*h)⁻¹ *
    (∑ i ∈ BY, if X (z.1 i) ∈ window h then bit (A (z.1 i))*trunc (T 0) (Y (z.1 i)) else 0) -
    ((BT.card : ℝ)*BY.card)⁻¹ * (∑ t ∈ BT, ∑ i ∈ BY, heavyKernel h J T (z.1 t) (z.1 i))
  let D := ((BY.card : ℝ)*h)⁻¹ *
    (∑ i ∈ BY, if X (z.1 i) ∈ window h then bit (A (z.1 i)) else 0) -
    ((BT.card : ℝ)*BY.card*h)⁻¹ *
      (∑ t ∈ BT, ∑ i ∈ BY, bit (A (z.1 t))*bit (A (z.1 i))*projKernel h J (X (z.1 t)) (X (z.1 i)))
  if cutoff ≤ D then clip (N/D) else 0
/-- A public risk certificate and one total estimator, public radius and interval for every n. -/
abbrev UpperProgram := ℝ × ((n : ℕ) → Estimator n × ℝ × OriginalIntervalProc n)
/-- The construction programme retains fixed independent blocks, public dyadic tuning,
scale-specific truncations, safeguards, range projection and deterministic risk and coverage certificates. -/
def UpperProgramCertificate (program : UpperProgram) : Prop :=
  κ.Valid → 0 < program.1 ∧ ∀ n : ℕ, 2 ≤ n →
    let t := (program.2 n).1
    let radius := (program.2 n).2.1
    let i := (program.2 n).2.2
    0 ≤ radius ∧ 2*radius ≤ 20*program.1*rate κ n ∧
    (∃ BT BY : Finset (Fin n), BT.Nonempty ∧ BY.Nonempty ∧ Disjoint BT BY ∧ BT ∪ BY = Finset.univ ∧
      ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ ∃ J : ℕ, ∃ T : Fin (J+1) → ℝ,
        (∀ j, 1 ≤ T j) ∧ ∃ cutoff : ℝ, 0 < cutoff ∧
          ∀ z, t.1 z = tunedRatio n BT BY h J T cutoff (originalDecisionDomain n z)) ∧
    (∀ z, i.1 z = closedInterval (max (-1/2) (t.1 z-radius)) (min (1/2) (t.1 z+radius))) ∧
    (∀ law, InModel κ law → decisionRisk n jointLaw (fun _ => ()) t law ≤ program.1*rate κ n ∧
      9/10 ≤ coverage n jointLaw (fun _ => ()) i law) ∧
    (∀ z, (i.1 z).length ≤ min 1 (2*radius))

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
