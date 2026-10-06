module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Basic

/-! Finite-moment point-CATE frontier: Helpers/LawConstruction. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- The known-design observed law assembled from its conditional kernel. -/
def uniformRecord (e : unitInterval → ℝ) (he : Measurable e) (Q : Bool → Kernel unitInterval ℝ) : Measure O :=
  design ⊗ₘ recordKernel e he Q
/-- Bernoulli weights sum to one, so the conditional record kernel is Markov. -/
-- @node: recordKernel_markov
lemma recordKernel_markov (e : unitInterval → ℝ) (he : Measurable e)
    (hr : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (Q : Bool → Kernel unitInterval ℝ)
    (hq : ∀ a, IsMarkovKernel (Q a)) : IsMarkovKernel (recordKernel e he Q) := by
  letI (a : Bool) := hq a
  constructor
  intro x
  constructor
  change (recordMeasure e Q x) univ = 1
  simp only [recordMeasure, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (hr x).1 (sub_nonneg.mpr (hr x).2)]
  simp
/-- Range-bounded propensities and Markov arm kernels give a probability record law. -/
-- @node: uniformRecord_probability
lemma uniformRecord_probability (e : unitInterval → ℝ) (he : Measurable e)
    (hr : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (Q : Bool → Kernel unitInterval ℝ)
    (hq : ∀ a, IsMarkovKernel (Q a)) : IsProbabilityMeasure (uniformRecord e he Q) := by
  letI := recordKernel_markov e he hr Q hq
  unfold uniformRecord design
  infer_instance
/-- The composed record law has the prescribed uniform covariate marginal. -/
-- @node: uniformRecord_marginal
lemma uniformRecord_marginal (e : unitInterval → ℝ) (he : Measurable e)
    (hr : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (Q : Bool → Kernel unitInterval ℝ)
    (hq : ∀ a, IsMarkovKernel (Q a)) : (uniformRecord e he Q).map X = design := by
  letI := recordKernel_markov e he hr Q hq
  change (volume ⊗ₘ recordKernel e he Q).fst = volume
  exact Measure.fst_compProd volume (recordKernel e he Q)
/-- The conditional record representation is preserved when expressed through the actual marginal. -/
-- @node: uniformRecord_version
lemma uniformRecord_version (e : unitInterval → ℝ) (he : Measurable e)
    (hr : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (Q : Bool → Kernel unitInterval ℝ)
    (hq : ∀ a, IsMarkovKernel (Q a)) :
  uniformRecord e he Q = ((uniformRecord e he Q).map X) ⊗ₘ recordKernel e he Q := by
  rw [uniformRecord_marginal e he hr Q hq]
  rfl
/-- Almost-everywhere kernel identities transport to the constructed covariate marginal. -/
-- @node: uniformRecord_ae
lemma uniformRecord_ae (e : unitInterval → ℝ) (he : Measurable e)
    (hr : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (Q : Bool → Kernel unitInterval ℝ)
    (hq : ∀ a, IsMarkovKernel (Q a)) (R : unitInterval → Prop) (hR : ∀ᵐ x ∂design, R x) :
  ∀ᵐ x ∂((uniformRecord e he Q).map X), R x := by
  rw [uniformRecord_marginal e he hr Q hq]
  exact hR
/-- Bundle the explicitly assembled law and its selected kernel-mean versions. -/
def lawFromUniform (e : unitInterval → ℝ) (he : Measurable e)
    (hr : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (Q : Bool → Kernel unitInterval ℝ)
    (hq : ∀ a, IsMarkovKernel (Q a)) (m0 tau : unitInterval → ℝ)
    (h0 : ∀ᵐ x ∂design, m0 x = ∫ y, y ∂Q false x)
    (h1 : ∀ᵐ x ∂design, m0 x + tau x = ∫ y, y ∂Q true x) : ObservedLaw where
  P := uniformRecord e he Q
  probability := uniformRecord_probability e he hr Q hq
  e := e
  e_measurable := he
  e_range := hr
  Q := Q
  markov := hq
  m0 := m0
  tau := tau
  record_version := uniformRecord_version e he hr Q hq
  mean0_version := uniformRecord_ae e he hr Q hq _ h0
  mean1_version := uniformRecord_ae e he hr Q hq _ h1
/-- The reference half propensity is a probability. -/
-- @node: half_range
lemma half_range : ∀ x : unitInterval, 0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 1 := by
  intro x
  constructor <;> norm_num
/-- Constant zero outcomes have zero mean in both arms. -/
-- @node: zero_means
lemma zero_means :
  (∀ᵐ x ∂design, (0 : ℝ) = ∫ y, y ∂Kernel.const unitInterval (Measure.dirac (0 : ℝ)) x) ∧
  (∀ᵐ x ∂design, (0 : ℝ)+0 = ∫ y, y ∂Kernel.const unitInterval (Measure.dirac (0 : ℝ)) x) := by
  constructor <;> filter_upwards [] with x <;> simp
/-- Constant zero outcome kernels are Markov. -/
-- @node: zero_markov
lemma zero_markov : ∀ a : Bool, IsMarkovKernel (Kernel.const unitInterval (Measure.dirac (0 : ℝ))) := by
  intro a
  infer_instance
/-- A fixed total extension for constructions outside their public domains. -/
def referenceLaw : ObservedLaw :=
  lawFromUniform (fun _ => 1/2) measurable_const half_range
    (fun _ => Kernel.const unitInterval (Measure.dirac (0 : ℝ))) zero_markov
    (fun _ => 0) (fun _ => 0) zero_means.1 zero_means.2

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
