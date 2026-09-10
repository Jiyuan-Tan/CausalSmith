import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Cover

/-!
# Gaussian feature embeddings and cover separation

This file defines the paper's explicit square-summable Gaussian feature map,
kernel mean embeddings, population discrepancies, and the two genericity sets.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace lp

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @env: S3
variable {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}

/-- The Gaussian kernel `exp (-(a-b)²)`. -/
def gaussianKernel (a b : ℝ) : ℝ :=
  Real.exp (-(a - b) ^ 2) -- @realizes k(exp (-(a-b)^2), range (0,1])

/-- A real Hilbert-space feature map of unit norm that realizes a specified kernel. -/
structure UnitNormFeatureMap (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  Φ : ℝ → H
  norm_eq_one : ∀ r, ‖Φ r‖ = 1
  inner_eq_kernel : ∀ a b, ⟪Φ a, Φ b⟫_ℝ = gaussianKernel a b

/-- The `m`th coordinate of the paper's explicit Gaussian feature expansion. -/
def gaussianFeatureCoefficient (r : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ m / m.factorial) * Real.exp (-r ^ 2) * r ^ m

/-- The explicit coefficient sequence is square-summable. -/
lemma gaussianFeature_memℓp (r : ℝ) :
    Memℓp (gaussianFeatureCoefficient r) 2 := by
  apply memℓp_gen
  norm_num
  simp only [gaussianFeatureCoefficient]
  have hs : Summable (fun m : ℕ => (2 * r ^ 2) ^ m / m.factorial) :=
    Real.summable_pow_div_factorial _
  apply (hs.mul_left (Real.exp (-r ^ 2) ^ 2)).congr
  intro m
  have hnonneg : 0 ≤ (2 : ℝ) ^ m / m.factorial := by positivity
  calc
    _ = Real.exp (-r ^ 2) ^ 2 * ((2 : ℝ) ^ m / m.factorial) *
        r ^ (2 * m) := by ring
    _ = (Real.sqrt ((2 : ℝ) ^ m / m.factorial)) ^ 2 *
        Real.exp (-r ^ 2) ^ 2 * r ^ (2 * m) := by
          rw [Real.sq_sqrt hnonneg]
          ac_rfl
    _ = _ := by ring

/-- The explicit Gaussian feature vector in real `ℓ²`. -/
def gaussianFeature (r : ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨gaussianFeatureCoefficient r, gaussianFeature_memℓp r⟩

lemma gaussianFeature_inner (a b : ℝ) :
    ⟪gaussianFeature a, gaussianFeature b⟫_ℝ =
      gaussianKernel a b := by
  rw [lp.inner_eq_tsum]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  change (∑' m : ℕ, gaussianFeatureCoefficient b m *
    gaussianFeatureCoefficient a m) = _
  have hterm : (fun m : ℕ => gaussianFeatureCoefficient b m *
      gaussianFeatureCoefficient a m) =
      fun m => (Real.exp (-a ^ 2) * Real.exp (-b ^ 2)) *
        ((2 * a * b) ^ m / m.factorial) := by
    funext m
    unfold gaussianFeatureCoefficient
    have hnonneg : 0 ≤ (2 : ℝ) ^ m / m.factorial := by positivity
    have hsqrt := Real.mul_self_sqrt hnonneg
    calc
      _ = (Real.sqrt ((2 : ℝ) ^ m / m.factorial) *
            Real.sqrt ((2 : ℝ) ^ m / m.factorial)) *
          (Real.exp (-a ^ 2) * Real.exp (-b ^ 2)) *
          (a ^ m * b ^ m) := by ring
      _ = _ := by rw [hsqrt]; ring
  rw [hterm, tsum_mul_left,
    (NormedSpace.expSeries_div_hasSum_exp (2 * a * b)).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add, ← Real.exp_add]
  unfold gaussianKernel
  congr 1
  ring

lemma gaussianFeature_norm (r : ℝ) : ‖gaussianFeature r‖ = 1 := by
  have hsq : ‖gaussianFeature r‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, gaussianFeature_inner]
    simp [gaussianKernel]
  nlinarith [norm_nonneg (gaussianFeature r)]

/-- The concrete unit-norm feature-map realization of the Gaussian kernel. -/
def gaussianFeatureMap : UnitNormFeatureMap (lp (fun _ : ℕ => ℝ) 2) where
  Φ := gaussianFeature
  norm_eq_one := gaussianFeature_norm
  inner_eq_kernel := gaussianFeature_inner

/-- The Bochner kernel mean embedding of a real-valued law in a Hilbert space. -/
def meanEmbedding {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (U : UnitNormFeatureMap H) (μ : Measure ℝ) : H :=
  ∫ r, U.Φ r ∂μ

/-- The observational law followed by the `n` interventional environment laws. -/
abbrev ObservedLawFamily (n : ℕ) := Fin (n + 1) → Measure (LatentState n)

/-- The canonical Radon--Nikodym ratio determined by the observed laws. -/
def observedLawRatio (laws : ObservedLawFamily n) (i : Fin n) (x : LatentState n) : ℝ :=
  ((laws i.succ).rnDeriv (laws 0) x).toReal
  -- @realizes \(R_i\)(Radon--Nikodym derivative computed from observed laws)

/-- The canonical observed-law ratio is globally measurable. -/
lemma measurable_observedLawRatio (laws : ObservedLawFamily n) (i : Fin n) :
    Measurable (observedLawRatio laws i) :=
  ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _)

/-- The law of ratio `i` under the observational environment. -/
def observationalRatioLaw {θ : Mechanism n G} (W : ObservedWorld G θ) (i : Fin n) :
    Measure ℝ := Measure.map (observedLawRatio W.law i) (W.law 0)

/-- The law of ratio `i` under intervention environment `j`. -/
def interventionalRatioLaw {θ : Mechanism n G} (W : ObservedWorld G θ)
    (j i : Fin n) : Measure ℝ :=
  Measure.map (observedLawRatio W.law i) (W.law j.succ)

/-- Population Gaussian-kernel MMD between the observational and environment-`j` ratio laws. -/
def populationDiscrepancy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (U : UnitNormFeatureMap H) {θ : Mechanism n G} (W : ObservedWorld G θ)
    (j i : Fin n) : ℝ :=
  ‖meanEmbedding U (observationalRatioLaw W i) -
    meanEmbedding U (interventionalRatioLaw W j i)‖
  -- @realizes \(D_{ji}\)(norm of difference of kernel mean embeddings)

-- @node: populationDiscrepancy_eq_zero_of_ratioLaw_eq
/-- Equal observational and interventional ratio laws have zero population discrepancy. -/
lemma populationDiscrepancy_eq_zero_of_ratioLaw_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) {θ : Mechanism n G} (W : ObservedWorld G θ)
    (j i : Fin n) (hLaw : observationalRatioLaw W i = interventionalRatioLaw W j i) :
    populationDiscrepancy U W j i = 0 := by
  simp [populationDiscrepancy, hLaw]

/-- The environment-`j` minus observational second-moment contrast of ratio `i`. -/
def secondMomentContrast {θ : Mechanism n G} (W : ObservedWorld G θ)
    (j i : Fin n) : ℝ :=
  (∫ x, (W.ratio i x) ^ 2 ∂W.law j.succ) -
    ∫ x, (W.ratio i x) ^ 2 ∂W.law 0
  -- @realizes \(F_{ji}\)(difference of second moments)

/-- The observable directed ratio graph. -/
def ratioGraph {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (U : UnitNormFeatureMap H) {θ : Mechanism n G} (W : ObservedWorld G θ) :
    Fin n → Fin n → Prop :=
  fun j i => j ≠ i ∧ 0 < populationDiscrepancy U W j i
  -- @realizes \(H_D\)(edge iff D_ji > 0)

-- @node: def:edge-separated-set
/-- Mechanisms whose second-moment contrast is nonzero on every permuted direct edge. -/
def edgeSeparatedSet
    (π : Equiv.Perm (Fin n)) : Set (StratumPoint G s) :=
  {θ | ∀ ⦃j i⦄, G.edge j i →
    secondMomentContrast (canonicalObservedWorld G θ.1 π) (π.symm j) (π.symm i) ≠ 0}
  -- @realizes \(\mathcal V_{G,s,\pi}\)(nonzero F on every direct edge)

-- @node: def:cover-separated-set
/-- Mechanisms whose Gaussian MMD is positive on every permuted ancestral cover. -/
def coverSeparatedSet
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (U : UnitNormFeatureMap H)
    (π : Equiv.Perm (Fin n)) : Set (StratumPoint G s) :=
  {θ | ∀ ⦃j i⦄, ancestralCover G j i →
    0 < populationDiscrepancy U (canonicalObservedWorld G θ.1 π)
      (π.symm j) (π.symm i)}
  -- @realizes \(\mathcal U_{G,s,\pi}\)(positive MMD on ancestral covers)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
