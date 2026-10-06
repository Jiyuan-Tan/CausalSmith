module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.SharedDesign

/-! The finite approximation dual produces supported probability priors with
matching algebraic moments, as in converse roadmap (54)--(55). -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set Filter
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped BigOperators ENNReal

-- keep: paper-local constructor endpoint for the radius approximation dual
lemma radius_dual_exists (J : ℕ) (a : ℝ)
    (ha : 0 < a) (ha1 : a < 1) :
    Nonempty (FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) := by
  apply exists_rationalFiniteMomentDual
    ha1
  simp only [Set.mem_Icc, not_and]
  intro h
  linarith

/-- The approximation dual is a normalized signed moment certificate in the
library's atomic Jordan-prior construction. -/
-- @node: radiusMomentCertificate
def radiusMomentCertificate (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) :
    NormalizedFiniteSignedMomentCertificate (Fin (3 * J + 2)) (3 * J) where
  node := D.nodes
  weight := D.weights
  node_injective := D.nodes_strictMono.injective
  normalized := D.weights_normalized
  moments_zero := D.moments_zero

/-- The two explicitly weighted sides are exactly the library's normalized
positive and negative Jordan priors. -/
-- @node: dualSide_eq_jordanPrior
lemma dualSide_eq_jordanPrior (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (h : Bool) :
    dualSide a J D h = if h then (radiusMomentCertificate a J D).positivePrior
      else (radiusMomentCertificate a J D).negativePrior := by
  cases h <;> rfl

/-- Both sides in (55) have total mass one, rather than merely nonnegative
atomic weights. -/
-- @node: dualSide_isProbabilityMeasure
lemma dualSide_isProbabilityMeasure (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (h : Bool) :
    IsProbabilityMeasure (dualSide a J D h) := by
  rw [dualSide_eq_jordanPrior]
  cases h <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The probability priors match every algebraic moment through the selected
matching degree, as required by the expansion in (59). -/
-- @node: dualSide_moments_eq
lemma dualSide_moments_eq (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (j : ℕ) (hj : j ≤ 3 * J) :
    (∫ x, x ^ j ∂dualSide a J D true) = ∫ x, x ^ j ∂dualSide a J D false := by
  simpa only [dualSide_eq_jordanPrior, Bool.false_eq_true, ↓reduceIte] using
    (radiusMomentCertificate a J D).jordanPriors_moments_eq j hj

/-- The interval support in (55) is inherited from the approximation dual's
finite node set. -/
-- @node: dualSide_ae_mem_interval
lemma dualSide_ae_mem_interval (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (h : Bool) :
    ∀ᵐ x ∂dualSide a J D h, x ∈ Icc a 1 := by
  have hs := (radiusMomentCertificate a J D).jordanPriors_ae_mem_range
  rw [dualSide_eq_jordanPrior]
  cases h
  · simp only [Bool.false_eq_true, ↓reduceIte]
    filter_upwards [hs.2] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact D.nodes_mem i
  · simp only [↓reduceIte]
    filter_upwards [hs.1] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact D.nodes_mem i

/-- The doubled positive or negative atomic weights sum to one. -/
-- @node: dualSide_weights_sum
lemma dualSide_weights_sum (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (h : Bool) :
    (∑ i, 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0)) = 1 := by
  let w := fun i => 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w]
    split <;> positivity
  let := dualSide_isProbabilityMeasure a J D h
  have hm : ENNReal.ofReal (∑ i, w i) = 1 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)]
    simpa only [dualSide, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, w] using
      (measure_univ (μ := dualSide a J D h))
  have ht := congrArg ENNReal.toReal hm
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hw i)),
    ENNReal.toReal_one] using ht

/-- The inverse-intensity tilt retains at most unit mass; therefore its
zero-atom coefficient in (56) is nonnegative. -/
-- @node: tiltedSide_weights_bounds
lemma tiltedSide_weights_bounds (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) :
    (∑ i, 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) *
      a / D.nodes i) ∈ Icc (0 : ℝ) 1 := by
  have hw : ∀ i, 0 ≤ 2 *
      (if h then max (D.weights i) 0 else max (-D.weights i) 0) := by
    intro i
    split <;> positivity
  have hx : ∀ i, 0 < D.nodes i := fun i => ha.trans_le (D.nodes_mem i).1
  refine ⟨Finset.sum_nonneg (fun i _ => div_nonneg (mul_nonneg (hw i) ha.le)
    (hx i).le), ?_⟩
  calc
    _ ≤ ∑ i, 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (div_le_iff₀ (hx i)).2
      exact mul_le_mul_of_nonneg_left (D.nodes_mem i).1 (hw i)
    _ = 1 := dualSide_weights_sum a J D h

/-- Adding the nonnegative zero atom in (56) restores total mass exactly
one, so the tilted sides are probability measures. -/
-- @node: tiltedSide_isProbabilityMeasure
lemma tiltedSide_isProbabilityMeasure (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) :
    IsProbabilityMeasure (tiltedSide a J D h) := by
  have hw : ∀ i, 0 ≤ 2 *
      (if h then max (D.weights i) 0 else max (-D.weights i) 0) * a / D.nodes i := by
    intro i
    have hx := ha.trans_le (D.nodes_mem i).1
    split <;> positivity
  have hs := tiltedSide_weights_bounds a J D h ha
  constructor
  simp only [tiltedSide, Measure.add_apply, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),
    ← ENNReal.ofReal_add hs.1 (sub_nonneg.mpr hs.2)]
  simp

/-- The guarded map in (58) is measurable even at the zero-intensity atom. -/
-- @node: latentFromIntensity_measurable
@[fun_prop] lemma latentFromIntensity_measurable (h : Bool) (a : ℝ) :
    Measurable (latentFromIntensity h a) := by
  unfold latentFromIntensity zeroLatent
  apply Measurable.ite
  · exact measurableSet_singleton 0
  · fun_prop
  · fun_prop

/-- The reference atom and the two sign-coupled tilted sides in (61)--(62)
form a probability measure whenever the reference weight is at most one. -/
-- @node: oneCellPrior_isProbabilityMeasure
lemma oneCellPrior_isProbabilityMeasure (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual
      (rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J) :
    IsProbabilityMeasure (oneCellPrior a J D h) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hw : 0 ≤ 1 - 1 / (J : ℝ) := by
    have := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hJr)
    simpa only [one_div, inv_one] using sub_nonneg.mpr this
  let := tiltedSide_isProbabilityMeasure a J D h ha
  let := tiltedSide_isProbabilityMeasure a J D (!h) ha
  constructor
  simp only [oneCellPrior, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    Measure.map_apply (latentFromIntensity_measurable false a) MeasurableSet.univ,
    Measure.map_apply (latentFromIntensity_measurable true a) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, mul_one]
  rw [show (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 by
    norm_num [one_div, ← two_mul, ENNReal.mul_inv_cancel], mul_one]
  rw [← ENNReal.ofReal_add (by positivity) hw]
  simp

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
