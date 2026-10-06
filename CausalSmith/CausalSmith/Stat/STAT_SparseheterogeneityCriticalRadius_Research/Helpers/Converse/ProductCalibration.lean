module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.ApproximationCalibration

/-! Product-prior expectations for common-reservoir normalization. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped BigOperators

noncomputable def expectedRawMassTotal (n J : ℕ) (kappa a : ℝ) : ℝ :=
  1 + rareScale n J kappa * ((n - 1 : ℕ) : ℝ) *
    (4 / (J : ℝ) + (1 - 1 / (J : ℝ)) * a)

noncomputable def expectedAlignedScoreTotal (n J : ℕ) (kappa a : ℝ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) : ℝ :=
  rareScale n J kappa * ((n - 1 : ℕ) : ℝ) *
    ((1 - 1 / (J : ℝ)) * a * |dualTargetGap a J D|)

private lemma oneCellPrior_integrable_of_stronglyMeasurable
    (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (f : LatentCell → ℝ) (hf : StronglyMeasurable f) :
    Integrable f (oneCellPrior a J D h) := by
  have htilt (t : Bool) (g : ℝ → ℝ) : Integrable g (tiltedSide a J D t) := by
    rw [tiltedSide, integrable_add_measure]
    constructor
    · rw [integrable_finsetSum_measure]
      intro i hi
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hmap (s t : Bool) : Integrable f
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable]
    exact htilt t (f ∘ latentFromIntensity s a)
  rw [oneCellPrior]
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · apply Integrable.smul_measure
    · apply Integrable.add_measure
      · exact (hmap false (!h)).smul_measure (by norm_num)
      · exact (hmap true h).smul_measure (by norm_num)
    · exact ENNReal.ofReal_ne_top

-- keep: exact product-prior expectation of the raw normalization mass
lemma latentProductPrior_integral_rawMassTotal
    (n J : ℕ) (kappa a : ℝ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hn : 0 < n) (ha : 0 < a) (hJ : 1 ≤ J) :
    ∫ theta, rawMassTotal n J kappa theta
        ∂latentProductPrior n a J D h =
      expectedRawMassTotal n J kappa a := by
  classical
  letI := oneCellPrior_isProbabilityMeasure a J D h ha hJ
  simp only [latentProductPrior]
  have hcell : Integrable latentIntensity (oneCellPrior a J D h) :=
    oneCellPrior_integrable_of_stronglyMeasurable a J D h latentIntensity
      latentIntensity_stronglyMeasurable
  have hterm (i : Fin (n - 1)) : Integrable
      (fun theta : Fin (n - 1) → LatentCell => latentIntensity (theta i))
      (Measure.pi (fun _ : Fin (n - 1) => oneCellPrior a J D h)) := by
    exact integrable_comp_eval hcell
  rw [show (fun theta => rawMassTotal n J kappa theta) =
      fun theta => 1 + rareScale n J kappa * ∑ i, latentIntensity (theta i) by
        funext theta
        exact rawMassTotal_eq_one_add_sum n J kappa theta hn]
  rw [integral_add (integrable_const 1)
    ((integrable_finset_sum Finset.univ fun i _ => hterm i).const_mul _),
    integral_const, integral_const_mul, integral_finsetSum]
  · simp_rw [integral_comp_eval
      (μ := fun _ : Fin (n - 1) => oneCellPrior a J D h)
      (f := latentIntensity) latentIntensity_stronglyMeasurable.aestronglyMeasurable,
      oneCellPrior_integral_latentIntensity a J D h ha hJ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, expectedRawMassTotal]
    simp
    ring
  · intro i hi
    exact hterm i

-- keep: exact product-prior expectation of the oriented signed-score total
lemma latentProductPrior_integral_rawSignedScoreTotal
    (n J : ℕ) (kappa a : ℝ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (hn : 0 < n) (ha : 0 < a) (hJ : 1 ≤ J) :
    ∫ theta, rawSignedScoreTotal n J kappa theta
        ∂latentProductPrior n a J D (orientedHypothesis a J D h) =
      (if h then 1 else -1) *
        expectedAlignedScoreTotal n J kappa a D := by
  classical
  let ho := orientedHypothesis a J D h
  letI := oneCellPrior_isProbabilityMeasure a J D ho ha hJ
  change (∫ theta, rawSignedScoreTotal n J kappa theta
      ∂Measure.pi (fun _ : Fin (n - 1) => oneCellPrior a J D ho)) = _
  have hcell : Integrable latentSignedScore (oneCellPrior a J D ho) :=
    oneCellPrior_integrable_of_stronglyMeasurable a J D ho latentSignedScore
      latentSignedScore_stronglyMeasurable
  have hterm (i : Fin (n - 1)) : Integrable
      (fun theta : Fin (n - 1) → LatentCell => latentSignedScore (theta i))
      (Measure.pi (fun _ : Fin (n - 1) => oneCellPrior a J D ho)) := by
    exact integrable_comp_eval hcell
  simp only [rawSignedScoreTotal]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_comp_eval
      (μ := fun _ : Fin (n - 1) => oneCellPrior a J D ho)
      (f := latentSignedScore)
      latentSignedScore_stronglyMeasurable.aestronglyMeasurable,
      show ho = orientedHypothesis a J D h from rfl,
      oneCellPrior_integral_oriented_latentSignedScore a J D h ha hJ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, expectedAlignedScoreTotal]
    ring
  · intro i hi
    exact hterm i

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
