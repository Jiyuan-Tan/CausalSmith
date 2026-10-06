module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.Calibration
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.Duality

/-! Exact one-cell expectations used to calibrate the normalized target. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped BigOperators ENNReal

lemma latentSignedScore_stronglyMeasurable :
    StronglyMeasurable latentSignedScore := by
  unfold latentSignedScore
  exact ((by unfold latentIntensity; fun_prop : StronglyMeasurable latentIntensity).mul
    latentSignValue_measurable.stronglyMeasurable).mul
      (by unfold latentScore; fun_prop)

lemma latentIntensity_stronglyMeasurable :
    StronglyMeasurable latentIntensity := by
  unfold latentIntensity
  fun_prop

private lemma tiltedSide_integrable_any (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (f : ℝ → ℝ) : Integrable f (tiltedSide a J D h) := by
  rw [tiltedSide, integrable_add_measure]
  constructor
  · rw [integrable_finsetSum_measure]
    intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma tiltedSide_integral_eq_sum (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (f : ℝ → ℝ) :
    ∫ x, f x ∂tiltedSide a J D h =
      ∑ i, (2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) *
          a / D.nodes i) * f (D.nodes i) +
        (1 - ∑ i, 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) *
          a / D.nodes i) * f 0 := by
  classical
  have hnode (i : Fin (3 * J + 2)) : 0 < D.nodes i :=
    ha.trans_le (D.nodes_mem i).1
  have hcoeff (i : Fin (3 * J + 2)) :
      0 ≤ 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) *
        a / D.nodes i := by
    apply div_nonneg
    · apply mul_nonneg
      · split <;> exact mul_nonneg (by norm_num) (le_max_right _ _)
      · exact ha.le
    · exact (hnode i).le
  have hzero :
      0 ≤ 1 - ∑ i, 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) *
        a / D.nodes i :=
    sub_nonneg.mpr (tiltedSide_weights_bounds a J D h ha).2
  rw [tiltedSide, integral_add_measure]
  · rw [integral_finsetSum_measure]
    · apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_smul_measure, integral_dirac,
          ENNReal.toReal_ofReal (hcoeff i), smul_eq_mul]
      · rw [integral_smul_measure, integral_dirac,
          ENNReal.toReal_ofReal hzero, smul_eq_mul]
    · intro i hi
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · rw [integrable_finsetSum_measure]
    intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma dualSide_integral_sub (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (f : ℝ → ℝ) :
    (∫ x, f x ∂dualSide a J D true) - (∫ x, f x ∂dualSide a J D false) =
      2 * ∑ i, D.weights i * f (D.nodes i) := by
  classical
  rw [dualSide, dualSide, integral_finsetSum_measure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (le_max_right _ _)),
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (le_max_right _ _))]
    have hmax : max (D.weights i) 0 - max (-D.weights i) 0 = D.weights i := by
      rcases le_total (D.weights i) 0 with hw | hw
      · simp [max_eq_right hw, max_eq_left (neg_nonneg.mpr hw)]
      · simp [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]
    rw [← sub_mul, ← mul_sub, hmax]
    ring
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A tilted side has first intensity moment exactly `a`. -/
lemma tiltedSide_integral_id (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) :
    ∫ x, x ∂tiltedSide a J D h = a := by
  rw [tiltedSide_integral_eq_sum a J D h ha]
  simp only [mul_zero, add_zero]
  calc
    ∑ i, (2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) *
        a / D.nodes i) * D.nodes i =
        a * ∑ i, 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hnode : D.nodes i ≠ 0 :=
        (ha.trans_le (D.nodes_mem i).1).ne'
      field_simp
    _ = a := by rw [dualSide_weights_sum, mul_one]

/-- Its score-weighted first moment is the rational-target moment of the
untilted Jordan side. -/
lemma tiltedSide_integral_intensity_score (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) :
    ∫ x, x * (x / (x + a)) ∂tiltedSide a J D h =
      a * ∫ x, rationalTarget a x ∂dualSide a J D h := by
  rw [tiltedSide_integral_eq_sum a J D h ha]
  simp only [zero_div, mul_zero, add_zero]
  rw [dualSide]
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hnode : 0 < D.nodes i := ha.trans_le (D.nodes_mem i).1
    have hweight :
        0 ≤ 2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) := by
      split <;> positivity
    rw [ENNReal.toReal_ofReal hweight]
    unfold rationalTarget
    field_simp
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The one-cell raw intensity expectation includes the retained reference
atom and the common tilted contribution. -/
lemma oneCellPrior_integral_latentIntensity (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J) :
    ∫ z, latentIntensity z ∂oneCellPrior a J D h =
      4 / (J : ℝ) + (1 - 1 / (J : ℝ)) * a := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have hscale : 0 ≤ 1 - 1 / (J : ℝ) := by
    rw [sub_nonneg, div_le_one hJpos]
    exact_mod_cast hJ
  have hlatent (s : Bool) (x : ℝ) :
      latentIntensity (latentFromIntensity s a x) = x := by
    by_cases hx : x = 0
    · simp [latentFromIntensity, zeroLatent, latentIntensity, hx]
    · simp [latentFromIntensity, latentIntensity, hx]
  have hcomp (s t : Bool) :
      Integrable (latentIntensity ∘ latentFromIntensity s a) (tiltedSide a J D t) := by
    simp_rw [Function.comp_def, hlatent]
    exact tiltedSide_integrable_any a J D t id
  have hmap (s t : Bool) :
      Integrable latentIntensity
        (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) :=
    (integrable_map_measure latentIntensity_stronglyMeasurable.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable).2 (hcomp s t)
  have hmapIntegral (s t : Bool) :
      ∫ z, latentIntensity z
          ∂Measure.map (latentFromIntensity s a) (tiltedSide a J D t) =
        ∫ x, x ∂tiltedSide a J D t := by
    rw [integral_map (latentFromIntensity_measurable s a).aemeasurable
      latentIntensity_stronglyMeasurable.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hlatent s)
  have hhalfFalse : Integrable latentIntensity
      ((1 / 2 : ENNReal) •
        Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h))) :=
    (hmap false (!h)).smul_measure (c := (1 / 2 : ENNReal)) (by norm_num)
  have hhalfTrue : Integrable latentIntensity
      ((1 / 2 : ENNReal) •
        Measure.map (latentFromIntensity true a) (tiltedSide a J D h)) :=
    (hmap true h).smul_measure (c := (1 / 2 : ENNReal)) (by norm_num)
  rw [oneCellPrior, integral_add_measure]
  · rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (J : ℝ)),
      integral_smul_measure, ENNReal.toReal_ofReal hscale,
      integral_add_measure hhalfFalse hhalfTrue,
      integral_smul_measure, integral_smul_measure,
      hmapIntegral false (!h), hmapIntegral true h]
    rw [tiltedSide_integral_id a J D (!h) ha,
      tiltedSide_integral_id a J D h ha]
    norm_num [referenceLatent, latentIntensity]
    ring
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · apply Integrable.smul_measure
    · rw [integrable_add_measure]
      exact ⟨hhalfFalse, hhalfTrue⟩
    · exact ENNReal.ofReal_ne_top

/-- Before orientation, the two hypotheses have opposite signed-score means
whose magnitude is the approximation-dual gap. -/
lemma oneCellPrior_integral_latentSignedScore (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J) :
    ∫ z, latentSignedScore z ∂oneCellPrior a J D h =
      (1 - 1 / (J : ℝ)) * a *
        (if h then dualTargetGap a J D else -dualTargetGap a J D) := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have hscale : 0 ≤ 1 - 1 / (J : ℝ) := by
    rw [sub_nonneg, div_le_one hJpos]
    exact_mod_cast hJ
  let g : ℝ → ℝ := fun x => x * (x / (x + a))
  have hlatent (s : Bool) (x : ℝ) :
      latentSignedScore (latentFromIntensity s a x) =
        (if s then 1 else -1) * g x := by
    cases s <;> by_cases hx : x = 0 <;>
      simp [latentSignedScore, latentFromIntensity, zeroLatent, latentIntensity,
        latentSignValue, latentSign, latentScore, g, hx]
  have hcomp (s t : Bool) :
      Integrable (latentSignedScore ∘ latentFromIntensity s a)
        (tiltedSide a J D t) :=
    tiltedSide_integrable_any a J D t _
  have hmap (s t : Bool) : Integrable latentSignedScore
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) :=
    (integrable_map_measure latentSignedScore_stronglyMeasurable.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable).2 (hcomp s t)
  have hmapIntegral (s t : Bool) :
      ∫ z, latentSignedScore z
          ∂Measure.map (latentFromIntensity s a) (tiltedSide a J D t) =
        ∫ x, (if s then 1 else -1) * g x ∂tiltedSide a J D t := by
    rw [integral_map (latentFromIntensity_measurable s a).aemeasurable
      latentSignedScore_stronglyMeasurable.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hlatent s)
  have hhalfFalse : Integrable latentSignedScore
      ((1 / 2 : ENNReal) •
        Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h))) :=
    (hmap false (!h)).smul_measure (c := (1 / 2 : ENNReal)) (by norm_num)
  have hhalfTrue : Integrable latentSignedScore
      ((1 / 2 : ENNReal) •
        Measure.map (latentFromIntensity true a) (tiltedSide a J D h)) :=
    (hmap true h).smul_measure (c := (1 / 2 : ENNReal)) (by norm_num)
  rw [oneCellPrior, integral_add_measure]
  · rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (J : ℝ)),
      integral_smul_measure, ENNReal.toReal_ofReal hscale,
      integral_add_measure hhalfFalse hhalfTrue,
      integral_smul_measure, integral_smul_measure,
      hmapIntegral false (!h), hmapIntegral true h]
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul, one_mul, integral_neg]
    norm_num [smul_eq_mul]
    have href : latentSignedScore referenceLatent = 0 := by
      simp [latentSignedScore, referenceLatent, latentIntensity, latentSignValue,
        latentSign, latentScore]
    rw [href, mul_zero, zero_add]
    dsimp [g]
    rw [tiltedSide_integral_intensity_score a J D (!h) ha,
      tiltedSide_integral_intensity_score a J D h ha]
    cases h <;> simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true,
      ↓reduceIte]
    · have hsub := dualSide_integral_sub a J D (rationalTarget a)
      dsimp [dualTargetGap] at hsub ⊢
      linear_combination -((1 - (J : ℝ)⁻¹) * a / 2) * hsub
    · have hsub := dualSide_integral_sub a J D (rationalTarget a)
      dsimp [dualTargetGap] at hsub ⊢
      linear_combination ((1 - (J : ℝ)⁻¹) * a / 2) * hsub
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · apply Integrable.smul_measure
    · rw [integrable_add_measure]
      exact ⟨hhalfFalse, hhalfTrue⟩
    · exact ENNReal.ofReal_ne_top

/-- Relabeling by the certificate orientation makes the score mean have the
requested hypothesis sign and the absolute dual separation. -/
lemma oneCellPrior_integral_oriented_latentSignedScore (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J) :
    ∫ z, latentSignedScore z
        ∂oneCellPrior a J D (orientedHypothesis a J D h) =
      (if h then 1 else -1) * (1 - 1 / (J : ℝ)) * a *
        |dualTargetGap a J D| := by
  rw [oneCellPrior_integral_latentSignedScore a J D
    (orientedHypothesis a J D h) ha hJ]
  unfold orientedHypothesis
  by_cases hgap : 0 ≤ dualTargetGap a J D
  · rw [if_pos hgap, abs_of_nonneg hgap]
    cases h <;> simp <;> ring
  · have hgap' : dualTargetGap a J D < 0 := lt_of_not_ge hgap
    rw [if_neg hgap, abs_of_neg hgap']
    cases h <;> simp <;> ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
