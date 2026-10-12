module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingFamily
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationAffinity

/-!
# Balanced response density and its sign mark

The scalar density factorization and centered mark moments support the full-record
likelihood density and the orthogonality expansion.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- The symmetric mixture of the two translated baseline densities. -/
def balancedDensity (δ y : ℝ) : ℝ := (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-δ) + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ))/2
-- @realizes g(balanced translated baseline density)
/-- The bounded response mark, extended by zero where the density vanishes. -/
def responseMark (δ y : ℝ) : ℝ :=
  if 0 < balancedDensity δ y then
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-δ) - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ))/(2*balancedDensity δ y) else 0
-- @realizes hmark(difference divided by 2g on g>0, zero otherwise)
/-- The second moment of the response mark under the balanced density. -/
def markEnergy (δ : ℝ) : ℝ := ∫ y, responseMark δ y ^ 2 * balancedDensity δ y
-- @realizes gamma(integral h²g)
/-- [The response mark belongs to [-1,1].](goal) -/
lemma responseMark_mem_Icc (δ y : ℝ) : responseMark δ y ∈ Set.Icc (-1) 1 := by
  have hminus := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y-δ)
  have hplus := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y+δ)
  unfold responseMark
  split_ifs with hg
  · have hden : 0 < 2 * balancedDensity δ y := by positivity
    constructor
    · apply (le_div_iff₀ hden).mpr
      dsimp [balancedDensity]
      linarith
    · apply (div_le_iff₀ hden).mpr
      dsimp [balancedDensity]
      linarith
  · constructor <;> norm_num
-- @realizes hmark(derived range [-1,1])
/-- [Balanced response densities are measurable and normalized.](goal) -/
lemma balancedDensity_probability (δ : ℝ) :
    Measurable (balancedDensity δ) ∧ (∀ y, 0 ≤ balancedDensity δ y) ∧ -- @realizes g(nonnegative normalized density)
    Integrable (balancedDensity δ) ∧ (∫ y, balancedDensity δ y) = 1 := by
  have hm := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized δ
  have hp : Integrable (fun y => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ)) ∧
      (∫ y, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ)) = 1 := by
    simpa only [sub_neg_eq_add] using
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized (-δ)
  refine ⟨?_, ?_, (hm.1.add hp.1).div_const 2, ?_⟩
  · unfold balancedDensity CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity
    apply Measurable.div_const
    apply Measurable.add
    all_goals
      apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      · fun_prop
      · fun_prop
  · intro y
    exact div_nonneg
      (add_nonneg
        (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y-δ))
        (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y+δ)))
      (by norm_num)
  · unfold balancedDensity
    have hmi := hm.1
    have hpi := hp.1
    integral_linearity
    rw [hm.2, hp.2]
    norm_num

/-- [The mark energy belongs to [0,1].](goal) -/
lemma markEnergy_mem_Icc (δ : ℝ) : markEnergy δ ∈ Set.Icc 0 1 := by
  obtain ⟨_, hg0, hgi, hg1⟩ := balancedDensity_probability δ
  have hh0 (y : ℝ) : 0 ≤ responseMark δ y ^ 2 * balancedDensity δ y :=
    mul_nonneg (sq_nonneg _) (hg0 y)
  have hh1 (y : ℝ) : responseMark δ y ^ 2 * balancedDensity δ y ≤ balancedDensity δ y := by
    have hh := responseMark_mem_Icc δ y
    have hs : responseMark δ y ^ 2 ≤ 1 := by nlinarith [hh.1, hh.2]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (hg0 y)
  constructor
  · exact integral_nonneg hh0
  · calc
      markEnergy δ ≤ ∫ y, balancedDensity δ y :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hh0) hgi
          (Filter.Eventually.of_forall hh1)
      _ = 1 := hg1
-- @realizes gamma(derived energy range [0,1])

/-- [Multiplying the mark by its density cancels the ratio, including density-zero points.](goal) -/
-- @node: responseMark_mul_balancedDensity
lemma responseMark_mul_balancedDensity (δ y : ℝ) :
    responseMark δ y * balancedDensity δ y =
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-δ) -
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ)) / 2 := by
  have hm := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y-δ)
  have hp := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg (y+δ)
  unfold responseMark
  split_ifs with hg
  · field_simp
  · have hz : balancedDensity δ y = 0 :=
      le_antisymm (le_of_not_gt hg) ((balancedDensity_probability δ).2.1 y)
    have hsum :
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-δ) +
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ) = 0 := by
      dsimp [balancedDensity] at hz
      linarith
    have hm0 : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-δ) = 0 := by
      linarith
    have hp0 : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ) = 0 := by
      linarith
    simp [hm0, hp0]

/-- [Each translated baseline has exactly the sign-mark likelihood factor.](goal) -/
-- @node: shiftedDensity_eq_balancedDensity_mul_mark
lemma shiftedDensity_eq_balancedDensity_mul_mark (δ y : ℝ) (σ : Bool) :
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity
        (y - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * δ) =
      balancedDensity δ y *
        (1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * responseMark δ y) := by
  have h := responseMark_mul_balancedDensity δ y
  cases σ <;>
    simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf,
      Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, sub_neg_eq_add] <;>
    dsimp [balancedDensity] at h ⊢ <;> nlinarith

/-- [The density-weighted mark is integrable as a difference of two translated densities.](goal) -/
-- @node: responseMark_weighted_integrable
lemma responseMark_weighted_integrable (δ : ℝ) :
    Integrable (fun y => responseMark δ y * balancedDensity δ y) := by
  have hm := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized δ
  have hp := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized (-δ)
  simpa only [responseMark_mul_balancedDensity, sub_neg_eq_add, Pi.sub_apply] using (hm.1.sub hp.1).div_const 2

/-- [The balanced response mark has zero density-weighted first moment.](goal) -/
-- @node: responseMark_weighted_integral_zero
lemma responseMark_weighted_integral_zero (δ : ℝ) :
    (∫ y, responseMark δ y * balancedDensity δ y) = 0 := by
  simp only [responseMark_mul_balancedDensity]
  have hm := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized δ
  have hp := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized (-δ)
  simp only [sub_neg_eq_add] at hp
  rw [integral_div, integral_sub hm.1 hp.1, hm.2, hp.2]
  norm_num

/-- [The extended-by-zero response mark is Borel measurable.](goal) -/
-- @node: responseMark_measurable
@[fun_prop] lemma responseMark_measurable (δ : ℝ) : Measurable (responseMark δ) := by
  unfold responseMark
  apply Measurable.ite (measurableSet_lt measurable_const (balancedDensity_probability δ).1)
  · have ht (t : ℝ) : Measurable (fun y =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-t)) := by
      unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity
      apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
      · fun_prop
      · fun_prop
    have hp : Measurable (fun y =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y+δ)) := by
      simpa only [sub_neg_eq_add] using ht (-δ)
    exact ((ht δ).sub hp).div (measurable_const.mul (balancedDensity_probability δ).1)
  · fun_prop

/-- [Integration under the balanced response measure is integration against its real density.](goal) -/
-- @node: balancedResponse_integral_eq
lemma balancedResponse_integral_eq (δ : ℝ) (v : ℝ → ℝ) :
    (∫ y, v y ∂volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))) =
      ∫ y, v y * balancedDensity δ y := by
  rw [integral_withDensity_eq_integral_toReal_smul
    ((balancedDensity_probability δ).1.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal ((balancedDensity_probability δ).2.1 _),
    smul_eq_mul, mul_comm]

/-- [The centered response mark is integrable under its actual balanced law.](goal) -/
-- @node: responseMark_balanced_integrable
lemma responseMark_balanced_integrable (δ : ℝ) :
    Integrable (responseMark δ)
      (volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))) := by
  apply (integrable_withDensity_iff
    ((balancedDensity_probability δ).1.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal ((balancedDensity_probability δ).2.1 _)] using
    responseMark_weighted_integrable δ

/-- [The response mark has zero first moment under the balanced response law.](goal) -/
-- @node: responseMark_balanced_integral_zero
lemma responseMark_balanced_integral_zero (δ : ℝ) :
    (∫ y, responseMark δ y
      ∂volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))) = 0 := by
  rw [balancedResponse_integral_eq, responseMark_weighted_integral_zero]

/-- [The squared mark is density-integrable, dominated by the normalized balanced density.](goal) -/
-- @node: responseMark_sq_weighted_integrable
lemma responseMark_sq_weighted_integrable (δ : ℝ) :
    Integrable (fun y => responseMark δ y ^ 2 * balancedDensity δ y) := by
  apply (balancedDensity_probability δ).2.2.1.mono'
  · exact ((responseMark_measurable δ).pow_const 2).mul
      (balancedDensity_probability δ).1 |>.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro y
    have hg := (balancedDensity_probability δ).2.1 y
    have hh := responseMark_mem_Icc δ y
    have hs : responseMark δ y ^ 2 ≤ 1 := by nlinarith [hh.1, hh.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hg)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hg

/-- [The squared response mark is integrable under the balanced response law.](goal) -/
-- @node: responseMark_sq_balanced_integrable
lemma responseMark_sq_balanced_integrable (δ : ℝ) :
    Integrable (fun y => responseMark δ y ^ 2)
      (volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))) := by
  apply (integrable_withDensity_iff
    ((balancedDensity_probability δ).1.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal ((balancedDensity_probability δ).2.1 _)] using
    responseMark_sq_weighted_integrable δ

/-- [The response mark's second moment under its law is precisely the declared energy.](goal) -/
-- @node: responseMark_balanced_secondMoment
lemma responseMark_balanced_secondMoment (δ : ℝ) :
    (∫ y, responseMark δ y ^ 2
      ∂volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))) = markEnergy δ := by
  exact balancedResponse_integral_eq δ (fun y => responseMark δ y ^ 2)

/-- [A translated baseline law is the balanced law tilted by the exact scalar sign likelihood.](goal) -/
-- @node: shiftedResponseLaw_eq_withDensity
lemma shiftedResponseLaw_eq_withDensity (δ : ℝ) (σ : Bool) :
    volume.withDensity (fun y => ENNReal.ofReal
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity
        (y - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * δ))) =
    (volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))).withDensity
      (fun y => ENNReal.ofReal
        (1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * responseMark δ y)) := by
  have ht : Measurable (fun y => ENNReal.ofReal
      (1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * responseMark δ y)) := by
    fun_prop
  rw [← withDensity_mul volume ((balancedDensity_probability δ).1.ennreal_ofReal) ht]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply]
  rw [shiftedDensity_eq_balancedDensity_mul_mark, ENNReal.ofReal_mul
    ((balancedDensity_probability δ).2.1 y)]

end CausalSmith.Experimentation.NoisygraphTtePrecision
