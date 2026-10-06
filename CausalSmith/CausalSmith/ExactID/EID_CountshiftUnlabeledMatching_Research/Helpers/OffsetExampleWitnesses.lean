module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.OffsetExamples

/-! Concrete fixed and randomized offset witnesses. -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: fixedOffsetMeasure
private def fixedOffsetMeasure : Measure ℝ := Measure.dirac 2

-- @node: fixedOffsetMeasure_probability
private lemma fixedOffsetMeasure_probability :
    IsProbabilityMeasure fixedOffsetMeasure := by
  rw [isProbabilityMeasure_iff]
  simp [fixedOffsetMeasure]

-- @node: randomOffsetMeasure
private def randomOffsetMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / 3 : ℝ) • Measure.dirac (1 / 2 : ℝ) +
    ENNReal.ofReal (2 / 3 : ℝ) • Measure.dirac 2

-- @node: randomOffsetMeasure_probability
private lemma randomOffsetMeasure_probability :
    IsProbabilityMeasure randomOffsetMeasure := by
  rw [isProbabilityMeasure_iff]
  simp [randomOffsetMeasure]
  have h3 : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [h3, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 3⁻¹)
      (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  norm_num

-- @node: randomOffsetMeasure_inv_integrable
private lemma randomOffsetMeasure_inv_integrable :
    Integrable (fun s : ℝ => s⁻¹) randomOffsetMeasure := by
  rw [randomOffsetMeasure, integrable_add_measure]
  constructor <;> apply Integrable.smul_measure (integrable_dirac (by finiteness)) <;> simp

-- @node: randomOffsetMeasure_inv_sq_integrable
private lemma randomOffsetMeasure_inv_sq_integrable :
    Integrable (fun s : ℝ => s⁻¹ ^ 2) randomOffsetMeasure := by
  rw [randomOffsetMeasure, integrable_add_measure]
  constructor <;> apply Integrable.smul_measure (integrable_dirac (by finiteness)) <;> simp

-- @node: randomOffsetMeasure_inv_integral
private lemma randomOffsetMeasure_inv_integral :
    (∫ s : ℝ, s⁻¹ ∂randomOffsetMeasure) = 1 := by
  rw [randomOffsetMeasure, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac]
    norm_num [ENNReal.toReal_ofReal]
  · apply Integrable.smul_measure (integrable_dirac (by finiteness))
    simp
  · apply Integrable.smul_measure (integrable_dirac (by finiteness))
    simp

-- @node: offsetExample_gaussian_exp_integral_pos
private lemma offsetExample_gaussian_exp_integral_pos :
    0 < ∫ v : EuclideanSpace ℝ (Fin 1), Real.exp (v 0)
      ∂multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin 1)))
    (S := (1 : Matrix (Fin 1) (Fin 1) ℝ)) Matrix.PosDef.one.posSemidef (i := 0)
  have h := mgf_gaussianReal hp.map_eq 1
  rw [show (∫ v : EuclideanSpace ℝ (Fin 1), Real.exp (v 0)
      ∂multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
      Real.exp ((0 : ℝ) * 1 + (1 : NNReal) * 1 ^ 2 / 2) by
        simpa [mgf] using h]
  positivity

/-- A constant positive nonunit offset gives genuinely different adjusted
second-factorial expectations. -/
-- @node: fixed_offset_atomic_model_witness
lemma fixed_offset_atomic_model_witness :
    ∃ (Ω' : Type) (ms' : MeasurableSpace Ω') (μ' : Measure Ω'),
      letI : MeasurableSpace Ω' := ms'
      ∃ 𝔐' : AtomicCountModel 1 1 Ω' μ',
        μ' Set.univ = 1 ∧
        (∀ᵐ ω ∂μ', 𝔐'.S 0 ω 0 ≠ 1) ∧
        (∫ ω, firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 *
          (firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 - 1) ∂μ') ≠
          ∫ ω, secondFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 ∂μ' := by
  let _ : IsProbabilityMeasure fixedOffsetMeasure := fixedOffsetMeasure_probability
  have hpos : ∀ᵐ s ∂fixedOffsetMeasure, 0 < s := by simp [fixedOffsetMeasure]
  have hne : ∀ᵐ s ∂fixedOffsetMeasure, s ≠ 1 := by simp [fixedOffsetMeasure]
  have hinv : Integrable (fun s : ℝ => s⁻¹) fixedOffsetMeasure :=
    integrable_dirac (by finiteness)
  have hinv2 : Integrable (fun s : ℝ => s⁻¹ ^ 2) fixedOffsetMeasure :=
    integrable_dirac (by finiteness)
  refine ⟨OffsetExampleSpace, inferInstance, offsetExampleLaw fixedOffsetMeasure, ?_⟩
  let 𝔐 := offsetExampleModel fixedOffsetMeasure hpos
  refine ⟨𝔐, isProbabilityMeasure_iff.mp (offsetExample_law_probability fixedOffsetMeasure),
    ?_, ?_⟩
  · simpa [𝔐] using offsetExample_nonunit fixedOffsetMeasure hpos hne 0
  · rw [← sub_ne_zero]
    rw [offsetExample_moment_difference fixedOffsetMeasure hpos hinv hinv2]
    apply mul_ne_zero
    · norm_num [fixedOffsetMeasure]
    · exact ne_of_gt offsetExample_gaussian_exp_integral_pos

/-- A positive nonunit random offset with mean inverse one makes the two
adjusted second-factorial expectations coincide. -/
-- @node: random_offset_atomic_model_witness
lemma random_offset_atomic_model_witness :
    ∃ (Ω' : Type) (ms' : MeasurableSpace Ω') (μ' : Measure Ω'),
      letI : MeasurableSpace Ω' := ms'
      ∃ 𝔐' : AtomicCountModel 1 1 Ω' μ',
        μ' Set.univ = 1 ∧
        (∀ᵐ ω ∂μ', 𝔐'.S 0 ω 0 ≠ 1) ∧
        (∫ ω, firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 *
          (firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 - 1) ∂μ') =
          ∫ ω, secondFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 ∂μ' := by
  let _ : IsProbabilityMeasure randomOffsetMeasure := randomOffsetMeasure_probability
  have hpos : ∀ᵐ s ∂randomOffsetMeasure, 0 < s := by simp [randomOffsetMeasure]
  have hne : ∀ᵐ s ∂randomOffsetMeasure, s ≠ 1 := by simp [randomOffsetMeasure]
  refine ⟨OffsetExampleSpace, inferInstance, offsetExampleLaw randomOffsetMeasure, ?_⟩
  let 𝔐 := offsetExampleModel randomOffsetMeasure hpos
  refine ⟨𝔐, isProbabilityMeasure_iff.mp (offsetExample_law_probability randomOffsetMeasure),
    ?_, ?_⟩
  · simpa [𝔐] using offsetExample_nonunit randomOffsetMeasure hpos hne 0
  · apply sub_eq_zero.mp
    rw [offsetExample_moment_difference randomOffsetMeasure hpos
      randomOffsetMeasure_inv_integrable randomOffsetMeasure_inv_sq_integrable,
      randomOffsetMeasure_inv_integral, sub_self, zero_mul]

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
