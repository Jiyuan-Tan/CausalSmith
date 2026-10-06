module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CapacityHandle
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionBudget
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionKernel

/-! # Reflection, common shift, and Fourier transfer

The product-law assertion simultaneously states iid Haar sampling and independence from
the common shift. The arbitrary assignment kernel reads only W and its own fresh randomness.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

-- @node: lem:reflection-transfer
/-- Even reflection transfers restriction norms, random shifts produce independent Haar
samples, and squared imbalance decomposes over the Fourier coefficients in L². This uses [the stated conclusion](goal). -/
lemma reflection_transfer :
    (∀ p : ℕ, p = 1 ∨ p = 2 → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∃ c : ℝ, 0 < c ∧ ∀ g : Cube p → ℝ,
        Measurable g → MemLp g 2 (cubeMeasure p) → sobolevNormSq p s g < ⊤ →
          componentFourierBudget p s g ≤ ENNReal.ofReal c * sobolevNormSq p s g) ∧
    (∀ d : ℕ, 2 ≤ d → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ m : CenteredL2Fn d, SobolevClass d s m → reflectedBudget s m.val ≤
        ENNReal.ofReal CUpper) ∧
    (∀ (n d : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      (X : Ω → Covariates n d), UniformDraw μ X →
      (μ.prod ((reflectionLaw n d).prod (torusMeasure d))).map
        (fun ω => (shiftedSample (X ω.1) ω.2.1 ω.2.2, ω.2.2)) =
          (Measure.pi (fun _ : Fin n => torusMeasure d)).prod (torusMeasure d)) ∧
    (∀ (n d : ℕ), 2 ≤ n → 2 ≤ d → ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ m : CenteredL2Fn d, SobolevClass d s m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Covariates n d),
      UniformDraw μ X → ∀ ρ : Kernel (Fin n → Torus d) (Signs n), IsMarkovKernel ρ →
      (∫⁻ ω, ∫⁻ z, ENNReal.ofReal |∑ i, sgn (z i) * m.val (X ω.1 i)| ^ 2
        ∂ρ (shiftedSample (X ω.1) ω.2.1 ω.2.2)
        ∂μ.prod ((reflectionLaw n d).prod (torusMeasure d))) =
      ∑' k : Fin d → ℤ, ENNReal.ofReal ‖Fhat m.val k‖ ^ 2 *
        ∫⁻ w, ∫⁻ z, ENNReal.ofReal ‖∑ i, (sgn (z i) : ℂ) * ek k (w i)‖ ^ 2
          ∂ρ w ∂Measure.pi (fun _ : Fin n => torusMeasure d))  := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp s hs hs1
    refine ⟨1, zero_lt_one, ?_⟩
    intro g hg hLp hfinite
    simpa using exact_reflection_budget.1 p hp s hs hs1 g hg hLp hfinite
  · intro d hd s hs hs1 m hm
    have hbudget := (exact_reflection_budget.2 d s hd hs hs1 m hm).2.2.1
    exact hbudget.trans (by norm_num [CUpper])
  · intro n d Ω _ μ X hX
    exact reflectionLaw_map_shiftedSample n d Ω μ X hX
  · intro n d hn hd s hs hs1 m hm Ω _ μ X hX ρ hρ
    letI : IsMarkovKernel ρ := hρ
    exact reflection_kernel_fourier_identity (by omega) m Ω μ X hX ρ

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
