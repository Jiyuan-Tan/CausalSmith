module
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! A quantitative testing floor for the complete-arrival two-point experiment. -/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: complete_arrival_exp_eighth_lt_two
/-- [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_exp_eighth_lt_two : Real.exp (1 / 8 : ℝ) < 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmon : Real.exp (1 / 8 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    exact Real.exp_le_exp.mpr (by norm_num)
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  nlinarith [Real.exp_one_lt_three]

-- @node: complete_arrival_product_testing_half
/-- Given [the specified inputs and assumptions](hyp:Ω,n,hn,P₁,P₀,hac,hint,hchi), [the stated mathematical conclusion holds](goal). -/
lemma complete_arrival_product_testing_half {Ω : Type}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (n : ℕ) (hn : 1 ≤ n) (P₁ P₀ : Measure Ω)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₀]
    (hac : P₁ ≪ P₀)
    (hint : Integrable (fun x => ((P₁.rnDeriv P₀ x).toReal - 1) ^ 2) P₀)
    (hchi : Causalean.Stat.chiSqDiv P₁ P₀ ≤ (1 / 8 : ℝ) / n) :
    ∀ A : Set (Fin n → Ω), MeasurableSet A →
      (Measure.pi (fun _ : Fin n => P₁)).real Aᶜ +
        (Measure.pi (fun _ : Fin n => P₀)).real A ≥ 1 / 2 := by
  intro A hA
  let Q₁ : Measure (Fin n → Ω) := Measure.pi (fun _ => P₁)
  let Q₀ : Measure (Fin n → Ω) := Measure.pi (fun _ => P₀)
  have hprod_ac : Q₁ ≪ Q₀ :=
    Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous
      P₁ P₀ hac n
  have hprod_int : Integrable
      (fun x => ((Q₁.rnDeriv Q₀ x).toReal - 1) ^ 2) Q₀ :=
    Causalean.Stat.pi_iid_integrable_sq_dev P₁ P₀ hac hint n
  have hchi_non : 0 ≤ Causalean.Stat.chiSqDiv P₁ P₀ :=
    Causalean.Stat.chiSqDiv_nonneg
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : (n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀ ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hchi (le_of_lt hnpos)
    field_simp [hnpos.ne'] at h
    linarith
  have hprod_chi : Causalean.Stat.chiSqDiv Q₁ Q₀ ≤
      Real.exp (1 / 8 : ℝ) - 1 := by
    have hident := Causalean.Stat.one_add_chiSqDiv_pi_iid_general
      P₁ P₀ hac hint n
    change 1 + Causalean.Stat.chiSqDiv Q₁ Q₀ =
      (1 + Causalean.Stat.chiSqDiv P₁ P₀) ^ n at hident
    have hpow : (1 + Causalean.Stat.chiSqDiv P₁ P₀) ^ n ≤
        Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv P₁ P₀) := by
      calc
        _ ≤ (Real.exp (Causalean.Stat.chiSqDiv P₁ P₀)) ^ n :=
          pow_le_pow_left₀ (by linarith)
            (by linarith [Real.add_one_le_exp (Causalean.Stat.chiSqDiv P₁ P₀)]) n
        _ = _ := by rw [← Real.exp_nat_mul]
    linarith [hpow, Real.exp_le_exp.mpr hmul]
  letI : IsProbabilityMeasure Q₁ := by dsimp [Q₁]; infer_instance
  letI : IsProbabilityMeasure Q₀ := by dsimp [Q₀]; infer_instance
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    Q₁ Q₀ hprod_ac hprod_int
  have hchi_lt : Causalean.Stat.chiSqDiv Q₁ Q₀ < 1 := by
    linarith [complete_arrival_exp_eighth_lt_two]
  have htv_le : Causalean.Stat.tvDist Q₁ Q₀ ≤ 1 / 2 := by
    have hsqrt := Real.sqrt_le_sqrt (le_of_lt hchi_lt)
    have h := htv.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Real.sqrt_one] using hsqrt) (by norm_num : (0 : ℝ) ≤ 1 / 2))
    simpa using h
  have htest := Causalean.Stat.one_sub_tvDist_le_test
    (μ := Q₁) (ν := Q₀) hA.compl
  simpa only [compl_compl] using (le_trans (by linarith : (1 / 2 : ℝ) ≤
    1 - Causalean.Stat.tvDist Q₁ Q₀) htest)

end CausalSmith.Stat.MarRareqLogfrontier
