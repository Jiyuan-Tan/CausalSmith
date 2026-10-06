module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.RandomizedKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationPriorTarget
public import Causalean.Stat.Minimax.MinimaxRisk

/-! Centered squared-risk comparison and variance absorption for equations
(13)--(16) of the activated point-risk lower bound. -/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hd,hb,hq,hslice,π₀,π₁,h₀,h₁,hgap), [the stated mathematical conclusion holds](goal). -/
-- @node: activatedRarePriorATE_mean_separation
lemma activatedRarePriorATE_mean_separation (η : ℝ) (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hb : 0 < rareMass η n q) (hq : 0 < q)
    (hslice : RareArrivalSlice n q) {π₀ π₁ : Measure ℝ}
    (h₀ : FiniteReciprocalPrior (lowerEndpoint n q) π₀)
    (h₁ : FiniteReciprocalPrior (lowerEndpoint n q) π₁)
    (hgap : 1 / 12 ≤ |(∫ z, z⁻¹ ∂π₁) - ∫ z, z⁻¹ ∂π₀|) :
    (rareCount η n d q : ℝ) * rareMass η n q / 12 ≤
      |(∫ z, activatedRarePriorATE η n d q hd hb hq hslice z
          ∂Measure.pi (fun _ : Fin (rareCount η n d q) => π₁)) -
        (∫ z, activatedRarePriorATE η n d q hd hb hq hslice z
          ∂Measure.pi (fun _ : Fin (rareCount η n d q) => π₀))| := by
  rw [activatedRarePriorATE_integral η n d q hd hb hq hslice h₁,
    activatedRarePriorATE_integral η n d q hd hb hq hslice h₀,
    ← mul_sub, abs_mul, abs_of_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hb.le)]
  have h := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg (Nat.cast_nonneg (rareCount η n d q)) hb.le)
  nlinarith [h]

/-- Given [the specified inputs and assumptions](hyp:Ω,μ,T,τ,θ,herror,htarget,hcenter), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_centered_risk_le
lemma activated_centered_risk_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T τ : Ω → ℝ) (θ : ℝ)
    (herror : Integrable (fun ω => (T ω - τ ω) ^ 2) μ)
    (htarget : Integrable (fun ω => (τ ω - θ) ^ 2) μ)
    (hcenter : Integrable (fun ω => (T ω - θ) ^ 2) μ) :
    (∫ ω, (T ω - θ) ^ 2 ∂μ) ≤
      2 * (∫ ω, (T ω - τ ω) ^ 2 ∂μ) +
        2 * (∫ ω, (τ ω - θ) ^ 2 ∂μ) := by
  calc
    _ ≤ ∫ ω, 2 * (T ω - τ ω) ^ 2 + 2 * (τ ω - θ) ^ 2 ∂μ := by
      apply integral_mono hcenter ((herror.const_mul 2).add (htarget.const_mul 2))
      intro ω
      have h := add_sq_le (a := T ω - τ ω) (b := τ ω - θ)
      change (T ω - θ) ^ 2 ≤ 2 * (T ω - τ ω) ^ 2 + 2 * (τ ω - θ) ^ 2
      nlinarith [h]
    _ = _ := by rw [integral_add (herror.const_mul 2) (htarget.const_mul 2),
      integral_const_mul, integral_const_mul]

/-- Given [the specified inputs and assumptions](hyp:Ω,μ,T,hT,θ,s,hs,hint), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_error_probability_mul_sq_le_risk
lemma activated_error_probability_mul_sq_le_risk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℝ)
    (hT : Measurable T) (θ s : ℝ) (hs : 0 ≤ s)
    (hint : Integrable (fun ω => (T ω - θ) ^ 2) μ) :
    μ.real {ω | s ≤ |T ω - θ|} * s ^ 2 ≤ ∫ ω, (T ω - θ) ^ 2 ∂μ := by
  classical
  let E := {ω | s ≤ |T ω - θ|}
  have hE : MeasurableSet E := by
    dsimp [E]
    have hm : Measurable (fun ω => |T ω - θ|) := by fun_prop
    exact measurableSet_le measurable_const hm
  have hmono := integral_mono ((integrable_const (s ^ 2)).indicator hE) hint
    (fun ω => by
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        have hmiss : s ≤ |T ω - θ| := hω
        simpa only [sq_abs] using (sq_le_sq₀ hs (abs_nonneg _)).2 hmiss
      · rw [indicator_of_notMem hω]
        exact sq_nonneg _)
  rw [integral_indicator_const _ hE] at hmono
  simpa only [smul_eq_mul] using hmono

/-- Given [the specified inputs and assumptions](hyp:Ω,Q₀,Q₁,T,hT,θ₀,θ₁,h₀,h₁), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_center_testing_risk_lower
lemma activated_center_testing_risk_lower {Ω : Type*} [MeasurableSpace Ω]
    (Q₀ Q₁ : Measure Ω) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (T : Ω → ℝ) (hT : Measurable T) (θ₀ θ₁ : ℝ)
    (h₀ : Integrable (fun ω => (T ω - θ₀) ^ 2) Q₀)
    (h₁ : Integrable (fun ω => (T ω - θ₁) ^ 2) Q₁) :
    |θ₁ - θ₀| ^ 2 / 8 * (1 - Causalean.Stat.tvDist Q₀ Q₁) ≤
      max (∫ ω, (T ω - θ₀) ^ 2 ∂Q₀) (∫ ω, (T ω - θ₁) ^ 2 ∂Q₁) := by
  let s := |θ₁ - θ₀| / 2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsep : 2 * s ≤ |θ₀ - θ₁| := by dsimp [s]; rw [abs_sub_comm]; linarith
  have htest := Causalean.Stat.real_two_point_lower_bound
    (P₀ := Q₀) (P₁ := Q₁) hT hsep
  have hr₀ := activated_error_probability_mul_sq_le_risk Q₀ T hT θ₀ s hs h₀
  have hr₁ := activated_error_probability_mul_sq_le_risk Q₁ T hT θ₁ s hs h₁
  have hmax : max (Q₀.real {ω | s ≤ |T ω - θ₀|})
      (Q₁.real {ω | s ≤ |T ω - θ₁|}) * s ^ 2 ≤
      max (∫ ω, (T ω - θ₀) ^ 2 ∂Q₀) (∫ ω, (T ω - θ₁) ^ 2 ∂Q₁) := by
    rw [max_mul_of_nonneg _ _ (sq_nonneg s)]
    exact max_le_max hr₀ hr₁
  have h := (mul_le_mul_of_nonneg_right htest (sq_nonneg s)).trans hmax
  calc
    _ = (1 - Causalean.Stat.tvDist Q₀ Q₁) / 2 * s ^ 2 := by dsimp [s]; ring
    _ ≤ _ := h

/-- Given [the specified inputs and assumptions](hyp:Δ,J,b,R,C₀,C₁,tv,htv,htest,h₀,h₁), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_fuzzy_risk_variance_subtraction
lemma activated_fuzzy_risk_variance_subtraction (Δ J b R C₀ C₁ tv : ℝ)
    (htv : tv ≤ 1 / 8)
    (htest : Δ ^ 2 / 8 * (1 - tv) ≤ max C₀ C₁)
    (h₀ : C₀ ≤ 2 * R + J * b ^ 2 / 2)
    (h₁ : C₁ ≤ 2 * R + J * b ^ 2 / 2) :
    7 * Δ ^ 2 / 128 - J * b ^ 2 / 4 ≤ R := by
  have hupper := max_le h₀ h₁
  have hbudget := mul_le_mul_of_nonneg_left (show 7 / 8 ≤ 1 - tv by linarith)
    (show 0 ≤ Δ ^ 2 / 8 by positivity)
  linarith [hbudget.trans (htest.trans hupper)]

/-- Given [the specified inputs and assumptions](hyp:J,b,Δ,R,hJ,hb,hgap,hrisk), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_fuzzy_risk_absorb_variance
lemma activated_fuzzy_risk_absorb_variance (J : ℕ) (b Δ R : ℝ)
    (hJ : 2048 ≤ J) (hb : 0 ≤ b) (hgap : (J : ℝ) * b / 12 ≤ Δ)
    (hrisk : 7 * Δ ^ 2 / 128 - (J : ℝ) * b ^ 2 / 4 ≤ R) :
    (1 / 4096) * ((J : ℝ) * b) ^ 2 ≤ R := by
  have hJreal : (2048 : ℝ) ≤ J := by exact_mod_cast hJ
  have hΔ : 0 ≤ Δ := (by positivity : 0 ≤ (J : ℝ) * b / 12).trans hgap
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (J : ℝ) * b / 12) hΔ).2 hgap
  have hpenalty := mul_le_mul_of_nonneg_right hJreal
    (show 0 ≤ (J : ℝ) * b ^ 2 by positivity)
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:Ω,Q₀,Q₁,T,hT,θ₀,θ₁,b,R,J,hJ,hb,hgap,htv,hint₀,hint₁,hcenter₀,hcenter₁), [the stated mathematical conclusion holds](goal). -/
-- @node: activated_fuzzy_risk_lower_of_center_comparison
lemma activated_fuzzy_risk_lower_of_center_comparison
    {Ω : Type*} [MeasurableSpace Ω]
    (Q₀ Q₁ : Measure Ω) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (T : Ω → ℝ) (hT : Measurable T) (θ₀ θ₁ b R : ℝ) (J : ℕ)
    (hJ : 2048 ≤ J) (hb : 0 ≤ b)
    (hgap : (J : ℝ) * b / 12 ≤ |θ₁ - θ₀|)
    (htv : Causalean.Stat.tvDist Q₀ Q₁ ≤ 1 / 8)
    (hint₀ : Integrable (fun ω => (T ω - θ₀) ^ 2) Q₀)
    (hint₁ : Integrable (fun ω => (T ω - θ₁) ^ 2) Q₁)
    (hcenter₀ : (∫ ω, (T ω - θ₀) ^ 2 ∂Q₀) ≤ 2 * R + (J : ℝ) * b ^ 2 / 2)
    (hcenter₁ : (∫ ω, (T ω - θ₁) ^ 2 ∂Q₁) ≤ 2 * R + (J : ℝ) * b ^ 2 / 2) :
    (1 / 4096) * ((J : ℝ) * b) ^ 2 ≤ R := by
  have htest := activated_center_testing_risk_lower Q₀ Q₁ T hT θ₀ θ₁ hint₀ hint₁
  have hsubtract := activated_fuzzy_risk_variance_subtraction
    |θ₁ - θ₀| (J : ℝ) b R _ _ (Causalean.Stat.tvDist Q₀ Q₁)
    htv htest hcenter₀ hcenter₁
  exact activated_fuzzy_risk_absorb_variance J b |θ₁ - θ₀| R hJ hb hgap hsubtract

end CausalSmith.Stat.MarRareqLogfrontier
