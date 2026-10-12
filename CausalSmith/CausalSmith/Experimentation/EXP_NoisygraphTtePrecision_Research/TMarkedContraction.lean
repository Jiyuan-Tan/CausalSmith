module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ContractionTV
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingSupport

/-!
# Marked planted-matching full-record contraction

Assembles the full-record contraction from its density, expansion, and posterior-energy
lemmas, with an explicit proof of the calibrated numerical bound.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hκ,hγ,hδ), [The specified amplitude makes the response-mark/channel energy product at most 1/625.](goal) -/
-- @node: calibrated_mark_channel_energy_le
lemma calibrated_mark_channel_energy_le (γ κ δ : ℝ) (hκ : 0 < κ)
    (hγ : γ ≤ 16*Real.pi^2*δ^2)
    (hδ : δ = 1/(100*Real.pi*Real.sqrt κ)) : γ*κ ≤ 1/625 := by
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hp := Real.pi_pos
  have hsp : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hid : (16*Real.pi^2*δ^2)*κ = 1/625 := by
    rw [hδ]
    field_simp
    nlinarith [hs]
  calc
    γ*κ ≤ (16*Real.pi^2*δ^2)*κ := mul_le_mul_of_nonneg_right hγ hκ.le
    _ = 1/625 := hid

/-- Given [the stated assumptions](hyp:hx0,hx), [The numerical geometric-series bound at 9/40000 is strictly below (1/50)^2.](goal) -/
-- @node: calibrated_contraction_sqrt_lt
lemma calibrated_contraction_sqrt_lt (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 9/40000) : Real.sqrt (x/(1-x^2)) < 1/50 := by
  have hx1 : x < 1 := lt_of_le_of_lt hx (by norm_num)
  have hsq : x^2 ≤ (9/40000 : ℝ)^2 := by nlinarith
  have hden : 0 < 1-x^2 := by nlinarith
  have hquot : x/(1-x^2) < (1/50 : ℝ)^2 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hnonneg : 0 ≤ x/(1-x^2) := div_nonneg hx0 hden.le
  have hs := Real.sq_sqrt hnonneg
  have hs0 := Real.sqrt_nonneg (x/(1-x^2))
  nlinarith

/-- Given [the stated assumptions](hyp:hn,hm,hfit,hr,hrq,hq,hδ,hδu,ha,hH,hi), [The exact full-record densities and odd-order identity give the uniform planted energy
bounds and the declared numerical causal-sign TV separation.](goal) -/
-- @node: thm:marked-contraction
theorem marked_contraction (n m : ℕ) (hn : 4 ≤ n) (hm : 1 ≤ m) (hfit : 2*m ≤ n) -- @realizes m(natural carrier with 1≤m and 2*m≤n, hence m∈{1,...,floor(n/2)})
    (q r δ : ℝ) (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1) (hδ : 0 < δ) (hδu : δ ≤ 1/12)
    (D : Design (Fin n)) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) :
    let P := fun σ => signLaw n m hfit D σ δ
    let Q := referenceLaw n m hfit q r δ
    let L := fun σ => likelihoodPoly n m hfit q r δ σ
    let x := (9/64)*markEnergy δ*kappa q r
    (∀ σ, P σ ≪ Q ∧ (P σ).rnDeriv Q =ᵐ[Q] fun o => ENNReal.ofReal (L σ o)) ∧
    (∫ o, (L true o - L false o)^2 ∂Q) =
      4 * ∑ k ∈ (Finset.Icc 1 m).filter Odd, markEnergy δ ^ k * orderEnergy n m hfit q r k ∧
    (q/2 ≤ m*r → ∀ k ∈ Finset.Icc 1 m, orderEnergy n m hfit q r k ≤ ((9/64)*kappa q r)^k) ∧
    (q/2 ≤ m*r → x < 1 → Causalean.Stat.tvDist (P true) (P false) ≤ Real.sqrt (x/(1-x^2))) ∧
    (q/2 ≤ m*r → δ = 1/(100*Real.pi*Real.sqrt (kappa q r)) →
      Causalean.Stat.tvDist (P true) (P false) < 1/50) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact likelihood_density n m hm hfit q r δ hr hrq hq hδ hδu D ha hH hi σ
  · exact likelihood_odd_energy n m hm hfit q r δ hr hrq hq hδ hδu
  · intro hregime k hk
    exact posterior_order_energy_le n m hm hfit q r hr hrq hq hregime k hk
  · intro hregime hx
    exact contraction_tv n m hm hfit q r δ hr hrq hq hδ hδu D ha hH hi hregime hx
  · intro hregime hcal
    have hκ1 := kappa_ge_one_of_positive q r hr hrq hq
    have hκ : 0 < kappa q r := lt_of_lt_of_le (by norm_num) hκ1
    have hγ := (matching_support n m 1 hn (by omega) (by omega)
      hm hfit true δ hδ hδu).2.2.1
    have henergy := calibrated_mark_channel_energy_le (markEnergy δ) (kappa q r) δ
      hκ hγ hcal
    have hx0 : 0 ≤ (9/64)*markEnergy δ*kappa q r :=
      mul_nonneg (mul_nonneg (by norm_num) (markEnergy_mem_Icc δ).1) hκ.le
    have hxle : (9/64)*markEnergy δ*kappa q r ≤ 9/40000 := by
      nlinarith
    have hx : (9/64)*markEnergy δ*kappa q r < 1 :=
      lt_of_le_of_lt hxle (by norm_num)
    exact lt_of_le_of_lt
      (contraction_tv n m hm hfit q r δ hr hrq hq hδ hδu D ha hH hi hregime hx)
      (calibrated_contraction_sqrt_lt _ hx0 hxle)

end CausalSmith.Experimentation.NoisygraphTtePrecision
