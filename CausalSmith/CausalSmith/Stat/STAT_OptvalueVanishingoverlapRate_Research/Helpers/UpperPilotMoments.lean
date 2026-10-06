module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilot

/-! # Pilot clipping-scale second moments

Roadmap equation (19) follows from the deterministic anchored-radius bound,
a linear envelope for the pilot midpoint, and the marginal Poisson means.
The elementary square-root envelope avoids needing joint independence for this step.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open scoped BigOperators

/-- A pilot midpoint is controlled by a linear count envelope, including at zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotMidpoint_le_linear_center (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ) (j : Fin 4) :
    pilotMidpoint H hH m L Np j ≤
      (1 + H) * pilotCenterFormula m Np j + 2 * H * (L / m) := by
  have hc : 0 ≤ pilotCenterFormula m Np j := by unfold pilotCenterFormula; positivity
  have hδ : 0 ≤ L / m := div_nonneg hL hm.le
  have hs := two_mul_le_add_of_sq_le_mul hc hδ
    (Real.sq_sqrt (mul_nonneg hc hδ)).le
  have he := pilotMidpoint_sub_center_le_halfWidth H hH m L hm hL Np j
  have ha := le_abs_self (pilotMidpoint H hH m L Np j - pilotCenterFormula m Np j)
  dsimp only [pilotHalfWidthFormula] at he
  rw [mul_div_assoc] at he
  nlinarith [Real.sqrt_nonneg (pilotCenterFormula m Np j * (L / m))]

/-- The four-coordinate mass is the sum of the four outcome atoms. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma totalMassVec_eq_sum_coordinates (b : Fin 4 → ℝ) :
    totalMassVecFormula b = ∑ j, b j := by
  simp [totalMassVecFormula, armMassVecFormula, cellIdx, Fin.sum_univ_succ]
  ring

/-- The total pilot midpoint mass has a linear envelope with four width terms. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotTotalMass_le_linear_centers (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ) :
    totalMassVecFormula (pilotMidpoint H hH m L Np) ≤
      (1 + H) * (∑ j, pilotCenterFormula m Np j) + 8 * H * (L / m) := by
  rw [totalMassVec_eq_sum_coordinates]
  calc
    _ ≤ ∑ j, ((1 + H) * pilotCenterFormula m Np j + 2 * H * (L / m)) :=
      Finset.sum_le_sum fun j _ => pilotMidpoint_le_linear_center H hH m L hm hL Np j
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Squaring the anchored-radius envelope keeps only one inverse-overlap power in the term proportional to the random total midpoint mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hε1), the [stated conclusion](goal) holds. -/
lemma pilotClippingScale_sq_le (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Np : Fin 4 → ℕ) :
    clippingScaleFormula ε (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np) ^ 2 ≤
      512 * H ^ 2 * (totalMassVecFormula (pilotMidpoint H hH m L Np) * (L / m) / ε +
        ((L / m) / ε) ^ 2) := by
  have hB : 0 ≤ totalMassVecFormula (pilotMidpoint H hH m L Np) := by
    rw [totalMassVec_eq_sum_coordinates]
    exact Finset.sum_nonneg fun j _ => pilotMidpoint_nonneg H hH m L hm Np j
  have hδ : 0 ≤ L / m := div_nonneg hL hm.le
  have hscale := pilotClippingScale_le_total_scale H hH m L ε hm hL hε hε1 Np
  have hr (j : Fin 4) : 0 ≤ pilotRadiusFormula H hH m L Np j := by
    have he := le_max_right 0 (pilotCenterFormula m Np j - pilotHalfWidthFormula H hH m L Np j)
    have hh : 0 ≤ pilotHalfWidthFormula H hH m L Np j := by unfold pilotHalfWidthFormula; positivity
    have hc : 0 ≤ pilotCenterFormula m Np j := by unfold pilotCenterFormula; positivity
    dsimp [pilotRadiusFormula, pilotLower, pilotUpperFormula]
    rw [max_def]
    split_ifs <;> linarith
  have hS : 0 ≤ clippingScaleFormula ε (pilotMidpoint H hH m L Np)
      (pilotRadiusFormula H hH m L Np) := by
    unfold clippingScaleFormula armWeightFormula armRadiusFormula
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg _ (add_nonneg (hr _) (hr _))
    apply add_nonneg (by norm_num)
    exact div_nonneg hB (le_trans
      (add_nonneg (pilotMidpoint_nonneg H hH m L hm Np _)
        (pilotMidpoint_nonneg H hH m L hm Np _)) (le_max_left _ _))
  have hsq := pow_le_pow_left₀ hS hscale 2
  have hs := Real.sq_sqrt (div_nonneg (mul_nonneg hB hδ) hε.le)
  have ht (u v : ℝ) : (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (u - v)]
  calc
    _ ≤ (16 * H * (Real.sqrt (totalMassVecFormula (pilotMidpoint H hH m L Np) *
        (L / m) / ε) + (L / m) / ε)) ^ 2 := hsq
    _ ≤ (16 * H) ^ 2 * (2 * ((Real.sqrt (totalMassVecFormula
        (pilotMidpoint H hH m L Np) * (L / m) / ε)) ^ 2 + ((L / m) / ε) ^ 2)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (ht _ _) (sq_nonneg _)
    _ = _ := by rw [hs]; ring


-- @node: pilotCenter_integrable_and_mean
/-- A normalized marginal Poisson pilot count is integrable and has mean q. Both properties are transported from the first raw factorial moment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hm,hq,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotCenter_integrable_and_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Ω → ℕ) (m q : ℝ) (hm : 0 < m) (hq : 0 ≤ q)
    (hlaw : HasLaw W (poissonMeasure ⟨m * q, mul_nonneg hm.le hq⟩) μ) :
    Integrable (fun ω => (W ω : ℝ) / m) μ ∧
      (∫ ω, (W ω : ℝ) / m ∂μ) = q := by
  let rate : NNReal := ⟨m * q, mul_nonneg hm.le hq⟩
  have hi : Integrable (fun N : ℕ => (N : ℝ)) (poissonMeasure rate) := by
    simpa using poisson_descFactorial_integrable rate 1
  have ht : Integrable (fun ω => (W ω : ℝ)) μ := by
    have hmap := hlaw.map_eq
    exact (hmap ▸ hi).comp_aemeasurable hlaw.aemeasurable
  refine ⟨ht.div_const m, ?_⟩
  rw [integral_div]
  have he : (∫ ω, (W ω : ℝ) ∂μ) = m * q := by
    have hx := hlaw.integral_comp
      (show AEStronglyMeasurable (fun N : ℕ => (N : ℝ)) (poissonMeasure rate) from
        (Measurable.of_discrete).aestronglyMeasurable)
    have hr := poisson_descFactorial_moment rate 1
    simp only [Nat.descFactorial_one, pow_one] at hr
    change (∫ N : ℕ, (N : ℝ) ∂poissonMeasure rate) = m * q at hr
    simpa only [Function.comp_def] using hx.trans hr
  rw [he, mul_div_cancel_left₀ _ (ne_of_gt hm)]

/-- Equation (19) for the actual pilot clipping scale. Only marginal Poisson laws are needed; null cells and arbitrarily small positive overlap are included. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hq,hH,hm,hL,hε,hε1,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotClippingScale_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hq : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hq j)⟩) μ) :
    (∫ ω, clippingScaleFormula ε (pilotMidpoint H hH m L (fun j => W j ω))
      (pilotRadiusFormula H hH m L (fun j => W j ω)) ^ 2 ∂μ) ≤
      512 * H ^ 2 * (1 + 9 * H) *
        (totalMassVecFormula q * (L / m) / ε + ((L / m) / ε) ^ 2) := by
  let δ := L / m
  have hδ : 0 ≤ δ := div_nonneg hL hm.le
  have hc (j : Fin 4) := pilotCenter_integrable_and_mean μ (W j) m (q j) hm (hq j) (hlaw j)
  let C : Ω → ℝ := fun ω => ∑ j, (W j ω : ℝ) / m
  have hC : Integrable C μ := integrable_finsetSum _ (fun j _ => (hc j).1)
  have hmean : (∫ ω, C ω ∂μ) = totalMassVecFormula q := by
    rw [totalMassVec_eq_sum_coordinates]
    dsimp [C]
    rw [integral_finsetSum _ (fun j _ => (hc j).1)]
    simp only [(hc _).2]
  have hpoint (ω : Ω) :
      clippingScaleFormula ε (pilotMidpoint H hH m L (fun j => W j ω))
        (pilotRadiusFormula H hH m L (fun j => W j ω)) ^ 2 ≤
      512 * H ^ 2 * (((1 + H) * C ω + 8 * H * δ) * δ / ε + (δ / ε) ^ 2) := by
    apply (pilotClippingScale_sq_le H hH m L ε hm hL hε hε1 _).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ hδ
    exact pilotTotalMass_le_linear_centers H hH m L hm hL _
  have hi : Integrable (fun ω => 512 * H ^ 2 *
      (((1 + H) * C ω + 8 * H * δ) * δ / ε + (δ / ε) ^ 2)) μ :=
    ((((hC.const_mul (1 + H)).add (integrable_const _)).mul_const δ).div_const ε
      |>.add (integrable_const _)).const_mul _
  calc
    _ ≤ ∫ ω, 512 * H ^ 2 *
        (((1 + H) * C ω + 8 * H * δ) * δ / ε + (δ / ε) ^ 2) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hi (ae_of_all _ hpoint)
    _ = 512 * H ^ 2 * (((1 + H) * totalMassVecFormula q + 8 * H * δ) * δ / ε +
        (δ / ε) ^ 2) := by
      rw [integral_const_mul, integral_add, integral_div, integral_mul_const,
        integral_add, integral_const_mul, hmean]
      · simp
      · exact hC.const_mul _
      · exact integrable_const _
      · exact (((hC.const_mul _).add (integrable_const _)).mul_const _).div_const _
      · exact integrable_const _
    _ ≤ _ := by
      have hp : 0 ≤ totalMassVecFormula q := by
        rw [totalMassVec_eq_sum_coordinates]
        exact Finset.sum_nonneg fun j _ => hq j
      have hs : δ * δ / ε ≤ (δ / ε) ^ 2 := by
        apply (div_le_iff₀ hε).2
        have hh : (δ / ε) ^ 2 * ε ≤ (δ / ε) ^ 2 :=
          mul_le_of_le_one_right (sq_nonneg _) hε1
        have hid : δ * δ = (δ / ε) ^ 2 * ε * ε := by field_simp
        rw [hid]
        exact mul_le_mul_of_nonneg_right hh hε.le
      rw [mul_assoc (512 * H ^ 2)]
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 512 * H ^ 2)
      have hterm : 0 ≤ totalMassVecFormula q * δ / ε := by positivity
      change _ ≤ (1 + 9 * H) * (totalMassVecFormula q * δ / ε + (δ / ε) ^ 2)
      have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 8 * H)
      have hid : ((1 + H) * totalMassVecFormula q + 8 * H * δ) * δ / ε =
          (1 + H) * (totalMassVecFormula q * δ / ε) + 8 * H * (δ * δ / ε) := by ring
      rw [hid]
      nlinarith

/-- The observed-cell form of (19), with exactly the paper's mass and overlap scales. Positivity is not required of the cell mass, so null cells are retained. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hεhalf,hlaw), the [stated conclusion](goal) holds. -/
lemma observedPilotClippingScale_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (W : Fin 4 → Ω → ℕ)
    (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure
      ⟨m * cellVector P x j, mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ) :
    (∫ ω, clippingScaleFormula ε (pilotMidpoint H hH m L (fun j => W j ω))
      (pilotRadiusFormula H hH m L (fun j => W j ω)) ^ 2 ∂μ) ≤
      512 * H ^ 2 * (1 + 9 * H) *
        (cellMass P x * L / (m * ε) + L ^ 2 / (m ^ 2 * ε ^ 2)) := by
  have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
    simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]
    ring
  have hbound := pilotClippingScale_integral_sq_le μ W (cellVector P x)
    (fun _ => ENNReal.toReal_nonneg) H hH m L ε hm hL hε (by linarith) hlaw
  rw [hmass] at hbound
  convert hbound using 1; ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
