module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotRegularity

/-! # Clipping-scale moments on failed pilot rectangles

The clipping-scale component of roadmap (22) follows from its affine square
envelope and the joint first score moment on rectangle failure. The midpoint
and failure event remain coupled throughout the argument.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped BigOperators NNReal

/-- The total midpoint mass is at most the true mass plus the aggregate deviation-and-width score, including failed pilots. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hH,hL), the [stated conclusion](goal) holds. -/
lemma pilotTotalMass_le_true_mass_add_score {Ω : Type*}
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hH : 0 < H) (L : ℝ) (hL : 0 ≤ L) (ω : Ω) :
    totalMassVecFormula (pilotMidpoint H hH m L (fun j => W j ω)) ≤
      (∑ j, (q j : ℝ)) + empiricalAggregateScore W H L m q ω := by
  have hs := pilotMidpoint_total_abs_error_le_score W q m hm H hH L hL ω
  have hd : totalMassVecFormula (pilotMidpoint H hH m L (fun j => W j ω)) -
      ∑ j, (q j : ℝ) ≤ ∑ j, |pilotMidpoint H hH m L (fun i => W i ω) j - q j| := by
    rw [totalMassVec_eq_sum_coordinates, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun j _ => le_abs_self _
  linarith

open Classical in
/-- The bad-pilot second moment of the clipping scale has an exponential factor multiplying only mass-normalized deviations. The probability term and joint score term are both derived from the independent Poisson laws. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hε,hε1,hW,hlaw,hind), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_clippingScale_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L ε : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (hind : iIndepFun W μ) :
    (∫ ω, if (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      clippingScaleFormula ε (pilotMidpoint H hHpos m L (fun j => W j ω))
        (pilotRadiusFormula H hHpos m L (fun j => W j ω)) ^ 2 else 0 ∂μ) ≤
      512 * H ^ 2 *
        (((∑ j, (q j : ℝ)) * (L / m) / ε + ((L / m) / ε) ^ 2) *
            (8 * Real.exp (-40 * L)) +
          ((L / m) / ε) * ((H / universalH) * productMomentConstant 4 1 *
            Real.exp (-20 * L) *
            (Real.sqrt ((∑ j, (q j : ℝ)) * L / m) + L / m))) := by
  classical
  let B : Set Ω := {ω | (fun j => (q j : ℝ)) ∉ pilotRectangle
    (pilotLower H hHpos m L (fun j => W j ω))
    (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  let Q : ℝ := ∑ j, (q j : ℝ)
  let δ : ℝ := L / m
  let E := empiricalAggregateScore W H L m q
  let a : ℝ := Q * δ / ε + (δ / ε) ^ 2
  have hδ : 0 ≤ δ := div_nonneg (by linarith) m.coe_nonneg
  have ha : 0 ≤ a := by dsimp [a, Q]; positivity
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hiE : Integrable E μ := by
    simpa only [pow_one] using
      pilotAggregateScore_pow_integrable μ W q m hm H L hH hL hW hlaw 1 (Or.inl rfl)
  have hprob : μ.real B ≤ 8 * Real.exp (-40 * L) := by
    have hp := pilotRectangle_bad_probability_le μ W q m hm H hHpos L hH hL hlaw
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hp).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hscore : (∫ ω, B.indicator E ω ∂μ) ≤
      (H / universalH) * productMomentConstant 4 1 * Real.exp (-20 * L) *
        (Real.sqrt (Q * L / m) + L / m) := by
    have hs := pilotRectangle_bad_aggregate_moment_le μ W q m hm H hHpos L hH hL
      hW hlaw hind 1 (Or.inl rfl)
    simpa only [Set.indicator, B, E, empiricalAggregateScore, normalizedDeviation,
      pilotCenterFormula, pilotHalfWidth_eq_empiricalRadius, pow_one, Q, Set.mem_setOf_eq] using hs
  have hi : Integrable (fun ω => 512 * H ^ 2 *
      (B.indicator (fun _ => a) ω + (δ / ε) * B.indicator E ω)) μ :=
    (((integrable_const a).indicator hB).add
      ((hiE.indicator hB).const_mul (δ / ε))).const_mul _
  have hpoint (ω : Ω) :
      (if ω ∈ B then clippingScaleFormula ε
        (pilotMidpoint H hHpos m L (fun j => W j ω))
        (pilotRadiusFormula H hHpos m L (fun j => W j ω)) ^ 2 else 0) ≤
      512 * H ^ 2 * (B.indicator (fun _ => a) ω + (δ / ε) * B.indicator E ω) := by
    by_cases hb : ω ∈ B
    · rw [if_pos hb, Set.indicator_of_mem hb, Set.indicator_of_mem hb]
      have hs := pilotClippingScale_sq_le H hHpos m L ε (NNReal.coe_pos.mpr hm)
        (by linarith) hε hε1 (fun j => W j ω)
      apply hs.trans
      have ht := pilotTotalMass_le_true_mass_add_score W q m hm H hHpos L (by linarith) ω
      have hm := mul_le_mul_of_nonneg_right ht (div_nonneg hδ hε.le)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 512 * H ^ 2)
      dsimp [a, δ, Q, E] at *
      convert add_le_add_right hm ((L / m / ε) ^ 2) using 1 <;> ring
    · simp [hb, Set.indicator_of_notMem hb]
  calc
    _ ≤ ∫ ω, 512 * H ^ 2 *
        (B.indicator (fun _ => a) ω + (δ / ε) * B.indicator E ω) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => by
        change 0 ≤ if ω ∈ B then _ else 0
        split_ifs <;> positivity) hi (ae_of_all _ hpoint)
    _ = 512 * H ^ 2 * (a * μ.real B + (δ / ε) * ∫ ω, B.indicator E ω ∂μ) := by
      rw [integral_const_mul, integral_add ((integrable_const a).indicator hB)
        ((hiE.indicator hB).const_mul _), integral_indicator_const a hB, integral_const_mul]
      simp only [smul_eq_mul, mul_comm a]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 512 * H ^ 2)
      exact add_le_add (mul_le_mul_of_nonneg_left hprob ha)
        (mul_le_mul_of_nonneg_left hscore (div_nonneg hδ hε.le))

open Classical in
/-- The clipping-scale component of (22) has the same mass and overlap scales as (19), with an exponentially small multiplier. In particular the mass term has only one inverse-overlap power even on failed pilot rectangles. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hε,hε1,hW,hlaw,hind), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_clippingScale_normalized_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L ε : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (hind : iIndepFun W μ) :
    (∫ ω, if (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      clippingScaleFormula ε (pilotMidpoint H hHpos m L (fun j => W j ω))
        (pilotRadiusFormula H hHpos m L (fun j => W j ω)) ^ 2 else 0 ∂μ) ≤
      512 * H ^ 2 * (8 + 2 * (H / universalH) * productMomentConstant 4 1) *
        Real.exp (-20 * L) *
        ((∑ j, (q j : ℝ)) * L / (m * ε) + L ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2)) := by
  have hb := pilotRectangle_bad_clippingScale_integral_sq_le μ W q m hm H hHpos L ε
    hH hL hε hε1 hW hlaw hind
  let Q : ℝ := ∑ j, (q j : ℝ)
  let δ : ℝ := L / m
  let a : ℝ := Q * δ / ε + (δ / ε) ^ 2
  let C : ℝ := (H / universalH) * productMomentConstant 4 1
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun j _ => (q j).coe_nonneg
  have hδ : 0 ≤ δ := div_nonneg (by linarith) m.coe_nonneg
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hC : 0 ≤ C := mul_nonneg (div_nonneg hHpos.le universalH_pos.le)
    (productMomentConstant_pos 4 1).le
  have hsqrt : Real.sqrt (Q * δ) ≤ Q + δ := by
    nlinarith [Real.sq_sqrt (mul_nonneg hQ hδ), Real.sqrt_nonneg (Q * δ),
      sq_nonneg (Q - δ)]
  have hδsq : δ * δ / ε ≤ (δ / ε) ^ 2 := by
    apply (div_le_iff₀ hε).2
    have h := mul_le_of_le_one_right (sq_nonneg (δ / ε)) hε1
    have he : δ * δ = (δ / ε) ^ 2 * ε * ε := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right h hε.le
  have hscale : (δ / ε) * (Real.sqrt (Q * δ) + δ) ≤ 2 * a := by
    have h := mul_le_mul_of_nonneg_left hsqrt (div_nonneg hδ hε.le)
    dsimp [a]
    have he : δ / ε * (Q + δ) = Q * δ / ε + δ * δ / ε := by ring
    rw [he] at h
    have he' : δ / ε * (Real.sqrt (Q * δ) + δ) =
        δ / ε * Real.sqrt (Q * δ) + δ * δ / ε := by ring
    rw [he']
    nlinarith [div_nonneg (mul_nonneg hQ hδ) hε.le]
  have hexp : Real.exp (-40 * L) ≤ Real.exp (-20 * L) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h1 := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 8 * a by positivity)
  have h2 := mul_le_mul_of_nonneg_left hscale
    (mul_nonneg hC (Real.exp_nonneg (-20 * L)))
  apply hb.trans
  have he : (∑ j, (q j : ℝ)) * L / (m * ε) + L ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2) = a := by
    dsimp [a, Q, δ]
    ring
  rw [he]
  apply (show _ ≤ 512 * H ^ 2 * ((8 + 2 * C) * Real.exp (-20 * L) * a) from ?_).trans_eq
    (by dsimp [C]; ring)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 512 * H ^ 2)
  change a * (8 * Real.exp (-40 * L)) +
    (δ / ε) * (C * Real.exp (-20 * L) * (Real.sqrt (Q * L / m) + δ)) ≤ _
  have heq : Q * L / m = Q * δ := by dsimp [δ]; ring
  rw [heq]
  nlinarith

open Classical in
/-- Cauchy–Schwarz couples the failed-rectangle probability to its clipping-scale second moment, giving the first-moment component of roadmap (22). The mass term retains a square root of one inverse-overlap power. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hε,hε1,hW,hlaw,hind), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_clippingScale_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L ε : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (hind : iIndepFun W μ) :
    (∫ ω, if (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      clippingScaleFormula ε (pilotMidpoint H hHpos m L (fun j => W j ω))
        (pilotRadiusFormula H hHpos m L (fun j => W j ω)) else 0 ∂μ) ≤
      Real.sqrt (8 * (512 * H ^ 2 *
        (8 + 2 * (H / universalH) * productMomentConstant 4 1))) *
        Real.exp (-30 * L) *
        (Real.sqrt ((∑ j, (q j : ℝ)) * L / (m * ε)) + L / (m * ε)) := by
  classical
  let B : Set Ω := {ω | (fun j => (q j : ℝ)) ∉ pilotRectangle
    (pilotLower H hHpos m L (fun j => W j ω))
    (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  let S : Ω → ℝ := fun ω => clippingScaleFormula ε
    (pilotMidpoint H hHpos m L (fun j => W j ω))
    (pilotRadiusFormula H hHpos m L (fun j => W j ω))
  let C : ℝ := 512 * H ^ 2 *
    (8 + 2 * (H / universalH) * productMomentConstant 4 1)
  let a : ℝ := (∑ j, (q j : ℝ)) * L / (m * ε)
  let b : ℝ := L / (m * ε)
  let s : ℝ := Real.sqrt a + b
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hS := pilotClippingScale_memLp_two μ W q m hm H hHpos L ε hH hL hε hε1 hW hlaw
  have hSn (ω : Ω) : 0 ≤ S ω := clippingScale_nonneg ε _ _
    (pilotMidpoint_nonneg H hHpos m L (NNReal.coe_pos.mpr hm) _)
    (fun j => (pilotRadius_pos H hHpos m L (NNReal.coe_pos.mpr hm) (by linarith) _ j).le)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hs : 0 ≤ s := add_nonneg (Real.sqrt_nonneg _) hb
  have hC : 0 ≤ C := by
    dsimp [C]
    have := (productMomentConstant_pos 4 1).le
    have := universalH_pos
    positivity
  have hprob : μ.real B ≤ 8 * Real.exp (-40 * L) := by
    have hp := pilotRectangle_bad_probability_le μ W q m hm H hHpos L hH hL hlaw
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hp).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hsecond : (∫ ω, B.indicator (fun ω => S ω ^ 2) ω ∂μ) ≤
      C * Real.exp (-20 * L) * s ^ 2 := by
    have h := pilotRectangle_bad_clippingScale_normalized_le μ W q m hm H hHpos L ε
      hH hL hε hε1 hW hlaw hind
    have hab : a + b ^ 2 ≤ s ^ 2 := by
      dsimp [s]
      nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
    have he : L ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2) = b ^ 2 := by dsimp [b]; ring
    simp only [he] at h
    simpa only [Set.indicator, B, S, Set.mem_ofPred_eq] using
      h.trans (mul_le_mul_of_nonneg_left hab (mul_nonneg hC (Real.exp_nonneg _)))
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := B.indicator S) (g := B.indicator (fun _ => (1 : ℝ)))
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun ω _ => hSn ω) ω)
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (by simpa using hS.indicator hB)
    (by simpa using (memLp_const (1 : ℝ) (p := (2 : ENNReal)) (μ := μ)).indicator hB)
  have hmul (ω : Ω) : B.indicator S ω * B.indicator (fun _ => (1 : ℝ)) ω =
      B.indicator S ω := by by_cases h : ω ∈ B <;> simp [h]
  have hsq (ω : Ω) : (B.indicator S ω) ^ (2 : ℝ) =
      B.indicator (fun ω => S ω ^ 2) ω := by
    by_cases h : ω ∈ B <;> simp [h]
  have hone (ω : Ω) : (B.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ) =
      B.indicator (fun _ => (1 : ℝ)) ω := by by_cases h : ω ∈ B <;> simp [h]
  simp_rw [hmul, hsq, hone, ← Real.sqrt_eq_rpow] at hholder
  rw [integral_indicator_const _ hB] at hholder
  simp only [smul_eq_mul, mul_one] at hholder
  have hbound := mul_le_mul (Real.sqrt_le_sqrt hsecond) (Real.sqrt_le_sqrt hprob)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have heq : Real.sqrt (C * Real.exp (-20 * L) * s ^ 2) *
      Real.sqrt (8 * Real.exp (-40 * L)) =
      Real.sqrt (8 * C) * Real.exp (-30 * L) * s := by
    rw [← Real.sqrt_mul (by positivity)]
    have hexp : Real.exp (-20 * L) * Real.exp (-40 * L) =
        Real.exp (-30 * L) ^ 2 := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have he : C * Real.exp (-20 * L) * s ^ 2 * (8 * Real.exp (-40 * L)) =
        (Real.sqrt (8 * C) * Real.exp (-30 * L) * s) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      rw [← hexp]
      ring
    rw [he, Real.sqrt_sq (by positivity)]
  simpa only [Set.indicator, B, S, C, s, a, b, Set.mem_ofPred_eq] using
    (hholder.trans hbound).trans_eq heq

end CausalSmith.Stat.OptvalueVanishingoverlapRate
