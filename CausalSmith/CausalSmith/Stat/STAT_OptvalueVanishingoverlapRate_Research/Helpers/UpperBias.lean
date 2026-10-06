module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPoissonization
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary

/-! # Localized pilot geometry for Jackson bias

On the localization event, the empirical half width is controlled by the true
coordinate's square-root scale. The boundary-distance factor loses its additive
level term, including at zero coordinates. These are the deterministic pilot
inputs to roadmap equations (11) and (20). -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate


-- @node: localized_pilot_sqrt_le
/-- Solving the localization inequality replaces the empirical square-root scale by the true coordinate scale plus a level-sized remainder. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hc,hq,hδ,hH,hloc), the [stated conclusion](goal) holds. -/
lemma localized_pilot_sqrt_le {c q δ H : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hδ : 0 ≤ δ) (hH : 0 ≤ H)
    (hloc : c - H * (Real.sqrt (c * δ) + δ) ≤ q) :
    Real.sqrt (c * δ) ≤ Real.sqrt (q * δ) + (H + 1) * δ := by
  have hs := Real.sq_sqrt (mul_nonneg hc hδ)
  have ht := Real.sq_sqrt (mul_nonneg hq hδ)
  have hlocδ := mul_le_mul_of_nonneg_right hloc hδ
  by_contra h
  have hgap : 0 < Real.sqrt (c * δ) - Real.sqrt (q * δ) - (H + 1) * δ := by
    linarith
  have hsum : 0 < Real.sqrt (c * δ) + Real.sqrt (q * δ) + δ := by
    have := Real.sqrt_nonneg (q * δ)
    nlinarith
  have hprod := mul_pos hgap hsum
  have hcross : 0 ≤ (H + 2) * Real.sqrt (q * δ) * δ := by positivity
  nlinarith [sq_nonneg δ]


-- @node: localized_pilot_halfWidth_le
/-- The localized half width has a true-mass envelope with a constant depending only on the universal pilot multiplier. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hc,hq,hδ,hH,hloc), the [stated conclusion](goal) holds. -/
lemma localized_pilot_halfWidth_le {c q δ H : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hδ : 0 ≤ δ) (hH : 1 ≤ H)
    (hloc : c - H * (Real.sqrt (c * δ) + δ) ≤ q) :
    H * (Real.sqrt (c * δ) + δ) ≤
      H * (H + 2) * (Real.sqrt (q * δ) + δ) := by
  have hs := localized_pilot_sqrt_le hc hq hδ (by linarith) hloc
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ H by linarith)
  have hcross : 0 ≤ H * (H + 1) * Real.sqrt (q * δ) := by positivity
  nlinarith


-- @node: localized_interval_boundary_le
/-- For a localized nonnegative interval, its boundary-distance product is controlled by true mass times level, with no level-squared remainder. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hq,hh,hδ,hB,hlo,hhi,hwidth), the [stated conclusion](goal) holds. -/
lemma localized_interval_boundary_le {c q h δ B : ℝ}
    (hq : 0 ≤ q) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hB : 1 ≤ B)
    (hlo : max 0 (c - h) ≤ q) (hhi : q ≤ c + h)
    (hwidth : h ≤ B * (Real.sqrt (q * δ) + δ)) :
    Real.sqrt ((q - max 0 (c - h)) * (c + h - q)) ≤
      2 * B * Real.sqrt (q * δ) := by
  have hleft : 0 ≤ q - max 0 (c - h) := sub_nonneg.mpr hlo
  have hright : 0 ≤ c + h - q := sub_nonneg.mpr hhi
  have hleftq : q - max 0 (c - h) ≤ q := by linarith [le_max_left 0 (c - h)]
  have hright2 : c + h - q ≤ 2 * h := by linarith [le_max_right 0 (c - h)]
  have hboundary : (q - max 0 (c - h)) * (c + h - q) ≤
      (2 * B * Real.sqrt (q * δ)) ^ 2 := by
    by_cases hsmall : q ≤ δ
    · have hs : Real.sqrt (q * δ) ≤ δ := by
        nlinarith [Real.sq_sqrt (mul_nonneg hq hδ), Real.sqrt_nonneg (q * δ),
          mul_le_mul_of_nonneg_right hsmall hδ]
      have hw : h ≤ 2 * B * δ := by nlinarith
      have hprod := mul_le_mul hleftq (hright2.trans (by nlinarith : 2 * h ≤ 4 * B * δ))
        hright hq
      have hBs : B ≤ B ^ 2 := by nlinarith
      have hb := mul_le_mul_of_nonneg_right hBs (mul_nonneg hq hδ)
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hq hδ)]
      nlinarith
    · have hs : δ ≤ Real.sqrt (q * δ) := by
        nlinarith [Real.sq_sqrt (mul_nonneg hq hδ), Real.sqrt_nonneg (q * δ),
          mul_le_mul_of_nonneg_right (le_of_not_ge hsmall) hδ]
      have hw : h ≤ 2 * B * Real.sqrt (q * δ) := by nlinarith
      have hprod : (q - max 0 (c - h)) * (c + h - q) ≤ h ^ 2 := by
        have hl := le_max_right 0 (c - h)
        nlinarith [sq_nonneg (q - c)]
      exact hprod.trans (pow_le_pow_left₀ hh hw 2)
  have hs := Real.sq_sqrt (mul_nonneg hleft hright)
  have ht : 0 ≤ 2 * B * Real.sqrt (q * δ) := by positivity
  nlinarith [Real.sqrt_nonneg ((q - max 0 (c - h)) * (c + h - q))]

/-- On the actual pilot interval, the coordinate half width obeys the true-mass envelope used before equation (20). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hHlarge,hm,hL,hq,hlo), the [stated conclusion](goal) holds. -/
lemma pilotHalfWidth_le_true_scale (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H)
    (m L : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ)
    (j : Fin 4) (q : ℝ) (hq : 0 ≤ q)
    (hlo : pilotLower H hH m L Np j ≤ q) :
    pilotHalfWidthFormula H hH m L Np j ≤
      H * (H + 2) * (Real.sqrt (q * L / m) + L / m) := by
  have hc : 0 ≤ pilotCenterFormula m Np j := by dsimp [pilotCenterFormula]; positivity
  have hloc := (le_max_right 0
    (pilotCenterFormula m Np j - pilotHalfWidthFormula H hH m L Np j)).trans hlo
  simp only [pilotHalfWidthFormula, mul_div_assoc] at hloc ⊢
  simpa only [pilotHalfWidthFormula, mul_div_assoc] using
    localized_pilot_halfWidth_le hc hq (div_nonneg hL hm.le) hHlarge hloc

/-- The actual pilot face-distance factor retains the true coordinate's square-root scale, and vanishes at a zero coordinate. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hHlarge,hm,hL,hq,hloc), the [stated conclusion](goal) holds. -/
lemma pilotBoundary_le_true_scale (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H)
    (m L : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ)
    (j : Fin 4) (q : ℝ) (hq : 0 ≤ q)
    (hloc : q ∈ Set.Icc (pilotLower H hH m L Np j) (pilotUpperFormula H hH m L Np j)) :
    Real.sqrt ((q - pilotLower H hH m L Np j) *
      (pilotUpperFormula H hH m L Np j - q)) ≤
      2 * (H * (H + 2)) * Real.sqrt (q * L / m) := by
  have hh : 0 ≤ pilotHalfWidthFormula H hH m L Np j := by dsimp [pilotHalfWidthFormula]; positivity
  have hB : 1 ≤ H * (H + 2) := by nlinarith
  have hw := pilotHalfWidth_le_true_scale H hH hHlarge m L hm hL Np j q hq hloc.1
  simp only [mul_div_assoc] at hw ⊢
  simpa only [pilotLower, pilotUpperFormula, mul_div_assoc] using localized_interval_boundary_le
    hq hh (div_nonneg hL hm.le) hB hloc.1 hloc.2 hw

/-- The coordinate radius is bounded by the same true-mass scale as its half width whenever the true coordinate lies above the pilot lower endpoint. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hHlarge,hm,hL,hq,hlo), the [stated conclusion](goal) holds. -/
lemma pilotRadius_le_true_scale (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H)
    (m L : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ)
    (j : Fin 4) (q : ℝ) (hq : 0 ≤ q)
    (hlo : pilotLower H hH m L Np j ≤ q) :
    pilotRadiusFormula H hH m L Np j ≤
      H * (H + 2) * (Real.sqrt (q * L / m) + L / m) := by
  have hr : pilotRadiusFormula H hH m L Np j ≤ pilotHalfWidthFormula H hH m L Np j := by
    have h := le_max_right 0 (pilotCenterFormula m Np j - pilotHalfWidthFormula H hH m L Np j)
    dsimp [pilotRadiusFormula, pilotUpperFormula, pilotLower]
    linarith
  exact hr.trans (pilotHalfWidth_le_true_scale H hH hHlarge m L hm hL Np j q hq hlo)

/-- On a localized rectangle, summing the coordinate radius bounds gives the true arm-mass scale used in equation (20). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hHlarge,hm,hL,hq,hlo), the [stated conclusion](goal) holds. -/
lemma pilotArmRadius_le_true_scale (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H)
    (m L : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ)
    (q : Fin 4 → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hlo : ∀ j, pilotLower H hH m L Np j ≤ q j) (a : Bool) :
    armRadiusFormula (pilotRadiusFormula H hH m L Np) a ≤
      2 * (H * (H + 2)) * (Real.sqrt (armMassVecFormula q a * L / m) + L / m) := by
  have h₀ := pilotRadius_le_true_scale H hH hHlarge m L hm hL Np
    (cellIdx a false) _ (hq _) (hlo _)
  have h₁ := pilotRadius_le_true_scale H hH hHlarge m L hm hL Np
    (cellIdx a true) _ (hq _) (hlo _)
  have hs₀ : Real.sqrt (q (cellIdx a false) * L / m) ≤
      Real.sqrt (armMassVecFormula q a * L / m) := by
    apply Real.sqrt_le_sqrt
    dsimp [armMassVecFormula]
    gcongr
    exact le_add_of_nonneg_right (hq _)
  have hs₁ : Real.sqrt (q (cellIdx a true) * L / m) ≤
      Real.sqrt (armMassVecFormula q a * L / m) := by
    apply Real.sqrt_le_sqrt
    dsimp [armMassVecFormula]
    gcongr
    exact le_add_of_nonneg_left (hq _)
  have ht₀ := mul_le_mul_of_nonneg_left hs₀ (show 0 ≤ H * (H + 2) by positivity)
  have ht₁ := mul_le_mul_of_nonneg_left hs₁ (show 0 ≤ H * (H + 2) by positivity)
  dsimp only [armRadiusFormula]
  linarith

/-- The arm's two boundary-distance factors have no additive level remainder, including arms with zero true mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hHlarge,hm,hL,hq,hloc), the [stated conclusion](goal) holds. -/
lemma pilotArmBoundary_le_true_scale (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H)
    (m L : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ)
    (q : Fin 4 → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hloc : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (a : Bool) :
    (∑ y : Bool, Real.sqrt ((q (cellIdx a y) - pilotLower H hH m L Np (cellIdx a y)) *
      (pilotUpperFormula H hH m L Np (cellIdx a y) - q (cellIdx a y)))) ≤
      4 * (H * (H + 2)) * Real.sqrt (armMassVecFormula q a * L / m) := by
  have hterm (y : Bool) := pilotBoundary_le_true_scale H hH hHlarge m L hm hL Np
    (cellIdx a y) _ (hq _) (hloc _)
  have hs (y : Bool) : Real.sqrt (q (cellIdx a y) * L / m) ≤
      Real.sqrt (armMassVecFormula q a * L / m) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hm.le
    apply mul_le_mul_of_nonneg_right _ hL
    cases y
    · exact le_add_of_nonneg_right (hq _)
    · exact le_add_of_nonneg_left (hq _)
  have hmul (y : Bool) := mul_le_mul_of_nonneg_left (hs y)
    (show 0 ≤ 2 * (H * (H + 2)) by positivity)
  simp only [Fintype.sum_bool]
  linarith [hterm false, hterm true, hmul false, hmul true]

/-- The localized boundary factors keep the inverse arm masses attached to their coordinates. Applying the observed armwise square-root bound (21) produces one square-root inverse-overlap factor, as needed for (20). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hH,hHlarge,hm,hL,hloc), the [stated conclusion](goal) holds. -/
lemma observed_pilot_weightedBoundary_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ)
    (hloc : cellVector P x ∈
      pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np)) :
    (∑ a : Bool, cellMass P x / armMass P a x * ∑ y : Bool,
      Real.sqrt (((cellVector P x) (cellIdx a y) - pilotLower H hH m L Np (cellIdx a y)) *
        (pilotUpperFormula H hH m L Np (cellIdx a y) - (cellVector P x) (cellIdx a y)))) ≤
      4 * (H * (H + 2)) * Real.sqrt 2 * Real.sqrt (cellMass P x * L / (m * ε)) := by
  have hq (j : Fin 4) : 0 ≤ (cellVector P x) j := ENNReal.toReal_nonneg
  have hscale : 0 ≤ 2 * (H * (H + 2)) * Real.sqrt (L / m) := by positivity
  have hs := observed_armwise_sqrt_bound d ε P hε hP x hp
  calc
    _ ≤ ∑ a : Bool, cellMass P x / armMass P a x * ∑ y : Bool,
        (2 * (H * (H + 2)) * Real.sqrt (L / m)) * Real.sqrt (jointMass P x a y) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hp.le
        (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg))
      apply Finset.sum_le_sum
      intro y _
      have ht := pilotBoundary_le_true_scale H hH hHlarge m L hm hL Np
        (cellIdx a y) _ (hq _) (hloc _)
      rw [mul_div_assoc, Real.sqrt_mul (hq _)] at ht
      have heq : (cellVector P x) (cellIdx a y) = jointMass P x a y := by
        cases a <;> cases y <;> simp [cellVector, cellIdx]
      simpa only [heq, mul_assoc, mul_comm, mul_left_comm] using ht
    _ = (2 * (H * (H + 2)) * Real.sqrt (L / m)) *
        (∑ a : Bool, cellMass P x / armMass P a x * ∑ y : Bool,
          Real.sqrt (jointMass P x a y)) := by
      simp only [Fintype.sum_bool]
      ring
    _ ≤ (2 * (H * (H + 2)) * Real.sqrt (L / m)) *
        (2 * Real.sqrt 2 * Real.sqrt (cellMass P x / ε)) :=
      mul_le_mul_of_nonneg_left hs hscale
    _ = _ := by
      have he : cellMass P x * L / (m * ε) = (L / m) * (cellMass P x / ε) := by ring
      rw [he, Real.sqrt_mul (div_nonneg hL hm.le)]
      ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
