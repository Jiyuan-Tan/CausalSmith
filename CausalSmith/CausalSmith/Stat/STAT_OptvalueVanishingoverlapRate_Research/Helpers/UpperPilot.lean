module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBias
public import Causalean.Stat.Concentration.Poisson.EmpiricalRadius

/-! # Pilot radius variance control

The pilot radius controls the normalized Poisson variance on every localized rectangle.
Midpoint-based radius bounds prove roadmap (17); keeping each anchored denominator
with its radius proves (18) and the deterministic clipping-scale envelope (22a).
The pilot midpoint deviations and the observed-cell modulus prove (22b),
retaining each inverse arm mass with its own outcome-coordinate deviations. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

/-- Truncating the lower endpoint at zero moves the midpoint above the pilot count center. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH), the [stated conclusion](goal) holds. -/
lemma pilotCenter_le_midpoint (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (Np : Fin 4 → ℕ) (j : Fin 4) :
    pilotCenterFormula m Np j ≤ pilotMidpoint H hH m L Np j := by
  have h := le_max_right 0 (pilotCenterFormula m Np j - pilotHalfWidthFormula H hH m L Np j)
  dsimp [pilotMidpoint, pilotLower, pilotUpperFormula]
  linarith


-- @node: pilotMidpoint_nonneg
/-- The midpoint coordinates are nonnegative for positive exposure and level. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm), the [stated conclusion](goal) holds. -/
lemma pilotMidpoint_nonneg (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (Np : Fin 4 → ℕ) (j : Fin 4) :
    0 ≤ pilotMidpoint H hH m L Np j := by
  exact le_trans (by dsimp [pilotCenterFormula]; positivity)
    (pilotCenter_le_midpoint H hH m L Np j)

/-- The radius never exceeds the original half width, including intervals truncated at zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH), the [stated conclusion](goal) holds. -/
lemma pilotRadius_le_halfWidth (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (Np : Fin 4 → ℕ) (j : Fin 4) :
    pilotRadiusFormula H hH m L Np j ≤ pilotHalfWidthFormula H hH m L Np j := by
  have h := le_max_right 0 (pilotCenterFormula m Np j - pilotHalfWidthFormula H hH m L Np j)
  dsimp [pilotRadiusFormula, pilotLower, pilotUpperFormula]
  linarith

/-- The coordinate radius is bounded by the square-root scale at the rectangle midpoint (17). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotRadius_le_midpoint_scale (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ) (j : Fin 4) :
    pilotRadiusFormula H hH m L Np j ≤
      H * (Real.sqrt (pilotMidpoint H hH m L Np j * L / m) + L / m) := by
  apply (pilotRadius_le_halfWidth H hH m L Np j).trans
  dsimp only [pilotHalfWidthFormula]
  apply mul_le_mul_of_nonneg_left _ hH.le
  apply add_le_add _ le_rfl
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pilotCenter_le_midpoint H hH m L Np j) hL) hm.le

/-- Summing the two coordinate radii yields the armwise square-root scale in (17). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotArmRadius_le_midpoint_scale (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ) (a : Bool) :
    armRadiusFormula (pilotRadiusFormula H hH m L Np) a ≤
      2 * H * (Real.sqrt (armMassVecFormula (pilotMidpoint H hH m L Np) a * L / m) + L / m) := by
  let b := pilotMidpoint H hH m L Np
  have hb₀ := pilotMidpoint_nonneg H hH m L hm Np (cellIdx a false)
  have hb₁ := pilotMidpoint_nonneg H hH m L hm Np (cellIdx a true)
  have h₀ := pilotRadius_le_midpoint_scale H hH m L hm hL Np (cellIdx a false)
  have h₁ := pilotRadius_le_midpoint_scale H hH m L hm hL Np (cellIdx a true)
  have hs₀ : Real.sqrt (b (cellIdx a false) * L / m) ≤
      Real.sqrt (armMassVecFormula b a * L / m) := by
    apply Real.sqrt_le_sqrt
    dsimp [armMassVecFormula]
    gcongr
    exact le_add_of_nonneg_right hb₁
  have hs₁ : Real.sqrt (b (cellIdx a true) * L / m) ≤
      Real.sqrt (armMassVecFormula b a * L / m) := by
    apply Real.sqrt_le_sqrt
    dsimp [armMassVecFormula]
    gcongr
    exact le_add_of_nonneg_left hb₀
  change _ ≤ 2 * H * (Real.sqrt (armMassVecFormula b a * L / m) + L / m)
  dsimp only [armRadiusFormula]
  have ht₀ := mul_le_mul_of_nonneg_left hs₀ hH.le
  have ht₁ := mul_le_mul_of_nonneg_left hs₁ hH.le
  change pilotRadiusFormula H hH m L Np (cellIdx a false) ≤
    H * (Real.sqrt (b (cellIdx a false) * L / m) + L / m) at h₀
  change pilotRadiusFormula H hH m L Np (cellIdx a true) ≤
    H * (Real.sqrt (b (cellIdx a true) * L / m) + L / m) at h₁
  nlinarith


-- @node: anchored_weighted_sqrt_le
/-- The anchored denominator gives the arm square-root term a single inverse-overlap scale (18). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hB,ht,hδ,hε), the [stated conclusion](goal) holds. -/
lemma anchored_weighted_sqrt_le {B t δ ε : ℝ}
    (hB : 0 ≤ B) (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    B / max t (ε * B) * Real.sqrt (t * δ) ≤ Real.sqrt (B * δ / ε) := by
  by_cases hB0 : B = 0
  · simp [hB0]
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  let D := max t (ε * B)
  have hED : ε * B ≤ D := le_max_right _ _
  have htD : t ≤ D := le_max_left _ _
  have hD : 0 < D := lt_of_lt_of_le (mul_pos hε hBp) hED
  have hprod : (ε * B) * t ≤ D ^ 2 := by
    simpa only [pow_two] using mul_le_mul hED htD ht hD.le
  have hscale := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ B * δ / ε by positivity)
  have hid : (B * δ / ε) * ((ε * B) * t) = B ^ 2 * (t * δ) := by
    field_simp
  rw [hid] at hscale
  have hs := Real.sq_sqrt (show 0 ≤ t * δ by positivity)
  have hu := Real.sq_sqrt (show 0 ≤ B * δ / ε by positivity)
  have hsq : (B * Real.sqrt (t * δ)) ^ 2 ≤
      (Real.sqrt (B * δ / ε) * D) ^ 2 := by
    rw [mul_pow, mul_pow, hs, hu]
    exact hscale
  change B / D * Real.sqrt (t * δ) ≤ _
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hD).2
  nlinarith [Real.sqrt_nonneg (t * δ), Real.sqrt_nonneg (B * δ / ε),
    mul_nonneg hB (Real.sqrt_nonneg (t * δ)),
    mul_nonneg (Real.sqrt_nonneg (B * δ / ε)) hD.le]


-- @node: anchored_weighted_radius_le
/-- Weighting an arm radius by the anchored denominator preserves its square-root scale (18). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hB,ht,hδ,hε,hC,hR), the [stated conclusion](goal) holds. -/
lemma anchored_weighted_radius_le {B t δ ε R C : ℝ}
    (hB : 0 ≤ B) (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hC : 0 ≤ C) (hR : R ≤ C * (Real.sqrt (t * δ) + δ)) :
    B / max t (ε * B) * R ≤
      C * (Real.sqrt (B * δ / ε) + δ / ε) := by
  have hD0 : 0 ≤ max t (ε * B) := le_trans ht (le_max_left _ _)
  have hw0 : 0 ≤ B / max t (ε * B) := div_nonneg hB hD0
  have hw : B / max t (ε * B) ≤ 1 / ε := by
    by_cases hB0 : B = 0
    · simp [hB0, hε.le]
    have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hD : 0 < max t (ε * B) := lt_of_lt_of_le (mul_pos hε hBp) (le_max_right _ _)
    apply (div_le_div_iff₀ hD hε).2
    simp [mul_comm]
  have hs := anchored_weighted_sqrt_le hB ht hδ hε
  have hl := mul_le_mul_of_nonneg_right hw hδ
  calc
    _ ≤ B / max t (ε * B) * (C * (Real.sqrt (t * δ) + δ)) :=
      mul_le_mul_of_nonneg_left hR hw0
    _ = C * (B / max t (ε * B) * Real.sqrt (t * δ) +
        B / max t (ε * B) * δ) := by ring
    _ ≤ C * (Real.sqrt (B * δ / ε) + δ / ε) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [one_div_mul_eq_div] using add_le_add hs hl

/-- The actual pilot arm radius and random anchored weight satisfy equation (18) jointly. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε), the [stated conclusion](goal) holds. -/
lemma pilotArmRadius_weighted_le (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hε : 0 < ε) (Np : Fin 4 → ℕ) (a : Bool) :
    let b := pilotMidpoint H hH m L Np
    totalMassVecFormula b / anchoredDenomFormula ε b a * armRadiusFormula (pilotRadiusFormula H hH m L Np) a ≤
      2 * H * (Real.sqrt (totalMassVecFormula b * (L / m) / ε) + (L / m) / ε) := by
  dsimp only
  let b := pilotMidpoint H hH m L Np
  have hb := pilotMidpoint_nonneg H hH m L hm Np
  have ht (a : Bool) : 0 ≤ armMassVecFormula b a := add_nonneg (hb _) (hb _)
  have hB : 0 ≤ totalMassVecFormula b := add_nonneg (ht false) (ht true)
  apply anchored_weighted_radius_le hB (ht a) (div_nonneg hL hm.le) hε
    (by positivity)
  simpa only [mul_div_assoc] using
    pilotArmRadius_le_midpoint_scale H hH m L hm hL Np a

/-- Each unweighted pilot arm radius is also bounded by the total-mass overlap scale. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hε1), the [stated conclusion](goal) holds. -/
lemma pilotArmRadius_le_total_scale (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Np : Fin 4 → ℕ) (a : Bool) :
    let b := pilotMidpoint H hH m L Np
    armRadiusFormula (pilotRadiusFormula H hH m L Np) a ≤
      2 * H * (Real.sqrt (totalMassVecFormula b * (L / m) / ε) + (L / m) / ε) := by
  dsimp only
  let b := pilotMidpoint H hH m L Np
  have hb := pilotMidpoint_nonneg H hH m L hm Np
  have ht (a : Bool) : 0 ≤ armMassVecFormula b a := add_nonneg (hb _) (hb _)
  have hB : 0 ≤ totalMassVecFormula b := add_nonneg (ht false) (ht true)
  have htB : armMassVecFormula b a ≤ totalMassVecFormula b := by
    cases a
    · exact le_add_of_nonneg_right (ht true)
    · exact le_add_of_nonneg_left (ht false)
  have hδ : 0 ≤ L / m := div_nonneg hL hm.le
  have hlinear : L / m ≤ (L / m) / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  have harg : armMassVecFormula b a * (L / m) ≤ totalMassVecFormula b * (L / m) / ε := by
    apply (le_div_iff₀ hε).2
    calc
      armMassVecFormula b a * (L / m) * ε ≤ armMassVecFormula b a * (L / m) :=
        mul_le_of_le_one_right (mul_nonneg (ht a) hδ) hε1
      _ ≤ totalMassVecFormula b * (L / m) := mul_le_mul_of_nonneg_right htB hδ
  apply (pilotArmRadius_le_midpoint_scale H hH m L hm hL Np a).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * H)
  simpa only [mul_div_assoc] using add_le_add (Real.sqrt_le_sqrt harg) hlinear

/-- The full clipping scale has the deterministic total-mass envelope (22a), without separating random arm denominators from their radii. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hε1), the [stated conclusion](goal) holds. -/
lemma pilotClippingScale_le_total_scale (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Np : Fin 4 → ℕ) :
    let b := pilotMidpoint H hH m L Np
    clippingScaleFormula ε b (pilotRadiusFormula H hH m L Np) ≤
      16 * H * (Real.sqrt (totalMassVecFormula b * (L / m) / ε) + (L / m) / ε) := by
  dsimp only
  have h₀ := pilotArmRadius_le_total_scale H hH m L ε hm hL hε hε1 Np false
  have h₁ := pilotArmRadius_le_total_scale H hH m L ε hm hL hε hε1 Np true
  have hw₀ := pilotArmRadius_weighted_le H hH m L ε hm hL hε Np false
  have hw₁ := pilotArmRadius_weighted_le H hH m L ε hm hL hε Np true
  dsimp only [clippingScaleFormula, armWeightFormula]
  simp only [Fintype.sum_bool]
  nlinarith

/-- The localized coordinate variance is controlled by the logarithmic pilot level, including coordinates whose pilot interval meets zero (roadmap equation (24)). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hHlarge,hm,hL,hqu), the [stated conclusion](goal) holds. -/
lemma pilotRadius_variance_bound (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H)
    (m L : ℝ) (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (j : Fin 4) (q : ℝ)
    (hqu : q ≤ pilotUpperFormula H hH m L Np j) :
    q / (m * (pilotRadiusFormula H hH m L Np j) ^ 2) ≤ 8 / L := by
  let c := pilotCenterFormula m Np j
  let h := pilotHalfWidthFormula H hH m L Np j
  let r := pilotRadiusFormula H hH m L Np j
  let level := L / m
  have hc : 0 ≤ c := by dsimp [c, pilotCenterFormula]; positivity
  have hlevel : 0 < level := div_pos hL hm
  have harg : 0 ≤ c * level := mul_nonneg hc hlevel.le
  have hs : (Real.sqrt (c * level)) ^ 2 = c * level := Real.sq_sqrt harg
  have hh : h = H * (Real.sqrt (c * level) + level) := by
    dsimp [h, pilotHalfWidthFormula, c, level]
    congr 2
    congr 1
    ring
  have hhlevel : level ≤ h := by
    rw [hh]
    nlinarith [Real.sqrt_nonneg (c * level)]
  have hhpos : 0 < h := lt_of_lt_of_le hlevel hhlevel
  have hhs : Real.sqrt (c * level) ≤ h := by
    rw [hh]
    nlinarith [Real.sqrt_nonneg (c * level)]
  have hclevel : c * level ≤ h ^ 2 := by
    nlinarith [Real.sqrt_nonneg (c * level)]
  have hr : h / 2 ≤ r := by
    dsimp [r, pilotRadiusFormula, pilotLower, pilotUpperFormula]
    change h / 2 ≤ (c + h - max 0 (c - h)) / 2
    rw [max_def]
    split_ifs <;> linarith
  have hrpos : 0 < r := lt_of_lt_of_le (by linarith) hr
  have hqu' : q ≤ c + h := hqu
  have hscale : q * level ≤ 8 * r ^ 2 := by
    have hqh : q * level ≤ (c + h) * level :=
      mul_le_mul_of_nonneg_right hqu' hlevel.le
    have hhlevel' : h * level ≤ h ^ 2 := by nlinarith
    nlinarith
  apply (div_le_div_iff₀ (mul_pos hm (sq_pos_of_pos hrpos)) hL).2
  have heq : q * L = (q * level) * m := by dsimp [level]; field_simp
  rw [heq]
  nlinarith

/-- Truncating a nonnegative pilot center at zero moves its midpoint by at most its half width, including intervals that meet the boundary. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotMidpoint_sub_center_le_halfWidth (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ) (j : Fin 4) :
    |pilotMidpoint H hH m L Np j - pilotCenterFormula m Np j| ≤
      pilotHalfWidthFormula H hH m L Np j := by
  have hc : 0 ≤ pilotCenterFormula m Np j := by dsimp [pilotCenterFormula]; positivity
  have hh : 0 ≤ pilotHalfWidthFormula H hH m L Np j := by
    dsimp [pilotHalfWidthFormula]
    positivity
  have hmid := pilotCenter_le_midpoint H hH m L Np j
  rw [abs_of_nonneg (sub_nonneg.mpr hmid)]
  dsimp [pilotMidpoint, pilotLower, pilotUpperFormula]
  rw [max_def]
  split_ifs <;> linarith

/-- Each midpoint error is bounded by the pilot-count error plus the random half width; no localization event is needed in equation (22b). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotMidpoint_abs_error_le (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ) (q : Fin 4 → ℝ) (j : Fin 4) :
    |pilotMidpoint H hH m L Np j - q j| ≤
      |pilotCenterFormula m Np j - q j| + pilotHalfWidthFormula H hH m L Np j := by
  calc
    _ = |(pilotMidpoint H hH m L Np j - pilotCenterFormula m Np j) +
        (pilotCenterFormula m Np j - q j)| := by congr 1; ring
    _ ≤ |pilotMidpoint H hH m L Np j - pilotCenterFormula m Np j| +
        |pilotCenterFormula m Np j - q j| := abs_add_le _ _
    _ ≤ _ := by
      have h := pilotMidpoint_sub_center_le_halfWidth H hH m L hm hL Np j
      linarith

/-- Summing within an arm before weighting preserves the outcome-coordinate shell bound used in equation (22b). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotArmDelta_le_coordinate_errors (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ) (q : Fin 4 → ℝ) (a : Bool) :
    armDelta (pilotMidpoint H hH m L Np) q a ≤
      ∑ y : Bool, (|pilotCenterFormula m Np (cellIdx a y) - q (cellIdx a y)| +
        pilotHalfWidthFormula H hH m L Np (cellIdx a y)) := by
  exact Finset.sum_le_sum fun y _ =>
    pilotMidpoint_abs_error_le H hH m L hm hL Np q (cellIdx a y)

/-- On an occupied observed cell, overlap makes the anchored denominator exactly the observed arm mass, as required in roadmap equations (1) and (22b). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hP,hp), the [stated conclusion](goal) holds. -/
lemma anchoredDenom_cellVector_eq_armMass {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x) (a : Bool) :
    anchoredDenomFormula ε (cellVector P x) a = armMass P a x := by
  have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
    simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]
    ring
  have harm : armMassVecFormula (cellVector P x) a = armMass P a x := by
    cases a <;> simp [armMassVecFormula, cellVector, armMass, cellIdx] <;> ring
  obtain ⟨hlo, hhi⟩ := hP.overlap x hp
  have ht : ε * cellMass P x ≤ armMass P true x :=
    (le_div_iff₀ hp).mp hlo
  have hf : ε * cellMass P x ≤ armMass P false x := by
    have hs : cellMass P x = armMass P false x + armMass P true x := by
      simp [cellMass, armMass]
      ring
    have hu : armMass P true x ≤ (1 - ε) * cellMass P x :=
      (div_le_iff₀ hp).mp hhi
    nlinarith
  rw [anchoredDenomFormula, hmass, harm]
  apply max_eq_left
  cases a <;> assumption

/-- The cell-value perturbation keeps the inverse observed arm mass attached to its armwise deviations. The constant four absorbs the unweighted modulus term. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hb), the [stated conclusion](goal) holds. -/
lemma observedCell_armwise_modulus_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d)
    (hp : 0 < cellMass P x) (b : Fin 4 → ℝ) (hb : ∀ j, 0 ≤ b j) :
    |armwiseExtensionFormula ε b - armwiseExtensionFormula ε (cellVector P x)| ≤
      4 * ∑ a : Bool, cellMass P x / armMass P a x * armDelta b (cellVector P x) a := by
  have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
    simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]
    ring
  have hq : ∀ j, 0 ≤ cellVector P x j := fun _ => ENNReal.toReal_nonneg
  have hq0 : cellVector P x ≠ 0 := by
    intro hz
    rw [hz] at hmass
    simp [totalMassVecFormula, armMassVecFormula] at hmass
    linarith
  have hmod := armwise_modulus_extension.1 ε hε b (cellVector P x) hb hq hq0
  have hweight (a : Bool) : 1 ≤ cellMass P x / armMass P a x := by
    have ha0 : 0 < armMass P a x := by
      have hden : 0 < anchoredDenomFormula ε (cellVector P x) a :=
        lt_of_lt_of_le (mul_pos hε (by simpa only [hmass] using hp)) (le_max_right _ _)
      rwa [anchoredDenom_cellVector_eq_armMass ε P hP x hp a] at hden
    apply (le_div_iff₀ ha0).2
    have hother : 0 ≤ armMass P (!a) x :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    cases a <;> simp [cellMass, armMass] at * <;> linarith
  have hsum : (∑ a : Bool, armDelta b (cellVector P x) a) ≤
      ∑ a : Bool, cellMass P x / armMass P a x * armDelta b (cellVector P x) a := by
    apply Finset.sum_le_sum
    intro a _
    have hδ : 0 ≤ armDelta b (cellVector P x) a :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hweight a) hδ
  simp only [hmass, anchoredDenom_cellVector_eq_armMass ε P hP x hp] at hmod
  linarith

/-- Equation (22b) for the actual pilot: every arm's inverse propensity remains paired with the sum of that arm's count deviations and half widths. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotCellValue_abs_error_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (H : ℝ) (hH : 0 < H) (m L : ℝ) (hm : 0 < m) (hL : 0 ≤ L)
    (Np : Fin 4 → ℕ) :
    |armwiseExtensionFormula ε (pilotMidpoint H hH m L Np) -
      armwiseExtensionFormula ε (cellVector P x)| ≤
      4 * ∑ a : Bool, cellMass P x / armMass P a x *
        ∑ y : Bool, (|pilotCenterFormula m Np (cellIdx a y) - (cellVector P x) (cellIdx a y)| +
          pilotHalfWidthFormula H hH m L Np (cellIdx a y)) := by
  apply (observedCell_armwise_modulus_le ε P hε hP x hp _
    (pilotMidpoint_nonneg H hH m L hm Np)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left
    (pilotArmDelta_le_coordinate_errors H hH m L hm hL Np (cellVector P x) a)
  exact div_nonneg hp.le (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

/-- The clipping definition bounds cell error by its width plus the center's error, even when the true cell lies outside the pilot rectangle. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hwidth), the [stated conclusion](goal) holds. -/
lemma clippedCellValue_abs_error_le_width_add (ε : ℝ) (K d : ℕ) (m : ℝ)
    (c r : Fin 4 → ℝ) (Ne : Fin 4 → ℕ) (p : ℝ)
    (hwidth : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r) :
    |clippedCellValueFormula ε K d m c r Ne - p| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r + |armwiseExtensionFormula ε c - p| := by
  have hlo : armwiseExtensionFormula ε c -
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r ≤
      clippedCellValueFormula ε K d m c r Ne := le_max_left _ _
  have hhi : clippedCellValueFormula ε K d m c r Ne ≤ armwiseExtensionFormula ε c +
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r := by
    apply max_le
    · linarith
    · exact min_le_left _ _
  have hcenter : |clippedCellValueFormula ε K d m c r Ne - armwiseExtensionFormula ε c| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε c r :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ = |(clippedCellValueFormula ε K d m c r Ne - armwiseExtensionFormula ε c) +
        (armwiseExtensionFormula ε c - p)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hcenter le_rfl)

/-- The actual clipped cell statistic obeys the bad-pilot deterministic envelope preceding (29), with the center term reduced to the coordinate shells in (22b). The nonnegative width follows from the construction, not an extra premise. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_abs_error_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (H : ℝ) (hH : 0 < H) (m L : ℝ) (hm : 0 < m) (hL : 0 ≤ L)
    (K : ℕ) (Np Ne : Fin 4 → ℕ) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    |clippedCellValueFormula ε K d m b r Ne - armwiseExtensionFormula ε (cellVector P x)| ≤
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r +
      4 * ∑ a : Bool, cellMass P x / armMass P a x *
        ∑ y : Bool, (|pilotCenterFormula m Np (cellIdx a y) - (cellVector P x) (cellIdx a y)| +
          pilotHalfWidthFormula H hH m L Np (cellIdx a y)) := by
  dsimp only
  have hb := pilotMidpoint_nonneg H hH m L hm Np
  have hr (j : Fin 4) : 0 ≤ pilotRadiusFormula H hH m L Np j := by
    have hc : 0 ≤ pilotCenterFormula m Np j := by dsimp [pilotCenterFormula]; positivity
    have hh : 0 ≤ pilotHalfWidthFormula H hH m L Np j := by
      dsimp [pilotHalfWidthFormula]
      positivity
    dsimp [pilotRadiusFormula, pilotLower, pilotUpperFormula]
    rw [max_def]
    split_ifs <;> linarith
  have ht (a : Bool) : 0 ≤ armMassVecFormula (pilotMidpoint H hH m L Np) a :=
    add_nonneg (hb _) (hb _)
  have hB : 0 ≤ totalMassVecFormula (pilotMidpoint H hH m L Np) :=
    add_nonneg (ht false) (ht true)
  have hscale : 0 ≤ clippingScaleFormula ε (pilotMidpoint H hH m L Np)
      (pilotRadiusFormula H hH m L Np) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg _ (add_nonneg (hr _) (hr _))
    exact add_nonneg (by norm_num)
      (div_nonneg hB (le_trans (ht a) (le_max_left _ _)))
  exact (clippedCellValue_abs_error_le_width_add ε K d m _ _ Ne _
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hscale)).trans
      (add_le_add le_rfl (pilotCellValue_abs_error_le ε P hε hP x hp
        H hH m L hm hL Np))

end CausalSmith.Stat.OptvalueVanishingoverlapRate
