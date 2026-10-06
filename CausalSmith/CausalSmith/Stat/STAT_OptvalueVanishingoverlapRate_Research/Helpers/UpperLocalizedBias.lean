module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilot

/-! # Inverse-arm weighted localized bias envelope

The true-mass radius and boundary estimates are combined with occupied-cell
overlap. This reduces the right side of roadmap (11) to the square-root and
linear scales preceding degree calibration in (20), without detaching an
inverse arm mass from its radius. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate


-- @node: observed_inverse_arm_bounds
/-- An occupied cell's inverse arm fraction lies between one and the inverse public overlap floor. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp), the [stated conclusion](goal) holds. -/
lemma observed_inverse_arm_bounds {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d)
    (hp : 0 < cellMass P x) (a : Bool) :
    1 ≤ cellMass P x / armMass P a x ∧
      cellMass P x / armMass P a x ≤ 1 / ε := by
  have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
    simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]
    ring
  have hfloor : ε * cellMass P x ≤ armMass P a x := by
    rw [← anchoredDenom_cellVector_eq_armMass ε P hP x hp a, ← hmass]
    exact le_max_right _ _
  have ha : 0 < armMass P a x := lt_of_lt_of_le (mul_pos hε hp) hfloor
  have hother : 0 ≤ armMass P (!a) x :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  constructor
  · apply (le_div_iff₀ ha).2
    cases a <;> simp [cellMass, armMass] at * <;> linarith
  · apply (div_le_div_iff₀ ha hε).2
    simpa only [one_mul, mul_comm] using hfloor

/-- Weighting the localized radii by their own inverse arm fractions retains one square-root inverse-overlap factor and one linear inverse-overlap factor. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hH,hHlarge,hm,hL,hloc), the [stated conclusion](goal) holds. -/
lemma observed_pilot_weightedRadius_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → ℕ)
    (hloc : cellVector P x ∈
      pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np)) :
    (∑ a : Bool, cellMass P x / armMass P a x *
      armRadiusFormula (pilotRadiusFormula H hH m L Np) a) ≤
      4 * (H * (H + 2)) *
        (Real.sqrt (cellMass P x * L / (m * ε)) + L / (m * ε)) := by
  have hq (j : Fin 4) : 0 ≤ cellVector P x j := ENNReal.toReal_nonneg
  have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
    simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]
    ring
  have ht (a : Bool) : 0 ≤ armMassVecFormula (cellVector P x) a :=
    add_nonneg (hq _) (hq _)
  have hterm (a : Bool) := anchored_weighted_radius_le
    (B := totalMassVecFormula (cellVector P x)) (t := armMassVecFormula (cellVector P x) a)
    (by rw [hmass]; exact hp.le) (ht a) (div_nonneg hL hm.le) hε
    (show 0 ≤ 2 * (H * (H + 2)) by positivity)
    (by simpa only [mul_div_assoc] using
      (pilotArmRadius_le_true_scale H hH hHlarge m L hm hL Np
        (cellVector P x) hq (fun j => (hloc j).1) a))
  have hbound (a : Bool) : cellMass P x / armMass P a x *
      armRadiusFormula (pilotRadiusFormula H hH m L Np) a ≤
      2 * (H * (H + 2)) *
        (Real.sqrt (cellMass P x * L / (m * ε)) + L / (m * ε)) := by
    have h := hterm a
    change totalMassVecFormula (cellVector P x) /
      anchoredDenomFormula ε (cellVector P x) a * _ ≤ _ at h
    rw [hmass, anchoredDenom_cellVector_eq_armMass ε P hP x hp a] at h
    simpa only [mul_div_assoc, div_div] using h
  simp only [Fintype.sum_bool]
  linarith [hbound false, hbound true]

/-- The entire occupied-cell envelope in (11), including its unweighted term, reduces to the localized scales needed in (20). This is a deterministic bound on the approximation envelope; it does not assume a polynomial error bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hH,hHlarge,hm,hL,hK,hloc), the [stated conclusion](goal) holds. -/
lemma observed_pilot_biasEnvelope_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L K : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hK : 0 < K) (Np : Fin 4 → ℕ)
    (hloc : cellVector P x ∈
      pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np)) :
    (∑ a : Bool, (1 + cellMass P x / armMass P a x) *
      ((∑ y : Bool, Real.sqrt
        (((cellVector P x) (cellIdx a y) - pilotLower H hH m L Np (cellIdx a y)) *
         (pilotUpperFormula H hH m L Np (cellIdx a y) - (cellVector P x) (cellIdx a y)))) / K +
       armRadiusFormula (pilotRadiusFormula H hH m L Np) a / K ^ 2)) ≤
      8 * (H * (H + 2)) * Real.sqrt 2 *
        Real.sqrt (cellMass P x * L / (m * ε)) / K +
      8 * (H * (H + 2)) *
        (Real.sqrt (cellMass P x * L / (m * ε)) + L / (m * ε)) / K ^ 2 := by
  let b (a : Bool) : ℝ := ∑ y : Bool, Real.sqrt
    (((cellVector P x) (cellIdx a y) - pilotLower H hH m L Np (cellIdx a y)) *
     (pilotUpperFormula H hH m L Np (cellIdx a y) - (cellVector P x) (cellIdx a y)))
  let r (a : Bool) : ℝ := armRadiusFormula (pilotRadiusFormula H hH m L Np) a
  let w (a : Bool) : ℝ := cellMass P x / armMass P a x
  have hr (a : Bool) : 0 ≤ r a := by
    have hc (j : Fin 4) : 0 ≤ pilotCenterFormula m Np j := by dsimp [pilotCenterFormula]; positivity
    have hh (j : Fin 4) : 0 ≤ pilotHalfWidthFormula H hH m L Np j := by
      dsimp [pilotHalfWidthFormula]; positivity
    have hj (j : Fin 4) : 0 ≤ pilotRadiusFormula H hH m L Np j := by
      dsimp [pilotRadiusFormula, pilotLower, pilotUpperFormula]
      rw [max_def]
      split_ifs <;> linarith [hc j, hh j]
    exact add_nonneg (hj _) (hj _)
  have hb (a : Bool) : 0 ≤ b a := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hreduce : (∑ a : Bool, (1 + w a) * (b a / K + r a / K ^ 2)) ≤
      2 * ((∑ a : Bool, w a * b a) / K + (∑ a : Bool, w a * r a) / K ^ 2) := by
    calc
      _ ≤ ∑ a : Bool, (2 * w a) * (b a / K + r a / K ^ 2) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_right _
          (add_nonneg (div_nonneg (hb a) hK.le) (div_nonneg (hr a) (sq_nonneg K)))
        have hw := (observed_inverse_arm_bounds ε P hε hP x hp a).1
        change 1 ≤ w a at hw
        linarith
      _ = _ := by simp only [Fintype.sum_bool]; ring
  have hboundary := observed_pilot_weightedBoundary_le ε P hε hP x hp
    H hH hHlarge m L hm hL Np hloc
  have hradius := observed_pilot_weightedRadius_le ε P hε hP x hp
    H hH hHlarge m L hm hL Np hloc
  apply hreduce.trans
  have hbdiv := div_le_div_of_nonneg_right hboundary hK.le
  have hrdiv := div_le_div_of_nonneg_right hradius (sq_nonneg K)
  change (∑ a : Bool, w a * b a) / K ≤ _ at hbdiv
  change (∑ a : Bool, w a * r a) / K ^ 2 ≤ _ at hrdiv
  convert mul_le_mul_of_nonneg_left (add_le_add hbdiv hrdiv)
    (show (0 : ℝ) ≤ 2 by norm_num) using 1
  ring


-- @node: logarithmic_degree_bias_scale_le
/-- A degree at least a positive multiple of the log scale converts the boundary and radius terms into the normalized bias scales in (20). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hx,hy,hL,hκ,hdegree), the [stated conclusion](goal) holds. -/
lemma logarithmic_degree_bias_scale_le {x y L K κ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hL : 1 ≤ L) (hκ : 0 < κ)
    (hdegree : κ * L ≤ K) :
    L * x / K + (L * x + L ^ 2 * y) / K ^ 2 ≤
      (1 / κ + 1 / κ ^ 2) * (x + y) := by
  have hLp : 0 < L := by linarith
  have hK : 0 < K := lt_of_lt_of_le (mul_pos hκ hLp) hdegree
  have hfirst : L * x / K ≤ x / κ := by
    apply (div_le_div_iff₀ hK hκ).2
    convert mul_le_mul_of_nonneg_right hdegree hx using 1 <;> ring
  have hsq := pow_le_pow_left₀ (mul_nonneg hκ.le hLp.le) hdegree 2
  have hsecond : (L * x + L ^ 2 * y) / K ^ 2 ≤ (x + y) / κ ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hK) (sq_pos_of_pos hκ)).2
    have hLsq : L ≤ L ^ 2 := by nlinarith
    have hnum := mul_le_mul_of_nonneg_right hLsq hx
    have hden := mul_le_mul_of_nonneg_right hsq (add_nonneg hx hy)
    have hnumκ := mul_le_mul_of_nonneg_right hnum (sq_nonneg κ)
    nlinarith
  have hxy : x / κ ≤ (x + y) / κ :=
    div_le_div_of_nonneg_right (le_add_of_nonneg_right hy) hκ.le
  calc
    _ ≤ (x + y) / κ + (x + y) / κ ^ 2 := add_le_add (hfirst.trans hxy) hsecond
    _ = _ := by ring


-- @node: localized_bias_sqrt_scale_eq
/-- The pre-calibration square-root scale is the log scale times the normalized scale; the identity also covers null cell masses. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hm,hε,hL), the [stated conclusion](goal) holds. -/
lemma localized_bias_sqrt_scale_eq {p m ε L : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hL : 0 < L) :
    Real.sqrt (p * L / (m * ε)) = L * Real.sqrt (p / (m * ε * L)) := by
  have he : p * L / (m * ε) = L ^ 2 * (p / (m * ε * L)) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]

/-- For occupied cells, the actual pilot envelope has the two bias scales in roadmap (20) once the degree is logarithmic. This bounds the envelope itself and leaves the tensor Jackson approximation step explicit upstream. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,hH,hHlarge,hm,hL,hκ,hdegree,hloc), the [stated conclusion](goal) holds. -/
lemma observed_pilot_biasEnvelope_normalized_le {d : ℕ} (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L K κ : ℝ)
    (hm : 0 < m) (hL : 1 ≤ L) (hκ : 0 < κ) (hdegree : κ * L ≤ K)
    (Np : Fin 4 → ℕ)
    (hloc : cellVector P x ∈
      pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np)) :
    (∑ a : Bool, (1 + cellMass P x / armMass P a x) *
      ((∑ y : Bool, Real.sqrt
        (((cellVector P x) (cellIdx a y) - pilotLower H hH m L Np (cellIdx a y)) *
         (pilotUpperFormula H hH m L Np (cellIdx a y) - (cellVector P x) (cellIdx a y)))) / K +
       armRadiusFormula (pilotRadiusFormula H hH m L Np) a / K ^ 2)) ≤
      8 * (H * (H + 2)) * Real.sqrt 2 * (1 / κ + 1 / κ ^ 2) *
        (Real.sqrt (cellMass P x / (m * ε * L)) + 1 / (m * ε * L)) := by
  have hLp : 0 < L := by linarith
  have hK : 0 < K := lt_of_lt_of_le (mul_pos hκ hLp) hdegree
  have he := observed_pilot_biasEnvelope_le ε P hε hP x hp
    H hH hHlarge m L K hm hLp.le hK Np hloc
  have hs := localized_bias_sqrt_scale_eq (p := cellMass P x) hm hε hLp
  have ht : L / (m * ε) = L ^ 2 * (1 / (m * ε * L)) := by
    field_simp
  have hn := logarithmic_degree_bias_scale_le
    (Real.sqrt_nonneg (cellMass P x / (m * ε * L)))
    (by positivity : 0 ≤ 1 / (m * ε * L)) hL hκ hdegree
  have htwo : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hr : 0 ≤ (Real.sqrt (cellMass P x * L / (m * ε)) + L / (m * ε)) / K ^ 2 := by
    positivity
  have hcoef : 0 ≤ 8 * (H * (H + 2)) := by positivity
  have hraise := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right htwo hr) hcoef
  apply he.trans
  calc
    _ ≤ 8 * (H * (H + 2)) * Real.sqrt 2 *
        (Real.sqrt (cellMass P x * L / (m * ε)) / K +
          (Real.sqrt (cellMass P x * L / (m * ε)) + L / (m * ε)) / K ^ 2) := by
      convert add_le_add (le_refl
        (8 * (H * (H + 2)) * Real.sqrt 2 * Real.sqrt (cellMass P x * L / (m * ε)) / K))
        hraise using 1 <;> first | rfl | ring
    _ ≤ _ := by
      rw [hs, ht]
      convert mul_le_mul_of_nonneg_left hn
        (show 0 ≤ 8 * (H * (H + 2)) * Real.sqrt 2 by positivity) using 1 <;> first | rfl | ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
