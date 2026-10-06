module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Activation

/-! Rare-cell mass and the complementary small-dimension scale in equations
(17)--(18) of the connected-interval frontier proof. -/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: rareCount_mass_le_half
lemma rareCount_mass_le_half (η : ℝ) (n d : ℕ) (q : ℝ)
    (hb : 0 < rareMass η n q) :
    (rareCount η n d q : ℝ) * rareMass η n q ≤ 1 / 2 := by
  have hcount : rareCount η n d q ≤ Nat.floor ((2 * rareMass η n q)⁻¹) :=
    min_le_right _ _
  have hfloor := Nat.floor_le (show 0 ≤ (2 * rareMass η n q)⁻¹ by positivity)
  have hle : (rareCount η n d q : ℝ) ≤ (2 * rareMass η n q)⁻¹ :=
    (Nat.cast_le.mpr hcount).trans hfloor
  have hmul := mul_le_mul_of_nonneg_right hle hb.le
  have hid : (2 * rareMass η n q)⁻¹ * rareMass η n q = 1 / 2 := by
    field_simp
  linarith [hid]

/-- Given [the specified inputs and assumptions](hyp:η,n,d,q,hd,hb,hbsmall), [the stated mathematical conclusion holds](goal). -/
-- @node: rareCount_mass_lower
lemma rareCount_mass_lower (η : ℝ) (n d : ℕ) (q : ℝ)
    (hd : 2 ≤ d) (hb : 0 < rareMass η n q) (hbsmall : rareMass η n q ≤ 1 / 4) :
    min ((d : ℝ) * rareMass η n q / 2) (1 / 4) ≤
      (rareCount η n d q : ℝ) * rareMass η n q := by
  by_cases hbranch : d - 1 ≤ Nat.floor ((2 * rareMass η n q)⁻¹)
  · rw [rareCount, min_eq_left hbranch]
    have hdim : (d : ℝ) / 2 ≤ ((d - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      push_cast
      linarith
    apply (min_le_left _ _).trans
    nlinarith
  · rw [rareCount, min_eq_right (le_of_not_ge hbranch)]
    have hf := Nat.sub_one_lt_floor ((2 * rareMass η n q)⁻¹)
    have hmul := mul_lt_mul_of_pos_right hf hb
    have hid : (2 * rareMass η n q)⁻¹ * rareMass η n q = 1 / 2 := by
      field_simp
    apply (min_le_right _ _).trans
    nlinarith

/-- Given [the specified inputs and assumptions](hyp:η,Δ,n,d,q,hη,hηsmall,hd,hN,hell,hbsmall,hseparation), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_prior_segment_width_lower
lemma interval_prior_segment_width_lower (η Δ : ℝ) (n d : ℕ) (q : ℝ)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2)
    (hd : 2 ≤ d) (hN : 0 < effectiveSize n q) (hell : 0 < logScale n q)
    (hbsmall : rareMass η n q ≤ 1 / 4)
    (hseparation : (rareCount η n d q : ℝ) * rareMass η n q / 12 ≤ Δ) :
    (η / 24) * min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) ≤ Δ := by
  have hb : 0 < rareMass η n q := by
    unfold rareMass
    positivity
  have hmass := rareCount_mass_lower η n d q hd hb hbsmall
  have hscale : (η / 24) * min 1 ((d : ℝ) /
      (effectiveSize n q * logScale n q)) ≤
      min ((d : ℝ) * rareMass η n q / 2) (1 / 4) / 12 := by
    rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 12)]
    apply le_min
    · have h := mul_le_mul_of_nonneg_left
        (min_le_right (1 : ℝ) ((d : ℝ) / (effectiveSize n q * logScale n q)))
        (show 0 ≤ η / 24 by positivity)
      convert h using 1
      dsimp [rareMass]
      ring
    · have h := mul_le_mul_of_nonneg_left
        (min_le_left (1 : ℝ) ((d : ℝ) / (effectiveSize n q * logScale n q)))
        (show 0 ≤ η / 24 by positivity)
      linarith
  exact hscale.trans ((div_le_div_of_nonneg_right hmass (by norm_num)).trans hseparation)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,D,q,hd,hcapacity,hsmall), [the stated mathematical conclusion holds](goal). -/
-- @node: rareCount_small_dimension
lemma rareCount_small_dimension (η : ℝ) (n d D : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hcapacity : (D : ℝ) ≤ (2 * rareMass η n q)⁻¹)
    (hsmall : rareCount η n d q < D) : d ≤ D := by
  have hfloor : D ≤ Nat.floor ((2 * rareMass η n q)⁻¹) := by
    exact (Nat.le_floor_iff (by
      exact (show (0 : ℝ) ≤ D by positivity).trans hcapacity)).mpr hcapacity
  have hbranch : d - 1 < D := by
    unfold rareCount at hsmall
    omega
  omega

/-- Given [the specified inputs and assumptions](hyp:n,d,D,q,hN,hell,hd), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_small_dimension_scale
lemma interval_small_dimension_scale (n d D : ℕ) (q : ℝ)
    (hN : 1 ≤ effectiveSize n q) (hell : 1 ≤ logScale n q) (hd : d ≤ D) :
    min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) ≤
      (D : ℝ) * (Real.sqrt (effectiveSize n q))⁻¹ := by
  have hNpos : 0 < effectiveSize n q := by linarith
  have hspos : 0 < Real.sqrt (effectiveSize n q) := Real.sqrt_pos.mpr hNpos
  have hs : Real.sqrt (effectiveSize n q) ≤ effectiveSize n q := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hNpos.le, ?_⟩
    nlinarith
  have hden : Real.sqrt (effectiveSize n q) ≤ effectiveSize n q * logScale n q := by
    nlinarith
  have hdim : (d : ℝ) ≤ D := by exact_mod_cast hd
  apply (min_le_right _ _).trans
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) hspos).mpr
  have hmul := mul_le_mul_of_nonneg_right hdim hspos.le
  have hmul' := mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ D by positivity)
  exact hmul.trans hmul'

end CausalSmith.Stat.MarRareqLogfrontier
