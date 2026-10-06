module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalScales
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalThresholds
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationSampleLikelihood
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationPriorTarget
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Lower.ActivationMixture

/-! The bounded-effective-size and small-rare-count cases in equations (18)--(19). -/

public section

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hN,hell), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_many_scale_sqrt
lemma interval_many_scale_sqrt (n d : ℕ) (q : ℝ)
    (hN : 0 < effectiveSize n q) (hell : 0 < logScale n q) :
    Real.sqrt (min 1 (((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2)) =
      min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) := by
  let x := (d : ℝ) / (effectiveSize n q * logScale n q)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  change Real.sqrt (min 1 (x ^ 2)) = min 1 x
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right (by nlinarith : x ^ 2 ≤ 1), Real.sqrt_sq hx,
      min_eq_right hx1]
  · rw [min_eq_left (by nlinarith : 1 ≤ x ^ 2), Real.sqrt_one,
      min_eq_left (le_of_not_ge hx1)]

/-- Given [the specified inputs and assumptions](hyp:N,T,hN,hNT), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_bounded_size_parametric_scale
lemma interval_bounded_size_parametric_scale (N T : ℝ)
    (hN : 0 < N) (hNT : N ≤ T) :
    min 1 (Real.sqrt T)⁻¹ ≤ min 1 (Real.sqrt N)⁻¹ := by
  apply min_le_min_left
  exact (inv_le_inv₀ (Real.sqrt_pos.mpr (hN.trans_le hNT))
    (Real.sqrt_pos.mpr hN)).mpr (Real.sqrt_le_sqrt hNT)

/-- Given [the specified inputs and assumptions](hyp:η,n,d,D,q,hd,hN,hell,hcapacity,hsmall), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_small_rare_count_scale
lemma interval_small_rare_count_scale (η : ℝ) (n d D : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hN : 1 ≤ effectiveSize n q) (hell : 1 ≤ logScale n q)
    (hcapacity : (D : ℝ) ≤ (2 * rareMass η n q)⁻¹)
    (hsmall : rareCount η n d q < D) :
    min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) ≤
      (D : ℝ) * min 1 (Real.sqrt (effectiveSize n q))⁻¹ := by
  have hs : 1 ≤ Real.sqrt (effectiveSize n q) := Real.one_le_sqrt.mpr hN
  have hinv : (Real.sqrt (effectiveSize n q))⁻¹ ≤ 1 := by
    simpa using (inv_le_inv₀ (by linarith : 0 < Real.sqrt (effectiveSize n q))
      (by norm_num : (0 : ℝ) < 1)).mpr hs
  rw [min_eq_right hinv]
  exact interval_small_dimension_scale n d D q hN hell
    (rareCount_small_dimension η n d D q hd hcapacity hsmall)

/-- Given [the specified inputs and assumptions](hyp:η,T,c₀,c₁,D,hT,hD,hc₀,hc₁,n,d,q,L,hd,hN,hell,hparam,hcapacity,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_many_scale_of_large_regime
lemma interval_many_scale_of_large_regime (η T c₀ c₁ : ℝ) (D : ℕ)
    (hT : 1 ≤ T) (hD : 1 ≤ D) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (n d : ℕ) (q L : ℝ) (hd : 1 ≤ d)
    (hN : 0 < effectiveSize n q) (hell : 1 ≤ logScale n q)
    (hparam : c₀ * min 1 (Real.sqrt (effectiveSize n q))⁻¹ ≤ L)
    (hcapacity : T ≤ effectiveSize n q → (D : ℝ) ≤ (2 * rareMass η n q)⁻¹)
    (hlarge : T ≤ effectiveSize n q → D ≤ rareCount η n d q →
      c₁ * min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) ≤ L) :
    min c₁ (min (c₀ * min 1 (Real.sqrt T)⁻¹) (c₀ / D)) *
      min 1 ((d : ℝ) / (effectiveSize n q * logScale n q)) ≤ L := by
  let c := min c₁ (min (c₀ * min 1 (Real.sqrt T)⁻¹) (c₀ / D))
  let b := min 1 ((d : ℝ) / (effectiveSize n q * logScale n q))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  change c * b ≤ L
  by_cases hNT : T ≤ effectiveSize n q
  · by_cases hJ : D ≤ rareCount η n d q
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hb).trans (hlarge hNT hJ)
    · have hscale := interval_small_rare_count_scale η n d D q hd
        (hT.trans hNT) hell (hcapacity hNT) (lt_of_not_ge hJ)
      have hc : c ≤ c₀ / D := (min_le_right _ _).trans (min_le_right _ _)
      have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hD)
      have hcpos : 0 ≤ c := by dsimp [c]; positivity
      have hmul := mul_le_mul_of_nonneg_left hscale hcpos
      have hcoef : c * (D : ℝ) ≤ c₀ := (le_div_iff₀ hDpos).mp hc
      have hmul' := mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ min 1 (Real.sqrt (effectiveSize n q))⁻¹ by positivity)
      have hfinish : c * ((D : ℝ) * min 1 (Real.sqrt (effectiveSize n q))⁻¹) ≤ L := by
        calc
          c * ((D : ℝ) * min 1 (Real.sqrt (effectiveSize n q))⁻¹) ≤
              c₀ * min 1 (Real.sqrt (effectiveSize n q))⁻¹ := by
            simpa [mul_assoc] using hmul'
          _ ≤ L := hparam
      exact hmul.trans hfinish
  · have hc : c ≤ c₀ * min 1 (Real.sqrt T)⁻¹ :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hcpos : 0 ≤ c := by dsimp [c]; positivity
    have hb1 : b ≤ 1 := min_le_left _ _
    have hscale := interval_bounded_size_parametric_scale
      (effectiveSize n q) T hN (le_of_not_ge hNT)
    calc
      c * b ≤ c := by nlinarith
      _ ≤ c₀ * min 1 (Real.sqrt T)⁻¹ := hc
      _ ≤ c₀ * min 1 (Real.sqrt (effectiveSize n q))⁻¹ :=
        mul_le_mul_of_nonneg_left hscale hc₀.le
      _ ≤ L := hparam

end CausalSmith.Stat.MarRareqLogfrontier
