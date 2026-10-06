module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Calibration

/-! # Quantitative separation of the fair comparator effect

The explicit comparator logarithms give a quadratic effect gap, uniformly through
zero effect and zero amplitude, on the paper's fixed amplitude neighbourhood.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Reciprocal bounds for the two logarithms in the fair effect gap.](goal) Under [the stated assumptions](hyp:x,hx,hx',hy,hy'). -/
-- @node: fair_log_gap_bounds
lemma fair_log_gap_bounds (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/100)
    (hy : 0 ≤ y) (hy' : y ≤ 1/100) :
    x + (100/101)*y ≤ -Real.log (1-x) + Real.log (1+y) ∧
    -Real.log (1-x) + Real.log (1+y) ≤ (100/99)*x + y := by
  have hxp : 0 < 1-x := by linarith
  have hyp : 0 < 1+y := by linarith
  have hxl := Real.log_le_sub_one_of_pos hxp
  have hxu := Real.one_sub_inv_le_log_of_pos hxp
  have hyl := Real.one_sub_inv_le_log_of_pos hyp
  have hyu := Real.log_le_sub_one_of_pos hyp
  have hxi : 1 - (1-x)⁻¹ = -x/(1-x) := by field_simp; ring
  have hyi : 1 - (1+y)⁻¹ = y/(1+y) := by field_simp; ring
  rw [hxi, neg_div] at hxu
  rw [hyi] at hyl
  have hxq : x/(1-x) ≤ (100/99)*x := by
    apply (div_le_iff₀ hxp).mpr
    nlinarith
  have hyq : (100/101)*y ≤ y/(1+y) := by
    apply (le_div_iff₀ hyp).mpr
    nlinarith
  constructor <;> linarith

/-- [The exponential increment has the bounds used by the fair calibration roadmap. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:ht). -/
-- @node: fair_exp_increment_bounds
lemma fair_exp_increment_bounds (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) :
    t ≤ Real.exp t - 1 ∧ Real.exp t - 1 ≤ (4/3)*t := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hl := Real.add_one_le_exp t
  have hu := Real.exp_bound_div_one_sub_of_interval ht.1 (by linarith : t < 1)
  have hden : 0 < 1-t := by linarith
  have hu' := (le_div_iff₀ hden).mp hu
  constructor
  · linarith
  · nlinarith [mul_nonneg (show 0 ≤ Real.exp t - 1 by linarith)
      (show 0 ≤ 1/4-t by linarith)]

/-- The explicit fair comparator loses between three and six times the quadratic amplitude. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:ht,hδ) hold, and [the stated conclusion follows](goal). -/
-- @node: comparatorEffect_gap_bounds
lemma comparatorEffect_gap_bounds (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100) :
    3*t*δ^2 ≤ t-comparatorEffect t δ ∧
    t-comparatorEffect t δ ≤ 6*t*δ^2 := by
  let d := Real.exp t - 1
  let B := 1 + d*(2/5)
  let a := d*δ^2/B
  obtain ⟨hdlo, hdhi⟩ := fair_exp_increment_bounds t ht
  change t ≤ d at hdlo
  change d ≤ (4/3)*t at hdhi
  have hd0 : 0 ≤ d := ht.1.trans hdlo
  have hd1 : d ≤ 1/3 := by linarith [ht.2]
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBp : 0 < B := by linarith
  have hBhi : B ≤ 4/3 := by dsimp [B]; linarith
  have hδsq : δ^2 ≤ 1/10000 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hδ
    nlinarith [sq_nonneg (δ-1/100), sq_nonneg (δ+1/100)]
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have haeq : a*B = d*δ^2 := by dsimp [a]; field_simp
  have had : a ≤ d*δ^2 := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hB)]
  have haSmall : a ≤ 1/1000 := by nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hδsq)]
  have haLower : (3/4)*(t*δ^2) ≤ a := by
    have h1 := mul_le_mul_of_nonneg_right hdlo (sq_nonneg δ)
    have h2 := mul_le_mul_of_nonneg_left hBhi ha0
    nlinarith
  have haUpper : a ≤ (4/3)*(t*δ^2) := by
    have h1 := mul_le_mul_of_nonneg_right hdhi (sq_nonneg δ)
    nlinarith
  have hx : d*δ^2/((2/5)*B) = (5/2)*a := by dsimp [a]; field_simp <;> ring
  have hy : d*δ^2/((1-2/5)*B) = (5/3)*a := by dsimp [a]; field_simp <;> ring
  have hgap : t-comparatorEffect t δ =
      -Real.log (1-(5/2)*a) + Real.log (1+(5/3)*a) := by
    unfold comparatorEffect
    change t - (t + Real.log (1-d*δ^2/((2/5)*B)) -
      Real.log (1+d*δ^2/((1-2/5)*B))) = _
    rw [hx, hy]
    ring
  obtain ⟨hl, hu⟩ := fair_log_gap_bounds ((5/2)*a) ((5/3)*a)
    (by positivity) (by linarith) (by positivity) (by linarith)
  rw [hgap]
  constructor <;> nlinarith

/-- [The fair comparator stays between half the input effect and the input effect.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:ht). -/
-- @node: comparatorEffect_range_bounds
lemma comparatorEffect_range_bounds (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100) :
    t/2 ≤ comparatorEffect t δ ∧ comparatorEffect t δ ≤ t := by
  obtain ⟨hl, hu⟩ := comparatorEffect_gap_bounds t δ ht hδ
  have hsq : δ^2 ≤ 1/10000 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hδ
    nlinarith [sq_nonneg (δ-1/100), sq_nonneg (δ+1/100)]
  have hm := mul_le_mul_of_nonneg_left hsq ht.1
  have hn := mul_nonneg ht.1 (sq_nonneg δ)
  constructor <;> nlinarith

end CausalSmith.Stat.LogoddsLowsmoothFrontier
