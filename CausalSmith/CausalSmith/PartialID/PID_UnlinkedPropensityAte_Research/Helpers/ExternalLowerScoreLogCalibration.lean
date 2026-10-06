module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogTesting

/-! Numerical calibration of the three-score external-log perturbation. -/

@[expose] public section

open MeasureTheory Set Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,x,y,z), [this definition](goal) introduces the corresponding object. -/
def threeScoreGapSq {ε : ℝ} (x y z : ScoreSpace ε) : ℝ :=
  ((z : ℝ) - y) ^ 2 + ((z : ℝ) - x) ^ 2 + ((y : ℝ) - x) ^ 2

/-- For [the specified mathematical inputs](hyp:ε,α,x,y,z,m), [this definition](goal) introduces the corresponding object. -/
def threeScoreCalibratedU {ε : ℝ} (α : ℝ) (x y z : ScoreSpace ε) (m : ℕ) : ℝ :=
  Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2)) /
    (Real.sqrt 3 * Real.sqrt (threeScoreGapSq x y z) * Real.sqrt (m : ℝ))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,_hxy,hyz), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreGapSq_pos {ε : ℝ} (x y z : ScoreSpace ε)
    (_hxy : x < y) (hyz : y < z) :
    0 < threeScoreGapSq x y z := by
  unfold threeScoreGapSq
  have hzy : 0 < (z : ℝ) - y := sub_pos.mpr hyz
  nlinarith [sq_pos_of_pos hzy, sq_nonneg ((z : ℝ) - x), sq_nonneg ((y : ℝ) - x)]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hα,x,y,z,hxy,hyz,m,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreCalibratedU_pos {ε : ℝ} (α : ℝ)
    (hα : 0 < α ∧ α < 1 / 2) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z) (m : ℕ) (hm : 0 < m) :
    0 < threeScoreCalibratedU α x y z m := by
  unfold threeScoreCalibratedU
  have hβ : 0 < 1 - 2 * α := by linarith [hα.2]
  have hlog : 0 < Real.log (1 + (1 - 2 * α) ^ 2) :=
    Real.log_pos (by nlinarith [sq_pos_of_pos hβ])
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  positivity [threeScoreGapSq_pos x y z hxy hyz]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hα,x,y,z,hxy,hyz,m,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreCalibratedU_chisq_scalar {ε : ℝ} (α : ℝ)
    (hα : 0 < α ∧ α < 1 / 2) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z) (m : ℕ) (hm : 0 < m) :
    3 * (threeScoreCalibratedU α x y z m) ^ 2 * threeScoreGapSq x y z =
      Real.log (1 + (1 - 2 * α) ^ 2) / (m : ℝ) := by
  let c : ℝ := Real.log (1 + (1 - 2 * α) ^ 2)
  let D : ℝ := threeScoreGapSq x y z
  have hβ : 0 < 1 - 2 * α := by linarith [hα.2]
  have hc : 0 < c := by
    dsimp [c]
    exact Real.log_pos (by nlinarith [sq_pos_of_pos hβ])
  have hD : 0 < D := threeScoreGapSq_pos x y z hxy hyz
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hroot3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hrootc : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
  have hrootD : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD.le
  have hrootm : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  change 3 * (Real.sqrt c /
      (Real.sqrt 3 * Real.sqrt D * Real.sqrt (m : ℝ))) ^ 2 * D = c / (m : ℝ)
  rw [div_pow, mul_pow, mul_pow, hroot3, hrootc, hrootD, hrootm]
  field_simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hα,x,y,z,hxy,hyz,m,hm), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreCalibratedU_pow_bound {ε : ℝ} (α : ℝ)
    (hα : 0 < α ∧ α < 1 / 2) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z) (m : ℕ) (hm : 0 < m) :
    (1 + 3 * (threeScoreCalibratedU α x y z m) ^ 2 *
      threeScoreGapSq x y z) ^ m ≤ 1 + (1 - 2 * α) ^ 2 := by
  rw [threeScoreCalibratedU_chisq_scalar α hα x y z hxy hyz m hm]
  let c : ℝ := Real.log (1 + (1 - 2 * α) ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    have hβ : 0 < 1 - 2 * α := by linarith [hα.2]
    exact Real.log_pos (by nlinarith [sq_pos_of_pos hβ])
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.one_sub_div_pow_le_exp_neg (n := m) (t := -c)
    (by linarith : -c ≤ (m : ℝ))
  have hexp : Real.exp c = 1 + (1 - 2 * α) ^ 2 := Real.exp_log (by positivity)
  simpa only [c, neg_div, sub_neg_eq_add, neg_neg, hexp] using h

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,x,y,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreCalibratedU_tendsto_zero {ε : ℝ} (α : ℝ)
    (x y z : ScoreSpace ε) :
    Tendsto (fun m : ℕ => threeScoreCalibratedU α x y z m) atTop (nhds 0) := by
  have hinv : Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  let C : ℝ := Real.sqrt (Real.log (1 + (1 - 2 * α) ^ 2)) /
    (Real.sqrt 3 * Real.sqrt (threeScoreGapSq x y z))
  have h : Tendsto (fun m : ℕ => C * (Real.sqrt (m : ℝ))⁻¹)
      atTop (nhds (C * 0)) := tendsto_const_nhds.mul hinv
  convert h using 1
  · funext m
    dsimp [C, threeScoreCalibratedU]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  · simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,x,y,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreCalibratedU_eventually_weights_pos {ε : ℝ} (α : ℝ)
    (x y z : ScoreSpace ε) :
    ∀ᶠ m : ℕ in atTop,
      0 < 1 / 3 + threeScoreCalibratedU α x y z m * ((z : ℝ) - y) ∧
      0 < 1 / 3 - threeScoreCalibratedU α x y z m * ((z : ℝ) - x) ∧
      0 < 1 / 3 + threeScoreCalibratedU α x y z m * ((y : ℝ) - x) := by
  have hu := threeScoreCalibratedU_tendsto_zero α x y z
  have hxlim : Tendsto (fun m : ℕ =>
      1 / 3 + threeScoreCalibratedU α x y z m * ((z : ℝ) - y))
      atTop (nhds (1 / 3)) := by
    simpa using tendsto_const_nhds.add (hu.mul_const ((z : ℝ) - y))
  have hylim : Tendsto (fun m : ℕ =>
      1 / 3 - threeScoreCalibratedU α x y z m * ((z : ℝ) - x))
      atTop (nhds (1 / 3)) := by
    simpa using tendsto_const_nhds.sub (hu.mul_const ((z : ℝ) - x))
  have hzlim : Tendsto (fun m : ℕ =>
      1 / 3 + threeScoreCalibratedU α x y z m * ((y : ℝ) - x))
      atTop (nhds (1 / 3)) := by
    simpa using tendsto_const_nhds.add (hu.mul_const ((y : ℝ) - x))
  filter_upwards
    [hxlim.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)),
      hylim.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3)),
      hzlim.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))]
    with m hxm hym hzm
  exact ⟨hxm, hym, hzm⟩

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,T,ρ,α,hα,x,y,z,hxy,hyz,m,hm,hx,hy,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreCalibratedU_commonTrial_tv_bound {ε : ℝ} {T : Type*}
    [MeasurableSpace T] (ρ : Measure T) [IsProbabilityMeasure ρ]
    (α : ℝ) (hα : 0 < α ∧ α < 1 / 2) (x y z : ScoreSpace ε)
    (hxy : x < y) (hyz : y < z) (m : ℕ) (hm : 0 < m)
    (hx : 0 < 1 / 3 + threeScoreCalibratedU α x y z m * ((z : ℝ) - y))
    (hy : 0 < 1 / 3 - threeScoreCalibratedU α x y z m * ((z : ℝ) - x))
    (hz : 0 < 1 / 3 + threeScoreCalibratedU α x y z m * ((y : ℝ) - x)) :
    Causalean.Stat.tvDist
      (ρ.prod (Measure.pi (fun _ : Fin m =>
        threeScorePerturbedLaw x y z (threeScoreCalibratedU α x y z m))))
      (ρ.prod (Measure.pi (fun _ : Fin m => threeScoreBaseLaw x y z))) ≤
      (1 - 2 * α) / 2 := by
  let u := threeScoreCalibratedU α x y z m
  have htv := threeScorePerturbedLaw_commonTrial_tv_bound
    ρ x y z u hxy hyz hx hy hz m
  have hpow := threeScoreCalibratedU_pow_bound α hα x y z hxy hyz m hm
  have hβ : 0 < 1 - 2 * α := by linarith [hα.2]
  calc
    _ ≤ (1 / 2 : ℝ) * Real.sqrt
        ((1 + 3 * u ^ 2 * threeScoreGapSq x y z) ^ m - 1) := by
      simpa [u, threeScoreGapSq] using htv
    _ ≤ (1 / 2 : ℝ) * Real.sqrt ((1 - 2 * α) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
      linarith
    _ = (1 - 2 * α) / 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hβ]
      ring

end
end CausalSmith.PartialID.UnlinkedPropensityAte
