module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogCalibration

/-! Explicit strict filling thresholds for the calibrated three-score pair. -/

@[expose] public section

open Filter
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,x,y,z), [this definition](goal) introduces the corresponding object. -/
def threeScoreThreshold {ε : ℝ} (x y z : ScoreSpace ε) : ℝ :=
  (((x : ℝ) / 3) + min (((x : ℝ) + y) / 3) ((z : ℝ) / 3)) / 2

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,hx0,hxy,hyz), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreThreshold_baseline {ε : ℝ} (x y z : ScoreSpace ε)
    (hx0 : 0 < (x : ℝ)) (hxy : x < y) (hyz : y < z) :
    let t := threeScoreThreshold x y z
    let q := ((x : ℝ) + y + z) / 3
    (x : ℝ) * (1 / 3) < t ∧
      t < min ((x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3))
        ((z : ℝ) * (1 / 3)) ∧
      0 < t / q ∧ t / q < 1 := by
  dsimp only
  have hxyR : (x : ℝ) < (y : ℝ) := hxy
  have hyzR : (y : ℝ) < (z : ℝ) := hyz
  have hy0 : 0 < (y : ℝ) := lt_trans hx0 hxy
  have hz0 : 0 < (z : ℝ) := lt_trans hy0 hyz
  have hlower : (x : ℝ) / 3 <
      min (((x : ℝ) + y) / 3) ((z : ℝ) / 3) := by
    rw [lt_min_iff]
    constructor <;> linarith
  have htLower : (x : ℝ) / 3 < threeScoreThreshold x y z := by
    unfold threeScoreThreshold
    linarith
  have htUpper : threeScoreThreshold x y z <
      min (((x : ℝ) + y) / 3) ((z : ℝ) / 3) := by
    unfold threeScoreThreshold
    linarith
  have hq : 0 < ((x : ℝ) + y + z) / 3 := by linarith
  have ht0 : 0 < threeScoreThreshold x y z := lt_trans (by positivity) htLower
  have htq : threeScoreThreshold x y z < ((x : ℝ) + y + z) / 3 := by
    have hmin := min_le_left (((x : ℝ) + y) / 3) ((z : ℝ) / 3)
    linarith
  refine ⟨?_, ?_, div_pos ht0 hq, (div_lt_one hq).2 htq⟩
  · convert htLower using 1 <;> norm_num [div_eq_mul_inv]
  · convert htUpper using 1 <;> norm_num [div_eq_mul_inv] <;> ring

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,α,hα,x,y,z,hx0,hxy,hyz), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreCalibratedU_eventually_thresholds {ε : ℝ}
    (α : ℝ) (hα : 0 < α ∧ α < 1 / 2)
    (x y z : ScoreSpace ε) (hx0 : 0 < (x : ℝ))
    (hxy : x < y) (hyz : y < z) :
    ∀ᶠ m : ℕ in atTop,
      let u := threeScoreCalibratedU α x y z m
      let t := threeScoreThreshold x y z
      0 < 1 / 3 + u * ((z : ℝ) - y) ∧
      0 < 1 / 3 - u * ((z : ℝ) - x) ∧
      0 < 1 / 3 + u * ((y : ℝ) - x) ∧
      0 ≤ u ∧ u * ((z : ℝ) - x) ≤ 1 / 3 ∧
      (x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) < t ∧
      t < min
        ((x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) +
          (y : ℝ) * (1 / 3 - u * ((z : ℝ) - x)))
        ((z : ℝ) * (1 / 3 + u * ((y : ℝ) - x))) := by
  have hbase := threeScoreThreshold_baseline x y z hx0 hxy hyz
  dsimp only at hbase
  have hu := threeScoreCalibratedU_tendsto_zero α x y z
  have hxlim : Tendsto (fun m : ℕ =>
      (x : ℝ) * (1 / 3 + threeScoreCalibratedU α x y z m *
        ((z : ℝ) - y))) atTop (nhds ((x : ℝ) * (1 / 3))) := by
    convert tendsto_const_nhds.mul
      (tendsto_const_nhds.add (hu.mul_const ((z : ℝ) - y))) using 1 <;> simp
  have hxylim : Tendsto (fun m : ℕ =>
      (x : ℝ) * (1 / 3 + threeScoreCalibratedU α x y z m *
          ((z : ℝ) - y)) +
        (y : ℝ) * (1 / 3 - threeScoreCalibratedU α x y z m *
          ((z : ℝ) - x))) atTop
      (nhds ((x : ℝ) * (1 / 3) + (y : ℝ) * (1 / 3))) := by
    convert
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.add (hu.mul_const ((z : ℝ) - y)))).add
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub (hu.mul_const ((z : ℝ) - x)))) using 1 <;> simp
  have hzlim : Tendsto (fun m : ℕ =>
      (z : ℝ) * (1 / 3 + threeScoreCalibratedU α x y z m *
        ((y : ℝ) - x))) atTop (nhds ((z : ℝ) * (1 / 3))) := by
    convert tendsto_const_nhds.mul
      (tendsto_const_nhds.add (hu.mul_const ((y : ℝ) - x))) using 1 <;> simp
  filter_upwards
    [threeScoreCalibratedU_eventually_weights_pos α x y z,
      eventually_gt_atTop (0 : ℕ),
      hxlim.eventually (Iio_mem_nhds hbase.1),
      hxylim.eventually (Ioi_mem_nhds (lt_of_lt_of_le hbase.2.1
        (min_le_left _ _))),
      hzlim.eventually (Ioi_mem_nhds (lt_of_lt_of_le hbase.2.1
        (min_le_right _ _)))]
    with m hweights hm hfirst hfirstTwo hthird
  dsimp only
  have hu0 := (threeScoreCalibratedU_pos α hα x y z hxy hyz m hm).le
  refine ⟨hweights.1, hweights.2.1, hweights.2.2, hu0, ?_, hfirst, ?_⟩
  · linarith [hweights.2.1]
  · exact lt_min hfirstTwo hthird

end
end CausalSmith.PartialID.UnlinkedPropensityAte
