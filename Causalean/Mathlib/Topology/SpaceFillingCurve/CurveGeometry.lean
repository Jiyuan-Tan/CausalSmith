module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CubeInverse
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CubeProximity
public import Causalean.Mathlib.Topology.SpaceFillingCurve.DyadicScale
public import Causalean.Mathlib.Topology.SpaceFillingCurve.TimeProximity

/-!
# Geometry of localized dyadic cube maps

Closed-cell localization implies that the limiting map fills the cube and
obeys the quantitative Hölder bound needed for matching.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- At every parameter in the unit interval, a localized dyadic map takes
its value in the unit cube. -/
theorem LocalizedCubeMap.mapsToCube {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    InUnitCube (H.toFun t) := by
  have htime : t ∈ dyadicTimeCell d 0 ⟨0, by simp⟩ := by
    simpa [dyadicTimeCell] using ht
  have hcube := H.localizes 0 ⟨0, by simp⟩ t htime
  simpa [dyadicCubeCell, InUnitCube] using hcube

/-- A localized dyadic cube map reaches every point of the unit cube from a
parameter in the unit interval. -/
theorem LocalizedCubeMap.surjectiveOn {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) (x : Fin d → ℝ) (hx : InUnitCube x) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ H.toFun t = x := by
  obtain ⟨t, ht, hcells⟩ := T.exists_parameter_for_cubePoint x hx
  refine ⟨t, ht, ?_⟩
  apply T.eq_of_shared_cubeCells
  intro n
  obtain ⟨k, htk, hxk⟩ := hcells n
  exact ⟨k, H.localizes n k t htk, hxk⟩

/-- Given [a cube dimension and traversal](hyp:d,T), [a localized map](hyp:H), [a dimension of at least two](hyp:hd),
and [two unit-interval parameters](hyp:s,t,hs,ht), [the squared Euclidean distance between the map's two values is at most 16·d·|s − t|^(2/d)](goal), a Hölder bound of exponent 1/d. -/
theorem LocalizedCubeMap.modulus {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) (hd : 2 ≤ d) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    sqEuclideanDist (H.toFun s) (H.toFun t) ≤
      16 * (d : ℝ) * |s - t| ^ ((2 : ℝ) / d) := by
  -- Separate `s = t`. Otherwise use `exists_dyadicScale` on `|s-t|`,
  -- `exists_neighboring_timeCells` at that scale, then localize both values.
  -- Combine `sqEuclideanDist_le_of_neighboring_cubeCells` with
  -- `dyadicScale_sq_bound` and multiply by `4*d`.
  -- For a zero gap, rewrite the distance as a sum of zero squares. For a
  -- positive gap, the scale upper bound supplies `hgap` for time proximity;
  -- both resulting memberships feed `H.localizes` at the same level.
  -- `hs` and `ht` give `|s-t| ≤ 1`.  At a positive gap, take the scale
  -- `n` and neighboring indices `k,l`; the cube estimate is `4*d*w_n²`,
  -- while the lower scale inequality gives `w_n² ≤ 4*gap^(2/d)`.
  by_cases heq : s = t
  · subst t
    simp [sqEuclideanDist] <;> positivity
  · have hδ : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr heq)
    have hδ1 : |s - t| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> have := hs.1 <;> have := hs.2 <;>
        have := ht.1 <;> have := ht.2 <;> linarith
    obtain ⟨n, hnlow, hnup⟩ := exists_dyadicScale d (by omega) hδ hδ1
    obtain ⟨k, l, hsk, htl, hkl, hlk⟩ :=
      exists_neighboring_timeCells d n hs ht hnup
    have hcube := sqEuclideanDist_le_of_neighboring_cubeCells T k l
      ⟨hkl, hlk⟩ (H.toFun s) (H.toFun t)
      (H.localizes n k s hsk) (H.localizes n l t htl)
    have hscale := dyadicScale_sq_bound d n (by omega) hnlow
    have hdR : (0 : ℝ) ≤ d := by exact_mod_cast (Nat.zero_le d)
    nlinarith [mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hdR)]

/-- The quantitative squared-distance modulus makes a localized dyadic cube
map continuous on the unit interval. -/
theorem LocalizedCubeMap.continuousOn {d : ℕ} {T : DyadicTraversal d}
    (H : LocalizedCubeMap d T) (hd : 2 ≤ d) :
    ContinuousOn H.toFun (Set.Icc (0 : ℝ) 1) := by
  -- Apply the coordinatewise sequential or epsilon-delta criterion to
  -- `H.modulus`; each squared coordinate increment is bounded by the sum.
  -- Equivalently derive the norm Hölder estimate using `sqEuclideanDist`
  -- as the squared `EuclideanSpace` distance, then use
  -- `HolderOnWith.continuousOn`. Coordinatewise `continuousOn_pi` avoids
  -- changing the tuple codomain.
  -- For the coordinate route, `Finset.single_le_sum` bounds each squared
  -- coordinate increment by `sqEuclideanDist`. Use `continuousOn_iff`
  -- with a small positive radius and `Real.continuous_rpow_const` at zero,
  -- then assemble coordinates via `continuousOn_pi`.
  apply continuousOn_pi.mpr
  intro i
  intro s hs
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hp : 0 < (2 : ℝ) / d := by
    positivity
  have hbound : Filter.Tendsto
      (fun t : ℝ => Real.sqrt (16 * (d : ℝ) * |s - t| ^ ((2 : ℝ) / d)))
      (nhdsWithin s (Set.Icc (0 : ℝ) 1)) (nhds 0) := by
    have hc : ContinuousAt
        (fun t : ℝ => Real.sqrt (16 * (d : ℝ) * |s - t| ^ ((2 : ℝ) / d))) s := by
      fun_prop (disch := positivity)
    have hh : ContinuousWithinAt
        (fun t : ℝ => Real.sqrt (16 * (d : ℝ) * |s - t| ^ ((2 : ℝ) / d)))
        (Set.Icc (0 : ℝ) 1) s := hc.continuousWithinAt
    have hzero : Real.sqrt (16 * (d : ℝ) * |s - s| ^ ((2 : ℝ) / d)) = 0 := by
      simp [hp.ne']
    simpa only [ContinuousWithinAt, hzero] using hh
  apply squeeze_zero' (Filter.Eventually.of_forall fun t => dist_nonneg)
    ?_ hbound
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hcoord : ((H.toFun s i) - (H.toFun t i)) ^ 2 ≤
      sqEuclideanDist (H.toFun s) (H.toFun t) := by
    unfold sqEuclideanDist
    exact Finset.single_le_sum (f := fun j : Fin d => (H.toFun s j - H.toFun t j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hmod := H.modulus hd hs ht
  have hnonneg : 0 ≤ 16 * (d : ℝ) * |s - t| ^ ((2 : ℝ) / d) := by positivity
  have hsqrt := (Real.le_sqrt
    (show 0 ≤ |H.toFun t i - H.toFun s i| by positivity) hnonneg).mpr
    (by
      calc
        |H.toFun t i - H.toFun s i| ^ 2 = (H.toFun s i - H.toFun t i) ^ 2 := by
          rw [sq_abs]
          ring
        _ ≤ sqEuclideanDist (H.toFun s) (H.toFun t) := hcoord
        _ ≤ 16 * (d : ℝ) * |s - t| ^ ((2 : ℝ) / d) := hmod)
  simpa [Real.dist_eq, abs_sub_comm] using hsqrt

end Causalean.Mathlib.Topology.SpaceFillingCurve
