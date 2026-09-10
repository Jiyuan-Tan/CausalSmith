import Causalean.Mathlib.Analysis.WeightedCircularTube.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Separated nets and packing bounds on the unit circle

This module constructs finite maximal separated subsets of the Euclidean unit circle and proves
that their number of sites is proportional to the reciprocal of the separation scale. Its
non-strict separation convention makes maximality imply coverage by open balls of the same radius.
-/

noncomputable section

open Metric MeasureTheory Set
open scoped ENNReal NNReal Real Topology

namespace Causalean.Mathlib.Analysis.WeightedCircularTube

/-- For [a real separation scale](hyp:r) and [a set of planar points](hyp:s), the [property of being separated at least at that scale](goal) means that every two distinct points in the set are at distance at least the separation scale. -/
def IsSeparatedAtLeast (r : ℝ) (s : Set Plane) : Prop :=
  s.Pairwise fun x y => r ≤ dist x y

/-- For [a finite set of planar sites](hyp:sites) and [a real separation scale](hyp:r), the [property of being a maximal separated set on the unit circle](goal) means that the sites lie on the unit circle, are separated by at least that scale, and are maximal among all sets with both properties. -/
def IsMaximalSeparated (sites : Finset Plane) (r : ℝ) : Prop :=
  Maximal (fun s : Set Plane => s ⊆ unitCircle ∧ IsSeparatedAtLeast r s) (sites : Set Plane)

/-- For [a finite set of planar sites](hyp:sites) and [a real radius](hyp:r), the [property of covering the unit circle](goal) means that every point of the unit circle belongs to an open ball of radius $r$ centred at one of the sites. -/
def CoversUnitCircle (sites : Finset Plane) (r : ℝ) : Prop :=
  unitCircle ⊆ ⋃ x ∈ (sites : Set Plane), ball x r

private theorem volume_norm_annulus (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    volume {z : Plane | 1 - t < ‖z‖ ∧ ‖z‖ < 1 + t} =
      ENNReal.ofReal (4 * Real.pi * t) := by
  have hset : {z : Plane | 1 - t < ‖z‖ ∧ ‖z‖ < 1 + t} =
      ball 0 (1 + t) \ closedBall 0 (1 - t) := by
    ext z
    simp only [mem_ofPred_eq, mem_sdiff, mem_ball, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨hz2, not_le.mpr hz1⟩
    · rintro ⟨hz2, hz1⟩
      exact ⟨lt_of_not_ge hz1, hz2⟩
  rw [hset, MeasureTheory.measure_sdiff (closedBall_subset_ball (by linarith))
    measurableSet_closedBall.nullMeasurableSet measure_closedBall_lt_top.ne]
  rw [Complex.volume_ball, Complex.volume_closedBall, ENNReal.coe_nnreal_eq]
  rw [← ENNReal.ofReal_pow (by linarith : 0 ≤ 1 + t) 2,
    ← ENNReal.ofReal_pow (by linarith : 0 ≤ 1 - t) 2]
  change ENNReal.ofReal ((1 + t) ^ 2) * ENNReal.ofReal Real.pi -
      ENNReal.ofReal ((1 - t) ^ 2) * ENNReal.ofReal Real.pi =
        ENNReal.ofReal (4 * Real.pi * t)
  rw [← ENNReal.ofReal_mul (sq_nonneg (1 + t)),
    ← ENNReal.ofReal_mul (sq_nonneg (1 - t))]
  rw [← ENNReal.ofReal_sub ((1 + t) ^ 2 * Real.pi)
    (mul_nonneg (sq_nonneg (1 - t)) Real.pi_pos.le)]
  congr 1
  ring

private theorem volume_biUnion_disjoint_balls (sites : Finset Plane) (t : ℝ)
    (hd : Set.Pairwise (sites : Set Plane)
      (Function.onFun Disjoint fun x => ball x t)) (ht : 0 ≤ t) :
    volume (⋃ x ∈ (sites : Set Plane), ball x t) =
      ENNReal.ofReal ((sites.card : ℝ) * Real.pi * t ^ 2) := by
  change volume (⋃ x ∈ sites, ball x t) = _
  rw [MeasureTheory.measure_biUnion_finset hd fun _ _ => measurableSet_ball]
  simp_rw [Complex.volume_ball, ENNReal.coe_nnreal_eq]
  change ∑ _ ∈ sites, ENNReal.ofReal t ^ 2 * ENNReal.ofReal Real.pi =
    ENNReal.ofReal ((sites.card : ℝ) * Real.pi * t ^ 2)
  rw [← ENNReal.ofReal_pow ht 2, Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_mul (sq_nonneg t)]
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (sites.card : ℝ))]
  congr 1
  ring

private theorem volume_biUnion_balls_le (sites : Finset Plane) (t : ℝ) (ht : 0 ≤ t) :
    volume (⋃ x ∈ (sites : Set Plane), ball x t) ≤
      ENNReal.ofReal ((sites.card : ℝ) * Real.pi * t ^ 2) := by
  calc
    volume (⋃ x ∈ (sites : Set Plane), ball x t) =
        volume (⋃ x ∈ sites, ball x t) := rfl
    _ ≤ ∑ x ∈ sites, volume (ball x t) := measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal ((sites.card : ℝ) * Real.pi * t ^ 2) := by
      simp_rw [Complex.volume_ball, ENNReal.coe_nnreal_eq]
      change ∑ _ ∈ sites, ENNReal.ofReal t ^ 2 * ENNReal.ofReal Real.pi = _
      rw [← ENNReal.ofReal_pow ht 2, Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_mul (sq_nonneg t)]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (sites.card : ℝ))]
      congr 1
      ring

/-- When [the separation radius is positive](hyp:hr) and [a finite site set is inclusion-maximal
at that non-strict separation radius](hyp:hmax), [its open balls of that radius cover the unit
circle](goal). -/
theorem unitCircle_maximalSeparated_covers {sites : Finset Plane} {r : ℝ}
    (hr : 0 < r) (hmax : IsMaximalSeparated sites r) :
    CoversUnitCircle sites r := by
  intro x hx
  by_contra hxcover
  simp only [mem_iUnion, mem_ball, not_exists] at hxcover
  have hxsites : x ∉ (sites : Set Plane) := by
    intro hxs
    have := hxcover x hxs
    simp [hr] at this
  have hsep : IsSeparatedAtLeast r (insert x (sites : Set Plane)) := by
    rw [IsSeparatedAtLeast, pairwise_insert]
    refine ⟨hmax.prop.2, ?_⟩
    intro y hy hxy
    exact ⟨not_lt.mp (hxcover y hy), by simpa [dist_comm] using not_lt.mp (hxcover y hy)⟩
  have hle : (sites : Set Plane) ⊆ insert x (sites : Set Plane) := subset_insert _ _
  have hproper := hmax.eq_of_le
    ⟨Set.insert_subset hx hmax.prop.1, hsep⟩ hle
  exact hxsites (hproper ▸ mem_insert x (sites : Set Plane))

/-- At [every positive separation radius](hyp:hr), [there exists a finite inclusion-maximal
separated subset of the unit circle](goal). -/
theorem unitCircle_exists_finite_maximalSeparated {r : ℝ} (hr : 0 < r) :
    ∃ sites : Finset Plane, IsMaximalSeparated sites r := by
  let P : Set (Set Plane) := {s | s ⊆ unitCircle ∧ IsSeparatedAtLeast r s}
  obtain ⟨m, hm⟩ := zorn_subset P (by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, ?_⟩
    · constructor
      · rintro x ⟨s, hs, hxs⟩
        exact (hc hs).1 hxs
      · intro x hx y hy hxy
        obtain ⟨sx, hsx, hxsx⟩ := hx
        obtain ⟨sy, hsy, hxsy⟩ := hy
        rcases hchain.total hsx hsy with hsub | hsub
        · exact (hc hsy).2 (hsub hxsx) hxsy hxy
        · exact (hc hsx).2 hxsx (hsub hxsy) hxy
    · intro s hs
      exact subset_sUnion_of_mem hs)
  have hmfin : m.Finite := by
    let ε : ℝ≥0 := ⟨r / 3, by positivity⟩
    obtain ⟨N, -, hNfin, hNcover⟩ :=
      Metric.exists_finite_isCover_of_isCompact (s := unitCircle) (ε := ε)
        (by
          apply ne_of_gt
          change 0 < r / 3
          linarith) isCompact_unitCircle
    let f : m → N := fun x =>
      ⟨(hNcover (hm.prop.1 x.2)).choose,
        (hNcover (hm.prop.1 x.2)).choose_spec.1⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      by_contra hne
      have hsep : r ≤ dist (x : Plane) y := hm.prop.2 x.2 y.2 hne
      have hxclose := (hNcover (hm.prop.1 x.2)).choose_spec.2
      have hyclose := (hNcover (hm.prop.1 y.2)).choose_spec.2
      change edist (x : Plane) (f x : Plane) ≤ (ε : ℝ≥0∞) at hxclose
      change edist (y : Plane) (f y : Plane) ≤ (ε : ℝ≥0∞) at hyclose
      have hdist : dist (x : Plane) y ≤ 2 * (r / 3) := by
        calc
          dist (x : Plane) y ≤ dist (x : Plane) (f x : Plane) + dist (f x : Plane) y :=
            dist_triangle _ _ _
          _ = dist (x : Plane) (f x : Plane) + dist (f y : Plane) y := by rw [hxy]
          _ ≤ r / 3 + r / 3 := by
            gcongr
            · rw [edist_dist, ENNReal.coe_nnreal_eq,
                ENNReal.ofReal_le_ofReal_iff (by positivity)] at hxclose
              change dist (x : Plane) (f x : Plane) ≤ r / 3 at hxclose
              exact hxclose
            · rw [edist_dist, ENNReal.coe_nnreal_eq,
                ENNReal.ofReal_le_ofReal_iff (by positivity)] at hyclose
              change dist (y : Plane) (f y : Plane) ≤ r / 3 at hyclose
              rw [dist_comm]
              exact hyclose
          _ = 2 * (r / 3) := by ring
      linarith
    letI : Finite N := Set.finite_coe_iff.mpr hNfin
    letI : Finite m := Finite.of_injective f hf
    exact Set.toFinite m
  refine ⟨hmfin.toFinset, ?_⟩
  unfold IsMaximalSeparated
  rw [hmfin.coe_toFinset]
  change Maximal (fun s => s ∈ P) m
  exact hm

private theorem card_le_three_div_of_separated {h : ℝ} {sites : Finset Plane}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 6)
    (hsubcircle : (sites : Set Plane) ⊆ unitCircle)
    (hsep : IsSeparatedAtLeast (3 * h) (sites : Set Plane)) :
    (sites.card : ℝ) ≤ 3 / h := by
  let t : ℝ := 3 * h / 2
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hd : Set.Pairwise (sites : Set Plane)
      (Function.onFun Disjoint fun x => ball x t) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    have := hsep hx hy hxy
    dsimp [t]
    convert this using 1 <;> ring
  have hcontain : (⋃ x ∈ (sites : Set Plane), ball x t) ⊆
      {z : Plane | 1 - t < ‖z‖ ∧ ‖z‖ < 1 + t} := by
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    change dist z x < t at hzx
    have hxnorm : ‖x‖ = 1 := hsubcircle hx
    have htri₁ : dist x 0 ≤ dist x z + dist z 0 := dist_triangle _ _ _
    have htri₂ : dist z 0 ≤ dist z x + dist x 0 := dist_triangle _ _ _
    simp only [dist_zero_right, hxnorm] at htri₁ htri₂
    have hxz : dist x z < t := by simpa only [dist_comm] using hzx
    exact ⟨by linarith, by linarith⟩
  have hvol := measure_mono (μ := volume) hcontain
  rw [volume_biUnion_disjoint_balls sites t hd ht0.le,
    volume_norm_annulus t ht0 ht1] at hvol
  have hreal : (sites.card : ℝ) * Real.pi * t ^ 2 ≤ 4 * Real.pi * t :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol
  dsimp [t] at hreal
  have hp : 0 < Real.pi := Real.pi_pos
  have hc : (sites.card : ℝ) * h * (9 / 4 : ℝ) ≤ 6 := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hh hp)).mp
    calc
      ((sites.card : ℝ) * h * (9 / 4 : ℝ)) * (h * Real.pi) =
          (sites.card : ℝ) * Real.pi * (3 * h / 2) ^ 2 := by ring
      _ ≤ 4 * Real.pi * (3 * h / 2) := hreal
      _ = 6 * (h * Real.pi) := by ring
  apply (le_div_iff₀ hh).2
  nlinarith

private theorem quarter_div_le_card_of_cover {h : ℝ} {sites : Finset Plane}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 6)
    (hcover : CoversUnitCircle sites (3 * h)) :
    (1 / 4 : ℝ) / h ≤ (sites.card : ℝ) := by
  have hh1 : h < 1 := by linarith
  have hcontain : {z : Plane | 1 - h < ‖z‖ ∧ ‖z‖ < 1 + h} ⊆
      ⋃ x ∈ (sites : Set Plane), ball x (4 * h) := by
    intro z hz
    have hznorm : 0 < ‖z‖ := by linarith [hz.1]
    have hz0 : z ≠ 0 := norm_pos_iff.mp hznorm
    let u : Plane := NormedSpace.normalize z
    have hu : u ∈ unitCircle := by
      change ‖u‖ = 1
      exact NormedSpace.norm_normalize hz0
    have hzu_eq : dist z u = |‖z‖ - 1| := by
      calc
        dist z u = dist (‖z‖ • NormedSpace.normalize z) (NormedSpace.normalize z) := by
          rw [NormedSpace.norm_smul_normalize]
        _ = ‖(‖z‖ - 1) • NormedSpace.normalize z‖ := by
          rw [dist_eq_norm, sub_smul, one_smul]
        _ = |‖z‖ - 1| := by
          rw [norm_smul, NormedSpace.norm_normalize hz0, mul_one, Real.norm_eq_abs]
    have hzu : dist z u < h := by
      rw [hzu_eq, abs_lt]
      constructor <;> linarith [hz.1, hz.2]
    have hucover := hcover hu
    simp only [mem_iUnion] at hucover ⊢
    obtain ⟨x, hx, hux⟩ := hucover
    refine ⟨x, hx, ?_⟩
    change dist z x < 4 * h
    change dist u x < 3 * h at hux
    calc
      dist z x ≤ dist z u + dist u x := dist_triangle _ _ _
      _ < h + 3 * h := add_lt_add hzu hux
      _ = 4 * h := by ring
  have hvol₁ := measure_mono (μ := volume) hcontain
  have hvol₂ := volume_biUnion_balls_le sites (4 * h) (by positivity)
  rw [volume_norm_annulus h hh hh1] at hvol₁
  have hvol := hvol₁.trans hvol₂
  have hreal : 4 * Real.pi * h ≤
      (sites.card : ℝ) * Real.pi * (4 * h) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol
  have hp : 0 < Real.pi := Real.pi_pos
  have hc : (1 / 4 : ℝ) ≤ (sites.card : ℝ) * h := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hh hp)).mp
    calc
      (1 / 4 : ℝ) * (h * Real.pi) = Real.pi * h / 4 := by ring
      _ ≤ ((sites.card : ℝ) * Real.pi * (4 * h) ^ 2) / 16 := by linarith
      _ = ((sites.card : ℝ) * h) * (h * Real.pi) := by ring
  exact (div_le_iff₀ hh).2 hc

/-- [There are positive universal constants with an ordered small-scale range such that every
finite site set maximal at separation three times a positive scale in that range has open
three-scale balls covering the unit circle and a number of sites comparable to the reciprocal
scale](goal). -/
theorem unitCircle_maximalSeparated_card_bounds :
    ∃ cpack Cpack hstar : ℝ,
      0 < cpack ∧ cpack ≤ Cpack ∧ 0 < hstar ∧
        ∀ (h : ℝ) (sites : Finset Plane),
          0 < h → h ≤ hstar → IsMaximalSeparated sites (3 * h) →
            CoversUnitCircle sites (3 * h) ∧
              cpack / h ≤ (sites.card : ℝ) ∧
                (sites.card : ℝ) ≤ Cpack / h := by
  refine ⟨1 / 4, 3, 1 / 6, by norm_num, by norm_num, by norm_num, ?_⟩
  intro h sites hh hhsmall hmax
  have hcover : CoversUnitCircle sites (3 * h) :=
    unitCircle_maximalSeparated_covers (by positivity) hmax
  exact ⟨hcover,
    quarter_div_le_card_of_cover hh hhsmall hcover,
    card_le_three_div_of_separated hh hhsmall hmax.prop.1 hmax.prop.2⟩

/-- [There are positive universal constants with an ordered small-scale range such that at every
positive scale in that range one can choose a finite site set maximal at separation three times
that scale, whose open three-scale balls cover the unit circle and whose size is comparable to the
reciprocal scale](goal). -/
theorem unitCircle_exists_maximalSeparated_with_card_bounds :
    ∃ cpack Cpack hstar : ℝ,
      0 < cpack ∧ cpack ≤ Cpack ∧ 0 < hstar ∧
        ∀ (h : ℝ), 0 < h → h ≤ hstar →
          ∃ sites : Finset Plane,
            IsMaximalSeparated sites (3 * h) ∧
              CoversUnitCircle sites (3 * h) ∧
                cpack / h ≤ (sites.card : ℝ) ∧
                  (sites.card : ℝ) ≤ Cpack / h := by
  obtain ⟨cpack, Cpack, hstar, hcpos, hcC, hhstar, hbounds⟩ :=
    unitCircle_maximalSeparated_card_bounds
  refine ⟨cpack, Cpack, hstar, hcpos, hcC, hhstar, ?_⟩
  intro h hh hhstar'
  obtain ⟨sites, hmax⟩ := unitCircle_exists_finite_maximalSeparated (r := 3 * h) (by positivity)
  obtain ⟨hcover, hlower, hupper⟩ := hbounds h sites hh hhstar' hmax
  exact ⟨sites, hmax, hcover, hlower, hupper⟩

end Causalean.Mathlib.Analysis.WeightedCircularTube
