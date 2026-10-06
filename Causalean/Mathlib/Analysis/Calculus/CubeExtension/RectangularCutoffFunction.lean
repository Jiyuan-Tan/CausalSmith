module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.RectangularAffineGeometry
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth cutoffs between nested rectangular boxes

A fixed smooth cutoff equals one on the normalized cube and vanishes near
the boundary of a prescribed larger closed box. Its finitely many derivatives
are uniformly bounded by constants depending only on the boxes and order.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open scoped ContDiff
open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- [The open coordinate box](goal) with [corners lo and hi](hyp:lo,hi) consists of
the points lying strictly between lo_i and hi_i in every coordinate i. -/
def rectOpenBox {d : ℕ} (lo hi : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, lo i < x i ∧ x i < hi i}

/-- If [the box with corners lo and hi strictly contains the normalized cube in
every coordinate, that is lo_i < −1 and 1 < hi_i](hyp:hmargin), then for [any
order m](hyp:m) [there is a smooth function χ equal to one on the cube, with
closed support inside the open box, whose ambient derivatives of every order up
to m + 1 are bounded in operator norm by a positive constant B](goal). -/
theorem exists_rectangular_smooth_cutoff (d m : ℕ)
    (lo hi : Fin d → ℝ) (hmargin : ∀ i, lo i < -1 ∧ 1 < hi i) :
    ∃ χ : (Fin d → ℝ) → ℝ,
      ContDiff ℝ ∞ χ ∧
      (∀ x ∈ cube d, χ x = 1) ∧
      tsupport χ ⊆ rectOpenBox lo hi ∧
      ∃ B : ℝ, 0 < B ∧
        ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ B := by
  obtain ⟨q, hq, hqface⟩ :
      ∃ q : ℝ, 1 < q ∧ ∀ i, q ≤ min (-lo i) (hi i) := by
    by_cases hd : d = 0
    · subst d
      exact ⟨2, by norm_num, fun i => Fin.elim0 i⟩
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdpos
      let q : ℝ := (Finset.univ : Finset (Fin d)).inf' Finset.univ_nonempty
        (fun i => min (-lo i) (hi i))
      refine ⟨q, ?_, ?_⟩
      · apply (Finset.lt_inf'_iff _).2
        intro i hi_mem
        have hm := hmargin i
        exact lt_min (by linarith [hm.1]) hm.2
      · intro i
        exact Finset.inf'_le _ (Finset.mem_univ i)
  let rIn : ℝ := (1 + q) / 2
  let rOut : ℝ := (rIn + q) / 2
  have hrIn : 1 < rIn := by dsimp [rIn]; linarith
  have hrOut : rIn < rOut := by dsimp [rOut, rIn]; linarith
  have hrOutq : rOut < q := by dsimp [rOut, rIn]; linarith
  let χ : ContDiffBump (0 : Fin d → ℝ) :=
    ⟨rIn, rOut, by linarith, hrOut⟩
  have hχ : ContDiff ℝ ∞ (χ : (Fin d → ℝ) → ℝ) := χ.contDiff
  have hχone : ∀ x ∈ cube d, χ x = 1 := by
    intro x hx
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖x‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
      intro i
      simpa only [Real.norm_eq_abs] using (abs_le.mpr (hx i))
    exact hnorm.trans hrIn.le
  have hχsupp : tsupport (χ : (Fin d → ℝ) → ℝ) ⊆ rectOpenBox lo hi := by
    intro x hx i
    rw [χ.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at hx
    have hxi : |x i| ≤ rOut := (norm_le_pi_norm x i).trans hx
    have hface := hqface i
    constructor
    · have : -q < x i := by linarith [abs_le.mp hxi]
      linarith [le_min_iff.mp hface]
    · have : x i < q := by linarith [abs_le.mp hxi]
      linarith [le_min_iff.mp hface]
  have hχcompact : HasCompactSupport (χ : (Fin d → ℝ) → ℝ) := χ.hasCompactSupport
  have hbound : ∀ j : Fin (m + 2), ∃ C : ℝ,
      ∀ x, ‖iteratedFDeriv ℝ j.val (χ : (Fin d → ℝ) → ℝ) x‖ ≤ C := by
    intro j
    exact (hχcompact.iteratedFDeriv j.val).exists_bound_of_continuous
      ((contDiff_infty.mp hχ j.val).continuous_iteratedFDeriv')
  choose C hC using hbound
  let B : ℝ := max 1 ((Finset.univ : Finset (Fin (m + 2))).sup' Finset.univ_nonempty C)
  refine ⟨χ, hχ, hχone, hχsupp, B, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro j hj x
    have hj' : j < m + 2 := by omega
    have hle : C ⟨j, hj'⟩ ≤ B :=
      (Finset.le_sup' C (Finset.mem_univ ⟨j, hj'⟩)).trans (le_max_right _ _)
    exact (hC ⟨j, hj'⟩ x).trans hle

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
