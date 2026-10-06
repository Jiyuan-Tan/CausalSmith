module
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.AmbientGrid
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.BoundaryTransfer
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Interior interpolation from a bounded top derivative

This isolates the finite-grid estimate for a bounded highest derivative.
The boundary trace is handled separately by `BoundaryTransfer`.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- Fix [a derivative order k](hyp:k), [an interval length d](hyp:d) that is [positive](hyp:hd),
[a nonnegative value envelope M](hyp:M,hM) and [a nonnegative top-derivative envelope
T](hyp:T,hT). Then [there is one nonnegative constant B such that, for every interval from a to
a + d and every function f that is k times continuously differentiable on it, bounded by M there,
and whose k-th within-interval derivative is bounded by T there, every ambient derivative of f of
order at most k is bounded by B at the interior points](goal). -/
theorem uniform_interior_ambient_jet_bound_of_top_bound
    (k : ℕ) (d M T : ℝ) (hd : 0 < d) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (f : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |f x| ≤ M) →
        (∀ x ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x| ≤ T) →
        ∀ j ≤ k, ∀ x ∈ Set.Ioo a (a + d),
          |iteratedDeriv j f x| ≤ B := by
  cases k with
  | zero =>
      refine ⟨M, hM, ?_⟩
      intro a f hf hval htop j hj x hx
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      simpa using hval x (Set.Ioo_subset_Icc_self hx)
  | succ n =>
      obtain ⟨B, hB, hbound⟩ :=
        uniform_interior_ambient_jet_bound n 1 (d / 2) M T
          (by norm_num) (by norm_num) (by linarith) hM hT
      refine ⟨max B T, le_max_of_le_left hB, ?_⟩
      intro a f hf hval htop j hj x hx
      have hab : a < a + d := by linarith
      have hu : UniqueDiffOn ℝ (Set.Icc a (a + d)) := uniqueDiffOn_Icc hab
      have hreg (y : ℝ) (hy : y ∈ Set.Ioo a (a + d)) :
          ContDiffAt ℝ (n + 1) f y :=
        (hf.mono Set.Ioo_subset_Icc_self).contDiffAt (isOpen_Ioo.mem_nhds hy)
      have htop' (y : ℝ) (hy : y ∈ Set.Ioo a (a + d)) :
          |iteratedDeriv (n + 1) f y| ≤ T := by
        rw [← iteratedDerivWithin_eq_iteratedDeriv hu (hreg y hy)
          (Set.Ioo_subset_Icc_self hy)]
        exact htop y (Set.Ioo_subset_Icc_self hy)
      by_cases hjtop : j = n + 1
      · subst j
        exact (htop' x hx).trans (le_max_right _ _)
      · have hjlow : j ≤ n := by omega
        let b : ℝ := (a + x) / 2
        have hsub : Set.Icc b (b + d / 2) ⊆ Set.Ioo a (a + d) := by
          intro y hy
          dsimp [b] at hy
          constructor <;> nlinarith [hy.1, hy.2, hx.1, hx.2, hd]
        have hx' : x ∈ Set.Ioo b (b + d / 2) := by
          dsimp [b]
          constructor <;> nlinarith [hx.1, hx.2]
        have hf' : ContDiffOn ℝ n f (Set.Icc b (b + d / 2)) :=
          (hf.of_le (by exact_mod_cast Nat.le_succ n)).mono
            (Set.Subset.trans hsub Set.Ioo_subset_Icc_self)
        have hval' : ∀ y ∈ Set.Icc b (b + d / 2), |f y| ≤ M := by
          intro y hy
          exact hval y (Set.Ioo_subset_Icc_self (hsub hy))
        have hdiffioo : DifferentiableOn ℝ (iteratedDeriv n f)
            (Set.Ioo a (a + d)) := by
          exact ((hf.mono Set.Ioo_subset_Icc_self).differentiableOn_iteratedDerivWithin
            (Nat.cast_lt.mpr n.lt_succ_self) isOpen_Ioo.uniqueDiffOn).congr
              (fun y hy => (iteratedDerivWithin_of_isOpen isOpen_Ioo hy).symm)
        have hholder : ∀ y ∈ Set.Icc b (b + d / 2),
            ∀ z ∈ Set.Icc b (b + d / 2),
            |iteratedDeriv n f y - iteratedDeriv n f z| ≤
              T * |y - z| ^ (1 : ℝ) := by
          intro y hy z hz
          have hmv := (convex_Ioo a (a + d)).norm_image_sub_le_of_norm_derivWithin_le
            hdiffioo (fun w hw => by
              rw [derivWithin_of_isOpen isOpen_Ioo hw, ← iteratedDeriv_succ,
                Real.norm_eq_abs]
              exact htop' w hw) (hsub hy) (hsub hz)
          simpa [Real.norm_eq_abs, abs_sub_comm] using hmv
        exact (hbound b f hf' hval' hholder j hjlow x hx').trans (le_max_left _ _)

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
