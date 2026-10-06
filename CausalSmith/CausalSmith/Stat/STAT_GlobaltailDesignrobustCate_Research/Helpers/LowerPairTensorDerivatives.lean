module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairCutoffDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Whole-space tensor derivative bounds for the binary witness

The product rule combines the bounded cutoff derivatives into bounded ambient
jets, as in equations (2)--(6) of the lower-pair membership roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

/-- Every coordinate cutoff has bounded ambient derivatives of every order. -/
-- @node: bump1_coordinate_iteratedFDeriv_bounded
lemma bump1_coordinate_iteratedFDeriv_bounded (d n : ℕ) (i : Fin d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Fin d → ℝ,
      ‖iteratedFDeriv ℝ n (fun x : Fin d → ℝ => bump1 (x i)) x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := bump1_iteratedDeriv_bounded n
  let g : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  refine ⟨B * ‖g‖ ^ n, mul_nonneg hB (pow_nonneg (norm_nonneg _) _), fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (bump1 ∘ g) x‖ ≤ _
  rw [g.iteratedFDeriv_comp_right (bump1_contDiff (n := n)) x le_rfl]
  have hc := (iteratedFDeriv ℝ n bump1 (g x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => g)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb (g x)

/-- All tensor-cutoff jets have finite whole-space operator norm bounds. -/
-- @node: witnessBump_iteratedFDeriv_bounded
lemma witnessBump_iteratedFDeriv_bounded (d n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Fin d → ℝ,
      ‖iteratedFDeriv ℝ n (witnessBump d) x‖ ≤ B := by
  classical
  let C : ℕ → Fin d → ℝ := fun k i =>
    (bump1_coordinate_iteratedFDeriv_bounded d k i).choose
  have hC0 (k : ℕ) (i : Fin d) : 0 ≤ C k i :=
    (bump1_coordinate_iteratedFDeriv_bounded d k i).choose_spec.1
  have hC (k : ℕ) (i : Fin d) (x : Fin d → ℝ) :
      ‖iteratedFDeriv ℝ k (fun x : Fin d → ℝ => bump1 (x i)) x‖ ≤ C k i :=
    (bump1_coordinate_iteratedFDeriv_bounded d k i).choose_spec.2 x
  let B : ℝ := ∑ p ∈ (Finset.univ : Finset (Fin d)).sym n,
    ((p : Multiset (Fin d)).countPerms : ℝ) *
      ∏ i : Fin d, C ((p : Multiset (Fin d)).count i) i
  refine ⟨B, ?_, fun x => ?_⟩
  · exact Finset.sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg (fun i _ => hC0 _ i)))
  · have hb := norm_iteratedFDeriv_prod_le (𝕜 := ℝ)
      (u := (Finset.univ : Finset (Fin d)))
      (f := fun i (x : Fin d → ℝ) => bump1 (x i))
      (N := (n : WithTop ℕ∞))
      (fun i _ => bump1_contDiff.comp (contDiff_apply ℝ ℝ i)) (x := x) le_rfl
    apply hb.trans
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hC _ i x)

/-- The next bounded tensor jet controls increments of every tensor derivative. -/
-- @node: witnessBump_iteratedFDeriv_lipschitz_bound
lemma witnessBump_iteratedFDeriv_lipschitz_bound (d n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : Fin d → ℝ,
      ‖iteratedFDeriv ℝ n (witnessBump d) x -
        iteratedFDeriv ℝ n (witnessBump d) y‖ ≤ B * ‖x - y‖ := by
  obtain ⟨B, hB, hb⟩ := witnessBump_iteratedFDeriv_bounded d (n + 1)
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n (witnessBump d)) :=
    (witnessBump_contDiff d (n := ⊤)).differentiable_iteratedFDeriv
      (by exact_mod_cast (show (n : ℕ∞) < ⊤ from by simp))
  refine ⟨B, hB, fun x y => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (fun z _ => hd z)
    (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hb z)
    (convex_univ : Convex ℝ (Set.univ : Set (Fin d → ℝ)))
    (Set.mem_univ y) (Set.mem_univ x)
  exact h

/-- Bounded jets and the mean value theorem give the whole-space tensor Hölder modulus. -/
-- @node: witnessBump_iteratedFDeriv_holder_bound
lemma witnessBump_iteratedFDeriv_holder_bound (d n : ℕ) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : Fin d → ℝ,
      ‖iteratedFDeriv ℝ n (witnessBump d) x -
        iteratedFDeriv ℝ n (witnessBump d) y‖ ≤ B * ‖x - y‖ ^ α := by
  obtain ⟨B0, hB0, hb0⟩ := witnessBump_iteratedFDeriv_bounded d n
  obtain ⟨B1, hB1, hb1⟩ := witnessBump_iteratedFDeriv_lipschitz_bound d n
  refine ⟨max B1 (2 * B0), hB1.trans (le_max_left _ _), fun x y => ?_⟩
  by_cases hxy : ‖x - y‖ ≤ 1
  · have hp : ‖x - y‖ ≤ ‖x - y‖ ^ α :=
      Real.self_le_rpow_of_le_one (norm_nonneg _) hxy hα1
    exact (hb1 x y).trans (mul_le_mul (le_max_left _ _) hp (norm_nonneg _)
      (hB1.trans (le_max_left _ _)))
  · have hp : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_not_ge hxy) hα.le
    have hb : ‖iteratedFDeriv ℝ n (witnessBump d) x -
        iteratedFDeriv ℝ n (witnessBump d) y‖ ≤ 2 * B0 :=
      (norm_sub_le _ _).trans (by linarith [hb0 x, hb0 y])
    exact hb.trans ((le_max_right _ _).trans
      (le_mul_of_one_le_right (hB1.trans (le_max_left _ _)) hp))

end CausalSmith.Stat.GlobalTailDesignRobustCate
