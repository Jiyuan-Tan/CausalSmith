module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridAdmissibility
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridApprox
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.PairPolynomial

/-!
# Error transfer for the finite stable-grid fit

Lexicographic tie breaking preserves the minimum empirical residual. A candidate
that approximates the seven population moments then bounds the selected fit's
population discrepancy by twice the sampling error plus the grid error.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators

/-- The scalar moment represented by a decoded stable grid candidate. -/
-- @node: gridCodeMoment
noncomputable def gridCodeMoment {M : Nat} (alpha : ℝ) (c : GridCode M) (k : Nat) : ℝ :=
  ∑ s : Fin 4,
    (Matrix.vecMul (gridNu c) ((stabilizedGridMatrix alpha c) ^ k)) s * gridReward c s

/-- The lexicographic tie break selects a candidate with minimum empirical residual. [Under the listed formal conditions](hyp:hα,hc), [the stated conclusion holds](goal).-/
-- @node: selectGridCode_objective_le
lemma selectGridCode_objective_le {T M : Nat} (alpha : ℝ) (hα : 0 ≤ alpha)
    (b e : Policy 2) (w : ObsView T 2) {c : GridCode M}
    (hc : c ∈ gridCandidates M alpha) :
    gridObjective alpha b e w (selectGridCode (M := M) alpha b e w) ≤
      gridObjective alpha b e w c := by
  classical
  unfold selectGridCode
  rw [dif_pos (gridCandidates_nonempty M alpha hα)]
  dsimp only
  split_ifs with hm
  · have htie := (Finset.mem_filter.mp
      (Classical.choose_spec (Finset.exists_min_image _ gridLexCode hm)).1).2
    rw [htie]
    exact (Classical.choose_spec (Finset.exists_min_image _ _
      (gridCandidates_nonempty M alpha hα))).2 c hc
  · exact (Classical.choose_spec (Finset.exists_min_image _ _
      (gridCandidates_nonempty M alpha hα))).2 c hc

/-- An approximating candidate transfers the empirical maximum error to the
selected realization's population moments. [Under the listed formal conditions](hyp:hα,hc,happrox), [the stated conclusion holds](goal).-/
-- @node: selected_grid_moment_error
lemma selected_grid_moment_error {T M : Nat} (alpha : ℝ) (hα : 0 ≤ alpha)
    (b e : Policy 2) (w : ObsView T 2) (m : Fin 7 → ℝ) (eta : ℝ)
    {c : GridCode M} (hc : c ∈ gridCandidates M alpha)
    (happrox : ∀ k : Fin 7, |m k - gridCodeMoment alpha c k.val| ≤ eta) :
    (⨆ k : Fin 7,
      |gridCodeMoment alpha (selectGridCode (M := M) alpha b e w) k.val - m k|) ≤
      2 * (⨆ k : Fin 7, |empiricalMoment k.val b e w - m k|) + eta := by
  let eps := ⨆ k : Fin 7, |empiricalMoment k.val b e w - m k|
  have heps (k : Fin 7) : |empiricalMoment k.val b e w - m k| ≤ eps := by
    dsimp only [eps]
    exact le_ciSup (f := fun j : Fin 7 => |empiricalMoment j.val b e w - m j|)
      (Set.finite_range _).bddAbove k
  have hcobj : gridObjective alpha b e w c ≤ eps + eta := by
    apply ciSup_le
    intro k
    exact (abs_sub_le _ (m k) _).trans (add_le_add (heps k) (happrox k))
  have hfit := (selectGridCode_objective_le alpha hα b e w hc).trans hcobj
  apply ciSup_le
  intro k
  have hres : |empiricalMoment k.val b e w -
      gridCodeMoment alpha (selectGridCode (M := M) alpha b e w) k.val| ≤
      gridObjective alpha b e w (selectGridCode (M := M) alpha b e w) := by
    unfold gridObjective
    exact le_ciSup (f := fun j : Fin 7 => |empiricalMoment j.val b e w -
      gridCodeMoment alpha (selectGridCode (M := M) alpha b e w) j.val|)
      (Set.finite_range _).bddAbove k
  calc
    _ ≤ |gridCodeMoment alpha (selectGridCode (M := M) alpha b e w) k.val -
          empiricalMoment k.val b e w| + |empiricalMoment k.val b e w - m k| :=
      abs_sub_le _ _ _
    _ ≤ (eps + eta) + eps := by
      rw [abs_sub_comm (gridCodeMoment alpha _ k.val)]
      exact add_le_add (hres.trans hfit) (heps k)
    _ = _ := by dsimp only [eps]; ring

/-- Equation (15) of the upper-bound proof: the actual selected candidate fits
all seven target-policy moments within twice their sampling error plus T⁻¹. [Under the listed formal conditions](hyp:hT,hM), [the stated conclusion holds](goal).-/
-- @node: selected_grid_intervention_moment_error
lemma selected_grid_intervention_moment_error {T : Nat} {t0 zeta : ℝ}
    (hT : 12 ≤ T) (M : RawPomdpExperiment T 2 2)
    (hM : BinaryPomdpClass t0 zeta M) (w : ObsView T 2) :
    let m := fun k : Fin 7 => matrixMoment (stationaryLaw (policyKernel M M.b))
      (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val
    (⨆ k : Fin 7,
      |gridCodeMoment (mixingAlpha t0)
        (selectGridCode (M := gridSize T (mixingAlpha t0))
          (mixingAlpha t0) M.b M.e w) k.val - m k|) ≤
      2 * (⨆ k : Fin 7, |empiricalMoment k.val M.b M.e w - m k|) + (T : ℝ)⁻¹ := by
  obtain ⟨c, hc, herr⟩ := grid_approximation hT M hM
  apply selected_grid_moment_error (mixingAlpha t0) (Real.exp_nonneg _) M.b M.e w
    _ (T : ℝ)⁻¹ hc
  simpa only [matrixMoment, fourMatrixPower, gridCodeMoment] using herr

end CausalSmith.Stat.PomdpBinaryhiddenRate
