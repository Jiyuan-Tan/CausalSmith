import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TRademacherMixtureSeparation

/-!
# High-probability diagonal supports

This file turns finite-design convergence in probability into finite supports
whose probability tends to one and on which the error vanishes uniformly.
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @node: FiniteDesign.TendstoInProb.exists_uniform_support
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,X,c,hX), [the exists uniform support result holds](goal). -/
lemma FiniteDesign.TendstoInProb.exists_uniform_support
    {Ω : ℕ → Type*} [∀ r, Fintype (Ω r)] [∀ r, DecidableEq (Ω r)]
    {D : ∀ r, FiniteDesign (Ω r)}
    {X : ∀ r, Ω r → ℝ} {c : ℝ}
    (hX : FiniteDesign.TendstoInProb D X (fun _ => c)) :
    ∃ (Γ : ∀ r, Finset (Ω r)) (e : ℕ → ℝ),
      Tendsto (fun r => (D r).Pr (fun w => w ∈ Γ r)) atTop (nhds 1) ∧
      Tendsto e atTop (nhds 0) ∧
      (∀ r, 0 < e r) ∧
      (∀ r w, w ∈ Γ r → |X r w - c| < e r) ∧
      Tendsto (fun r => sSup {x : ℝ | ∃ w ∈ Γ r,
        x = |X r w - c|}) atTop (nhds 0) := by
  classical
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδpos : ∀ k, 0 < δ k := by
    intro k
    dsimp [δ]
    positivity
  have hcut : ∀ k, ∃ N, ∀ r, N ≤ r →
      (D r).Pr (fun w => δ k ≤ |X r w - c|) < δ k := by
    intro k
    have ht := hX (δ k) (hδpos k)
    have hev : ∀ᶠ r in atTop,
        (D r).Pr (fun w => δ k ≤ |X r w - c|) < δ k :=
      (tendsto_order.1 ht).2 (δ k) (hδpos k)
    exact eventually_atTop.1 hev
  choose N hN using hcut
  let m : ℕ → ℕ := fun k => if k = 0 then 0 else max k (N k)
  let level : ℕ → ℕ := fun r => Nat.findGreatest (fun k => m k ≤ r) r
  have hlevel : Tendsto level atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro k
    refine ⟨max k (m k), fun r hr => ?_⟩
    apply Nat.le_findGreatest
    · exact (le_max_left k (m k)).trans hr
    · exact (le_max_right k (m k)).trans hr
  let e : ℕ → ℝ := fun r => δ (level r)
  have he : Tendsto e atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hlevel
  let Γ : ∀ r, Finset (Ω r) := fun r => Finset.univ.filter
    (fun w => |X r w - c| < e r)
  have hlevel_spec : ∀ r, m (level r) ≤ r := by
    intro r
    apply Nat.findGreatest_spec (P := fun k => m k ≤ r) (Nat.zero_le r)
    simp [m]
  have hbad : Tendsto (fun r => (D r).Pr
      (fun w => e r ≤ |X r w - c|)) atTop (nhds 0) := by
    exact squeeze_zero (fun r => (D r).Pr_nonneg _) (fun r => by
      by_cases hk : level r = 0
      · simpa [e, δ, hk] using (D r).Pr_le_one
          (fun w => e r ≤ |X r w - c|)
      · exact (hN (level r) r ((le_max_right _ _).trans (by
          simpa [m, hk] using hlevel_spec r))).le) he
  have hprob : Tendsto (fun r => (D r).Pr (fun w => w ∈ Γ r))
      atTop (nhds 1) := by
    apply Tendsto.congr' _ (by simpa using
      (tendsto_const_nhds.sub hbad : Tendsto (fun r => 1 -
        (D r).Pr (fun w => e r ≤ |X r w - c|)) atTop (nhds (1 - 0))))
    filter_upwards [] with r
    unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
    simp only [Γ, Finset.mem_filter, Finset.mem_univ, true_and]
    symm
    calc
      ∑ z, (D r).p z * (if |X r z - c| < e r then 1 else 0) =
          (∑ z, (D r).p z) -
            ∑ z, (D r).p z * (if e r ≤ |X r z - c| then 1 else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : |X r z - c| < e r
        · simp [hz, not_le.mpr hz]
        · simp [hz, le_of_not_gt hz]
      _ = 1 - ∑ z, (D r).p z *
          (if e r ≤ |X r z - c| then 1 else 0) := by rw [(D r).p_sum]
  have hnonempty : ∀ᶠ r in atTop, (Γ r).Nonempty := by
    have hpositive : ∀ᶠ r in atTop,
        (1 : ℝ) / 2 < (D r).Pr (fun w => w ∈ Γ r) :=
      (tendsto_order.1 hprob).1 ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hpositive] with r hr
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hz : (D r).Pr (fun w => w ∈ Γ r) = 0 := by
      rw [hempty]
      unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
      simp
    linarith
  have hsSup : Tendsto (fun r => sSup {x : ℝ | ∃ w ∈ Γ r,
      x = |X r w - c|}) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ he
    · filter_upwards [hnonempty] with r hr
      obtain ⟨w, hw⟩ := hr
      let S : Set ℝ := {x : ℝ | ∃ w ∈ Γ r, x = |X r w - c|}
      have hmem : |X r w - c| ∈ S := ⟨w, hw, rfl⟩
      have hbdd : BddAbove S := by
        refine ⟨e r, ?_⟩
        rintro x ⟨v, hv, rfl⟩
        exact (by simpa [Γ] using hv : |X r v - c| < e r).le
      exact (abs_nonneg _).trans (le_csSup hbdd hmem)
    · filter_upwards [hnonempty] with r hr
      apply csSup_le
      · obtain ⟨w, hw⟩ := hr
        exact ⟨|X r w - c|, w, hw, rfl⟩
      · rintro x ⟨w, hw, rfl⟩
        exact (by simpa [Γ] using hw : |X r w - c| < e r).le
  exact ⟨Γ, e, hprob, he, fun r => hδpos (level r), (by
    intro r w hw
    simpa [Γ] using hw), hsSup⟩

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
