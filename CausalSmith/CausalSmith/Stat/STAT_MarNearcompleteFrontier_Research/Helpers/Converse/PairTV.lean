module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Target

/-! # Nonnegative eight-atom Poisson intensity obligations -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier

/-- All four possible observed coefficients of an oriented pair are nonnegative. Given [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `u`](hyp:u), [the specified input `o`](hyp:o), [the specified input `hz`](hyp:hz), [the specified input `hu`](hyp:hu), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq). -/
-- @node: pairObservedCoeff_nonneg
lemma pairObservedCoeff_nonneg (q σ z u : ℝ) (o : Obs d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hu : u = -1 ∨ u = 1) :
    0 ≤ pairObservedCoeff q σ z u o := by
  have hdlo : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hdhi : delta q ≤ 1 / 2 := by unfold delta; linarith [hq.1]
  rcases hσ with hσ | hσ <;> rcases hz with hz | hz <;> rcases hu with hu | hu <;>
    subst σ <;> subst z <;> subst u <;>
    simp only [pairObservedCoeff] <;> split_ifs <;> norm_num [delta] at * <;> linarith

/-- Every observed count atom has a nonnegative unnormalized intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq). -/
-- @node: countAtomMass_nonneg
lemma countAtomMass_nonneg (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (θ : Theta n d) (o : Obs d)
    (hσ : σ = -1 ∨ σ = 1) :
    0 ≤ countAtomMass n d q σ hd θ o := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := ell_pos_for_normalization n
  have hK := priorK_lower_for_normalization n
  have hKpos : (0 : ℝ) < priorK n := by linarith
  have hM : (pairCount n d : ℝ) ≤ (n : ℝ) * ell n := by
    have hm : pairCount n d ≤ Nat.floor ((n : ℝ) * ell n) := by
      unfold pairCount
      exact min_le_right _ _
    have hf : ((Nat.floor ((n : ℝ) * ell n) : ℕ) : ℝ) ≤ (n : ℝ) * ell n :=
      Nat.floor_le (le_of_lt (mul_pos hnpos hL))
    exact (Nat.cast_le.mpr hm).trans hf
  have hbound : 8 * (pairCount n d : ℝ) ≤ (n : ℝ) * priorK n := by
    nlinarith [mul_nonneg (le_of_lt hnpos) (sub_nonneg.mpr hK)]
  have hsmall : (pairCount n d : ℝ) / (512 * n * priorK n) < 1 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hrewrite :
      2 * (pairCount n d : ℝ) * priorH n * priorB n =
        (pairCount n d : ℝ) / (512 * n * priorK n) := by
    unfold priorH priorB
    field_simp
    <;> ring
  have hf : 0 ≤ fillerMass n d := by
    unfold fillerMass
    rw [hrewrite]
    linarith
  have hcoeff : 0 ≤ fillerObservedCoeff q o := by
    have hb := baseMean_mem_unit q hq
    rcases hb with ⟨hb0, hb1⟩
    unfold fillerObservedCoeff
    split_ifs <;> nlinarith
  have hp (j : Fin (pairCount n d)) : 0 ≤ latentP n (θ.1 j) := by
    unfold latentP
    split
    · exact mul_nonneg (by unfold priorB; positivity)
        (interpolationNode_nonneg_for_normalization n _)
    · positivity
  have hpair (j : Fin (pairCount n d)) (side : Bool) :
      0 ≤ pairObservedCoeff q σ (latentZ n (θ.1 j)) (orientation θ j side) o := by
    apply pairObservedCoeff_nonneg q σ _ _ o hq hσ
    · unfold latentZ
      split <;> (try split_ifs) <;> simp
    · unfold orientation
      split_ifs <;> simp
  unfold countAtomMass
  apply add_nonneg
  · split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro side _
    split_ifs
    · exact mul_nonneg (hp j) (hpair j side)
    · exact le_refl 0

end CausalSmith.Stat.MarNearcompleteFrontier
