module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentSpanning
/-! Parent-before-child enumerations of finite connected graphs and the resulting
specified labeled-tree probability bound. This closes the geometric input to the general
Cayley component-count estimate and sparse common-mass Hamming-cost bound. -/
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Every finite connected graph has an ordering in which each non-root vertex has an earlier
neighbor. Removing a non-cut vertex constructs the ordering inductively.  [the theorem's stated inputs and assumptions](hyp:hG), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:m,G). -/
-- @node: connected_parent_order
lemma connected_parent_order (m : ℕ) (G : SimpleGraph (Fin (m + 1)))
    (hG : G.Connected) :
    ∃ e : Fin (m + 1) ≃ Fin (m + 1),
      ∀ i, i ≠ 0 → ∃ j, j < i ∧ G.Adj (e i) (e j) := by
  classical
  induction m with
  | zero =>
    refine ⟨Equiv.refl _, ?_⟩
    intro i hi
    apply (hi _).elim
    apply Fin.ext
    have := i.isLt
    simp only [Fin.val_zero]
    omega
  | succ m ih =>
    obtain ⟨v, hv⟩ := hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let a : Fin (m + 1) ≃ {x : Fin (m + 2) // x ≠ v} := finSuccAboveEquiv v
    let H := (G.induce {v}ᶜ).comap a
    have hH : H.Connected := (SimpleGraph.Iso.comap a _).connected_iff.mpr hv
    obtain ⟨e, he⟩ := ih H hH
    let f : Fin (m + 2) ≃ Fin (m + 2) :=
      (finSuccEquivLast.trans (Equiv.optionCongr e)).trans (finSuccEquiv' v).symm
    have hf (i : Fin (m + 1)) : f i.castSucc = v.succAbove (e i) := by
      simp [f, Equiv.trans_apply, finSuccEquivLast_castSucc]
    have hfl : f (Fin.last (m + 1)) = v := by
      simp [f, Equiv.trans_apply]
    refine ⟨f, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · intro hi
      obtain ⟨w, hw⟩ := hG.preconnected.exists_adj_of_nontrivial v
      let b : {x : Fin (m + 2) // x ≠ v} := ⟨w, hw.ne.symm⟩
      let j := e.symm (a.symm b)
      refine ⟨j.castSucc, Fin.castSucc_lt_last j, ?_⟩
      rw [hfl, hf]
      have hb : v.succAbove (e j) = w := by
        change (a (e j)).val = w
        simp [j, b]
      rw [hb]
      exact hw
    · intro hi
      have hk : k ≠ 0 := by
        intro hk
        apply hi
        simp [hk]
      obtain ⟨j, hj, hadj⟩ := he k hk
      refine ⟨j.castSucc, by simpa using hj, ?_⟩
      rw [hf, hf]
      exact hadj

/-- Shared-sign edges from each child to its earlier parent imply membership in the recursive
ordered-tree event. The result uses [the stated assumptions](hyp:hL,hedge) and establishes [the displayed conclusion](goal). -/
-- @node: mem_orderedSharedTreeEvent_of_edges
lemma mem_orderedSharedTreeEvent_of_edges (hL : ℝ)
    (p : (k : ℕ) → Fin (k + 1)) (m : ℕ) (x : Fin (m + 1) → Covariate)
    (hedge : ∀ k (hk : k < m), sharedAdj hL (m + 1) x
      ⟨k + 1, by omega⟩ ⟨(p k).val, by have := (p k).isLt; omega⟩) :
    x ∈ orderedSharedTreeEvent hL p m := by
  induction m with
  | zero => exact Set.mem_univ _
  | succ m ih =>
    refine ⟨ih (fun i => x i.castSucc) ?_, ?_⟩
    · intro k hk
      have h := hedge k (by omega)
      simpa only [sharedAdj, Fin.castSucc_mk, ne_eq, Fin.mk.injEq] using h
    · exact hedge m (by omega)

/-- A specified connected labeled graph on at least two iid uniform covariates obeys the
root-length times child-length envelope. A fixed connected ordering discards every unused edge.
 [the theorem's stated inputs and assumptions](hyp:m,hm,T,hT), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: labeledSharedTreeEvent_volume_le
lemma labeledSharedTreeEvent_volume_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (m : ℕ) (hm : 1 ≤ m) (T : SimpleGraph (Fin (m + 1))) (hT : T.Connected) :
    (Measure.pi (fun _ : Fin (m + 1) => (volume : Measure Covariate)))
      (labeledSharedTreeEvent hL (m + 1) (m + 1) id T) ≤
      ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ m) := by
  classical
  obtain ⟨e, he⟩ := connected_parent_order m T hT
  have hparent (k : ℕ) (hk : k < m) :
      ∃ j : Fin (k + 1), T.Adj (e ⟨k + 1, by omega⟩)
        (e ⟨j.val, by have := j.isLt; omega⟩) := by
    obtain ⟨j, hj, hadj⟩ := he ⟨k + 1, by omega⟩ (by
      intro h; have := congrArg Fin.val h; simp at this)
    exact ⟨⟨j.val, by exact hj⟩, hadj⟩
  let p : (k : ℕ) → Fin (k + 1) := fun k =>
    if hk : k < m then (hparent k hk).choose else 0
  have hp (k : ℕ) (hk : k < m) :
      T.Adj (e ⟨k + 1, by omega⟩)
        (e ⟨(p k).val, by have := (p k).isLt; omega⟩) := by
    simpa only [p, dif_pos hk] using (hparent k hk).choose_spec
  calc
    _ ≤ (Measure.pi (fun _ : Fin (m + 1) => (volume : Measure Covariate)))
        {x | (fun i => x (e i)) ∈ orderedSharedTreeEvent hL p m} := by
      apply measure_mono
      intro x hx
      apply mem_orderedSharedTreeEvent_of_edges
      intro k hk
      have h := hx _ _ (hp k hk)
      exact ⟨fun heq => (hp k hk).ne (congrArg e heq), h.2⟩
    _ ≤ _ := selected_orderedSharedTreeEvent_volume_le hL hhL (m + 1) m hm e e.injective p


/-- Every specified labeled tree has the roadmap probability envelope, without an assumed
enumeration or probability bound.  [the theorem's stated inputs and assumptions](hyp:hhL,s,hs,T,T), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: uniform_labeled_tree_probability_bound
lemma uniform_labeled_tree_probability_bound (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (s : ℕ) (hs : 2 ≤ s)
    (T : {T : SimpleGraph (Fin s) // T.IsTree}) :
    (Measure.pi (fun _ : Fin s => (volume : Measure Covariate)))
      (labeledSharedTreeEvent hL s s id T.val) ≤
        ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ (s - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  simpa using labeledSharedTreeEvent_volume_le hL hhL m (by omega)
    T.val T.property.connected

/-- The actual size-s component count has the binomial Cayley expectation bound under iid
uniform design.  [the theorem's stated inputs and assumptions](hyp:hL,hhL,n,s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:cayley). -/
-- @node: lintegral_sizeComponentCount_le_cayley
lemma lintegral_sizeComponentCount_le_cayley (cayley : CayleyLabeledTreeCount)
    (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n s : ℕ) (hs : 2 ≤ s) :
    (∫⁻ x, (sizeComponentCount hL n x s : ℝ≥0∞)
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))) ≤
      ENNReal.ofReal ((n.choose s : ℝ) * 2 * hL * (s : ℝ) ^ (s - 2) *
        (4 * deltaL hL) ^ (s - 1)) := by
  exact lintegral_sizeComponentCount_le_of_uniform_labeled_tree_bound cayley hL n s hs
    (uniform_labeled_tree_probability_bound hL hhL s hs)

/-- The constructed common-mass coupling has expected Hamming cost at most 1024 times
separation, squared sample size, macro radius, and micro radius in the sparse regime.  [the theorem's stated inputs and assumptions](hyp:hL,hhL,n,hn,hcap,n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:cayley). -/
-- @node: commonMassCoupling_hamming_cost_le_sparse
lemma commonMassCoupling_hamming_cost_le_sparse (cayley : CayleyLabeledTreeCount)
    (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ) (hn : 1 ≤ n)
    (hcap : (n : ℝ) * deltaL hL ≤ 1 / 128) :
    (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂commonMassCoupling hL n) ≤
      ENNReal.ofReal (1024 * separation hL * (n : ℝ) ^ 2 * hL * deltaL hL) := by
  exact commonMassCoupling_hamming_cost_le_of_labeled_tree_bound cayley hL hhL n hn hcap
    (fun s hs _ => uniform_labeled_tree_probability_bound hL hhL s hs)

end CausalSmith.Stat.PrivateCateRoughdesign
