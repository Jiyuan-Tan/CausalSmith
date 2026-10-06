module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.SharpTargetIncidence

/-! Completeness of the maintained private-row queue. -/

public section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Every newly deletable group enters the maintained queue. -/
-- @node: incidencePeelStep_queue_complete
lemma incidencePeelStep_queue_complete {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G)
    (hdegree : ∀ i, st.degree i =
      (st.remaining.filter fun h => i ∈ S h).card)
    (hneighbors : ∀ i, st.neighbors i =
      Finset.univ.filter fun h : G => i ∈ S h)
    (hqueueSound : ∀ h, h ∈ st.queue →
      FrozenDeletable S frozen st.remaining h)
    (hqueue : ∀ h, FrozenDeletable S frozen st.remaining h → h ∈ st.queue) :
    ∀ h, FrozenDeletable S frozen
      (incidencePeelStep S frozen st).remaining h →
      h ∈ (incidencePeelStep S frozen st).queue := by
  classical
  intro h hh
  by_cases hq : st.queue.Nonempty
  · let g := Classical.choose hq
    have hgq : g ∈ st.queue := Classical.choose_spec hq
    have hgdel : FrozenDeletable S frozen st.remaining g :=
      hqueueSound g hgq
    have hgR : g ∈ st.remaining := hgdel.1
    have hrem : (incidencePeelStep S frozen st).remaining = st.remaining.erase g := by
      unfold incidencePeelStep
      simp [hq, g]
    have hqueue' : (incidencePeelStep S frozen st).queue =
        st.queue.erase g ∪ (S g).biUnion (fun i =>
          if st.degree i = 2 then
            (st.neighbors i).filter (fun k => k ∈ st.remaining.erase g ∧
              some k ≠ frozen)
          else ∅) := by
      unfold incidencePeelStep
      simp [hq, g]
    obtain ⟨hhR, hhf, i, hi, hip⟩ := hh
    have hR : h ∈ st.remaining := (Finset.mem_erase.mp (hrem ▸ hhR)).2
    have hne : h ≠ g := (Finset.mem_erase.mp (hrem ▸ hhR)).1
    have hqsub : st.queue ⊆ st.remaining :=
      fun k hk => (hqueueSound k hk).1
    have hdegree' := incidencePeelStep_degree_correct S frozen st hdegree hqsub
    have hdnew : (incidencePeelStep S frozen st).degree i = 1 :=
      (incidenceDegree_one_iff_private S (incidencePeelStep S frozen st)
        h hhR hdegree' i hi).mpr hip
    by_cases hig : i ∈ S g
    · have hdold : st.degree i = 2 := by
        have htwo : 0 < st.degree i := by
          rw [hdegree i]
          exact Finset.card_pos.mpr ⟨g, Finset.mem_filter.mpr ⟨hgR, hig⟩⟩
        unfold incidencePeelStep at hdnew
        simp only [dif_pos hq] at hdnew
        change (if i ∈ S g then st.degree i - 1 else st.degree i) = 1 at hdnew
        simp only [if_pos hig] at hdnew
        omega
      rw [hqueue', Finset.mem_union]
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hig, ?_⟩
      simp only [hdold, ↓reduceIte, Finset.mem_filter]
      refine ⟨?_, by simpa [hrem] using hhR, hhf⟩
      rw [hneighbors i]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · have hdold : st.degree i = 1 := by
        unfold incidencePeelStep at hdnew
        simp only [dif_pos hq] at hdnew
        change (if i ∈ S g then st.degree i - 1 else st.degree i) = 1 at hdnew
        simp only [if_neg hig] at hdnew
        exact hdnew
      have holdprivate := (incidenceDegree_one_iff_private S st h hR hdegree i hi).mp hdold
      have hold : FrozenDeletable S frozen st.remaining h := by
        exact ⟨hR, hhf, i, hi, holdprivate⟩
      rw [hqueue', Finset.mem_union]
      left
      exact Finset.mem_erase.mpr ⟨hne, hqueue h hold⟩
  · have hsame : (incidencePeelStep S frozen st).remaining = st.remaining := by
      unfold incidencePeelStep
      simp [hq]
    have hqueue' : (incidencePeelStep S frozen st).queue = st.queue := by
      unfold incidencePeelStep
      simp [hq]
    rw [hqueue']
    exact hqueue h (hsame ▸ hh)

/-- Every deletable group in a maintained-incidence run is queued. -/
-- @node: incidencePeelRun_queue_complete
lemma incidencePeelRun_queue_complete {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (n : ℕ) :
    ∀ h, FrozenDeletable S frozen
      ((incidencePeelStep S frozen)^[n]
        (incidencePeelInit S frozen)).remaining h →
      h ∈ ((incidencePeelStep S frozen)^[n]
        (incidencePeelInit S frozen)).queue := by
  classical
  induction n with
  | zero =>
      intro h hh
      exact (incidencePeelInit_queue_iff_deletable S frozen h).mpr hh
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hstate := incidencePeelRun_degree_correct S frozen n
        (incidencePeelInit S frozen)
        (incidencePeelInit_degree_correct S frozen)
        (by intro h hh
            exact ((incidencePeelInit_queue_iff_deletable S frozen h).mp hh).1)
      exact incidencePeelStep_queue_complete S frozen _ hstate.1
        (incidencePeelRun_neighbors_correct S frozen n)
        (incidencePeelRun_queue_sound S frozen n) ih

/-- A nonempty queue after a step was nonempty before it. -/
-- @node: incidencePeelStep_queue_nonempty_prior
lemma incidencePeelStep_queue_nonempty_prior {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G)
    (h : (incidencePeelStep S frozen st).queue.Nonempty) :
    st.queue.Nonempty := by
  classical
  by_contra hq
  have hempty : st.queue = ∅ := Finset.not_nonempty_iff_eq_empty.mp hq
  have hstep : (incidencePeelStep S frozen st).queue = st.queue := by
    unfold incidencePeelStep
    simp [hq]
  rw [hstep, hempty] at h
  exact Finset.not_nonempty_empty h

/-- If the queue remains nonempty, each prior step spent one group. -/
-- @node: incidencePeelRun_nonempty_card_bound
lemma incidencePeelRun_nonempty_card_bound {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (n : ℕ)
    (hq : (((incidencePeelStep S frozen)^[n]
      (incidencePeelInit S frozen)).queue).Nonempty) :
    n + (((incidencePeelStep S frozen)^[n]
      (incidencePeelInit S frozen)).remaining).card ≤ Fintype.card G := by
  classical
  induction n with
  | zero =>
      simp [incidencePeelInit]
  | succ n ih =>
      let st := (incidencePeelStep S frozen)^[n]
        (incidencePeelInit S frozen)
      have hprev : st.queue.Nonempty := by
        apply incidencePeelStep_queue_nonempty_prior S frozen st
        simpa only [Function.iterate_succ_apply'] using hq
      have hsound := incidencePeelRun_queue_sound S frozen n
        (Classical.choose hprev) (Classical.choose_spec hprev)
      have hgR : Classical.choose hprev ∈ st.remaining := hsound.1
      have hcard : (incidencePeelStep S frozen st).remaining.card + 1 =
          st.remaining.card := by
        unfold incidencePeelStep
        simp only [dif_pos hprev]
        rw [Finset.card_erase_of_mem hgR]
        have hpos : 0 < st.remaining.card := Finset.card_pos.mpr ⟨_, hgR⟩
        omega
      have hrec := ih hprev
      change n + st.remaining.card ≤ Fintype.card G at hrec
      rw [Function.iterate_succ_apply']
      change n + 1 + (incidencePeelStep S frozen st).remaining.card ≤ _
      omega

/-- The queue has no legal deletion left after at most one step per group. -/
-- @node: incidencePeelRun_queue_empty
lemma incidencePeelRun_queue_empty {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) :
    (incidencePeelRun S frozen).queue = ∅ := by
  classical
  by_contra hne
  have hq : (incidencePeelRun S frozen).queue.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hbound := incidencePeelRun_nonempty_card_bound S frozen
    (Fintype.card G) hq
  have hcard : (incidencePeelRun S frozen).remaining.card = 0 := by
    change Fintype.card G + (incidencePeelRun S frozen).remaining.card ≤
      Fintype.card G at hbound
    omega
  obtain ⟨g, hg⟩ := hq
  have hgR := (incidencePeelRun_queue_sound S frozen
    (Fintype.card G) g hg).1
  have hpos : 0 < (incidencePeelRun S frozen).remaining.card := by
    exact Finset.card_pos.mpr ⟨g, hgR⟩
  omega

/-- Maintained-incidence peeling leaves the canonical parallel-peeling residual. -/
-- @node: incidencePeelRun_remaining_eq_peelResidual
lemma incidencePeelRun_remaining_eq_peelResidual {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) :
    (incidencePeelRun S frozen).remaining = peelResidual S frozen := by
  classical
  let step := peelStep S frozen
  let residual := peelResidual S frozen
  have hfixed : step residual = residual :=
    peelStep_fixed_after_card S frozen
  have hmono {R R' : Finset G} (hRR' : R ⊆ R') :
      step R ⊆ step R' := by
    intro h hh
    simp only [step, peelStep, Finset.mem_filter] at hh ⊢
    obtain ⟨hR, hkeep⟩ := hh
    refine ⟨hRR' hR, ?_⟩
    rcases hkeep with hf | hn
    · exact Or.inl hf
    · right
      intro ⟨i, hi, hip⟩
      apply hn
      exact ⟨i, hi, fun k hk hne => hip k (hRR' hk) hne⟩
  have hpreserve (st : IncidencePeelState p G)
      (hsub : residual ⊆ st.remaining)
      (hqueue : ∀ h, h ∈ st.queue →
        FrozenDeletable S frozen st.remaining h) :
      residual ⊆ (incidencePeelStep S frozen st).remaining := by
    by_cases hq : st.queue.Nonempty
    · let g := Classical.choose hq
      have hgdel := hqueue g (Classical.choose_spec hq)
      intro x hx
      have hxR := hsub hx
      simp only [incidencePeelStep, dif_pos hq]
      apply Finset.mem_erase.mpr
      refine ⟨?_, hxR⟩
      intro hxg
      subst x
      have hgstep : g ∈ step residual := hfixed.symm ▸ hx
      simp only [step, peelStep, Finset.mem_filter] at hgstep
      rcases hgstep.2 with hf | hn
      · exact hgdel.2.1 hf
      · obtain ⟨_, _, i, hi, hip⟩ := hgdel
        exact hn ⟨i, hi, fun k hk hne => hip k (hsub hk) hne⟩
    · intro x hx
      simp only [incidencePeelStep, dif_neg hq]
      exact hsub hx
  have hrun (n : ℕ) : residual ⊆
      ((incidencePeelStep S frozen)^[n]
        (incidencePeelInit S frozen)).remaining := by
    induction n with
    | zero =>
        intro x hx
        exact Finset.mem_univ x
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hpreserve _ ih (incidencePeelRun_queue_sound S frozen n)
  have hresSub : residual ⊆ (incidencePeelRun S frozen).remaining := by
    exact hrun (Fintype.card G)
  have hterminalFixed : step (incidencePeelRun S frozen).remaining =
      (incidencePeelRun S frozen).remaining := by
    apply Finset.Subset.antisymm
    · intro h hh
      simp only [step, peelStep, Finset.mem_filter] at hh
      exact hh.1
    · intro h hh
      simp only [step, peelStep, Finset.mem_filter]
      refine ⟨hh, ?_⟩
      by_cases hf : some h = frozen
      · exact Or.inl hf
      · right
        intro hp
        have hdel : FrozenDeletable S frozen
            (incidencePeelRun S frozen).remaining h :=
          ⟨hh, hf, hp⟩
        have hq := incidencePeelRun_queue_complete S frozen
          (Fintype.card G) h hdel
        rw [← incidencePeelRun, incidencePeelRun_queue_empty S frozen] at hq
        simp at hq
  have hiter (n : ℕ) : (incidencePeelRun S frozen).remaining ⊆
      step^[n] Finset.univ := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        rw [← hterminalFixed]
        exact hmono ih
  apply Finset.Subset.antisymm
  · simpa [residual, peelResidual, step] using
      hiter (Fintype.card G)
  · exact hresSub

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
