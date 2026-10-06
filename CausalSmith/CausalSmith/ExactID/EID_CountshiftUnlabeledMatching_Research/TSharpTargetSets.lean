module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.SharpTargetQueueComplete

/-! Sharp marginal target sets and order-independent private-row peeling. -/

@[expose] public section

open MeasureTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: incidenceScanPotential_drop
lemma incidenceScanPotential_drop {p : ℕ} (T : Finset (Fin p))
    (degree weight : Fin p → ℕ) :
    (∑ i : Fin p, if 2 ≤ (if i ∈ T then degree i - 1 else degree i) then
        weight i else 0) +
      (∑ i ∈ T, if degree i = 2 then weight i else 0) =
      ∑ i : Fin p, if 2 ≤ degree i then weight i else 0 := by
  classical
  have hsum : (∑ i ∈ T, if degree i = 2 then weight i else 0) =
      ∑ i : Fin p, if i ∈ T then
        (if degree i = 2 then weight i else 0) else 0 := by
    simp
  rw [hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ T
  · simp only [hi, ↓reduceIte]
    split_ifs <;> omega
  · simp [hi]

-- @node: incidencePeelBudget
def incidencePeelBudget {p : ℕ} {G : Type*} [Fintype G]
    (S : G → Finset (Fin p)) (st : IncidencePeelState p G) : ℕ :=
  st.cost + 2 * st.remaining.card +
    3 * ∑ g ∈ st.remaining, (S g).card +
    ∑ i : Fin p, if 2 ≤ st.degree i then 2 * (st.neighbors i).card else 0

-- @node: incidencePeelStep_budget_le
lemma incidencePeelStep_budget_le {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) (st : IncidencePeelState p G)
    (hqueue : st.queue ⊆ st.remaining) :
    incidencePeelBudget S (incidencePeelStep S frozen st) ≤
      incidencePeelBudget S st + 1 := by
  classical
  unfold incidencePeelStep
  split_ifs with hq
  · let g := Classical.choose hq
    have hgq : g ∈ st.queue := Classical.choose_spec hq
    have hgR : g ∈ st.remaining := hqueue hgq
    change st.cost + 2 + 3 * (S g).card +
        (∑ i ∈ S g, if st.degree i = 2 then 2 * (st.neighbors i).card else 0) +
        2 * (st.remaining.erase g).card +
        3 * (∑ h ∈ st.remaining.erase g, (S h).card) +
        (∑ i : Fin p,
          if 2 ≤ (if i ∈ S g then st.degree i - 1 else st.degree i) then
            2 * (st.neighbors i).card else 0) ≤
      incidencePeelBudget S st + 1
    have hcard : (st.remaining.erase g).card + 1 = st.remaining.card := by
      have hpos : 0 < st.remaining.card := Finset.card_pos.mpr ⟨g, hgR⟩
      simp only [Finset.card_erase_of_mem hgR]
      omega
    have hsum : (∑ h ∈ st.remaining.erase g, (S h).card) +
        (S g).card = ∑ h ∈ st.remaining, (S h).card := by
      simpa using Finset.sum_erase_add st.remaining (fun h => (S h).card) hgR
    have hscan := incidenceScanPotential_drop (S g) st.degree
      (fun i => 2 * (st.neighbors i).card)
    unfold incidencePeelBudget
    omega
  · simp [incidencePeelBudget]
    omega

-- @node: incidenceNeighborCard_sum
lemma incidenceNeighborCard_sum {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) :
    (∑ i : Fin p, ((incidencePeelInit S frozen).neighbors i).card) =
      ∑ g : G, (S g).card := by
  classical
  simp_rw [incidencePeelInit_neighbors_correct]
  calc
    (∑ i : Fin p, (Finset.univ.filter fun g : G => i ∈ S g).card) =
        ∑ i : Fin p, ∑ g : G, if i ∈ S g then 1 else 0 := by
      simp
    _ = ∑ g : G, ∑ i : Fin p, if i ∈ S g then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ g : G, (S g).card := by simp

-- @node: incidencePeelInit_budget_le
lemma incidencePeelInit_budget_le {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) :
    incidencePeelBudget S (incidencePeelInit S frozen) ≤
      p + 5 * Fintype.card G + 9 * ∑ g : G, (S g).card := by
  classical
  let st := incidencePeelInit S frozen
  have hcost := incidencePeelInit_cost_le S frozen
  change st.cost ≤ p + 3 * Fintype.card G +
    4 * ∑ g : G, (S g).card at hcost
  have hremaining : st.remaining = Finset.univ := rfl
  have hscan :
      (∑ i : Fin p, if 2 ≤ st.degree i then
          2 * (st.neighbors i).card else 0) ≤
        2 * ∑ i : Fin p, (st.neighbors i).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> omega
  have hneighbors : (∑ i : Fin p, (st.neighbors i).card) =
      ∑ g : G, (S g).card := incidenceNeighborCard_sum S frozen
  unfold incidencePeelBudget
  rw [hremaining]
  simp only [Finset.card_univ]
  change st.cost + 2 * Fintype.card G +
    3 * (∑ g : G, (S g).card) +
    (∑ i : Fin p, if 2 ≤ st.degree i then
      2 * (st.neighbors i).card else 0) ≤
    p + 5 * Fintype.card G + 9 * ∑ g : G, (S g).card
  omega

-- @node: incidencePeelRun_budget_le
lemma incidencePeelRun_budget_le {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (frozen : Option G) :
    incidencePeelBudget S (incidencePeelRun S frozen) ≤
      incidencePeelBudget S (incidencePeelInit S frozen) + Fintype.card G := by
  classical
  let init := incidencePeelInit S frozen
  have hinit : init.queue ⊆ init.remaining := by
    intro g hg
    exact ((incidencePeelInit_queue_iff_deletable S frozen g).mp hg).1
  have hdegree : ∀ i, init.degree i =
      (init.remaining.filter fun g => i ∈ S g).card := by
    intro i
    change (incidencePeelInit S frozen).degree i =
      (Finset.univ.filter fun g => i ∈ S g).card
    exact incidencePeelInit_degree_correct S frozen i
  have hqueue (n : ℕ) :
      ((incidencePeelStep S frozen)^[n] init).queue ⊆
        ((incidencePeelStep S frozen)^[n] init).remaining :=
    (incidencePeelRun_degree_correct S frozen n init hdegree hinit).2
  have hiter (n : ℕ) :
      incidencePeelBudget S ((incidencePeelStep S frozen)^[n] init) ≤
        incidencePeelBudget S init + n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have hstep := incidencePeelStep_budget_le S frozen
          ((incidencePeelStep S frozen)^[n] init) (hqueue n)
        omega
  exact hiter (Fintype.card G)

-- @node: costedFrozenPeeling_cost_le
lemma costedFrozenPeeling_cost_le {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (g : G) :
    (costedFrozenPeeling S g).2 ≤
      12 * (p + Fintype.card G + ∑ h : G, (S h).card) := by
  classical
  let st := incidencePeelRun S (some g)
  have hrun := incidencePeelRun_budget_le S (some g)
  change incidencePeelBudget S st ≤
    incidencePeelBudget S (incidencePeelInit S (some g)) + Fintype.card G at hrun
  have hinit := incidencePeelInit_budget_le S (some g)
  have hcost : st.cost ≤ incidencePeelBudget S st := by
    unfold incidencePeelBudget
    omega
  have hsupport : (S g).card ≤ ∑ h : G, (S h).card := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun h : G => (S h).card)
      (fun h hh => Nat.zero_le _) (Finset.mem_univ g)
  change st.cost + (S g).card ≤ _
  omega

-- @node: costedFrozenPeeling_cost_le_refined
lemma costedFrozenPeeling_cost_le_refined {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p))
    (g : G) :
    (costedFrozenPeeling S g).2 ≤
      p + 6 * Fintype.card G +
        10 * ∑ h : G, (S h).card + (S g).card := by
  classical
  let st := incidencePeelRun S (some g)
  have hrun := incidencePeelRun_budget_le S (some g)
  change incidencePeelBudget S st ≤
    incidencePeelBudget S (incidencePeelInit S (some g)) + Fintype.card G at hrun
  have hinit := incidencePeelInit_budget_le S (some g)
  have hcost : st.cost ≤ incidencePeelBudget S st := by
    unfold incidencePeelBudget
    omega
  change st.cost + (S g).card ≤ _
  omega

-- @node: thm:sharp-target-sets
theorem sharp_target_sets {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (hcompat : (assignmentFiber v).Nonempty) :
    (∀ g, (↑(frozenPeeling (fun h => support v h) g) : Set (Fin p)) =
      targetSet v g) ∧
    (∀ g, peelStep (fun h => support v h) (some g)
      (peelResidual (fun h => support v h) (some g)) =
      peelResidual (fun h => support v h) (some g)) ∧
    (∀ g (run : List (Finset (Fin q))) (terminal : Finset (Fin q)),
      MaximalFrozenDeletionRun (fun h => support v h) (some g) run terminal →
      terminal = peelResidual (fun h => support v h) (some g)) ∧
    (∀ (M : ℕ) (Ω : Type) (ms : MeasurableSpace Ω)
      (μ : Measure Ω),
      letI : MeasurableSpace Ω := ms
      ∀ 𝔐 : AtomicCountModel p M Ω μ,
      GeneratesDirections μ 𝔐 v →
      ∀ g i, i ∈ targetSet v g →
        ∃ (f : Fin q ↪ Fin p) (𝔐' : AtomicCountModel p M Ω μ),
          f ∈ assignmentFiber v ∧ f g = i ∧
          totalEffect 𝔐'.A ∈ completionFiberAt v f ∧
          ∀ m, obsLaw μ 𝔐' m = obsLaw μ 𝔐 m) ∧
    (∀ g : Fin q,
      (costedFrozenPeeling (fun h => support v h) g).1 =
        frozenPeeling (fun h => support v h) g) ∧
    (Finset.univ.sum (fun g : Fin q =>
      (costedFrozenPeeling (fun h => support v h) g).2)) ≤
      12 * q * (p + q + ∑ g : Fin q, (support v g).card) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · classical
    intro g
    apply Set.Subset.antisymm
    · intro i hi
      obtain ⟨f₀, hf₀⟩ := hcompat
      obtain ⟨f, hf, hfg⟩ :=
        frozen_private_realized_by_assignment v f₀ hf₀ g i hi
      exact ⟨f, hf, hfg⟩
    · intro i hi
      obtain ⟨f, hf, rfl⟩ := hi
      let R := peelResidual (fun h => support v h) (some g)
      have hfixed : peelStep (fun h => support v h) (some g) R = R :=
        peelStep_fixed_after_card (fun h => support v h) (some g)
      have hgR : g ∈ R := by
        have hkeep (n : ℕ) : g ∈
            (peelStep (fun h => support v h) (some g))^[n] Finset.univ := by
          induction n with
          | zero => simp
          | succ n ih =>
            rw [Function.iterate_succ_apply']
            simp only [peelStep, Finset.mem_filter]
            exact ⟨ih, Or.inl trivial⟩
        exact hkeep _
      have hprivate : ∀ h ∈ R, h ≠ g → f g ∉ support v h := by
        intro h hh hne hmem
        let T := Relation.TransGen (Hf v f)
        have hacyc := hf.2
        let _ : IsTrans (Fin p) T := inferInstance
        let _ : Std.Irrefl T := ⟨hacyc⟩
        have hwf : WellFounded T := Finite.wellFounded_of_trans_of_irrefl T
        let C : Set (Fin p) :=
          {x | ∃ k ∈ R, k ≠ g ∧ f k = x ∧ T x (f g)}
        have hC : C.Nonempty := by
          refine ⟨f h, h, hh, hne, rfl, ?_⟩
          exact Relation.TransGen.single
            ⟨h, rfl, hmem, fun heq => hne (f.injective heq.symm)⟩
        obtain ⟨x, ⟨k, hk, hkg, rfl, hkpath⟩, hmin⟩ :=
          hwf.has_min C hC
        have hkprivate : ∀ k' ∈ R, k' ≠ k → f k ∉ support v k' := by
          intro k' hk' hkk' hsupport
          have hedge : Hf v f (f k') (f k) :=
            ⟨k', rfl, hsupport, fun heq => hkk' (f.injective heq.symm)⟩
          have hpath : T (f k') (f g) :=
            (Relation.TransGen.single hedge).trans hkpath
          by_cases hkg' : k' = g
          · subst k'
            exact hacyc (f g) hpath
          · exact hmin (f k') ⟨k', hk', hkg', rfl, hpath⟩
              (Relation.TransGen.single hedge)
        have hkdel : k ∉ peelStep (fun h => support v h) (some g) R := by
          simp only [peelStep, Finset.mem_filter]
          intro hkstep
          rcases hkstep.2 with hkg' | hno
          · exact hkg (Option.some.inj hkg')
          · exact hno ⟨f k, hf.1 k, hkprivate⟩
        exact hkdel (hfixed.symm ▸ hk)
      change f g ∈ frozenPeeling (fun h => support v h) g
      simp only [frozenPeeling, Finset.mem_filter]
      exact ⟨hf.1 g, hprivate⟩
  · intro g
    exact peelStep_fixed_after_card (fun h => support v h) (some g)
  · intro g run terminal hrun
    classical
    let S : Fin q → Finset (Fin p) := fun h => support v h
    let step := peelStep S (some g)
    let residual := peelResidual S (some g)
    have hfixed : step residual = residual :=
      peelStep_fixed_after_card S (some g)
    have hmono {R R' : Finset (Fin q)} (hRR' : R ⊆ R') :
        step R ⊆ step R' := by
      intro h hh
      simp only [step, peelStep, Finset.mem_filter] at hh ⊢
      obtain ⟨hR, hkeep⟩ := hh
      refine ⟨hRR' hR, ?_⟩
      rcases hkeep with hfrozen | hprivate
      · exact Or.inl hfrozen
      · right
        intro ⟨i, hi, hiprivate⟩
        apply hprivate
        exact ⟨i, hi, fun k hk hne => hiprivate k (hRR' hk) hne⟩
    have hpreserve {R R' : Finset (Fin q)}
        (hsub : residual ⊆ R)
        (hstep : FrozenDeletionStep S (some g) R R') :
        residual ⊆ R' := by
      obtain ⟨h, ⟨hR, hnotfrozen, i, hi, hiprivate⟩, rfl⟩ := hstep
      intro x hx
      have hxR := hsub hx
      apply Finset.mem_erase.mpr
      refine ⟨?_, hxR⟩
      intro hxh
      subst x
      have hstepmem : h ∈ step residual := hfixed.symm ▸ hx
      simp only [step, peelStep, Finset.mem_filter] at hstepmem
      obtain ⟨_, hkeep⟩ := hstepmem
      rcases hkeep with hfrozen | hno
      · exact hnotfrozen hfrozen
      · apply hno
        exact ⟨i, hi, fun k hk hne => hiprivate k (hsub hk) hne⟩
    have hwalk : ∀ (xs : List (Finset (Fin q))) (R T : Finset (Fin q)),
        residual ⊆ R →
        (∀ A B, (A, B) ∈ (R :: xs).zip (R :: xs).tail →
          FrozenDeletionStep S (some g) A B) →
        (R :: xs).getLast? = some T → residual ⊆ T := by
      intro xs
      induction xs with
      | nil =>
          intro R T hsub _ hlast
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst T
          exact hsub
      | cons R' xs ih =>
          intro R T hsub hsteps hlast
          have hpair : FrozenDeletionStep S (some g) R R' := by
            apply hsteps
            simp
          have hsteps' : ∀ A B,
              (A, B) ∈ (R' :: xs).zip (R' :: xs).tail →
                FrozenDeletionStep S (some g) A B := by
            intro A B hmem
            apply hsteps
            simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr hmem
          apply ih R' T (hpreserve hsub hpair) hsteps'
          simpa using hlast
    have hresSub : residual ⊆ terminal := by
      cases run with
      | nil => simp [MaximalFrozenDeletionRun] at hrun
      | cons R xs =>
        have hhead : R = Finset.univ := by
          simpa using hrun.1
        subst R
        exact hwalk xs Finset.univ terminal (Finset.subset_univ _)
          (fun A B hmem => hrun.2.1 A B hmem) hrun.2.2.1
    have hterminalFixed : step terminal = terminal := by
      apply Finset.Subset.antisymm
      · intro h hh
        simp only [step, peelStep, Finset.mem_filter] at hh
        exact hh.1
      · intro h hh
        simp only [step, peelStep, Finset.mem_filter]
        refine ⟨hh, ?_⟩
        by_cases hfrozen : some h = some g
        · exact Or.inl hfrozen
        · right
          intro hprivate
          exact hrun.2.2.2 h ⟨hh, hfrozen, hprivate⟩
    have hiter (n : ℕ) : terminal ⊆ step^[n] Finset.univ := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          rw [← hterminalFixed]
          exact hmono ih
    apply Finset.Subset.antisymm
    · simpa [residual, peelResidual, step, S] using
        hiter (Fintype.card (Fin q))
    · exact hresSub
  · intro M Ω ms μ
    letI : MeasurableSpace Ω := ms
    intro 𝔐 hgen g i hi
    obtain ⟨f, hf, hfg⟩ := hi
    have hq : 0 < q := Nat.pos_of_ne_zero (by intro h; subst q; exact Fin.elim0 g)
    have hp : 0 < p := Nat.pos_of_ne_zero (by
      intro h
      subst p
      exact Fin.elim0 (f g))
    have hvne : ∀ k, v k ≠ 0 := by
      intro k hz
      have hmem := hf.1 k
      simp [support, hz] at hmem
    have hvdistinct : ∀ k l, k ≠ l → ¬ ProjSim v k l := by
      intro k l hkl hproj
      have hsupports : support v k = support v l := by
        obtain ⟨c, hc, hcv⟩ := hproj
        ext x
        simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
        have heq := congrFun hcv x
        simp only [Pi.smul_apply, smul_eq_mul] at heq
        rw [heq]
        simp [hc]
      exact assignment_distinct_supports v f hf hkl hsupports
    have hmain := (compatibility_completion hp).2.2.2 q hq v hvne hvdistinct
    have hset := (hmain.2.2.2 M Ω ms μ 𝔐 hgen).1
    obtain ⟨B, hBat, _⟩ := canonical_completion_exists v f hf
    have hBfiber : B ∈ completionFiber v := by
      exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hBat⟩⟩
    rw [← hset] at hBfiber
    obtain ⟨𝔐', _, hlaw, hte⟩ := hBfiber
    refine ⟨f, 𝔐', hf, hfg, ?_, hlaw⟩
    exact hte ▸ hBat
  · intro g
    classical
    have hstate := incidencePeelRun_degree_correct
      (fun h => support v h) (some g) (Fintype.card (Fin q))
      (incidencePeelInit (fun h => support v h) (some g))
      (incidencePeelInit_degree_correct (fun h => support v h) (some g))
      (by intro h hh
          exact ((incidencePeelInit_queue_iff_deletable
            (fun h => support v h) (some g) h).mp hh).1)
    have hdegree := hstate.1
    have hgR := incidencePeelRun_frozen_mem
      (fun h => support v h) g (Fintype.card (Fin q))
    ext i
    simp only [costedFrozenPeeling, frozenPeeling, Finset.mem_filter]
    constructor
    · rintro ⟨hi, hd⟩
      refine ⟨hi, ?_⟩
      have hp := (incidenceDegree_one_iff_private
        (fun h => support v h)
        (incidencePeelRun (fun h => support v h) (some g))
        g hgR hdegree i hi).mp hd
      simpa only [incidencePeelRun_remaining_eq_peelResidual] using hp
    · rintro ⟨hi, hp⟩
      refine ⟨hi, ?_⟩
      apply (incidenceDegree_one_iff_private
        (fun h => support v h)
        (incidencePeelRun (fun h => support v h) (some g))
        g hgR hdegree i hi).mpr
      simpa only [incidencePeelRun_remaining_eq_peelResidual] using hp
  · classical
    calc
      (∑ g : Fin q,
          (costedFrozenPeeling (fun h => support v h) g).2) ≤
          ∑ _g : Fin q,
            12 * (p + q + ∑ h : Fin q, (support v h).card) := by
              apply Finset.sum_le_sum
              intro g _
              simpa using costedFrozenPeeling_cost_le
                (fun h => support v h) g
      _ = 12 * q * (p + q + ∑ h : Fin q, (support v h).card) := by
        simp
        ring

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
