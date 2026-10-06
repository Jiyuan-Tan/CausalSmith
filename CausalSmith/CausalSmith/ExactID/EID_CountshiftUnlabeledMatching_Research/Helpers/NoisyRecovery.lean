module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TNoUniformNoisyIncompleteSharpness
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TSharpTargetSets

/-! Support recovery and peeling equivalences for noisy incomplete experiments. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- A coordinatewise error below half the declared margin recovers every
nonzero coordinate, simultaneously across environments. -/
-- @node: recoveredSupport_eq_of_margin
lemma recoveredSupport_eq_of_margin {p M : ℕ}
    (d dhat : Fin M → Fin p → ℝ) (ε β : ℝ)
    (_hε : 0 < ε) (hβ : 2 * ε < β)
    (hmargin : β ≤ supportMargin d)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ ε) :
    ∀ m, recoveredSupport dhat β m =
      Finset.univ.filter (fun i => d m i ≠ 0) := by
  classical
  intro m
  ext i
  simp only [recoveredSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hzero : d m i = 0
  · simp only [hzero, ne_eq, not_true_eq_false, iff_false]
    intro hi
    have herror := happrox m i
    rw [hzero, sub_zero] at herror
    linarith
  · simp only [hzero, ne_eq, not_false_eq_true, iff_true]
    have hmem : |d m i| ∈
        {x : ℝ | ∃ m' i', d m' i' ≠ 0 ∧ x = |d m' i'|} :=
      ⟨m, i, hzero, rfl⟩
    have hbelow : BddBelow
        {x : ℝ | ∃ m' i', d m' i' ≠ 0 ∧ x = |d m' i'|} := by
      refine ⟨0, ?_⟩
      rintro x ⟨m', i', _, rfl⟩
      exact abs_nonneg _
    have habs : β ≤ |d m i| := hmargin.trans (csInf_le hbelow hmem)
    have herror := happrox m i
    have hreverse := abs_sub_abs_le_abs_sub (d m i) (dhat m i)
    rw [abs_sub_comm] at hreverse
    linarith

/-- The duplicate baseline and one added coordinate have support margin equal to
the added coordinate's strength. -/
-- @node: duplicateAlternative_supportMargin
lemma duplicateAlternative_supportMargin (p : ℕ) [NeZero p] (h : ℝ)
    (d : Fin p → Fin p → ℝ) (_hp : 4 ≤ p) (hh : 0 < h) (hh1 : h ≤ 1)
    (hbase : ∀ m, m ≠ 1 → d m = Pi.single 0 1)
    (halt : ∃ j : Fin p, j ≠ 0 ∧
      d 1 = (fun i => (Pi.single 0 (1 : ℝ) : Fin p → ℝ) i +
        h * (Pi.single j (1 : ℝ) : Fin p → ℝ) i)) :
    supportMargin d = h := by
  classical
  obtain ⟨j, hj0, hj⟩ := halt
  have h1j : d 1 j = h := by
    rw [hj]
    simp [hj0]
  have hbound : ∀ m i, d m i ≠ 0 → h ≤ |d m i| := by
    intro m i hne
    by_cases hm : m = 1
    · subst m
      rw [hj] at hne ⊢
      by_cases hi0 : i = 0
      · subst i
        simp [Ne.symm hj0] at hne ⊢
        simpa using hh1
      · by_cases hij : i = j
        · subst i
          simp [hj0] at hne ⊢
          exact le_abs_self h
        · simp [hi0, hij] at hne
    · rw [hbase m hm] at hne ⊢
      by_cases hi0 : i = 0
      · subst i
        simpa using hh1
      · simp [hi0] at hne
  have hmem : h ∈ {x : ℝ | ∃ m i, d m i ≠ 0 ∧ x = |d m i|} := by
    exact ⟨1, j, by rw [h1j]; exact ne_of_gt hh, by rw [h1j, abs_of_pos hh]⟩
  have hbelow : BddBelow {x : ℝ | ∃ m i, d m i ≠ 0 ∧ x = |d m i|} :=
    ⟨h, by rintro x ⟨m, i, hne, rfl⟩; exact hbound m i hne⟩
  apply le_antisymm
  · exact csInf_le hbelow hmem
  · apply le_csInf ⟨h, hmem⟩
    rintro x ⟨m, i, hne, rfl⟩
    exact hbound m i hne

/-- In a compatible model, equal shift supports identify exactly the
projective classes. -/
-- @node: compatible_support_eq_iff_proj
lemma compatible_support_eq_iff_proj {p M : ℕ}
    (d : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (hcompat : (assignmentFiber r.v).Nonempty) (m m' : Fin M) :
    (Finset.univ.filter (fun i => d m i ≠ 0) =
      Finset.univ.filter (fun i => d m' i ≠ 0)) ↔ ProjSim d m m' := by
  classical
  have hsupp (k : Fin M) :
      Finset.univ.filter (fun i => d k i ≠ 0) = support r.v (r.κ k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, support]
    rw [r.decomp k]
    simp [r.c_ne k]
  rw [hsupp m, hsupp m']
  constructor
  · intro heq
    obtain ⟨f, hf⟩ := hcompat
    exact (r.classes m m').mp (by
      by_contra hne
      exact assignment_distinct_supports r.v f hf hne heq)
  · intro hproj
    exact congrArg (support r.v) ((r.classes m m').mpr hproj)

/-- Uniform coordinate error and a support margin make support grouping agree
with projective grouping. -/
-- @node: recovered_support_eq_iff_proj
lemma recovered_support_eq_iff_proj {p M : ℕ}
    (d dhat : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (hcompat : (assignmentFiber r.v).Nonempty) (ε β : ℝ)
    (hε : 0 < ε) (hβ : 2 * ε < β)
    (hmargin : β ≤ supportMargin d)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ ε)
    (m m' : Fin M) :
    recoveredSupport dhat β m = recoveredSupport dhat β m' ↔
      ProjSim d m m' := by
  rw [recoveredSupport_eq_of_margin d dhat ε β hε hβ hmargin happrox m,
    recoveredSupport_eq_of_margin d dhat ε β hε hβ hmargin happrox m']
  exact compatible_support_eq_iff_proj d r hcompat m m'

/-- Transport peelStep_map_equiv across a relabeling of the support groups. -/
-- @node: peelStep_map_equiv
theorem peelStep_map_equiv {p : ℕ} {G H : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (S : G → Finset (Fin p)) (frozen : Option G) (R : Finset G) :
    peelStep (fun h => S (e.symm h)) (frozen.map e) (R.map e.toEmbedding) =
      (peelStep S frozen R).map e.toEmbedding := by
  classical
  ext h
  simp only [peelStep, Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨⟨g, hg, hgh⟩, hh⟩
    subst h
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    rcases hh with hf | hn
    · left
      cases frozen <;> simp at hf ⊢
      simpa using hf
    · right
      intro ⟨i, hi, hip⟩
      apply hn
      refine ⟨i, by simpa using hi, ?_⟩
      intro h' hh' hne
      obtain ⟨g', hg', rfl⟩ := hh'
      simpa using hip g' hg' (by exact fun he => hne (congrArg e he))
  · rintro ⟨g, ⟨hg, hh⟩, hgh⟩
    subst h
    refine ⟨⟨g, hg, rfl⟩, ?_⟩
    rcases hh with hf | hn
    · left
      simpa using congrArg (Option.map e) hf
    · right
      intro ⟨i, hi, hip⟩
      apply hn
      refine ⟨i, by simpa using hi, ?_⟩
      intro g' hg' hne
      simpa using hip (e g') ⟨g', hg', rfl⟩
        (by intro he; exact hne (e.injective he))

/-- Transport peelResidual_map_equiv across a relabeling of the support groups. -/
-- @node: peelResidual_map_equiv
theorem peelResidual_map_equiv {p : ℕ} {G H : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (S : G → Finset (Fin p)) (frozen : Option G) :
    peelResidual (fun h => S (e.symm h)) (frozen.map e) =
      (peelResidual S frozen).map e.toEmbedding := by
  classical
  have hiter (n : ℕ) (R : Finset G) :
      (peelStep (fun h => S (e.symm h)) (frozen.map e))^[n]
        (R.map e.toEmbedding) =
      ((peelStep S frozen)^[n] R).map e.toEmbedding := by
    induction n generalizing R with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ih, peelStep_map_equiv]
  unfold peelResidual
  rw [← Fintype.card_congr e]
  convert hiter (Fintype.card G) Finset.univ using 1
  · simp

/-- Transport peelsAll_equiv across a relabeling of the support groups. -/
-- @node: peelsAll_equiv
theorem peelsAll_equiv {p : ℕ} {G H : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (S : G → Finset (Fin p)) :
    peelsAll (fun h => S (e.symm h)) ↔ peelsAll S := by
  classical
  simp only [peelsAll]
  have h := peelResidual_map_equiv e S none
  simp only [Option.map_none] at h
  rw [h]
  exact Finset.map_eq_empty

/-- Transport recoveredGroupEquiv across a relabeling of the support groups. -/
-- @node: recoveredGroupEquiv
theorem recoveredGroupEquiv {p M : ℕ}
    (d dhat : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (hcompat : (assignmentFiber r.v).Nonempty) (ε β : ℝ)
    (hε : 0 < ε) (hβ : 2 * ε < β)
    (hmargin : β ≤ supportMargin d)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ ε) :
    ∃ e : Fin r.q ≃
      {s : Finset (Fin p) // s ∈ Finset.univ.image (recoveredSupport dhat β)},
      ∀ g, (e g).val = support r.v g := by
  classical
  have hsupp (m : Fin M) : recoveredSupport dhat β m =
      support r.v (r.κ m) := by
    rw [recoveredSupport_eq_of_margin d dhat ε β hε hβ hmargin happrox m]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, support]
    rw [r.decomp m]
    simp [r.c_ne m]
  let f : Fin r.q →
      {s : Finset (Fin p) // s ∈ Finset.univ.image (recoveredSupport dhat β)} :=
    fun g => ⟨support r.v g, by
      obtain ⟨m, hm⟩ := r.κ_surj g
      exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, by rw [hsupp, hm]⟩⟩
  have hinj : Function.Injective f := by
    intro g h hgh
    by_contra hne
    obtain ⟨a, ha⟩ := hcompat
    have heq : support r.v g = support r.v h := congrArg Subtype.val hgh
    exact assignment_distinct_supports r.v a ha hne heq
  have hsurj : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hs
    refine ⟨r.κ m, ?_⟩
    apply Subtype.ext
    change support r.v (r.κ m) = s
    rw [← hsupp m, hm]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro g
  rfl


/-- Exact support recovery makes the distinct support family peelable. -/
-- @node: recoveredCompatible_of_margin
theorem recoveredCompatible_of_margin {p M : ℕ}
    (d dhat : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (hcompat : (assignmentFiber r.v).Nonempty) (ε β : ℝ)
    (hε : 0 < ε) (hβ : 2 * ε < β)
    (hmargin : β ≤ supportMargin d)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ ε) :
    recoveredCompatible dhat β := by
  classical
  obtain ⟨e, he⟩ := recoveredGroupEquiv d dhat r hcompat ε β hε hβ hmargin happrox
  have hsupp (m : Fin M) : recoveredSupport dhat β m =
      support r.v (r.κ m) := by
    rw [recoveredSupport_eq_of_margin d dhat ε β hε hβ hmargin happrox m]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, support]
    rw [r.decomp m]
    simp [r.c_ne m]
  constructor
  · intro m hempty
    have hzero : r.v (r.κ m) = 0 := by
      funext i
      have hi : i ∉ support r.v (r.κ m) := by rw [← hsupp m, hempty]; simp
      simpa [support] using hi
    exact (r.v_ne (r.κ m)) hzero
  · have hall : peelsAll (fun g => support r.v g) :=
      (assignment_nonempty_iff_peelsAll r.v).mp hcompat
    have heq : (fun h : {s : Finset (Fin p) //
      s ∈ Finset.univ.image (recoveredSupport dhat β)} => h.val) =
      (fun h => support r.v (e.symm h)) := by
      funext h
      have hh := he (e.symm h)
      rw [e.apply_symm_apply] at hh
      exact hh
    letI : Fintype {s : Finset (Fin p) //
      s ∈ Finset.univ.image (recoveredSupport dhat β)} :=
        Subtype.fintype (fun s => s ∈ Finset.univ.image (recoveredSupport dhat β))
    have htrans := (peelsAll_equiv e (fun g => support r.v g)).mpr hall
    simpa only [← heq] using htrans

/-- Frozen peeling commutes with a relabeling of support groups. -/
-- @node: frozenPeeling_equiv
theorem frozenPeeling_equiv {p : ℕ} {G H : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (S : G → Finset (Fin p)) (g : G) :
    frozenPeeling (fun h => S (e.symm h)) (e g) = frozenPeeling S g := by
  classical
  ext i
  simp only [frozenPeeling, Finset.mem_filter, e.symm_apply_apply]
  have hres := peelResidual_map_equiv e S (some g)
  simp only [Option.map_some] at hres
  rw [hres]
  constructor
  · rintro ⟨hi, hprivate⟩
    refine ⟨hi, ?_⟩
    intro h hh hne
    have hh' : e h ∈ (peelResidual S (some g)).map e.toEmbedding :=
      Finset.mem_map.mpr ⟨h, hh, rfl⟩
    simpa using hprivate (e h) hh' (by intro he; exact hne (e.injective he))
  · rintro ⟨hi, hprivate⟩
    refine ⟨hi, ?_⟩
    intro h hh hne
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hh
    simpa using hprivate k hk (by intro he; exact hne (congrArg e he))

/-- Exact support recovery makes the reported set the sharp marginal target set. -/
-- @node: noisyIncompleteHandle_eq_targetSet
theorem noisyIncompleteHandle_eq_targetSet {p M : ℕ}
    (d dhat : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (hcompat : (assignmentFiber r.v).Nonempty) (ε β : ℝ)
    (hε : 0 < ε) (hβ : 2 * ε < β)
    (hmargin : β ≤ supportMargin d)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ ε) (m : Fin M) :
    (↑(noisyIncompleteHandle dhat ε β m) : Set (Fin p)) =
      targetSet r.v (r.κ m) := by
  classical
  let T : Finset (Finset (Fin p)) := Finset.univ.image (recoveredSupport dhat β)
  let G := {s : Finset (Fin p) // s ∈ T}
  let S : G → Finset (Fin p) := Subtype.val
  let group : Fin M → G := fun k =>
    ⟨recoveredSupport dhat β k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩
  have hgood := recoveredCompatible_of_margin d dhat r hcompat ε β hε hβ hmargin happrox
  have hsupp (k : Fin M) : recoveredSupport dhat β k = support r.v (r.κ k) := by
    rw [recoveredSupport_eq_of_margin d dhat ε β hε hβ hmargin happrox k]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, support]
    rw [r.decomp k]
    simp [r.c_ne k]
  obtain ⟨e, he⟩ := recoveredGroupEquiv d dhat r hcompat ε β hε hβ hmargin happrox
  have hS : S = fun h => support r.v (e.symm h) := by
    funext h
    have hh := he (e.symm h)
    rw [e.apply_symm_apply] at hh
    exact hh
  have hgroup : group m = e (r.κ m) := by
    apply Subtype.ext
    exact (hsupp m).trans (he (r.κ m)).symm
  have hhandle : noisyIncompleteHandle dhat ε β m = frozenPeeling S (group m) := by
    unfold noisyIncompleteHandle
    dsimp [T, G, S, group]
    rw [if_pos hgood]
  have hpeel : frozenPeeling S (group m) =
      frozenPeeling (fun g => support r.v g) (r.κ m) := by
    rw [hS, hgroup]
    exact frozenPeeling_equiv e (fun g => support r.v g) (r.κ m)
  rw [hhandle, hpeel]
  exact (sharp_target_sets r.v hcompat).1 (r.κ m)

-- @node: costedFrozenPeeling_eq_frozenPeeling
theorem costedFrozenPeeling_eq_frozenPeeling {p : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (S : G → Finset (Fin p)) (g : G) :
    (costedFrozenPeeling S g).1 = frozenPeeling S g := by
  classical
  have hstate := incidencePeelRun_degree_correct S (some g) (Fintype.card G)
    (incidencePeelInit S (some g))
    (incidencePeelInit_degree_correct S (some g))
    (by intro h hh
        exact ((incidencePeelInit_queue_iff_deletable S (some g) h).mp hh).1)
  have hdegree := hstate.1
  have hgR := incidencePeelRun_frozen_mem S g (Fintype.card G)
  ext i
  simp only [costedFrozenPeeling, frozenPeeling, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hd⟩
    refine ⟨hi, ?_⟩
    have hp := (incidenceDegree_one_iff_private S
      (incidencePeelRun S (some g)) g hgR hdegree i hi).mp hd
    simpa only [incidencePeelRun_remaining_eq_peelResidual] using hp
  · rintro ⟨hi, hp⟩
    refine ⟨hi, ?_⟩
    apply (incidenceDegree_one_iff_private S
      (incidencePeelRun S (some g)) g hgR hdegree i hi).mpr
    simpa only [incidencePeelRun_remaining_eq_peelResidual] using hp

-- @node: costedNoisyIncompleteHandle_eq_of_margin
theorem costedNoisyIncompleteHandle_eq_of_margin {p M : ℕ}
    (d dhat : Fin M → Fin p → ℝ) (r : ProjectiveReduction d)
    (hcompat : (assignmentFiber r.v).Nonempty) (ε β : ℝ)
    (hε : 0 < ε) (hβ : 2 * ε < β)
    (hmargin : β ≤ supportMargin d)
    (happrox : ∀ m i, |dhat m i - d m i| ≤ ε) :
    (costedNoisyIncompleteHandle dhat ε β).1 =
      noisyIncompleteHandle dhat ε β := by
  classical
  let T : Finset (Finset (Fin p)) := Finset.univ.image (recoveredSupport dhat β)
  let G := {s : Finset (Fin p) // s ∈ T}
  let S : G → Finset (Fin p) := Subtype.val
  have hgood := recoveredCompatible_of_margin d dhat r hcompat ε β
    hε hβ hmargin happrox
  obtain ⟨e, he⟩ := recoveredGroupEquiv d dhat r hcompat ε β
    hε hβ hmargin happrox
  have hS : S = fun h => support r.v (e.symm h) := by
    funext h
    have hh := he (e.symm h)
    rw [e.apply_symm_apply] at hh
    exact hh
  have hall : peelsAll (fun g => support r.v g) :=
    (assignment_nonempty_iff_peelsAll r.v).mp hcompat
  have hpeel : peelsAll S := by
    rw [hS]
    exact (peelsAll_equiv e (fun g => support r.v g)).mpr hall
  have hbase : (incidencePeelRun S none).remaining = ∅ := by
    rw [incidencePeelRun_remaining_eq_peelResidual]
    exact hpeel
  have hc : (∀ m, recoveredSupport dhat β m ≠ ∅) ∧
      (incidencePeelRun S none).remaining = ∅ := ⟨hgood.1, hbase⟩
  funext m
  unfold costedNoisyIncompleteHandle noisyIncompleteHandle
  dsimp only
  split_ifs with hif
  · simpa only [Prod.fst] using
      (costedFrozenPeeling_eq_frozenPeeling S
        (⟨recoveredSupport dhat β m,
          Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩⟩ : G))
  · exact False.elim (hif hc)

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
