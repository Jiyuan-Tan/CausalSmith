module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.OrderedMass.Setwise

/-! # Ordered weakest-cell mass combinatorics -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory

/-- The minimum mass in a macro-cube is below each of its microcell masses. [For the stated inputs and conditions](hyp:d,P,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_cubeMass_le_microcellMass {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ) (k : Fin d → Fin (2 ^ j))
    (ℓ : Fin d → Fin (m + 1)) :
    cubeMass P m j k ≤ microcellMass P m j k ℓ := by
  unfold cubeMass
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨ℓ', rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨ℓ, rfl⟩

/-- A finite family of microcells contains one attaining the macro-cube minimum. [For the stated inputs and conditions](hyp:d,P,m,j,k), [the asserted conclusion holds](goal). -/
lemma orderedMass_cubeMass_attained {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ) (k : Fin d → Fin (2 ^ j)) :
    ∃ ℓ : Fin d → Fin (m + 1), cubeMass P m j k = microcellMass P m j k ℓ := by
  let S : Set ℝ := Set.range (fun ℓ : Fin d → Fin (m + 1) => microcellMass P m j k ℓ)
  have hS : S.Nonempty := by
    let ℓ : Fin d → Fin (m + 1) := fun _ => ⟨0, Nat.zero_lt_succ m⟩
    exact ⟨microcellMass P m j k ℓ, ℓ, rfl⟩
  have hfin : S.Finite := Set.finite_range _
  obtain ⟨ℓ, hℓ⟩ := Set.Nonempty.csInf_mem hS hfin
  exact ⟨ℓ, hℓ.symm⟩

/-- The setwise tail estimate gives a treated-mass bound for any measurable
microcell once its covariate mass has a lower bound. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ,a,Pc,μ₁,e,hmodel,hC,hγ,ha,E,hE,hmass), [the asserted conclusion holds](goal). -/
lemma orderedMass_microcell_lower {d : ℕ} (β B L C c_f γ a : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (hC : 1 ≤ C) (hγ : 1 < γ) (ha : 0 ≤ a)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E)
    (hmass : a ≤ (covariateLaw (Pc.map observed)).real E) :
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        a ^ (γ / (γ - 1)) ≤
      (Pc.map observed).real {z | z.2.1 = true ∧ z.1 ∈ E} := by
  have hexp : 0 ≤ γ / (γ - 1) := by positivity
  have hpow := Real.rpow_le_rpow ha hmass hexp
  have hcoeff : 0 ≤ ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) := by
    positivity
  exact (mul_le_mul_of_nonneg_left hpow hcoeff).trans
    (orderedMass_setwise_lower β B L C c_f γ Pc μ₁ e hmodel hC hγ E hE)

/-- The sharp setwise tail estimate applies to any finite union of selected
microcells, with covariate mass growing linearly in the number selected. [For the stated inputs and conditions](hyp:d,m,j,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,hC,hγ,hcf,S,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_selectedMicrocells_treated_lower (d m j : ℕ)
    (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (hC : 1 ≤ C) (hγ : 1 < γ) (hcf : 0 ≤ c_f)
    (S : Finset (Fin d → Fin (2 ^ j)))
    (ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1)) :
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        ((S.card : ℝ) * (c_f *
          (ENNReal.ofReal (templateEta d m * meshWidth j) ^ d).toReal)) ^
          (γ / (γ - 1)) ≤
      (Pc.map observed).real {z | z.2.1 = true ∧
        z.1 ∈ ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)} := by
  let E : Set (Fin d → ℝ) := ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)
  have hE : MeasurableSet E := by
    dsimp [E]
    apply Finset.measurableSet_biUnion
    intro k hk
    exact orderedMass_scaledMicroCell_measurable d m j k (ℓ k)
  have ha : 0 ≤ (S.card : ℝ) *
      (c_f * (ENNReal.ofReal (templateEta d m * meshWidth j) ^ d).toReal) := by
    positivity
  exact orderedMass_microcell_lower β B L C c_f γ _ Pc μ₁ e hmodel hC hγ ha
    E hE (orderedMass_selectedMicrocells_covariate_lower d m j β B L C c_f γ
      Pc μ₁ e hmodel S ℓ)

/-- Sorting the finite macro-cube masses retains exactly one entry per cube. [For the stated inputs and conditions](hyp:d,P,m,j), [the asserted conclusion holds](goal). -/
lemma orderedMass_sorted_length {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ) :
    (orderedCubeMass P m j).length = (2 ^ j) ^ d := by
  unfold orderedCubeMass
  simp only [List.length_mergeSort, List.length_map, Finset.length_toList,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- The ordered masses are monotone in their list indices. [For the stated inputs and conditions](hyp:d,P,m,j), [the asserted conclusion holds](goal). -/
lemma orderedMass_sorted_mono {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ) :
    (orderedCubeMass P m j).SortedLE := by
  unfold orderedCubeMass
  exact List.sortedLE_mergeSort

/-- Every in-range ordered mass is the minimum mass of a macro-cube. [For the stated inputs and conditions](hyp:d,P,m,j,k,hk,hk'), [the asserted conclusion holds](goal). -/
lemma orderedMass_rank_attained {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j k : ℕ)
    (hk : 1 ≤ k) (hk' : k ≤ (2 ^ j) ^ d) :
    ∃ q : Fin d → Fin (2 ^ j),
      (orderedCubeMass P m j).getD (k - 1) 0 = cubeMass P m j q := by
  classical
  let l := orderedCubeMass P m j
  have hi : k - 1 < l.length := by
    rw [orderedMass_sorted_length]
    omega
  rw [List.getD_eq_getElem l 0 hi]
  have hm : l[k - 1] ∈ l := List.getElem_mem hi
  have hm' : l[k - 1] ∈
      ((Finset.univ : Finset (Fin d → Fin (2 ^ j))).toList.map (cubeMass P m j)) := by
    exact (List.mergeSort_perm _ _).mem_iff.mp hm
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hm'
  exact ⟨q, hq.symm⟩

/-- Every earlier ordered mass is no larger than the mass at rank `k`. [For the stated inputs and conditions](hyp:d,P,m,j,i,k,hi,hk), [the asserted conclusion holds](goal). -/
lemma orderedMass_rank_mono {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j i k : ℕ)
    (hi : i < k) (hk : k ≤ (2 ^ j) ^ d) :
    (orderedCubeMass P m j).getD i 0 ≤
      (orderedCubeMass P m j).getD (k - 1) 0 := by
  let l := orderedCubeMass P m j
  have hik : i ≤ k - 1 := by omega
  have hil : i < l.length := by
    rw [orderedMass_sorted_length]
    omega
  have hkl : k - 1 < l.length := by
    rw [orderedMass_sorted_length]
    omega
  rw [List.getD_eq_getElem l 0 hil, List.getD_eq_getElem l 0 hkl]
  exact (orderedMass_sorted_mono P m j).getElem_le_getElem_of_le hik

/-- The total mass of the first `k` ordered macro-cubes is at most `k` times
the mass at rank `k`. [For the stated inputs and conditions](hyp:d,P,m,j,k,hk), [the asserted conclusion holds](goal). -/
lemma orderedMass_initial_sum_le_rank {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j k : ℕ)
    (hk : k ≤ (2 ^ j) ^ d) :
    (∑ i ∈ Finset.range k, (orderedCubeMass P m j).getD i 0) ≤
      (k : ℝ) * (orderedCubeMass P m j).getD (k - 1) 0 := by
  calc
    (∑ i ∈ Finset.range k, (orderedCubeMass P m j).getD i 0) ≤
        ∑ _i ∈ Finset.range k, (orderedCubeMass P m j).getD (k - 1) 0 := by
          apply Finset.sum_le_sum
          intro i hi
          exact orderedMass_rank_mono P m j i k (Finset.mem_range.mp hi) hk
    _ = (k : ℝ) * (orderedCubeMass P m j).getD (k - 1) 0 := by
      simp

/-- At least `k` macro-cubes have weakest-microcell mass at most the mass at
rank `k`, counting ties with their multiplicity. [For the stated inputs and conditions](hyp:d,P,m,j,k,hk), [the asserted conclusion holds](goal). -/
lemma orderedMass_rank_threshold_card {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j k : ℕ)
    (hk : k ≤ (2 ^ j) ^ d) :
    k ≤ ((Finset.univ : Finset (Fin d → Fin (2 ^ j))).filter
      (fun q => cubeMass P m j q ≤ (orderedCubeMass P m j).getD (k - 1) 0)).card := by
  classical
  let rank := (orderedCubeMass P m j).getD (k - 1) 0
  let l := orderedCubeMass P m j
  let original := (Finset.univ : Finset (Fin d → Fin (2 ^ j))).toList.map (cubeMass P m j)
  have hlen : k ≤ l.length := by simpa [l, orderedMass_sorted_length] using hk
  have hprefix : ∀ x ∈ l.take k, x ≤ rank := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hik : i < k := by simpa using (lt_of_lt_of_le hi (List.length_take_le k l))
    have hil : i < l.length := lt_of_lt_of_le hik hlen
    simpa only [List.getElem_take, l, rank, List.getD_eq_getElem l 0 hil] using
      orderedMass_rank_mono P m j i k hik hk
  have hcount : k ≤ l.countP (fun x => x ≤ rank) := by
    have hsub : (l.take k).countP (fun x => x ≤ rank) ≤
        l.countP (fun x => x ≤ rank) := (List.take_sublist k l).countP_le
    have hall : (l.take k).countP (fun x => x ≤ rank) = k := by
      rw [List.countP_eq_length_filter]
      have hfilter : (l.take k).filter (fun x => x ≤ rank) = l.take k := by
        apply List.filter_eq_self.mpr
        simpa using hprefix
      rw [hfilter, List.length_take, min_eq_left hlen]
    omega
  have hperm : l.Perm original := by
    dsimp [l, original, orderedCubeMass]
    exact List.mergeSort_perm _ _
  have hcount' : k ≤ original.countP (fun x => x ≤ rank) := by
    rwa [hperm.countP_eq] at hcount
  have hmap : original.countP (fun x => x ≤ rank) =
      ((Finset.univ : Finset (Fin d → Fin (2 ^ j))).toList).countP
        (fun q => cubeMass P m j q ≤ rank) := by
    simp only [original, List.countP_map, Function.comp_def]
  rw [hmap] at hcount'
  have hnodup : ((Finset.univ : Finset (Fin d → Fin (2 ^ j))).toList).Nodup :=
    Finset.nodup_toList _
  simpa [rank] using hcount'.trans_eq
    (List.Nodup.card_eq_countP hnodup).symm

/-- A finite union of selected treated microcells has mass at most the sum
of its component treated masses. [For the stated inputs and conditions](hyp:d,P,m,j,S,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_selectedMicrocells_treated_upper {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j : ℕ)
    (S : Finset (Fin d → Fin (2 ^ j)))
    (ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1)) :
    P.real {z | z.2.1 = true ∧
      z.1 ∈ ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)} ≤
      ∑ k ∈ S, microcellMass P m j k (ℓ k) := by
  let E : (Fin d → Fin (2 ^ j)) → Set (Obs d) :=
    fun k => {z | z.2.1 = true ∧ z.1 ∈ scaledMicroCell d m j k (ℓ k)}
  have heq : {z | z.2.1 = true ∧
      z.1 ∈ ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)} = ⋃ k ∈ S, E k := by
    ext z
    simp [E]
  rw [heq]
  calc
    P.real (⋃ k ∈ S, E k) ≤ (∑ k ∈ S, P (E k)).toReal := by
      exact ENNReal.toReal_mono (by simp)
        (measure_biUnion_finset_le S E)
    _ = ∑ k ∈ S, microcellMass P m j k (ℓ k) := by
      rw [ENNReal.toReal_sum (by intro k hk; exact measure_ne_top _ _)]
      rfl

/-- Selecting a minimizing microcell in each cube bounds the mass of their
union by the number of cubes times any common upper bound on the minima. [For the stated inputs and conditions](hyp:d,P,m,j,S,ℓ,r,hmin,hr), [the asserted conclusion holds](goal). -/
lemma orderedMass_selectedMicrocells_treated_le_card_mul {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (m j : ℕ)
    (S : Finset (Fin d → Fin (2 ^ j)))
    (ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1)) (r : ℝ)
    (hmin : ∀ k ∈ S, microcellMass P m j k (ℓ k) = cubeMass P m j k)
    (hr : ∀ k ∈ S, cubeMass P m j k ≤ r) :
    P.real {z | z.2.1 = true ∧
      z.1 ∈ ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)} ≤
        (S.card : ℝ) * r := by
  calc
    P.real {z | z.2.1 = true ∧
        z.1 ∈ ⋃ k ∈ S, scaledMicroCell d m j k (ℓ k)} ≤
      ∑ k ∈ S, microcellMass P m j k (ℓ k) :=
        orderedMass_selectedMicrocells_treated_upper P m j S ℓ
    _ ≤ ∑ _k ∈ S, r := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hmin k hk]
      exact hr k hk
    _ = (S.card : ℝ) * r := by simp

/-- Choose exactly the first `k` weakest macro-cubes (breaking ties arbitrarily)
and one mass-minimizing microcell in each of them. [For the stated inputs and conditions](hyp:d,P,m,j,k,hk), [the asserted conclusion holds](goal). -/
lemma orderedMass_choose_ranked_minimizers {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j k : ℕ)
    (hk : k ≤ (2 ^ j) ^ d) :
    ∃ S : Finset (Fin d → Fin (2 ^ j)), S.card = k ∧
      ∃ ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1),
        (∀ q ∈ S, microcellMass P m j q (ℓ q) = cubeMass P m j q) ∧
        (∀ q ∈ S, cubeMass P m j q ≤
          (orderedCubeMass P m j).getD (k - 1) 0) := by
  classical
  let F := (Finset.univ : Finset (Fin d → Fin (2 ^ j))).filter
    (fun q => cubeMass P m j q ≤ (orderedCubeMass P m j).getD (k - 1) 0)
  obtain ⟨S, hSF, hS⟩ := Finset.exists_subset_card_eq
    (orderedMass_rank_threshold_card P m j k hk : k ≤ F.card)
  have hchoice : ∀ q : Fin d → Fin (2 ^ j),
      ∃ ℓ : Fin d → Fin (m + 1),
        cubeMass P m j q = microcellMass P m j q ℓ :=
    fun q => orderedMass_cubeMass_attained P m j q
  choose ℓ hℓ using hchoice
  refine ⟨S, hS, ℓ, ?_, ?_⟩
  · intro q hq
    exact (hℓ q).symm
  · intro q hq
    exact Finset.mem_filter.mp (hSF hq) |>.2

/-- The treated mass of `k` selected weakest microcells is at most `k`
times the `k`th weakest macro-cube mass. [For the stated inputs and conditions](hyp:d,P,m,j,k,hk), [the asserted conclusion holds](goal). -/
lemma orderedMass_ranked_union_upper {d : ℕ} (P : Measure (Obs d))
    [IsProbabilityMeasure P] (m j k : ℕ)
    (hk : k ≤ (2 ^ j) ^ d) :
    ∃ (S : Finset (Fin d → Fin (2 ^ j)))
      (ℓ : (Fin d → Fin (2 ^ j)) → Fin d → Fin (m + 1)),
      S.card = k ∧
      P.real {z | z.2.1 = true ∧
        z.1 ∈ ⋃ q ∈ S, scaledMicroCell d m j q (ℓ q)} ≤
        (k : ℝ) * (orderedCubeMass P m j).getD (k - 1) 0 := by
  obtain ⟨S, hS, ℓ, hmin, hr⟩ :=
    orderedMass_choose_ranked_minimizers P m j k hk
  refine ⟨S, ℓ, hS, ?_⟩
  simpa only [hS] using
    orderedMass_selectedMicrocells_treated_le_card_mul P m j S ℓ
      ((orderedCubeMass P m j).getD (k - 1) 0) hmin hr

end CausalSmith.Stat.WeakOverlap
