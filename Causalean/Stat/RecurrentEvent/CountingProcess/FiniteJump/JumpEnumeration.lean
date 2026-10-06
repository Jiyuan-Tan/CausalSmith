module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.Basic

/-!
# Measurable enumeration of finite counting-process jumps

The count process determines each ordered event time as a threshold-hitting time.
This supplies a countable representation of the random finite jump sum, even
though measurability of a finite set under its membership σ-algebra alone does
not give measurability of its cardinality or of arbitrary weighted sums.
-/

@[expose] public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The `k`th jump time is the first time by which at least `k + 1` events
have occurred. The value for an index beyond the last event is irrelevant. -/
noncomputable def Model.jumpTime (M : Model Ω μ) (k : ℕ) (ω : Ω) : ℝ :=
  sInf {t : ℝ | k + 1 ≤ M.count t ω}

/-- The number of events by the horizon is measurable under the ambient
sample σ-algebra, as a consequence of adaptedness of the count process. -/
theorem Model.measurable_eventCard (M : Model Ω μ) :
    Measurable (fun ω => (M.eventTimes ω).card) := by
  have hEq : (fun ω => (M.eventTimes ω).card) = M.count M.horizon := by
    funext ω
    classical
    change (M.eventTimes ω).card =
      ((M.eventTimes ω).filter (fun t => t ≤ M.horizon)).card
    congr 1
    exact (Finset.filter_eq_self.mpr
      (fun t ht => (M.events_in_horizon ω t ht).2)).symm
  rw [hEq]
  exact (M.count_adapted M.horizon).mono
    (M.filtration_le M.horizon) le_rfl

private theorem Model.jumpTime_event (M : Model Ω μ) (k : ℕ) (ω : Ω)
    (hk : k < (M.eventTimes ω).card) :
    M.jumpTime k ω ∈ M.eventTimes ω ∧
      k + 1 ≤ M.count (M.jumpTime k ω) ω := by
  classical
  let s := M.eventTimes ω
  let c : ℝ → ℕ := fun t => (s.filter (· ≤ t)).card
  let e := s.filter (fun t => k + 1 ≤ c t)
  have hc_mono : Monotone c := by
    intro a b hab
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
      le_trans (Finset.mem_filter.mp hx).2 hab⟩
  have he : e.Nonempty := by
    have hcard : k < s.card := hk
    have hs : s.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨s.max' hs, Finset.mem_filter.mpr ⟨s.max'_mem hs, ?_⟩⟩
    have hc : c (s.max' hs) = s.card := by
      have hf : s.filter (· ≤ s.max' hs) = s :=
        Finset.filter_eq_self.mpr (by intro t ht; exact Finset.le_max' s t ht)
      simp [c, hf]
    omega
  let x := e.min' he
  have hx : x ∈ s := (Finset.mem_filter.mp (e.min'_mem he)).1
  have hxc : k + 1 ≤ c x := (Finset.mem_filter.mp (e.min'_mem he)).2
  have hleast : ∀ t, k + 1 ≤ c t → x ≤ t := by
    intro t ht
    have hft : (s.filter (· ≤ t)).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < c t
      omega
    let y := (s.filter (· ≤ t)).max' hft
    have hy : y ∈ s := (Finset.mem_filter.mp ((s.filter (· ≤ t)).max'_mem hft)).1
    have hyt : y ≤ t := (Finset.mem_filter.mp ((s.filter (· ≤ t)).max'_mem hft)).2
    have hcy : c y = c t := by
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro z hz
      constructor
      · exact fun h => le_trans h hyt
      · intro h
        exact Finset.le_max' (s.filter (· ≤ t)) z (Finset.mem_filter.mpr ⟨hz, h⟩)
    have hye : y ∈ e := Finset.mem_filter.mpr ⟨hy, by omega⟩
    exact le_trans (Finset.min'_le e y hye) hyt
  have hclosed : IsLeast {t : ℝ | k + 1 ≤ c t} x :=
    ⟨hxc, hleast⟩
  have hInf : sInf {t : ℝ | k + 1 ≤ c t} = x := hclosed.csInf_eq
  constructor
  · simpa [Model.jumpTime, Model.count, c, s] using hInf.symm ▸ hx
  · simpa [Model.jumpTime, Model.count, c, s] using hInf.symm ▸ hxc

/-- Every in-range jump-time threshold is an event time in the finite path. -/
theorem Model.jumpTime_mem (M : Model Ω μ) (k : ℕ) (ω : Ω)
    (hk : k < (M.eventTimes ω).card) :
    M.jumpTime k ω ∈ M.eventTimes ω :=
  (M.jumpTime_event k ω hk).1

private theorem Model.count_jumpTime (M : Model Ω μ) (k : ℕ) (ω : Ω)
    (hk : k < (M.eventTimes ω).card) :
    M.count (M.jumpTime k ω) ω = k + 1 := by
  classical
  let s := M.eventTimes ω
  let x := M.jumpTime k ω
  have hx : x ∈ s := M.jumpTime_mem k ω hk
  have hbelow : BddBelow {t : ℝ | k + 1 ≤ M.count t ω} := by
    refine ⟨0, ?_⟩
    intro t ht
    change k + 1 ≤ M.count t ω at ht
    have hne : (s.filter (· ≤ t)).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < M.count t ω
      omega
    obtain ⟨y, hy⟩ := hne
    exact le_trans (le_of_lt (M.events_in_horizon ω y (Finset.mem_filter.mp hy).1).1)
      (Finset.mem_filter.mp hy).2
  have hthreshold : k + 1 ≤ M.count x ω := (M.jumpTime_event k ω hk).2
  have hfilter : s.filter (· ≤ x) = insert x (s.filter (· < x)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le h.2 with hlt | heq
      · exact Or.inr ⟨h.1, hlt⟩
      · exact Or.inl heq
    · rintro (rfl | ⟨hy, hlt⟩)
      · exact ⟨hx, le_rfl⟩
      · exact ⟨hy, le_of_lt hlt⟩
  have hcount : M.count x ω = (s.filter (· < x)).card + 1 := by
    change (s.filter (· ≤ x)).card = _
    rw [hfilter, Finset.card_insert_of_notMem (by simp)]
  by_contra hn
  change M.count x ω ≠ k + 1 at hn
  have hmore : k + 1 ≤ (s.filter (· < x)).card := by omega
  have hne : (s.filter (· < x)).Nonempty := Finset.card_pos.mp (by omega)
  let y := (s.filter (· < x)).max' hne
  have hy : y < x := (Finset.mem_filter.mp ((s.filter (· < x)).max'_mem hne)).2
  have hfy : s.filter (· ≤ y) = s.filter (· < x) := by
    apply Finset.filter_congr
    intro z hz
    constructor
    · intro h
      exact lt_of_le_of_lt h hy
    · intro h
      exact Finset.le_max' (s.filter (· < x)) z (Finset.mem_filter.mpr ⟨hz, h⟩)
  have hcy : k + 1 ≤ M.count y ω := by
    change k + 1 ≤ (s.filter (· ≤ y)).card
    rw [hfy]
    exact hmore
  have hxy : x ≤ y := by
    change sInf {t : ℝ | k + 1 ≤ M.count t ω} ≤ y
    exact csInf_le hbelow hcy
  exact (not_le_of_gt hy) hxy

/-- Distinct in-range threshold indices identify distinct event times. -/
theorem Model.jumpTime_injective (M : Model Ω μ) (ω : Ω)
    (i j : ℕ) (hi : i < (M.eventTimes ω).card)
    (hj : j < (M.eventTimes ω).card)
    (hij : M.jumpTime i ω = M.jumpTime j ω) : i = j := by
  have hci := M.count_jumpTime i ω hi
  have hcj := M.count_jumpTime j ω hj
  rw [hij] at hci
  omega

/-- A finite jump sum is the sum over the ordered threshold times below the
event count. This is the pathwise enumeration used for measurability. [The
model, payoff, and path](hyp:M,H,ω) give [the ordered-jump representation](goal). -/
theorem Model.jumpIntegral_eq_sum_jumpTime (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (ω : Ω) :
    M.jumpIntegral H M.horizon ω =
      ∑ k ∈ Finset.range (M.eventTimes ω).card, H (M.jumpTime k ω) ω := by
  classical
  let s := M.eventTimes ω
  have hfilter : s.filter (· ≤ M.horizon) = s :=
    Finset.filter_eq_self.mpr (fun t ht => (M.events_in_horizon ω t ht).2)
  have hsub : (Finset.range s.card).image (fun k => M.jumpTime k ω) ⊆ s := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact M.jumpTime_mem k ω (Finset.mem_range.mp hk)
  have hinj : Set.InjOn (fun k => M.jumpTime k ω) (Finset.range s.card) := by
    intro i hi j hj hij
    exact M.jumpTime_injective ω i j (Finset.mem_range.mp hi)
      (Finset.mem_range.mp hj) hij
  have himage : (Finset.range s.card).image (fun k => M.jumpTime k ω) = s := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  change (∑ t ∈ s.filter (· ≤ M.horizon), H t ω) = _
  rw [hfilter, ← himage, Finset.sum_image hinj]

private theorem Model.jumpTime_eq_zero_of_card_le (M : Model Ω μ) (k : ℕ)
    (ω : Ω) (hk : (M.eventTimes ω).card ≤ k) : M.jumpTime k ω = 0 := by
  have hempty : {t : ℝ | k + 1 ≤ M.count t ω} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    have hle : M.count t ω ≤ (M.eventTimes ω).card :=
      Finset.card_filter_le _ _
    omega
  change sInf {t : ℝ | k + 1 ≤ M.count t ω} = 0
  rw [hempty]
  simp

private theorem Model.jumpTime_le_of_count (M : Model Ω μ) (k : ℕ)
    (ω : Ω) (t : ℝ) (ht : k + 1 ≤ M.count t ω) :
    M.jumpTime k ω ≤ t := by
  have hbelow : BddBelow {u : ℝ | k + 1 ≤ M.count u ω} := by
    refine ⟨0, ?_⟩
    intro u hu
    change k + 1 ≤ M.count u ω at hu
    have hne : ((M.eventTimes ω).filter (· ≤ u)).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < M.count u ω
      omega
    obtain ⟨v, hv⟩ := hne
    exact le_trans (le_of_lt (M.events_in_horizon ω v (Finset.mem_filter.mp hv).1).1)
      (Finset.mem_filter.mp hv).2
  exact csInf_le hbelow ht

/-- Each ordered event time is measurable because all count thresholds at
fixed times are measurable with respect to the ambient sample σ-algebra. -/
theorem Model.measurable_jumpTime (M : Model Ω μ) (k : ℕ) :
    Measurable (M.jumpTime k) := by
  apply measurable_of_Iio
  intro a
  have hset : (M.jumpTime k) ⁻¹' Iio a =
      ({ω | (M.eventTimes ω).card ≤ k} ∩ {ω | (0 : ℝ) < a}) ∪
        ⋃ q : ℚ, {ω | (q : ℝ) < a ∧ k + 1 ≤ M.count q ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_inter,
      Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      by_cases hk : (M.eventTimes ω).card ≤ k
      · left
        exact ⟨hk, by simpa [M.jumpTime_eq_zero_of_card_le k ω hk] using h⟩
      · right
        have hki : k < (M.eventTimes ω).card := by omega
        obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn h
        refine ⟨q, hqhi, ?_⟩
        have hcount := (M.jumpTime_event k ω hki).2
        have hmono : M.count (M.jumpTime k ω) ω ≤ M.count q ω := by
          unfold Model.count
          apply Finset.card_le_card
          intro v hv
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,
            le_trans (Finset.mem_filter.mp hv).2 (le_of_lt hqlo)⟩
        omega
    · rintro (⟨hk, ha⟩ | ⟨q, hqa, hq⟩)
      · simpa [M.jumpTime_eq_zero_of_card_le k ω hk] using ha
      · exact lt_of_le_of_lt (M.jumpTime_le_of_count k ω q hq) hqa
  rw [hset]
  apply MeasurableSet.union
  · have ha : MeasurableSet {ω : Ω | (0 : ℝ) < a} := by
      by_cases h : (0 : ℝ) < a
      · simpa [h] using (measurableSet_univ : MeasurableSet (Set.univ : Set Ω))
      · simpa [h] using (measurableSet_empty : MeasurableSet (∅ : Set Ω))
    exact (M.measurable_eventCard measurableSet_Iic).inter ha
  · apply MeasurableSet.iUnion
    intro q
    have hc : Measurable (M.count q) :=
      (M.count_adapted q).mono (M.filtration_le q) le_rfl
    have ha : MeasurableSet {ω : Ω | (q : ℝ) < a} := by
      by_cases h : (q : ℝ) < a
      · simpa [h] using (measurableSet_univ : MeasurableSet (Set.univ : Set Ω))
      · simpa [h] using (measurableSet_empty : MeasurableSet (∅ : Set Ω))
    exact ha.inter (hc measurableSet_Ici)

/-- Joint measurability of a payoff makes its sum over a random finite event
set measurable when the count process is adapted. -/
theorem Model.measurable_jumpIntegral (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : Measurable (fun p : ℝ × Ω => H p.1 p.2)) :
    Measurable (M.jumpIntegral H M.horizon) := by
  have hterm (k : ℕ) : Measurable (fun ω => H (M.jumpTime k ω) ω) := by
    exact hH.comp ((M.measurable_jumpTime k).prodMk measurable_id)
  have hsum (n : ℕ) :
      Measurable (fun ω => ∑ k ∈ Finset.range n, H (M.jumpTime k ω) ω) := by
    exact Finset.measurable_sum _ (fun k _ => hterm k)
  have hcard := M.measurable_eventCard
  apply measurable_of_Iio
  intro a
  have hset : (M.jumpIntegral H M.horizon) ⁻¹' Iio a =
      ⋃ n : ℕ, {ω | (M.eventTimes ω).card = n} ∩
        (fun ω => ∑ k ∈ Finset.range n, H (M.jumpTime k ω) ω) ⁻¹' Iio a := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_inter,
      Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨(M.eventTimes ω).card, rfl, ?_⟩
      change (∑ k ∈ Finset.range (M.eventTimes ω).card,
        H (M.jumpTime k ω) ω) < a
      rwa [M.jumpIntegral_eq_sum_jumpTime H ω] at h
    · rintro ⟨n, hn, h⟩
      change (∑ k ∈ Finset.range n, H (M.jumpTime k ω) ω) < a at h
      change M.jumpIntegral H M.horizon ω < a
      rw [M.jumpIntegral_eq_sum_jumpTime H ω, hn]
      exact h
  rw [hset]
  apply MeasurableSet.iUnion
  intro n
  exact (hcard (measurableSet_singleton n)).inter (hsum n measurableSet_Iio)

/-- Joint measurability of the payoff makes its pathwise integral against the
jointly measurable at-risk intensity measurable in the sample. -/
theorem Model.measurable_energyIntegral (M : Model Ω μ) (H : ℝ → Ω → ℝ)
    (hH : Measurable (fun p : ℝ × Ω => H p.1 p.2)) :
    Measurable (M.energyIntegral H M.horizon) := by
  have hf : Measurable (fun p : ℝ × Ω =>
      H p.1 p.2 * (M.atRisk p.1 p.2 * M.intensity p.1 p.2)) :=
    hH.mul (M.atRisk_joint_measurable.mul M.intensity_joint_measurable)
  have hi := (hf.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc 0 M.horizon))).measurable
  exact hi

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
