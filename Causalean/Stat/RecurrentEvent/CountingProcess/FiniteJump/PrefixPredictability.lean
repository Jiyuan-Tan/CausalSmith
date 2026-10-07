module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.BoundedRegularity

/-!
# Predictability of the two strict-past integral components

Separate the finite weighted jump prefix from the time integral. These are
filtration measurability obligations; neither uses compensation or L² moments.
Their difference is the prefix used in the square and cross-product expansions.
-/

public section

open MeasureTheory Set

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A time interval paired with the whole sample space is predictable. -/
private theorem Model.predictableSet_Ioc_univ (M : Model Ω μ) (a b : ℝ) :
    MeasurableSet[predictableSpace M.filtration] (Ioc a b ×ˢ (univ : Set Ω)) := by
  exact MeasurableSpace.measurableSet_generateFrom ⟨a, b, univ, MeasurableSet.univ, rfl⟩

/-- The time coordinate is measurable for the predictable σ-algebra. -/
private theorem Model.predictable_measurable_time (M : Model Ω μ) :
    Measurable[predictableSpace M.filtration] (Prod.fst : ℝ × Ω → ℝ) := by
  let : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
  change @Measurable _ _ (predictableSpace M.filtration) (borel ℝ) Prod.fst
  rw [borel_eq_generateFrom_Ioc ℝ]
  apply measurable_generateFrom
  rintro S ⟨a, b, hab, rfl⟩
  have heq : Prod.fst ⁻¹' Ioc a b = Ioc a b ×ˢ (univ : Set Ω) := by
    ext p
    simp
  rw [heq]
  exact M.predictableSet_Ioc_univ a b

/-- An observation available at a fixed time can be used at any later time. -/
private theorem Model.predictableSet_Ioi (M : Model Ω μ) (a : ℝ)
    (B : Set Ω) (hB : MeasurableSet[M.filtration a] B) :
    MeasurableSet[predictableSpace M.filtration] (Ioi a ×ˢ B) := by
  have heq : Ioi a ×ˢ B = ⋃ n : ℕ, Ioc a (n : ℝ) ×ˢ B := by
    ext p
    simp only [mem_prod, mem_Ioi, mem_Ioc, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge p.1
      exact ⟨n, ⟨h.1, hn⟩, h.2⟩
    · rintro ⟨n, ⟨ha, hn⟩, hB⟩
      exact ⟨ha, hB⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun n =>
    MeasurableSpace.measurableSet_generateFrom ⟨a, n, B, hB, rfl⟩)

/-- Moving the time coordinate backwards preserves predictable measurability
when the earlier time is supplied as a separate Borel parameter. -/
private theorem Model.predictable_measurable_min (M : Model Ω μ) :
    @Measurable ((ℝ × Ω) × ℝ) (ℝ × Ω)
      ((predictableSpace M.filtration).prod inferInstance)
      (predictableSpace M.filtration)
      (fun q => (min q.2 q.1.1, q.1.2)) := by
  let : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
  have ht : Measurable (fun q : (ℝ × Ω) × ℝ => q.1.1) :=
    M.predictable_measurable_time.comp measurable_fst
  apply measurable_generateFrom
  rintro S ⟨a, b, B, hB, rfl⟩
  have heq : (fun q : (ℝ × Ω) × ℝ => (min q.2 q.1.1, q.1.2)) ⁻¹'
      (Ioc a b ×ˢ B) =
      {q | a < q.2} ∩ ({q | q.2 ≤ b} ∪ {q | q.1.1 ≤ b}) ∩
        Prod.fst ⁻¹' (Ioi a ×ˢ B) := by
    ext q
    simp only [mem_preimage, mem_prod, mem_Ioc, lt_min_iff, min_le_iff,
      mem_inter_iff, mem_union, mem_ofPred_eq, mem_Ioi]
    tauto
  rw [heq]
  exact ((measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_const).union
      (measurableSet_le ht measurable_const))).inter
      ((M.predictableSet_Ioi a B hB).preimage measurable_fst)

/-- Event counts increase with time. -/
private theorem Model.count_mono_time (M : Model Ω μ) (ω : Ω) :
    Monotone (fun t => M.count t ω) := by
  intro a b hab
  apply Finset.card_le_card
  intro s hs
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1,
    (Finset.mem_filter.mp hs).2.trans hab⟩

/-- An in-range event time is the least time reaching its count threshold. -/
private theorem Model.jumpTime_isLeast (M : Model Ω μ) (k : ℕ) (ω : Ω)
    (hk : k < (M.eventTimes ω).card) :
    IsLeast {t : ℝ | k + 1 ≤ M.count t ω} (M.jumpTime k ω) := by
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
  simpa only [Model.jumpTime, Model.count, c, s, hInf] using hclosed

/-- A count threshold characterizes an in-range event time. -/
private theorem Model.jumpTime_le_iff_threshold (M : Model Ω μ) (k : ℕ) (ω : Ω)
    (hk : k < (M.eventTimes ω).card) (a : ℝ) :
    M.jumpTime k ω ≤ a ↔ k + 1 ≤ M.count a ω := by
  constructor
  · intro ha
    exact (M.jumpTime_isLeast k ω hk).1.trans (M.count_mono_time ω ha)
  · intro ha
    exact (M.jumpTime_isLeast k ω hk).2 ha

/-- Having already seen the indexed jump is a predictable event. -/
private theorem Model.predictableSet_jumpTime_lt (M : Model Ω μ) (k : ℕ) :
    MeasurableSet[predictableSpace M.filtration]
      {p : ℝ × Ω | k < (M.eventTimes p.2).card ∧ M.jumpTime k p.2 < p.1} := by
  have heq : {p : ℝ × Ω | k < (M.eventTimes p.2).card ∧ M.jumpTime k p.2 < p.1} =
      ⋃ q : ℚ, Ioi (q : ℝ) ×ˢ {ω | k + 1 ≤ M.count q ω} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_Ioi]
    constructor
    · rintro ⟨hk, ht⟩
      obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn ht
      exact ⟨q, hqhi, (M.jumpTime_le_iff_threshold k p.2 hk q).mp hqlo.le⟩
    · rintro ⟨q, hqt, hqc⟩
      have hk : k < (M.eventTimes p.2).card := by
        have hc : M.count q p.2 ≤ (M.eventTimes p.2).card :=
          Finset.card_filter_le _ _
        omega
      exact ⟨hk, lt_of_le_of_lt
        ((M.jumpTime_le_iff_threshold k p.2 hk q).mpr hqc) hqt⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun q => M.predictableSet_Ioi q _
    (M.count_adapted q measurableSet_Ici))

/-- Evaluating an already observed indexed jump preserves predictable
measurability; unobserved indices use the current time instead. -/
private theorem Model.predictable_measurable_pastJump (M : Model Ω μ) (k : ℕ) :
    @Measurable (ℝ × Ω) (ℝ × Ω) (predictableSpace M.filtration)
      (predictableSpace M.filtration)
      (fun p => if k < (M.eventTimes p.2).card ∧ M.jumpTime k p.2 < p.1
        then (M.jumpTime k p.2, p.2) else p) := by
  classical
  let : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
  let D : Set (ℝ × Ω) :=
    {p | k < (M.eventTimes p.2).card ∧ M.jumpTime k p.2 < p.1}
  have hD : MeasurableSet D := M.predictableSet_jumpTime_lt k
  apply measurable_generateFrom
  rintro S ⟨a, b, B, hB, rfl⟩
  have heq : (fun p : ℝ × Ω => if p ∈ D then (M.jumpTime k p.2, p.2) else p) ⁻¹'
      (Ioc a b ×ˢ B) =
      (D ∩ (Ioi a ×ˢ ({ω | M.count a ω ≤ k} ∩ B)) ∩
        (Prod.fst ⁻¹' Iic b ∪ (Ioi b ×ˢ {ω | k + 1 ≤ M.count b ω}))) ∪
        (Dᶜ ∩ (Ioc a b ×ˢ B)) := by
    ext p
    by_cases hp : p ∈ D
    · have hk := hp.1
      have ha := M.jumpTime_le_iff_threshold k p.2 hk a
      have hb := M.jumpTime_le_iff_threshold k p.2 hk b
      simp only [mem_preimage, mem_prod, mem_Ioc, mem_union,
        mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_Iic, mem_compl_iff, hp,
        true_and, not_true_eq_false, false_and, or_false]
      constructor
      · rintro ⟨⟨haj, hjb⟩, hpB⟩
        refine ⟨⟨lt_trans haj hp.2, ?_, hpB⟩, ?_⟩
        · have hn : ¬ k + 1 ≤ M.count a p.2 := by
            intro hc
            exact not_le_of_gt haj (ha.mpr hc)
          omega
        · by_cases htb : p.1 ≤ b
          · exact Or.inl htb
          · exact Or.inr ⟨lt_of_not_ge htb, hb.mp hjb⟩
      · rintro ⟨⟨hat, hca, hpB⟩, hbt | ⟨hbt, hcb⟩⟩
        · refine ⟨⟨?_, hp.2.le.trans hbt⟩, hpB⟩
          by_contra hn
          have hc := ha.mp (le_of_not_gt hn)
          omega
        · refine ⟨⟨?_, hb.mpr hcb⟩, hpB⟩
          by_contra hn
          have hc := ha.mp (le_of_not_gt hn)
          omega
    · simp [hp]
  change MeasurableSet ((fun p : ℝ × Ω =>
    if p ∈ D then (M.jumpTime k p.2, p.2) else p) ⁻¹' (Ioc a b ×ˢ B))
  rw [heq]
  exact ((hD.inter (M.predictableSet_Ioi a _
    ((M.count_adapted a measurableSet_Iic).inter hB))).inter
      ((M.predictable_measurable_time measurableSet_Iic).union
        (M.predictableSet_Ioi b _ (M.count_adapted b measurableSet_Ici)))).union
    (hD.compl.inter (MeasurableSpace.measurableSet_generateFrom ⟨a, b, B, hB, rfl⟩))

/-- The sum of a predictable payoff over events strictly before
the current time is a predictable process. [The model and payoff](hyp:M,H)
and [predictability](hyp:hH) give [predictability
of the strict-past event sum](goal). -/
theorem Model.predictable_strictJumpIntegral (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H) :
    M.Predictable (fun t ω =>
      ∑ s ∈ (M.eventTimes ω).filter (fun s => s < t), H s ω) := by
  classical
  let : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
  let F : ℕ → (ℝ × Ω) → ℝ := fun k p =>
    if k < (M.eventTimes p.2).card ∧ M.jumpTime k p.2 < p.1
    then H (M.jumpTime k p.2) p.2 else 0
  have hF (k : ℕ) : Measurable (F k) := by
    have hg := hH.comp (M.predictable_measurable_pastJump k)
    have hi := hg.indicator (M.predictableSet_jumpTime_lt k)
    convert hi using 1
    funext p
    by_cases hp : k < (M.eventTimes p.2).card ∧ M.jumpTime k p.2 < p.1 <;>
      simp [F, Set.indicator, hp]
  -- Finite sums of already observed jumps are left-continuous adapted time
  -- steps. Their measurability follows directly from the predictable cylinders;
  -- on each finite path the approximations eventually equal the strict prefix.
  have hsum (n : ℕ) : Measurable (fun p => ∑ k ∈ Finset.range n, F k p) :=
    Finset.measurable_sum _ (fun k _ => hF k)
  have hrepr (p : ℝ × Ω) :
      (∑ s ∈ (M.eventTimes p.2).filter (fun s => s < p.1), H s p.2) =
        ∑ k ∈ Finset.range (M.eventTimes p.2).card, F k p := by
    have he := M.jumpIntegral_eq_sum_jumpTime
      (fun s ω => if s < p.1 then H s ω else 0) p.2
    have hfilter : (M.eventTimes p.2).filter (fun s => s ≤ M.horizon) =
        M.eventTimes p.2 := Finset.filter_eq_self.mpr
      (fun s hs => (M.events_in_horizon p.2 s hs).2)
    rw [Model.jumpIntegral, hfilter, ← Finset.sum_filter] at he
    rw [he]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [F, Finset.mem_range.mp hk, true_and]
  change Measurable (fun p : ℝ × Ω =>
    ∑ s ∈ (M.eventTimes p.2).filter (fun s => s < p.1), H s p.2)
  apply measurable_of_tendsto_metrizable hsum
  apply tendsto_pi_nhds.mpr
  intro p
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (M.eventTimes p.2).card] with n hn
  rw [hrepr p]
  apply Finset.sum_subset (Finset.range_mono hn)
  intro k hkn hkc
  have hk : ¬ k < (M.eventTimes p.2).card := by
    simpa only [Finset.mem_range] using hkc
  simp [F, hk]

/-- Integrating a predictable payoff against predictable intensity
from zero through the current time gives a predictable process. -/
theorem Model.predictable_energyIntegral (M : Model Ω μ)
    (H : ℝ → Ω → ℝ) (hH : M.Predictable H) :
    M.Predictable (M.energyIntegral H) := by
  /- The rate-weighted payoff is predictable. A predictable parameter-integral
     argument for the kernel 0 < s < t proves the conclusion. Alternatively
     use adapted, continuous integrals where locally integrable, and express
     the Bochner integrability event predictably via the absolute lintegral.
     IMPORTANT: rate_integrable/rate_bounded are only asserted on [0,T].
     Do not assert global continuity or global local integrability; for t>T
     the definition remains a totalized integral. Endpoints have zero time
     mass, and t≤0 gives zero. Keep this all-time statement unchanged. -/
  let : MeasurableSpace (ℝ × Ω) := predictableSpace M.filtration
  have ht : Measurable (fun q : (ℝ × Ω) × ℝ => q.1.1) :=
    M.predictable_measurable_time.comp measurable_fst
  have hD : MeasurableSet {q : (ℝ × Ω) × ℝ | 0 < q.2 ∧ q.2 < q.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_lt measurable_snd ht)
  have hf : Measurable (fun q : (ℝ × Ω) × ℝ =>
      H (min q.2 q.1.1) q.1.2 *
        (M.atRisk (min q.2 q.1.1) q.1.2 * M.intensity (min q.2 q.1.1) q.1.2)) :=
    (hH.mul (M.atRisk_predictable.mul M.intensity_predictable)).comp
      M.predictable_measurable_min
  have hi := ((hf.indicator hD).stronglyMeasurable.integral_prod_right'
    (ν := volume)).measurable
  change Measurable (fun p : ℝ × Ω => M.energyIntegral H p.1 p.2)
  convert hi using 1
  funext p
  rw [Model.energyIntegral, integral_Ioc_eq_integral_Ioo]
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    by_cases hs : s ∈ Ioo 0 p.1
    · simp [Set.indicator, hs, hs.1, hs.2, min_eq_left (le_of_lt hs.2)]
    · have hs' : (p, s) ∉ {q : (ℝ × Ω) × ℝ | 0 < q.2 ∧ q.2 < q.1.1} := hs
      simp only [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs'])

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
