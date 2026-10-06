module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Anchor.Centering

/-! Inverse translation of centered binary laws into the binary anchor class,
including preservation of the causal conditions, contrasts, and supplied radius. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped ENNReal

-- @node: uncenterObs
noncomputable def uncenterObs {n : ℕ} (o : SampleObs n) : SampleObs n :=
  ⟨o.x, o.a, o.y + 1 / 2⟩

-- @node: uncenterFullObs
noncomputable def uncenterFullObs {n : ℕ}
    (z : DiscreteAteHeterogeneityFrontier.FullObs n) :
    DiscreteAteHeterogeneityFrontier.FullObs n :=
  ⟨z.x, z.a, z.y0 + 1 / 2, z.y1 + 1 / 2, z.y + 1 / 2⟩

-- @node: UncenterLawSpec
def UncenterLawSpec {n : ℕ} (P Q : Law n) : Prop :=
  Q.observedLaw = Measure.map uncenterObs P.observedLaw ∧
  Q.fullLaw = Measure.map uncenterFullObs P.fullLaw ∧
  Q.cellMass = P.cellMass ∧ Q.propensity = P.propensity ∧
  (∀ a k, 0 < P.cellMass k → Q.outcomeLaw a k =
    Measure.map (fun y : ℝ => y + 1 / 2) (P.outcomeLaw a k)) ∧
  (∀ a k, 0 < P.cellMass k →
    Q.outcomeMean a k = P.outcomeMean a k + 1 / 2)

-- @node: uncenterLaw_exists
lemma uncenterLaw_exists {n : ℕ} {rho : ℝ} (P : KnownRadiusClass n 1 rho) :
    ∃ Q : Law n, UncenterLawSpec P.law Q := by
  let shift : ℝ → ℝ := fun y => y + 1 / 2
  have hshift : Measurable shift := by fun_prop
  have hobs : Measurable (uncenterObs (n := n)) := by
    rw [measurable_comap_iff]
    change Measurable (fun o : SampleObs n => (o.x, o.a, o.y + 1 / 2))
    have ht : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
      rw [measurable_iff_comap_le]
      rfl
    exact ht.fst.prodMk (ht.snd.fst.prodMk (ht.snd.snd.add measurable_const))
  have hfull : Measurable (uncenterFullObs (n := n)) := by
    rw [measurable_comap_iff]
    change Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
      (z.x, z.a, z.y0 + 1 / 2, z.y1 + 1 / 2, z.y + 1 / 2))
    have ht : Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
      (z.x, z.a, z.y0, z.y1, z.y)) := by
      rw [measurable_iff_comap_le]
      rfl
    exact ht.fst.prodMk (ht.snd.fst.prodMk
      ((ht.snd.snd.fst.add measurable_const).prodMk
        ((ht.snd.snd.snd.fst.add measurable_const).prodMk
        (ht.snd.snd.snd.snd.add measurable_const))))
  let Q : Law n := {
    observedLaw := Measure.map uncenterObs P.law.observedLaw
    observed_isProbability := Measure.isProbabilityMeasure_map hobs.aemeasurable
    fullLaw := Measure.map uncenterFullObs P.law.fullLaw
    full_isProbability := Measure.isProbabilityMeasure_map hfull.aemeasurable
    cellMass := P.law.cellMass
    propensity := P.law.propensity
    outcomeLaw := fun a k => Measure.map shift (P.law.outcomeLaw a k)
    outcome_isProbability := by
      intro a k
      letI := P.law.outcome_isProbability a k
      exact Measure.isProbabilityMeasure_map hshift.aemeasurable
    outcomeMean := fun a k => ∫ y, y ∂Measure.map shift (P.law.outcomeLaw a k)
    observed_margin := by
      have hproj : Measurable
          (DiscreteAteHeterogeneityFrontier.FullObs.observed :
            DiscreteAteHeterogeneityFrontier.FullObs n → SampleObs n) := by
        rw [measurable_comap_iff]
        change Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
          (z.x, z.a, z.y))
        have ht : Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
          (z.x, z.a, z.y0, z.y1, z.y)) := by
          rw [measurable_iff_comap_le]
          rfl
        exact ht.fst.prodMk (ht.snd.fst.prodMk ht.snd.snd.snd.snd)
      rw [Measure.map_map hproj hfull, ← P.law.observed_margin,
        Measure.map_map hobs hproj]
      congr 1
    cellMass_eq := by
      intro k
      rw [P.law.cellMass_eq]
      unfold DiscreteAteHeterogeneityFrontier.realMass
      have hx : Measurable (fun o : SampleObs n => o.x) := by
        have ht : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
          rw [measurable_iff_comap_le]
          rfl
        exact measurable_fst.comp ht
      have hs : MeasurableSet {o : SampleObs n | o.x = k} :=
        (measurableSet_singleton k).preimage hx
      rw [Measure.map_apply_of_aemeasurable hobs.aemeasurable hs]
      rfl
    cellMass_range := P.law.cellMass_range
    propensity_range := P.law.propensity_range
    arm_outcome_factorization := by
      intro a k s hs
      have hevent : MeasurableSet {o : SampleObs n | o.x = k ∧ o.a = a ∧ o.y ∈ s} := by
        have ht : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
          rw [measurable_iff_comap_le]
          rfl
        exact ((measurableSet_singleton k).preimage (measurable_fst.comp ht)).inter
          (((measurableSet_singleton a).preimage
            (measurable_fst.comp (measurable_snd.comp ht))).inter
            (hs.preimage (measurable_snd.comp (measurable_snd.comp ht))))
      simp only [DiscreteAteHeterogeneityFrontier.realMass]
      rw [Measure.map_apply_of_aemeasurable hshift.aemeasurable hs,
        Measure.map_apply_of_aemeasurable hobs.aemeasurable hevent]
      convert P.law.arm_outcome_factorization a k (shift ⁻¹' s) (hshift hs) using 1
      congr 1
      rfl
    outcomeMean_eq := by
      intro a k
      rfl }
  refine ⟨Q, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · rfl
  · rfl
  · intro a k hk
    rfl
  · intro a k hk
    change (∫ y, y ∂Measure.map shift (P.law.outcomeLaw a k)) =
      P.law.outcomeMean a k + 1 / 2
    rw [integral_map hshift.aemeasurable (by fun_prop), P.law.outcomeMean_eq]
    letI := P.law.outcome_isProbability a k
    have hi : Integrable (fun y : ℝ => y) (P.law.outcomeLaw a k) :=
      DiscreteAteHeterogeneityFrontier.outcome_integrable_of_second_moment
        P.law P.variance_envelope a k hk
    change (∫ y, y + 1 / 2 ∂P.law.outcomeLaw a k) =
      (∫ y, y ∂P.law.outcomeLaw a k) + 1 / 2
    have huniv : (P.law.outcomeLaw a k).real Set.univ = 1 :=
      isProbabilityMeasure_iff_real.mp (P.law.outcome_isProbability a k)
    simpa only [Pi.add_apply, integral_const, smul_eq_mul, huniv, one_mul] using
      (integral_add hi (integrable_const (1 / 2 : ℝ)))

/-- Shift the centered law's outcomes by one half. -/
-- @node: uncenterLaw
noncomputable def uncenterLaw {n : ℕ} {rho : ℝ} (Q : KnownRadiusClass n 1 rho) : Law n :=
  Classical.choose (uncenterLaw_exists Q)

/-- Uncentering both potential outcomes and the observed outcome is measurable. -/
-- @node: uncenterFullObs_measurable
@[fun_prop] lemma uncenterFullObs_measurable (n : ℕ) :
    Measurable (uncenterFullObs (n := n)) := by
  rw [measurable_comap_iff]
  change Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
    (z.x, z.a, z.y0 + 1 / 2, z.y1 + 1 / 2, z.y + 1 / 2))
  have ht := fullObs_coordinates_measurable n
  exact ht.fst.prodMk (ht.snd.fst.prodMk
    ((ht.snd.snd.fst.add measurable_const).prodMk
      ((ht.snd.snd.snd.fst.add measurable_const).prodMk
        (ht.snd.snd.snd.snd.add measurable_const))))

/-- Translating the observed and selected potential outcomes preserves consistency,
roadmap (1). -/
-- @node: uncenterLaw_consistency
lemma uncenterLaw_consistency {n : ℕ} {rho : ℝ} (P : KnownRadiusClass n 1 rho) :
    Consistency (uncenterLaw P) := by
  have h := Classical.choose_spec (uncenterLaw_exists P)
  change UncenterLawSpec P.law (uncenterLaw P) at h
  change (uncenterLaw P).fullLaw
    {z | z.y ≠ if z.a then z.y1 else z.y0} = 0
  have ht := fullObs_coordinates_measurable n
  have hy : Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
      if z.a then z.y1 else z.y0) := by
    exact Measurable.ite
      ((measurableSet_singleton true).preimage ht.snd.fst)
      ht.snd.snd.snd.fst ht.snd.snd.fst
  have hs : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
      z.y ≠ if z.a then z.y1 else z.y0} :=
    (measurableSet_eq_fun ht.snd.snd.snd.snd hy).compl
  rw [h.2.1, Measure.map_apply (uncenterFullObs_measurable n) hs]
  have heq : uncenterFullObs ⁻¹'
      {z : DiscreteAteHeterogeneityFrontier.FullObs n |
        z.y ≠ if z.a then z.y1 else z.y0} =
      {z | z.y ≠ if z.a then z.y1 else z.y0} := by
    ext z
    cases ha : z.a <;> simp [uncenterFullObs, ha]
  rw [heq]
  exact P.consistency

/-- Deterministic translation preserves each arm's conditional exchangeability,
roadmap (1). -/
-- @node: uncenterLaw_exchangeability
lemma uncenterLaw_exchangeability {n : ℕ} {rho : ℝ} (P : KnownRadiusClass n 1 rho) :
    ConditionalExchangeability (uncenterLaw P) := by
  have h := Classical.choose_spec (uncenterLaw_exists P)
  change UncenterLawSpec P.law (uncenterLaw P) at h
  intro arm k a s hs
  have ht := fullObs_coordinates_measurable n
  have hx : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
      z.x = k} := (measurableSet_singleton k).preimage ht.fst
  have ha : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
      z.a = a} := (measurableSet_singleton a).preimage ht.snd.fst
  have hy : Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
      if arm then z.y1 else z.y0) := by
    cases arm <;> simpa using (by
      first | exact ht.snd.snd.fst | exact ht.snd.snd.snd.fst)
  have hys : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
      (if arm then z.y1 else z.y0) ∈ s} := hs.preimage hy
  have hxa : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
      z.x = k ∧ z.a = a} := hx.inter ha
  have hxy : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
      z.x = k ∧ (if arm then z.y1 else z.y0) ∈ s} := hx.inter hys
  have hxay : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
      z.x = k ∧ z.a = a ∧ (if arm then z.y1 else z.y0) ∈ s} :=
    hx.inter (ha.inter hys)
  rw [h.2.1,
    Measure.map_apply (uncenterFullObs_measurable n) hxay,
    Measure.map_apply (uncenterFullObs_measurable n) hx,
    Measure.map_apply (uncenterFullObs_measurable n) hxa,
    Measure.map_apply (uncenterFullObs_measurable n) hxy]
  have hshift : Measurable (fun y : ℝ => y + 1 / 2) := by fun_prop
  have hex := P.exchangeability arm k a
    ((fun y : ℝ => y + 1 / 2) ⁻¹' s) (hs.preimage hshift)
  cases arm <;> simpa [uncenterFullObs] using hex

/-- Translation cancels from each occupied-cell contrast, roadmap (6). -/
-- @node: uncenterLaw_cellEffect
lemma uncenterLaw_cellEffect {n : ℕ} {rho : ℝ} (Q : KnownRadiusClass n 1 rho)
    (k : Fin n) (hk : 0 < Q.law.cellMass k) :
    DiscreteAteHeterogeneityFrontier.cellEffect (uncenterLaw Q) k =
      DiscreteAteHeterogeneityFrontier.cellEffect Q.law k := by
  have h := Classical.choose_spec (uncenterLaw_exists Q)
  change UncenterLawSpec Q.law (uncenterLaw Q) at h
  unfold DiscreteAteHeterogeneityFrontier.cellEffect
  rw [h.2.2.2.2.2 true k hk, h.2.2.2.2.2 false k hk]
  ring

/-- Null cells contribute zero; inverse translation preserves the target. -/
-- @node: uncenterLaw_ateTarget
lemma uncenterLaw_ateTarget {n : ℕ} {rho : ℝ} (Q : KnownRadiusClass n 1 rho) :
    ateTarget (uncenterLaw Q) = ateTarget Q.law := by
  have h := Classical.choose_spec (uncenterLaw_exists Q)
  change UncenterLawSpec Q.law (uncenterLaw Q) at h
  unfold ateTarget DiscreteAteHeterogeneityFrontier.rawAteFormula
  apply Finset.sum_congr rfl
  intro k hk
  rw [h.2.2.1]
  by_cases hp : 0 < Q.law.cellMass k
  · rw [uncenterLaw_cellEffect Q k hp]
  · have hz : Q.law.cellMass k = 0 :=
      le_antisymm (le_of_not_gt hp) (Q.law.cellMass_range k).1
    rw [hz, zero_mul, zero_mul]

/-- Shifting the two centered atoms by one half yields precisely zero and one. -/
-- @node: uncenter_binary_atoms
lemma uncenter_binary_atoms (y : ℝ) :
    y + 1 / 2 ∈ ({0, 1} : Set ℝ) ↔ y ∈ ({-1 / 2, 1 / 2} : Set ℝ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Inverse translation gives binary potential outcomes and conditional marginals. -/
-- @node: uncenterLaw_binary
lemma uncenterLaw_binary {n : ℕ} {rho : ℝ} (Q : KnownRadiusClass n 1 rho)
    (hb : CenteredBinary Q.law) :
    (uncenterLaw Q).fullLaw {z | z.y0 ∉ ({0, 1} : Set ℝ) ∨
      z.y1 ∉ ({0, 1} : Set ℝ)} = 0 ∧
    ∀ a k, 0 < (uncenterLaw Q).cellMass k →
      (uncenterLaw Q).outcomeLaw a k (({0, 1} : Set ℝ)ᶜ) = 0 := by
  have h := Classical.choose_spec (uncenterLaw_exists Q)
  change UncenterLawSpec Q.law (uncenterLaw Q) at h
  constructor
  · have ht := fullObs_coordinates_measurable n
    have hs : MeasurableSet {z : DiscreteAteHeterogeneityFrontier.FullObs n |
        z.y0 ∉ ({0, 1} : Set ℝ) ∨ z.y1 ∉ ({0, 1} : Set ℝ)} :=
      (((MeasurableSet.singleton 0).union (MeasurableSet.singleton 1)).preimage
        ht.snd.snd.fst).compl.union
      (((MeasurableSet.singleton 0).union (MeasurableSet.singleton 1)).preimage
        ht.snd.snd.snd.fst).compl
    rw [h.2.1, Measure.map_apply (uncenterFullObs_measurable n) hs]
    have heq : uncenterFullObs ⁻¹'
        {z : DiscreteAteHeterogeneityFrontier.FullObs n |
          z.y0 ∉ ({0, 1} : Set ℝ) ∨ z.y1 ∉ ({0, 1} : Set ℝ)} =
        {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
          z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq, uncenterFullObs,
        uncenter_binary_atoms]
    rw [heq]
    exact hb.1
  · intro a k hk
    rw [h.2.2.1] at hk
    have hs : MeasurableSet (({0, 1} : Set ℝ)ᶜ) := by measurability
    have hshift : Measurable (fun y : ℝ => y + 1 / 2) := by fun_prop
    rw [h.2.2.2.2.1 a k hk, Measure.map_apply hshift hs]
    have heq : (fun y : ℝ => y + 1 / 2) ⁻¹' (({0, 1} : Set ℝ)ᶜ) =
        (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_compl_iff, uncenter_binary_atoms]
    rw [heq]
    exact hb.2 a k hk

/-- Every centered binary member of the real class shifts into the anchor class,
with exactly the same cell contrasts and radius, roadmap (6). -/
-- @node: uncenterLaw_class_embedding
lemma uncenterLaw_class_embedding {n : ℕ} {rho : ℝ} (Q : KnownRadiusClass n 1 rho)
    (hb : CenteredBinary Q.law) :
    ∃ P : ZengAnchorClass n rho, P.law = uncenterLaw Q := by
  have h := Classical.choose_spec (uncenterLaw_exists Q)
  change UncenterLawSpec Q.law (uncenterLaw Q) at h
  have hbinary := uncenterLaw_binary Q hb
  refine ⟨{ law := uncenterLaw Q
            n_ge_three := Q.n_ge_three
            rho_range := Q.radius.1
            consistency := uncenterLaw_consistency Q
            exchangeability := uncenterLaw_exchangeability Q
            overlap := ?_
            binary_potential := hbinary.1
            binary_outcome := hbinary.2
            radius := ?_ }, rfl⟩
  · intro k hk
    rw [h.2.2.1] at hk
    rw [h.2.2.2.1]
    exact Q.overlap k hk
  · intro k hk
    rw [h.2.2.1] at hk
    change |DiscreteAteHeterogeneityFrontier.cellEffect (uncenterLaw Q) k -
      ateTarget (uncenterLaw Q)| ≤ rho * 1
    rw [uncenterLaw_cellEffect Q k hk, uncenterLaw_ateTarget Q]
    exact Q.radius.2 k hk

/-- Centering the inverse-translated anchor law recovers the original full-data law. -/
-- @node: centerLaw_inverse_embedding
lemma centerLaw_inverse_embedding {n : ℕ} {rho : ℝ}
    (Q : KnownRadiusClass n 1 rho) (hb : CenteredBinary Q.law) :
    ∃ P : ZengAnchorClass n rho, (centerLaw P).fullLaw = Q.law.fullLaw := by
  obtain ⟨P, hP⟩ := uncenterLaw_class_embedding Q hb
  have hc := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at hc
  have hu := Classical.choose_spec (uncenterLaw_exists Q)
  change UncenterLawSpec Q.law (uncenterLaw Q) at hu
  refine ⟨P, ?_⟩
  rw [hc.2.1, hP, hu.2.1,
    Measure.map_map (centerFullObs_measurable n) (uncenterFullObs_measurable n)]
  have hid : (centerFullObs (n := n)) ∘ uncenterFullObs = id := by
    funext z
    cases z
    simp [Function.comp_def, centerFullObs, uncenterFullObs]
  rw [hid, Measure.map_id]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
