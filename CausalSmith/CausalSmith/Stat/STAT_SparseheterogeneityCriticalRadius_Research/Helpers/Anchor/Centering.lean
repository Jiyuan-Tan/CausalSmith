module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.T_KnownRadiusMinimaxFrontier

/-! Centering the binary radius class inside the real-outcome known-radius
class and transferring the matching minimax rate. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped ENNReal

noncomputable def centerObs {n : ℕ} (o : SampleObs n) : SampleObs n :=
  ⟨o.x, o.a, o.y - 1 / 2⟩

noncomputable def centerFullObs {n : ℕ}
    (z : DiscreteAteHeterogeneityFrontier.FullObs n) :
    DiscreteAteHeterogeneityFrontier.FullObs n :=
  ⟨z.x, z.a, z.y0 - 1 / 2, z.y1 - 1 / 2, z.y - 1 / 2⟩

def CenterLawSpec {n : ℕ} (P Q : Law n) : Prop :=
  Q.observedLaw = Measure.map centerObs P.observedLaw ∧
  Q.fullLaw = Measure.map centerFullObs P.fullLaw ∧
  Q.cellMass = P.cellMass ∧ Q.propensity = P.propensity ∧
  (∀ a k, 0 < P.cellMass k → Q.outcomeLaw a k =
    Measure.map (fun y : ℝ => y - 1 / 2) (P.outcomeLaw a k)) ∧
  (∀ a k, 0 < P.cellMass k →
    Q.outcomeMean a k = P.outcomeMean a k - 1 / 2)

-- @node: centerLaw_exists
lemma centerLaw_exists {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    ∃ Q : Law n, CenterLawSpec P.law Q := by
  let shift : ℝ → ℝ := fun y => y - 1 / 2
  have hshift : Measurable shift := by fun_prop
  have hobs : Measurable (centerObs (n := n)) := by
    rw [measurable_comap_iff]
    change Measurable (fun o : SampleObs n => (o.x, o.a, o.y - 1 / 2))
    have ht : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
      rw [measurable_iff_comap_le]
      rfl
    exact ht.fst.prodMk (ht.snd.fst.prodMk (ht.snd.snd.sub measurable_const))
  have hfull : Measurable (centerFullObs (n := n)) := by
    rw [measurable_comap_iff]
    change Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
      (z.x, z.a, z.y0 - 1 / 2, z.y1 - 1 / 2, z.y - 1 / 2))
    have ht : Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
      (z.x, z.a, z.y0, z.y1, z.y)) := by
      rw [measurable_iff_comap_le]
      rfl
    exact ht.fst.prodMk (ht.snd.fst.prodMk
      ((ht.snd.snd.fst.sub measurable_const).prodMk
        ((ht.snd.snd.snd.fst.sub measurable_const).prodMk
        (ht.snd.snd.snd.snd.sub measurable_const))))
  let Q : Law n := {
    observedLaw := Measure.map centerObs P.law.observedLaw
    observed_isProbability := Measure.isProbabilityMeasure_map hobs.aemeasurable
    fullLaw := Measure.map centerFullObs P.law.fullLaw
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
      P.law.outcomeMean a k - 1 / 2
    rw [integral_map hshift.aemeasurable (by fun_prop), P.law.outcomeMean_eq]
    letI := P.law.outcome_isProbability a k
    have hmem : ∀ᵐ y ∂P.law.outcomeLaw a k, y ∈ ({0, 1} : Set ℝ) := by
      rw [ae_iff]
      change (P.law.outcomeLaw a k) (({0, 1} : Set ℝ)ᶜ) = 0
      exact P.binary_outcome a k hk
    have hi : Integrable (fun y : ℝ => y) (P.law.outcomeLaw a k) :=
      Integrable.of_mem_Icc 0 1 (by fun_prop) (by
        filter_upwards [hmem] with y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl <;> simp)
    change (∫ y, y - 1 / 2 ∂P.law.outcomeLaw a k) =
      (∫ y, y ∂P.law.outcomeLaw a k) - 1 / 2
    have huniv : (P.law.outcomeLaw a k).real Set.univ = 1 :=
      isProbabilityMeasure_iff_real.mp (P.law.outcome_isProbability a k)
    simpa only [Pi.sub_apply, integral_const, smul_eq_mul, huniv, one_mul] using
      (integral_sub' hi (integrable_const (1 / 2 : ℝ)))

noncomputable def centerLaw {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) : Law n :=
  Classical.choose (centerLaw_exists P)

/-- Binary support puts every occupied conditional mean in the unit interval. -/
-- @node: anchor_outcomeMean_range
lemma anchor_outcomeMean_range {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho)
    (a : Bool) (k : Fin n) (hk : 0 < P.law.cellMass k) :
    P.law.outcomeMean a k ∈ Icc 0 1 := by
  letI := P.law.outcome_isProbability a k
  have hmem : ∀ᵐ y ∂P.law.outcomeLaw a k, y ∈ Icc (0 : ℝ) 1 := by
    have hb : ∀ᵐ y ∂P.law.outcomeLaw a k, y ∈ ({0, 1} : Set ℝ) := by
      rw [ae_iff]
      exact P.binary_outcome a k hk
    filter_upwards [hb] with y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> norm_num
  have hi : Integrable (fun y : ℝ => y) (P.law.outcomeLaw a k) :=
    Integrable.of_mem_Icc 0 1 (by fun_prop) hmem
  rw [P.law.outcomeMean_eq]
  constructor
  · exact integral_nonneg_of_ae (hmem.mono (fun y hy => hy.1))
  · have hle := integral_mono_ae hi (integrable_const (1 : ℝ))
      (hmem.mono (fun y hy => hy.2))
    simpa using hle

/-- Subtracting one half gives the centered mean envelope, roadmap (2). -/
-- @node: centerLaw_meanEnvelope
lemma centerLaw_meanEnvelope {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    MeanEnvelope 1 (centerLaw P) := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  intro a k hk
  rw [h.2.2.1] at hk
  rw [h.2.2.2.2.2 a k hk]
  have hm := anchor_outcomeMean_range P a k hk
  apply abs_le.mpr
  constructor <;> linarith [hm.1, hm.2]

/-- Binary support bounds the centered second moment without an extra assumption,
as required by roadmap (3). -/
-- @node: centerLaw_varianceEnvelope
lemma centerLaw_varianceEnvelope {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    VarianceEnvelope 1 (centerLaw P) := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  intro a k hk
  rw [h.2.2.1] at hk
  letI := P.law.outcome_isProbability a k
  have hm := anchor_outcomeMean_range P a k hk
  have hb : ∀ᵐ y ∂P.law.outcomeLaw a k, y ∈ ({0, 1} : Set ℝ) := by
    rw [ae_iff]
    exact P.binary_outcome a k hk
  have hbound : ∀ᵐ y ∂P.law.outcomeLaw a k,
      (y - P.law.outcomeMean a k) ^ 2 ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hb] with y hy
    refine ⟨sq_nonneg _, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> nlinarith [hm.1, hm.2]
  have hi : Integrable (fun y => (y - P.law.outcomeMean a k) ^ 2)
      (P.law.outcomeLaw a k) :=
    Integrable.of_mem_Icc 0 1 (by fun_prop) hbound
  have hshift : Measurable (fun y : ℝ => y - 1 / 2) := by fun_prop
  have hcancel : (fun y : ℝ =>
      (y - 1 / 2 - (P.law.outcomeMean a k - 1 / 2)) ^ 2) =
      (fun y => (y - P.law.outcomeMean a k) ^ 2) := by
    funext y
    ring
  rw [h.2.2.2.2.1 a k hk, h.2.2.2.2.2 a k hk]
  constructor
  · apply (integrable_map_measure (by fun_prop) hshift.aemeasurable).mpr
    simpa only [Function.comp_def, hcancel] using hi
  · rw [integral_map hshift.aemeasurable (by fun_prop), hcancel]
    have hle := integral_mono_ae hi (integrable_const (1 : ℝ))
      (hbound.mono (fun y hy => hy.2))
    simpa using hle

/-- Centering cancels from each occupied-cell treatment contrast, roadmap (4). -/
-- @node: centerLaw_cellEffect
lemma centerLaw_cellEffect {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho)
    (k : Fin n) (hk : 0 < P.law.cellMass k) :
    DiscreteAteHeterogeneityFrontier.cellEffect (centerLaw P) k =
      DiscreteAteHeterogeneityFrontier.cellEffect P.law k := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  unfold DiscreteAteHeterogeneityFrontier.cellEffect
  rw [h.2.2.2.2.2 true k hk, h.2.2.2.2.2 false k hk]
  ring

/-- Null cells contribute zero, so centering also preserves the target, roadmap (4). -/
-- @node: centerLaw_ateTarget
lemma centerLaw_ateTarget {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    ateTarget (centerLaw P) = ateTarget P.law := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  unfold ateTarget DiscreteAteHeterogeneityFrontier.rawAteFormula
  apply Finset.sum_congr rfl
  intro k hk
  rw [h.2.2.1]
  by_cases hp : 0 < P.law.cellMass k
  · rw [centerLaw_cellEffect P k hp]
  · have hz : P.law.cellMass k = 0 :=
      le_antisymm (le_of_not_gt hp) (P.law.cellMass_range k).1
    rw [hz, zero_mul, zero_mul]

/-- The supplied radius is invariant under centering, roadmap (4). -/
-- @node: centerLaw_knownRadius
lemma centerLaw_knownRadius {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    KnownRadius 1 rho (centerLaw P) := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  refine ⟨P.rho_range, ?_⟩
  intro k hk
  rw [h.2.2.1] at hk
  change |DiscreteAteHeterogeneityFrontier.cellEffect (centerLaw P) k -
    ateTarget (centerLaw P)| ≤ rho * 1
  rw [centerLaw_cellEffect P k hk, centerLaw_ateTarget P]
  exact P.radius k hk

/-- The coordinate map generating the full-record measurable space is measurable. -/
-- @node: fullObs_coordinates_measurable
@[fun_prop] lemma fullObs_coordinates_measurable (n : ℕ) :
    Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
      (z.x, z.a, z.y0, z.y1, z.y)) := by
  rw [measurable_iff_comap_le]
  rfl

/-- Centering both potential outcomes and the observed outcome is measurable. -/
-- @node: centerFullObs_measurable
@[fun_prop] lemma centerFullObs_measurable (n : ℕ) :
    Measurable (centerFullObs (n := n)) := by
  rw [measurable_comap_iff]
  change Measurable (fun z : DiscreteAteHeterogeneityFrontier.FullObs n =>
    (z.x, z.a, z.y0 - 1 / 2, z.y1 - 1 / 2, z.y - 1 / 2))
  have ht := fullObs_coordinates_measurable n
  exact ht.fst.prodMk (ht.snd.fst.prodMk
    ((ht.snd.snd.fst.sub measurable_const).prodMk
      ((ht.snd.snd.snd.fst.sub measurable_const).prodMk
        (ht.snd.snd.snd.snd.sub measurable_const))))

/-- Translating the observed and selected potential outcomes preserves consistency,
roadmap (1). -/
-- @node: centerLaw_consistency
lemma centerLaw_consistency {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    Consistency (centerLaw P) := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  change (centerLaw P).fullLaw
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
  rw [h.2.1, Measure.map_apply (centerFullObs_measurable n) hs]
  have heq : centerFullObs ⁻¹'
      {z : DiscreteAteHeterogeneityFrontier.FullObs n |
        z.y ≠ if z.a then z.y1 else z.y0} =
      {z | z.y ≠ if z.a then z.y1 else z.y0} := by
    ext z
    cases ha : z.a <;> simp [centerFullObs, ha]
  rw [heq]
  exact P.consistency

/-- Deterministic translation preserves each arm's conditional exchangeability,
roadmap (1). -/
-- @node: centerLaw_exchangeability
lemma centerLaw_exchangeability {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    ConditionalExchangeability (centerLaw P) := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
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
    Measure.map_apply (centerFullObs_measurable n) hxay,
    Measure.map_apply (centerFullObs_measurable n) hx,
    Measure.map_apply (centerFullObs_measurable n) hxa,
    Measure.map_apply (centerFullObs_measurable n) hxy]
  have hshift : Measurable (fun y : ℝ => y - 1 / 2) := by fun_prop
  have hex := P.exchangeability arm k a
    ((fun y : ℝ => y - 1 / 2) ⁻¹' s) (hs.preimage hshift)
  cases arm <;> simpa [centerFullObs] using hex

/-- The centered binary law satisfies every condition of the real-outcome class,
roadmap (1)--(4). -/
-- @node: centerLaw_class_embedding
lemma centerLaw_class_embedding {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    ∃ Q : KnownRadiusClass n 1 rho, Q.law = centerLaw P := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  refine ⟨{ law := centerLaw P
            n_ge_three := P.n_ge_three
            M_ge_one := by norm_num
            consistency := centerLaw_consistency P
            exchangeability := centerLaw_exchangeability P
            overlap := ?_
            mean_envelope := centerLaw_meanEnvelope P
            variance_envelope := centerLaw_varianceEnvelope P
            radius := centerLaw_knownRadius P }, rfl⟩
  intro k hk
  rw [h.2.2.1] at hk
  rw [h.2.2.2.1]
  exact P.overlap k hk

def CenteredBinary {n : ℕ} (P : Law n) : Prop :=
  P.fullLaw {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
    z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
  ∀ a k, 0 < P.cellMass k →
    P.outcomeLaw a k (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0

noncomputable def anchorEstimator (n : ℕ) (rho : ℝ)
    (sample : Fin n → SampleObs n) : ℝ :=
  knownRadiusEstimator n 1 rho (fun i => centerObs (sample i))

noncomputable def anchorWorstRisk (n : ℕ) (rho : ℝ) : ℝ :=
  ⨆ P : ZengAnchorClass n rho,
    DiscreteAteHeterogeneityFrontier.mse P.law (anchorEstimator n rho)

/-- Deterministic centering is a measurable map of the observed record. -/
-- @node: centerObs_measurable
@[fun_prop] lemma centerObs_measurable (n : ℕ) :
    Measurable (centerObs (n := n)) := by
  rw [measurable_comap_iff]
  change Measurable (fun o : SampleObs n => (o.x, o.a, o.y - 1 / 2))
  have ht : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact ht.fst.prodMk (ht.snd.fst.prodMk (ht.snd.snd.sub measurable_const))

/-- The estimator in roadmap (5) is measurable on the original binary sample. -/
-- @node: anchorEstimator_measurable
@[fun_prop] lemma anchorEstimator_measurable (n : ℕ) (rho : ℝ) :
    Measurable (anchorEstimator n rho) := by
  unfold anchorEstimator
  exact (knownRadiusEstimator_measurable n 1 rho).comp
    (measurable_pi_lambda _ (fun i =>
      (centerObs_measurable n).comp (measurable_pi_apply i)))

/-- Centering the input preserves the clipped estimator's range. -/
-- @node: anchorEstimator_range
lemma anchorEstimator_range (n : ℕ) (rho : ℝ) :
    ∀ sample, anchorEstimator n rho sample ∈ Icc (-1) 1 := by
  intro sample
  exact knownRadiusEstimator_range n 1 rho (by norm_num) _

/-- Exhibiting the centered admissible estimator proves the minimax comparison in (5). -/
-- @node: anchorMinimaxRisk_le_anchorWorstRisk
lemma anchorMinimaxRisk_le_anchorWorstRisk (n : ℕ) (rho : ℝ) :
    anchorMinimaxRisk n rho ≤ anchorWorstRisk n rho := by
  let est : DiscreteAteHeterogeneityFrontier.Estimator n n 1 :=
    ⟨anchorEstimator n rho, anchorEstimator_measurable n rho,
      anchorEstimator_range n rho⟩
  exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (e : DiscreteAteHeterogeneityFrontier.Estimator n n 1)
      (P : ZengAnchorClass n rho) => DiscreteAteHeterogeneityFrontier.mse P.law e.1)
    (fun e P => integral_nonneg (fun _ => sq_nonneg _)) est

/-- Centering commutes with the iid sample construction in roadmap (5). -/
-- @node: centerLaw_productLaw
lemma centerLaw_productLaw {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    DiscreteAteHeterogeneityFrontier.productLaw n (centerLaw P) =
      Measure.map (fun sample i => centerObs (sample i))
        (DiscreteAteHeterogeneityFrontier.productLaw n P.law) := by
  have h := Classical.choose_spec (centerLaw_exists P)
  change CenterLawSpec P.law (centerLaw P) at h
  unfold DiscreteAteHeterogeneityFrontier.productLaw
  rw [h.1]
  letI : IsProbabilityMeasure (Measure.map (centerObs (n := n)) P.law.observedLaw) :=
    Measure.isProbabilityMeasure_map (centerObs_measurable n).aemeasurable
  exact (Measure.pi_map_pi (fun _ => (centerObs_measurable n).aemeasurable)).symm

/-- Translation preserves the target and transports the loss integral, roadmap (5). -/
-- @node: anchorEstimator_mse_eq
lemma anchorEstimator_mse_eq {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho) :
    DiscreteAteHeterogeneityFrontier.mse P.law (anchorEstimator n rho) =
      DiscreteAteHeterogeneityFrontier.mse (centerLaw P)
        (knownRadiusEstimator n 1 rho) := by
  have ht : DiscreteAteHeterogeneityFrontier.rawAteFormula (centerLaw P) =
      DiscreteAteHeterogeneityFrontier.rawAteFormula P.law := centerLaw_ateTarget P
  unfold DiscreteAteHeterogeneityFrontier.mse
  rw [centerLaw_productLaw P, ht]
  have hm : Measurable (fun sample : Fin n → SampleObs n =>
      fun i => centerObs (sample i)) := by fun_prop
  have hloss : Measurable (fun x =>
      (knownRadiusEstimator n 1 rho x -
        DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2) :=
    ((knownRadiusEstimator_measurable n 1 rho).sub measurable_const).pow_const 2
  rw [integral_map hm.aemeasurable hloss.aestronglyMeasurable]
  rfl

/-- The full-class risk bound restricts to the binary class via centering.
This assembly depends on the real-outcome per-law risk lemma. -/
-- @node: anchorEstimator_risk_bound
lemma anchorEstimator_risk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n rho (P : ZengAnchorClass n rho),
      DiscreteAteHeterogeneityFrontier.mse P.law (anchorEstimator n rho) ≤
        C * rate n rho := by
  obtain ⟨C, hC, hbound⟩ := known_radius_estimator_risk_bound
  refine ⟨C, hC, ?_⟩
  intro n rho P
  obtain ⟨Q, hQ⟩ := centerLaw_class_embedding P
  rw [anchorEstimator_mse_eq P, ← hQ]
  simpa using hbound n 1 rho Q P.n_ge_three

/-- Taking the supremum yields the binary upper bound in roadmap (5). -/
-- @node: anchorWorstRisk_bound
lemma anchorWorstRisk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n rho, 3 ≤ n → 0 ≤ rho → rho ≤ 2 →
      anchorWorstRisk n rho ≤ C * rate n rho := by
  obtain ⟨C, hC, hbound⟩ := anchorEstimator_risk_bound
  refine ⟨C, hC, ?_⟩
  intro n rho hn hr0 hr2
  unfold anchorWorstRisk
  by_cases hne : Nonempty (ZengAnchorClass n rho)
  · letI := hne
    exact ciSup_le (fun P => hbound n rho P)
  · simp only [not_nonempty_iff] at hne
    letI := hne
    have hr : 0 ≤ rate n rho := by unfold rate; positivity
    simpa using mul_nonneg hC.le hr

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
