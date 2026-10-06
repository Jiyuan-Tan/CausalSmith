module
public import Causalean.Stat.RecurrentEvent.Observation
public import Causalean.Stat.RecurrentEvent.PoissonCampbell
public import Causalean.Stat.RecurrentEvent.TailRetention

/-!
# Primitive representation of observed recurrence events

The observed counting kernel is reduced to a finite primitive point sum,
then integrated against independent stopping times and Poisson intensity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.RecurrentEvent

variable {A X Y : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- [A recurrent-event model](hyp:M) and [an arm](hyp:a) determine [the
observed armwise recurrence-event measure](goal), which counts every retained
recurrence time with multiplicity. -/
noncomputable def Model.recurrenceEventMeasure (M : Model A X) (a : A) : Measure ℝ :=
  (M.observedLaw.restrict {y | y.1 = a}).bind (historyCountingKernel A)

/-- [A recurrent-event model](hyp:M), [an arm](hyp:a), [a requested time
set](hyp:s), and [a primitive outcome](hyp:ω) determine [the retained
primitive recurrence count in that set](goal), with points counted by
multiplicity. -/
noncomputable def Model.primitiveRecurrenceCountSet (M : Model A X)
    (a : A) (s : Set ℝ) (ω : Outcome A X) : ℝ≥0∞ := by
  classical
  exact ∑ i : Fin ω.2.1.1,
    if ω.1 = a ∧ M.time (ω.2.1.2 i) < M.stopTime ω ∧
        M.time (ω.2.1.2 i) ∈ s
    then (1 : ℝ≥0∞) else 0

/-- [A recurrent-event model](hyp:M), [an arm](hyp:a), and [a measurable time
set](hyp:s,hs) have [observed recurrence-event mass equal to the primitive
expected retained count before the observed stop](goal). -/
theorem Model.recurrence_event_measure_primitive (M : Model A X) (a : A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    M.recurrenceEventMeasure a s =
      ∫⁻ ω, M.primitiveRecurrenceCountSet a s ω ∂M.primitiveLaw := by
  classical
  have hcount (ω : Outcome A X) :
      (historyCountingKernel A (M.observe ω)) s =
        ∑ i : Fin ω.2.1.1,
          if M.time (ω.2.1.2 i) < M.stopTime ω ∧ M.time (ω.2.1.2 i) ∈ s
          then (1 : ℝ≥0∞) else 0 := by
    have hbad : ¬ M.horizon + 1 < M.stopTime ω := by
      have hle : M.stopTime ω ≤ M.horizon := min_le_right _ _
      linarith
    change (Measure.sum (fun n : ℕ =>
      if (M.observe ω).2.2.2 n < (M.observe ω).2.1 then
        Measure.dirac ((M.observe ω).2.2.2 n) else 0)) s = _
    rw [Measure.sum_apply _ hs]
    rw [tsum_eq_sum (s := Finset.range ω.2.1.1)]
    · rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : (n : ℕ) < ω.2.1.1 := n.isLt
      by_cases ht : M.time (ω.2.1.2 n) < M.stopTime ω
      · simp [Model.observe, hn', ht, Measure.dirac_apply, Set.indicator]
      · simp [Model.observe, hn', ht, hbad]
    · intro n hn
      have hn' : ¬ n < ω.2.1.1 := by simpa using hn
      simp [Model.observe, hn', hbad]
  have hmeas : Measurable (fun y : A × (ℝ × (Bool × (ℕ → ℝ))) =>
      (historyCountingKernel A y) s) :=
    (historyCountingKernel A).measurable_coe hs
  have harm : MeasurableSet {y : A × (ℝ × (Bool × (ℕ → ℝ))) | y.1 = a} :=
    (measurableSet_singleton a).preimage measurable_fst
  calc
    M.recurrenceEventMeasure a s =
        ∫⁻ y in {y | y.1 = a}, (historyCountingKernel A y) s ∂M.observedLaw := by
      unfold Model.recurrenceEventMeasure
      rw [Measure.bind_apply hs (historyCountingKernel A).aemeasurable]
    _ = ∫⁻ ω,
        ({y | y.1 = a}.indicator (fun y => (historyCountingKernel A y) s))
          (M.observe ω) ∂M.primitiveLaw := by
      rw [← lintegral_indicator harm _]
      unfold Model.observedLaw
      exact lintegral_map (μ := M.primitiveLaw) (hmeas.indicator harm) M.measurable_observe
    _ = ∫⁻ ω, M.primitiveRecurrenceCountSet a s ω ∂M.primitiveLaw := by
      congr 1
      funext ω
      change (if ω.1 = a then (historyCountingKernel A (M.observe ω)) s else 0) =
        M.primitiveRecurrenceCountSet a s ω
      by_cases ha : ω.1 = a
      · simp only [ha, if_true]
        rw [hcount ω]
        simp [Model.primitiveRecurrenceCountSet, ha]
      · simp [ha, Model.primitiveRecurrenceCountSet]

/-- [A recurrent-event model](hyp:M), [an arm](hyp:a), and [a measurable time
set](hyp:s,hs) have [a primitive stopped recurrence count equal to Poisson
intensity weighted by assignment mass and strict death and censoring
retention](goal). -/
theorem Model.recurrence_primitive_strict_tail (M : Model A X) (a : A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (∫⁻ ω, M.primitiveRecurrenceCountSet a s ω ∂M.primitiveLaw) =
      ∫⁻ t in s ∩ Ico (0 : ℝ) M.horizon,
        M.armLaw {a} * M.deathLaw (Ioi t) * M.censorLaw (Ioi t) *
          (M.intensity t : ℝ≥0∞) ∂volume := by
  classical
  letI := M.pointProb
  letI := M.armProb
  letI := M.deathProb
  letI := M.censorProb
  let μ := Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
    M.pointLaw M.poissonRate
  let F : Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X ×
      (ℝ × ℝ) → ℝ≥0∞ := fun z =>
    ∑ i : Fin z.1.1,
      if M.time (z.1.2 i) ∈ s ∧ M.time (z.1.2 i) < z.2.1 ∧
          M.time (z.1.2 i) < z.2.2 ∧ M.time (z.1.2 i) < M.horizon
      then 1 else 0
  have hF : Measurable F := by
    have he (n : ℕ) : MeasurableEmbedding
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
          (X := X) n) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x y h
        exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      · exact Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.measurable_fixedSizeEmbed n
      · intro u hu
        change @MeasurableSet _
          (⨅ m, (inferInstance : MeasurableSpace (Fin m → X)).map (Sigma.mk m))
          (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed n '' u)
        rw [MeasurableSpace.measurableSet_iInf]
        intro m
        change MeasurableSet
          ((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
            (X := X) m) ⁻¹'
          ((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
            (X := X) n) '' u))
        by_cases h : m = n
        · subst m
          rw [Set.preimage_image_eq u (fun x y h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)]
          exact hu
        · convert MeasurableSet.empty using 1
          ext x
          simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
          rintro ⟨y, _, heq⟩
          exact h (congrArg Sigma.fst heq).symm
    intro u hu
    have hset : F ⁻¹' u = ⋃ n : ℕ,
        (Prod.map (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.fixedSizeEmbed
          (X := X) n) id) ''
          {z : (Fin n → X) × (ℝ × ℝ) | F (⟨n, z.1⟩, z.2) ∈ u} := by
      ext ⟨⟨n, x⟩, dc⟩
      constructor
      · intro ht
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        exact ⟨(x, dc), ht, rfl⟩
      · intro ht
        obtain ⟨m, ⟨y, e⟩, hy, hz⟩ := Set.mem_iUnion.mp ht
        cases hz
        exact hy
    rw [hset]
    apply MeasurableSet.iUnion
    intro n
    apply ((he n).prodMap MeasurableEmbedding.id).measurableSet_image.mpr
    have hn : Measurable (fun z : (Fin n → X) × (ℝ × ℝ) => F (⟨n, z.1⟩, z.2)) := by
      change Measurable (fun z : (Fin n → X) × (ℝ × ℝ) =>
        ∑ i : Fin n,
          if M.time (z.1 i) ∈ s ∧ M.time (z.1 i) < z.2.1 ∧
              M.time (z.1 i) < z.2.2 ∧ M.time (z.1 i) < M.horizon
          then (1 : ℝ≥0∞) else 0)
      apply Finset.measurable_sum
      intro i hi
      have ht : Measurable (fun z : (Fin n → X) × (ℝ × ℝ) => M.time (z.1 i)) :=
        M.measurable_time.comp ((measurable_pi_apply i).comp measurable_fst)
      apply Measurable.ite
      · convert ((hs.preimage ht).inter
          (measurableSet_lt ht (measurable_fst.comp measurable_snd))).inter
          ((measurableSet_lt ht (measurable_snd.comp measurable_snd)).inter
            (measurableSet_lt ht (measurable_const : Measurable (fun _ => M.horizon)))) using 1 <;>
          ext z <;> simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_preimage, Function.comp_apply] <;> tauto
      · exact measurable_const
      · exact measurable_const
    exact hn hu
  let G : A × (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample X ×
      (ℝ × ℝ)) → ℝ≥0∞ := fun z => if z.1 = a then F z.2 else 0
  have hG : Measurable G :=
    Measurable.ite ((measurableSet_singleton a).preimage measurable_fst)
      (hF.comp measurable_snd) measurable_const
  have hcount (z : Outcome A X) : M.primitiveRecurrenceCountSet a s z = G z := by
    unfold Model.primitiveRecurrenceCountSet G F Model.stopTime
    by_cases ha : z.1 = a
    · simp only [ha, if_true]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [true_and, lt_min_iff]
      congr 1
      apply propext
      tauto
    · simp [ha]
  have hprimitive :
      (∫⁻ z, M.primitiveRecurrenceCountSet a s z ∂M.primitiveLaw) =
        M.armLaw {a} * (∫⁻ z, F z ∂μ.prod (M.deathLaw.prod M.censorLaw)) := by
    change (∫⁻ z, M.primitiveRecurrenceCountSet a s z
      ∂M.armLaw.prod (μ.prod (M.deathLaw.prod M.censorLaw))) = _
    simp_rw [hcount]
    rw [lintegral_prod_symm' G hG]
    have hinner (z : _) :
        (∫⁻ b, G (b, z) ∂M.armLaw) = M.armLaw {a} * F z := by
      change (∫⁻ b, ({a} : Set A).indicator (fun _ => F z) b ∂M.armLaw) = _
      rw [lintegral_indicator_const (measurableSet_singleton a)]
      exact mul_comm _ _
    simp_rw [hinner]
    rw [lintegral_const_mul (M.armLaw {a}) hF]
  rw [hprimitive]
  have hpoisson (dc : ℝ × ℝ) :
      (∫⁻ sample, F (sample, dc) ∂μ) =
        ∫⁻ t in Ico (0 : ℝ) M.horizon,
          (if t ∈ s ∧ t < dc.1 ∧ t < dc.2 then (M.intensity t : ℝ≥0∞) else 0)
            ∂volume := by
    let f : ℝ → ℝ≥0∞ := fun t =>
      if t ∈ s ∧ t < dc.1 ∧ t < dc.2 ∧ t < M.horizon then 1 else 0
    have hf : Measurable f := by
      apply Measurable.ite
      · convert ((hs.inter (measurableSet_Iio : MeasurableSet (Iio dc.1))).inter
          (measurableSet_Iio : MeasurableSet (Iio dc.2))).inter
          (measurableSet_Iio : MeasurableSet (Iio M.horizon)) using 1 <;>
          ext t <;> simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_Iio] <;> tauto
      · exact measurable_const
      · exact measurable_const
    calc
      (∫⁻ sample, F (sample, dc) ∂μ) =
          ∫⁻ t in Ico (0 : ℝ) M.horizon,
            f t * (M.intensity t : ℝ≥0∞) ∂volume := by
        exact M.poisson_time_lintegral f hf
      _ = _ := by
        apply setLIntegral_congr_fun measurableSet_Ico
        intro t ht
        simp only [f]
        have hth : t < M.horizon := ht.2
        by_cases h : t ∈ s ∧ t < dc.1 ∧ t < dc.2 <;> simp [h, hth]
  have hswap :
      (∫⁻ z, F z ∂μ.prod (M.deathLaw.prod M.censorLaw)) =
        ∫⁻ t in Ico (0 : ℝ) M.horizon,
          ∫⁻ dc : ℝ × ℝ,
            if t ∈ s ∧ t < dc.1 ∧ t < dc.2
            then (M.intensity t : ℝ≥0∞) else 0
            ∂(M.deathLaw.prod M.censorLaw) ∂volume := by
    rw [lintegral_prod_symm' F hF]
    simp_rw [hpoisson]
    have hH : Measurable (fun z : (ℝ × ℝ) × ℝ =>
        if z.2 ∈ s ∧ z.2 < z.1.1 ∧ z.2 < z.1.2
        then (M.intensity z.2 : ℝ≥0∞) else 0) := by
      have ht : Measurable (fun z : (ℝ × ℝ) × ℝ => z.2) := measurable_snd
      exact Measurable.ite
        ((hs.preimage ht).inter
          ((measurableSet_lt ht (measurable_fst.comp measurable_fst)).inter
            (measurableSet_lt ht (measurable_snd.comp measurable_fst))))
        (M.measurable_intensity.coe_nnreal_ennreal.comp ht) measurable_const
    exact lintegral_lintegral_swap hH.aemeasurable
  rw [hswap]
  have htail (t : ℝ) :
      (∫⁻ dc : ℝ × ℝ,
          if t ∈ s ∧ t < dc.1 ∧ t < dc.2
          then (M.intensity t : ℝ≥0∞) else 0
          ∂(M.deathLaw.prod M.censorLaw)) =
        if t ∈ s then M.deathLaw (Ioi t) * M.censorLaw (Ioi t) *
          (M.intensity t : ℝ≥0∞) else 0 := by
    by_cases ht : t ∈ s
    · simp only [ht, true_and, if_true]
      have hfun : (fun dc : ℝ × ℝ =>
          if t < dc.1 ∧ t < dc.2 then (M.intensity t : ℝ≥0∞) else 0) =
          (Ioi t ×ˢ Ioi t).indicator (fun _ => (M.intensity t : ℝ≥0∞)) := by
        funext dc
        simp [Set.indicator, Set.mem_prod]
      rw [hfun]
      rw [lintegral_indicator_const (measurableSet_Ioi.prod measurableSet_Ioi)]
      rw [Measure.prod_prod]
      exact mul_comm _ _
    · simp [ht]
  simp_rw [htail]
  have htailMeas (ν : Measure ℝ) [SFinite ν] :
      Measurable (fun t : ℝ => ν (Ioi t)) := by
    let E : Set (ℝ × ℝ) := {p | p.1 < p.2}
    have hE : MeasurableSet E := by
      dsimp [E]
      exact measurableSet_lt measurable_fst measurable_snd
    have h := measurable_measure_prodMk_left (ν := ν) hE
    convert h using 1
    funext t
    congr 1
  have hscore : Measurable (fun t : ℝ =>
      if t ∈ s then M.deathLaw (Ioi t) * M.censorLaw (Ioi t) *
        (M.intensity t : ℝ≥0∞) else 0) := by
    exact Measurable.ite hs
      (((htailMeas M.deathLaw).mul (htailMeas M.censorLaw)).mul
        M.measurable_intensity.coe_nnreal_ennreal) measurable_const
  rw [← lintegral_const_mul (M.armLaw {a}) hscore]
  calc
    (∫⁻ t in Ico (0 : ℝ) M.horizon,
        M.armLaw {a} * if t ∈ s then
          M.deathLaw (Ioi t) * M.censorLaw (Ioi t) * (M.intensity t : ℝ≥0∞)
        else 0 ∂volume) =
        ∫⁻ t in Ico (0 : ℝ) M.horizon,
          s.indicator (fun t => M.armLaw {a} * M.deathLaw (Ioi t) *
            M.censorLaw (Ioi t) * (M.intensity t : ℝ≥0∞)) t ∂volume := by
      congr 1
      funext t
      by_cases ht : t ∈ s <;> simp [Set.indicator, ht, mul_assoc]
    _ = _ := by
      rw [lintegral_indicator hs, Measure.restrict_restrict hs]


end Causalean.Stat.RecurrentEvent
