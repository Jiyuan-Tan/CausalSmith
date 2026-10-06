module
public import Causalean.Stat.Minimax.MinimaxRisk
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Stat.Minimax.LIntegralRisk
public import Causalean.Stat.Sample
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Superposition.Retention
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Recurrent events with endpoint censoring

The latent two-arm experiment, its observed history, the exact model atoms, and
the deterministic continuation and rate scales.
-/

@[expose] public section

open MeasureTheory Set Filter ProbabilityTheory
open scoped Interval NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

abbrev Arm := Bool -- @realizes mathbbA(two treatment arms) @realizes a(arm carrier)

/-- A finite recurrent-event configuration.  The first coordinate is the event
time; the second is an auxiliary ordering mark used only to obtain a canonical
standard-Borel realization of a finite point process. -/
abbrev RecurConfig := FiniteSample (ℝ × ℝ)

/-- The event-time multiset represented by a finite configuration. -/
noncomputable def RecurConfig.times (s : RecurConfig) : Multiset ℝ :=
  Multiset.ofList (List.ofFn (fun i => (s.points i).1))

/-- Count, in a padded stream with a declared finite length, the event times at
most a supplied threshold.  Keeping the length as a separate countable
coordinate makes joint measurability in the stream and threshold explicit. -/
noncomputable def RecurConfig.paddedCountLE
    (z : ℕ × (ℝ × (ℕ → ℝ × ℝ))) : ℕ :=
  ∑ i : Fin z.1, if (z.2.2 i).1 ≤ z.2.1 then 1 else 0

/-- The padded-stream count is jointly measurable in its declared length,
threshold, and stream. -/
@[fun_prop]
lemma RecurConfig.measurable_paddedCountLE :
    Measurable RecurConfig.paddedCountLE := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun y : ℝ × (ℕ → ℝ × ℝ) =>
    ∑ i : Fin n, if (y.2 i).1 ≤ y.1 then 1 else 0)
  apply Finset.measurable_sum Finset.univ
  intro i _
  apply Measurable.ite
  exact measurableSet_le (by fun_prop) measurable_fst
  · exact measurable_const
  · exact measurable_const

/-- The number of represented events whose event time is at most `x`. -/
noncomputable def RecurConfig.countLE (s : RecurConfig) (x : ℝ) : ℕ :=
  let padded := finiteSamplePaddedStream (0, 0) s
  RecurConfig.paddedCountLE (padded.1, x, padded.2)

/-- The induced recurrence count process on the study horizon.  It forgets
the enumeration of events and every auxiliary mark. -/
noncomputable def RecurConfig.countProcess (s : RecurConfig) :
    Set.Icc (0 : ℝ) 1 → ℕ := fun t => s.countLE t.1

/-- Counting events below a variable threshold is jointly measurable. -/
@[fun_prop]
lemma RecurConfig.measurable_countLE :
    Measurable (fun z : ℝ × RecurConfig => z.2.countLE z.1) := by
  have hpadded : Measurable
      (fun z : ℝ × RecurConfig => finiteSamplePaddedStream (0, 0) z.2) :=
    (finiteSamplePaddedStream_measurable (0, 0)).comp measurable_snd
  exact RecurConfig.measurable_paddedCountLE.comp
    (hpadded.fst.prodMk (measurable_fst.prodMk hpadded.snd))

/-- The count-process map is measurable in the product measurable space. -/
@[fun_prop]
lemma RecurConfig.measurable_countProcess :
    Measurable RecurConfig.countProcess := by
  rw [measurable_pi_iff]
  intro t
  exact RecurConfig.measurable_countLE.comp
    (measurable_const.prodMk measurable_id)

/-- The empty finite recurrent-event configuration. -/
def RecurConfig.empty : RecurConfig := fixedSizeEmbed 0 (fun i => Fin.elim0 i)

structure ClassConstants where
  beta : ℝ -- @realizes beta(positive Hölder exponent)
  kappa : ℝ -- @realizes kappa(positive retention exponent)
  rho : ℝ -- @realizes rho(positive remainder exponent)
  x0 : ℝ -- @realizes x0(terminal neighborhood width)
  lambdaMin : ℝ -- @realizes lambda_min(positive intensity lower bound)
  lambdaMax : ℝ -- @realizes lambda_max(upper bound above lambda_min)
  dMin : ℝ -- @realizes d_min(positive death lower bound)
  dMax : ℝ -- @realizes d_max(upper bound above d_min)
  Llambda : ℝ -- @realizes L_lambda(positive Hölder radius)
  Ld : ℝ -- @realizes L_d(positive Hölder radius)
  LG : ℝ -- @realizes L_G(positive remainder radius)
  gMin : ℝ -- @realizes g_min(positive endpoint coefficient lower bound)
  gMax : ℝ -- @realizes g_max(upper bound above g_min)
  Gint : ℝ -- @realizes G_int(interior retention bound)
  Ghor : ℝ -- @realizes G_hor(horizon retention bound)
  pMin : ℝ -- @realizes p_min(randomization lower bound)
  beta_pos : 0 < beta -- @realizes beta(range)
  kappa_pos : 0 < kappa -- @realizes kappa(range)
  rho_pos : 0 < rho -- @realizes rho(range)
  x0_pos : 0 < x0 -- @realizes x0(lower range)
  x0_le : x0 ≤ 1 / 2 -- @realizes x0(upper range)
  lambdaMin_pos : 0 < lambdaMin -- @realizes lambda_min(range)
  lambdaMin_lt : lambdaMin < lambdaMax -- @realizes lambda_max(range)
  dMin_pos : 0 < dMin -- @realizes d_min(range)
  dMin_lt : dMin < dMax -- @realizes d_max(range)
  Llambda_pos : 0 < Llambda -- @realizes L_lambda(range)
  Ld_pos : 0 < Ld -- @realizes L_d(range)
  LG_pos : 0 < LG -- @realizes L_G(range)
  gMin_pos : 0 < gMin -- @realizes g_min(range)
  gMin_lt : gMin < gMax -- @realizes g_max(range)
  Gint_pos : 0 < Gint -- @realizes G_int(lower range)
  Gint_le : Gint ≤ 1 -- @realizes G_int(upper range)
  Ghor_pos : 0 < Ghor -- @realizes G_hor(lower range)
  Ghor_le : Ghor ≤ 1 -- @realizes G_hor(upper range)
  pMin_pos : 0 < pMin -- @realizes p_min(lower range)
  pMin_le : pMin ≤ 1 / 2 -- @realizes p_min(upper range)

noncomputable def holderOrder (c : ClassConstants) : ℕ :=
  Nat.ceil c.beta - 1 -- @realizes ell(ceiling beta minus one)

structure LatentSubject where
  treatment : Arm -- @realizes A(randomized arm)
  recur : Arm → RecurConfig -- @realizes N_a_star(finite event configuration with multiplicities)
  death : Arm → ℝ -- @realizes D_a(latent death time)
  censor : Arm → ENNReal -- @realizes C_a(extended nonnegative censor time including infinity)

/-- Product coordinates of a latent subject. -/
def LatentSubject.toCoordinates (z : LatentSubject) :=
  (z.treatment, z.recur, z.death, z.censor)

/-- Product-derived measurable structure on latent subjects. -/
instance : MeasurableSpace LatentSubject :=
  MeasurableSpace.comap LatentSubject.toCoordinates inferInstance

/-- The complete latent coordinate map is measurable for the product-derived
structure. -/
@[fun_prop]
lemma measurable_latentSubject_toCoordinates :
    Measurable LatentSubject.toCoordinates := by
  apply Measurable.of_comap_le
  rfl

/-- Reading one arm's finite recurrent-event configuration is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_recur (a : Arm) :
    Measurable (fun z : LatentSubject => z.recur a) := by
  exact (measurable_pi_apply a).comp
    ((measurable_fst.comp measurable_snd).comp
      measurable_latentSubject_toCoordinates)

/-- Reading the assigned arm is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_treatment :
    Measurable (fun z : LatentSubject => z.treatment) := by
  exact measurable_fst.comp measurable_latentSubject_toCoordinates

/-- Reading one arm's death time is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_death (a : Arm) :
    Measurable (fun z : LatentSubject => z.death a) := by
  exact (measurable_pi_apply a).comp
    (((measurable_fst.comp measurable_snd).comp measurable_snd).comp
      measurable_latentSubject_toCoordinates)

/-- Reading one arm's censoring time is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_censor (a : Arm) :
    Measurable (fun z : LatentSubject => z.censor a) := by
  exact (measurable_pi_apply a).comp
    (((measurable_snd.comp measurable_snd).comp measurable_snd).comp
      measurable_latentSubject_toCoordinates)

/-- Reading the complete recurrence family is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_recurFamily :
    Measurable (fun z : LatentSubject => z.recur) :=
  (measurable_fst.comp measurable_snd).comp
    measurable_latentSubject_toCoordinates

/-- Reading the complete death-time family is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_deathFamily :
    Measurable (fun z : LatentSubject => z.death) :=
  ((measurable_fst.comp measurable_snd).comp measurable_snd).comp
    measurable_latentSubject_toCoordinates

/-- Reading the complete censoring family is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_censorFamily :
    Measurable (fun z : LatentSubject => z.censor) :=
  ((measurable_snd.comp measurable_snd).comp measurable_snd).comp
    measurable_latentSubject_toCoordinates

/-- Reading all non-assignment latent coordinates is measurable. -/
@[fun_prop]
lemma measurable_latentSubject_rest :
    Measurable (fun z : LatentSubject => (z.recur, z.death, z.censor)) :=
  measurable_latentSubject_recurFamily.prodMk
    (measurable_latentSubject_deathFamily.prodMk
      measurable_latentSubject_censorFamily)

/-- The nested product carrier used to assemble independent latent blocks. -/
abbrev LatentBlocks :=
  Arm × ((Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal)))

/-- Assemble the four product blocks into a latent subject. -/
def LatentSubject.ofBlocks (q : LatentBlocks) : LatentSubject where
  treatment := q.1
  recur := q.2.1
  death := q.2.2.1
  censor := q.2.2.2

@[simp]
lemma LatentSubject.toCoordinates_ofBlocks (q : LatentBlocks) :
    LatentSubject.toCoordinates (LatentSubject.ofBlocks q) = q := rfl

/-- Product-block assembly is measurable for the product-derived latent
measurable space. -/
@[fun_prop]
lemma LatentSubject.measurable_ofBlocks :
    Measurable LatentSubject.ofBlocks := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap LatentSubject.ofBlocks
    (MeasurableSpace.comap LatentSubject.toCoordinates inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact measurable_id.comap_le

structure ObsHistory where
  treatment : Arm -- @realizes O_i(observed treatment) @realizes A(observed label)
  exit : ℝ -- @realizes X_i(observed exit)
  deathInd : Bool -- @realizes Delta_i_D(observed death indicator)
  recur : RecurConfig -- @realizes N_i_obs(observed recurrence events with multiplicities)

/-- Product coordinates of an observed history. -/
def ObsHistory.toCoordinates (o : ObsHistory) :=
  (o.treatment, o.exit, o.deathInd, o.recur)

/-- Product-derived measurable structure on observed histories. -/
instance : MeasurableSpace ObsHistory :=
  MeasurableSpace.comap ObsHistory.toCoordinates inferInstance

/-- The complete observed coordinate map is measurable for the
product-derived structure. -/
@[fun_prop]
lemma measurable_obsHistory_toCoordinates :
    Measurable ObsHistory.toCoordinates := by
  apply Measurable.of_comap_le
  rfl

noncomputable def censorHorizon (z : LatentSubject) (a : Arm) : ℝ :=
  if z.censor a = ⊤ then 1 else min (z.censor a).toReal 1
  -- @realizes C_a(infinity remains retained through horizon)

/-- Evaluating a measurable finite family at a measurable arm is measurable. -/
lemma measurable_arm_eval {X : Type*} [MeasurableSpace X]
    (f : LatentSubject → Arm → X) (a : LatentSubject → Arm)
    (hf : Measurable f) (ha : Measurable a) :
    Measurable (fun z => f z (a z)) := by
  have heval : Measurable (fun q : (Arm → X) × Arm => q.1 q.2) := by
    apply measurable_from_prod_countable_left
    intro b
    exact measurable_pi_apply b
  exact heval.comp (hf.prodMk ha)

/-- The finite censoring horizon is measurable in both the latent subject and
the selected arm. -/
@[fun_prop]
lemma measurable_censorHorizon :
    Measurable (fun q : LatentSubject × Arm => censorHorizon q.1 q.2) := by
  have hc : Measurable (fun q : LatentSubject × Arm => q.1.censor q.2) := by
    have heval : Measurable
        (fun q : (Arm → ENNReal) × Arm => q.1 q.2) := by
      apply measurable_from_prod_countable_left
      intro a
      exact measurable_pi_apply a
    exact heval.comp
      (((((measurable_snd.comp measurable_snd).comp measurable_snd).comp
        measurable_latentSubject_toCoordinates).comp measurable_fst).prodMk
          measurable_snd)
  unfold censorHorizon
  apply Measurable.ite
  · exact measurableSet_eq_fun hc measurable_const
  · exact measurable_const
  · exact hc.ennreal_toReal.min measurable_const

/-- Put the event-time coordinate in the canonical increasing order. -/
noncomputable def RecurConfig.orderByTime (s : RecurConfig) : RecurConfig :=
  finiteSampleMap Prod.swap (orderByMarks (finiteSampleMap Prod.swap s))

/-- Canonical time ordering is measurable. -/
@[fun_prop]
lemma RecurConfig.measurable_orderByTime :
    Measurable RecurConfig.orderByTime := by
  exact (measurable_finiteSampleMap Prod.swap measurable_swap).comp
    (measurable_orderByMarks.comp
      (measurable_finiteSampleMap Prod.swap measurable_swap))

/-- The two-cell measurable partition that retains event times through a
fixed exit. -/
noncomputable def timeCutPartition (x : ℝ) :
    FiniteMeasurablePartition ℝ Bool where
  cell := fun t => decide (t ≤ x)
  measurable_cell := by
    change Measurable (fun t : ℝ => if t ≤ x then true else false)
    exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- Stable threshold filtering of a padded finite-event stream. -/
noncomputable def RecurConfig.paddedSelectedIndices
    (z : ℕ × (ℝ × (ℕ → ℝ × ℝ))) : Finset (Fin z.1) := by
  exact (timeCutPartition z.2.1).cellIndices true
    (streamToFiniteSample (z.1, z.2.2))

noncomputable def RecurConfig.paddedRestrictAt
    (z : ℕ × (ℝ × (ℕ → ℝ × ℝ))) : RecurConfig :=
  (timeCutPartition z.2.1).restrictCell true
    (streamToFiniteSample (z.1, z.2.2))

/-- Stable threshold filtering is measurable jointly in the declared input
length, threshold, and padded event stream. -/
@[fun_prop]
lemma RecurConfig.measurable_paddedRestrictAt :
    Measurable RecurConfig.paddedRestrictAt := by
  classical
  apply measurable_from_prod_countable_right
  intro n s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  rw [show (fun y : ℝ × (ℕ → ℝ × ℝ) =>
      RecurConfig.paddedRestrictAt (n, y)) ⁻¹' s =
      ⋃ t : Finset (Fin n),
        {y : ℝ × (ℕ → ℝ × ℝ) |
          RecurConfig.paddedSelectedIndices (n, y) = t} ∩
          (fun y : ℝ × (ℕ → ℝ × ℝ) =>
            fun k => (streamToFiniteSample (n, y.2)).points
              (t.orderIsoOfFin rfl k).1) ⁻¹'
              (fixedSizeEmbed t.card ⁻¹' s) by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro hy
      let t : Finset (Fin n) := RecurConfig.paddedSelectedIndices (n, y)
      refine ⟨t, rfl, ?_⟩
      change RecurConfig.paddedRestrictAt (n, y) ∈ s
      exact hy
    · rintro ⟨t, ht, hy⟩
      subst t
      change RecurConfig.paddedRestrictAt (n, y) ∈ s
      change RecurConfig.paddedRestrictAt (n, y) ∈ s at hy
      exact hy]
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.inter
  · have hregion : {y : ℝ × (ℕ → ℝ × ℝ) |
        RecurConfig.paddedSelectedIndices (n, y) = t} =
      ⋂ k : Fin n, if k ∈ t then
        {y | (y.2 k).1 ≤ y.1} else {y | (y.2 k).1 ≤ y.1}ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine Iff.trans Finset.ext_iff ?_
      simp only [RecurConfig.paddedSelectedIndices,
        FiniteMeasurablePartition.cellIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      apply forall_congr'
      intro k
      by_cases hkt : k ∈ t
      · simp_all [Finset.mem_filter, timeCutPartition, streamToFiniteSample,
          FiniteSample.points, FiniteSample.count]
        intro _
        exact Finset.mem_univ k
      · simp_all [Finset.mem_filter, timeCutPartition, streamToFiniteSample,
          FiniteSample.points, FiniteSample.count]
        exact Or.inl (Finset.mem_univ k)
    rw [hregion]
    apply MeasurableSet.iInter
    intro k
    split_ifs
    · exact measurableSet_le (measurable_fst.comp
        ((measurable_pi_apply (k : ℕ)).comp measurable_snd)) measurable_fst
    · exact (measurableSet_le (measurable_fst.comp
        ((measurable_pi_apply (k : ℕ)).comp measurable_snd)) measurable_fst).compl
  · have hst : MeasurableSet (fixedSizeEmbed t.card ⁻¹' s) := hs t.card
    apply hst.preimage
    apply measurable_pi_lambda
    intro k
    exact (measurable_pi_apply (((t.orderIsoOfFin rfl k).1 : Fin n) : ℕ)).comp
      measurable_snd

/-- Stop a finite recurrent-event configuration at the supplied observed exit.
The output contains exactly the events with time at most the exit and retains
their original relative order. -/
noncomputable def RecurConfig.stopAt (x : ℝ) (s : RecurConfig) : RecurConfig :=
  let padded := finiteSamplePaddedStream (0, 0) s
  RecurConfig.paddedRestrictAt (padded.1, x, padded.2)

/-- Stopping a finite configuration is jointly measurable in the threshold
and the configuration. -/
@[fun_prop]
lemma RecurConfig.measurable_stopAt :
    Measurable (fun z : ℝ × RecurConfig => z.2.stopAt z.1) := by
  have hpadded : Measurable
      (fun z : ℝ × RecurConfig => finiteSamplePaddedStream (0, 0) z.2) :=
    (finiteSamplePaddedStream_measurable (0, 0)).comp measurable_snd
  exact RecurConfig.measurable_paddedRestrictAt.comp
    (hpadded.fst.prodMk (measurable_fst.prodMk hpadded.snd))

noncomputable def observe (z : LatentSubject) : ObsHistory :=
  let x := min (z.death z.treatment) (censorHorizon z z.treatment)
  { treatment := z.treatment
    exit := x -- @realizes X_i(minimum death, censor, horizon)
    deathInd := decide (z.death z.treatment ≤ censorHorizon z z.treatment)
      -- @realizes Delta_i_D(death before censor and horizon)
    recur := (z.recur z.treatment).stopAt x }
      -- @realizes N_i_obs(recurrences through observed exit) @realizes O_i(observed tuple)


/-- The observed stopped history is a globally measurable function of the
latent subject. -/
@[fun_prop]
lemma measurable_observe : Measurable observe := by
  have ht : Measurable (fun z : LatentSubject => z.treatment) :=
    measurable_latentSubject_treatment
  have hdFamily : Measurable (fun z : LatentSubject => z.death) :=
    (((measurable_fst.comp measurable_snd).comp measurable_snd).comp
      measurable_latentSubject_toCoordinates)
  have hrFamily : Measurable (fun z : LatentSubject => z.recur) :=
    ((measurable_fst.comp measurable_snd).comp
      measurable_latentSubject_toCoordinates)
  have hd : Measurable (fun z : LatentSubject => z.death z.treatment) :=
    measurable_arm_eval _ _ hdFamily ht
  have hc : Measurable (fun z : LatentSubject => censorHorizon z z.treatment) :=
    measurable_censorHorizon.comp (measurable_id.prodMk ht)
  have hx : Measurable (fun z : LatentSubject =>
      min (z.death z.treatment) (censorHorizon z z.treatment)) := hd.min hc
  have hdelta : Measurable (fun z : LatentSubject =>
      decide (z.death z.treatment ≤ censorHorizon z z.treatment)) := by
    change Measurable (fun z : LatentSubject =>
      if z.death z.treatment ≤ censorHorizon z z.treatment then true else false)
    exact Measurable.ite (measurableSet_le hd hc) measurable_const measurable_const
  have hr : Measurable (fun z : LatentSubject => z.recur z.treatment) :=
    measurable_arm_eval _ _ hrFamily ht
  have hstop : Measurable (fun z : LatentSubject =>
      (z.recur z.treatment).stopAt
        (min (z.death z.treatment) (censorHorizon z z.treatment))) :=
    RecurConfig.measurable_stopAt.comp (hx.prodMk hr)
  rw [show Measurable observe ↔ Measurable (ObsHistory.toCoordinates ∘ observe) by
    exact ⟨fun h => measurable_obsHistory_toCoordinates.comp h,
      fun h => by
        rw [measurable_iff_comap_le]
        change MeasurableSpace.comap observe
          (MeasurableSpace.comap ObsHistory.toCoordinates inferInstance) ≤ _
        rw [MeasurableSpace.comap_comp]
        exact h.comap_le⟩]
  exact ht.prodMk (hx.prodMk (hdelta.prodMk hstop))

structure SubjectLaw where
  latent : Measure LatentSubject -- @realizes P(latent law)
  prob : latent Set.univ = 1
  observe_aemeasurable : AEMeasurable observe latent
    -- @realizes O(measurable stopped-history observation under the latent law)
  lam : Arm → ℝ → ℝ -- @realizes lambda_a(arm intensity carrier)
  hazard : Arm → ℝ → ℝ -- @realizes d_a(arm hazard carrier)
  p : Arm → ℝ -- @realizes p_a(known arm probabilities)
  g : Arm → ℝ -- @realizes g_a(endpoint coefficient carrier)

/-- Canonical finite Poisson configurations generated by a finite event-time
intensity, with the auxiliary ordering mark fixed at zero. -/
noncomputable def canonicalRecurrenceLawOf (ν : Measure ℝ)
    [IsFiniteMeasure ν] : Measure RecurConfig :=
  finiteMeasureMarkedPoissonLaw ν (Measure.dirac 0) (Measure.dirac 0) 1

/-- Stable restriction of a finite event sequence through a fixed exit.  It
retains the original relative order and is the restriction map appearing in
the finite-Poisson splitting theorem. -/
noncomputable def RecurConfig.restrictAt (x : ℝ) (s : RecurConfig) : RecurConfig :=
  (timeCutPartition x).restrictCell true s

/-- The jointly measurable stopping map is exactly the stable partition
restriction used by finite-Poisson splitting. -/
lemma RecurConfig.stopAt_eq_restrictAt (x : ℝ) (s : RecurConfig) :
    s.stopAt x = s.restrictAt x := by
  unfold RecurConfig.stopAt RecurConfig.paddedRestrictAt RecurConfig.restrictAt
  dsimp only
  rw [streamToFiniteSample_paddedStream]

/-- Stable restriction at a fixed exit has the exact thinned finite-Poisson
cell law supplied by partition splitting. -/
lemma canonicalRecurrenceLawOf_map_restrictAt
    (x : ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measure.map (RecurConfig.restrictAt x) (canonicalRecurrenceLawOf ν) =
      finiteMarkedPoissonSampleLaw
        ((timeCutPartition x).cellObservationLaw
          (normalizedFiniteMeasure ν (Measure.dirac 0)) true)
        (Measure.dirac 0)
        (finiteMeasureMass ν *
          (timeCutPartition x).cellMass
            (normalizedFiniteMeasure ν (Measure.dirac 0)) true) := by
  let p := timeCutPartition x
  let P := normalizedFiniteMeasure ν (Measure.dirac 0)
  let R : Measure ℝ := Measure.dirac 0
  let lam := finiteMeasureMass ν
  let μ := finiteMarkedPoissonSampleLaw P R lam
  let laws : Bool → Measure RecurConfig := fun b =>
    finiteMarkedPoissonSampleLaw (p.cellObservationLaw P b) R
      (lam * p.cellMass P b)
  have hsplit : Measure.map p.restrictPartition μ = Measure.pi laws := by
    exact p.map_restrictPartition_finiteMarkedPoissonSampleLaw P R lam
  have hcell : Measure.map (p.restrictCell true) μ = laws true := by
    calc
      Measure.map (p.restrictCell true) μ =
          Measure.map (Function.eval true)
            (Measure.map p.restrictPartition μ) := by
        rw [Measure.map_map (measurable_pi_apply true)
          p.measurable_restrictPartition]
        rfl
      _ = Measure.map (Function.eval true) (Measure.pi laws) := by rw [hsplit]
      _ = laws true := by
        rw [Measure.pi_map_eval]
        simp_rw [measure_univ]
        simp only [Finset.prod_const_one, one_smul]
  rw [show RecurConfig.restrictAt x =
    (timeCutPartition x).restrictCell true by rfl]
  unfold canonicalRecurrenceLawOf finiteMeasureMarkedPoissonLaw
  simpa only [p, P, R, lam, μ, laws, one_mul] using hcell

/-- The actual observed-history stopping map has the exact fixed-exit
finite-Poisson cell law. -/
lemma canonicalRecurrenceLawOf_map_stopAt
    (x : ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measure.map (RecurConfig.stopAt x) (canonicalRecurrenceLawOf ν) =
      finiteMarkedPoissonSampleLaw
        ((timeCutPartition x).cellObservationLaw
          (normalizedFiniteMeasure ν (Measure.dirac 0)) true)
        (Measure.dirac 0)
        (finiteMeasureMass ν *
          (timeCutPartition x).cellMass
            (normalizedFiniteMeasure ν (Measure.dirac 0)) true) := by
  rw [show RecurConfig.stopAt x = RecurConfig.restrictAt x by
    funext s
    exact RecurConfig.stopAt_eq_restrictAt x s]
  exact canonicalRecurrenceLawOf_map_restrictAt x ν

/-- Assemble independent treatment, recurrence, death, and censoring blocks
and map them to the latent-subject carrier. -/
noncomputable def latentProductLaw
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal)) : Measure LatentSubject :=
  Measure.map LatentSubject.ofBlocks
    (assignment.prod ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)))

/-- The assembled latent law is a probability law whenever each supplied
block is a probability law. -/
lemma latentProductLaw_univ
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] :
    latentProductLaw assignment recurLaw deathLaw censorLaw Set.univ = 1 := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  letI : IsProbabilityMeasure
      (assignment.prod ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))) :=
    inferInstance
  letI : IsProbabilityMeasure
      (latentProductLaw assignment recurLaw deathLaw censorLaw) :=
    Measure.isProbabilityMeasure_map LatentSubject.measurable_ofBlocks.aemeasurable
  exact measure_univ

/-- The product witness has exactly the supplied assignment marginal. -/
lemma latentProductLaw_map_treatment
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] :
    (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      LatentSubject.treatment = assignment := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  letI : IsProbabilityMeasure
      ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)) := inferInstance
  rw [latentProductLaw, Measure.map_map measurable_latentSubject_treatment
    LatentSubject.measurable_ofBlocks]
  change (assignment.prod
    ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))).fst = assignment
  exact Measure.fst_prod

/-- The product witness has exactly the supplied joint censoring marginal. -/
lemma latentProductLaw_map_censor
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] :
    (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      LatentSubject.censor = censorLaw := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  letI : IsProbabilityMeasure
      ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)) := inferInstance
  rw [latentProductLaw, Measure.map_map measurable_latentSubject_censorFamily
    LatentSubject.measurable_ofBlocks]
  change Measure.map (fun q : LatentBlocks => q.2.2.2)
    (assignment.prod ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))) = censorLaw
  calc
    _ = Measure.map (fun q => q.2.2)
        (Measure.map Prod.snd
          (assignment.prod ((Measure.pi recurLaw).prod
            (deathLaw.prod censorLaw)))) := by
      convert (Measure.map_map (measurable_snd.comp measurable_snd)
        measurable_snd).symm using 1 <;> rfl
    _ = Measure.map (fun q => q.2.2)
        ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = Measure.map Prod.snd
        (Measure.map Prod.snd
          ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))) := by
      convert (Measure.map_map measurable_snd measurable_snd).symm using 1 <;> rfl
    _ = Measure.map Prod.snd (deathLaw.prod censorLaw) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = censorLaw := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Each recurrence coordinate of the product witness has exactly its
supplied canonical marginal. -/
lemma latentProductLaw_map_recur
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] (a : Arm) :
    (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      (fun z => z.recur a) = recurLaw a := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  letI : IsProbabilityMeasure (deathLaw.prod censorLaw) := inferInstance
  letI : IsProbabilityMeasure
      ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)) := inferInstance
  rw [latentProductLaw, Measure.map_map (measurable_latentSubject_recur a)
    LatentSubject.measurable_ofBlocks]
  change Measure.map (fun q : LatentBlocks => q.2.1 a)
    (assignment.prod ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))) = recurLaw a
  calc
    _ = Measure.map (fun q => q.1 a)
        (Measure.map Prod.snd
          (assignment.prod ((Measure.pi recurLaw).prod
            (deathLaw.prod censorLaw)))) := by
      convert (Measure.map_map ((measurable_pi_apply a).comp measurable_fst)
        measurable_snd).symm using 1 <;> rfl
    _ = Measure.map (fun q => q.1 a)
        ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = Measure.map (Function.eval a)
        (Measure.map Prod.fst
          ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))) := by
      convert (Measure.map_map (measurable_pi_apply a) measurable_fst).symm using 1 <;> rfl
    _ = Measure.map (Function.eval a) (Measure.pi recurLaw) := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = recurLaw a := by
      rw [Measure.pi_map_eval]
      simp only [measure_univ, Finset.prod_const_one, one_smul]

/-- The product witness has exactly the supplied joint death-time marginal. -/
lemma latentProductLaw_map_death
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] :
    (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      LatentSubject.death = deathLaw := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  letI : IsProbabilityMeasure (deathLaw.prod censorLaw) := inferInstance
  letI : IsProbabilityMeasure
      ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)) := inferInstance
  rw [latentProductLaw, Measure.map_map measurable_latentSubject_deathFamily
    LatentSubject.measurable_ofBlocks]
  change Measure.map (fun q : LatentBlocks => q.2.2.1)
    (assignment.prod ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))) = deathLaw
  calc
    _ = Measure.map (fun q => q.2.1)
        (Measure.map Prod.snd
          (assignment.prod ((Measure.pi recurLaw).prod
            (deathLaw.prod censorLaw)))) := by
      convert (Measure.map_map (measurable_fst.comp measurable_snd)
        measurable_snd).symm using 1 <;> rfl
    _ = Measure.map (fun q => q.2.1)
        ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw)) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = Measure.map Prod.fst
        (Measure.map Prod.snd
          ((Measure.pi recurLaw).prod (deathLaw.prod censorLaw))) := by
      convert (Measure.map_map measurable_fst measurable_snd).symm using 1 <;> rfl
    _ = Measure.map Prod.fst (deathLaw.prod censorLaw) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = deathLaw := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Independence survives a measurable pushforward when both random variables
are read after that pushforward. -/
lemma IndepFun.of_map
    {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    {μ : Measure Ω} {φ : Ω → X} {f : X → Y} {g : X → Z}
    (hφ : Measurable φ) (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun (f ∘ φ) (g ∘ φ) μ) :
    IndepFun f g (μ.map φ) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  rw [Measure.map_apply hφ ((hs.preimage hf).inter (ht.preimage hg)),
    Measure.map_apply hφ (hs.preimage hf),
    Measure.map_apply hφ (ht.preimage hg)]
  change μ ((f ∘ φ) ⁻¹' s ∩ (g ∘ φ) ⁻¹' t) =
    μ ((f ∘ φ) ⁻¹' s) * μ ((g ∘ φ) ⁻¹' t)
  exact h s t hs ht

/-- Adding an independent probability-valued first coordinate does not alter
independence between two functions of the second coordinate. -/
lemma IndepFun.comp_snd_prod
    {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {f : Ω' → X} {g : Ω' → Y}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g ν) :
    IndepFun (f ∘ Prod.snd) (g ∘ Prod.snd) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have hst : MeasurableSet (f ⁻¹' s ∩ g ⁻¹' t) :=
    (hs.preimage hf).inter (ht.preimage hg)
  have hs' : MeasurableSet (f ⁻¹' s) := hs.preimage hf
  have ht' : MeasurableSet (g ⁻¹' t) := ht.preimage hg
  rw [show (f ∘ Prod.snd) ⁻¹' s ∩ (g ∘ Prod.snd) ⁻¹' t =
      Prod.snd ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) by ext q; rfl,
    ← Measure.map_apply measurable_snd hst,
    show (f ∘ Prod.snd) ⁻¹' s = Prod.snd ⁻¹' (f ⁻¹' s) by rfl,
    ← Measure.map_apply measurable_snd hs',
    show (g ∘ Prod.snd) ⁻¹' t = Prod.snd ⁻¹' (g ⁻¹' t) by rfl,
    ← Measure.map_apply measurable_snd ht',
    Measure.map_snd_prod, measure_univ, one_smul]
  exact h s t hs ht

/-- In the product witness, assignment is independent of all remaining latent
coordinates. -/
lemma latentProductLaw_randomAssignment
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] :
    IndepFun LatentSubject.treatment
      (fun z : LatentSubject => (z.recur, z.death, z.censor))
      (latentProductLaw assignment recurLaw deathLaw censorLaw) := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  let restLaw := (Measure.pi recurLaw).prod (deathLaw.prod censorLaw)
  letI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  apply IndepFun.of_map LatentSubject.measurable_ofBlocks
    measurable_latentSubject_treatment measurable_latentSubject_rest
  convert indepFun_prod (μ := assignment) (ν := restLaw)
    measurable_id measurable_id using 1 <;> rfl

/-- In the product witness, each recurrence coordinate is independent of its
same-arm death time. -/
lemma latentProductLaw_recurrenceDeathIndependence
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] (a : Arm) :
    IndepFun (fun z : LatentSubject => z.recur a)
      (fun z => z.death a)
      (latentProductLaw assignment recurLaw deathLaw censorLaw) := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  letI : IsProbabilityMeasure (Measure.pi recurLaw) := inferInstance
  letI : IsProbabilityMeasure (deathLaw.prod censorLaw) := inferInstance
  let restLaw := (Measure.pi recurLaw).prod (deathLaw.prod censorLaw)
  letI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  have hrest : IndepFun (fun q : (Arm → RecurConfig) ×
      ((Arm → ℝ) × (Arm → ENNReal)) => q.1 a)
      (fun q => q.2.1 a) restLaw := by
    have h := indepFun_prod (μ := Measure.pi recurLaw)
      (ν := deathLaw.prod censorLaw) measurable_id measurable_fst
    exact h.comp (measurable_pi_apply a) (measurable_pi_apply a)
  have hsource := IndepFun.comp_snd_prod
    (μ := assignment) (ν := restLaw)
    ((measurable_pi_apply a).comp measurable_fst)
    ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)) hrest
  apply IndepFun.of_map LatentSubject.measurable_ofBlocks
    (measurable_latentSubject_recur a) (measurable_latentSubject_death a)
  convert hsource using 1 <;> rfl

/-- In the product witness, each censoring coordinate is independent of the
same-arm recurrence and death pair. -/
lemma latentProductLaw_independentCensoring
    (assignment : Measure Arm)
    (recurLaw : Arm → Measure RecurConfig)
    (deathLaw : Measure (Arm → ℝ))
    (censorLaw : Measure (Arm → ENNReal))
    [IsProbabilityMeasure assignment]
    (hrecur : ∀ a, IsProbabilityMeasure (recurLaw a))
    [IsProbabilityMeasure deathLaw]
    [IsProbabilityMeasure censorLaw] (a : Arm) :
    IndepFun (fun z : LatentSubject => z.censor a)
      (fun z => (z.recur a, z.death a))
      (latentProductLaw assignment recurLaw deathLaw censorLaw) := by
  letI : ∀ a, IsProbabilityMeasure (recurLaw a) := hrecur
  let recurFamilyLaw := Measure.pi recurLaw
  letI : IsProbabilityMeasure recurFamilyLaw := by
    dsimp [recurFamilyLaw]
    infer_instance
  let leftLaw := recurFamilyLaw.prod deathLaw
  letI : IsProbabilityMeasure leftLaw := by
    dsimp [leftLaw]
    infer_instance
  let restLaw := recurFamilyLaw.prod (deathLaw.prod censorLaw)
  letI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  have hassoc : IndepFun
      (fun q : (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal)) => q.2.2 a)
      (fun q => (q.1 a, q.2.1 a)) restLaw := by
    have hprod := indepFun_prod (μ := leftLaw) (ν := censorLaw)
      (Measurable.prodMk ((measurable_pi_apply a).comp measurable_fst)
        ((measurable_pi_apply a).comp measurable_snd))
      (measurable_pi_apply a)
    have hprod' := hprod.symm
    have hmapped := IndepFun.of_map
      (μ := leftLaw.prod censorLaw)
      (φ := (MeasurableEquiv.prodAssoc :
        ((Arm → RecurConfig) × (Arm → ℝ)) × (Arm → ENNReal) ≃ᵐ
          (Arm → RecurConfig) × ((Arm → ℝ) × (Arm → ENNReal))))
      (f := fun q : (Arm → RecurConfig) ×
        ((Arm → ℝ) × (Arm → ENNReal)) => q.2.2 a)
      (g := fun q => (q.1 a, q.2.1 a))
      MeasurableEquiv.prodAssoc.measurable
      (by fun_prop) (by fun_prop) hprod'
    rw [Measure.prodAssoc_prod] at hmapped
    exact hmapped
  have hsource := IndepFun.comp_snd_prod
    (μ := assignment) (ν := restLaw)
    ((measurable_pi_apply a).comp (measurable_snd.comp measurable_snd))
    (((measurable_pi_apply a).comp measurable_fst).prodMk
      ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd))) hassoc
  apply IndepFun.of_map LatentSubject.measurable_ofBlocks
    (measurable_latentSubject_censor a)
    ((measurable_latentSubject_recur a).prodMk
      (measurable_latentSubject_death a))
  convert hsource using 1 <;> rfl

/-- The finite event-time intensity of a constant baseline recurrence rate. -/
noncomputable def baselineRecurrenceIntensity (lambda0 : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
    (fun _ => ENNReal.ofReal lambda0)

/-- A constant recurrence rate on the finite horizon has finite intensity. -/
lemma baselineRecurrenceIntensity_isFinite (lambda0 : ℝ) :
    IsFiniteMeasure (baselineRecurrenceIntensity lambda0) := by
  unfold baselineRecurrenceIntensity
  rw [withDensity_const]
  refine ⟨?_⟩
  rw [Measure.smul_apply]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    (measure_lt_top _ _)

/-- Build the constant-intensity, constant-hazard baseline from explicit
independent product blocks.  Assignment and joint censoring marginals are
inherited from the reference law; recurrences are canonical Poisson
configurations and death times are independent exponential variables. -/
noncomputable def SubjectLaw.baseline
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) : SubjectLaw := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  let assignment := reference.latent.map LatentSubject.treatment
  let censorLaw := reference.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun _ =>
    @canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
      (baselineRecurrenceIntensity_isFinite lambda0)
  let deathLaw : Measure (Arm → ℝ) := Measure.pi (fun _ => expMeasure d0)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ a : Arm, IsProbabilityMeasure (recurLaw a) := fun a => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ _a : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure deathLaw := by
    dsimp [deathLaw]
    infer_instance
  exact
    { latent := latentProductLaw assignment recurLaw deathLaw censorLaw
      prob := latentProductLaw_univ assignment recurLaw deathLaw censorLaw hrecur
      observe_aemeasurable := measurable_observe.aemeasurable
      lam := fun _ _ => lambda0
      hazard := fun _ _ => d0
      p := reference.p
      g := reference.g }

/-- Event-time intensity used by a treatment-only recurrence perturbation. -/
noncomputable def treatmentPerturbIntensity
    (base : SubjectLaw) (lam1 : ℝ → ℝ) (a : Arm) : Measure ℝ :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (if a then lam1 t else base.lam false t))

/-- Build a treatment-arm intensity perturbation from explicit product
blocks.  Assignment, joint death, and joint censoring marginals come from the
baseline; both recurrence arms are reconstructed from their canonical
Poisson laws. -/
noncomputable def SubjectLaw.perturbTreatment
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a)) : SubjectLaw := by
  letI : IsProbabilityMeasure base.latent := ⟨base.prob⟩
  let assignment := base.latent.map LatentSubject.treatment
  let deathLaw := base.latent.map LatentSubject.death
  let censorLaw := base.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun a =>
    @canonicalRecurrenceLawOf (treatmentPerturbIntensity base lam1 a) (hfinite a)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure deathLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_deathFamily.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ a : Arm, IsProbabilityMeasure (recurLaw a) := fun a => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  exact
    { latent := latentProductLaw assignment recurLaw deathLaw censorLaw
      prob := latentProductLaw_univ assignment recurLaw deathLaw censorLaw hrecur
      observe_aemeasurable := measurable_observe.aemeasurable
      lam := fun a => if a then lam1 else base.lam false
      hazard := base.hazard
      p := base.p
      g := base.g }

-- @env: S1
variable (c : ClassConstants) (P : SubjectLaw) (a : Arm)

noncomputable def observedLaw (P : SubjectLaw) : Measure ObsHistory :=
  P.latent.map observe -- @realizes P(observed law)

noncomputable def survival (P : SubjectLaw) (a : Arm) (t : ℝ) : ℝ :=
  Real.exp (-∫ u in (0 : ℝ)..t, P.hazard a u)
  -- @realizes S_a(exponential of negative integrated hazard)

noncomputable def retention (P : SubjectLaw) (a : Arm) (t : ℝ) : ℝ :=
  P.latent.real {z | ENNReal.ofReal t ≤ z.censor a} -- @realizes G_a(censor survival)

noncomputable def clinicalCount (z : LatentSubject) (a : Arm) (t : ℝ) : ℕ :=
  (z.recur a).countLE (min t (z.death a))
  -- @realizes N_a(recurrence count stopped at death)

noncomputable def armMean (P : SubjectLaw) (a : Arm) : ℝ :=
  ∫ t in (0 : ℝ)..1, survival P a t * P.lam a t
  -- @realizes mu_a(integral S times lambda)

-- @node: def:causal-target
noncomputable def causalTarget (P : SubjectLaw) : ℝ :=
  ∫ z, ((clinicalCount z true 1 : ℝ) - (clinicalCount z false 1 : ℝ)) ∂P.latent
  -- @realizes theta(latent expected treatment contrast)

-- @env: S2
variable (n : {m : ℕ // 3 ≤ m}) -- @realizes n(sample-size carrier constrained to n ≥ 3)
variable (i : {j : ℕ // 1 ≤ j ∧ j ≤ n.val}) -- @realizes i(values 1 through n)

noncomputable def sampleLaw (P : SubjectLaw) (n : ℕ) : Measure (Fin n → ObsHistory) :=
  Measure.pi (fun _ : Fin n => observedLaw P)

-- @node: ass:iid-sampling
def IidSampling (P : SubjectLaw) (n : ℕ) (law : Measure (Fin n → ObsHistory)) : Prop :=
  law = sampleLaw P n

-- @node: ass:random-assignment
def RandomAssignment (P : SubjectLaw) : Prop :=
  IndepFun LatentSubject.treatment
    (fun z : LatentSubject => (z.recur, z.death, z.censor)) P.latent

-- @node: ass:assignment-law
def AssignmentLaw (P : SubjectLaw) : Prop :=
  ∀ a : Arm, P.latent.real {z | z.treatment = a} = P.p a
  -- @realizes p_a(actual treatment probabilities)

-- @node: ass:treatment-overlap
def TreatmentOverlap (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, c.pMin ≤ P.p a -- @realizes p_a(lower range via p_min)

/-- The finite intensity measure on event times generated by one arm's
recurrence intensity. -/
noncomputable def recurrenceIntensity (P : SubjectLaw) (a : Arm) : Measure ℝ :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (P.lam a t))

/-- The canonical finite Poisson configuration law with the requested event
intensity and a deterministic auxiliary mark. -/
noncomputable def canonicalRecurrenceLaw (P : SubjectLaw) (a : Arm)
    [IsFiniteMeasure (recurrenceIntensity P a)] : Measure RecurConfig :=
  canonicalRecurrenceLawOf (recurrenceIntensity P a)

-- @node: ass:poisson-recurrence
def PoissonRecurrence (P : SubjectLaw) : Prop :=
  ∀ a : Arm,
    AEMeasurable (P.lam a) (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), 0 ≤ P.lam a t) ∧
    ∃ hν : IsFiniteMeasure (recurrenceIntensity P a),
      P.latent.map (fun z : LatentSubject => z.recur a) =
        @canonicalRecurrenceLaw P a hν
  -- @realizes N_a_star(full canonical Poisson configuration law with deterministic mark and ordering)

/-- The concrete constant-rate baseline has the full canonical Poisson
configuration law in each arm. -/
lemma SubjectLaw.baseline_poissonRecurrence
    (reference : SubjectLaw) (lambda0 d0 : ℝ)
    (hlambda0 : 0 ≤ lambda0) (hd0 : 0 < d0) :
    PoissonRecurrence (SubjectLaw.baseline reference lambda0 d0 hd0) := by
  intro a
  refine ⟨?_, ?_, ?_⟩
  · change AEMeasurable (fun _ : ℝ => lambda0)
      (volume.restrict (Set.Ioc (0 : ℝ) 1))
    exact measurable_const.aemeasurable
  · change ∀ᵐ _t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), 0 ≤ lambda0
    exact Filter.Eventually.of_forall (fun _ => hlambda0)
  let hν : IsFiniteMeasure
      (recurrenceIntensity (SubjectLaw.baseline reference lambda0 d0 hd0) a) := by
    change IsFiniteMeasure (baselineRecurrenceIntensity lambda0)
    exact baselineRecurrenceIntensity_isFinite lambda0
  refine ⟨hν, ?_⟩
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  let assignment := reference.latent.map LatentSubject.treatment
  let censorLaw := reference.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun _ =>
    @canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
      (baselineRecurrenceIntensity_isFinite lambda0)
  let deathLaw : Measure (Arm → ℝ) := Measure.pi (fun _ => expMeasure d0)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ b : Arm, IsProbabilityMeasure (recurLaw b) := fun _ => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ _b : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure deathLaw := by
    dsimp [deathLaw]
    infer_instance
  have hconfig : (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      (fun z => z.recur a) = @canonicalRecurrenceLaw
        (SubjectLaw.baseline reference lambda0 d0 hd0) a hν := by
    rw [latentProductLaw_map_recur assignment recurLaw deathLaw censorLaw hrecur a]
    rfl
  exact hconfig

/-- The concrete treatment perturbation has the full canonical Poisson
configuration law generated by its perturbed intensity in each arm. -/
lemma SubjectLaw.perturbTreatment_poissonRecurrence
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a))
    (hregular : ∀ a : Arm,
      AEMeasurable (if a then lam1 else base.lam false)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
        0 ≤ (if a then lam1 else base.lam false) t)) :
    PoissonRecurrence (SubjectLaw.perturbTreatment base lam1 hfinite) := by
  intro a
  refine ⟨(hregular a).1, (hregular a).2, ?_⟩
  have hint : recurrenceIntensity
      (SubjectLaw.perturbTreatment base lam1 hfinite) a =
      treatmentPerturbIntensity base lam1 a := by
    unfold recurrenceIntensity treatmentPerturbIntensity
    congr 2
    funext t
    cases a <;> rfl
  let hν : IsFiniteMeasure
      (recurrenceIntensity (SubjectLaw.perturbTreatment base lam1 hfinite) a) := by
    rw [hint]
    exact hfinite a
  refine ⟨hν, ?_⟩
  letI : IsProbabilityMeasure base.latent := ⟨base.prob⟩
  let assignment := base.latent.map LatentSubject.treatment
  let deathLaw := base.latent.map LatentSubject.death
  let censorLaw := base.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun b =>
    @canonicalRecurrenceLawOf (treatmentPerturbIntensity base lam1 b) (hfinite b)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure deathLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_deathFamily.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ b : Arm, IsProbabilityMeasure (recurLaw b) := fun b => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  have hconfig : (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      (fun z => z.recur a) = @canonicalRecurrenceLaw
        (SubjectLaw.perturbTreatment base lam1 hfinite) a hν := by
    rw [latentProductLaw_map_recur assignment recurLaw deathLaw censorLaw hrecur a]
    simp only [recurLaw, canonicalRecurrenceLaw, hint]
  exact hconfig

-- @node: ass:death-hazard
def DeathHazard (P : SubjectLaw) : Prop :=
  (∀ a : Arm, IntervalIntegrable (P.hazard a) volume 0 1) ∧
  (∀ a t, t ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ P.hazard a t) ∧
  (∀ a : Arm, (P.latent.map (fun z => z.death a)) ≪ (volume : Measure ℝ)) ∧
  (∀ a t, t ∈ Set.Icc (0 : ℝ) 1 →
    P.latent.real {z | t ≤ z.death a} = survival P a t) ∧
  (∀ a : Arm, P.latent.real {z | (1 : ℝ) < z.death a} = survival P a 1)
  -- @realizes D_a(survival induced by hazard) @realizes d_a(nonnegative locally integrable)

/-- An exponential law has a Lebesgue density. -/
lemma expMeasure_absolutelyContinuous (d : ℝ) :
    expMeasure d ≪ (volume : Measure ℝ) := by
  unfold expMeasure gammaMeasure
  exact withDensity_absolutelyContinuous _ _

/-- The strict upper tail of a positive-rate exponential law. -/
lemma expMeasure_real_Ioi (d : ℝ) (hd : 0 < d) (t : ℝ) (ht : 0 ≤ t) :
    (expMeasure d).real (Set.Ioi t) = Real.exp (-(d * t)) := by
  letI : IsProbabilityMeasure (expMeasure d) := isProbabilityMeasure_expMeasure hd
  have hcomp := measureReal_add_measureReal_compl
    (μ := expMeasure d) (s := Set.Iic t) measurableSet_Iic
  rw [show (Set.Iic t)ᶜ = Set.Ioi t by ext x; simp] at hcomp
  rw [← cdf_eq_real, cdf_expMeasure_eq hd, if_pos ht] at hcomp
  have huniv : (expMeasure d).real Set.univ = 1 := by
    simp [measureReal_def]
  rw [huniv] at hcomp
  linarith

/-- The closed upper tail of a positive-rate exponential law.  Absolute
continuity removes the endpoint atom. -/
lemma expMeasure_real_Ici (d : ℝ) (hd : 0 < d) (t : ℝ) (ht : 0 ≤ t) :
    (expMeasure d).real (Set.Ici t) = Real.exp (-(d * t)) := by
  letI : IsProbabilityMeasure (expMeasure d) := isProbabilityMeasure_expMeasure hd
  have hset : Set.Ici t = {t} ∪ Set.Ioi t := by
    ext x
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
  rw [hset]
  rw [measureReal_union (μ := expMeasure d)
    (s₁ := {t}) (s₂ := Set.Ioi t)
    (Set.disjoint_left.2 (by
      intro y hy hyt
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact lt_irrefl t hyt)) measurableSet_Ioi
    (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [measureReal_def, expMeasure_absolutelyContinuous d (measure_singleton t)]
  simp only [ENNReal.toReal_zero, zero_add, expMeasure_real_Ioi d hd t ht]

/-- Each death coordinate of the concrete baseline has exactly the requested
positive-rate exponential marginal. -/
lemma SubjectLaw.baseline_map_death
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) (a : Arm) :
    (SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
      (fun z => z.death a) = expMeasure d0 := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  let assignment := reference.latent.map LatentSubject.treatment
  let censorLaw := reference.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun _ =>
    @canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
      (baselineRecurrenceIntensity_isFinite lambda0)
  let deathLaw : Measure (Arm → ℝ) := Measure.pi (fun _ => expMeasure d0)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ b : Arm, IsProbabilityMeasure (recurLaw b) := fun _ => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ _b : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure (expMeasure d0) :=
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure deathLaw := by
    dsimp [deathLaw]
    infer_instance
  have hfamily :
      (SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
        LatentSubject.death = deathLaw := by
    change (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      LatentSubject.death = deathLaw
    exact latentProductLaw_map_death assignment recurLaw deathLaw censorLaw hrecur
  calc
    _ = Measure.map (Function.eval a)
        ((SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
          LatentSubject.death) := by
      rw [Measure.map_map (measurable_pi_apply a)
        measurable_latentSubject_deathFamily]
      rfl
    _ = Measure.map (Function.eval a) deathLaw := by rw [hfamily]
    _ = expMeasure d0 := by
      change Measure.map (Function.eval a)
        (Measure.pi (fun _ : Arm => expMeasure d0)) = expMeasure d0
      rw [Measure.pi_map_eval]
      rw [measure_univ]
      simp only [Finset.prod_const_one, one_smul]

/-- The concrete constant-rate baseline satisfies the complete death-hazard
atom, including the horizon tail convention used by observed histories. -/
lemma SubjectLaw.baseline_deathHazard
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) :
    DeathHazard (SubjectLaw.baseline reference lambda0 d0 hd0) := by
  have hmarg : ∀ a : Arm,
      (SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
        (fun z => z.death a) = expMeasure d0 :=
    SubjectLaw.baseline_map_death reference lambda0 d0 hd0
  have hsurv : ∀ (a : Arm) (t : ℝ),
      survival (SubjectLaw.baseline reference lambda0 d0 hd0) a t =
        Real.exp (-(d0 * t)) := by
    intro a t
    simp only [survival, SubjectLaw.baseline]
    rw [intervalIntegral.integral_const]
    simp
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact intervalIntegrable_const
  · intro a t ht
    exact hd0.le
  · intro a
    rw [hmarg a]
    exact expMeasure_absolutelyContinuous d0
  · intro a t ht
    have hmap := Measure.map_apply
      (measurable_latentSubject_death a) measurableSet_Ici
      (μ := (SubjectLaw.baseline reference lambda0 d0 hd0).latent)
      (s := Set.Ici t)
    rw [hmarg a] at hmap
    rw [measureReal_def]
    change ((SubjectLaw.baseline reference lambda0 d0 hd0).latent
      ((fun z => z.death a) ⁻¹' Set.Ici t)).toReal = _
    rw [← hmap]
    change (expMeasure d0).real (Set.Ici t) = _
    rw [expMeasure_real_Ici d0 hd0 t ht.1, hsurv]
  · intro a
    have hmap := Measure.map_apply
      (measurable_latentSubject_death a) measurableSet_Ioi
      (μ := (SubjectLaw.baseline reference lambda0 d0 hd0).latent)
      (s := Set.Ioi (1 : ℝ))
    rw [hmarg a] at hmap
    rw [measureReal_def]
    change ((SubjectLaw.baseline reference lambda0 d0 hd0).latent
      ((fun z => z.death a) ⁻¹' Set.Ioi (1 : ℝ))).toReal = _
    rw [← hmap]
    change (expMeasure d0).real (Set.Ioi 1) = _
    rw [expMeasure_real_Ioi d0 hd0 1 (by norm_num), hsurv]

/-- The death-hazard atom depends only on the hazard function and the
coordinate death marginals. -/
lemma DeathHazard.of_hazard_eq_deathMarginals_eq
    {P Q : SubjectLaw} (hP : DeathHazard P)
    (hhazard : Q.hazard = P.hazard)
    (hdeath : ∀ a : Arm,
      Q.latent.map (fun z => z.death a) =
        P.latent.map (fun z => z.death a)) :
    DeathHazard Q := by
  have hsurv : ∀ (a : Arm) (t : ℝ), survival Q a t = survival P a t := by
    intro a t
    simp only [survival, hhazard]
  have htail : ∀ (a : Arm) (s : Set ℝ), MeasurableSet s →
      Q.latent.real ((fun z => z.death a) ⁻¹' s) =
        P.latent.real ((fun z => z.death a) ⁻¹' s) := by
    intro a s hs
    rw [measureReal_def, measureReal_def]
    rw [← Measure.map_apply (measurable_latentSubject_death a) hs,
      hdeath a,
      Measure.map_apply (measurable_latentSubject_death a) hs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hhazard] using hP.1
  · simpa only [hhazard] using hP.2.1
  · intro a
    rw [hdeath a]
    exact hP.2.2.1 a
  · intro a t ht
    change Q.latent.real ((fun z => z.death a) ⁻¹' Set.Ici t) = _
    rw [htail a (Set.Ici t) measurableSet_Ici]
    have hp := hP.2.2.2.1 a t ht
    change P.latent.real ((fun z => z.death a) ⁻¹' Set.Ici t) = _ at hp
    rw [hp, hsurv]
  · intro a
    change Q.latent.real ((fun z => z.death a) ⁻¹' Set.Ioi 1) = _
    rw [htail a (Set.Ioi 1) measurableSet_Ioi]
    have hp := hP.2.2.2.2 a
    change P.latent.real ((fun z => z.death a) ⁻¹' Set.Ioi 1) = _ at hp
    rw [hp, hsurv]

-- @node: ass:recurrence-death-independence
def RecurrenceDeathIndependence (P : SubjectLaw) : Prop :=
  ∀ a : Arm, IndepFun (fun z : LatentSubject => z.recur a)
    (fun z => z.death a) P.latent

-- @node: ass:independent-censoring
def IndependentCensoring (P : SubjectLaw) : Prop :=
  ∀ a : Arm, IndepFun (fun z : LatentSubject => z.censor a)
    (fun z => (z.recur a, z.death a)) P.latent

/-- The baseline product construction discharges assignment independence and
same-arm recurrence/death independence structurally. -/
lemma SubjectLaw.baseline_productIndependence
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) :
    RandomAssignment (SubjectLaw.baseline reference lambda0 d0 hd0) ∧
    RecurrenceDeathIndependence
      (SubjectLaw.baseline reference lambda0 d0 hd0) ∧
    IndependentCensoring
      (SubjectLaw.baseline reference lambda0 d0 hd0) := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  let assignment := reference.latent.map LatentSubject.treatment
  let censorLaw := reference.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun _ =>
    @canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
      (baselineRecurrenceIntensity_isFinite lambda0)
  let deathLaw : Measure (Arm → ℝ) := Measure.pi (fun _ => expMeasure d0)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ b : Arm, IsProbabilityMeasure (recurLaw b) := fun _ => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ _b : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure deathLaw := by
    dsimp [deathLaw]
    infer_instance
  constructor
  · change IndepFun LatentSubject.treatment
      (fun z : LatentSubject => (z.recur, z.death, z.censor))
      (latentProductLaw assignment recurLaw deathLaw censorLaw)
    exact latentProductLaw_randomAssignment assignment recurLaw deathLaw censorLaw hrecur
  · constructor
    · intro a
      change IndepFun (fun z : LatentSubject => z.recur a)
        (fun z => z.death a)
        (latentProductLaw assignment recurLaw deathLaw censorLaw)
      exact latentProductLaw_recurrenceDeathIndependence
        assignment recurLaw deathLaw censorLaw hrecur a
    · intro a
      change IndepFun (fun z : LatentSubject => z.censor a)
        (fun z => (z.recur a, z.death a))
        (latentProductLaw assignment recurLaw deathLaw censorLaw)
      exact latentProductLaw_independentCensoring
        assignment recurLaw deathLaw censorLaw hrecur a

/-- The treatment perturbation product construction discharges assignment
independence and same-arm recurrence/death independence structurally. -/
lemma SubjectLaw.perturbTreatment_productIndependence
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a)) :
    RandomAssignment (SubjectLaw.perturbTreatment base lam1 hfinite) ∧
    RecurrenceDeathIndependence
      (SubjectLaw.perturbTreatment base lam1 hfinite) ∧
    IndependentCensoring
      (SubjectLaw.perturbTreatment base lam1 hfinite) := by
  letI : IsProbabilityMeasure base.latent := ⟨base.prob⟩
  let assignment := base.latent.map LatentSubject.treatment
  let deathLaw := base.latent.map LatentSubject.death
  let censorLaw := base.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun b =>
    @canonicalRecurrenceLawOf (treatmentPerturbIntensity base lam1 b) (hfinite b)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure deathLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_deathFamily.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ b : Arm, IsProbabilityMeasure (recurLaw b) := fun b => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  constructor
  · change IndepFun LatentSubject.treatment
      (fun z : LatentSubject => (z.recur, z.death, z.censor))
      (latentProductLaw assignment recurLaw deathLaw censorLaw)
    exact latentProductLaw_randomAssignment assignment recurLaw deathLaw censorLaw hrecur
  · constructor
    · intro a
      change IndepFun (fun z : LatentSubject => z.recur a)
        (fun z => z.death a)
        (latentProductLaw assignment recurLaw deathLaw censorLaw)
      exact latentProductLaw_recurrenceDeathIndependence
        assignment recurLaw deathLaw censorLaw hrecur a
    · intro a
      change IndepFun (fun z : LatentSubject => z.censor a)
        (fun z => (z.recur a, z.death a))
        (latentProductLaw assignment recurLaw deathLaw censorLaw)
      exact latentProductLaw_independentCensoring
        assignment recurLaw deathLaw censorLaw hrecur a

/-- The baseline preserves the reference assignment and joint censoring
marginals exactly. -/
lemma SubjectLaw.baseline_preserves_marginals
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0) :
    (SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
        LatentSubject.treatment = reference.latent.map LatentSubject.treatment ∧
    (SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
        LatentSubject.censor = reference.latent.map LatentSubject.censor := by
  letI : IsProbabilityMeasure reference.latent := ⟨reference.prob⟩
  let assignment := reference.latent.map LatentSubject.treatment
  let censorLaw := reference.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun _ =>
    @canonicalRecurrenceLawOf (baselineRecurrenceIntensity lambda0)
      (baselineRecurrenceIntensity_isFinite lambda0)
  let deathLaw : Measure (Arm → ℝ) := Measure.pi (fun _ => expMeasure d0)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ b : Arm, IsProbabilityMeasure (recurLaw b) := fun _ => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  letI : ∀ _b : Arm, IsProbabilityMeasure (expMeasure d0) := fun _ =>
    isProbabilityMeasure_expMeasure hd0
  letI : IsProbabilityMeasure deathLaw := by
    dsimp [deathLaw]
    infer_instance
  constructor
  · change (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      LatentSubject.treatment = assignment
    exact latentProductLaw_map_treatment assignment recurLaw deathLaw censorLaw hrecur
  · change (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      LatentSubject.censor = censorLaw
    exact latentProductLaw_map_censor assignment recurLaw deathLaw censorLaw hrecur

/-- The treatment perturbation preserves the baseline assignment, joint death,
and joint censoring marginals exactly. -/
lemma SubjectLaw.perturbTreatment_preserves_marginals
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a)) :
    (SubjectLaw.perturbTreatment base lam1 hfinite).latent.map
        LatentSubject.treatment = base.latent.map LatentSubject.treatment ∧
    (SubjectLaw.perturbTreatment base lam1 hfinite).latent.map
        LatentSubject.death = base.latent.map LatentSubject.death ∧
    (SubjectLaw.perturbTreatment base lam1 hfinite).latent.map
        LatentSubject.censor = base.latent.map LatentSubject.censor := by
  letI : IsProbabilityMeasure base.latent := ⟨base.prob⟩
  let assignment := base.latent.map LatentSubject.treatment
  let deathLaw := base.latent.map LatentSubject.death
  let censorLaw := base.latent.map LatentSubject.censor
  let recurLaw : Arm → Measure RecurConfig := fun b =>
    @canonicalRecurrenceLawOf (treatmentPerturbIntensity base lam1 b) (hfinite b)
  letI : IsProbabilityMeasure assignment :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_treatment.aemeasurable
  letI : IsProbabilityMeasure deathLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_deathFamily.aemeasurable
  letI : IsProbabilityMeasure censorLaw :=
    Measure.isProbabilityMeasure_map measurable_latentSubject_censorFamily.aemeasurable
  have hrecur : ∀ b : Arm, IsProbabilityMeasure (recurLaw b) := fun b => by
    dsimp [recurLaw, canonicalRecurrenceLawOf]
    infer_instance
  constructor
  · change (latentProductLaw assignment recurLaw deathLaw censorLaw).map
      LatentSubject.treatment = assignment
    exact latentProductLaw_map_treatment assignment recurLaw deathLaw censorLaw hrecur
  · constructor
    · change (latentProductLaw assignment recurLaw deathLaw censorLaw).map
        LatentSubject.death = deathLaw
      exact latentProductLaw_map_death assignment recurLaw deathLaw censorLaw hrecur
    · change (latentProductLaw assignment recurLaw deathLaw censorLaw).map
        LatentSubject.censor = censorLaw
      exact latentProductLaw_map_censor assignment recurLaw deathLaw censorLaw hrecur

/-- A treatment-only recurrence perturbation preserves the death-hazard atom
whenever its base law satisfies it. -/
lemma SubjectLaw.perturbTreatment_deathHazard
    (base : SubjectLaw) (lam1 : ℝ → ℝ)
    (hfinite : ∀ a : Arm, IsFiniteMeasure
      (treatmentPerturbIntensity base lam1 a))
    (hbase : DeathHazard base) :
    DeathHazard (SubjectLaw.perturbTreatment base lam1 hfinite) := by
  have hfamily :
      (SubjectLaw.perturbTreatment base lam1 hfinite).latent.map
          LatentSubject.death =
        base.latent.map LatentSubject.death :=
    (SubjectLaw.perturbTreatment_preserves_marginals
      base lam1 hfinite).2.1
  apply DeathHazard.of_hazard_eq_deathMarginals_eq hbase
  · rfl
  · intro a
    calc
      (SubjectLaw.perturbTreatment base lam1 hfinite).latent.map
          (fun z => z.death a) =
          Measure.map (Function.eval a)
            ((SubjectLaw.perturbTreatment base lam1 hfinite).latent.map
              LatentSubject.death) := by
        rw [Measure.map_map (measurable_pi_apply a)
          measurable_latentSubject_deathFamily]
        rfl
      _ = Measure.map (Function.eval a)
          (base.latent.map LatentSubject.death) := by rw [hfamily]
      _ = base.latent.map (fun z => z.death a) := by
        rw [Measure.map_map (measurable_pi_apply a)
          measurable_latentSubject_deathFamily]
        rfl

-- @node: ass:recurrence-bounds
def RecurrenceBounds (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    c.lambdaMin ≤ P.lam a t ∧ P.lam a t ≤ c.lambdaMax
    -- @realizes lambda_a(pointwise intensity band)

-- @node: ass:death-bounds
def DeathBounds (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    c.dMin ≤ P.hazard a t ∧ P.hazard a t ≤ c.dMax
    -- @realizes d_a(pointwise hazard band)

def HolderSeminormLe (k : ℕ) (γ L : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ k f (Set.Icc (0 : ℝ) 1) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) x -
        iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) y| ≤ L * |x - y| ^ γ

-- @node: ass:recurrence-holder
def RecurrenceHolder (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Llambda (P.lam a)
  -- @realizes lambda_a(Hölder smoothness)

-- @node: ass:death-holder
def DeathHolder (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Ld (P.hazard a)
  -- @realizes d_a(Hölder smoothness)

-- @node: ass:endpoint-retention
def EndpointRetention (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, ∀ x : ℝ, 0 < x → x ≤ c.x0 →
    |retention P a (1 - x) / (P.g a * x ^ c.kappa) - 1| ≤ c.LG * x ^ c.rho
  -- @realizes G_a(second-order endpoint tail) @realizes g_a(tail coefficient)

-- @node: ass:tail-envelope-small
def TailEnvelopeSmall (c : ClassConstants) : Prop :=
  c.LG * c.x0 ^ c.rho ≤ 1 / 2

-- @node: ass:endpoint-coefficient-bounds
def EndpointCoefficientBounds (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, c.gMin ≤ P.g a ∧ P.g a ≤ c.gMax
  -- @realizes g_a(coefficient range)

-- @node: ass:interior-retention
def InteriorRetention (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) (1 - c.x0), c.Gint ≤ retention P a t
  -- @realizes G_a(interior lower bound)

-- @node: ass:positive-horizon-retention
def PositiveHorizonRetention (c : ClassConstants) (P : SubjectLaw) : Prop :=
  ∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1, c.Ghor ≤ retention P a t
  -- @realizes G_a(positive horizon lower bound)

-- @node: def:model-class
structure ModelClass (c : ClassConstants) (P : SubjectLaw) : Prop where
  iid : ∀ n, IidSampling P n (sampleLaw P n)
  randomAssignment : RandomAssignment P
  assignmentLaw : AssignmentLaw P
  treatmentOverlap : TreatmentOverlap c P
  poissonRecurrence : PoissonRecurrence P
  deathHazard : DeathHazard P
  recurrenceDeathIndependence : RecurrenceDeathIndependence P
  independentCensoring : IndependentCensoring P
  recurrenceBounds : RecurrenceBounds c P
  deathBounds : DeathBounds c P
  recurrenceHolder : RecurrenceHolder c P
  deathHolder : DeathHolder c P
  endpointRetention : EndpointRetention c P
  tailEnvelopeSmall : TailEnvelopeSmall c
  endpointCoefficientBounds : EndpointCoefficientBounds c P
  interiorRetention : InteriorRetention c P
  -- @realizes mathcalP(exact conjunction of model atoms)

noncomputable def continuationGram (ell : ℕ) : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ :=
  fun j m => ((2 : ℝ) ^ (m.val + j.val + 1) - 1) / (m.val + j.val + 1)

noncomputable def continuationRhs (ell : ℕ) : Fin (ell + 1) → ℝ :=
  fun j => 1 / (j.val + 1)

-- @node: def:continuation-polynomial
noncomputable def continuationPoly (ell : ℕ) (x : ℝ) : ℝ :=
  ∑ m : Fin (ell + 1),
    (∑ j : Fin (ell + 1), ((continuationGram ell)⁻¹) m j * continuationRhs ell j) * x ^ m.val
  -- @realizes k_ell(moment-matching polynomial)

-- @node: def:continuation-weight
noncomputable def continuationWeight (ell : ℕ) (h t : ℝ) : ℝ :=
  if h = 0 then 1 else
    (if t ≤ 1 - h then 1 else 0) +
      (if 1 - 2 * h ≤ t ∧ t ≤ 1 - h then continuationPoly ell ((1 - t) / h) else 0)
  -- @realizes w_h(two-piece continuation weight)

-- @node: def:bandwidth
noncomputable def bandwidth (c : ClassConstants) (n : ℕ) : ℝ :=
  min (c.x0 / 2) (if c.kappa ≤ 1 then
    (n : ℝ) ^ (-(1 / (2 * c.beta + 2))) else
    (n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1))))
  -- @realizes h_n(endpoint bandwidth)

-- @node: def:variance-factor
noncomputable def varianceFactor (c : ClassConstants) (h : ℝ) : ℝ :=
  if c.kappa < 1 then 1 else if c.kappa = 1 then 1 + Real.log (1 / h)
  else h ^ (1 - c.kappa)
  -- @realizes B_kappa(three rate regimes)

-- @node: def:risk-scale
noncomputable def riskScale (c : ClassConstants) (n : ℕ) : ℝ :=
  if c.kappa < 1 then (n : ℝ)⁻¹ else if c.kappa = 1 then
    Real.log n / n else
    (n : ℝ) ^ (-((2 * c.beta + 2) / (2 * c.beta + c.kappa + 1)))
  -- @realizes r_n(three squared-risk regimes)

-- @env: S3
variable (alpha : ℝ) -- @realizes alpha(real miscoverage parameter; range in theorem signatures)

noncomputable def minimaxRisk (c : ClassConstants) (n : ℕ) : ℝ :=
  (Causalean.Stat.minimaxValueENNReal
    (fun (f : {f : (Fin n → ObsHistory) → ℝ // Measurable f})
      (P : {P : SubjectLaw // ModelClass c P}) =>
      Causalean.Stat.sqRiskLIntegral (sampleLaw P.1 n) f.1 (causalTarget P.1))).toReal
  -- @realizes R_n(all-measurable-estimator minimax risk)

-- @node: def:endpoint-relaxed-superclass
def RelaxedClass (c : ClassConstants) (P : SubjectLaw) : Prop :=
  (∀ n, IidSampling P n (sampleLaw P n)) ∧ RandomAssignment P ∧
  AssignmentLaw P ∧ TreatmentOverlap c P ∧ IndependentCensoring P ∧
  EndpointRetention c P ∧ TailEnvelopeSmall c ∧
  EndpointCoefficientBounds c P ∧ InteriorRetention c P ∧
  (∀ a : Arm, Integrable (fun z : LatentSubject => (clinicalCount z a 1 : ℝ) ^ 2) P.latent) ∧
  (∀ a : Arm, Tendsto
    (fun t : ℝ => ∫ z, (clinicalCount z a t : ℝ) ∂P.latent)
    (nhdsWithin 1 (Set.Iio 1))
    (nhds (∫ z, (clinicalCount z a 1 : ℝ) ∂P.latent)))
  -- @realizes mathcalQ_rel(endpoint-relaxed causal class)

noncomputable def relaxedTarget (P : SubjectLaw) : ℝ := causalTarget P
  -- @realizes vartheta(endpoint-relaxed count contrast)

def ConvergesInLaw (μ : ℕ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
    Tendsto (fun n => ∫ x, f x ∂μ n) atTop (nhds (∫ x, f x ∂ν))

noncomputable def relaxedMinimaxRisk (c : ClassConstants) (n : ℕ) : ENNReal :=
  (Causalean.Stat.minimaxValueENNReal
    (fun (f : {f : (Fin n → ObsHistory) → ℝ // Measurable f})
      (P : {P : SubjectLaw // RelaxedClass c P}) =>
      Causalean.Stat.sqRiskLIntegral (sampleLaw P.1 n) f.1 (relaxedTarget P.1)))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
