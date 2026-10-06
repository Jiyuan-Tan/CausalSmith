module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.MarkedFactorial
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.StreamLaw
public import Causalean.Mathlib.Probability.Poisson.InverseMoments
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk
public import Mathlib.Probability.Distributions.Uniform

/-! Exact count bridges from the mixed-stream encoding to finite Poisson samples. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

attribute [local instance] Classical.propDecidable

/-- For [the specified inputs and assumptions](hyp:d,pool,j,arrived,ones), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def streamEvent {d : ℕ} (pool : Fin 3) (j : Cell d)
    (arrived ones : Bool) : Set (ObsRecord d × Fin 3) :=
  {z | z.2 = pool ∧ z.1.A = j.1 ∧ z.1.X = j.2.1 ∧ z.1.S = j.2.2 ∧
    (arrived = false ∨ z.1.R = true) ∧ (ones = false ∨ z.1.RY = true)}

/-- For [the specified inputs and assumptions](hyp:d,j,arrived,ones), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def obsStreamEvent {d : ℕ} (j : Cell d) (arrived ones : Bool) : Set (ObsRecord d) :=
  {z | z.A = j.1 ∧ z.X = j.2.1 ∧ z.S = j.2.2 ∧
    (arrived = false ∨ z.R = true) ∧ (ones = false ∨ z.RY = true)}

/-- For [the specified inputs and assumptions](hyp:d,P), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def markedObsLaw {d : ℕ} (P : FullLaw d) :
    Measure (ObsRecord d × Fin 3) :=
  (P.1.map obs).prod (PMF.uniformOfFintype (Fin 3)).toMeasure

/-- [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def uniformPoolMass (_ : Fin 3) : ℝ≥0 := 1 / 3

/-- [the stated mathematical conclusion holds](goal). -/
lemma uniformPoolMass_sum : ∑ i : Fin 3, uniformPoolMass i = 1 := by
  norm_num [uniformPoolMass]

/-- [the stated mathematical conclusion holds](goal). -/
lemma labelLaw_uniformPoolMass :
    labelLaw uniformPoolMass uniformPoolMass_sum =
      (PMF.uniformOfFintype (Fin 3)).toMeasure := by
  apply Measure.ext_of_singleton
  intro i
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  simp [labelLaw, uniformPoolMass, PMF.ofFintype_apply]

/-- Given [the specified inputs and assumptions](hyp:d,pool,j,arrived,ones), [the stated mathematical conclusion holds](goal). -/
lemma streamEvent_eq_prod {d : ℕ} (pool : Fin 3) (j : Cell d)
    (arrived ones : Bool) :
    streamEvent pool j arrived ones = obsStreamEvent j arrived ones ×ˢ {pool} := by
  ext z
  simp only [streamEvent, obsStreamEvent, Set.mem_ofPred_eq, Set.mem_prod,
    Set.mem_singleton_iff]
  tauto

/-- Given [the specified inputs and assumptions](hyp:d,P,pool,j,arrived,ones), [the stated mathematical conclusion holds](goal). -/
lemma markedObsLaw_streamEvent_real {d : ℕ} (P : FullLaw d) (pool : Fin 3)
    (j : Cell d) (arrived ones : Bool) :
    (markedObsLaw P).real (streamEvent pool j arrived ones) =
      (P.1.map obs).real (obsStreamEvent j arrived ones) / 3 := by
  rw [streamEvent_eq_prod]
  rw [markedObsLaw, measureReal_def, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.uniformOfFintype_apply]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]
  rfl

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma markedObsLaw_isProbabilityMeasure {d : ℕ} (P : FullLaw d) :
    IsProbabilityMeasure (markedObsLaw P) := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (PMF.uniformOfFintype (Fin 3)).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  unfold markedObsLaw
  infer_instance

attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:d,P), [the stated mathematical conclusion holds](goal). -/
lemma map_obs_isProbabilityMeasure {d : ℕ} (P : FullLaw d) :
    IsProbabilityMeasure (P.1.map obs) := by
  letI : IsProbabilityMeasure P.1 := P.2
  exact Measure.isProbabilityMeasure_map (by fun_prop)

attribute [local instance] map_obs_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:d,P,lam), [the stated mathematical conclusion holds](goal). -/
lemma map_unshuffle_markedObsLaw {d : ℕ} (P : FullLaw d) (lam : ℝ≥0) :
    Measure.map unshuffle (finitePoissonSampleLaw (markedObsLaw P) lam) =
      Measure.pi (fun _ : Fin 3 =>
        finitePoissonSampleLaw (P.1.map obs) (lam * (1 / 3))) := by
  letI : IsProbabilityMeasure P.1 := P.2
  calc
    Measure.map unshuffle (finitePoissonSampleLaw (markedObsLaw P) lam) =
        labeledStreamLaw (P.1.map obs) uniformPoolMass uniformPoolMass_sum lam := by
      simp only [labeledStreamLaw, markedObsLaw, labelLaw_uniformPoolMass]
    _ = Measure.pi (fun i : Fin 3 =>
          finitePoissonSampleLaw (P.1.map obs) (lam * uniformPoolMass i)) :=
      labeledStreamLaw_eq_independent (P.1.map obs)
        uniformPoolMass uniformPoolMass_sum lam
    _ = _ := by simp [uniformPoolMass]

/-- Given [the specified inputs and assumptions](hyp:d,P,j), [the stated mathematical conclusion holds](goal). -/
lemma map_obsStreamEvent_membership_real {d : ℕ} (P : FullLaw d) (j : Cell d) :
    (P.1.map obs).real (obsStreamEvent j false false) = cellProb P j := by
  rw [measureReal_def, Measure.map_apply (by fun_prop)
    (Set.Finite.measurableSet (Set.toFinite _))]
  unfold cellProb
  congr 2
  ext r
  simp [obsStreamEvent, obs, inCell]

/-- Given [the specified inputs and assumptions](hyp:d,P,j), [the stated mathematical conclusion holds](goal). -/
lemma map_obsStreamEvent_arrived_real {d : ℕ} (P : FullLaw d) (j : Cell d) :
    (P.1.map obs).real (obsStreamEvent j true false) = arrivedCell P j := by
  rw [measureReal_def, Measure.map_apply (by fun_prop)
    (Set.Finite.measurableSet (Set.toFinite _))]
  unfold arrivedCell
  congr 2
  ext r
  simp [obsStreamEvent, obs, inCell]
  tauto

/-- Given [the specified inputs and assumptions](hyp:d,P,j), [the stated mathematical conclusion holds](goal). -/
lemma map_obsStreamEvent_arrivedOne_real {d : ℕ} (P : FullLaw d) (j : Cell d) :
    (P.1.map obs).real (obsStreamEvent j true true) =
      P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} := by
  rw [measureReal_def, Measure.map_apply (by fun_prop)
    (Set.Finite.measurableSet (Set.toFinite _)), measureReal_def]
  congr 2
  ext r
  simp [obsStreamEvent, obs, inCell]
  tauto

/-- Given [the specified inputs and assumptions](hyp:k,d,records,assign,pool,j,arrived,ones), [the stated mathematical conclusion holds](goal). -/
lemma streamCount_eq_eventCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (pool : Fin 3) (j : Cell d)
    (arrived ones : Bool) :
    streamCount records assign pool j arrived ones =
      eventCount (fixedSizeEmbed k (fun i ↦ (records i, assign i)))
        (streamEvent pool j arrived ones) := by
  classical
  simp [streamCount, eventCount, streamEvent, FiniteSample.count,
    FiniteSample.points, fixedSizeEmbed]
  apply congrArg Finset.card
  grind

/-- Given [the specified inputs and assumptions](hyp:d,pool,j), [the stated mathematical conclusion holds](goal). -/
lemma streamEvent_ones_subset_arrived {d : ℕ} (pool : Fin 3) (j : Cell d) :
    streamEvent pool j true true ⊆ streamEvent pool j true false := by
  intro z hz
  rcases hz with ⟨hp, ha, hx, hs, hr, _hy⟩
  exact ⟨hp, ha, hx, hs, hr, by simp⟩

/-- Given [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma memberCount_eq_eventCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) :
    memberCount records assign j =
      eventCount (fixedSizeEmbed k (fun i ↦ (records i, assign i)))
        (streamEvent 0 j false false) := by
  exact streamCount_eq_eventCount records assign 0 j false false

/-- Given [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma pilotCount_eq_eventCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) :
    pilotCount records assign j =
      eventCount (fixedSizeEmbed k (fun i ↦ (records i, assign i)))
        (streamEvent 1 j true false) := by
  exact streamCount_eq_eventCount records assign 1 j true false

/-- Given [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma arrivedCount_eq_eventCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) :
    arrivedCount records assign j =
      eventCount (fixedSizeEmbed k (fun i ↦ (records i, assign i)))
        (streamEvent 2 j true false) := by
  exact streamCount_eq_eventCount records assign 2 j true false

/-- Given [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma arrivedOneCount_eq_eventCount {k d : ℕ} (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) :
    arrivedOneCount records assign j =
      eventCount (fixedSizeEmbed k (fun i ↦ (records i, assign i)))
        (streamEvent 2 j true true) := by
  exact streamCount_eq_eventCount records assign 2 j true true

/-- Given [the specified inputs and assumptions](hyp:k,d,v,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma arrivedOne_fallingFactorial_eq_weightedFactorial {k d v : ℕ}
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) (j : Cell d) :
    (arrivedOneCount records assign j : ℝ) *
        fallingFactorial (arrivedCount records assign j - 1) (v - 1) =
      weightedFactorial (streamEvent 2 j true true) (streamEvent 2 j true false) v
        (fixedSizeEmbed k (fun i ↦ (records i, assign i))) := by
  rw [arrivedOneCount, arrivedCount,
    streamCount_eq_eventCount, streamCount_eq_eventCount]
  rfl

/-- Given [the specified inputs and assumptions](hyp:k,d,n,q,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma factorialBranch_eq_weightedFactorialSum {k d : ℕ} (n : ℕ) (q : ℝ)
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) (j : Cell d) :
    factorialBranch n q records assign j =
      if needleBranch n d q then
        ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
          needleCoeff n d q v *
            weightedFactorial (streamEvent 2 j true true)
              (streamEvent 2 j true false) v
              (fixedSizeEmbed k (fun i ↦ (records i, assign i)))
      else 0 := by
  unfold factorialBranch
  split_ifs with hbranch
  · apply Finset.sum_congr rfl
    intro v hv
    rw [← arrivedOne_fallingFactorial_eq_weightedFactorial
      (records := records) (assign := assign) (j := j) (v := v)]
    ring
  · rfl

/-- For [the specified inputs and assumptions](hyp:n,d,q,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def poissonFactorialBranch (n d : ℕ) (q : ℝ) (j : Cell d)
    (s : FiniteSample (ObsRecord d × Fin 3)) : ℝ :=
  if needleBranch n d q then
    ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
      needleCoeff n d q v *
        weightedFactorial (streamEvent 2 j true true)
          (streamEvent 2 j true false) v s
  else 0

/-- For [the specified inputs and assumptions](hyp:d,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def poissonRatioBranch {d : ℕ} (j : Cell d)
    (s : FiniteSample (ObsRecord d × Fin 3)) : ℝ :=
  if 0 < eventCount s (streamEvent 2 j true false) then
    eventCount s (streamEvent 2 j true true) /
      eventCount s (streamEvent 2 j true false)
  else 0

/-- For [the specified inputs and assumptions](hyp:n,d,q,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def poissonSelectedCellEstimate (n d : ℕ) (q : ℝ) (j : Cell d)
    (s : FiniteSample (ObsRecord d × Fin 3)) : ℝ :=
  if needleBranch n d q ∧
      eventCount s (streamEvent 1 j true false) ≤ needleRadius n q / 4 then
    poissonFactorialBranch n d q j s
  else poissonRatioBranch j s

/-- Given [the specified inputs and assumptions](hyp:k,d,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma ratioBranch_eq_poissonRatioBranch {k d : ℕ}
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) (j : Cell d) :
    ratioBranch records assign j = poissonRatioBranch j
      (fixedSizeEmbed k (fun i ↦ (records i, assign i))) := by
  rw [ratioBranch, poissonRatioBranch, arrivedCount_eq_eventCount,
    arrivedOneCount_eq_eventCount]

/-- Given [the specified inputs and assumptions](hyp:k,d,n,q,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma selectedCellEstimate_eq_poissonSelectedCellEstimate {k d : ℕ}
    (n : ℕ) (q : ℝ) (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) (j : Cell d) :
    selectedCellEstimate n q records assign j = poissonSelectedCellEstimate n d q j
      (fixedSizeEmbed k (fun i ↦ (records i, assign i))) := by
  unfold selectedCellEstimate poissonSelectedCellEstimate
  rw [pilotCount_eq_eventCount, ratioBranch_eq_poissonRatioBranch]
  split_ifs with hbranch
  · rw [factorialBranch_eq_weightedFactorialSum]
    simp only [poissonFactorialBranch, hbranch.1, if_true]
  · rfl

/-- Given [the specified inputs and assumptions](hyp:X,s,A,B,hAB), [the stated mathematical conclusion holds](goal). -/
lemma eventCount_mono {X : Type*} [MeasurableSpace X]
    (s : FiniteSample X) {A B : Set X} (hAB : A ⊆ B) :
    eventCount s A ≤ eventCount s B := by
  classical
  unfold eventCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hAB hi

/-- Given [the specified inputs and assumptions](hyp:d,j,s), [the stated mathematical conclusion holds](goal). -/
lemma poissonRatioBranch_mem_unitInterval {d : ℕ} (j : Cell d)
    (s : FiniteSample (ObsRecord d × Fin 3)) :
    poissonRatioBranch j s ∈ Set.Icc (0 : ℝ) 1 := by
  have hsub := streamEvent_ones_subset_arrived 2 j
  have hle := eventCount_mono s hsub
  unfold poissonRatioBranch
  split_ifs with hpos
  · constructor
    · positivity
    · exact (div_le_one (by exact_mod_cast hpos)).2 (by exact_mod_cast hle)
  · simp

/-- Given [the specified inputs and assumptions](hyp:d,j), [the stated mathematical conclusion holds](goal). -/
lemma measurable_poissonRatioBranch {d : ℕ} (j : Cell d) :
    Measurable (poissonRatioBranch j) := by
  let A := streamEvent 2 j true true
  let B := streamEvent 2 j true false
  have hA : MeasurableSet A := Set.Finite.measurableSet (Set.toFinite _)
  have hB : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite _)
  unfold poissonRatioBranch
  apply Measurable.ite
  · exact (measurable_eventCount B hB) measurableSet_Ioi
  · exact ((measurable_of_countable (fun z : ℕ => (z : ℝ))).comp
      (measurable_eventCount A hA)).div
        ((measurable_of_countable (fun z : ℕ => (z : ℝ))).comp
          (measurable_eventCount B hB))
  · exact measurable_const

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
lemma integrable_poissonRatioBranch_sq (n d : ℕ) (P : FullLaw d) (j : Cell d) :
    Integrable (fun s => (poissonRatioBranch j s) ^ 2)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  apply Integrable.of_bound ((measurable_poissonRatioBranch j).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rcases poissonRatioBranch_mem_unitInterval j s with ⟨hzero, hone⟩
  nlinarith [mul_nonneg hzero (sub_nonneg.mpr hone)]

/-- Given [the specified inputs and assumptions](hyp:X,Y,Q,f,hf,lam), [the stated mathematical conclusion holds](goal). -/
lemma map_finitePoissonSampleLaw_finiteSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (f : X → Y) (hf : Measurable f) (lam : ℝ≥0) :
    Measure.map (finiteSampleMap f) (finitePoissonSampleLaw Q lam) =
      (letI : IsProbabilityMeasure (Measure.map f Q) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finitePoissonSampleLaw (Measure.map f Q) lam) := by
  letI : IsProbabilityMeasure (Measure.map f Q) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let F := finiteSampleMap f
  have hF : Measurable F := measurable_finiteSampleMap f hf
  apply Measure.ext_of_iUnion_eq_univ
    (show (⋃ n : ℕ, FiniteSample.count ⁻¹' ({n} : Set ℕ)) = Set.univ by ext s; simp)
  intro n
  rw [Measure.restrict_map hF
      (measurable_finiteSample_count (MeasurableSet.singleton n))]
  have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      FiniteSample.count ⁻¹' ({n} : Set ℕ) := by ext s; rfl
  rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
    finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
    Measure.map_map hF (measurable_fixedSizeEmbed n)]
  have hfun : F ∘ fixedSizeEmbed n =
      fixedSizeEmbed n ∘ (fun x : Fin n → X => fun i => f (x i)) := by
    funext x
    exact finiteSampleMap_fixedSizeEmbed f n x
  rw [hfun]
  congr 1
  let G : (Fin n → X) → (Fin n → Y) := fun x i => f (x i)
  have hG : Measurable G :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  calc
    Measure.map (fixedSizeEmbed n ∘ G) (Measure.pi fun _ : Fin n => Q) =
        Measure.map (fixedSizeEmbed n) (Measure.map G (Measure.pi fun _ : Fin n => Q)) :=
      (Measure.map_map (measurable_fixedSizeEmbed n) hG).symm
    _ = Measure.map (fixedSizeEmbed n)
        (Measure.pi fun _ : Fin n => Measure.map f Q) := by
      rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]

/-- Given [the specified inputs and assumptions](hyp:X,Q,intensity,B,hB), [the stated mathematical conclusion holds](goal). -/
lemma finitePoissonSampleLaw_map_eventCount
    {X : Type*} [MeasurableSpace X] [Fintype X] [MeasurableSingletonClass X]
    [DecidableEq X] (Q : Measure X) [IsProbabilityMeasure Q]
    (intensity : ℝ≥0) (B : Set X) (hB : MeasurableSet B) :
    Measure.map (fun s : FiniteSample X => eventCount s B)
        (finitePoissonSampleLaw Q intensity) =
      poissonMeasure (intensity * (Q B).toNNReal) := by
  classical
  let f : X → Bool := fun x => decide (x ∈ B)
  have hf : Measurable f := measurable_of_finite _
  let QB := Measure.map f Q
  letI : IsProbabilityMeasure QB :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let H : FiniteSample Bool → (Bool → ℕ) :=
    fun s => Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram
      s.points
  have hpoint (s : FiniteSample X) : eventCount s B = H (finiteSampleMap f s) true := by
    rcases s with ⟨n, x⟩
    simp only [eventCount, H,
      Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram,
      finiteSampleMap, FiniteSample.count, FiniteSample.points, f]
    rw [Fintype.card_subtype]
    change (Finset.univ.filter (fun i : Fin n => x i ∈ B)).card =
      (Finset.univ.filter (fun i : Fin n => decide (x i ∈ B) = true)).card
    apply congrArg Finset.card
    ext i
    simp
  have hmass : QB {true} = Q B := by
    rw [Measure.map_apply hf (MeasurableSet.singleton true)]
    congr 1
    ext x
    simp [f]
  have hH : Measurable H :=
    Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.measurable_finiteSampleHistogram
  have hEval : Measurable (Function.eval true : (Bool → ℕ) → ℕ) :=
    measurable_pi_apply true
  calc
    Measure.map (fun s : FiniteSample X => eventCount s B)
        (finitePoissonSampleLaw Q intensity) =
        Measure.map (Function.eval true)
          (Measure.map H
            (Measure.map (finiteSampleMap f) (finitePoissonSampleLaw Q intensity))) := by
      rw [Measure.map_map hEval hH,
        Measure.map_map (hEval.comp hH) (measurable_finiteSampleMap f hf)]
      · congr 1
        funext s
        exact hpoint s
    _ = Measure.map (Function.eval true)
        (Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw
          QB intensity) := by
      rw [map_finitePoissonSampleLaw_finiteSampleMap Q f hf intensity,
        Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finitePoissonSampleLaw_map_histogram]
    _ = poissonMeasure (intensity * (QB {true}).toNNReal) := by
      unfold Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.independentPoissonCountLaw
      rw [Measure.pi_map_eval]
      simp
    _ = _ := by rw [hmass]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j,Q,lam), [the stated mathematical conclusion holds](goal). -/
lemma integral_poissonFactorialBranch (n d : ℕ) (q : ℝ) (j : Cell d)
    (Q : Measure (ObsRecord d × Fin 3)) [IsProbabilityMeasure Q] (lam : ℝ≥0) :
    (∫ s, poissonFactorialBranch n d q j s ∂finitePoissonSampleLaw Q lam) =
      if needleBranch n d q then
        ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
          needleCoeff n d q v * (lam : ℝ) ^ v *
            (Q (streamEvent 2 j true true)).toReal *
              (Q (streamEvent 2 j true false)).toReal ^ (v - 1)
      else 0 := by
  classical
  have hOne : MeasurableSet (streamEvent 2 j true true) :=
    Set.Finite.measurableSet (Set.toFinite _)
  have hArrived : MeasurableSet (streamEvent 2 j true false) :=
    Set.Finite.measurableSet (Set.toFinite _)
  have hsub := streamEvent_ones_subset_arrived 2 j
  by_cases hbranch : needleBranch n d q
  · simp only [poissonFactorialBranch, if_pos hbranch]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro v hv
      have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
      rw [integral_const_mul,
        finitePoisson_nestedEvent_factorialMoment Q lam
          (streamEvent 2 j true true) (streamEvent 2 j true false)
          hOne hArrived hsub v hv1]
      ring
    · intro v hv
      have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
      exact (integrable_weightedFactorial Q lam
        (streamEvent 2 j true true) (streamEvent 2 j true false)
        hOne hArrived hsub v hv1).const_mul _
  · simp [poissonFactorialBranch, hbranch]

/-- Given [the specified inputs and assumptions](hyp:X,Q,lam,A,B,hA,hB,hAB,v,hv), [the stated mathematical conclusion holds](goal). -/
lemma integrable_sq_weightedFactorial
    {X : Type*} [MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    (lam : ℝ≥0) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (v : ℕ) (hv : 1 ≤ v) :
    Integrable (fun s : FiniteSample X => (weightedFactorial A B v s) ^ 2)
      (finitePoissonSampleLaw Q lam) := by
  have hPoisson : Integrable (fun N : ℕ => (N.descFactorial v : ℝ) ^ 2)
      (poissonMeasure lam) := by
    have hsum := integrable_finsetSum (Finset.range (min v v + 1))
      (fun r _ =>
        (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
          lam (v + v - r)).const_mul
            ((v.choose r : ℝ) * (v.choose r : ℝ) * (Nat.factorial r : ℝ)))
    refine hsum.congr (Filter.Eventually.of_forall fun N => ?_)
    change (∑ r ∈ Finset.range (min v v + 1),
      (v.choose r : ℝ) * (v.choose r : ℝ) * (Nat.factorial r : ℝ) *
        (N.descFactorial (v + v - r) : ℝ)) = (N.descFactorial v : ℝ) ^ 2
    rw [pow_two,
      Causalean.Stat.Concentration.Poisson.descFactorial_mul N v v]
  have hCount : Integrable
      (fun s : FiniteSample X => (s.count.descFactorial v : ℝ) ^ 2)
      (finitePoissonSampleLaw Q lam) := by
    rw [← finitePoissonSampleLaw_map_count Q lam] at hPoisson
    exact hPoisson.comp_aemeasurable measurable_finiteSample_count.aemeasurable
  have hmeas : AEStronglyMeasurable
      (fun s : FiniteSample X => (weightedFactorial A B v s) ^ 2)
      (finitePoissonSampleLaw Q lam) :=
    ((measurable_weightedFactorial A B hA hB v).pow_const 2).aestronglyMeasurable
  apply integrable_of_le_of_le hmeas
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      _ (integrable_zero _ _ _) hCount
  filter_upwards [] with s
  have hs := weightedFactorial_nonneg_le_countFactorial A B hAB v hv s
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:X,Q,lam,A,B,C,D,hA,hB,hC,hD,hAB,hCD,v,w,hv,hw), [the stated mathematical conclusion holds](goal). -/
lemma integrable_mul_weightedFactorial
    {X : Type*} [MeasurableSpace X] (Q : Measure X) [IsProbabilityMeasure Q]
    (lam : ℝ≥0) (A B C D : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAB : A ⊆ B) (hCD : C ⊆ D) (v w : ℕ) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    Integrable (fun s : FiniteSample X =>
      weightedFactorial A B v s * weightedFactorial C D w s)
      (finitePoissonSampleLaw Q lam) := by
  have hPoisson : Integrable (fun N : ℕ =>
      (N.descFactorial v : ℝ) * (N.descFactorial w : ℝ))
      (poissonMeasure lam) := by
    have hsum := integrable_finsetSum (Finset.range (min v w + 1))
      (fun r _ =>
        (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
          lam (v + w - r)).const_mul
            ((v.choose r : ℝ) * (w.choose r : ℝ) * (Nat.factorial r : ℝ)))
    refine hsum.congr (Filter.Eventually.of_forall fun N => ?_)
    change (∑ r ∈ Finset.range (min v w + 1),
      (v.choose r : ℝ) * (w.choose r : ℝ) * (Nat.factorial r : ℝ) *
        (N.descFactorial (v + w - r) : ℝ)) =
          (N.descFactorial v : ℝ) * (N.descFactorial w : ℝ)
    rw [Causalean.Stat.Concentration.Poisson.descFactorial_mul N v w]
  have hCount : Integrable (fun s : FiniteSample X =>
      (s.count.descFactorial v : ℝ) * (s.count.descFactorial w : ℝ))
      (finitePoissonSampleLaw Q lam) := by
    rw [← finitePoissonSampleLaw_map_count Q lam] at hPoisson
    exact hPoisson.comp_aemeasurable measurable_finiteSample_count.aemeasurable
  have hmeas : AEStronglyMeasurable (fun s : FiniteSample X =>
      weightedFactorial A B v s * weightedFactorial C D w s)
      (finitePoissonSampleLaw Q lam) :=
    ((measurable_weightedFactorial A B hA hB v).mul
      (measurable_weightedFactorial C D hC hD w)).aestronglyMeasurable
  apply integrable_of_le_of_le hmeas
      (Filter.Eventually.of_forall fun s => mul_nonneg
        (weightedFactorial_nonneg_le_countFactorial A B hAB v hv s).1
        (weightedFactorial_nonneg_le_countFactorial C D hCD w hw s).1)
      _ (integrable_zero _ _ _) hCount
  filter_upwards [] with s
  exact mul_le_mul
    (weightedFactorial_nonneg_le_countFactorial A B hAB v hv s).2
    (weightedFactorial_nonneg_le_countFactorial C D hCD w hw s).2
    (weightedFactorial_nonneg_le_countFactorial C D hCD w hw s).1
    (by positivity)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
lemma integral_markedPoissonFactorialBranch (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (j : Cell d) :
    (∫ s, poissonFactorialBranch n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      if needleBranch n d q then
        ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1),
          needleCoeff n d q v * ((((n : ℝ≥0) / 2 : ℝ≥0) : ℝ) ^ v) *
            (P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} / 3) *
              (arrivedCell P j / 3) ^ (v - 1)
      else 0 := by
  rw [integral_poissonFactorialBranch]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  change needleCoeff n d q v * ((((n : ℝ≥0) / 2 : ℝ≥0) : ℝ) ^ v) *
      (markedObsLaw P).real (streamEvent 2 j true true) *
        ((markedObsLaw P).real (streamEvent 2 j true false)) ^ (v - 1) = _
  rw [markedObsLaw_streamEvent_real, markedObsLaw_streamEvent_real,
    map_obsStreamEvent_arrivedOne_real, map_obsStreamEvent_arrived_real]

end CausalSmith.Stat.MarRareqLogfrontier
