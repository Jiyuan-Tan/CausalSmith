module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.CellBounds
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamStatistic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.CellLaws
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments

/-!
# Paper-local four-stream moment targets

These leaves isolate equations (3)--(5) of the upper-risk proof. They expose
the exact independent Poisson stream law and the estimator's named cell statistics.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal BigOperators
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- The ideal independent four-stream law for one full-data distribution. -/
noncomputable def fourStreamLaw {d : ℕ} (n : ℕ) (P : FullLaw d) :
    Measure (Fin 4 → FiniteSample (Obs d)) :=
  labeledStreamLaw (observedLaw P).toMeasure uniformFourMass
    uniformFourMass_sum ((n : NNReal) / 2)

/-- Mean count of arrived records in a cell of one auxiliary stream. -/
noncomputable def streamZ {d : ℕ} (n : ℕ) (P : FullLaw d)
    (x : Fin d) (a s : Bool) : ℝ :=
  ((n : ℝ) / 8) * arrivedCellMass P x a s

/-- Nonnegative Poisson rate for an arrived cell in one auxiliary stream. -/
noncomputable def streamPoissonRate {d : ℕ} (n : ℕ) (P : FullLaw d)
    (x : Fin d) (a s : Bool) : NNReal :=
  ((n : NNReal) / 8) * ⟨arrivedCellMass P x a s,
    arrivedCellMass_nonneg P x a s⟩

private lemma missingCellMass_eq_massOf_missing {d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    missingCellMass P x a s =
      massOf P (fun w ↦ w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = false) := by
  classical
  unfold missingCellMass cellMass arrivedCellMass massOf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  cases hR : w.R <;>
    by_cases hc : w.X = x ∧ w.A = a ∧ w.S = s <;> simp [hR, hc]

private lemma finiteStreamCount_eq_histogram_sum {d : ℕ}
    (sample : FiniteSample (Obs d)) (E : Obs d → Prop) :
    finiteStreamCount sample E =
      ∑ o : Obs d, @ite ℝ (E o) (Classical.propDecidable _)
        (finiteSampleHistogram sample.points o : ℝ) 0 := by
  rcases sample with ⟨N, sample⟩
  unfold finiteStreamCount finiteSampleHistogram FiniteSample.points
  change (∑ i : Fin N, @ite ℝ (E (sample i)) (Classical.propDecidable _) 1 0) = _
  calc
    _ = ∑ o : Obs d, ∑ i : {i : Fin N // sample i = o},
        @ite ℝ (E (sample i)) (Classical.propDecidable _) 1 0 :=
      (Fintype.sum_fiberwise sample
        (fun i ↦ @ite ℝ (E (sample i)) (Classical.propDecidable _) 1 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro o ho
      by_cases hE : E o
      · have hforall : ∀ i : {i : Fin N // sample i = o}, E (sample i) := by
          intro i
          rw [i.property]
          exact hE
        simp only [hE, if_true, hforall]
        norm_cast
        change (∑ _i : {i : Fin N // sample i = o}, (1 : ℕ)) = _
        simp
        rfl
      · have hforall : ∀ i : {i : Fin N // sample i = o}, ¬E (sample i) := by
          intro i hi
          apply hE
          simpa [i.property] using hi
        simp only [hE, if_false, hforall]
        simp

-- @node: upper_stream_v_mean
/-- Equation (3), first moment: the normalized missing count has mean equal to
the missing cell mass. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_v_mean {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, streamV n d streams x a s ∂fourStreamLaw n P) =
      missingCellMass P x a s := by
  classical
  let μ := fourStreamLaw n P
  let Q := (observedLaw P).toMeasure
  let lam : NNReal := ((n : NNReal) / 2) * uniformFourMass 1
  let hist : FiniteSample (Obs d) → (Obs d → ℕ) :=
    fun z ↦ finiteSampleHistogram z.points
  have hstream : Measure.map (fun streams ↦ streams 1) μ =
      finitePoissonSampleLaw Q lam := by
    let ν : Fin 4 → Measure (FiniteSample (Obs d)) := fun i ↦
      finitePoissonSampleLaw (observedLaw P).toMeasure
        (((n : NNReal) / 2) * uniformFourMass i)
    haveI (i : Fin 4) : IsProbabilityMeasure (ν i) := by
      dsimp [ν]
      infer_instance
    rw [show μ = Measure.pi ν by
      unfold μ fourStreamLaw ν
      exact labeledStreamLaw_eq_independent _ _ _ _]
    simpa [ν, Q, lam] using (Measure.pi_map_eval (μ := ν) 1)
  have hhist : Measure.map hist (finitePoissonSampleLaw Q lam) =
      independentPoissonCountLaw Q lam := by
    exact finitePoissonSampleLaw_map_histogram Q lam
  have hmap : Measure.map (fun streams ↦ hist (streams 1)) μ =
      independentPoissonCountLaw Q lam := by
    rw [← hhist, ← hstream, Measure.map_map]
    · rfl
    · exact measurable_finiteSampleHistogram
    · fun_prop
  rw [show streamV n d = fun streams x a s ↦
      finiteStreamCount (streams 1)
        (fun o ↦ inCell o x a s ∧ o.R = false) / ((n : ℝ) / 8) by rfl]
  simp_rw [finiteStreamCount_eq_histogram_sum]
  change (∫ streams,
    (∑ o : Obs d, @ite ℝ (inCell o x a s ∧ o.R = false)
      (Classical.propDecidable _) (hist (streams 1) o : ℝ) 0) /
      ((n : ℝ) / 8) ∂μ) = _
  rw [← integral_map
    (μ := μ) (φ := fun streams ↦ hist (streams 1))
    (f := fun counts : Obs d → ℕ ↦
      (∑ o : Obs d, @ite ℝ (inCell o x a s ∧ o.R = false)
        (Classical.propDecidable _) (counts o : ℝ) 0) / ((n : ℝ) / 8))
    (by
      change AEMeasurable
        ((fun z : FiniteSample (Obs d) ↦ finiteSampleHistogram z.points) ∘
          fun streams ↦ streams 1) μ
      exact (measurable_finiteSampleHistogram.comp
        (measurable_pi_apply 1)).aemeasurable)
    (measurable_of_countable _).aestronglyMeasurable, hmap]
  unfold independentPoissonCountLaw
  rw [integral_div]
  rw [integral_finset_sum]
  have hite (o : Obs d) :
      (∫ counts : Obs d → ℕ,
        @ite ℝ (inCell o x a s ∧ o.R = false) (Classical.propDecidable _)
          (counts o : ℝ) 0
        ∂Measure.pi (fun o : Obs d ↦ poissonMeasure
          (lam * (Q {o}).toNNReal))) =
      @ite ℝ (inCell o x a s ∧ o.R = false) (Classical.propDecidable _)
        (∫ counts : Obs d → ℕ, (counts o : ℝ)
          ∂Measure.pi (fun o : Obs d ↦ poissonMeasure
            (lam * (Q {o}).toNNReal))) 0 := by
    by_cases h : inCell o x a s ∧ o.R = false <;> simp [h]
  simp_rw [hite]
  simp_rw [integral_comp_eval
    (μ := fun o : Obs d ↦ poissonMeasure (lam * (Q {o}).toNNReal))
    (i := _)
    (f := fun k : ℕ ↦ (k : ℝ))
    (measurable_of_countable _).aestronglyMeasurable]
  simp_rw [Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  dsimp only [lam]
  change (∑ o : Obs d, if inCell o x a s ∧ o.R = false then
      ((((n : NNReal) / 2) * uniformFourMass 1 * (Q {o}).toNNReal : NNReal) : ℝ)
      else 0) /
      ((n : ℝ) / 8) = missingCellMass P x a s
  simp only [uniformFourMass]
  have hn8 : ((n : ℝ) / 8) ≠ 0 := by positivity
  rw [missingCellMass_eq_massOf_missing P x a s]
  have hobs := obsMass_sum_event P
    (fun o : Obs d ↦ inCell o x a s ∧ o.R = false)
  have hobs' :
      (∑ o : Obs d, if inCell o x a s ∧ o.R = false then
        obsMass (observedLaw P) o else 0) =
      massOf P (fun w ↦ w.X = x ∧ w.A = a ∧ w.S = s ∧ w.R = false) := by
    simpa [inCell, observe, and_assoc] using hobs
  rw [← hobs']
  unfold Q obsMass
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  push_cast
  field_simp
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o ho
  by_cases h : inCell o x a s ∧ o.R = false <;> simp [h] <;> ring
  intro i hi
  by_cases h : inCell i x a s ∧ i.R = false
  · simp only [h, if_true]
    have hint : Integrable (fun k : ℕ ↦ (k : ℝ))
        (poissonMeasure (lam * ((observedLaw P).toMeasure {i}).toNNReal)) :=
      (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
        (lam * ((observedLaw P).toMeasure {i}).toNNReal)).integrable (by norm_num)
    exact integrable_comp_eval
      (μ := fun o : Obs d ↦ poissonMeasure (lam * ((observedLaw P).toMeasure {o}).toNNReal))
      (i := i) hint
  · simp [h]

-- @node: upper_map_finitePoissonSampleLaw_finiteSampleMap
/-- Given [the specified input `X`](hyp:X), [the specified input `Y`](hyp:Y), [the specified input `P`](hyp:P), [the specified input `f`](hyp:f), [the specified input `hf`](hyp:hf), [the specified input `lambda`](hyp:lambda), [the stated mathematical conclusion holds](goal). -/
lemma upper_map_finitePoissonSampleLaw_finiteSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → Y) (hf : Measurable f) (lambda : ℝ≥0) :
    Measure.map (finiteSampleMap f) (finitePoissonSampleLaw P lambda) =
      (letI : IsProbabilityMeasure (Measure.map f P) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finitePoissonSampleLaw (Measure.map f P) lambda) := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let F := finiteSampleMap f
  have hF : Measurable F := measurable_finiteSampleMap f hf
  let mu := Measure.map F (finitePoissonSampleLaw P lambda)
  let nu := finitePoissonSampleLaw (Measure.map f P) lambda
  have hrest (n : ℕ) :
      mu.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        nu.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by
    rw [show mu = Measure.map F (finitePoissonSampleLaw P lambda) by rfl,
      Measure.restrict_map hF
        (measurable_finiteSample_count (MeasurableSet.singleton n))]
    have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({n} : Set ℕ) := by ext s; rfl
    rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
      show nu = finitePoissonSampleLaw (Measure.map f P) lambda by rfl,
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
    change Measure.map (fixedSizeEmbed n ∘ G)
      (Measure.pi fun _ : Fin n => P) = _
    calc
      Measure.map (fixedSizeEmbed n ∘ G) (Measure.pi fun _ : Fin n => P) =
          Measure.map (fixedSizeEmbed n)
            (Measure.map G (Measure.pi fun _ : Fin n => P)) :=
        (Measure.map_map (measurable_fixedSizeEmbed n) hG).symm
      _ = Measure.map (fixedSizeEmbed n)
          (Measure.pi fun _ : Fin n => Measure.map f P) := by
        rw [show G = (fun x i => f (x i)) by rfl,
          Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  have hdecomp (eta : Measure (FiniteSample Y)) :
      eta = Measure.sum (fun n =>
        eta.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
    have hdis : Pairwise (Function.onFun Disjoint
        (fun n : ℕ => (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹'
          ({n} : Set ℕ))) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro s hi hj
      apply hij
      simpa using hi.symm.trans hj
    have hcover : ⋃ n : ℕ,
        (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹' ({n} : Set ℕ) =
          Set.univ := by ext s; simp
    calc
      eta = eta.restrict Set.univ := by rw [Measure.restrict_univ]
      _ = eta.restrict (⋃ n : ℕ,
          FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by rw [hcover]
      _ = Measure.sum (fun n =>
          eta.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
        exact Measure.restrict_iUnion hdis
          (fun n => measurable_finiteSample_count (MeasurableSet.singleton n))
  change mu = nu
  rw [hdecomp mu, hdecomp nu]
  congr 1
  funext n
  exact hrest n

-- @node: upper_measurable_eventCount
/-- Given [the specified input `X`](hyp:X), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
lemma upper_measurable_eventCount {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (E : X → Bool) : Measurable (fun z : FiniteSample X =>
      (Finset.univ.filter (fun i : Fin z.count => E (z.points i) = true)).card) := by
  classical
  apply measurable_to_countable'
  intro k
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  exact measurable_of_countable (fun xs : Fin m → X =>
    (Finset.univ.filter (fun i : Fin m => E (xs i) = true)).card)
      (measurableSet_singleton k)

-- @node: upper_finitePoissonSampleLaw_eventCount
/-- An event count in a finite Poisson sample has the corresponding Poisson law. Given [the specified input `X`](hyp:X), [the specified input `Q`](hyp:Q), [the specified input `lam`](hyp:lam), [the specified input `E`](hyp:E), [the specified input `hE`](hyp:hE), [the stated mathematical conclusion holds](goal). -/
lemma upper_finitePoissonSampleLaw_eventCount {X : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [Countable X]
    (Q : Measure X) [IsProbabilityMeasure Q] (lam : NNReal)
    (E : X → Bool) (hE : Measurable E) :
    Measure.map (fun z : FiniteSample X =>
      (Finset.univ.filter (fun i : Fin z.count => E (z.points i) = true)).card)
      (finitePoissonSampleLaw Q lam) =
        poissonMeasure (lam * (Q {x | E x = true}).toNNReal) := by
  classical
  let p : FiniteMeasurablePartition X Bool :=
    { cell := E, measurable_cell := hE }
  let R : Measure ℝ := Measure.dirac 0
  have herase := upper_map_finitePoissonSampleLaw_finiteSampleMap
    (Q.prod R) Prod.fst measurable_fst lam
  have hprod : Measure.map Prod.fst (Q.prod R) = Q := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have herase' :
      Measure.map (finiteSampleMap Prod.fst)
        (finiteMarkedPoissonSampleLaw Q R lam) =
      finitePoissonSampleLaw Q lam := by
    change Measure.map (finiteSampleMap Prod.fst)
      (finitePoissonSampleLaw (Q.prod R) lam) = finitePoissonSampleLaw Q lam
    simpa only [hprod] using herase
  have hcount (z : FiniteSample (X × ℝ)) :
      (p.restrictCell true z).count =
        (Finset.univ.filter (fun i : Fin (finiteSampleMap Prod.fst z).count =>
          E ((finiteSampleMap Prod.fst z).points i) = true)).card := by
    change (p.cellIndices true z).card = _
    simp only [FiniteMeasurablePartition.cellIndices, p,
      finiteSampleMap, FiniteSample.count, FiniteSample.points]
    congr 1
    exact Finset.filter_congr_decidable _ _ _
  have hmarked := p.map_restrictCell_count_finiteMarkedPoissonSampleLaw
    Q R lam true
  have hmass : p.cellMass Q true = (Q {x | E x = true}).toNNReal := by
    rfl
  rw [hmass] at hmarked
  have hmeas := upper_measurable_eventCount E
  calc
    Measure.map (fun z : FiniteSample X =>
        (Finset.univ.filter (fun i : Fin z.count => E (z.points i) = true)).card)
        (finitePoissonSampleLaw Q lam) =
      Measure.map (fun z : FiniteSample (X × ℝ) =>
        (p.restrictCell true z).count) (finiteMarkedPoissonSampleLaw Q R lam) := by
      rw [← herase', Measure.map_map]
      · exact congrArg (fun f => Measure.map f (finiteMarkedPoissonSampleLaw Q R lam))
          (funext fun z => (hcount z).symm)
      · exact hmeas
      · exact measurable_finiteSampleMap Prod.fst measurable_fst
    _ = _ := hmarked

-- @node: upper_finiteStreamCount_eq_eventCount
/-- Given [the specified input `d`](hyp:d), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). Given [the specified input `z`](hyp:z). -/
lemma upper_finiteStreamCount_eq_eventCount {d : ℕ}
    (z : FiniteSample (Obs d)) (E : Obs d → Prop) [DecidablePred E] :
    finiteStreamCount z E =
      ((Finset.univ.filter (fun i : Fin z.count => E (z.points i))).card : ℝ) := by
  classical
  rcases z with ⟨N, points⟩
  unfold finiteStreamCount
  simp only [FiniteSample.count, FiniteSample.points]
  have hsum :
      (∑ i : Fin N, @ite ℝ (E (points i)) (Classical.propDecidable _) 1 0) =
        ∑ i : Fin N, if E (points i) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : E (points i) <;> simp [h]
  calc
    _ = (∑ i : Fin N, if E (points i) then (1 : ℝ) else 0) := hsum
    _ = _ := by
      convert (Finset.sum_boole (fun i : Fin N => E (points i))
        (Finset.univ : Finset (Fin N)) :
        (∑ i : Fin N, if E (points i) then (1 : ℝ) else 0) =
          ((Finset.univ.filter (fun i : Fin N => E (points i))).card : ℝ)) using 1
      congr 1

-- @node: upper_stream_v_second_moment
/-- Equation (3), second moment: a scaled Poisson missing count has its mean
squared plus its Poisson variance. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_v_second_moment {n d : ℕ} (hn : 0 < n) (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    (∫ streams, (streamV n d streams x a s) ^ 2 ∂fourStreamLaw n P) =
      (missingCellMass P x a s) ^ 2 +
        missingCellMass P x a s / ((n : ℝ) / 8) := by
  classical
  let μ := fourStreamLaw n P
  let Q := (observedLaw P).toMeasure
  let lam : NNReal := ((n : NNReal) / 2) * uniformFourMass 1
  let E : Obs d → Bool := fun o => decide (inCell o x a s ∧ o.R = false)
  let count : (Fin 4 → FiniteSample (Obs d)) → ℕ := fun streams =>
    (Finset.univ.filter (fun i : Fin (streams 1).count =>
      E ((streams 1).points i) = true)).card
  let rate : NNReal := lam * (Q {o | E o = true}).toNNReal
  have hstream : Measure.map (fun streams ↦ streams 1) μ =
      finitePoissonSampleLaw Q lam := by
    let ν : Fin 4 → Measure (FiniteSample (Obs d)) := fun i ↦
      finitePoissonSampleLaw Q (((n : NNReal) / 2) * uniformFourMass i)
    haveI (i : Fin 4) : IsProbabilityMeasure (ν i) := by
      dsimp [ν]
      infer_instance
    rw [show μ = Measure.pi ν by
      unfold μ fourStreamLaw ν
      exact labeledStreamLaw_eq_independent _ _ _ _]
    simpa [ν, Q, lam] using (Measure.pi_map_eval (μ := ν) 1)
  have hcountMeas : Measurable count :=
    (upper_measurable_eventCount E).comp (measurable_pi_apply 1)
  have hlaw : Measure.map count μ = poissonMeasure rate := by
    rw [show count = (fun z : FiniteSample (Obs d) =>
        (Finset.univ.filter (fun i : Fin z.count => E (z.points i) = true)).card) ∘
        (fun streams => streams 1) by rfl]
    rw [← Measure.map_map (upper_measurable_eventCount E)
      (measurable_pi_apply 1), hstream]
    exact upper_finitePoissonSampleLaw_eventCount Q lam E (measurable_of_countable E)
  have hcountReal (streams : Fin 4 → FiniteSample (Obs d)) :
      finiteStreamCount (streams 1)
        (fun o ↦ inCell o x a s ∧ o.R = false) = (count streams : ℝ) := by
    simpa only [count, E, decide_eq_true_eq] using
      upper_finiteStreamCount_eq_eventCount (streams 1)
        (fun o ↦ inCell o x a s ∧ o.R = false)
  have hV (streams : Fin 4 → FiniteSample (Obs d)) :
      streamV n d streams x a s = (count streams : ℝ) / ((n : ℝ) / 8) := by
    unfold streamV
    rw [hcountReal]
  have hmean :
      (∫ streams, (count streams : ℝ) / ((n : ℝ) / 8) ∂μ) =
        missingCellMass P x a s := by
    simpa only [μ, ← hV] using upper_stream_v_mean hn P x a s
  have hfirst :
      (∫ k : ℕ, (k : ℝ) / ((n : ℝ) / 8) ∂poissonMeasure rate) =
        missingCellMass P x a s := by
    rw [← hlaw, integral_map hcountMeas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    exact hmean
  have hsecond :
      (∫ k : ℕ, ((k : ℝ) / ((n : ℝ) / 8)) ^ 2 ∂poissonMeasure rate) =
        (rate : ℝ) ^ 2 / (((n : ℝ) / 8) ^ 2) +
          (rate : ℝ) / (((n : ℝ) / 8) ^ 2) := by
    simp only [div_pow]
    rw [integral_div, Causalean.Mathlib.Probability.Poisson.PairSecondMoment.poisson_count_second_moment]
    ring
  have hn8 : ((n : ℝ) / 8) ≠ 0 := by positivity
  have hrate : (rate : ℝ) / ((n : ℝ) / 8) = missingCellMass P x a s := by
    rw [← hfirst, integral_div,
      Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment]
  simp_rw [hV]
  change (∫ streams, ((count streams : ℝ) / ((n : ℝ) / 8)) ^ 2 ∂μ) = _
  calc
    (∫ streams, ((count streams : ℝ) / ((n : ℝ) / 8)) ^ 2 ∂μ) =
        ∫ k : ℕ, ((k : ℝ) / ((n : ℝ) / 8)) ^ 2 ∂Measure.map count μ := by
      rw [integral_map hcountMeas.aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
    _ = _ := by
      rw [hlaw, hsecond, ← hrate]
      field_simp

-- @node: upper_stream_arrived_count_law
/-- Equation (3), count law: the pilot and correction arrived counts each
have the Poisson law with rate given by the arrived cell mass. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_arrived_count_law {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    Measure.map (fun streams ↦ streamCpilot d streams x a s) (fourStreamLaw n P) =
        Measure.map (fun k : ℕ ↦ (k : ℝ))
          (poissonMeasure (streamPoissonRate n P x a s)) ∧
      Measure.map (fun streams ↦ streamC d streams x a s) (fourStreamLaw n P) =
        Measure.map (fun k : ℕ ↦ (k : ℝ))
          (poissonMeasure (streamPoissonRate n P x a s)) := by
  classical
  let Q := (observedLaw P).toMeasure
  let E : Obs d → Bool := fun o => decide (inCell o x a s ∧ o.R = true)
  have hmass : (Q {o | E o = true}).toNNReal =
      ⟨arrivedCellMass P x a s, arrivedCellMass_nonneg P x a s⟩ := by
    apply NNReal.eq
    change (Q {o | E o = true}).toReal = arrivedCellMass P x a s
    simp only [E, decide_eq_true_eq]
    rw [show (Q {o | inCell o x a s ∧ o.R = true}).toReal =
          ∑ o : Obs d, if inCell o x a s ∧ o.R = true then
            obsMass (observedLaw P) o else 0 by
          rw [show Q = (observedLaw P).toMeasure by rfl,
            PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
          · apply Finset.sum_congr rfl
            intro o ho
            by_cases h : inCell o x a s ∧ o.R = true <;>
              simp [Set.indicator, h, obsMass]
          · intro o ho
            by_cases h : inCell o x a s ∧ o.R = true <;>
              simp [Set.indicator, h, PMF.apply_ne_top]]
    simpa only [inCell, arrivedCellMass, and_assoc] using
      observed_arrived_mass P x a s
  have hcount (i : Fin 4) (hi : i = 2 ∨ i = 3) :
      Measure.map (fun streams => finiteStreamCount (streams i)
        (fun o => inCell o x a s ∧ o.R = true)) (fourStreamLaw n P) =
        Measure.map (fun k : ℕ => (k : ℝ))
          (poissonMeasure (streamPoissonRate n P x a s)) := by
    let lam : NNReal := ((n : NNReal) / 2) * uniformFourMass i
    let count : FiniteSample (Obs d) → ℕ := fun z =>
      (Finset.univ.filter (fun j : Fin z.count => E (z.points j) = true)).card
    have hstream : Measure.map (fun streams => streams i) (fourStreamLaw n P) =
        finitePoissonSampleLaw Q lam := by
      let ν : Fin 4 → Measure (FiniteSample (Obs d)) := fun j =>
        finitePoissonSampleLaw Q (((n : NNReal) / 2) * uniformFourMass j)
      haveI (j : Fin 4) : IsProbabilityMeasure (ν j) := by
        dsimp [ν]
        infer_instance
      rw [show fourStreamLaw n P = Measure.pi ν by
        unfold fourStreamLaw ν Q
        exact labeledStreamLaw_eq_independent _ _ _ _]
      simpa [ν, lam] using (Measure.pi_map_eval (μ := ν) i)
    have hlaw : Measure.map count (finitePoissonSampleLaw Q lam) =
        poissonMeasure (lam * (Q {o | E o = true}).toNNReal) :=
      upper_finitePoissonSampleLaw_eventCount Q lam E (measurable_of_countable E)
    have hrate : lam * (Q {o | E o = true}).toNNReal =
        streamPoissonRate n P x a s := by
      rw [hmass]
      cases hi with
      | inl h => subst i; norm_num [lam, uniformFourMass, streamPoissonRate]; ring
      | inr h => subst i; norm_num [lam, uniformFourMass, streamPoissonRate]; ring
    have hreal (z : FiniteSample (Obs d)) :
        finiteStreamCount z (fun o => inCell o x a s ∧ o.R = true) =
          (count z : ℝ) := by
      simpa only [count, E, decide_eq_true_eq] using
        upper_finiteStreamCount_eq_eventCount z
          (fun o => inCell o x a s ∧ o.R = true)
    have heval : Measurable (fun streams : Fin 4 → FiniteSample (Obs d) =>
        streams i) := measurable_pi_apply i
    have hcountMeas : Measurable count := upper_measurable_eventCount E
    have hcast : Measurable (fun k : ℕ => (k : ℝ)) := measurable_of_countable _
    calc
      _ = Measure.map ((fun k : ℕ => (k : ℝ)) ∘ count ∘
          (fun streams => streams i)) (fourStreamLaw n P) := by
        congr 1
        funext streams
        exact hreal (streams i)
      _ = Measure.map (fun k : ℕ => (k : ℝ))
          (Measure.map count (Measure.map (fun streams => streams i)
            (fourStreamLaw n P))) := by
        rw [Measure.map_map hcountMeas heval]
        rw [Measure.map_map hcast (hcountMeas.comp heval)]
      _ = _ := by rw [hstream, hlaw, hrate]
  constructor
  · exact hcount 2 (Or.inl rfl)
  · exact hcount 3 (Or.inr rfl)

end CausalSmith.Stat.MarNearcompleteFrontier
