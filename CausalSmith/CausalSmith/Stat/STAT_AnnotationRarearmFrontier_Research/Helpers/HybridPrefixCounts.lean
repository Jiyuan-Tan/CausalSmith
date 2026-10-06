module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePrefixCounts
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.HybridFiniteEncoding

/-!
Joint independent Poisson histogram laws for the outcome, pilot, and factorial prefixes.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- The three ideal ordered pools have independent Poisson sample laws. -/
-- @node: hybridPoissonPrefixLaw
noncomputable def hybridPoissonPrefixLaw {d : Nat} (P : DiscreteLaw d) (u tp t : NNReal) :
    Measure (FiniteSample (Obs d) × FiniteSample (AuxObs d) × FiniteSample (AuxObs d)) :=
  (finitePoissonSampleLaw (obsLaw P) u).prod
    ((finitePoissonSampleLaw (auxMarginal P).toMeasure tp).prod
      (finitePoissonSampleLaw (auxMarginal P).toMeasure t))

/-- The ideal three-pool experiment is a probability law even at zero intensities. -/
-- @node: hybridPoissonPrefixLaw_probability
instance hybridPoissonPrefixLaw_probability {d : Nat} (P : DiscreteLaw d) (u tp t : NNReal) :
    IsProbabilityMeasure (hybridPoissonPrefixLaw P u tp t) := by
  unfold hybridPoissonPrefixLaw
  infer_instance

/-- Disjoint sum indices distinguish all atoms of the three histograms. -/
-- @node: hybridPrefixCounts
noncomputable def hybridPrefixCounts {d : Nat}
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d) × FiniteSample (AuxObs d)) :
    Obs d ⊕ (AuxObs d ⊕ AuxObs d) → Nat :=
  Sum.elim (finiteSampleHistogram s.1.points)
    (Sum.elim (finiteSampleHistogram s.2.1.points) (finiteSampleHistogram s.2.2.points))

/-- Histograms of all three ordered finite samples are measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: hybridPrefixCounts_measurable
lemma hybridPrefixCounts_measurable (d : Nat) :
    Measurable (hybridPrefixCounts (d := d)) := by
  change Measurable ((MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Obs d ⊕ (AuxObs d ⊕ AuxObs d) => Nat)).symm ∘
    (fun s : FiniteSample (Obs d) × FiniteSample (AuxObs d) × FiniteSample (AuxObs d) =>
      (finiteSampleHistogram s.1.points,
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : AuxObs d ⊕ AuxObs d => Nat)).symm
          (finiteSampleHistogram s.2.1.points, finiteSampleHistogram s.2.2.points))))
  apply (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable.comp
  apply Measurable.prodMk
  · exact baseline_finiteSampleHistogram_measurable.comp measurable_fst
  · exact (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable.comp
      ((baseline_finiteSampleHistogram_measurable.comp (measurable_fst.comp measurable_snd)).prodMk
        (baseline_finiteSampleHistogram_measurable.comp (measurable_snd.comp measurable_snd)))

/-- Under the stated inputs and conditions, Thinning and the product law give independent Poisson counts for every atom.  This gives [the stated result](goal). -/
-- @node: hybrid_prefix_counts_law
lemma hybrid_prefix_counts_law {d : Nat} (P : DiscreteLaw d) (u tp t : NNReal) :
    (hybridPoissonPrefixLaw P u tp t).map hybridPrefixCounts =
      Measure.pi (fun i : Obs d ⊕ (AuxObs d ⊕ AuxObs d) => poissonMeasure
        (Sum.elim (fun z => u * ((obsLaw P) {z}).toNNReal)
          (Sum.elim (fun z => tp * ((auxMarginal P).toMeasure {z}).toNNReal)
            (fun z => t * ((auxMarginal P).toMeasure {z}).toNNReal)) i)) := by
  let H : FiniteSample (AuxObs d) × FiniteSample (AuxObs d) →
      (AuxObs d ⊕ AuxObs d → Nat) := fun s =>
    Sum.elim (finiteSampleHistogram s.1.points) (finiteSampleHistogram s.2.points)
  have hH : Measurable H := by
    change Measurable ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : AuxObs d ⊕ AuxObs d => Nat)).symm ∘
      (fun s : FiniteSample (AuxObs d) × FiniteSample (AuxObs d) =>
        (finiteSampleHistogram s.1.points, finiteSampleHistogram s.2.points)))
    exact (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable.comp
      ((baseline_finiteSampleHistogram_measurable.comp measurable_fst).prodMk
        (baseline_finiteSampleHistogram_measurable.comp measurable_snd))
  let rates : Obs d ⊕ (AuxObs d ⊕ AuxObs d) → NNReal :=
    Sum.elim (fun z => u * ((obsLaw P) {z}).toNNReal)
      (Sum.elim (fun z => tp * ((auxMarginal P).toMeasure {z}).toNNReal)
        (fun z => t * ((auxMarginal P).toMeasure {z}).toNNReal))
  have haux := Measure.map_prod_map
    (finitePoissonSampleLaw (auxMarginal P).toMeasure tp)
    (finitePoissonSampleLaw (auxMarginal P).toMeasure t)
    (baseline_finiteSampleHistogram_measurable (X := AuxObs d))
    (baseline_finiteSampleHistogram_measurable (X := AuxObs d))
  rw [finitePoissonSampleLaw_map_histogram, finitePoissonSampleLaw_map_histogram] at haux
  have hauxlaw : ((finitePoissonSampleLaw (auxMarginal P).toMeasure tp).prod
      (finitePoissonSampleLaw (auxMarginal P).toMeasure t)).map H =
      Measure.pi (fun i : AuxObs d ⊕ AuxObs d => poissonMeasure (rates (.inr i))) := by
    rw [← (measurePreserving_sumPiEquivProdPi_symm
      (fun i : AuxObs d ⊕ AuxObs d => poissonMeasure (rates (.inr i)))).map_eq]
    change _ = Measure.map (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : AuxObs d ⊕ AuxObs d => Nat)).symm
        ((independentPoissonCountLaw (auxMarginal P).toMeasure tp).prod
          (independentPoissonCountLaw (auxMarginal P).toMeasure t))
    rw [haux, Measure.map_map (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable
      (by fun_prop)]
    rfl
  have hjoint := Measure.map_prod_map (finitePoissonSampleLaw (obsLaw P) u)
    ((finitePoissonSampleLaw (auxMarginal P).toMeasure tp).prod
      (finitePoissonSampleLaw (auxMarginal P).toMeasure t))
    (baseline_finiteSampleHistogram_measurable (X := Obs d)) hH
  rw [finitePoissonSampleLaw_map_histogram, hauxlaw] at hjoint
  rw [← (measurePreserving_sumPiEquivProdPi_symm
    (fun i => poissonMeasure (rates i))).map_eq]
  change _ = Measure.map (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Obs d ⊕ (AuxObs d ⊕ AuxObs d) => Nat)).symm
      ((independentPoissonCountLaw (obsLaw P) u).prod
        (Measure.pi (fun i : AuxObs d ⊕ AuxObs d => poissonMeasure (rates (.inr i)))))
  rw [hjoint, Measure.map_map (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable
    ((baseline_finiteSampleHistogram_measurable).prodMap hH)]
  rfl

/-- [Under the stated inputs and conditions](hyp:d,P,i,u,tp,t), Every atom has its prescribed Poisson marginal in the three-pool law.  This gives [the stated result](goal).-/
-- @node: hybrid_prefix_count_marginal
lemma hybrid_prefix_count_marginal {d : Nat} (P : DiscreteLaw d) (u tp t : NNReal)
    (i : Obs d ⊕ (AuxObs d ⊕ AuxObs d)) :
    (hybridPoissonPrefixLaw P u tp t).map (fun s => hybridPrefixCounts s i) =
      poissonMeasure (Sum.elim (fun z => u * ((obsLaw P) {z}).toNNReal)
        (Sum.elim (fun z => tp * ((auxMarginal P).toMeasure {z}).toNNReal)
          (fun z => t * ((auxMarginal P).toMeasure {z}).toNNReal)) i) := by
  rw [show (fun s => hybridPrefixCounts s i) =
    (fun c : Obs d ⊕ (AuxObs d ⊕ AuxObs d) → Nat => c i) ∘ hybridPrefixCounts by rfl,
    ← Measure.map_map (by fun_prop) (hybridPrefixCounts_measurable d),
    hybrid_prefix_counts_law]
  exact (measurePreserving_eval _ i).map_eq

/-- [Under the stated inputs and conditions](hyp:d,P,u,tp,t), All atom counts are mutually independent across cells and across pools.  This gives [the stated result](goal).-/
-- @node: hybrid_prefix_counts_independent
lemma hybrid_prefix_counts_independent {d : Nat} (P : DiscreteLaw d) (u tp t : NNReal) :
    iIndepFun (fun i s => hybridPrefixCounts s i) (hybridPoissonPrefixLaw P u tp t) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((measurable_pi_apply i).comp (hybridPrefixCounts_measurable d)).aemeasurable)).2
  simp only [Function.comp_def]
  simp_rw [hybrid_prefix_count_marginal]
  exact hybrid_prefix_counts_law P u tp t

/-- Under the stated inputs and conditions, The outcome success counts and both marginal pools form the independent arm experiment.  This gives [the stated result](goal). -/
-- @node: hybrid_prefix_arm_counts_independent
lemma hybrid_prefix_arm_counts_independent {d : Nat} (P : DiscreteLaw d)
    (u tp t : NNReal) :
    iIndepFun (fun i : Fin 3 × Bool × Fin d => fun s => hybridPrefixCounts s
      (if i.1 = 0 then Sum.inl (i.2.2,i.2.1,true)
       else if i.1 = 1 then Sum.inr (Sum.inl (i.2.2,i.2.1))
       else Sum.inr (Sum.inr (i.2.2,i.2.1)))) (hybridPoissonPrefixLaw P u tp t) := by
  apply (hybrid_prefix_counts_independent P u tp t).precomp
  rintro ⟨i,a,j⟩ ⟨i',a',j'⟩ h
  fin_cases i <;> fin_cases i' <;> simp_all

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,u,tp,t), Outcome success counts have mean intensity times the marked mass.  This gives [the stated result](goal).-/
-- @node: hybrid_prefix_success_count_law
lemma hybrid_prefix_success_count_law {d : Nat} (P : DiscreteLaw d)
    (u tp t : NNReal) (j : Fin d) (a : Bool) :
    (hybridPoissonPrefixLaw P u tp t).map
      (fun s => hybridPrefixCounts s (Sum.inl (j,a,true))) =
      poissonMeasure (u * Real.toNNReal (markedMass P j a)) := by
  rw [hybrid_prefix_count_marginal]
  simp [obsLaw, markedMass, jointMass]

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,u,tp,t), Pilot arm counts have mean pilot intensity times the arm mass.  This gives [the stated result](goal).-/
-- @node: hybrid_prefix_pilot_count_law
lemma hybrid_prefix_pilot_count_law {d : Nat} (P : DiscreteLaw d)
    (u tp t : NNReal) (j : Fin d) (a : Bool) :
    (hybridPoissonPrefixLaw P u tp t).map
      (fun s => hybridPrefixCounts s (Sum.inr (Sum.inl (j,a)))) =
      poissonMeasure (tp * Real.toNNReal (armMass P j a)) := by
  rw [hybrid_prefix_count_marginal]
  simp [← auxMarginal_toReal_armMass]

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,u,tp,t), Factorial arm counts have mean factorial intensity times the arm mass.  This gives [the stated result](goal).-/
-- @node: hybrid_prefix_factorial_count_law
lemma hybrid_prefix_factorial_count_law {d : Nat} (P : DiscreteLaw d)
    (u tp t : NNReal) (j : Fin d) (a : Bool) :
    (hybridPoissonPrefixLaw P u tp t).map
      (fun s => hybridPrefixCounts s (Sum.inr (Sum.inr (j,a)))) =
      poissonMeasure (t * Real.toNNReal (armMass P j a)) := by
  rw [hybrid_prefix_count_marginal]
  simp [← auxMarginal_toReal_armMass]

end CausalSmith.Stat.AnnotationRarearmFrontier
