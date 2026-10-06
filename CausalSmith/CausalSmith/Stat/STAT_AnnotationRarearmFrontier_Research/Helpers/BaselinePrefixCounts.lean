module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.BaselinePoissonRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.FinitePrefixTransfer
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.Basic
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw

/-!
Exact thinning laws for the two independent ordered Poisson pools of the baseline.
The complete-record and auxiliary histograms are joined before selecting arm counts.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory Causalean.Stat
open scoped BigOperators ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix

/-- The complete-record law is a probability measure. -/
-- @node: baseline_obsLaw_probability
instance baseline_obsLaw_probability {d : Nat} (P : DiscreteLaw d) :
    IsProbabilityMeasure (obsLaw P) := by
  unfold obsLaw
  infer_instance

/-- The histogram of an ordered finite sample on a finite alphabet is measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: baseline_finiteSampleHistogram_measurable
lemma baseline_finiteSampleHistogram_measurable {X : Type*} [Finite X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X] :
    Measurable (fun s : FiniteSample X => finiteSampleHistogram s.points) := by
  apply measurable_to_countable'
  intro c
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet {x : Fin n → X | finiteSampleHistogram x = c}
  exact Set.Finite.measurableSet (Set.toFinite _)

/-- The full histogram of both pools, with disjoint indices for the two channels. -/
-- @node: baselinePrefixCounts
noncomputable def baselinePrefixCounts {d : Nat}
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d)) : Obs d ⊕ AuxObs d → Nat :=
  Sum.elim (finiteSampleHistogram s.1.points) (finiteSampleHistogram s.2.points)

/-- Both ordered finite alphabets make the joint histogram measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: baselinePrefixCounts_measurable
lemma baselinePrefixCounts_measurable (d : Nat) :
    Measurable (baselinePrefixCounts (d := d)) := by
  change Measurable ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Obs d ⊕ AuxObs d => Nat)).symm ∘
    (fun s : FiniteSample (Obs d) × FiniteSample (AuxObs d) =>
      (finiteSampleHistogram s.1.points, finiteSampleHistogram s.2.points)))
  exact (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable.comp
    ((baseline_finiteSampleHistogram_measurable.comp measurable_fst).prodMk
      (baseline_finiteSampleHistogram_measurable.comp measurable_snd))

/-- Under the stated inputs and conditions, Thinning the independent ordered prefixes gives independent Poisson counts,
including zero-mass atoms, jointly across the two channels.  This gives [the stated result](goal). -/
-- @node: baseline_prefix_counts_law
lemma baseline_prefix_counts_law {d : Nat} (P : DiscreteLaw d) (u t : NNReal) :
    (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t).map
      baselinePrefixCounts =
    Measure.pi (fun i : Obs d ⊕ AuxObs d => poissonMeasure
      (Sum.elim (fun z => u * ((obsLaw P) {z}).toNNReal)
        (fun z => t * ((auxMarginal P).toMeasure {z}).toNNReal) i)) := by
  have hleft : Measurable (fun s : FiniteSample (Obs d) => finiteSampleHistogram s.points) :=
    baseline_finiteSampleHistogram_measurable
  have hright : Measurable (fun s : FiniteSample (AuxObs d) => finiteSampleHistogram s.points) :=
    baseline_finiteSampleHistogram_measurable
  let rates : Obs d ⊕ AuxObs d → NNReal :=
    Sum.elim (fun z => u * ((obsLaw P) {z}).toNNReal)
      (fun z => t * ((auxMarginal P).toMeasure {z}).toNNReal)
  have hjoint := Measure.map_prod_map
    (finitePoissonSampleLaw (obsLaw P) u)
    (finitePoissonSampleLaw (auxMarginal P).toMeasure t) hleft hright
  rw [finitePoissonSampleLaw_map_histogram, finitePoissonSampleLaw_map_histogram] at hjoint
  have hsplit := (measurePreserving_sumPiEquivProdPi_symm
    (fun i => poissonMeasure (rates i))).map_eq
  rw [← hsplit]
  change _ = Measure.map (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Obs d ⊕ AuxObs d => Nat)).symm
      ((independentPoissonCountLaw (obsLaw P) u).prod
        (independentPoissonCountLaw (auxMarginal P).toMeasure t))
  rw [hjoint, Measure.map_map (by fun_prop) (hleft.prodMap hright)]
  rfl

/-- [Under the stated inputs and conditions](hyp:d,P,i,u,t), Each coordinate has its exact Poisson marginal under the joint prefix law.  This gives [the stated result](goal).-/
-- @node: baseline_prefix_count_marginal
lemma baseline_prefix_count_marginal {d : Nat} (P : DiscreteLaw d) (u t : NNReal)
    (i : Obs d ⊕ AuxObs d) :
    (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t).map
      (fun s => baselinePrefixCounts s i) = poissonMeasure
        (Sum.elim (fun z => u * ((obsLaw P) {z}).toNNReal)
          (fun z => t * ((auxMarginal P).toMeasure {z}).toNNReal) i) := by
  rw [show (fun s => baselinePrefixCounts s i) =
    (fun c : Obs d ⊕ AuxObs d → Nat => c i) ∘ baselinePrefixCounts by rfl,
    ← Measure.map_map (by fun_prop) (baselinePrefixCounts_measurable d),
    baseline_prefix_counts_law]
  exact (measurePreserving_eval _ i).map_eq

/-- [Under the stated inputs and conditions](hyp:d,P,u,t), The full collection of complete and auxiliary atom counts is independent.  This gives [the stated result](goal).-/
-- @node: baseline_prefix_counts_independent
lemma baseline_prefix_counts_independent {d : Nat} (P : DiscreteLaw d) (u t : NNReal) :
    iIndepFun (fun i s => baselinePrefixCounts s i)
      (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t) := by
  let : IsProbabilityMeasure (independentPoissonPrefixLaw
    (obsLaw P) (auxMarginal P).toMeasure u t) := by
    unfold independentPoissonPrefixLaw
    infer_instance
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((measurable_pi_apply i).comp (baselinePrefixCounts_measurable d)).aemeasurable)).2
  simp only [Function.comp_def]
  simp_rw [baseline_prefix_count_marginal]
  exact baseline_prefix_counts_law P u t

/-- Under the stated inputs and conditions, Selecting one arm's success counts and both marginal arm counts preserves independence.  This gives [the stated result](goal). -/
-- @node: baseline_prefix_arm_counts_independent
lemma baseline_prefix_arm_counts_independent {d : Nat} (P : DiscreteLaw d)
    (u t : NNReal) (a : Bool) :
    iIndepFun (fun i : Fin 3 × Fin d => fun s => baselinePrefixCounts s
      (if i.1 = 0 then Sum.inl (i.2, a, true)
        else if i.1 = 1 then Sum.inr (i.2, a) else Sum.inr (i.2, !a)))
      (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t) := by
  apply (baseline_prefix_counts_independent P u t).precomp
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  fin_cases i <;> fin_cases i' <;> cases a <;> simp_all

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,u,t), A complete-prefix success count has the exact marked-mass Poisson mean.  This gives [the stated result](goal).-/
-- @node: baseline_prefix_success_count_law
lemma baseline_prefix_success_count_law {d : Nat} (P : DiscreteLaw d)
    (u t : NNReal) (j : Fin d) (a : Bool) :
    (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t).map
      (fun s => baselinePrefixCounts s (Sum.inl (j,a,true))) =
        poissonMeasure (u * Real.toNNReal (markedMass P j a)) := by
  rw [baseline_prefix_count_marginal]
  simp [obsLaw, markedMass, jointMass]

/-- [Under the stated inputs and conditions](hyp:d,P,j,a,u,t), An auxiliary-prefix count has the exact arm-mass Poisson mean.  This gives [the stated result](goal).-/
-- @node: baseline_prefix_arm_count_law
lemma baseline_prefix_arm_count_law {d : Nat} (P : DiscreteLaw d)
    (u t : NNReal) (j : Fin d) (a : Bool) :
    (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t).map
      (fun s => baselinePrefixCounts s (Sum.inr (j,a))) =
        poissonMeasure (t * Real.toNNReal (armMass P j a)) := by
  rw [baseline_prefix_count_marginal]
  simp [← auxMarginal_toReal_armMass]

/-- The clipped inverse-count contrast on the two untruncated ordered prefixes. -/
-- @node: baselineOrderedPrefixStatistic
noncomputable def baselineOrderedPrefixStatistic {d : Nat} (u : NNReal)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d)) : Real :=
  let H := fun a => ∑ j : Fin d,
    (baselinePrefixCounts s (Sum.inl (j,a,true)) : Real) / (u : Real) *
      (1 + (baselinePrefixCounts s (Sum.inr (j,!a)) : Real) /
        ((baselinePrefixCounts s (Sum.inr (j,a)) : Real) + 1))
  max (-1) (min 1 (H true - H false))

/-- The ordered-prefix statistic is measurable. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: baselineOrderedPrefixStatistic_measurable
lemma baselineOrderedPrefixStatistic_measurable (d : Nat) (u : NNReal) :
    Measurable (baselineOrderedPrefixStatistic (d := d) u) := by
  unfold baselineOrderedPrefixStatistic
  fun_prop

/-- [Under the stated inputs and conditions](hyp:d,u,s), The ordered-prefix statistic takes values in the prescribed interval.  This gives [the stated result](goal).-/
-- @node: baselineOrderedPrefixStatistic_mem_Icc
lemma baselineOrderedPrefixStatistic_mem_Icc {d : Nat} (u : NNReal)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d)) :
    baselineOrderedPrefixStatistic u s ∈ Set.Icc (-1) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Under the stated inputs and conditions, The ordered Poisson prefixes satisfy the baseline contrast risk bound by
thinning, the independent-cell moment bounds, and clipping.  This gives [the stated result](goal). -/
-- @node: baseline_ordered_prefix_risk
lemma baseline_ordered_prefix_risk :
    ∃ C : Real, 0 < C ∧ ∀ (d : Nat) (eps : Real) (P : DiscreteLaw d) (u t : NNReal),
      2 ≤ d → 0 < eps → eps ≤ 1 / 4 → ModelClass d eps P → 0 < u → 0 < t →
      sqRisk
        (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t)
        (baselineOrderedPrefixStatistic u) (ateFunctional P) ≤
          C * (1 / ((u : Real) * eps) + 1 / ((t : Real) * eps)) +
            4 * ((d : Real) / (Real.exp 1 * (t : Real) * eps)) ^ 2 := by
  obtain ⟨C,hC,hbound⟩ := baseline_poisson_contrast_risk
  refine ⟨C,hC,?_⟩
  intro d eps P u t hd heps heps' hP hu ht
  let mu := independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t
  let : IsProbabilityMeasure mu := by
    unfold mu independentPoissonPrefixLaw
    infer_instance
  let Z := fun a j s => baselinePrefixCounts (d := d) s (Sum.inl (j,a,true))
  let K := fun a j s => baselinePrefixCounts (d := d) s (Sum.inr (j,a))
  have hm (a j) : Measurable (Z a j) ∧ Measurable (K a j) := by
    constructor <;> fun_prop
  have hZ (a j) : mu.map (Z a j) = poissonMeasure
      (u * Real.toNNReal (markedMass P j a)) := baseline_prefix_success_count_law P u t j a
  have hK (a j) : mu.map (K a j) = poissonMeasure
      (t * Real.toNNReal (armMass P j a)) := baseline_prefix_arm_count_law P u t j a
  have hi (a) : iIndepFun
      (fun i : Fin 3 × Fin d => if i.1 = 0 then Z a i.2
        else if i.1 = 1 then K a i.2 else K (!a) i.2) mu := by
    convert baseline_prefix_arm_counts_independent P u t a using 1
    funext i s
    dsimp [Z,K]
    split_ifs <;> rfl
  exact hbound d eps P u t _ mu Z K hd heps heps' hP hu ht hm hZ hK hi

end CausalSmith.Stat.AnnotationRarearmFrontier
