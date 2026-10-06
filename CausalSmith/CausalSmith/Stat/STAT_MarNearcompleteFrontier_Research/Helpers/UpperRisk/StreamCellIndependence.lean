module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamRiskAssembly
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Independence of Poisson stream histograms across cells

Singleton histogram counts are independent within each Poisson stream and
across the four streams. Disjoint cell coordinates therefore supply independent
missing-membership corrections.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- The singleton counts in each of the four finite Poisson streams. Given [the specified input `d`](hyp:d), [the specified input `i`](hyp:i), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_streamHistogram
noncomputable def upper_streamHistogram {d : ℕ}
    (streams : Fin 4 → FiniteSample (Obs d)) (i : Fin 4) (o : Obs d) : ℕ :=
  finiteSampleHistogram (streams i).points o

/-- Every histogram coordinate is a measurable count statistic. Given [the specified input `d`](hyp:d), [the specified input `i`](hyp:i), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_measurable_streamHistogram
lemma upper_measurable_streamHistogram {d : ℕ} (i : Fin 4) (o : Obs d) :
    Measurable (fun streams => upper_streamHistogram streams i o) := by
  exact (measurable_pi_apply o).comp
    (measurable_finiteSampleHistogram.comp (measurable_pi_apply i))

/-- A stream histogram has the independent singleton Poisson count law. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `i`](hyp:i), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamHistogram_law
lemma upper_streamHistogram_law {n d : ℕ} (P : FullLaw d) (i : Fin 4) :
    (fourStreamLaw n P).map (fun streams => upper_streamHistogram streams i) =
      independentPoissonCountLaw (observedLaw P).toMeasure
        (((n : NNReal) / 2) * uniformFourMass i) := by
  classical
  let ν : Fin 4 → Measure (FiniteSample (Obs d)) := fun i =>
    finitePoissonSampleLaw (observedLaw P).toMeasure
      (((n : NNReal) / 2) * uniformFourMass i)
  have hμ : fourStreamLaw n P = Measure.pi ν :=
    labeledStreamLaw_eq_independent _ _ _ _
  have hs : (fourStreamLaw n P).map (fun streams => streams i) = ν i := by
    rw [hμ]
    simpa [ν] using Measure.pi_map_eval (μ := ν) i
  change (fourStreamLaw n P).map
    ((fun z : FiniteSample (Obs d) => finiteSampleHistogram z.points) ∘
      (fun streams => streams i)) = _
  rw [← Measure.map_map measurable_finiteSampleHistogram (measurable_pi_apply i), hs]
  exact finitePoissonSampleLaw_map_histogram _ _

/-- The entire family of stream-by-atom counts is independent. This combines
Poisson splitting within each stream with independence of the four streams. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamHistogram_iIndepFun
lemma upper_streamHistogram_iIndepFun {n d : ℕ} (P : FullLaw d) :
    iIndepFun (fun p : Fin 4 × Obs d =>
      fun streams => upper_streamHistogram streams p.1 p.2) (fourStreamLaw n P) := by
  classical
  let := upper_fourStreamLaw_isProbabilityMeasure (n := n) P
  let ν : Fin 4 → Measure (FiniteSample (Obs d)) := fun i =>
    finitePoissonSampleLaw (observedLaw P).toMeasure
      (((n : NNReal) / 2) * uniformFourMass i)
  have hμ : fourStreamLaw n P = Measure.pi ν :=
    labeledStreamLaw_eq_independent _ _ _ _
  apply iIndepFun_uncurry' (fun i o => upper_measurable_streamHistogram i o)
  · have hi : iIndepFun (fun i (streams : Fin 4 → FiniteSample (Obs d)) => streams i)
        (fourStreamLaw n P) := by
      rw [hμ]
      exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    exact hi.comp (fun _ z => finiteSampleHistogram z.points)
      (fun _ => measurable_finiteSampleHistogram)
  · intro i
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun o => (upper_measurable_streamHistogram i o).aemeasurable),
      upper_streamHistogram_law]
    have he (o : Obs d) :
        (fourStreamLaw n P).map (fun streams => upper_streamHistogram streams i o) =
          poissonMeasure ((((n : NNReal) / 2) * uniformFourMass i) *
            (((observedLaw P).toMeasure {o}).toNNReal)) := by
      change (fourStreamLaw n P).map
        ((fun counts : Obs d → ℕ => counts o) ∘
          (fun streams => upper_streamHistogram streams i)) = _
      rw [← Measure.map_map (measurable_pi_apply o)
        (measurable_pi_lambda _ (upper_measurable_streamHistogram i)),
        upper_streamHistogram_law]
      simpa [independentPoissonCountLaw] using
        (Measure.pi_map_eval (μ := fun o : Obs d =>
          poissonMeasure ((((n : NNReal) / 2) * uniformFourMass i) *
            (((observedLaw P).toMeasure {o}).toNNReal))) o)
    simp_rw [he]
    rfl

/-- Coordinates belonging to one observed covariate-treatment-surrogate cell. Given [the specified input `d`](hyp:d), [the specified input `j`](hyp:j), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_cellCoordinates
noncomputable def upper_cellCoordinates {d : ℕ} (j : Fin d × Bool × Bool) :
    Finset (Fin 4 × Obs d) := by
  classical
  exact Finset.univ.filter (fun p => inCell p.2 j.1 j.2.1 j.2.2)

/-- Distinct cells use disjoint singleton histogram coordinates. Given [the specified input `d`](hyp:d), [the specified input `j`](hyp:j), [the specified input `k`](hyp:k), [the specified input `hjk`](hyp:hjk), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_cellCoordinates_disjoint
lemma upper_cellCoordinates_disjoint {d : ℕ} {j k : Fin d × Bool × Bool}
    (hjk : j ≠ k) : Disjoint (upper_cellCoordinates j) (upper_cellCoordinates k) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hpk
  have hj : inCell p.2 j.1 j.2.1 j.2.2 := by
    simpa [upper_cellCoordinates] using hp
  have hk : inCell p.2 k.1 k.2.1 k.2.2 := by
    simpa [upper_cellCoordinates] using hpk
  apply hjk
  unfold inCell at hj hk
  exact Prod.ext (hj.1.symm.trans hk.1)
    (Prod.ext (hj.2.1.symm.trans hk.2.1) (hj.2.2.symm.trans hk.2.2))

/-- The complete count vectors for two distinct cells are independent. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `j`](hyp:j), [the specified input `k`](hyp:k), [the specified input `hjk`](hyp:hjk), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_cellHistogram_indepFun
lemma upper_cellHistogram_indepFun {n d : ℕ} (P : FullLaw d)
    {j k : Fin d × Bool × Bool} (hjk : j ≠ k) :
    IndepFun
      (fun streams (p : upper_cellCoordinates j) =>
        upper_streamHistogram streams p.val.1 p.val.2)
      (fun streams (p : upper_cellCoordinates k) =>
        upper_streamHistogram streams p.val.1 p.val.2) (fourStreamLaw n P) := by
  exact (upper_streamHistogram_iIndepFun P).indepFun_finset
    (upper_cellCoordinates j) (upper_cellCoordinates k)
    (upper_cellCoordinates_disjoint hjk)
    (fun p => upper_measurable_streamHistogram p.1 p.2)

/-- An event count is the sum of its singleton histogram counts. Given [the specified input `d`](hyp:d), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). Given [the specified input `sample`](hyp:sample). -/
-- @node: upper_finiteStreamCount_eq_histogram_sum
lemma upper_finiteStreamCount_eq_histogram_sum {d : ℕ}
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

/-- Extend a cell's count vector by zero outside that cell. Given [the specified input `d`](hyp:d), [the specified input `j`](hyp:j), [the specified input `v`](hyp:v), [the specified input `i`](hyp:i), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_extendCellHistogram
noncomputable def upper_extendCellHistogram {d : ℕ} (j : Fin d × Bool × Bool)
    (v : upper_cellCoordinates j → ℕ) (i : Fin 4) (o : Obs d) : ℕ := by
  classical
  exact if hp : (i, o) ∈ upper_cellCoordinates j then v ⟨(i, o), hp⟩ else 0

/-- Counts formed from the zero extension of a cell histogram. Given [the specified input `d`](hyp:d), [the specified input `j`](hyp:j), [the specified input `v`](hyp:v), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_cellHistogramCount
noncomputable def upper_cellHistogramCount {d : ℕ} (j : Fin d × Bool × Bool)
    (v : upper_cellCoordinates j → ℕ) (i : Fin 4) (E : Obs d → Prop) : ℝ := by
  classical
  exact ∑ o : Obs d, if E o then (upper_extendCellHistogram j v i o : ℝ) else 0

/-- Any event supported on a cell can be counted from that cell's histogram. Given [the specified input `d`](hyp:d), [the specified input `j`](hyp:j), [the specified input `i`](hyp:i), [the specified input `E`](hyp:E), [the specified input `hE`](hyp:hE), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_cellHistogramCount_eq
lemma upper_cellHistogramCount_eq {d : ℕ} (j : Fin d × Bool × Bool)
    (streams : Fin 4 → FiniteSample (Obs d)) (i : Fin 4) (E : Obs d → Prop)
    (hE : ∀ o, E o → inCell o j.1 j.2.1 j.2.2) :
    upper_cellHistogramCount j
      (fun p => upper_streamHistogram streams p.val.1 p.val.2) i E =
      finiteStreamCount (streams i) E := by
  classical
  rw [upper_finiteStreamCount_eq_histogram_sum]
  unfold upper_cellHistogramCount
  apply Finset.sum_congr rfl
  intro o ho
  by_cases he : E o
  · have hp : (i, o) ∈ upper_cellCoordinates j := by
      simpa [upper_cellCoordinates] using hE o he
    simp [he, upper_extendCellHistogram, hp, upper_streamHistogram]
  · simp [he]

/-- The selected correction is a function of just one cell's count vector. Given [the specified input `d`](hyp:d), [the specified input `n`](hyp:n), [the specified input `j`](hyp:j), [the specified input `v`](hyp:v), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_cellHistogramCorrection
noncomputable def upper_cellHistogramCorrection {d : ℕ} (n : ℕ)
    (j : Fin d × Bool × Bool) (v : upper_cellCoordinates j → ℕ) : ℝ :=
  let M := upper_cellHistogramCount j v 1
    (fun o => inCell o j.1 j.2.1 j.2.2 ∧ o.R = false)
  let Cp := upper_cellHistogramCount j v 2
    (fun o => inCell o j.1 j.2.1 j.2.2 ∧ o.R = true)
  let C := upper_cellHistogramCount j v 3
    (fun o => inCell o j.1 j.2.1 j.2.2 ∧ o.R = true)
  let U := upper_cellHistogramCount j v 3
    (fun o => inCell o j.1 j.2.1 j.2.2 ∧ o.RY = true)
  M / ((n : ℝ) / 8) *
    (if Cp ≤ polyThreshold n / 4 then lightCorrection n C U else heavyCorrection C U)

/-- A cell correction agrees exactly with its histogram representation. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `j`](hyp:j), [the stated mathematical conclusion holds](goal). Given [the specified input `streams`](hyp:streams). -/
-- @node: upper_cellHistogramCorrection_eq
lemma upper_cellHistogramCorrection_eq {n d : ℕ} (j : Fin d × Bool × Bool)
    (streams : Fin 4 → FiniteSample (Obs d)) :
    upper_cellHistogramCorrection n j
      (fun p => upper_streamHistogram streams p.val.1 p.val.2) =
      streamCellCorrection n d streams j.1 j.2.1 j.2.2 := by
  unfold upper_cellHistogramCorrection
  have hc (i : Fin 4) (F : Obs d → Prop) :
      upper_cellHistogramCount j
        (fun p => upper_streamHistogram streams p.val.1 p.val.2) i
        (fun o => inCell o j.1 j.2.1 j.2.2 ∧ F o) =
      finiteStreamCount (streams i) (fun o => inCell o j.1 j.2.1 j.2.2 ∧ F o) :=
    upper_cellHistogramCount_eq j streams i _ (fun _ h => h.1)
  simp only [hc]
  rfl

/-- The histogram representation of a cell correction is measurable. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `j`](hyp:j), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_measurable_cellHistogramCorrection
lemma upper_measurable_cellHistogramCorrection {n d : ℕ} (j : Fin d × Bool × Bool) :
    Measurable (upper_cellHistogramCorrection n j) := by
  fun_prop

/-- Corrections from distinct cells are independent, even though their pilot
and outcome branches within a cell can be dependent. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `j`](hyp:j), [the specified input `k`](hyp:k), [the specified input `hjk`](hyp:hjk), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamCellCorrection_indepFun
lemma upper_streamCellCorrection_indepFun {n d : ℕ} (P : FullLaw d)
    {j k : Fin d × Bool × Bool} (hjk : j ≠ k) :
    IndepFun (fun streams => streamCellCorrection n d streams j.1 j.2.1 j.2.2)
      (fun streams => streamCellCorrection n d streams k.1 k.2.1 k.2.2)
      (fourStreamLaw n P) := by
  have hi := (upper_cellHistogram_indepFun (n := n) P hjk).comp
    (upper_measurable_cellHistogramCorrection (n := n) j)
    (upper_measurable_cellHistogramCorrection (n := n) k)
  simpa only [Function.comp_def, upper_cellHistogramCorrection_eq] using hi

end CausalSmith.Stat.MarNearcompleteFrontier
