import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FinitePoissonHistogram
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseObservationSufficiency

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: denseSignCell
/-- For [the specified data point or sample](hyp:z), the [dense sign cell records the alphabet cell and whether treatment and outcome agree](goal). -/
noncomputable def denseSignCell {d : ℕ} (z : Obs d) : Fin d × Fin 2 :=
  (z.1, if z.2.1 = z.2.2 then 0 else 1)

-- @node: measurable_denseSignCell
/-- [the stated measurable dense sign cell relation holds](goal). -/
@[fun_prop]
lemma measurable_denseSignCell {d : ℕ} : Measurable (denseSignCell : Obs d → Fin d × Fin 2) := by
  exact measurable_of_countable _

-- @node: denseSignCell_mass_zero
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), then [under the zero contrast, every dense sign cell has mass $1/(2d)$](goal). -/
lemma denseSignCell_mass_zero {d : ℕ} (hd : 2 ≤ d) (x : Fin d) (j : Fin 2) :
    obsLaw (observedMarginal (denseLaw (denseZeroContrast d hd)))
      (denseSignCell ⁻¹' {(x,j)}) = ENNReal.ofReal (1 / (2 * d : ℝ)) := by
  rw [← Measure.map_apply measurable_denseSignCell (MeasurableSet.singleton (x,j))]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [obsLaw, PMF.toMeasure_map _ (f := denseSignCell) measurable_denseSignCell,
    PMF.toMeasure_apply_singleton]
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun z _hz ↦ by
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  have hatom (z : Obs d) :
      ((observedMarginal (denseLaw (denseZeroContrast d hd))).pmf z).toReal =
        1 / (4 * d : ℝ) := by
    rw [show ((observedMarginal (denseLaw (denseZeroContrast d hd))).pmf z).toReal =
      jointMass (observedMarginal (denseLaw (denseZeroContrast d hd))) z.1 z.2.1 z.2.2 by rfl,
      denseObservedAtomMass]
    simp [denseZeroContrast]
  have hite (p : Prop) [Decidable p] (a : ENNReal) :
      (if p then a else 0).toReal = if p then a.toReal else 0 := by
    split_ifs <;> simp_all
  simp_rw [hite, hatom]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have harith : (d : ℝ) * ((d : ℝ)⁻¹ * 4⁻¹ * 2) * 2 = 1 := by
    field_simp [hd0]
    norm_num
  have hsum (c : ℝ) : ∑ x' : Fin d, (if x = x' then c else 0) = c := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _hb hbx
      simp [Ne.symm hbx]
    · simp
  fin_cases j <;>
    simp [denseSignCell, Fintype.sum_prod_type]
  all_goals try measurability
  all_goals
    rw [Finset.sum_add_distrib, hsum]
    ring

-- @node: denseRegroupCounts
/-- For [the specified count table](hyp:c), the [regrouped dense counts pair the two sign-category counts within each alphabet cell](goal). -/
noncomputable def denseRegroupCounts {d : ℕ} (c : Fin d × Fin 2 → ℕ) :
    Fin d → DenseSignCounts := fun x ↦ (c (x, 0), c (x, 1))

-- @node: measurable_denseRegroupCounts
/-- [the stated measurable dense regroup counts relation holds](goal). -/
@[fun_prop]
lemma measurable_denseRegroupCounts {d : ℕ} :
    Measurable (denseRegroupCounts : (Fin d × Fin 2 → ℕ) →
      Fin d → DenseSignCounts) := by
  exact measurable_of_countable _

-- @node: denseSignStatistic_eq_regroupHistogram
/-- [the dense sign statistic equals the regrouped observation histogram](goal). -/
lemma denseSignStatistic_eq_regroupHistogram {d : ℕ} (s : DensePoissonSample d) :
    denseSignStatistic s = denseRegroupCounts (finitePoissonHistogram denseSignCell s) := by
  classical
  funext x
  unfold denseSignStatistic denseRegroupCounts finitePoissonHistogram denseSignCell
  congr 1 <;> apply congrArg Finset.card <;> ext i <;> simp

-- @node: map_denseRegroupCounts_pi_poisson
/-- [the stated map dense regroup counts product poisson relation holds](goal). -/
lemma map_denseRegroupCounts_pi_poisson (d : ℕ) (r : NNReal) :
    Measure.map denseRegroupCounts
        (Measure.pi (fun _ : Fin d × Fin 2 ↦ poissonMeasure r)) =
      Measure.pi (fun _ : Fin d ↦
        (poissonMeasure r).prod (poissonMeasure r)) := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply measurable_denseRegroupCounts (MeasurableSet.singleton v)]
  have hpre : denseRegroupCounts ⁻¹' {v} =
      {fun z : Fin d × Fin 2 ↦ if z.2 = 0 then (v z.1).1 else (v z.1).2} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hc
      funext z
      rcases z with ⟨zx, zj⟩
      have hx := congrFun hc zx
      fin_cases zj
      · exact congrArg Prod.fst hx
      · exact congrArg Prod.snd hx
    · intro hc
      funext x
      apply Prod.ext
      · simpa [denseRegroupCounts] using congrFun hc (x, 0)
      · simpa [denseRegroupCounts] using congrFun hc (x, 1)
  rw [hpre, Measure.pi_singleton]
  rw [Measure.pi_singleton]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro x _hx
  rw [Fin.prod_univ_two]
  rw [show ({v x} : Set DenseSignCounts) = {(v x).1} ×ˢ {(v x).2} by
    ext z
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod]
  simp

-- @node: map_denseSignStatistic_baseline
/-- If [the alphabet size satisfies its stated restriction](hyp:hd), then [the stated map dense sign statistic baseline relation holds](goal). -/
lemma map_denseSignStatistic_baseline {n d : ℕ} (hd : 2 ≤ d) :
    Measure.map denseSignStatistic
        (finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw (denseZeroContrast d hd))))
          (Real.toNNReal (2 * n))) =
      Measure.pi (fun _ : Fin d ↦ denseSignBaseline (poissonCellIntensity n d)) := by
  rw [show Measure.map denseSignStatistic _ =
      Measure.map denseRegroupCounts
        (Measure.map (finitePoissonHistogram denseSignCell)
          (finitePoissonSampleLaw
            (obsLaw (observedMarginal (denseLaw (denseZeroContrast d hd))))
            (Real.toNNReal (2 * n)))) by
    rw [Measure.map_map measurable_denseRegroupCounts
      (measurable_finitePoissonHistogram denseSignCell measurable_denseSignCell)]
    congr 1
    funext s
    exact denseSignStatistic_eq_regroupHistogram s]
  rw [finitePoissonHistogram_law _ denseSignCell measurable_denseSignCell]
  have hmean (z : Fin d × Fin 2) :
      Real.toNNReal (2 * n) *
          (obsLaw (observedMarginal (denseLaw (denseZeroContrast d hd)))
            (denseSignCell ⁻¹' {z})).toNNReal =
        (poissonCellIntensity n d / 2).toNNReal := by
    rw [denseSignCell_mass_zero hd z.1 z.2]
    apply NNReal.eq
    push_cast
    rw [ENNReal.toReal_ofReal (by positivity)]
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [Real.coe_toNNReal _ (by unfold poissonCellIntensity; positivity)]
    simp [poissonCellIntensity]
    field_simp
  simp_rw [hmean]
  rw [map_denseRegroupCounts_pi_poisson]
  congr 1

-- @node: map_denseSignStatistic_denseLaw
/-- [the stated map dense sign statistic dense law relation holds](goal). -/
lemma map_denseSignStatistic_denseLaw {n d : ℕ} (theta : DenseContrast d) :
    Measure.map denseSignStatistic
        (finitePoissonSampleLaw (obsLaw (observedMarginal (denseLaw theta)))
          (Real.toNNReal (2 * n))) =
      Measure.pi (fun x : Fin d ↦
        denseSignLaw (poissonCellIntensity n d) (theta.1 x)) := by
  let Q0 := finitePoissonSampleLaw
    (obsLaw (observedMarginal (denseLaw (denseZeroContrast d theta.2.1))))
    (Real.toNNReal (2 * n))
  let g : (Fin d → DenseSignCounts) → ENNReal := fun r ↦
    ∏ x, ENNReal.ofReal (oneCellLikelihood 0 (theta.1 x) (r x))
  have hg : Measurable g := measurable_of_countable _
  have hfactor : denseSampleLikelihoodENN theta = g ∘ denseSignStatistic := by
    funext s
    rw [denseSampleLikelihoodENN_factors]
    rfl
  rw [densePoissonSampleLaw_eq_withDensity, hfactor]
  apply Measure.ext_of_singleton
  intro r
  rw [map_withDensity_comp_singleton Q0 denseSignStatistic
    measurable_denseSignStatistic g hg]
  rw [show Measure.map denseSignStatistic Q0 =
      Measure.pi (fun _ : Fin d ↦ denseSignBaseline (poissonCellIntensity n d)) by
    exact map_denseSignStatistic_baseline theta.2.1]
  letI (_x : Fin d) : IsProbabilityMeasure
      (denseSignBaseline (poissonCellIntensity n d)) := by
    unfold denseSignBaseline
    infer_instance
  letI (x : Fin d) : IsProbabilityMeasure
      (denseSignLaw (poissonCellIntensity n d) (theta.1 x)) := by
    unfold denseSignLaw
    infer_instance
  rw [Measure.pi_singleton, Measure.pi_singleton]
  unfold g
  rw [← Finset.prod_mul_distrib]
  congr 1
  funext x
  rw [denseSignLaw_eq_withDensity]
  · rw [withDensity_apply _ (MeasurableSet.singleton (r x)), lintegral_singleton]
    rfl
  · unfold poissonCellIntensity
    positivity
  · rw [abs_le]
    constructor <;> linarith [(theta.2.2 x).1, (theta.2.2 x).2]

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
