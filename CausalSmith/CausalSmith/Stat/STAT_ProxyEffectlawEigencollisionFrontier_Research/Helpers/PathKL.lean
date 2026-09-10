import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathCertificates
import Causalean.Stat.Minimax.ChiSquaredFinite
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-! Finite observed-carrier and chi-square certificates for the labelled path. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- KL divergence is bounded by chi-square divergence. -/
-- @node: klDiv_le_chiSqDiv
lemma klDiv_le_chiSqDiv {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Finite Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    InformationTheory.klDiv μ ν ≤ ENNReal.ofReal (Causalean.Stat.chiSqDiv μ ν) := by
  rw [InformationTheory.klDiv_eq_integral_klFun,
    if_pos ⟨hac, Integrable.of_finite⟩]
  apply ENNReal.ofReal_le_ofReal
  rw [Causalean.Stat.chiSqDiv]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x =>
      InformationTheory.klFun_nonneg ENNReal.toReal_nonneg
  · exact Integrable.of_finite
  · filter_upwards with x
    let r := (μ.rnDeriv ν x).toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    by_cases hzero : r = 0
    · simp [InformationTheory.klFun_apply, r, hzero]
    · have hlog := Real.log_le_sub_one_of_pos (lt_of_le_of_ne hr (Ne.symm hzero))
      rw [InformationTheory.klFun_apply]
      nlinarith [mul_le_mul_of_nonneg_left hlog hr]

/-- The finite sixteen-cell carrier of one observed labelled-path record. -/
-- @node: PathVisibleCell
abbrev PathVisibleCell := Bool × Bool × Bool × Bool

/-- The atomic law of the four visible Bernoulli coordinates. -/
-- @node: pathVisibleCoefficient
noncomputable def pathVisibleCoefficient (g h : ℝ) (v : PathVisibleCell) : ℝ≥0∞ :=
  if v.1 then
    ∑ u : Fin 2, ∑ y0 : Bool, ENNReal.ofReal (pathWeight g h u true v.2.1 v.2.2.1 y0 v.2.2.2)
  else
    ∑ u : Fin 2, ∑ y1 : Bool, ENNReal.ofReal (pathWeight g h u false v.2.1 v.2.2.1 v.2.2.2 y1)

/-- The atomic law of the four visible Bernoulli coordinates. -/
-- @node: pathVisibleLaw
noncomputable def pathVisibleLaw (g h : ℝ) : Measure PathVisibleCell :=
  ∑ v : PathVisibleCell,
    pathVisibleCoefficient g h v • Measure.dirac v

/-- Every singleton of the finite visible carrier has its explicit cell mass. -/
-- @node: pathVisibleLaw_singleton
lemma pathVisibleLaw_singleton (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (v : PathVisibleCell) :
    (pathVisibleLaw g h).real {v} = pathVisibleMass g h v.1 v.2.1 v.2.2.1 v.2.2.2 := by
  classical
  simp only [pathVisibleLaw, Measure.real_def, Measure.finsetSum_apply,
    MeasurableSet.singleton, Measure.smul_apply, Measure.dirac_apply']
  rw [Finset.sum_eq_single v]
  · simp only [Set.indicator_of_mem (Set.mem_singleton v), smul_eq_mul, Pi.one_apply, mul_one]
    unfold pathVisibleCoefficient pathVisibleMass
    split_ifs
    all_goals rw [ENNReal.toReal_sum (by simp)]
    all_goals apply Finset.sum_congr rfl
    all_goals intro u _
    all_goals rw [ENNReal.toReal_sum (by simp)]
    all_goals apply Finset.sum_congr rfl
    · intro y0 _
      rw [ENNReal.toReal_ofReal
        (pathWeight_nonneg g h hg0 hg1 hh u true v.2.1 v.2.2.1 y0 v.2.2.2)]
    · intro y1 _
      rw [ENNReal.toReal_ofReal
        (pathWeight_nonneg g h hg0 hg1 hh u false v.2.1 v.2.2.1 v.2.2.2 y1)]
  · intro w _ hw
    rw [Set.indicator_of_notMem]
    · simp
    · simpa using hw
  · simp

/-- Mapping the finite visible carrier to observation records recovers the observed margin. -/
-- @node: pathVisibleLaw_map
lemma pathVisibleLaw_map (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    letI := pathLaw_isProbabilityMeasure g h hg0 hg1
      (by constructor <;> linarith [abs_le.mp hh]) hh
    (pathVisibleLaw g h).map (fun v => pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2) =
      obsLaw (pathLaw g h) := by
  letI := pathLaw_isProbabilityMeasure g h hg0 hg1
    (by constructor <;> linarith [abs_le.mp hh]) hh
  rw [pathVisibleLaw, Measure.map_finset_sum'
    (measurable_of_finite (fun v : PathVisibleCell =>
      pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2)).aemeasurable]
  simp_rw [Measure.map_smul, Measure.map_dirac'
    (measurable_of_finite (fun v : PathVisibleCell =>
      pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2))]
  rw [obsLaw, pathLaw,
    Measure.map_finset_sum' (obsMap_measurable 2 2 2).aemeasurable]
  simp_rw [Measure.map_finset_sum' (obsMap_measurable 2 2 2).aemeasurable,
    Measure.map_smul, Measure.map_dirac' (obsMap_measurable 2 2 2)]
  simp [pathVisibleCoefficient, Fintype.sum_prod_type, Fin.sum_univ_two,
    pathObsPoint, pathPoint, witnessPoint, obsMap, add_smul]
  abel_nf

/-- The visible atomic law has total mass one on the path domain. -/
-- @node: pathVisibleLaw_isProbabilityMeasure
lemma pathVisibleLaw_isProbabilityMeasure (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : IsProbabilityMeasure (pathVisibleLaw g h) := by
  let hDomain : TangentAmplitudeDomain h := by
    constructor <;> linarith [abs_le.mp hh]
  letI hP := pathLaw_isProbabilityMeasure g h hg0 hg1 hDomain hh
  constructor
  have hmap := pathVisibleLaw_map g h hg0 hg1 hh
  have huniv := congrArg (fun μ : Measure (Obs 2 2) => μ Set.univ) hmap
  rw [Measure.map_apply (measurable_of_finite (fun v : PathVisibleCell =>
    pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2)) MeasurableSet.univ] at huniv
  simpa using huniv

/-- Every base visible cell has a uniform positive mass. -/
-- @node: pathVisibleLaw_base_floor
lemma pathVisibleLaw_base_floor (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (v : PathVisibleCell) :
    1 / 1000 ≤ (pathVisibleLaw g 0).real {v} := by
  rw [pathVisibleLaw_singleton g 0 hg0 hg1 (by norm_num)]
  exact pathVisibleMass_base_floor g hg0 hg1 _ _ _ _

/-- The displaced finite visible law is absolutely continuous with respect to the base law. -/
-- @node: pathVisibleLaw_absolutelyContinuous
lemma pathVisibleLaw_absolutelyContinuous (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4) :
    pathVisibleLaw g h ≪ pathVisibleLaw g 0 := by
  intro A hzero
  by_cases hA : A.Nonempty
  · obtain ⟨v, hv⟩ := hA
    have hmono : pathVisibleLaw g 0 {v} ≤ pathVisibleLaw g 0 A :=
      measure_mono (singleton_subset_iff.mpr hv)
    have hposReal : 0 < (pathVisibleLaw g 0).real {v} :=
      lt_of_lt_of_le (by norm_num) (pathVisibleLaw_base_floor g hg0 hg1 v)
    have hpos : pathVisibleLaw g 0 {v} ≠ 0 := by
      intro hz
      rw [Measure.real_def, hz, ENNReal.toReal_zero] at hposReal
      exact lt_irrefl 0 hposReal
    exact False.elim (hpos (nonpos_iff_eq_zero.mp (hzero ▸ hmono)))
  · rw [not_nonempty_iff_eq_empty.mp hA]
    simp

/-- The observed labelled-path law is absolutely continuous with respect to its base law. -/
-- @node: pathObsLaw_absolutelyContinuous
lemma pathObsLaw_absolutelyContinuous (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    letI := pathLaw_isProbabilityMeasure g h hg0 hg1
      (by constructor <;> linarith [abs_le.mp hh]) hh
    letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
      (by norm_num [TangentAmplitudeDomain]) (by norm_num)
    obsLaw (pathLaw g h) ≪ obsLaw (pathLaw g 0) := by
  letI := pathLaw_isProbabilityMeasure g h hg0 hg1
    (by constructor <;> linarith [abs_le.mp hh]) hh
  letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
    (by norm_num [TangentAmplitudeDomain]) (by norm_num)
  let f := fun v : PathVisibleCell => pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2
  rw [← pathVisibleLaw_map g h hg0 hg1 hh,
    ← pathVisibleLaw_map g 0 hg0 hg1 (by norm_num)]
  exact (pathVisibleLaw_absolutelyContinuous g h hg0 hg1).map (measurable_of_finite f)

/-- The labelled-path observed log likelihood ratio is integrable. -/
-- @node: pathObsLaw_llr_integrable
lemma pathObsLaw_llr_integrable (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    letI := pathLaw_isProbabilityMeasure g h hg0 hg1
      (by constructor <;> linarith [abs_le.mp hh]) hh
    letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
      (by norm_num [TangentAmplitudeDomain]) (by norm_num)
    Integrable (llr (obsLaw (pathLaw g h)) (obsLaw (pathLaw g 0)))
      (obsLaw (pathLaw g h)) := by
  letI := pathLaw_isProbabilityMeasure g h hg0 hg1
    (by constructor <;> linarith [abs_le.mp hh]) hh
  letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
    (by norm_num [TangentAmplitudeDomain]) (by norm_num)
  letI := pathVisibleLaw_isProbabilityMeasure g h hg0 hg1 hh
  letI := pathVisibleLaw_isProbabilityMeasure g 0 hg0 hg1 (by norm_num)
  let f := fun v : PathVisibleCell => pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2
  rw [← pathVisibleLaw_map g h hg0 hg1 hh,
    ← pathVisibleLaw_map g 0 hg0 hg1 (by norm_num)]
  exact InformationTheory.integrable_llr_map
    (pathVisibleLaw_absolutelyContinuous g h hg0 hg1) (measurable_of_finite f)
    Integrable.of_finite

/-- The chi-square divergence of the finite visible path is quadratically bounded. -/
-- @node: pathVisibleLaw_chiSqDiv_bound
lemma pathVisibleLaw_chiSqDiv_bound (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    Causalean.Stat.chiSqDiv (pathVisibleLaw g h) (pathVisibleLaw g 0) ≤
      16000 * g ^ 2 * h ^ 2 := by
  letI := pathVisibleLaw_isProbabilityMeasure g h hg0 hg1 hh
  letI := pathVisibleLaw_isProbabilityMeasure g 0 hg0 hg1 (by norm_num)
  have hac := pathVisibleLaw_absolutelyContinuous g h hg0 hg1
  have hformula := Causalean.Stat.finite_one_add_chiSqDiv
    (pathVisibleLaw g h) (pathVisibleLaw g 0) hac
  have hmass (μ : Measure PathVisibleCell) [IsProbabilityMeasure μ] :
      ∑ v, μ.real {v} = 1 := by
    simpa using (MeasureTheory.sum_measureReal_singleton (μ := μ) Finset.univ)
  have hidentity : Causalean.Stat.chiSqDiv (pathVisibleLaw g h) (pathVisibleLaw g 0) =
      ∑ v : PathVisibleCell,
        ((pathVisibleLaw g h).real {v} - (pathVisibleLaw g 0).real {v}) ^ 2 /
          (pathVisibleLaw g 0).real {v} := by
    have hp := hmass (pathVisibleLaw g h)
    have hq := hmass (pathVisibleLaw g 0)
    calc
      _ = (∑ v : PathVisibleCell,
          (pathVisibleLaw g h).real {v} ^ 2 / (pathVisibleLaw g 0).real {v}) - 1 := by
            linarith [hformula]
      _ = (∑ v : PathVisibleCell,
          (pathVisibleLaw g h).real {v} ^ 2 / (pathVisibleLaw g 0).real {v}) -
            2 * (∑ v : PathVisibleCell, (pathVisibleLaw g h).real {v}) +
              ∑ v : PathVisibleCell, (pathVisibleLaw g 0).real {v} := by
            rw [hp, hq]
            ring
      _ = ∑ v : PathVisibleCell,
          ((pathVisibleLaw g h).real {v} - (pathVisibleLaw g 0).real {v}) ^ 2 /
            (pathVisibleLaw g 0).real {v} := by
            symm
            calc
              _ = ∑ v : PathVisibleCell,
                  (((pathVisibleLaw g h).real {v} ^ 2 /
                    (pathVisibleLaw g 0).real {v} -
                    2 * (pathVisibleLaw g h).real {v}) +
                    (pathVisibleLaw g 0).real {v}) := by
                  apply Finset.sum_congr rfl
                  intro v _
                  have hqpos : 0 < (pathVisibleLaw g 0).real {v} :=
                    lt_of_lt_of_le (by norm_num) (pathVisibleLaw_base_floor g hg0 hg1 v)
                  field_simp
                  ring
              _ = _ := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                    ← Finset.mul_sum]
  rw [hidentity]
  calc
    _ ≤ ∑ _v : PathVisibleCell, 1000 * g ^ 2 * h ^ 2 := by
      apply Finset.sum_le_sum
      intro v _
      have hqfloor := pathVisibleLaw_base_floor g hg0 hg1 v
      have hdiff := pathVisibleMass_diff_bound g h hg0 hh v.1 v.2.1 v.2.2.1 v.2.2.2
      rw [← pathVisibleLaw_singleton g h hg0 hg1 hh,
        ← pathVisibleLaw_singleton g 0 hg0 hg1 (by norm_num)] at hdiff
      have hqpos : 0 < (pathVisibleLaw g 0).real {v} :=
        lt_of_lt_of_le (by norm_num) hqfloor
      rw [div_le_iff₀ hqpos]
      have hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg hg0 (abs_nonneg h)) |>.2 hdiff
      rw [sq_abs] at hsq
      calc
        _ ≤ (g * |h|) ^ 2 := hsq
        _ = g ^ 2 * h ^ 2 := by rw [mul_pow, sq_abs]
        _ ≤ 1000 * g ^ 2 * h ^ 2 * (pathVisibleLaw g 0).real {v} := by
          have hs : 1 ≤ 1000 * (pathVisibleLaw g 0).real {v} := by nlinarith
          have hn : 0 ≤ g ^ 2 * h ^ 2 := mul_nonneg (sq_nonneg g) (sq_nonneg h)
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hs hn)
    _ = 16000 * g ^ 2 * h ^ 2 := by
      norm_num [Fintype.card_prod]
      ring

/-- The observed one-record KL divergence along the labelled path is quadratic in `g*h`. -/
-- @node: pathLaw_observed_kl_bound
lemma pathLaw_observed_kl_bound (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    letI := pathLaw_isProbabilityMeasure g h hg0 hg1
      (by constructor <;> linarith [abs_le.mp hh]) hh
    letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
      (by norm_num [TangentAmplitudeDomain]) (by norm_num)
    InformationTheory.klDiv (obsLaw (pathLaw g h)) (obsLaw (pathLaw g 0)) ≤
      ENNReal.ofReal (16000 * g ^ 2 * h ^ 2) := by
  letI := pathLaw_isProbabilityMeasure g h hg0 hg1
    (by constructor <;> linarith [abs_le.mp hh]) hh
  letI := pathLaw_isProbabilityMeasure g 0 hg0 hg1
    (by norm_num [TangentAmplitudeDomain]) (by norm_num)
  letI := pathVisibleLaw_isProbabilityMeasure g h hg0 hg1 hh
  letI := pathVisibleLaw_isProbabilityMeasure g 0 hg0 hg1 (by norm_num)
  rw [← pathVisibleLaw_map g h hg0 hg1 hh,
    ← pathVisibleLaw_map g 0 hg0 hg1 (by norm_num)]
  calc
    _ ≤ InformationTheory.klDiv (pathVisibleLaw g h) (pathVisibleLaw g 0) :=
      InformationTheory.klDiv_map_le (pathVisibleLaw g h) (pathVisibleLaw g 0)
        (measurable_of_finite _)
    _ ≤ ENNReal.ofReal (Causalean.Stat.chiSqDiv
        (pathVisibleLaw g h) (pathVisibleLaw g 0)) :=
      klDiv_le_chiSqDiv _ _ (pathVisibleLaw_absolutelyContinuous g h hg0 hg1)
    _ ≤ ENNReal.ofReal (16000 * g ^ 2 * h ^ 2) :=
      ENNReal.ofReal_le_ofReal (pathVisibleLaw_chiSqDiv_bound g h hg0 hg1 hh)

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
