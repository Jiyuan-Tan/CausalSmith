import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathKL
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.QuotientLaw

/-! Finite-cell KL and quotient-law separation certificates for the collision witness. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The coordinate measurable structure on labelled atomic laws is their Borel structure. -/
-- @node: atomicLaw_borelSpace
instance atomicLaw_borelSpace (k : ℕ) (radius : ℝ) :
    BorelSpace (AtomicLaw k radius) where
  measurable_eq := by
    change MeasurableSpace.comap (fun ν : AtomicLaw k radius => (ν.weight, ν.atom)) _ = _
    calc
      MeasurableSpace.comap (fun ν : AtomicLaw k radius => (ν.weight, ν.atom))
          (inferInstance : MeasurableSpace ((Fin k → ℝ) × (Fin k → ℝ))) =
          MeasurableSpace.comap (fun ν : AtomicLaw k radius => (ν.weight, ν.atom))
            (borel ((Fin k → ℝ) × (Fin k → ℝ))) := by
              exact congrArg (MeasurableSpace.comap
                (fun ν : AtomicLaw k radius => (ν.weight, ν.atom)))
                (@BorelSpace.measurable_eq ((Fin k → ℝ) × (Fin k → ℝ))
                  inferInstance inferInstance inferInstance)
      _ = borel (AtomicLaw k radius) := borel_comap.symm

/-- The quotient law's mapped measurable structure contains all open sets of its installed
Wasserstein topology. -/
-- @node: lawModulo_opensMeasurableSpace
instance lawModulo_opensMeasurableSpace (k : ℕ) (radius : ℝ) :
    OpensMeasurableSpace (AtomicLaw.LawModulo k radius) where
  borel_le := by
    apply MeasurableSpace.generateFrom_le
    intro U hU
    change MeasurableSet (AtomicLaw.LawModulo.ofProbabilityLaw ⁻¹' U)
    change IsOpen (AtomicLaw.LawModulo.ofProbabilityLaw ⁻¹' U) at hU
    exact hU.measurableSet

/-- The collision witness represented on the finite visible Bernoulli carrier. -/
-- @node: witnessVisibleLaw
noncomputable def witnessVisibleLaw (eps : ℝ) : Measure PathVisibleCell :=
  pathVisibleLaw (2 * eps) 0

/-- Mapping the finite collision-witness carrier recovers its observed margin. -/
-- @node: witnessVisibleLaw_map
lemma witnessVisibleLaw_map (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1 / 8) :
    letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
    (witnessVisibleLaw eps).map
        (fun v => pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2) =
      obsLaw (witnessLaw eps) := by
  letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
  unfold witnessVisibleLaw
  have hmap := pathVisibleLaw_map (2 * eps) 0 (by positivity) (by linarith) (by norm_num)
  unfold obsLaw at hmap ⊢
  simpa [pathLaw_zero] using hmap

/-- The finite visible collision-witness law has total mass one. -/
-- @node: witnessVisibleLaw_isProbabilityMeasure
lemma witnessVisibleLaw_isProbabilityMeasure (eps : ℝ) (heps0 : 0 ≤ eps)
    (heps1 : eps ≤ 1 / 8) : IsProbabilityMeasure (witnessVisibleLaw eps) := by
  unfold witnessVisibleLaw
  exact pathVisibleLaw_isProbabilityMeasure (2 * eps) 0 (by positivity) (by linarith)
    (by norm_num)

set_option maxHeartbeats 800000 in
-- Expanding all sixteen visible cells requires a larger heartbeat budget.
/-- Each visible cell changes by at most the collision amplitude. -/
-- @node: witnessVisibleLaw_singleton_diff_bound
lemma witnessVisibleLaw_singleton_diff_bound (eps : ℝ) (heps0 : 0 ≤ eps)
    (heps1 : eps ≤ 1 / 8) (v : PathVisibleCell) :
    |(witnessVisibleLaw eps).real {v} - (witnessVisibleLaw 0).real {v}| ≤ eps := by
  unfold witnessVisibleLaw
  simp only [mul_zero]
  rw [pathVisibleLaw_singleton (2 * eps) 0 (by positivity) (by linarith) (by norm_num),
    pathVisibleLaw_singleton 0 0 (by norm_num) (by norm_num) (by norm_num)]
  rcases v with ⟨t, x, z, y⟩
  cases t <;> cases x <;> cases z <;> cases y
  all_goals
    simp only [pathVisibleMass]
    simp_rw [pathWeight_zero (2 * eps), pathWeight_zero 0]
    norm_num [witnessWeight, bernoulliMass, div_eq_mul_inv]
    apply (abs_le).2
    constructor <;> nlinarith

/-- Every base collision-witness visible cell has a uniform positive mass. -/
-- @node: witnessVisibleLaw_base_floor
lemma witnessVisibleLaw_base_floor (v : PathVisibleCell) :
    1 / 1000 ≤ (witnessVisibleLaw 0).real {v} := by
  unfold witnessVisibleLaw
  simp only [mul_zero]
  exact pathVisibleLaw_base_floor 0 (by norm_num) (by norm_num) v

/-- Every collision-witness visible law is absolutely continuous with respect to the base law. -/
-- @node: witnessVisibleLaw_absolutelyContinuous
lemma witnessVisibleLaw_absolutelyContinuous (eps : ℝ) :
    witnessVisibleLaw eps ≪ witnessVisibleLaw 0 := by
  intro A hzero
  by_cases hA : A.Nonempty
  · obtain ⟨v, hv⟩ := hA
    have hmono : witnessVisibleLaw 0 {v} ≤ witnessVisibleLaw 0 A :=
      measure_mono (singleton_subset_iff.mpr hv)
    have hposReal : 0 < (witnessVisibleLaw 0).real {v} :=
      lt_of_lt_of_le (by norm_num) (witnessVisibleLaw_base_floor v)
    have hpos : witnessVisibleLaw 0 {v} ≠ 0 := by
      intro hz
      rw [Measure.real_def, hz, ENNReal.toReal_zero] at hposReal
      exact lt_irrefl 0 hposReal
    exact False.elim (hpos (nonpos_iff_eq_zero.mp (hzero ▸ hmono)))
  · rw [not_nonempty_iff_eq_empty.mp hA]
    simp

/-- The observed collision-witness law is absolutely continuous with respect to the base law. -/
-- @node: witnessObsLaw_absolutelyContinuous
lemma witnessObsLaw_absolutelyContinuous (eps : ℝ) (heps0 : 0 ≤ eps)
    (heps1 : eps ≤ 1 / 8) :
    letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
    letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
    obsLaw (witnessLaw eps) ≪ obsLaw (witnessLaw 0) := by
  letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
  letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  let f := fun v : PathVisibleCell => pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2
  rw [← witnessVisibleLaw_map eps heps0 heps1,
    ← witnessVisibleLaw_map 0 (by norm_num) (by norm_num)]
  exact (witnessVisibleLaw_absolutelyContinuous eps).map (measurable_of_finite f)

/-- The collision-witness observed log likelihood ratio is integrable. -/
-- @node: witnessObsLaw_llr_integrable
lemma witnessObsLaw_llr_integrable (eps : ℝ) (heps0 : 0 ≤ eps)
    (heps1 : eps ≤ 1 / 8) :
    letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
    letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
    Integrable (llr (obsLaw (witnessLaw eps)) (obsLaw (witnessLaw 0)))
      (obsLaw (witnessLaw eps)) := by
  letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
  letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  letI := witnessVisibleLaw_isProbabilityMeasure eps heps0 heps1
  letI := witnessVisibleLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  let f := fun v : PathVisibleCell => pathObsPoint v.1 v.2.1 v.2.2.1 v.2.2.2
  rw [← witnessVisibleLaw_map eps heps0 heps1,
    ← witnessVisibleLaw_map 0 (by norm_num) (by norm_num)]
  exact InformationTheory.integrable_llr_map
    (witnessVisibleLaw_absolutelyContinuous eps) (measurable_of_finite f)
    Integrable.of_finite

/-- The finite visible collision-witness chi-square divergence is quadratic. -/
-- @node: witnessVisibleLaw_chiSqDiv_bound
lemma witnessVisibleLaw_chiSqDiv_bound (eps : ℝ) (heps0 : 0 ≤ eps)
    (heps1 : eps ≤ 1 / 8) :
    Causalean.Stat.chiSqDiv (witnessVisibleLaw eps) (witnessVisibleLaw 0) ≤
      16000 * eps ^ 2 := by
  letI := witnessVisibleLaw_isProbabilityMeasure eps heps0 heps1
  letI := witnessVisibleLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  have hac := witnessVisibleLaw_absolutelyContinuous eps
  have hformula := Causalean.Stat.finite_one_add_chiSqDiv
    (witnessVisibleLaw eps) (witnessVisibleLaw 0) hac
  have hmass (mu : Measure PathVisibleCell) [IsProbabilityMeasure mu] :
      ∑ v, mu.real {v} = 1 := by
    simpa using (MeasureTheory.sum_measureReal_singleton (μ := mu) Finset.univ)
  have hidentity : Causalean.Stat.chiSqDiv (witnessVisibleLaw eps) (witnessVisibleLaw 0) =
      ∑ v : PathVisibleCell,
        ((witnessVisibleLaw eps).real {v} - (witnessVisibleLaw 0).real {v}) ^ 2 /
          (witnessVisibleLaw 0).real {v} := by
    have hp := hmass (witnessVisibleLaw eps)
    have hq := hmass (witnessVisibleLaw 0)
    calc
      _ = (∑ v : PathVisibleCell,
          (witnessVisibleLaw eps).real {v} ^ 2 / (witnessVisibleLaw 0).real {v}) - 1 := by
            linarith [hformula]
      _ = (∑ v : PathVisibleCell,
          (witnessVisibleLaw eps).real {v} ^ 2 / (witnessVisibleLaw 0).real {v}) -
            2 * (∑ v : PathVisibleCell, (witnessVisibleLaw eps).real {v}) +
              ∑ v : PathVisibleCell, (witnessVisibleLaw 0).real {v} := by
            rw [hp, hq]
            ring
      _ = ∑ v : PathVisibleCell,
          ((witnessVisibleLaw eps).real {v} - (witnessVisibleLaw 0).real {v}) ^ 2 /
            (witnessVisibleLaw 0).real {v} := by
            symm
            calc
              _ = ∑ v : PathVisibleCell,
                  (((witnessVisibleLaw eps).real {v} ^ 2 /
                    (witnessVisibleLaw 0).real {v} -
                    2 * (witnessVisibleLaw eps).real {v}) +
                    (witnessVisibleLaw 0).real {v}) := by
                  apply Finset.sum_congr rfl
                  intro v _
                  have hqpos : 0 < (witnessVisibleLaw 0).real {v} :=
                    lt_of_lt_of_le (by norm_num) (witnessVisibleLaw_base_floor v)
                  field_simp
                  ring
              _ = _ := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hidentity]
  calc
    _ ≤ ∑ _v : PathVisibleCell, 1000 * eps ^ 2 := by
      apply Finset.sum_le_sum
      intro v _
      have hqfloor := witnessVisibleLaw_base_floor v
      have hdiff := witnessVisibleLaw_singleton_diff_bound eps heps0 heps1 v
      have hqpos : 0 < (witnessVisibleLaw 0).real {v} :=
        lt_of_lt_of_le (by norm_num) hqfloor
      rw [div_le_iff₀ hqpos]
      have hsq := sq_le_sq₀ (abs_nonneg _) heps0 |>.2 hdiff
      rw [sq_abs] at hsq
      calc
        _ ≤ eps ^ 2 := hsq
        _ ≤ 1000 * eps ^ 2 * (witnessVisibleLaw 0).real {v} := by
          have hs : 1 ≤ 1000 * (witnessVisibleLaw 0).real {v} := by nlinarith
          have := mul_le_mul_of_nonneg_left hs (sq_nonneg eps)
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
    _ = 16000 * eps ^ 2 := by
      norm_num [Fintype.card_prod]
      ring

/-- The observed one-record KL divergence of the collision witness is quadratic. -/
-- @node: witnessLaw_observed_kl_bound
lemma witnessLaw_observed_kl_bound (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1 / 8) :
    letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
    letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
    InformationTheory.klDiv (obsLaw (witnessLaw eps)) (obsLaw (witnessLaw 0)) ≤
      ENNReal.ofReal (16000 * eps ^ 2) := by
  letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
  letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  letI := witnessVisibleLaw_isProbabilityMeasure eps heps0 heps1
  letI := witnessVisibleLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  rw [← witnessVisibleLaw_map eps heps0 heps1,
    ← witnessVisibleLaw_map 0 (by norm_num) (by norm_num)]
  calc
    _ ≤ InformationTheory.klDiv (witnessVisibleLaw eps) (witnessVisibleLaw 0) :=
      InformationTheory.klDiv_map_le _ _ (measurable_of_finite _)
    _ ≤ ENNReal.ofReal (Causalean.Stat.chiSqDiv
        (witnessVisibleLaw eps) (witnessVisibleLaw 0)) :=
      klDiv_le_chiSqDiv _ _ (witnessVisibleLaw_absolutelyContinuous eps)
    _ ≤ ENNReal.ofReal (16000 * eps ^ 2) :=
      ENNReal.ofReal_le_ofReal (witnessVisibleLaw_chiSqDiv_bound eps heps0 heps1)

/-- A collision witness whose quadratic KL is within the local radius belongs to the
quotient local experiment. -/
-- @node: witness_localQuotientExperiment
lemma witness_localQuotientExperiment (n : ℕ) (cLoc eps : ℝ)
    (hcLoc : LocalRadiusDomain cLoc) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1 / 8)
    (hKL : 16000 * eps ^ 2 ≤ cLoc / n) :
    letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
    LocalQuotientExperiment (n := n) (L := 2) (pi0 := 1 / 10)
      (sigma0 := 1 / 10) (cLoc := cLoc) (witnessLaw eps) := by
  letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
  refine { toUCVMWModel := witness_ucvmwModel eps heps0 heps1
           cLoc_pos := hcLoc.1
           cLoc_lt_one := hcLoc.2
           neighborhood := ?_ }
  unfold LocalQuotientNeighborhood
  exact (witnessLaw_observed_kl_bound eps heps0 heps1).trans
    (ENNReal.ofReal_le_ofReal hKL)

/-- The collision witness quotient laws are separated by exactly the collision amplitude. -/
-- @node: witness_quotientLaw_wass1
lemma witness_quotientLaw_wass1 (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1 / 8) :
    letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
    letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
    AtomicLaw.LawModulo.wass1
      (quotientLaw (witnessLaw 0) (witness_ucvmwModel 0 (by norm_num) (by norm_num)))
      (quotientLaw (witnessLaw eps) (witness_ucvmwModel eps heps0 heps1)) = eps := by
  letI := witnessLaw_isProbabilityMeasure eps heps0 heps1
  letI := witnessLaw_isProbabilityMeasure 0 (by norm_num) (by norm_num)
  rw [quotientLaw, quotientLaw, AtomicLaw.LawModulo.wass1_ofProbabilityLaw]
  obtain ⟨gamma, hgamma⟩ := AtomicLaw.wass1_optimal_plan
    (quotientLawRaw_valid (witnessLaw 0) (witness_ucvmwModel 0 (by norm_num) (by norm_num)))
    (quotientLawRaw_valid (witnessLaw eps) (witness_ucvmwModel eps heps0 heps1))
  rw [← hgamma]
  unfold AtomicLaw.transportCost
  change (∑ i, ∑ j, gamma.mass i j *
    |latentEffect (witnessLaw 0) i - latentEffect (witnessLaw eps) j|) = eps
  have hcost : ∀ i j : Fin 2,
      |latentEffect (witnessLaw 0) i - latentEffect (witnessLaw eps) j| = eps := by
    intro i j
    rw [witness_latentEffect 0 (by norm_num) (by norm_num),
      witness_latentEffect eps heps0 heps1]
    fin_cases i <;> fin_cases j <;> norm_num [abs_of_nonneg heps0]
  simp_rw [hcost, ← Finset.sum_mul]
  change (∑ i, ∑ j, gamma.mass i j) * eps = eps
  have hsum : ∑ i, ∑ j, gamma.mass i j = 1 := by
    simp_rw [gamma.fst_marginal]
    exact (quotientLawRaw_valid (witnessLaw 0)
      (witness_ucvmwModel 0 (by norm_num) (by norm_num))).2.1
  rw [hsum, one_mul]

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
