import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessFactorization
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.WitnessSpectral

/-! Finite-sum, envelope, matrix, and law calculations for the explicit collision witness. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

-- @node: measurableSet_obsArm
lemma measurableSet_obsArm (t : Bool) : MeasurableSet (obsArm (dx := 2) (dz := 2) t) := by
  have hcoord : Measurable (@Obs.toCoordinates 2 2) := continuous_induced_dom.measurable
  have hT : Measurable (fun o : Obs 2 2 => o.T) := by
    change Measurable (fun o => (Obs.toCoordinates o).1)
    exact hcoord.fst
  exact hT (measurableSet_singleton t)

-- @node: measurable_obs_Z_mul_X
lemma measurable_obs_Z_mul_X (i j : Fin 2) :
    Measurable (fun o : Obs 2 2 => o.Z i * o.X j) := by
  have hcoord : Measurable (@Obs.toCoordinates 2 2) := continuous_induced_dom.measurable
  have hX : Measurable (fun o : Obs 2 2 => o.X) := by
    change Measurable (fun o => (Obs.toCoordinates o).2.1)
    exact hcoord.snd.fst
  have hZ : Measurable (fun o : Obs 2 2 => o.Z) := by
    change Measurable (fun o => (Obs.toCoordinates o).2.2.1)
    exact hcoord.snd.snd.fst
  exact ((measurable_pi_apply i).comp hZ).mul ((measurable_pi_apply j).comp hX)

-- @node: obs_witness_arm_mass
lemma obs_witness_arm_mass (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8)
    (t : Bool) :
    letI := witnessLaw_isProbabilityMeasure eps hlo hhi
    (obsLaw (witnessLaw eps)).real (obsArm t) = if t then 13 / 25 else 12 / 25 := by
  classical
  letI := witnessLaw_isProbabilityMeasure eps hlo hhi
  have hfull : MeasurableSet {w : FullData 2 2 2 | w.T = t} :=
    (obsMap_measurable 2 2 2) (measurableSet_obsArm t)
  change ((witnessLaw eps).map obsMap).real (obsArm t) = _
  rw [Measure.real, Measure.map_apply (obsMap_measurable 2 2 2) (measurableSet_obsArm t)]
  change (witnessLaw eps).real {w | w.T = t} = _
  rw [witnessLaw_real eps _ hfull]
  simp_rw [ENNReal.toReal_ofReal (witnessWeight_nonneg eps hlo hhi _ _ _ _ _ _)]
  simp only [witnessPoint, Set.mem_setOf_eq]
  have hselect (u : Fin 2) :
      (∑ s : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u s x z y0 y1 * if s = t then 1 else 0) =
      ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1 := by
    cases t <;>
      rw [show (Finset.univ : Finset Bool) = {false, true} by decide] <;> simp
  simp_rw [hselect, witnessWeight_sum_nuisance]
  fin_cases t <;> simp [bernoulliMass] <;> norm_num

-- @node: witness_latentMass
lemma witness_latentMass (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8)
    (u : Fin 2) :
    latentMass (witnessLaw eps) u = if u.val = 0 then 2 / 5 else 3 / 5 := by
  classical
  rw [latentMass, witnessLaw_real eps _ (measurableSet_witness_latentClass u)]
  simp_rw [ENNReal.toReal_ofReal (witnessWeight_nonneg eps hlo hhi _ _ _ _ _ _)]
  rw [witness_sum_restrict_latentClass eps u (fun _ => (1 : ℝ))]
  simp only [mul_one]
  simp_rw [witnessWeight_sum_nuisance]
  fin_cases u <;> simp [bernoulliMass] <;> norm_num

-- @node: witness_latentCell_mass
lemma witness_latentCell_mass (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8)
    (u : Fin 2) (t : Bool) :
    (witnessLaw eps).real (latentCell u t) =
      (if u.val = 0 then 2 / 5 else 3 / 5) *
        bernoulliMass (if u.val = 0 then 2 / 5 else 3 / 5) t := by
  classical
  rw [witnessLaw_real eps _ (measurableSet_witness_latentCell u t)]
  simp_rw [ENNReal.toReal_ofReal (witnessWeight_nonneg eps hlo hhi _ _ _ _ _ _)]
  rw [witness_sum_restrict_latentCell eps u t (fun _ => (1 : ℝ))]
  simp only [mul_one]
  exact witnessWeight_sum_nuisance eps u t

-- @node: witness_targetFeature
lemma witness_targetFeature (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8) :
    targetFeature (witnessLaw eps) = fun i u : Fin 2 =>
      if i.val = 0 then 1 else if u.val = 0 then 1 / 5 else 4 / 5 := by
  ext i u
  rw [targetFeature, conditionalMean_witness_latentClass eps hlo hhi]
  fin_cases i <;> fin_cases u <;>
    simp (config := { maxSteps := 1000000 })
      [witnessWeight, witnessPoint, vec2, boolReal, bernoulliMass] <;> ring

-- @node: witness_referenceFeature
lemma witness_referenceFeature (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8)
    (t : Bool) :
    referenceFeature (witnessLaw eps) t = fun i u : Fin 2 =>
      if i.val = 0 then 1 else if t then
        (if u.val = 0 then 7 / 20 else 3 / 4)
      else (if u.val = 0 then 3 / 10 else 7 / 10) := by
  ext i u
  rw [referenceFeature, conditionalMean_witness_latentCell eps hlo hhi]
  fin_cases i <;> fin_cases u <;> cases t <;>
    simp (config := { maxSteps := 1000000 })
      [witnessWeight, witnessPoint, vec2, boolReal, bernoulliMass] <;> ring

-- @node: witness_latentEffect
lemma witness_latentEffect (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8)
    (u : Fin 2) :
    latentEffect (witnessLaw eps) u =
      if u.val = 0 then 1 / 4 - eps else 1 / 4 + eps := by
  unfold latentEffect latentMean
  rw [conditionalMean_witness_latentClass eps hlo hhi,
    conditionalMean_witness_latentClass eps hlo hhi]
  fin_cases u <;>
    simp (config := { maxSteps := 1000000 })
      [witnessWeight, witnessPoint, potential, boolReal, bernoulliMass] <;> ring

-- @node: conditionalMean_obsLaw_witness
lemma conditionalMean_obsLaw_witness (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (A : Set (Obs 2 2)) [DecidablePred (· ∈ A)]
    (hA : MeasurableSet A) (f : Obs 2 2 → ℝ) (hf : Measurable f) :
    letI := witnessLaw_isProbabilityMeasure eps hlo hhi
    conditionalMean (obsLaw (witnessLaw eps)) A f =
      (∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1 *
          if obsMap (witnessPoint u t x z y0 y1) ∈ A then 1 else 0)⁻¹ *
      (∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1 *
          if obsMap (witnessPoint u t x z y0 y1) ∈ A then
            f (obsMap (witnessPoint u t x z y0 y1)) else 0) := by
  classical
  letI := witnessLaw_isProbabilityMeasure eps hlo hhi
  have hpre : MeasurableSet (obsMap ⁻¹' A) := (obsMap_measurable 2 2 2) hA
  have hmass : (obsLaw (witnessLaw eps)).real A = (witnessLaw eps).real (obsMap ⁻¹' A) := by
    change ((witnessLaw eps).map obsMap).real A = _
    exact congrArg ENNReal.toReal
      (Measure.map_apply (obsMap_measurable 2 2 2) hA)
  have hint : ∫ o in A, f o ∂obsLaw (witnessLaw eps) =
      ∫ w in obsMap ⁻¹' A, f (obsMap w) ∂witnessLaw eps := by
    change ∫ o, f o ∂((witnessLaw eps).map obsMap).restrict A = _
    rw [Measure.restrict_map (obsMap_measurable 2 2 2) hA]
    exact integral_map (obsMap_measurable 2 2 2).aemeasurable
      hf.aestronglyMeasurable
  rw [conditionalMean, hmass, hint, witnessLaw_real eps _ hpre,
    integral_witnessLaw_restrict eps _ hpre]
  simp_rw [ENNReal.toReal_ofReal (witnessWeight_nonneg eps hlo hhi _ _ _ _ _ _)]
  simp only [Set.mem_preimage]

-- @node: witness_sum_restrict_obsArm
lemma witness_sum_restrict_obsArm (eps : ℝ) (t : Bool)
    (F : Obs 2 2 → ℝ) :
    (∑ u : Fin 2, ∑ s : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      witnessWeight eps u s x z y0 y1 *
        if (obsMap (witnessPoint u s x z y0 y1)).T = t then
          F (obsMap (witnessPoint u s x z y0 y1)) else 0) =
    ∑ u : Fin 2, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      witnessWeight eps u t x z y0 y1 * F (obsMap (witnessPoint u t x z y0 y1)) := by
  apply Finset.sum_congr rfl
  intro u _
  cases t <;> rw [show (Finset.univ : Finset Bool) = {false, true} by decide] <;>
    simp [obsMap, witnessPoint]

-- @node: conditionalMean_obsArm_witness
lemma conditionalMean_obsArm_witness (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (t : Bool) (f : Obs 2 2 → ℝ) (hf : Measurable f) :
    letI := witnessLaw_isProbabilityMeasure eps hlo hhi
    conditionalMean (obsLaw (witnessLaw eps)) (obsArm t) f =
      (∑ u : Fin 2, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1)⁻¹ *
      (∑ u : Fin 2, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1 * f (obsMap (witnessPoint u t x z y0 y1))) := by
  classical
  rw [conditionalMean_obsLaw_witness eps hlo hhi _ (measurableSet_obsArm t) _ hf]
  simp only [obsArm, Set.mem_setOf_eq]
  rw [witness_sum_restrict_obsArm eps t (fun _ => (1 : ℝ)),
    witness_sum_restrict_obsArm eps t f]
  simp only [mul_one]

-- @node: witnessWeight_sum_outcomes_mul
lemma witnessWeight_sum_outcomes_mul (eps : ℝ) (u : Fin 2) (t x z : Bool)
    (c : ℝ) :
    ∑ y0 : Bool, ∑ y1 : Bool, witnessWeight eps u t x z y0 y1 * c =
      ((if u.val = 0 then 2 / 5 else 3 / 5) *
        bernoulliMass (if u.val = 0 then 2 / 5 else 3 / 5) t *
        bernoulliMass (if u.val = 0 then 1 / 5 else 4 / 5) x *
        bernoulliMass (if t then (if u.val = 0 then 7 / 20 else 3 / 4)
          else (if u.val = 0 then 3 / 10 else 7 / 10)) z) * c := by
  let a : ℝ := (if u.val = 0 then 2 / 5 else 3 / 5) *
    bernoulliMass (if u.val = 0 then 2 / 5 else 3 / 5) t *
    bernoulliMass (if u.val = 0 then 1 / 5 else 4 / 5) x *
    bernoulliMass (if t then (if u.val = 0 then 7 / 20 else 3 / 4)
      else (if u.val = 0 then 3 / 10 else 7 / 10)) z
  let p : ℝ := if u.val = 0 then 1 / 2 - eps else 1 / 2 + eps
  have hw (y0 y1 : Bool) : witnessWeight eps u t x z y0 y1 * c =
      (a * c * bernoulliMass (1 / 4) y0) * bernoulliMass p y1 := by
    simp only [witnessWeight, a, p]
    ring
  simp_rw [hw, sum_mul_bernoulliMass]
  rfl

-- @node: witnessWeight_sum_outcomes
lemma witnessWeight_sum_outcomes (eps : ℝ) (u : Fin 2) (t x z : Bool) :
    ∑ y0 : Bool, ∑ y1 : Bool, witnessWeight eps u t x z y0 y1 =
      (if u.val = 0 then 2 / 5 else 3 / 5) *
        bernoulliMass (if u.val = 0 then 2 / 5 else 3 / 5) t *
        bernoulliMass (if u.val = 0 then 1 / 5 else 4 / 5) x *
        bernoulliMass (if t then (if u.val = 0 then 7 / 20 else 3 / 4)
          else (if u.val = 0 then 3 / 10 else 7 / 10)) z := by
  simpa using witnessWeight_sum_outcomes_mul eps u t x z 1

-- @node: conditionalMean_obsArm_ZX
lemma conditionalMean_obsArm_ZX (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (t : Bool) (i j : Fin 2) :
    letI := witnessLaw_isProbabilityMeasure eps hlo hhi
    conditionalMean (obsLaw (witnessLaw eps)) (obsArm t) (fun o => o.Z i * o.X j) =
      (∑ u : Fin 2, ∑ x : Bool, ∑ z : Bool,
        (if u.val = 0 then 2 / 5 else 3 / 5) *
          bernoulliMass (if u.val = 0 then 2 / 5 else 3 / 5) t *
          bernoulliMass (if u.val = 0 then 1 / 5 else 4 / 5) x *
          bernoulliMass (if t then (if u.val = 0 then 7 / 20 else 3 / 4)
            else (if u.val = 0 then 3 / 10 else 7 / 10)) z)⁻¹ *
      (∑ u : Fin 2, ∑ x : Bool, ∑ z : Bool,
        ((if u.val = 0 then 2 / 5 else 3 / 5) *
          bernoulliMass (if u.val = 0 then 2 / 5 else 3 / 5) t *
          bernoulliMass (if u.val = 0 then 1 / 5 else 4 / 5) x *
          bernoulliMass (if t then (if u.val = 0 then 7 / 20 else 3 / 4)
            else (if u.val = 0 then 3 / 10 else 7 / 10)) z) *
          (vec2 1 (boolReal z) i * vec2 1 (boolReal x) j)) := by
  rw [conditionalMean_obsArm_witness eps hlo hhi t _
    (measurable_obs_Z_mul_X i j)]
  apply congrArg₂ (· * ·)
  · apply congrArg Inv.inv
    simp_rw [witnessWeight_sum_outcomes]
  · simp only [obsMap, witnessPoint]
    simp_rw [witnessWeight_sum_outcomes_mul]

set_option maxHeartbeats 1000000 in
-- @node: witness_observedProxyMoment_entry
lemma witness_observedProxyMoment_entry (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (t : Bool) (i j : Fin 2) :
    letI := witnessLaw_isProbabilityMeasure eps hlo hhi
    observedProxyMoment (obsSummary (witnessLaw eps)) t i j =
      if i.val = 0 then (if j.val = 0 then 1 else if t then 8 / 13 else 1 / 2)
      else if j.val = 0 then (if t then 163 / 260 else 1 / 2)
      else if t then 142 / 325 else 31 / 100 := by
  classical
  letI := witnessLaw_isProbabilityMeasure eps hlo hhi
  unfold observedProxyMoment
  cases t <;> simp only [Bool.false_eq_true, eq_self, if_false, if_true]
  all_goals unfold obsSummary
  all_goals fin_cases i <;> fin_cases j <;> norm_num
  all_goals
    rw [conditionalMean_obsArm_ZX eps hlo hhi]
  all_goals
    simp (config := { maxSteps := 1000000 })
      [obsMap, witnessPoint, vec2, boolReal, bernoulliMass] <;> ring

-- @node: witness_observedProxyMoment_det
lemma witness_observedProxyMoment_det (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (t : Bool) :
    letI := witnessLaw_isProbabilityMeasure eps hlo hhi
    det2 (observedProxyMoment (obsSummary (witnessLaw eps)) t) =
      if t then (2 / 5 : ℝ) * (3 / 5) * (36 / 169) else 3 / 50 := by
  letI := witnessLaw_isProbabilityMeasure eps hlo hhi
  unfold det2
  rw [witness_observedProxyMoment_entry eps hlo hhi,
    witness_observedProxyMoment_entry eps hlo hhi,
    witness_observedProxyMoment_entry eps hlo hhi,
    witness_observedProxyMoment_entry eps hlo hhi]
  cases t <;> norm_num

-- @node: ae_witnessLaw_of_points
lemma ae_witnessLaw_of_points (eps : ℝ) (p : FullData 2 2 2 → Prop)
    (h : ∀ (u : Fin 2) (t x z y0 y1 : Bool), p (witnessPoint u t x z y0 y1)) :
    ∀ᵐ w ∂witnessLaw eps, p w := by
  rw [witnessLaw]
  simp only [ae_finsetSum_measure_iff]
  intro u _ t _ x _ z _ y0 _ y1 _
  by_cases hc : ENNReal.ofReal (witnessWeight eps u t x z y0 y1) = 0
  · simp [hc]
  · rw [Measure.ae_ennreal_smul_measure_iff hc, ae_dirac_eq]
    exact h u t x z y0 y1

-- @node: witness_consistency
lemma witness_consistency (eps : ℝ) : CausalConsistency (witnessLaw eps) := by
  unfold CausalConsistency
  apply ae_witnessLaw_of_points
  intro u t x z y0 y1
  cases t <;> simp [witnessPoint, potential]

-- @node: witness_anchor
lemma witness_anchor (eps : ℝ) : AnchorNormalization (witnessLaw eps) := by
  unfold AnchorNormalization
  apply ae_witnessLaw_of_points
  intro u t x z y0 y1 i hi
  simp [witnessPoint, vec2, hi]

-- @node: witness_outerProduct_norm
lemma witness_outerProduct_norm (x z : Bool) :
    ‖matrixCLM (outerProduct (vec2 1 (boolReal z)) (vec2 1 (boolReal x)))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  cases x <;> cases z <;>
    simp [matrixCLM, outerProduct, vec2, boolReal, Matrix.toEuclideanLin_apply,
      Matrix.mulVec, dotProduct, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  all_goals
    have hS : (Real.sqrt (v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2)) ^ 2 =
        v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2 := Real.sq_sqrt (by positivity)
    have hA : (Real.sqrt (v.ofLp 0 ^ 2)) ^ 2 = v.ofLp 0 ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hB : (Real.sqrt ((v.ofLp 0 + v.ofLp 1) ^ 2)) ^ 2 =
        (v.ofLp 0 + v.ofLp 1) ^ 2 := Real.sq_sqrt (by positivity)
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 := Real.sqrt_nonneg (v.ofLp 0 ^ 2 + v.ofLp 1 ^ 2)
    have ha0 := Real.sqrt_nonneg (v.ofLp 0 ^ 2)
    have hb0 := Real.sqrt_nonneg ((v.ofLp 0 + v.ofLp 1) ^ 2)
    have h20 := Real.sqrt_nonneg 2
    nlinarith [sq_nonneg (v.ofLp 0 - v.ofLp 1)]

-- @node: witness_boundedX
lemma witness_boundedX (eps : ℝ) : BoundedTargetProxy (L := 2) (witnessLaw eps) := by
  unfold BoundedTargetProxy
  apply ae_witnessLaw_of_points
  intro u t x z y0 y1
  simp [witnessPoint, vec2, boolReal, Fin.sum_univ_two]
  cases x <;> norm_num [Real.sqrt_le_iff]

-- @node: witness_boundedProxyProduct
lemma witness_boundedProxyProduct (eps : ℝ) :
    BoundedProxyProduct (L := 2) (witnessLaw eps) := by
  unfold BoundedProxyProduct
  apply ae_witnessLaw_of_points
  intro u t x z y0 y1
  simpa [witnessPoint] using witness_outerProduct_norm x z

-- @node: witness_boundedOutcomeProxyProduct
lemma witness_boundedOutcomeProxyProduct (eps : ℝ) :
    BoundedOutcomeProxyProduct (L := 2) (witnessLaw eps) := by
  unfold BoundedOutcomeProxyProduct
  apply ae_witnessLaw_of_points
  intro u t x z y0 y1
  cases t
  · cases y0
    · change ‖matrixCLM (0 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simp [matrixCLM]
    · change ‖matrixCLM (1 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simpa using witness_outerProduct_norm x z
  · cases y1
    · change ‖matrixCLM (0 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simp [matrixCLM]
    · change ‖matrixCLM (1 • outerProduct (vec2 1 (boolReal z))
        (vec2 1 (boolReal x)))‖ ≤ 2
      simpa using witness_outerProduct_norm x z

-- @node: witness_latentArmPositivity
lemma witness_latentArmPositivity (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) : LatentArmPositivity (pi0 := 1 / 10) (witnessLaw eps) := by
  intro u t
  rw [witness_latentCell_mass eps hlo hhi]
  fin_cases u <;> cases t <;> norm_num [bernoulliMass]

-- @node: witness_proxyRankMargin
lemma witness_proxyRankMargin (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) : ProxyRankMargin (sigma0 := 1 / 10) (witnessLaw eps) := by
  constructor
  · rw [witness_referenceFeature eps hlo hhi false]
    exact witnessReferenceMatrix_false_signalMinSingular
  constructor
  · rw [witness_referenceFeature eps hlo hhi true]
    exact witnessReferenceMatrix_true_signalMinSingular
  · rw [witness_targetFeature eps hlo hhi]
    exact witnessTargetMatrix_signalMinSingular

-- @node: witness_det_targetFeature
lemma witness_det_targetFeature (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8) :
    det2 (targetFeature (witnessLaw eps)) = 3 / 5 := by
  rw [witness_targetFeature eps hlo hhi]
  norm_num [det2]

-- @node: witness_det_referenceFeature
lemma witness_det_referenceFeature (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (t : Bool) :
    det2 (referenceFeature (witnessLaw eps) t) = 2 / 5 := by
  rw [witness_referenceFeature eps hlo hhi]
  cases t <;> norm_num [det2]

-- @node: two_by_two_injective_of_signalMinSingular_pos
lemma two_by_two_injective_of_signalMinSingular_pos (A : RectMatrix 2 2)
    (hA : 0 < signalMinSingular A) :
    Function.Injective (Matrix.toEuclideanLin A) := by
  apply (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos _).2
  intro i hi
  have hi_le : i ≤ 1 := by
    simpa using (Nat.le_pred_of_lt hi)
  have hant := (Matrix.toEuclideanLin A).singularValues_antitone hi_le
  apply lt_of_lt_of_le hA
  simpa [signalMinSingular, singularValue] using hant

/-- The collision witness belongs to the uniformly conditioned model throughout its
admissible amplitude interval. -/
lemma witness_ucvmwModel (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8) :
    letI := witnessLaw_isProbabilityMeasure eps hlo hhi
    UCVMWModel (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (witnessLaw eps) := by
  letI := witnessLaw_isProbabilityMeasure eps hlo hhi
  exact
    { referenceProxySeparation := witness_referenceProxySeparation eps hlo hhi
      coreDomain := by norm_num [CoreParameterDomain]
      targetProxySeparation := witness_targetProxySeparation eps hlo hhi
      consistency := witness_consistency eps
      latentIgnorability := witness_armwiseLatentIgnorability eps hlo hhi
      anchor := witness_anchor eps
      boundedX := witness_boundedX eps
      boundedProxyProduct := witness_boundedProxyProduct eps
      boundedOutcomeProxyProduct := witness_boundedOutcomeProxyProduct eps
      latentArmPositivity := witness_latentArmPositivity eps hlo hhi
      proxyRankMargin := witness_proxyRankMargin eps hlo hhi }


end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
