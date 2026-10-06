module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.RawBayes
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Transfer

/-!
The tagged affine parameter's original fixed experiment, exact ordered prefix
retention with its independent seed, and the conditional and predictive failure
budgets. These are the experiment leaves for the final minimax transfer.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

variable (n m d : Nat) (eps : Real) (hd : 2 ≤ d)
  (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)

/-- The complete mark kernel retains the hypothesis and its latent vector. -/
-- @node: affineTaggedCompleteKernel
noncomputable def affineTaggedCompleteKernel : Kernel (AffineRawParameter n m d eps) (Obs d) :=
  Kernel.ofFunOfCountable fun theta =>
    (normalizedLaw theta.1 n m d eps hd sigma theta.2).pmf.toMeasure

/-- The auxiliary mark kernel is the full normalized arm marginal. -/
-- @node: affineTaggedAuxiliaryKernel
noncomputable def affineTaggedAuxiliaryKernel : Kernel (AffineRawParameter n m d eps) (AuxObs d) :=
  Kernel.ofFunOfCountable fun theta =>
    (auxMarginal (normalizedLaw theta.1 n m d eps hd sigma theta.2)).toMeasure

/-- Every complete mark law is a probability measure. -/
-- @node: affineTaggedCompleteKernel_isProbabilityMeasure
instance affineTaggedCompleteKernel_isProbabilityMeasure (theta : AffineRawParameter n m d eps) :
    IsProbabilityMeasure (affineTaggedCompleteKernel n m d eps hd sigma theta) := by
  change IsProbabilityMeasure (normalizedLaw theta.1 n m d eps hd sigma theta.2).pmf.toMeasure
  infer_instance

/-- Every auxiliary mark law is a probability measure. -/
-- @node: affineTaggedAuxiliaryKernel_isProbabilityMeasure
instance affineTaggedAuxiliaryKernel_isProbabilityMeasure (theta : AffineRawParameter n m d eps) :
    IsProbabilityMeasure (affineTaggedAuxiliaryKernel n m d eps hd sigma theta) := by
  change IsProbabilityMeasure (auxMarginal (normalizedLaw theta.1 n m d eps hd sigma theta.2)).toMeasure
  infer_instance

/-- The unseeded tagged raw experiment has the actual ordered conditional laws. -/
-- @node: affineTaggedOrderedKernel
noncomputable def affineTaggedOrderedKernel :
    Kernel (AffineRawParameter n m d eps) (RawTwoPool (Obs d) (AuxObs d)) :=
  Kernel.ofFunOfCountable fun theta =>
    affineOrderedRawKernel n m d eps hd sigma theta.1 theta.2

/-- The ordered tagged raw laws are probability measures. -/
-- @node: affineTaggedOrderedKernel_isMarkovKernel
instance affineTaggedOrderedKernel_isMarkovKernel :
    IsMarkovKernel (affineTaggedOrderedKernel n m d eps hd sigma) where
  isProbabilityMeasure theta := by
    change IsProbabilityMeasure (affineOrderedRawKernel n m d eps hd sigma theta.1 theta.2)
    infer_instance

/-- The fixed experiment keeps both full original ordered arrays. -/
-- @node: affineTaggedFixedKernel
noncomputable def affineTaggedFixedKernel :
    Kernel (AffineRawParameter n m d eps) (Sample n m d) :=
  Kernel.ofFunOfCountable fun theta =>
    annotationLaw (normalizedLaw theta.1 n m d eps hd sigma theta.2) n m

/-- [The fixed tagged experiment satisfies the exact unequal two-pool interface. ](goal)-/
-- @node: affineTaggedFixedKernel_isFixedTwoPool
lemma affineTaggedFixedKernel_isFixedTwoPool :
    IsFixedTwoPoolExperiment n m (affineTaggedFixedKernel n m d eps hd sigma)
      (affineTaggedCompleteKernel n m d eps hd sigma)
      (affineTaggedAuxiliaryKernel n m d eps hd sigma) := by
  intro theta
  rfl

/-- [Retaining the hypothesis tag changes neither scaled intensity nor mark law. ](goal)-/
-- @node: affineTaggedOrderedKernel_isRandomScale
lemma affineTaggedOrderedKernel_isRandomScale :
    IsRandomScaleTwoPoolExperiment (affineTaggedOrderedKernel n m d eps hd sigma)
      (affineTaggedCompleteKernel n m d eps hd sigma)
      (affineTaggedAuxiliaryKernel n m d eps hd sigma)
      (fun theta => Real.toNNReal (rawNormalizer n m d eps sigma theta.2))
      (Real.toNNReal (affineTuning n m d eps).u)
      (Real.toNNReal (affineTuning n m d eps).w) := by
  intro theta
  exact affineOrderedRawKernel_isRandomScale n m d eps hd sigma theta.1 theta.2

/-- [Under the stated inputs and conditions](hyp:fallbackX,fallbackY,theta), Exact retention on joint success gives the original fixed data law times
its success probability, for every parameter rather than merely on average.  This gives [the stated result](goal).-/
-- @node: affineTaggedOrderedKernel_retention_success
lemma affineTaggedOrderedKernel_retention_success
    (fallbackX : Fin n → Obs d) (fallbackY : Fin m → AuxObs d)
    (theta : AffineRawParameter n m d eps) :
    ((affineTaggedOrderedKernel n m d eps hd sigma theta).restrict
      (retentionSuccessSet n m)).map (twoPoolOrderedRetention fallbackX fallbackY) =
    (poissonMeasure (Real.toNNReal ((affineTuning n m d eps).u *
        rawNormalizer n m d eps sigma theta.2)) (Set.Ici n) *
      poissonMeasure (Real.toNNReal ((affineTuning n m d eps).w *
        rawNormalizer n m d eps sigma theta.2)) (Set.Ici m)) •
      affineTaggedFixedKernel n m d eps hd sigma theta := by
  exact map_twoPoolOrderedRetention_restrict_success
    (normalizedLaw theta.1 n m d eps hd sigma theta.2).pmf.toMeasure
    (auxMarginal (normalizedLaw theta.1 n m d eps hd sigma theta.2)).toMeasure
    _ _ n m fallbackX fallbackY

/-- [Under the stated inputs and conditions](hyp:fallbackX,fallbackY,theta), The same exact retention identity keeps the independent uniform seed.  This gives [the stated result](goal).-/
-- @node: affineRawTaggedKernel_retention_success
lemma affineRawTaggedKernel_retention_success
    (fallbackX : Fin n → Obs d) (fallbackY : Fin m → AuxObs d)
    (theta : AffineRawParameter n m d eps) :
    ((affineRawTaggedKernel n m d eps hd sigma theta).restrict
      ((retentionSuccessSet (X := Obs d) (Y := AuxObs d) n m) ×ˢ Set.univ)).map
        (Prod.map (twoPoolOrderedRetention fallbackX fallbackY) id) =
    (poissonMeasure (Real.toNNReal ((affineTuning n m d eps).u *
        rawNormalizer n m d eps sigma theta.2)) (Set.Ici n) *
      poissonMeasure (Real.toNNReal ((affineTuning n m d eps).w *
        rawNormalizer n m d eps sigma theta.2)) (Set.Ici m)) •
      ((affineTaggedFixedKernel n m d eps hd sigma theta).prod seedLaw) := by
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  change (((affineTaggedOrderedKernel n m d eps hd sigma theta).prod seedLaw).restrict
    (_ ×ˢ Set.univ)).map _ = _
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    ← Measure.map_prod_map _ _ (measurable_twoPoolOrderedRetention fallbackX fallbackY)
      measurable_id, Measure.map_id,
    affineTaggedOrderedKernel_retention_success, Measure.prod_smul_left]

/-- [Under the stated hypotheses](hyp:hn,heps,heps',hS,hx), Conditional count failure fits the half-gap budget for every raw table.  This gives [the stated result](goal). -/
-- @node: affineTaggedOrderedKernel_failure_gap
lemma affineTaggedOrderedKernel_failure_gap
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (theta : AffineRawParameter n m d eps) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    affineTaggedOrderedKernel n m d eps hd sigma theta (retentionFailureSet n m) ≤
      ENNReal.ofReal (gap ^ 2 / 128) := by
  intro nu gap
  have htail := conditional_retentionFailure_le_poissonLowerTails
    (affineTaggedOrderedKernel n m d eps hd sigma)
    (affineTaggedCompleteKernel n m d eps hd sigma)
    (affineTaggedAuxiliaryKernel n m d eps hd sigma)
    (fun theta => Real.toNNReal (rawNormalizer n m d eps sigma theta.2))
    (Real.toNNReal (affineTuning n m d eps).u)
    (Real.toNNReal (affineTuning n m d eps).w)
    (affineTaggedOrderedKernel_isRandomScale n m d eps hd sigma) n m theta
  rw [← Real.toNNReal_mul (by change 0 ≤ 128 * (n : Real); positivity),
    ← Real.toNNReal_mul (by change 0 ≤ 128 * ((n : Real) + m); positivity)] at htail
  exact htail.trans (affine_prefix_failure_sum_gap n m d eps hn hd heps heps' hS hx sigma theta.2)

/-- [Under the stated hypotheses](hyp:hn,heps,heps',hS,hx,hyp), Integrating the uniform tablewise budget gives the same predictive budget
under either tagged prior; no low-scale exception is needed.  This gives [the stated result](goal). -/
-- @node: affineTaggedOrderedKernel_predictive_failure_gap
lemma affineTaggedOrderedKernel_predictive_failure_gap
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) (hyp : Bool) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    priorPredictive (affineRawTaggedPrior n m d eps sigma hyp)
      (affineTaggedOrderedKernel n m d eps hd sigma) (retentionFailureSet n m) ≤
      ENNReal.ofReal (gap ^ 2 / 128) := by
  intro nu gap
  rw [priorPredictive_apply _ _ (measurableSet_retentionFailureSet n m)]
  calc
    _ ≤ ∫⁻ _theta, ENNReal.ofReal (gap ^ 2 / 128)
        ∂affineRawTaggedPrior n m d eps sigma hyp := lintegral_mono fun theta =>
      affineTaggedOrderedKernel_failure_gap n m d eps hd sigma hn heps heps' hS hx theta
    _ = _ := by simp

/-- [Under the stated hypotheses](hyp:hn,heps,heps',hS,hx), The independent seed has unit mass, so it adds no count failure.  This gives [the stated result](goal). -/
-- @node: affineRawTaggedKernel_failure_gap
lemma affineRawTaggedKernel_failure_gap
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (theta : AffineRawParameter n m d eps) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    affineRawTaggedKernel n m d eps hd sigma theta
      ((retentionFailureSet (X := Obs d) (Y := AuxObs d) n m) ×ˢ Set.univ) ≤
      ENNReal.ofReal (gap ^ 2 / 128) := by
  intro nu gap
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  change ((affineTaggedOrderedKernel n m d eps hd sigma theta).prod seedLaw) _ ≤ _
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact affineTaggedOrderedKernel_failure_gap n m d eps hd sigma hn heps heps' hS hx theta

/-- A randomized original rule uses the first requested records when both
prefixes exist, and returns zero on failure, keeping the same seed. -/
-- @node: affineTransferredRule
noncomputable def affineTransferredRule (T : Sample n m d × Real → Real)
    (fallbackX : Fin n → Obs d) (fallbackY : Fin m → AuxObs d) :
    RawTwoPool (Obs d) (AuxObs d) × Real → Real := fun z =>
  if z.1 ∈ retentionSuccessSet n m then
    T (twoPoolOrderedRetention fallbackX fallbackY z.1, z.2)
  else 0

/-- [Under the stated inputs and conditions](hyp:T,hT,fallbackX,fallbackY), Prefix transfer preserves joint Borel measurability with the seed.  This gives [the stated result](goal).-/
-- @node: affineTransferredRule_measurable
lemma affineTransferredRule_measurable (T : Sample n m d × Real → Real)
    (hT : Measurable T) (fallbackX : Fin n → Obs d) (fallbackY : Fin m → AuxObs d) :
    Measurable (affineTransferredRule n m d T fallbackX fallbackY) := by
  unfold affineTransferredRule
  apply Measurable.ite ((measurableSet_retentionSuccessSet n m).preimage measurable_fst)
  · exact hT.comp (((measurable_twoPoolOrderedRetention fallbackX fallbackY).comp
      measurable_fst).prodMk measurable_snd)
  · exact measurable_const

/-- [Under the stated inputs and conditions](hyp:T,fallbackX,fallbackY,z), Prefix transfer preserves the clipping constraint, including on failure.  This gives [the stated result](goal).-/
-- @node: affineTransferredRule_mem_Icc
lemma affineTransferredRule_mem_Icc (T : Rule n m d)
    (fallbackX : Fin n → Obs d) (fallbackY : Fin m → AuxObs d)
    (z : RawTwoPool (Obs d) (AuxObs d) × Real) :
    affineTransferredRule n m d T.1 fallbackX fallbackY z ∈ Set.Icc (-1) 1 := by
  unfold affineTransferredRule
  split
  · exact T.2.2 _
  · constructor <;> norm_num

/-- [Under the stated hypotheses](hyp:hn,heps,heps',hS,hx), For each actual normalized table, successful ordered retention pays exactly
its fixed-experiment risk; zero fallback costs at most the count-failure mass.  This gives [the stated result](goal). -/
-- @node: affineTransferredRule_conditional_risk_le
lemma affineTransferredRule_conditional_risk_le
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (T : Rule n m d) (fallbackX : Fin n → Obs d) (fallbackY : Fin m → AuxObs d)
    (theta : AffineRawParameter n m d eps) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let gap := (∫ lat, affineRawTarget n m d eps sigma true lat ∂nu) -
      (∫ lat, affineRawTarget n m d eps sigma false lat ∂nu)
    let target := ateFunctional (normalizedLaw theta.1 n m d eps hd sigma theta.2)
    (∫⁻ z, ENNReal.ofReal ((affineTransferredRule n m d T.1 fallbackX fallbackY z - target) ^ 2)
      ∂affineRawTaggedKernel n m d eps hd sigma theta) ≤
    (∫⁻ z, ENNReal.ofReal ((T.1 z - target) ^ 2)
      ∂((affineTaggedFixedKernel n m d eps hd sigma theta).prod seedLaw)) +
      ENNReal.ofReal (gap ^ 2 / 128) := by
  intro nu gap target
  let E : Set (RawTwoPool (Obs d) (AuxObs d) × Real) :=
    retentionSuccessSet n m ×ˢ Set.univ
  have hE : MeasurableSet E := (measurableSet_retentionSuccessSet n m).prod MeasurableSet.univ
  let mu := affineRawTaggedKernel n m d eps hd sigma theta
  have hsuccess : (∫⁻ z in E,
      ENNReal.ofReal ((affineTransferredRule n m d T.1 fallbackX fallbackY z - target) ^ 2) ∂mu) ≤
      ∫⁻ z, ENNReal.ofReal ((T.1 z - target) ^ 2)
        ∂((affineTaggedFixedKernel n m d eps hd sigma theta).prod seedLaw) := by
    have heq : (∫⁻ z in E,
        ENNReal.ofReal ((affineTransferredRule n m d T.1 fallbackX fallbackY z - target) ^ 2) ∂mu) =
        ∫⁻ z in E, ENNReal.ofReal ((T.1
          (Prod.map (twoPoolOrderedRetention fallbackX fallbackY) id z) - target) ^ 2) ∂mu := by
      apply setLIntegral_congr_fun hE
      intro z hz
      simp only [affineTransferredRule, if_pos hz.1]
      rfl
    have hT := T.2.1
    rw [heq, ← lintegral_map (f := fun z : Sample n m d × Real =>
      ENNReal.ofReal ((T.1 z - target) ^ 2)) (by fun_prop)
      ((measurable_twoPoolOrderedRetention fallbackX fallbackY).prodMap measurable_id)]
    change (∫⁻ z, ENNReal.ofReal ((T.1 z - target) ^ 2)
      ∂((affineRawTaggedKernel n m d eps hd sigma theta).restrict
        (retentionSuccessSet n m ×ˢ Set.univ)).map _) ≤ _
    rw [affineRawTaggedKernel_retention_success, lintegral_smul_measure, smul_eq_mul]
    apply mul_le_of_le_one_left (by positivity)
    exact (mul_le_mul prob_le_one prob_le_one (by positivity) (by positivity)).trans_eq (by simp)
  have hfailure : (∫⁻ z in Eᶜ,
      ENNReal.ofReal ((affineTransferredRule n m d T.1 fallbackX fallbackY z - target) ^ 2) ∂mu) ≤
      ENNReal.ofReal (gap ^ 2 / 128) := by
    have hb := affine_normalized_target_bounds n m d eps hn hd heps heps' sigma theta.1 theta.2
    have htarget : target ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
    have heq : Eᶜ = retentionFailureSet (X := Obs d) (Y := AuxObs d) n m ×ˢ Set.univ := by
      ext z
      simp only [E, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, and_true,
        retentionSuccessSet, retentionFailureSet, Set.mem_setOf_eq, Set.mem_union]
      omega
    calc
      _ ≤ ∫⁻ _z in Eᶜ, (1 : ENNReal) ∂mu := by
        apply setLIntegral_mono measurable_const
        intro z hz
        have hz' : z.1 ∉ retentionSuccessSet (X := Obs d) (Y := AuxObs d) n m := by
          simpa [E] using hz
        simp only [affineTransferredRule, if_neg hz', zero_sub, neg_sq]
        exact (ENNReal.ofReal_le_ofReal htarget).trans_eq ENNReal.ofReal_one
      _ = mu Eᶜ := by simp
      _ ≤ _ := by
        rw [heq]
        exact affineRawTaggedKernel_failure_gap n m d eps hd sigma hn heps heps' hS hx theta
  rw [← lintegral_add_compl _ hE]
  exact add_le_add hsuccess hfailure

end CausalSmith.Stat.AnnotationRarearmFrontier
