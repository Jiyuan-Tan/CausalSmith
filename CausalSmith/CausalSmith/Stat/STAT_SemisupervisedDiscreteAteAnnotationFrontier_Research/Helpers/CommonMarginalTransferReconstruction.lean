module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalTransferRisk

/-! Raw-count reindexing, ordered Poisson kernels, and predictive reconstruction. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

-- @node: helper:common-marginal-labeled-mark-kernel
/-- [the stated conditions](hyp:d) defines [the specified object](goal). -/
noncomputable def commonMarginalLabeledMarkKernel (d : Nat) :
    Kernel (DiscreteLaw d) (Obs d) where
  toFun P := obsLaw P
  measurable' := measurable_from_top
/-- [the stated conditions](hyp:d,P) defines [the specified object](goal). -/

instance (d : Nat) (P : DiscreteLaw d) :
    IsProbabilityMeasure ((commonMarginalLabeledMarkKernel d) P) := by
  change IsProbabilityMeasure (obsLaw P)
  infer_instance

-- @node: helper:common-marginal-aux-mark-kernel
/-- [the stated conditions](hyp:d) defines [the specified object](goal). -/
noncomputable def commonMarginalAuxMarkKernel (d : Nat) :
    Kernel (DiscreteLaw d) (AuxObs d) where
  toFun P := (auxMarginal P).toMeasure
  measurable' := measurable_from_top
/-- [the stated conditions](hyp:d,P) defines [the specified object](goal). -/

instance (d : Nat) (P : DiscreteLaw d) :
    IsProbabilityMeasure ((commonMarginalAuxMarkKernel d) P) := by
  change IsProbabilityMeasure (auxMarginal P).toMeasure
  infer_instance

-- @node: helper:common-marginal-ordered-raw-kernel
/-- [the stated conditions](hyp:R,u,v) defines [the specified object](goal). -/
noncomputable def commonMarginalOrderedRawKernel {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (u v : NNReal) : Kernel (DiscreteLaw d)
      (Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer.RawTwoPool
        (Obs d) (AuxObs d)) where
  toFun P :=
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      (obsLaw P) (u * Real.toNNReal (R.rawScale P))).prod
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      (auxMarginal P).toMeasure (v * Real.toNNReal (R.rawScale P)))
  measurable' := measurable_from_top

-- @node: helper:common-marginal-ordered-raw-experiment
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma commonMarginal_orderedRaw_isRandomScale {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (u v : NNReal) :
    IsRandomScaleTwoPoolExperiment
      (commonMarginalOrderedRawKernel R u v)
      (commonMarginalLabeledMarkKernel d)
      (commonMarginalAuxMarkKernel d)
      (fun P => Real.toNNReal (R.rawScale P)) u v := by
  intro P
  rfl

-- @node: helper:common-marginal-raw-count-reindex
/-- The nested count-table encoding used by the common-marginal construction
is canonically equivalent to a pair of labeled and auxiliary histograms.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
def commonMarginalRawCountEquiv (d : Nat) :
    RawPoissonCounts d ≃ ((Obs d → Nat) × (AuxObs d → Nat)) where
  toFun z :=
    (⟨fun o => if o.2.2 then (z o.1 o.2.1).1.1 else (z o.1 o.2.1).1.2,
      fun o => (z o.1 o.2).2⟩)
  invFun z := fun x arm => ((z.1 (x, arm, true), z.1 (x, arm, false)), z.2 (x, arm))
  left_inv z := by
    funext x arm
    simp
  right_inv z := by
    rcases z with ⟨zL, zU⟩
    apply Prod.ext
    · funext o
      rcases o with ⟨x, arm, y⟩
      cases y <;> rfl
    · funext o
      rcases o with ⟨x, arm⟩
      rfl

/-- Reindexing the recipe's nested raw count law gives the generic paired
independent-Poisson histogram law consumed by histogram reconstruction.  [the stated conditions](hyp:hu,hv) [the stated conclusion](goal). -/
lemma rawPoissonLaw_map_commonMarginalRawCountEquiv {d : Nat}
    (P : DiscreteLaw d) (scale u v : Real) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Measure.map (commonMarginalRawCountEquiv d) (rawPoissonLaw P scale u v) =
      (independentPoissonCountLaw (obsLaw P) (Real.toNNReal (u * scale))).prod
        (independentPoissonCountLaw (auxMarginal P).toMeasure
          (Real.toNNReal (v * scale))) := by
  apply Measure.ext_of_singleton
  rintro ⟨zL, zU⟩
  rw [Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton (zL, zU))]
  rw [show (commonMarginalRawCountEquiv d :
      RawPoissonCounts d → ((Obs d → Nat) × (AuxObs d → Nat))) ⁻¹'
        ({(zL, zU)} : Set ((Obs d → Nat) × (AuxObs d → Nat))) =
      {((commonMarginalRawCountEquiv d).symm (zL, zU))} by
        ext z
        constructor
        · intro h
          calc
            z = (commonMarginalRawCountEquiv d).symm
                ((commonMarginalRawCountEquiv d) z) := by simp
            _ = (commonMarginalRawCountEquiv d).symm (zL, zU) := by rw [h]
        · intro h
          rw [h]
          simp]
  rw [show ({(zL, zU)} : Set ((Obs d → Nat) × (AuxObs d → Nat))) =
      ({zL} : Set (Obs d → Nat)) ×ˢ ({zU} : Set (AuxObs d → Nat)) by
        ext z
        simp]
  rw [Measure.prod_prod]
  have hobsRate (x : Fin d) (arm y : Bool) :
      Real.toNNReal (u * scale * jointMass P x arm y) =
        Real.toNNReal u * Real.toNNReal scale *
          ((obsLaw P) ({(x, arm, y)} : Set (Obs d))).toNNReal := by
    have hj : 0 ≤ jointMass P x arm y := ENNReal.toReal_nonneg
    have hjNN : Real.toNNReal (jointMass P x arm y) =
        ((obsLaw P) ({(x, arm, y)} : Set (Obs d))).toNNReal := by
      apply NNReal.eq
      simpa [obsLaw, jointMass, Real.coe_toNNReal] using
        (ENNReal.coe_toNNReal_eq_toReal (P.pmf (x, arm, y))).symm
    calc
      Real.toNNReal (u * scale * jointMass P x arm y) =
          Real.toNNReal (u * (jointMass P x arm y * scale)) := by congr 1 <;> ring
      _ = Real.toNNReal u * Real.toNNReal (jointMass P x arm y * scale) :=
        Real.toNNReal_mul hu
      _ = Real.toNNReal u *
          (Real.toNNReal (jointMass P x arm y) * Real.toNNReal scale) := by
        rw [Real.toNNReal_mul hj]
      _ = Real.toNNReal u * Real.toNNReal scale *
          ((obsLaw P) ({(x, arm, y)} : Set (Obs d))).toNNReal := by
        rw [hjNN]
        ac_rfl
  have hauxMass (x : Fin d) (arm : Bool) :
      (auxMarginal P (x, arm)).toReal = armMass P x arm := by
    unfold auxMarginal armMass jointMass
    rw [PMF.map_apply, tsum_fintype]
    cases arm <;> simp only [Fintype.sum_prod_type] <;> simp
    all_goals
      rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  have hauxRate (x : Fin d) (arm : Bool) :
      Real.toNNReal (v * scale * armMass P x arm) =
        Real.toNNReal v * Real.toNNReal scale *
          ((auxMarginal P).toMeasure
            ({(x, arm)} : Set (AuxObs d))).toNNReal := by
    have ha : 0 ≤ armMass P x arm := by
      unfold armMass jointMass
      positivity
    have haNN : Real.toNNReal (armMass P x arm) =
        ((auxMarginal P).toMeasure
          ({(x, arm)} : Set (AuxObs d))).toNNReal := by
      apply NNReal.eq
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      rw [ENNReal.coe_toNNReal_eq_toReal, hauxMass]
      exact Real.coe_toNNReal _ ha
    calc
      Real.toNNReal (v * scale * armMass P x arm) =
          Real.toNNReal (v * (armMass P x arm * scale)) := by congr 1 <;> ring
      _ = Real.toNNReal v * Real.toNNReal (armMass P x arm * scale) :=
        Real.toNNReal_mul hv
      _ = Real.toNNReal v *
          (Real.toNNReal (armMass P x arm) * Real.toNNReal scale) := by
        rw [Real.toNNReal_mul ha]
      _ = Real.toNNReal v * Real.toNNReal scale *
          ((auxMarginal P).toMeasure
            ({(x, arm)} : Set (AuxObs d))).toNNReal := by
        rw [haNN]
        ac_rfl
  have hcontrolMass (x : Fin d) (arm : Bool) :
      armMass P x arm - markedMass P x arm = jointMass P x arm false := by
    unfold armMass markedMass
    simp
  simp [rawPoissonLaw, independentPoissonCountLaw,
    commonMarginalRawCountEquiv, Measure.pi_singleton,
    Real.toNNReal_mul hu, Real.toNNReal_mul hv]
  simp_rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp_rw [hcontrolMass]
  simp_rw [markedMass]
  simp_rw [hobsRate]
  simp_rw [hauxRate]
  simp [Fintype.prod_prod_type]
  simp_rw [Finset.prod_mul_distrib]
  ac_rfl

-- @node: helper:common-marginal-predictive-reconstruction-contraction
/-- Reindexing the nested raw counts and reconstructing the two ordered
Poisson samples is a common Markov channel, so it contracts the distance
between the recipe's two prior-predictive laws.  [the stated conditions](hyp:hu,hv,hRu,hRv) [the stated conclusion](goal). -/
lemma commonMarginal_predictive_reconstruction_contraction {eps : Real}
    {calibration : CommonMarginalCalibration eps}
    {n m d L k : Nat} {B a u v : Real}
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hRu : R.labeledIntensity = u) (hRv : R.auxiliaryIntensity = v) :
    Causalean.Stat.tvDist
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive R.prior0
          (commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v)))
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive R.prior1
          (commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v))) ≤
      Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 := by
  let Kreindex : Kernel (RawPoissonCounts d)
      ((Obs d → Nat) × (AuxObs d → Nat)) :=
    Kernel.deterministic (commonMarginalRawCountEquiv d)
      (measurable_of_countable _)
  let Kreconstruct := pairedHistogramReconstructionKernel (Obs d) (AuxObs d)
  let K := Kreconstruct ∘ₖ Kreindex
  have hkernel : K ∘ₖ R.experimentKernel =
      commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v) := by
    apply Kernel.ext
    intro P
    dsimp only [K]
    rw [Kernel.comp_assoc, Kernel.comp_apply, Kernel.comp_apply]
    change Kreconstruct ∘ₘ
        (Kernel.deterministic (commonMarginalRawCountEquiv d)
          (measurable_of_countable _) ∘ₘ R.experimentKernel P) = _
    rw [Measure.deterministic_comp_eq_map, R.experimentKernel_eq,
      hRu, hRv,
      rawPoissonLaw_map_commonMarginalRawCountEquiv P (R.rawScale P) u v hu hv,
      pairedIndependentPoissonCountLaw_comp_reconstruction]
    simp only [commonMarginalOrderedRawKernel]
    rw [Real.toNNReal_mul hu, Real.toNNReal_mul hv]
    rfl
  have hbranch0 : K ∘ₘ R.rawExperiment0 =
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive R.prior0
        (commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v)) := by
    rw [R.rawExperiment0_eq]
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
    rw [Measure.comp_assoc, hkernel]
  have hbranch1 : K ∘ₘ R.rawExperiment1 =
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive R.prior1
        (commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v)) := by
    rw [R.rawExperiment1_eq]
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
    rw [Measure.comp_assoc, hkernel]
  rw [← hbranch0, ← hbranch1]
  letI : IsProbabilityMeasure R.prior0 := R.probability0
  letI : IsProbabilityMeasure R.prior1 := R.probability1
  have hExperimentProbability (P : DiscreteLaw d) :
      IsProbabilityMeasure (R.experimentKernel P) := by
    rw [R.experimentKernel_eq]
    unfold rawPoissonLaw
    infer_instance
  letI : IsProbabilityMeasure R.rawExperiment0 := by
    rw [R.rawExperiment0_eq]
    exact Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
      R.prior0 R.experimentKernel hExperimentProbability
  letI : IsProbabilityMeasure R.rawExperiment1 := by
    rw [R.rawExperiment1_eq]
    exact Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
      R.prior1 R.experimentKernel hExperimentProbability
  exact Causalean.Stat.tvDist_bind_le R.rawExperiment0 R.rawExperiment1 K

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
