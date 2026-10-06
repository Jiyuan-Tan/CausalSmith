module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CausalDensity
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.WithDensity

/-!
Measurable probability kernels for conditionally independent potential outcomes.
The covariate domain is the unit interval, on which the observed-law densities are normalized.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Joint measurability of a conditional outcome density on the covariate support. -/
-- @node: measurable_conditionalOutcomeDensity
@[fun_prop] lemma measurable_conditionalOutcomeDensity (P : ObsLaw) (a : Bool) :
    Measurable (fun z : Set.Icc (0 : ℝ) 1 × ℝ =>
      ENNReal.ofReal (P.eta a z.1.val z.2)) := by
  have hm : Measurable (fun z : Set.Icc (0 : ℝ) 1 × ℝ => P.eta a z.1.val z.2) :=
    (P.eta_measurable a).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  fun_prop

/-- The conditional potential-outcome law, as a measurable kernel on unit covariates. -/
-- @node: conditionalOutcomeKernel
def conditionalOutcomeKernel (P : ObsLaw) (a : Bool) : Kernel (Set.Icc (0 : ℝ) 1) ℝ :=
  letI : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  (Kernel.const (Set.Icc (0 : ℝ) 1) unitVolume).withDensity
    (fun x y => ENNReal.ofReal (P.eta a x.val y))

/-- Evaluating the outcome kernel gives exactly the prescribed conditional density law. -/
-- @node: conditionalOutcomeKernel_apply
lemma conditionalOutcomeKernel_apply (P : ObsLaw) (a : Bool) (x : Set.Icc (0 : ℝ) 1) :
    conditionalOutcomeKernel P a x =
      unitVolume.withDensity (fun y => ENNReal.ofReal (P.eta a x.val y)) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact Kernel.withDensity_apply _ (measurable_conditionalOutcomeDensity P a) x

/-- Every unit covariate is assigned a probability outcome law. -/
-- @node: conditionalOutcomeKernel_isMarkov
instance conditionalOutcomeKernel_isMarkov (P : ObsLaw) (a : Bool) :
    IsMarkovKernel (conditionalOutcomeKernel P a) where
  isProbabilityMeasure x := by
    rw [conditionalOutcomeKernel_apply]
    exact conditionalOutcome_isProbabilityMeasure P a x.val x.property

/-- Independently draw the two potential outcomes, conditional on the covariate. -/
-- @node: potentialPairKernel
def potentialPairKernel (P : ObsLaw) : Kernel (Set.Icc (0 : ℝ) 1) (ℝ × ℝ) :=
  (conditionalOutcomeKernel P false).prod (conditionalOutcomeKernel P true)

/-- The independent product of conditional probability laws is a probability kernel. -/
-- @node: potentialPairKernel_isMarkov
instance potentialPairKernel_isMarkov (P : ObsLaw) : IsMarkovKernel (potentialPairKernel P) := by
  unfold potentialPairKernel
  infer_instance

/-- The potential-pair law factors into its two conditional laws on rectangles. -/
-- @node: potentialPairKernel_apply_prod
lemma potentialPairKernel_apply_prod (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1)
    (D0 D1 : Set ℝ) :
    potentialPairKernel P x (D0 ×ˢ D1) =
      conditionalOutcomeKernel P false x D0 * conditionalOutcomeKernel P true x D1 := by
  exact Kernel.prod_apply_prod

/-- At each fixed covariate, the two potential coordinates are independent. -/
-- @node: potentialPairKernel_indepFun
lemma potentialPairKernel_indepFun (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd (potentialPairKernel P x) := by
  rw [potentialPairKernel, Kernel.prod_apply]
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- Each conditional outcome kernel is supported on the unit interval. -/
-- @node: conditionalOutcomeKernel_ae_mem
lemma conditionalOutcomeKernel_ae_mem (P : ObsLaw) (a : Bool)
    (x : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ y ∂conditionalOutcomeKernel P a x, y ∈ Set.Icc 0 1 := by
  rw [conditionalOutcomeKernel_apply]
  exact (withDensity_absolutelyContinuous unitVolume _).ae_le
    (ae_restrict_mem measurableSet_Icc)

/-- Both coordinates of the conditional potential-pair law lie in the unit interval. -/
-- @node: potentialPairKernel_ae_mem
lemma potentialPairKernel_ae_mem (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂potentialPairKernel P x, z.1 ∈ Set.Icc 0 1 ∧ z.2 ∈ Set.Icc 0 1 := by
  rw [potentialPairKernel, Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).2
  filter_upwards [conditionalOutcomeKernel_ae_mem P false x] with y0 hy0
  filter_upwards [conditionalOutcomeKernel_ae_mem P true x] with y1 hy1
  exact ⟨hy0, hy1⟩

/-- The first marginal of the potential-pair kernel is the treatment-zero outcome law. -/
-- @node: potentialPairKernel_map_fst
lemma potentialPairKernel_map_fst (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    (potentialPairKernel P x).map Prod.fst = conditionalOutcomeKernel P false x := by
  rw [potentialPairKernel, Kernel.prod_apply, Measure.map_fst_prod]
  simp

/-- The second marginal of the potential-pair kernel is the treatment-one outcome law. -/
-- @node: potentialPairKernel_map_snd
lemma potentialPairKernel_map_snd (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    (potentialPairKernel P x).map Prod.snd = conditionalOutcomeKernel P true x := by
  rw [potentialPairKernel, Kernel.prod_apply, Measure.map_snd_prod]
  simp

end CausalSmith.Stat.DensityEffectRoughNull
