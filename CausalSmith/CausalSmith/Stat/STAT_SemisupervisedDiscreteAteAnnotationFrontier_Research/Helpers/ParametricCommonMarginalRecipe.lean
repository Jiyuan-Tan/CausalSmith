module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPrior
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.KnownMarginalLimit

/-!
# Parametric common-marginal recipe

This file supplies the low-dimensional branch of the common-marginal recipe.
Both laws put all covariate mass on the reservoir cell, use propensity one half,
and differ only in the treated outcome mean.
-/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Stat.Minimax.FiniteSideInformation

noncomputable section
/-- [the stated conditions](hyp:hk,i) defines [the specified object](goal). -/

def parametricRareCell {d k : Nat} (hk : k ≤ d - 1) (i : Fin k) : Fin d :=
  ⟨i.1 + 1, by omega⟩
/-- [the stated conditions](hyp:hk) establishes [the stated conclusion](goal). -/

lemma parametricRareCell_injective {d k : Nat} (hk : k ≤ d - 1) :
    Function.Injective (parametricRareCell hk) := by
  intro i j hij
  apply Fin.ext
  simpa [parametricRareCell] using congrArg Fin.val hij
/-- [the stated conditions](hyp:hr,hk) establishes [the stated conclusion](goal). -/

lemma parametricReservoir_ne_rare {d k : Nat} (r : Fin d) (hr : r.1 = 0)
    (hk : k ≤ d - 1) (i : Fin k) :
    r ≠ parametricRareCell hk i := by
  intro h
  have := congrArg Fin.val h
  simp [parametricRareCell, hr] at this
/-- [the stated conditions](hyp:r) defines [the specified object](goal). -/

noncomputable def reservoirPmf {d : Nat} (r : Fin d) : FinitePmf (Fin d) :=
  ⟨fun x => if x = r then 1 else 0, by
    constructor
    · intro x
      by_cases hx : x = r <;> simp [hx]
    · simp⟩
/-- [the stated conditions](hyp:_heps,heps2,r,hg) defines [the specified object](goal). -/

noncomputable def parametricTheta {d : Nat} {eps g : Real}
    (_heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d) (hg : g ∈ Set.Icc (0 : Real) 1) :
    KnownMarginalParam d eps :=
  (reservoirPmf r,
    fun _ => ⟨1 / 2, le_of_lt heps2, by linarith⟩,
    fun arm _ => if arm then ⟨g, hg⟩ else ⟨0, by norm_num⟩)
/-- [the stated conditions](hyp:heps,heps2,r,hg) defines [the specified object](goal). -/

noncomputable def parametricReservoirLaw {d : Nat} {eps g : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d) (hg : g ∈ Set.Icc (0 : Real) 1) :
    DiscreteLaw d :=
  knownMarginalLaw (parametricTheta heps heps2 r hg) heps.le

private lemma parametricReservoirLaw_cellMass {d : Nat} {eps g : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d) (hg : g ∈ Set.Icc (0 : Real) 1)
    (x : Fin d) :
    cellMass (parametricReservoirLaw heps heps2 r hg) x = if x = r then 1 else 0 := by
  simp [parametricReservoirLaw, knownMarginalLaw_cellMass, parametricTheta, reservoirPmf]

private lemma parametricReservoirLaw_armMass {d : Nat} {eps g : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d) (hg : g ∈ Set.Icc (0 : Real) 1)
    (x : Fin d) (arm : Bool) :
    armMass (parametricReservoirLaw heps heps2 r hg) x arm =
      (if x = r then 1 else 0) * (if arm then 1 / 2 else 1 - 1 / 2) := by
  simp [parametricReservoirLaw, knownMarginalLaw_armMass, parametricTheta, reservoirPmf]

private lemma parametricReservoirLaw_propensity {d : Nat} {eps g : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d) (hg : g ∈ Set.Icc (0 : Real) 1) :
    propensity (parametricReservoirLaw heps heps2 r hg) r = 1 / 2 := by
  rw [propensity, parametricReservoirLaw_armMass, parametricReservoirLaw_cellMass]
  simp

private lemma parametricReservoirLaw_outcomeMean {d : Nat} {eps g : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d) (hg : g ∈ Set.Icc (0 : Real) 1)
    (arm : Bool) (x : Fin d) :
    outcomeMean (parametricReservoirLaw heps heps2 r hg) arm x =
      if x = r then (if arm then g else 0) else 0 := by
  by_cases hx : x = r
  · subst x
    rw [if_pos rfl]
    cases arm
    · simpa [parametricReservoirLaw, parametricTheta, reservoirPmf] using
        knownMarginalLaw_outcomeMean_of_pos (parametricTheta heps heps2 r hg) r false
          (by norm_num [parametricTheta, reservoirPmf]) heps
    · simpa [parametricReservoirLaw, parametricTheta, reservoirPmf] using
        knownMarginalLaw_outcomeMean_of_pos (parametricTheta heps heps2 r hg) r true
          (by norm_num [parametricTheta, reservoirPmf]) heps
  · rw [if_neg hx, outcomeMean, parametricReservoirLaw_armMass]
    have hj : jointMass (parametricReservoirLaw heps heps2 r hg) x arm true = 0 := by
      rw [parametricReservoirLaw, knownMarginalLaw_jointMass]
      simp [knownMarginalAtom, parametricTheta, reservoirPmf, hx]
    simp [hj, hx]

private lemma parametricReservoirLaw_auxTable_eq {d : Nat} {eps g₀ g₁ : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d)
    (hg₀ : g₀ ∈ Set.Icc (0 : Real) 1) (hg₁ : g₁ ∈ Set.Icc (0 : Real) 1) :
    auxTableOf (parametricReservoirLaw heps heps2 r hg₀) =
      auxTableOf (parametricReservoirLaw heps heps2 r hg₁) := by
  funext z
  exact parametricReservoirLaw_armMass heps heps2 r hg₀ z.1 z.2 |>.trans
    (parametricReservoirLaw_armMass heps heps2 r hg₁ z.1 z.2).symm

private lemma parametricReservoirLaw_model {d : Nat} {eps g : Real}
    (hd : 2 ≤ d) (heps : 0 < eps) (heps2 : eps < 1 / 2) (r : Fin d)
    (hg : g ∈ Set.Icc (0 : Real) 1) :
    ModelClass d eps (parametricReservoirLaw heps heps2 r hg) := by
  exact (knownMarginalParamToClass hd heps heps2 (parametricTheta heps heps2 r hg)).2

/-- In the parametric regime, a single occupied reservoir cell gives a common-marginal recipe
whose treated means differ by twice the calibrated root-`n` shift.  [the stated conditions](hyp:calibration,n,m,d,L,B,a,k,hd,hn,heps,heps2,hk,hgap) [the stated conclusion](goal). -/
noncomputable def parametricCommonMarginalRecipe {eps : Real}
    (calibration : CommonMarginalCalibration eps) (n m d L : Nat) (B a : Real) (k : Nat)
    (hd : 2 ≤ d) (hn : 1 ≤ n) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (hk : k ≤ d - 1) (hgap : calibration.dualGap / Real.sqrt n ≤ 1 / 4) :
    CommonMarginalRecipe calibration n m d L B a k := by
  let r : Fin d := ⟨0, by omega⟩
  let delta : Real := calibration.dualGap / Real.sqrt n
  have hnR : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    exact div_nonneg calibration.dualGap_pos.le hsqrt.le
  have hg0 : 1 / 2 - delta ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp [delta] at hgap ⊢ <;> linarith
  have hg1 : 1 / 2 + delta ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp [delta] at hgap ⊢ <;> linarith
  let P0 := parametricReservoirLaw heps heps2 r hg0
  let P1 := parametricReservoirLaw heps heps2 r hg1
  let generator : Measure (Fin k → Real) := Measure.pi (fun _ : Fin k => Measure.dirac 0)
  let sigma : SignedMeasure Real := (Measure.dirac 0).toSignedMeasure
  let nu : Measure Real := Measure.dirac 0
  let dual : Measure Real := Measure.dirac 0
  let lawOf : Bool → (Fin k → Real) → DiscreteLaw d := fun branch _ => if branch then P1 else P0
  let prior0 : Measure (DiscreteLaw d) := Measure.dirac P0
  let prior1 : Measure (DiscreteLaw d) := Measure.dirac P1
  let experimentKernel : Kernel (DiscreteLaw d) (RawPoissonCounts d) :=
    { toFun := fun P => rawPoissonLaw P 1 0 0
      measurable' := measurable_from_top }
  refine {
    finiteAtomConstruction := False
    kappa := (1 - 2 * eps) / eps
    degree_ge_two := False.elim
    bandwidth_pos := False.elim
    shift_eq := False.elim
    kappa_eq := rfl
    rareCount_le := hk
    reservoir := r
    reservoir_is_first := rfl
    rareCell := parametricRareCell hk
    rareCell_injective := parametricRareCell_injective hk
    reservoir_ne_rare := parametricReservoir_ne_rare r rfl hk
    outcomeSign := fun _ => 1
    outcomeSign_mem := by intro; norm_num
    generator := generator
    generatorProbability := by dsimp [generator]; infer_instance
    sigma := sigma
    sigmaVariationProbability := by
      dsimp [sigma]
      simpa only [Measure.variation_toSignedMeasure] using
        (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : Real)))
    sigma_support := False.elim
    outcomeSign_integrable := by
      dsimp [sigma]
      simp
    sigma_density := by
      dsimp [sigma]
      rw [Measure.variation_toSignedMeasure]
      ext s hs
      rw [Measure.toSignedMeasure_apply_measurable hs,
        withDensityᵥ_apply (by simp) hs]
      simp [Measure.real, hs]
    nu := nu
    nuProbability := by dsimp [nu]; infer_instance
    nu_eq := False.elim
    generator_eq_iid := by
      dsimp [generator, nu]
    generator_support := False.elim
    dual0 := dual
    dual1 := dual
    dualProbability0 := by dsimp [dual]; infer_instance
    dualProbability1 := by dsimp [dual]; infer_instance
    dualSupport0 := False.elim
    dualSupport1 := False.elim
    dualMomentMatch := False.elim
    dualSeparation := False.elim
    sigmaMomentZero := False.elim
    sigmaSeparation := False.elim
    lawOf := lawOf
    lawOf_measurable := by intro branch; fun_prop
    rawMass := fun _ x => if x = r then 1 else 0
    rawTotalMass := fun _ => 1
    rawTarget := fun branch _ => ateFunctional (if branch then P1 else P0)
    rawMass_sum := by
      exact Filter.Eventually.of_forall fun _ => by simp
    rawMass_pos := by exact Filter.Eventually.of_forall fun _ => by simp
    rareRawMass := False.elim
    reservoirRawMass := False.elim
    unusedRawMass := by
      apply Filter.Eventually.of_forall
      intro _ x hx _
      simp [hx]
    normalization := by
      intro branch
      apply Filter.Eventually.of_forall
      intro _ x
      cases branch <;> simp [lawOf, P0, P1, parametricReservoirLaw_cellMass]
    rawTarget_formula := by
      intro branch
      exact Filter.Eventually.of_forall fun _ => by simp [lawOf]
    rawScale := fun _ => 1
    rawScale_measurable := measurable_const
    rawScale_lawOf := by
      intro branch
      exact Filter.Eventually.of_forall fun _ => by simp
    commonTable_pointwise := by
      apply Filter.Eventually.of_forall
      intro _
      dsimp [lawOf, P0, P1]
      exact parametricReservoirLaw_auxTable_eq heps heps2 r hg0 hg1
    rareTreatmentMass := False.elim
    reservoirPropensity := by
      intro branch
      apply Filter.Eventually.of_forall
      intro _
      cases branch <;> simp [lawOf, P0, P1, parametricReservoirLaw_propensity]
    controlOutcomeZero := by
      intro branch
      apply Filter.Eventually.of_forall
      intro _ x
      cases branch <;> simp [lawOf, P0, P1, parametricReservoirLaw_outcomeMean]
    reservoirTreatedOutcomeZero := False.elim
    rareOutcomeMeans := False.elim
    parametricShape := by
      intro _
      apply Filter.Eventually.of_forall
      intro _
      refine ⟨hgap, ?_⟩
      simp [lawOf, P0, P1, parametricReservoirLaw_cellMass,
        parametricReservoirLaw_outcomeMean, delta]
    model0 := by
      apply Filter.Eventually.of_forall
      intro _
      simpa [lawOf, P0] using parametricReservoirLaw_model hd heps heps2 r hg0
    model1 := by
      apply Filter.Eventually.of_forall
      intro _
      simpa [lawOf, P1] using parametricReservoirLaw_model hd heps heps2 r hg1
    prior0 := prior0
    prior1 := prior1
    prior0_eq := by simp [prior0, generator, lawOf]
    prior1_eq := by simp [prior1, generator, lawOf]
    probability0 := by dsimp [prior0]; infer_instance
    probability1 := by dsimp [prior1]; infer_instance
    priorModel0 := by
      simp only [prior0, MeasureTheory.ae_dirac_eq, Filter.eventually_pure]
      exact parametricReservoirLaw_model hd heps heps2 r hg0
    priorModel1 := by
      simp only [prior1, MeasureTheory.ae_dirac_eq, Filter.eventually_pure]
      exact parametricReservoirLaw_model hd heps heps2 r hg1
    labeledIntensity := 0
    auxiliaryIntensity := 0
    experimentKernel := experimentKernel
    experimentKernel_eq := by intro P; rfl
    rawExperiment0 := Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
      prior0 experimentKernel
    rawExperiment1 := Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
      prior1 experimentKernel
    rawExperiment0_eq := rfl
    rawExperiment1_eq := rfl }

/-- The single-reservoir recipe, specialized to the four paper-facing scales, populates a prior
handle whenever the parametric branch condition and root-`n` shift bound hold.  [the stated conditions](hyp:calibration,n,m,d,hd,hn,heps,heps2,hreg,hgap) [the stated conclusion](goal). -/
noncomputable def parametricCommonMarginalPriorHandle {eps : Real}
    (calibration : CommonMarginalCalibration eps) (n m d : Nat)
    (hd : 2 ≤ d) (hn : 1 ≤ n) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (hreg : commonMarginalParametricRegime calibration n m d)
    (hgap : calibration.dualGap / Real.sqrt n ≤ 1 / 4) :
    CommonMarginalPriorHandle calibration n m d := by
  let L := Nat.ceil (calibration.degreeConstant * logEN n)
  let B := calibration.bandwidthConstant * L / (n + m : Nat)
  let a := calibration.gamma * B / (L : Real) ^ 2
  let k := min (d - 1) ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊
  have hk : k ≤ d - 1 := by
    dsimp [k]
    exact min_le_left _ _
  let recipe := parametricCommonMarginalRecipe calibration n m d L B a k
    hd hn heps heps2 hk hgap
  refine {
    L := L
    B := B
    a := a
    k := k
    recipe := recipe
    branchCondition := by
      change False ↔ ¬commonMarginalParametricRegime calibration n m d
      simp [hreg]
    degree_eq := rfl
    bandwidth_eq := rfl
    shift_eq := rfl
    rareCount_eq := rfl }

end

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
