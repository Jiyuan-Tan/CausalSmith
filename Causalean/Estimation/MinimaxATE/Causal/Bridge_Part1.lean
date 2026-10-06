/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Estimation.ATE.Setup
public import Causalean.Estimation.MinimaxATE.Causal.Construction
public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.PO.Bridge.FromSCMCondIndep
public import Causalean.SCM.Factored.ObsChainKernel
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Causal Grounding of the Minimax ATE Model: Foundations

This first part defines the causal ATE of the constructed backdoor system and proves consistency,
coordinate formulas for its factual and potential-outcome variables, and elementary integral and
conditional-expectation facts used by the later bridge parts. The final identification theorem is
proved in `Bridge_Part3.lean`. -/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

open Causalean.Mathlib.Probability.Independence

namespace Causalean.Estimation.MinimaxATE.Causal

open Causalean Causalean.PO Causalean.Estimation.ATE
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {C : Type} [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [StandardBorelSpace C]
variable {m : C → ℝ} {g : Bool → C → ℝ}

/-! ## Carrier regularity instances -/
/-- For [a finite, nonempty covariate space equipped with a measurable structure whose singletons are measurable, a propensity function, and an outcome-regression function for both treatment arms](hyp:C,m,g), [the population law of the constructed potential-outcome system is a probability measure](goal). -/
instance dgpPO_isProb : IsProbabilityMeasure (dgpPO m g).μ := by
  change IsProbabilityMeasure (SCM.latentProduct (dgpSCM m g))
  infer_instance

/-- The constructed potential-outcome system has a standard Borel sample space. -/
theorem dgpPO_borel : StandardBorelSpace (dgpPO m g).Ω := by
  change StandardBorelSpace (SCM.LatentValues (dgpSCM m g))
  haveI : ∀ n : SWIGNode WNode, StandardBorelSpace (swigΩ (WΩ C) n) := by
    intro n; cases n <;> infer_instance
  exact StandardBorelSpace.pi_countable

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose singletons are measurable and a standard-Borel structure, a propensity function, and an outcome-regression function for both treatment arms](hyp:C,m,g), [the sample space of the constructed potential-outcome system has a standard-Borel structure](goal). -/
noncomputable instance dgpPO_standardBorel : StandardBorelSpace (dgpPO m g).Ω :=
  dgpPO_borel

/-! ## The causal estimand -/

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable](hyp:C),
[a propensity function](hyp:m), and [an outcome-regression function](hyp:g), [the causal average
treatment effect](goal) is the average treatment effect of the constructed finite backdoor
potential-outcome system.

The theorem `causalATE_eq_ate` later identifies this potential-outcome estimand with the finite
observed-data contrast `ate g` under validity and strict overlap. -/
noncomputable def causalATE (m : C → ℝ) (g : Bool → C → ℝ) : ℝ :=
  (dgpBackdoor m g).ATE

/-! ## Causal-layer obligations (mirrors the CausalSmith stat witness) -/

/-- The constructed potential-outcome system satisfies consistency. -/
theorem dgp_consistency : (dgpPO m g).Consistency :=
  POSystem.ofSCM_consistency (dgpSCM m g) (dgpFixed m g)

/-- For [a propensity function](hyp:m) and [an outcome-regression function](hyp:g), the
[covariate-noise index](goal) identifies the latent disturbance that generates covariates in the
constructed potential-outcome system. It is used to read the factual covariate from a latent
realization. -/
abbrev iUn (m : C → ℝ) (g : Bool → C → ℝ) :
    {u // u ∈ (dgpSCM m g).unobserved} :=
  ⟨SWIGNode.random WNode.Un, by simp [dgpSCM, wSWIGGraph]⟩

/-- For [a propensity function](hyp:m) and [an outcome-regression function](hyp:g), the
[treatment-assignment-noise index](goal) identifies the latent disturbance that determines
treatment in the constructed potential-outcome system. It is used to express the factual
treatment rule. -/
abbrev iEa (m : C → ℝ) (g : Bool → C → ℝ) :
    {u // u ∈ (dgpSCM m g).unobserved} :=
  ⟨SWIGNode.random WNode.Ea, by simp [dgpSCM, wSWIGGraph]⟩

/-- For [a propensity function](hyp:m) and [an outcome-regression function](hyp:g), the
[outcome-noise index](goal) identifies the latent disturbance that generates outcomes in the
constructed potential-outcome system. It is used to express factual and counterfactual outcome
rules. -/
abbrev iEy (m : C → ℝ) (g : Bool → C → ℝ) :
    {u // u ∈ (dgpSCM m g).unobserved} :=
  ⟨SWIGNode.random WNode.Ey, by simp [dgpSCM, wSWIGGraph]⟩

private lemma dgp_AIdx_name :
    Classical.choose ((dgpSCM m g).observed_is_random (AIdx m g).val (AIdx m g).property) =
      WNode.A := by
  have hspec :=
    Classical.choose_spec ((dgpSCM m g).observed_is_random (AIdx m g).val
      (AIdx m g).property)
  change SWIGNode.random WNode.A =
      SWIGNode.random
        (Classical.choose ((dgpSCM m g).observed_is_random (AIdx m g).val
          (AIdx m g).property)) at hspec
  injection hspec with h
  exact h.symm

private lemma dgp_regimeTargetN_single_A (d : Bool) :
    regimeTargetN (dgpSCM m g)
      (Regime.single (AIdx m g) (show obsValue (dgpSCM m g) (AIdx m g) from d)) =
        {WNode.A} := by
  classical
  ext D
  constructor
  · intro hD
    simp only [regimeTargetN, Finset.mem_image] at hD
    rcases hD with ⟨v, hv, hname⟩
    have hvA : v = AIdx m g := by
      have hv_target : v ∈
          (Regime.single (AIdx m g) (show obsValue (dgpSCM m g) (AIdx m g) from d)).target :=
        (Finset.mem_filter.mp hv).1
      have hv_single : v ∈ ({AIdx m g} : Finset (ObsIdx (dgpSCM m g))) := by
        exact hv_target
      exact Finset.mem_singleton.mp hv_single
    subst v
    rw [dgp_AIdx_name (m := m) (g := g)] at hname
    simpa [hname]
  · intro hD
    have hDA : D = WNode.A := by simpa using hD
    subst D
    simp only [regimeTargetN, Finset.mem_image]
    refine ⟨AIdx m g, ?_, dgp_AIdx_name (m := m) (g := g)⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_singleton_self (AIdx m g),
      by simpa [dgp_AIdx_name (m := m) (g := g), dgpSCM, wSWIGGraph]⟩

/-- For [a finite covariate space, propensity function, and outcome regression](hyp:C,m,g), [the
constructed backdoor data-generating process's factual covariate equals its latent covariate coordinate](goal). -/
lemma dgp_factualX_eq_latentUn :
    (dgpBackdoor m g).factualX =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) := by
  funext ℓ
  simp only [POBackdoorSystem.factualX, POVar.factual, POVar.cf]
  change (dgpBackdoor m g).xVar.equiv
      (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (XIdx m g)) =
    ℓ (iUn (C := C) m g)
  rw [inducedEval_empty_eq_evalMap (dgpSCM m g) (dgpFixed m g) ℓ (XIdx m g)]
  change (XEquiv m g)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by
          simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩) =
    ℓ (iUn (C := C) m g)
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
  unfold XEquiv dgpSCM parentVal iUn
  rfl

/-- The [covariate singleton equivalence](goal) identifies a covariate value with the
configuration containing that value at the covariate node alone. It lets the constructed system
compare ordinary covariate values with graph-indexed configurations. -/
noncomputable def dgpXSingletonEquiv :
    C ≃ᵐ ValuesOn ({SWIGNode.random WNode.Xc} : Finset (SWIGNode WNode)) (swigΩ (WΩ C)) where
  toFun := singletonValues (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc)
  invFun := singletonValue (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc)
  left_inv := fun x =>
    singletonValue_singletonValues (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc) x
  right_inv := fun x =>
    singletonValues_singletonValue (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc) x
  measurable_toFun := measurable_singletonValues (α := swigΩ (WΩ C))
  measurable_invFun := measurable_singletonValue (α := swigΩ (WΩ C))

/-- For [a finite covariate space, propensity function, and outcome regression](hyp:C,m,g), [the
constructed backdoor process's factual treatment is the threshold treatment function of its latent
covariate and treatment-noise coordinates](goal). -/
lemma dgp_factualD_eq_treatFun :
    (dgpBackdoor m g).factualD =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) := by
  funext ℓ
  simp only [POBackdoorSystem.factualD, POVar.factual, POVar.cf]
  change (dgpBackdoor m g).dVar.equiv
      (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (AIdx m g)) =
    treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
  rw [inducedEval_empty_eq_evalMap (dgpSCM m g) (dgpFixed m g) ℓ (AIdx m g)]
  change (AEquiv m g)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.A, by
          simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩) =
    treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.A, by simp [dgpSCM, wSWIGGraph]⟩]
  change treatFun
      (m ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by
          simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩))
      (ℓ (iEa (C := C) m g)) =
    treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
  unfold dgpSCM parentVal iUn
  rfl

/-- For [a finite covariate space, propensity function, and outcome regression](hyp:C,m,g), [the
constructed backdoor process's factual outcome is its outcome function evaluated at the threshold
treatment, latent covariate, and outcome-noise coordinates](goal). -/
lemma dgp_factualY_eq_outFun :
    (dgpBackdoor m g).factualY =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        outFun (C := C) g
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
          (ℓ (iUn (C := C) m g))
          (ℓ (iEy (C := C) m g))) := by
  funext ℓ
  simp only [POBackdoorSystem.factualY, POVar.factual, POVar.cf]
  change (dgpBackdoor m g).yVar.equiv
      (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (YIdx m g)) =
    outFun (C := C) g
      (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
      (ℓ (iUn (C := C) m g))
      (ℓ (iEy (C := C) m g))
  rw [inducedEval_empty_eq_evalMap (dgpSCM m g) (dgpFixed m g) ℓ (YIdx m g)]
  change (YEquiv m g)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Y, by
          simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩) =
    outFun (C := C) g
      (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
      (ℓ (iUn (C := C) m g))
      (ℓ (iEy (C := C) m g))
  rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
    ⟨SWIGNode.random WNode.Y, by simp [dgpSCM, wSWIGGraph]⟩]
  change outFun (C := C) g
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.A, by
          simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩)
      ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by
          simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩)
      (ℓ (iEy (C := C) m g)) =
    outFun (C := C) g
      (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
      (ℓ (iUn (C := C) m g))
      (ℓ (iEy (C := C) m g))
  have hAeval :
      (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.A, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩ =
        treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)) := by
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.A, by simp [dgpSCM, wSWIGGraph]⟩]
    change treatFun
        (m ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩))
        (ℓ (iEa (C := C) m g)) =
      treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    unfold dgpSCM parentVal iUn
    rfl
  have hXeval :
      (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩ =
        ℓ (iUn (C := C) m g) := by
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    unfold dgpSCM parentVal iUn
    rfl
  rw [hAeval, hXeval]

/-- For [a finite covariate space, propensity function, outcome regression, and treatment value](hyp:C,m,g,d),
[the constructed backdoor process's potential outcome at that treatment equals its outcome function
of the latent covariate and outcome-noise coordinates](goal). -/
lemma dgp_YofD_eq_outFun (d : Bool) :
    (dgpBackdoor m g).YofD d =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))) := by
  funext ℓ
  let r : Regime (ObsIdx (dgpSCM m g)) (obsValue (dgpSCM m g)) :=
    Regime.single (AIdx m g) d
  let M' := (dgpSCM m g).fixSet (regimeTargetN (dgpSCM m g) r)
    (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
  unfold POBackdoorSystem.YofD POVar.cfUnder POVar.cf
  change (YEquiv m g)
      (M'.evalMap (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
        ⟨SWIGNode.random WNode.Y, by
          simp [M', SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩) =
    outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))
  let ξ : ∀ w : {w // w ∈ M'.dag.parents (SWIGNode.random WNode.Y)}, swigΩ (WΩ C) w.val :=
    fun w =>
      if huo : w.val ∈ M'.unobserved then ℓ ⟨w.val, huo⟩
      else if hfix : w.val ∈ M'.fixed then
        combinedFixed (dgpSCM m g) (dgpFixed m g) r ⟨w.val, hfix⟩
      else
        have hedge : M'.dag.edge w.val (SWIGNode.random WNode.Y) := M'.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M'.observed := by
          rcases Finset.mem_union.mp (M'.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        M'.evalMap (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
          ⟨w.val, Finset.mem_union_left _ hobs⟩
  rw [SCM.evalMap_fixSet_observed_apply (dgpSCM m g) (regimeTargetN (dgpSCM m g) r)
    (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
    (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
    ⟨SWIGNode.random WNode.Y, by simp [dgpSCM, wSWIGGraph]⟩]
  change (YEquiv m g) ((dgpSCM m g).structFun ⟨SWIGNode.random WNode.Y, by
      simp [dgpSCM, wSWIGGraph]⟩
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)) =
    outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))
  simp only [YEquiv, dgpSCM]
  change outFun (C := C) g
      (parentVal (C := C)
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)
        (show wEdge WNode.A WNode.Y from trivial))
      (parentVal (C := C)
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)
        (show wEdge WNode.Xc WNode.Y from trivial))
      (parentVal (C := C)
        (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
          (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
          (SWIGNode.random WNode.Y) ξ)
        (show wEdge WNode.Ey WNode.Y from trivial)) =
    outFun (C := C) g d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))
  have hTargetA : regimeTargetN (dgpSCM m g) r = {WNode.A} := by
    dsimp [r]
    exact dgp_regimeTargetN_single_A (m := m) (g := g) d
  have hDmem : WNode.A ∈ regimeTargetN (dgpSCM m g) r := by
    simpa [hTargetA]
  have hAtgt : (AIdx m g) ∈ r.target := by
    change (AIdx m g) ∈ ({AIdx m g} : Finset (ObsIdx (dgpSCM m g)))
    exact Finset.mem_singleton_self (AIdx m g)
  have hAval : (AIdx m g).val = SWIGNode.random WNode.A := by
    rfl
  have hA : parentVal (C := C)
      (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ)
      (show wEdge WNode.A WNode.Y from trivial) = d := by
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ
        ⟨SWIGNode.random WNode.A, wParent_mem (show wEdge WNode.A WNode.Y from trivial)⟩ = d
    refine (SCM.fixMonoParentMap_apply_random (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Y) WNode.A hDmem
      ξ _).trans ?_
    dsimp [ξ]
    have hAf_unobs : SWIGNode.fixed WNode.A ∉ M'.unobserved := by
      show SWIGNode.fixed WNode.A ∉ (dgpSCM m g).unobserved
      simp [dgpSCM, wSWIGGraph]
    have hAf_fixed : SWIGNode.fixed WNode.A ∈ M'.fixed :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨WNode.A, hDmem, rfl⟩)
    rw [dif_neg hAf_unobs, dif_pos hAf_fixed]
    change (combinedFixed (dgpSCM m g) (dgpFixed m g) r
      ⟨SWIGNode.fixed WNode.A, hAf_fixed⟩ : Bool) = d
    rw [combinedFixed_new (dgpSCM m g) (dgpFixed m g) r
      (AIdx m g) hAtgt WNode.A hDmem hAval]
    rfl
  rw [hA]
  have hXeval : M'.evalMap (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
      ⟨SWIGNode.random WNode.Xc, Finset.mem_union_left _ (by simp [M', dgpSCM, wSWIGGraph])⟩ =
    ℓ (iUn (C := C) m g) := by
    rw [SCM.evalMap_fixSet_observed_apply (dgpSCM m g) (regimeTargetN (dgpSCM m g) r)
      (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
      (combinedFixed (dgpSCM m g) (dgpFixed m g) r) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    simp only [dgpSCM]
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Xc) _
        ⟨SWIGNode.random WNode.Un, wParent_mem (show wEdge WNode.Un WNode.Xc from trivial)⟩ =
      ℓ (iUn (C := C) m g)
    refine (SCM.fixMonoParentMap_apply_random_notMem (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Xc)
      _ WNode.Un (by simpa [hTargetA]) _).trans ?_
    exact dif_pos (iUn (C := C) m g).property
  have hXnot : WNode.Xc ∉ regimeTargetN (dgpSCM m g) r := by
    simpa [hTargetA]
  have hX : parentVal (C := C)
      (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ)
      (show wEdge WNode.Xc WNode.Y from trivial) = ℓ (iUn (C := C) m g) := by
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ
        ⟨SWIGNode.random WNode.Xc, wParent_mem (show wEdge WNode.Xc WNode.Y from trivial)⟩ =
      ℓ (iUn (C := C) m g)
    refine (SCM.fixMonoParentMap_apply_random_notMem (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Y)
      ξ WNode.Xc hXnot _).trans ?_
    dsimp [ξ]
    have hXc_unobs : SWIGNode.random WNode.Xc ∉ M'.unobserved := by
      show SWIGNode.random WNode.Xc ∉ (dgpSCM m g).unobserved
      simp [dgpSCM, wSWIGGraph]
    have hXc_fixed : SWIGNode.random WNode.Xc ∉ M'.fixed := by
      show SWIGNode.random WNode.Xc ∉
        (dgpSCM m g).fixed ∪ (regimeTargetN (dgpSCM m g) r).image SWIGNode.fixed
      intro hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact absurd h (by
          show SWIGNode.random WNode.Xc ∉ (∅ : Finset (SWIGNode WNode))
          simp)
      · obtain ⟨D, -, hD⟩ := Finset.mem_image.mp h
        simp at hD
    rw [dif_neg hXc_unobs, dif_neg hXc_fixed]
    exact hXeval
  rw [hX]
  have hEynot : WNode.Ey ∉ regimeTargetN (dgpSCM m g) r := by
    simpa [hTargetA]
  have hEy : parentVal (C := C)
      (SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ)
      (show wEdge WNode.Ey WNode.Y from trivial) = ℓ (iEy (C := C) m g) := by
    change SCM.fixMonoParentMap (dgpSCM m g).toSWIGGraph (regimeTargetN (dgpSCM m g) r)
        (regimeTargetN_obs (dgpSCM m g) r) (regimeTargetN_notFixed (dgpSCM m g) r)
        (SWIGNode.random WNode.Y) ξ
        ⟨SWIGNode.random WNode.Ey, wParent_mem (show wEdge WNode.Ey WNode.Y from trivial)⟩ =
      ℓ (iEy (C := C) m g)
    refine (SCM.fixMonoParentMap_apply_random_notMem (Ω := WΩ C) (dgpSCM m g).toSWIGGraph
      (regimeTargetN (dgpSCM m g) r) (regimeTargetN_obs (dgpSCM m g) r)
      (regimeTargetN_notFixed (dgpSCM m g) r) (SWIGNode.random WNode.Y)
      ξ WNode.Ey hEynot _).trans ?_
    dsimp [ξ]
    exact dif_pos (iEy (C := C) m g).property
  rw [hEy]

/-- For [a finite covariate space, propensity function, and outcome regression](hyp:C,m,g), [the
indicator of factual treatment being true in the constructed process equals the indicator that
treatment noise does not exceed the propensity at the latent covariate](goal). -/
lemma dgp_dIndicator_true_eq_threshold :
    (dgpBackdoor m g).dVar.indicator true =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if (show ℝ from ℓ (iEa (C := C) m g)) ≤
            m (show C from ℓ (iUn (C := C) m g)) then (1 : ℝ) else 0) := by
  funext ℓ
  unfold POVar.indicator POVar.event
  change (((dgpBackdoor m g).factualD ⁻¹' {true}).indicator (fun _ => (1 : ℝ))) ℓ =
    (if (show ℝ from ℓ (iEa (C := C) m g)) ≤
        m (show C from ℓ (iUn (C := C) m g)) then (1 : ℝ) else 0)
  have hval : (dgpBackdoor m g).factualD ℓ =
      treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)) := by
    rw [dgp_factualD_eq_treatFun (m := m) (g := g)]
  by_cases h : (show ℝ from ℓ (iEa (C := C) m g)) ≤
      m (show C from ℓ (iUn (C := C) m g))
  · have hb : (dgpBackdoor m g).factualD ℓ = true := by
      rw [hval]
      unfold treatFun
      simp only [decide_eq_true_eq]
      exact h
    rw [Set.indicator_of_mem
      (show ℓ ∈ (dgpBackdoor m g).factualD ⁻¹' ({true} : Set Bool) from hb), if_pos h]
  · have hb : (dgpBackdoor m g).factualD ℓ = false := by
      rw [hval]
      unfold treatFun
      simp only [decide_eq_false_iff_not]
      exact h
    have hnot : ℓ ∉ (dgpBackdoor m g).factualD ⁻¹' ({true} : Set Bool) := by
      intro hmem
      have hmem' : (dgpBackdoor m g).factualD ℓ = true := hmem
      rw [hb] at hmem'
      exact Bool.noConfusion hmem'
    rw [Set.indicator_of_notMem hnot, if_neg h]

/-- For [a threshold between zero and one](hyp:t,ht), [the uniform-law integral of the indicator
that a draw does not exceed the threshold equals the threshold](goal). -/
lemma unifLaw_integral_Iic_indicator (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ e, (if e ≤ t then (1 : ℝ) else 0) ∂unifLaw = t := by
  have hs : MeasurableSet (Set.Iic t : Set ℝ) := measurableSet_Iic
  have hfun : (fun e : ℝ => if e ≤ t then (1 : ℝ) else 0) =
      (Set.Iic t).indicator (fun _ => (1 : ℝ)) := by
    funext e
    by_cases h : e ≤ t
    · simp [Set.indicator_of_mem, h]
    · simp [Set.indicator_of_notMem, h]
  rw [hfun]
  have hint : ∫ e, (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) e ∂unifLaw =
      unifLaw.real (Set.Iic t) := by
    exact MeasureTheory.integral_indicator_one (μ := unifLaw) hs
  rw [hint]
  rw [MeasureTheory.measureReal_def]
  unfold unifLaw
  rw [Measure.restrict_apply hs]
  have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) t := by
    ext e
    constructor
    · intro h
      exact ⟨h.2.1, h.1⟩
    · intro h
      exact ⟨h.2, ⟨h.1, le_trans h.2 ht.2⟩⟩
  rw [hset, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal]
  · simp
  · simpa using ht.1

/-- On [a finite measure space, for a real-valued function](hyp:Ω,μ,f), if [the function is
measurable](hyp:hf) and [takes only the values zero and one](hyp:h01), then [it is integrable](goal). -/
lemma integrable_of_measurable_zero_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (h01 : ∀ ω, f ω = 0 ∨ f ω = 1) :
    Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
  intro ω
  rcases h01 ω with h | h <;> simp [h]

private lemma dgp_indep_ea_un :
    Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEa (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance)
      (dgpPO m g).μ := by
  change Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEa (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance)
      ((dgpSCM m g).latentProduct)
  rw [← IndepFun_iff_Indep]
  change IndepFun
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEa (C := C) m g))
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g))
      (Measure.pi (dgpSCM m g).latentDist)
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  have hdisj : Disjoint ({iEa (C := C) m g} : Finset {u // u ∈ (dgpSCM m g).unobserved})
      ({iUn (C := C) m g} : Finset {u // u ∈ (dgpSCM m g).unobserved}) := by
    simp
  have hbase := indepFun_pi_of_disjoint
    (Ω := fun u : {u // u ∈ (dgpSCM m g).unobserved} => swigΩ (WΩ C) u.val)
    (S := {iEa (C := C) m g}) (T := {iUn (C := C) m g})
    (fun u => (dgpSCM m g).latentDist u) hdisj
  have hcomp := hbase.comp
    (measurable_pi_apply
      (⟨iEa (C := C) m g, by simp⟩ :
        {u // u ∈ ({iEa (C := C) m g} :
          Finset {u // u ∈ (dgpSCM m g).unobserved})}))
    (measurable_pi_apply
      (⟨iUn (C := C) m g, by simp⟩ :
        {u // u ∈ ({iUn (C := C) m g} :
          Finset {u // u ∈ (dgpSCM m g).unobserved})}))
  have h_fintype : Fintype.ofFinite {u // u ∈ (dgpSCM m g).unobserved} =
      Finset.Subtype.fintype (dgpSCM m g).unobserved :=
    Subsingleton.elim _ _
  rw [h_fintype] at hcomp
  exact hcomp

private lemma dgp_integral_ea_threshold (x : C) (ht : m x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0) ∂(dgpPO m g).μ =
      m x := by
  change ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (fun e : ℝ => if e ≤ m x then (1 : ℝ) else 0) (ℓ (iEa (C := C) m g)) ∂Measure.pi
        (dgpSCM m g).latentDist =
      m x
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  have hf_meas : Measurable (fun e : ℝ => if e ≤ m x then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  rw [← integral_map (μ := Measure.pi (dgpSCM m g).latentDist)
    (f := fun e : ℝ => if e ≤ m x then (1 : ℝ) else 0)
    (measurable_pi_apply (iEa (C := C) m g)).aemeasurable]
  swap
  · exact hf_meas.aestronglyMeasurable
  rw [Measure.pi_map_eval]
  have hscale : (∏ j ∈ Finset.univ.erase (iEa (C := C) m g),
      ((dgpSCM m g).latentDist j) Set.univ) = 1 := by
    simp
  rw [hscale, one_smul]
  unfold iEa dgpSCM
  change ∫ e, (if e ≤ m x then (1 : ℝ) else 0) ∂unifLaw = m x
  exact unifLaw_integral_Iic_indicator (m x) ht

/-- For [a finite standard-Borel covariate population, propensity function, and two outcome
regressions](hyp:C,m,g), [a fixed covariate value](hyp:x), and [the requirement that its
propensity lies between zero and one](hyp:ht), [the conditional mean of the latent treatment
threshold indicator given the covariate equals that propensity almost surely](goal). -/
lemma dgp_condExp_ea_threshold_const (x : C) (ht : m x ∈ Set.Icc (0 : ℝ) 1) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0 |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance]
      =ᵐ[(dgpPO m g).μ] fun _ => m x := by
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEa (C := C) m g)
  let uFun : SCM.LatentValues (dgpSCM m g) → C := fun ℓ => ℓ (iUn (C := C) m g)
  let eInd : SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun ℓ => if eFun ℓ ≤ m x then (1 : ℝ) else 0
  have he_sm : StronglyMeasurable[MeasurableSpace.comap eFun inferInstance] eInd := by
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap eFun inferInstance
    have he_meas : Measurable eFun := comap_measurable eFun
    have hset : MeasurableSet {ℓ : SCM.LatentValues (dgpSCM m g) | eFun ℓ ≤ m x} :=
      measurableSet_le he_meas measurable_const
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  have hle_e : MeasurableSpace.comap eFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [eFun]
    exact (measurable_pi_apply (iEa (C := C) m g)).comap_le
  have hle_u : MeasurableSpace.comap uFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [uFun]
    exact (measurable_pi_apply (iUn (C := C) m g)).comap_le
  haveI : IsProbabilityMeasure (dgpPO m g).μ := dgpPO_isProb
  haveI : IsFiniteMeasure (dgpPO m g).μ := inferInstance
  haveI : IsFiniteMeasure ((dgpPO m g).μ.trim hle_u) :=
    isFiniteMeasure_trim (μ := (dgpPO m g).μ) hle_u
  have hsig : SigmaFinite ((dgpPO m g).μ.trim hle_u) :=
    MeasureTheory.IsFiniteMeasure.toSigmaFinite ((dgpPO m g).μ.trim hle_u)
  have hmain := by
    exact @MeasureTheory.condExp_indep_eq
      (SCM.LatentValues (dgpSCM m g)) ℝ _ _ _
      (MeasurableSpace.comap eFun inferInstance)
      (MeasurableSpace.comap uFun inferInstance)
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g)))
      ((dgpPO m g).μ) eInd hle_e hle_u hsig he_sm dgp_indep_ea_un
  have hmain' :
      (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0 |
        MeasurableSpace.comap
          (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance]
        =ᵐ[(dgpPO m g).μ]
          fun _ => ∫ ℓ : SCM.LatentValues (dgpSCM m g),
            (if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0) ∂(dgpPO m g).μ := by
    exact hmain
  refine hmain'.trans ?_
  exact Filter.Eventually.of_forall fun ℓ => by
    dsimp [eInd, eFun, uFun]
    change (∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEa (C := C) m g)) ≤ m x then (1 : ℝ) else 0) ∂(dgpPO m g).μ) =
      m x
    exact dgp_integral_ea_threshold (m := m) (g := g) x ht

end Causalean.Estimation.MinimaxATE.Causal
