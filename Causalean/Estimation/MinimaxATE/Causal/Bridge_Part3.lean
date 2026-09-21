/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Estimation.MinimaxATE.Causal.Bridge_Part2
public import Causalean.Mathlib.MeasureTheory.FinsetValues

/-! # Causal Grounding of the Minimax ATE Model: Identification

This third part completes the interface between the causal layer (the
`POBackdoorSystem` built in `Construction.lean`) and the observed-data contrast `ate g` on which
the minimax proof machinery computes.

The headline theorem is `causalATE_eq_ate`:

    causalATE m g  =  ate g           (under strict overlap `0 < m x < 1`)

where `causalATE m g := (dgpBackdoor m g).ATE = ∫ (Y(1) − Y(0)) dμ` is the
potential-outcome ATE of the constructed backdoor system.  With this in hand the
causal-centered lower bounds in `Causal/Minimax.lean` are bounds on the *causal*
estimand, identified by backdoor adjustment, not merely on a regression contrast.

The final proof routes through the reusable `BackdoorEstimationSystem.θ₀_eq_ATE`
(`Estimation/ATE/Setup.lean`): instantiate the estimation system with value-space
regression `μ_val := g` and propensity `e_val := m`, so that
`θ₀ = ∫ (g 1 − g 0) dP_X` and `θ₀ = S.ATE`; then `P_X = Uniform(C)` collapses
`θ₀` to the average `(1/card C) Σ_x (g 1 x − g 0 x) = ate g`.

This part proves `dgp_unconfoundedness` and `dgp_adjustedCE_eq_g`, the genuine
causal-layer obligations: the d-separation lift and the outcome-regression
conditional-mean computation of the constructed SCM law. It also proves
`dgp_propScore_eq_m`, `dgp_overlap`, `dgp_assumptions`, and `dgp_P_X_eq_covLaw`, then uses
`dgpBES` to assemble the backdoor-estimation-system interface needed for the final bridge theorem.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean.Estimation.MinimaxATE.Causal

open Causalean Causalean.PO Causalean.Estimation.ATE
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {C : Type} [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [StandardBorelSpace C]
variable {m : C → ℝ} {g : Bool → C → ℝ}

/-! ## Carrier regularity instances -/
/-- **Unconfoundedness** `A ⟂ (Y(1), Y(0)) | X`.  The treatment noise `Ea` and
outcome noise `Ey` are independent latent roots given the covariate, so the
realized treatment is conditionally independent of the potential-outcome bundle
given `X`.  Discharged via `POSystem.ofSCM_condIndepCF_of_dSep` (d-separation in
the split graph + value correspondences). -/
theorem dgp_unconfoundedness :
    (dgpPO m g).CondIndepCF
      (RegimedVar.ofFactual (dgpBackdoor m g).dVar)
      (dgpBackdoor m g).cfBundle
      (RegimedVar.ofFactual (dgpBackdoor m g).xVar)
      (dgpPO m g).μ := by
  classical
  let X : Finset (SWIGNode WNode) := {SWIGNode.random WNode.A}
  let Y : Finset (SWIGNode WNode) :=
    {SWIGNode.random WNode.Ey, SWIGNode.random WNode.Un}
  let Z : Finset (SWIGNode WNode) := {SWIGNode.random WNode.Xc}
  let cVar : POVar (dgpPO m g) (ValuesOn Z (swigΩ (WΩ C))) :=
    ⟨XIdx m g, by
      exact dgpXSingletonEquiv (C := C)⟩
  let c : RegimedVar (dgpPO m g) (ValuesOn Z (swigΩ (WΩ C))) :=
    RegimedVar.ofFactual cVar
  let aMap : ValuesOn X (swigΩ (WΩ C)) → Bool :=
    fun vals => vals ⟨SWIGNode.random WNode.A, by simp [X]⟩
  let BMap : ValuesOn Y (swigΩ (WΩ C)) →
      (∀ i : Fin (dgpBackdoor m g).cfBundle.n, (dgpBackdoor m g).cfBundle.type i) :=
    fun vals i => by
      dsimp [POBackdoorSystem.cfBundle, POCFBundle.cons, POCFBundle.nil] at i ⊢
      exact Fin.cases
        (outFun (C := C) g true
          (vals ⟨SWIGNode.random WNode.Un, by simp [Y]⟩)
          (vals ⟨SWIGNode.random WNode.Ey, by simp [Y]⟩))
        (fun j => Fin.cases
          (outFun (C := C) g false
            (vals ⟨SWIGNode.random WNode.Un, by simp [Y]⟩)
            (vals ⟨SWIGNode.random WNode.Ey, by simp [Y]⟩))
          (fun k => k.elim0) j) i
  haveI : StandardBorelSpace (POSystem.ofSCM (dgpSCM m g) (dgpFixed m g)).Ω := by
    change StandardBorelSpace (dgpPO m g).Ω
    exact dgpPO_borel
  haveI : StandardBorelSpace
      (∀ i : Fin (dgpBackdoor m g).cfBundle.n, (dgpBackdoor m g).cfBundle.type i) := by
    haveI : ∀ i : Fin (dgpBackdoor m g).cfBundle.n,
        StandardBorelSpace ((dgpBackdoor m g).cfBundle.type i) := by
      intro i
      dsimp [POBackdoorSystem.cfBundle, POCFBundle.cons, POCFBundle.nil] at i ⊢
      exact Fin.cases (inferInstance : StandardBorelSpace ℝ)
        (fun j => Fin.cases (inferInstance : StandardBorelSpace ℝ)
          (fun k => k.elim0) j) i
    exact StandardBorelSpace.pi_countable
  haveI : Nonempty
      (∀ i : Fin (dgpBackdoor m g).cfBundle.n, (dgpBackdoor m g).cfBundle.type i) := by
    haveI : ∀ i : Fin (dgpBackdoor m g).cfBundle.n,
        Nonempty ((dgpBackdoor m g).cfBundle.type i) := by
      intro i
      dsimp [POBackdoorSystem.cfBundle, POCFBundle.cons, POCFBundle.nil] at i ⊢
      exact Fin.cases (inferInstance : Nonempty ℝ)
        (fun j => Fin.cases (inferInstance : Nonempty ℝ)
          (fun k => k.elim0) j) i
    infer_instance
  have hci :
      (dgpPO m g).CondIndepCF
        (RegimedVar.ofFactual (dgpBackdoor m g).dVar)
        (dgpBackdoor m g).cfBundle c (dgpPO m g).μ := by
    refine POSystem.ofSCM_condIndepCF_of_dSep (M := dgpSCM m g) (s := dgpFixed m g)
      (X := X) (Y := Y) (Z := Z)
      ?hX ?hY ?hZ ?hDisj_XY ?hDisj_XZ ?hDisj_YZ ?hdSep
      (RegimedVar.ofFactual (dgpBackdoor m g).dVar)
      (dgpBackdoor m g).cfBundle c aMap BMap ?haMap ?hBMap ?ha_value ?hB_value ?hc_value
    · intro v hv
      simp [X] at hv
      subst v
      simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]
    · intro v hv
      simp [Y] at hv
      rcases hv with rfl | rfl <;>
        simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]
    · intro v hv
      simp [Z] at hv
      subst v
      simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]
    · decide
    · decide
    · decide
    · change (initialSWIG wDAG).dSep
        ({SWIGNode.random WNode.A} : Finset (SWIGNode WNode))
        ({SWIGNode.random WNode.Ey, SWIGNode.random WNode.Un} : Finset (SWIGNode WNode))
        ({SWIGNode.random WNode.Xc} : Finset (SWIGNode WNode))
      decide
    · dsimp [aMap]
      exact measurable_pi_apply
        (⟨SWIGNode.random WNode.A, by simp [X]⟩ : {w // w ∈ X})
    · refine measurable_pi_lambda _ ?_
      intro i
      fin_cases i
      · dsimp [BMap]
        unfold outFun
        exact Measurable.ite
            (measurableSet_le
            (measurable_pi_apply
              (⟨SWIGNode.random WNode.Ey, by simp [Y]⟩ : {w // w ∈ Y}))
            ((measurable_of_finite (g true)).comp
              (measurable_pi_apply
                (⟨SWIGNode.random WNode.Un, by simp [Y]⟩ : {w // w ∈ Y}))))
          measurable_const measurable_const
      · dsimp [BMap]
        unfold outFun
        exact Measurable.ite
            (measurableSet_le
            (measurable_pi_apply
              (⟨SWIGNode.random WNode.Ey, by simp [Y]⟩ : {w // w ∈ Y}))
            ((measurable_of_finite (g false)).comp
              (measurable_pi_apply
                (⟨SWIGNode.random WNode.Un, by simp [Y]⟩ : {w // w ∈ Y}))))
          measurable_const measurable_const
    · funext ℓ
      change (dgpBackdoor m g).factualD ℓ =
        (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.A, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩
      rw [dgp_factualD_eq_treatFun (m := m) (g := g)]
      symm
      rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.A, by simp [dgpSCM, wSWIGGraph]⟩]
      change treatFun (m ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩))
          (ℓ (iEa (C := C) m g)) =
        treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))
      rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
      unfold dgpSCM parentVal iUn
      rfl
    · funext ℓ i
      dsimp [POCFBundle.jointValue, POBackdoorSystem.cfBundle, POCFBundle.cons,
        POCFBundle.nil, BMap]
      fin_cases i
      · change (dgpBackdoor m g).YofD true ℓ =
          outFun (C := C) g true
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Un, by
                simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩)
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Ey, by
                simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩)
        rw [dgp_YofD_eq_outFun (m := m) (g := g) true]
        rfl
      · change (dgpBackdoor m g).YofD false ℓ =
          outFun (C := C) g false
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Un, by
                simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩)
            ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
              ⟨SWIGNode.random WNode.Ey, by
                simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩)
        rw [dgp_YofD_eq_outFun (m := m) (g := g) false]
        rfl
    · funext ℓ z
      rcases z with ⟨v, hv⟩
      simp [Z] at hv
      subst v
      change (dgpBackdoor m g).factualX ℓ =
        (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩
      rw [dgp_factualX_eq_latentUn (m := m) (g := g)]
      change ℓ (iUn (C := C) m g) =
        (dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩
      rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
        ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
      unfold dgpSCM parentVal iUn
      rfl
  have hc_eq : c.value =
      singletonValues (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc) ∘
        (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value := by
    funext ℓ z
    rcases z with ⟨v, hv⟩
    simp [Z] at hv
    subst v
    rfl
  refine POSystem.condIndepCF_congr_cond ?_ hci
  rw [hc_eq]
  apply le_antisymm
  · have hx_meas :
        @Measurable (dgpPO m g).Ω C
          (MeasurableSpace.comap
            (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value inferInstance)
          inferInstance
          (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value :=
      comap_measurable _
    exact ((measurable_singletonValues (α := swigΩ (WΩ C))
      (v := SWIGNode.random WNode.Xc)).comp hx_meas).comap_le
  · have hsingleton_meas :
        @Measurable (dgpPO m g).Ω
          (ValuesOn ({SWIGNode.random WNode.Xc} : Finset (SWIGNode WNode)) (swigΩ (WΩ C)))
          (MeasurableSpace.comap
            (singletonValues (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc) ∘
              (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value) inferInstance)
          inferInstance
          (singletonValues (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc) ∘
            (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value) :=
      comap_measurable _
    have hx_meas :
        @Measurable (dgpPO m g).Ω C
          (MeasurableSpace.comap
            (singletonValues (α := swigΩ (WΩ C)) (v := SWIGNode.random WNode.Xc) ∘
              (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value) inferInstance)
          inferInstance
          (RegimedVar.ofFactual (dgpBackdoor m g).xVar).value := by
      exact (measurable_singletonValue (α := swigΩ (WΩ C))
        (v := SWIGNode.random WNode.Xc)).comp hsingleton_meas
    exact hx_meas.comap_le

/-- The constructed treatment propensity equals the supplied propensity function
given the covariate.

This follows from the structural treatment assignment using independent unit-interval noise. -/
theorem dgp_propScore_eq_m (hv : ValidDGP m g) :
    (dgpBackdoor m g).propScore true
      =ᵐ[(dgpPO m g).μ] (fun ω => m ((dgpBackdoor m g).factualX ω)) := by
  unfold POBackdoorSystem.propScore
  rw [POBackdoorSystem.sigmaX, dgp_factualX_eq_latentUn (m := m) (g := g),
    dgp_dIndicator_true_eq_threshold (m := m) (g := g)]
  exact dgp_condExp_ea_threshold_var (m := m) (g := g) hv

/-- The constructed adjusted conditional mean equals the supplied outcome regression
in each treatment arm.

Only overlap is needed for the observable ratio defining the adjusted conditional mean. -/
theorem dgp_adjustedCE_eq_g (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1)
    (d : Bool) :
    (dgpBackdoor m g).adjustedCE d
      =ᵐ[(dgpPO m g).μ] (fun ω => g d ((dgpBackdoor m g).factualX ω)) := by
  let S : POBackdoorSystem (dgpPO m g) C := dgpBackdoor m g
  have hY : Integrable S.factualY (dgpPO m g).μ := by
    refine MeasureTheory.Integrable.of_bound S.measurable_factualY.aestronglyMeasurable 1
      (Filter.Eventually.of_forall ?_)
    intro ℓ
    rw [show S.factualY =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          outFun (C := C) g
            (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
            (ℓ (iUn (C := C) m g))
            (ℓ (iEy (C := C) m g))) from
          dgp_factualY_eq_outFun (m := m) (g := g)]
    by_cases h :
        (show ℝ from ℓ (iEy (C := C) m g)) ≤
          g (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
            (ℓ (iUn (C := C) m g))
    · simp [outFun, h]
    · simp [outFun, h]
  have hov :
      ∀ᵐ ω ∂(dgpPO m g).μ,
        0 < S.propScore true ω ∧ S.propScore true ω < 1 := by
    filter_upwards [dgp_propScore_eq_m (m := m) (g := g) hv] with ω hω
    rw [hω]
    exact ⟨(hso _).1, (hso _).2⟩
  have h_ne : ∀ᵐ ω ∂(dgpPO m g).μ, S.propScore d ω ≠ 0 :=
    S.propScore_ne_of_overlap hov d
  have houtcome :
      S.outcomeReg =ᵐ[(dgpPO m g).μ]
        fun ω => g (S.factualD ω) (S.factualX ω) := by
    unfold POBackdoorSystem.outcomeReg POBackdoorSystem.sigmaDX POBackdoorSystem.factualDX
    rw [show S.factualY =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          outFun (C := C) g
            (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
            (ℓ (iUn (C := C) m g))
            (ℓ (iEy (C := C) m g))) from
          dgp_factualY_eq_outFun (m := m) (g := g)]
    rw [show S.factualD =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) from
          dgp_factualD_eq_treatFun (m := m) (g := g)]
    rw [show S.factualX =
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) from
          dgp_factualX_eq_latentUn (m := m) (g := g)]
    exact dgp_condExp_outcome_threshold_var (m := m) (g := g) hv
  have hratio_def :
      S.adjustedCE d
        = S.xVar.condExpRatio
          (fun ω => S.factualY ω * S.dVar.indicator d ω)
          (S.dVar.indicator d) (dgpPO m g).μ := by
    funext ω
    unfold POBackdoorSystem.adjustedCE POBackdoorSystem.propScore
      POBackdoorSystem.sigmaX POBackdoorSystem.factualX POVar.condExpRatio
      POVar.condExpGiven
    rfl
  rw [hratio_def]
  refine S.xVar.condExpRatio_eq_of_mul
    (g := fun ω => S.factualY ω * S.dVar.indicator d ω)
    (h := S.dVar.indicator d)
    (target := fun ω => g d (S.factualX ω)) ?_ ?_
  · let s : Set (dgpPO m g).Ω := S.dVar.event d
    let target : (dgpPO m g).Ω → ℝ := fun ω => g d (S.factualX ω)
    have hsDX : MeasurableSet[S.sigmaDX] s := by
      change MeasurableSet[MeasurableSpace.comap S.factualDX inferInstance]
        (S.factualD ⁻¹' {d})
      exact ⟨Prod.fst ⁻¹' {d}, measurableSet_singleton d |>.preimage measurable_fst, rfl⟩
    have hs : MeasurableSet s := S.dVar.measurableSet_event d (measurableSet_singleton d)
    have hmul_indicator :
        (fun ω => S.factualY ω * S.dVar.indicator d ω) = s.indicator S.factualY := by
      funext ω
      by_cases hω : ω ∈ s
      · have hind : S.dVar.indicator d ω = 1 := S.dVar.indicator_apply_eq_one hω
        rw [hind, mul_one, Set.indicator_of_mem hω]
      · have hD : S.factualD ω ≠ d := hω
        have hind : S.dVar.indicator d ω = 0 := S.dVar.indicator_apply_eq_zero hD
        rw [hind, mul_zero, Set.indicator_of_notMem hω]
    have htarget_meas : Measurable[S.sigmaX] target := by
      have hg_d : Measurable (fun x : C => g d x) := measurable_of_finite _
      change Measurable[MeasurableSpace.comap S.factualX inferInstance]
        ((fun x : C => g d x) ∘ S.factualX)
      exact hg_d.comp (comap_measurable S.factualX)
    have htarget_sm : StronglyMeasurable[S.sigmaX] target :=
      htarget_meas.stronglyMeasurable
    have houtcome_target :
        s.indicator S.outcomeReg =ᵐ[(dgpPO m g).μ] s.indicator target := by
      filter_upwards [houtcome] with ω hω
      by_cases hmem : ω ∈ s
      · have hD : S.factualD ω = d := hmem
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hω, hD]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    have htower :
        (dgpPO m g).μ[s.indicator S.factualY | S.sigmaX]
          =ᵐ[(dgpPO m g).μ] (dgpPO m g).μ[s.indicator S.outcomeReg | S.sigmaX] := by
      simpa [s, POBackdoorSystem.outcomeReg] using
        MeasureTheory.condExp_setIndicator_condExp_of_le
          (μ := (dgpPO m g).μ) (m := S.sigmaX) (m' := S.sigmaDX)
          S.sigmaX_le_sigmaDX S.sigmaDX_le hsDX hY
    have hleft :
        (dgpPO m g).μ[fun ω => S.factualY ω * S.dVar.indicator d ω | S.sigmaX]
          =ᵐ[(dgpPO m g).μ] (dgpPO m g).μ[s.indicator target | S.sigmaX] :=
      (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := (dgpPO m g).μ)
        (Filter.EventuallyEq.of_eq hmul_indicator)).trans
        (htower.trans
          (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := (dgpPO m g).μ)
            houtcome_target))
    have hind_int : Integrable (S.dVar.indicator d) (dgpPO m g).μ :=
      S.dVar.integrable_indicator d (measurableSet_singleton d)
    have htarget_mul_indicator :
        target * S.dVar.indicator d = s.indicator target := by
      funext ω
      by_cases hω : ω ∈ s
      · have hind : S.dVar.indicator d ω = 1 := S.dVar.indicator_apply_eq_one hω
        rw [Pi.mul_apply, hind, mul_one, Set.indicator_of_mem hω]
      · have hD : S.factualD ω ≠ d := hω
        have hind : S.dVar.indicator d ω = 0 := S.dVar.indicator_apply_eq_zero hD
        rw [Pi.mul_apply, hind, mul_zero, Set.indicator_of_notMem hω]
    have htarget_mul_int : Integrable (target * S.dVar.indicator d) (dgpPO m g).μ := by
      rw [htarget_mul_indicator]
      exact (MeasureTheory.Integrable.indicator
        (MeasureTheory.integrable_condExp (μ := (dgpPO m g).μ) (m := S.sigmaDX) (f := S.factualY)) hs)
          |>.congr houtcome_target
    have hpull :
        (dgpPO m g).μ[target * S.dVar.indicator d | S.sigmaX]
          =ᵐ[(dgpPO m g).μ] target * (dgpPO m g).μ[S.dVar.indicator d | S.sigmaX] :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := (dgpPO m g).μ) htarget_sm htarget_mul_int hind_int
    change (dgpPO m g).μ[fun ω => S.factualY ω * S.dVar.indicator d ω | S.sigmaX]
        =ᵐ[(dgpPO m g).μ] (dgpPO m g).μ[S.dVar.indicator d | S.sigmaX] * target
    refine hleft.trans ?_
    refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := (dgpPO m g).μ)
      (Filter.EventuallyEq.of_eq htarget_mul_indicator.symm)).trans ?_
    exact hpull.trans (Filter.EventuallyEq.of_eq (by
      funext ω
      exact mul_comm _ _))
  · have hEq : S.xVar.condExpGiven (S.dVar.indicator d) (dgpPO m g).μ = S.propScore d := by
      unfold POVar.condExpGiven POBackdoorSystem.propScore
        POBackdoorSystem.sigmaX POBackdoorSystem.factualX
      rfl
    rw [hEq]
    exact h_ne

/-- The constructed propensity satisfies overlap whenever the supplied propensity
is strictly between zero and one. -/
theorem dgp_overlap (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂(dgpPO m g).μ,
      0 < (dgpBackdoor m g).propScore true ω ∧
      (dgpBackdoor m g).propScore true ω < 1 := by
  filter_upwards [dgp_propScore_eq_m (m := m) (g := g) hv] with ω hω
  rw [hω]; exact ⟨(hso _).1, (hso _).2⟩

private lemma outFun_norm_le_one (d : Bool) (x : C) (ey : ℝ) :
    ‖outFun (C := C) g d x ey‖ ≤ (1 : ℝ) := by
  unfold outFun
  split_ifs <;> norm_num

@[fun_prop]
private lemma dgp_integrable_YofD (d : Bool) :
    Integrable ((dgpBackdoor m g).YofD d) (dgpPO m g).μ := by
  refine MeasureTheory.Integrable.of_bound
    ((dgpBackdoor m g).measurable_YofD d).aestronglyMeasurable 1
    (Filter.Eventually.of_forall ?_)
  intro ℓ
  rw [dgp_YofD_eq_outFun (m := m) (g := g) d]
  exact outFun_norm_le_one (g := g) d (ℓ (iUn (C := C) m g)) (ℓ (iEy (C := C) m g))

/-- The treated potential outcome is integrable because it is bounded Bernoulli-valued. -/
@[fun_prop]
theorem dgp_integrable_Y1 :
    Integrable ((dgpBackdoor m g).YofD true) (dgpPO m g).μ := by
  exact dgp_integrable_YofD (m := m) (g := g) true

/-- The control potential outcome is integrable because it is bounded Bernoulli-valued. -/
@[fun_prop]
theorem dgp_integrable_Y0 :
    Integrable ((dgpBackdoor m g).YofD false) (dgpPO m g).μ := by
  exact dgp_integrable_YofD (m := m) (g := g) false

/-- The constructed finite backdoor system satisfies the standard backdoor assumptions. -/
theorem dgp_assumptions (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    (dgpBackdoor m g).Assumptions where
  consistency := dgp_consistency
  unconfoundedness := dgp_unconfoundedness
  overlap := dgp_overlap hv hso
  integrable_Y1 := dgp_integrable_Y1
  integrable_Y0 := dgp_integrable_Y0

/-! ## The covariate marginal is uniform -/

/-- The factual covariate marginal of the constructed system is uniform on the
finite covariate space. -/
theorem dgp_P_X_eq_covLaw :
    (dgpPO m g).μ.map (dgpBackdoor m g).factualX = covLaw C := by
  let iUn : {u // u ∈ (dgpSCM m g).unobserved} :=
    ⟨SWIGNode.random WNode.Un, by simp [dgpSCM, wSWIGGraph]⟩
  have hx : (dgpBackdoor m g).factualX =
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ iUn) := by
    funext ℓ
    simp only [POBackdoorSystem.factualX, POVar.factual, POVar.cf]
    change (dgpBackdoor m g).xVar.equiv
        (inducedEval (dgpSCM m g) (dgpFixed m g) Regime.empty ℓ (XIdx m g)) =
      ℓ iUn
    rw [inducedEval_empty_eq_evalMap (dgpSCM m g) (dgpFixed m g) ℓ (XIdx m g)]
    change (XEquiv m g)
        ((dgpSCM m g).evalMap (dgpFixed m g) ℓ
          ⟨SWIGNode.random WNode.Xc, by
            simp [SCM.randomVars, SWIGGraph.randomVars, dgpSCM, wSWIGGraph]⟩) = ℓ iUn
    rw [SCM.evalMap_observed_unfold (dgpSCM m g) (dgpFixed m g) ℓ
      ⟨SWIGNode.random WNode.Xc, by simp [dgpSCM, wSWIGGraph]⟩]
    unfold XEquiv dgpSCM parentVal
    rfl
  rw [hx]
  change Measure.map (Function.eval iUn) (SCM.latentProduct (dgpSCM m g)) = covLaw C
  letI : ∀ u : {u // u ∈ (dgpSCM m g).unobserved},
      IsProbabilityMeasure ((dgpSCM m g).latentDist u) :=
    (dgpSCM m g).isProbability_latent
  haveI : ∀ u : {u // u ∈ (dgpSCM m g).unobserved},
      SigmaFinite ((dgpSCM m g).latentDist u) := fun _ => inferInstance
  rw [SCM.latentProduct, MeasureTheory.Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  change covLaw C = covLaw C
  rfl

/-! ## The estimation system with value-space regressions `(g, m)` -/

/-- For [a finite, nonempty covariate space equipped with a measurable structure whose
singletons are measurable and with a standard Borel structure](hyp:C),
[a propensity function](hyp:m), [an outcome-regression function](hyp:g), [evidence that they
form a valid data-generating process](hyp:hv), and [strict overlap of the propensity at every
covariate value](hyp:hso), [the backdoor estimation system](goal) is the constructed
potential-outcome system equipped with those supplied propensity and outcome-regression functions.

Strict overlap supplies the pointwise positivity and upper-bound fields for the propensity. -/
noncomputable def dgpBES (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    BackdoorEstimationSystem (dgpPO m g) C where
  toPOBackdoorSystem := dgpBackdoor m g
  μ_val := g
  μ_meas := fun _ => measurable_of_finite _
  e_val := m
  e_meas := measurable_of_finite _
  e_pos := fun x => (hso x).1
  e_lt_one := fun x => (hso x).2
  μ_reg_compat := fun d => (dgp_adjustedCE_eq_g hv hso d).symm
  e_compat := dgp_propScore_eq_m hv

/-! ## The bridge -/

/-- **Causal identification bridge.** Suppose [the data-generating process `(m, g)` is
valid](hyp:hv) and satisfies [strict overlap: the propensity `m` lies strictly between `0`
and `1` at every covariate value](hyp:hso). Then [the causal average treatment effect
`E[Y(1) − Y(0)]` of the backdoor potential-outcome system built from `(m, g)` equals the
finite observed-data contrast `ate g = (1/|C|)·Σₓ(g(1,x) − g(0,x))`](goal).

The bridge uses backdoor identification and the uniform covariate marginal, so lower bounds for
the observed-data contrast transfer to the causal estimand. -/
theorem causalATE_eq_ate (hv : ValidDGP m g) (hso : ∀ x, m x ∈ Set.Ioo (0 : ℝ) 1) :
    causalATE m g = ate g := by
  have hθ : (dgpBES (m := m) (g := g) hv hso).θ₀ =
      (dgpBES (m := m) (g := g) hv hso).toPOBackdoorSystem.ATE :=
    (dgpBES (m := m) (g := g) hv hso).θ₀_eq_ATE
      (dgp_assumptions (m := m) (g := g) hv hso)
  -- `causalATE = S.ATE = θ₀ = ∫ (g 1 − g 0) dP_X`, and `P_X = Uniform(C)` turns
  -- the integral into the average `(1/card C) Σ_x (g 1 x − g 0 x) = ate g`.
  rw [causalATE]
  change (dgpBES (m := m) (g := g) hv hso).toPOBackdoorSystem.ATE = ate g
  rw [← hθ]
  unfold BackdoorEstimationSystem.θ₀ BackdoorEstimationSystem.P_X dgpBES
  rw [dgp_P_X_eq_covLaw (m := m) (g := g)]
  unfold covLaw ate
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply]
  calc
    ∑ x, (Fintype.card C : ℝ)⁻¹ * (g true x - g false x)
        = ∑ x, ((Fintype.card C : ℝ)⁻¹ * g true x -
            (Fintype.card C : ℝ)⁻¹ * g false x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = ∑ x, (Fintype.card C : ℝ)⁻¹ * g true x -
          ∑ x, (Fintype.card C : ℝ)⁻¹ * g false x := by
          rw [Finset.sum_sub_distrib]
    _ = (Fintype.card C : ℝ)⁻¹ * ∑ x, g true x -
          (Fintype.card C : ℝ)⁻¹ * ∑ x, g false x := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = (Fintype.card C : ℝ)⁻¹ * (∑ x, g true x - ∑ x, g false x) := by
          ring

end Causalean.Estimation.MinimaxATE.Causal
