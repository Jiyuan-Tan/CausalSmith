/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.MinimaxATE.Causal.Bridge_Part1

/-! # Causal Grounding of the Minimax ATE Model: Conditional Expectations

This second part proves the variable-threshold conditional-expectation identities for the
treatment and outcome noises in the constructed backdoor system. The causal assumptions,
backdoor-estimation-system assembly, and final ATE identification are proved in
`Bridge_Part3.lean`. -/

public section

open Causalean.Graph


open Causalean.Mathlib.Probability.Independence

namespace Causalean.Estimation.MinimaxATE.Causal

open Causalean Causalean.PO Causalean.Estimation.ATE
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {C : Type} [Fintype C] [Nonempty C] [MeasurableSpace C]
  [MeasurableSingletonClass C] [StandardBorelSpace C]
variable {m : C → ℝ} {g : Bool → C → ℝ}

/-! ## Carrier regularity instances -/
/-- For [a finite covariate space, propensity function, and outcome regression](hyp:C,m,g), if [they
define a valid data-generating process](hyp:hv), then [the conditional expectation of the treatment-noise
threshold indicator given the latent covariate equals the propensity evaluated at that covariate](goal). -/
lemma dgp_condExp_ea_threshold_var (hv : ValidDGP m g) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      if (show ℝ from ℓ (iEa (C := C) m g)) ≤
          m (show C from ℓ (iUn (C := C) m g)) then (1 : ℝ) else 0 |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iUn (C := C) m g)) inferInstance]
      =ᵐ[(dgpPO m g).μ]
        fun ℓ => m (show C from ℓ (iUn (C := C) m g)) := by
  classical
  let uFun : SCM.LatentValues (dgpSCM m g) → C := fun ℓ => ℓ (iUn (C := C) m g)
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEa (C := C) m g)
  let cell : C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun x ℓ => if uFun ℓ = x then (1 : ℝ) else 0
  let eth : C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun x ℓ => if eFun ℓ ≤ m x then (1 : ℝ) else 0
  let piece : C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun x ℓ => cell x ℓ * eth x ℓ
  have hle_σUn :
      MeasurableSpace.comap uFun inferInstance ≤
        (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [uFun]
    exact (measurable_pi_apply (iUn (C := C) m g)).comap_le
  have hcell_sm : ∀ x, StronglyMeasurable[MeasurableSpace.comap uFun inferInstance] (cell x) := by
    intro x
    have hu_meas :
        @Measurable (SCM.LatentValues (dgpSCM m g)) C
          (MeasurableSpace.comap uFun inferInstance) inferInstance uFun :=
      comap_measurable uFun
    have hs :
        @MeasurableSet (SCM.LatentValues (dgpSCM m g))
          (MeasurableSpace.comap uFun inferInstance)
          {ℓ : SCM.LatentValues (dgpSCM m g) | uFun ℓ = x} :=
      (MeasurableSet.singleton x).preimage hu_meas
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap uFun inferInstance
    exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
  have heth_meas : ∀ x, Measurable (eth x) := by
    intro x
    change @Measurable (SCM.LatentValues (dgpSCM m g)) ℝ
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) inferInstance
      (eth x)
    dsimp [eth, eFun]
    exact Measurable.ite
      (measurableSet_le
        (show Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (show ℝ from ℓ (iEa (C := C) m g))) from
            measurable_pi_apply (iEa (C := C) m g))
        measurable_const)
      measurable_const measurable_const
  have heth_int : ∀ x, Integrable (eth x) (dgpPO m g).μ := by
    intro x
    exact integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) (heth_meas x) fun ℓ => by
      dsimp [eth]
      split_ifs <;> simp
  have hpiece_int : ∀ x, Integrable (piece x) (dgpPO m g).μ := by
    intro x
    refine integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) ?_ ?_
    · change Measurable (piece x)
      exact ((hcell_sm x).mono hle_σUn).measurable.mul (heth_meas x)
    · intro ℓ
      dsimp [piece, cell, eth]
      split_ifs <;> simp
  have hpiece_pull : ∀ x,
      (dgpPO m g).μ[piece x | MeasurableSpace.comap uFun inferInstance]
        =ᵐ[(dgpPO m g).μ] cell x * (fun _ => m x) := by
    intro x
    have hpull :
        (dgpPO m g).μ[piece x | MeasurableSpace.comap uFun inferInstance]
          =ᵐ[(dgpPO m g).μ]
            cell x * (dgpPO m g).μ[eth x | MeasurableSpace.comap uFun inferInstance] := by
      have hmul : piece x = cell x * eth x := rfl
      rw [hmul]
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (μ := (dgpPO m g).μ) (m := MeasurableSpace.comap uFun inferInstance)
        (hcell_sm x) (hpiece_int x) (heth_int x)
    refine hpull.trans ?_
    have hconst :
        (dgpPO m g).μ[eth x | MeasurableSpace.comap uFun inferInstance]
          =ᵐ[(dgpPO m g).μ] fun _ => m x := by
      exact dgp_condExp_ea_threshold_const (m := m) (g := g) x (hv.m_mem x)
    filter_upwards [hconst] with ℓ hℓ
    change cell x ℓ *
        (dgpPO m g).μ[eth x | MeasurableSpace.comap uFun inferInstance] ℓ =
      cell x ℓ * m x
    exact congrArg (fun y => cell x ℓ * y) hℓ
  have hsource :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if eFun ℓ ≤ m (uFun ℓ) then (1 : ℝ) else 0)
        =
      (∑ x : C, piece x) := by
    funext ℓ
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single (uFun ℓ)]
    · dsimp [piece, cell, eth]
      simp
    · intro x _ hx
      have hx' : uFun ℓ ≠ x := fun h => hx h.symm
      dsimp [piece, cell]
      simp [hx']
    · intro hnot
      exact (hnot (Finset.mem_univ (uFun ℓ))).elim
  have htarget :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => m (uFun ℓ)) =
      (∑ x : C, cell x * fun _ : SCM.LatentValues (dgpSCM m g) => m x) := by
    funext ℓ
    simp only [Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_eq_single (uFun ℓ)]
    · dsimp [cell]
      simp
    · intro x _ hx
      have hx' : uFun ℓ ≠ x := fun h => hx h.symm
      dsimp [cell]
      simp [hx']
    · intro hnot
      exact (hnot (Finset.mem_univ (uFun ℓ))).elim
  have hsum :
      (dgpPO m g).μ[(∑ x : C, piece x) | MeasurableSpace.comap uFun inferInstance]
        =ᵐ[(dgpPO m g).μ]
          (∑ x : C, (dgpPO m g).μ[piece x | MeasurableSpace.comap uFun inferInstance]) := by
    simpa using
      (MeasureTheory.condExp_finset_sum
        (μ := (dgpPO m g).μ) (s := (Finset.univ : Finset C))
        (f := piece) (by intro x _; exact hpiece_int x)
        (MeasurableSpace.comap uFun inferInstance))
  refine (MeasureTheory.condExp_congr_ae (μ := (dgpPO m g).μ)
    (m := MeasurableSpace.comap uFun inferInstance)
    (Filter.EventuallyEq.of_eq hsource)).trans ?_
  refine hsum.trans ?_
  refine (eventuallyEq_sum fun x _ => hpiece_pull x).trans ?_
  exact Filter.EventuallyEq.of_eq htarget.symm

private lemma dgp_indep_ey_dx :
    Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEy (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance)
      (dgpPO m g).μ := by
  change Indep
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEy (C := C) m g)) inferInstance)
      (MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance)
      ((dgpSCM m g).latentProduct)
  rw [← IndepFun_iff_Indep]
  change IndepFun
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => ℓ (iEy (C := C) m g))
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
          ℓ (iUn (C := C) m g)))
      (Measure.pi (dgpSCM m g).latentDist)
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  let S : Finset {u // u ∈ (dgpSCM m g).unobserved} := {iEy (C := C) m g}
  let T : Finset {u // u ∈ (dgpSCM m g).unobserved} :=
    {iUn (C := C) m g, iEa (C := C) m g}
  have hdisj : Disjoint S T := by
    simp [S, T, iEy, iUn, iEa]
  have hbase := indepFun_pi_of_disjoint
    (Ω := fun u : {u // u ∈ (dgpSCM m g).unobserved} => swigΩ (WΩ C) u.val)
    (S := S) (T := T)
    (fun u => (dgpSCM m g).latentDist u) hdisj
  let pEy : {u // u ∈ S} := ⟨iEy (C := C) m g, by simp [S]⟩
  let pUn : {u // u ∈ T} := ⟨iUn (C := C) m g, by simp [T]⟩
  let pEa : {u // u ∈ T} := ⟨iEa (C := C) m g, by simp [T]⟩
  let right :
      (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) → Bool × C :=
    fun vals =>
      (treatFun (m (show C from vals pUn)) (show ℝ from vals pEa),
        (show C from vals pUn))
  have hright : Measurable right := by
    have hUn : Measurable (fun vals : (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) =>
        (show C from vals pUn)) := by
      exact measurable_pi_apply pUn
    have hEa : Measurable (fun vals : (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) =>
        (show ℝ from vals pEa)) := by
      exact measurable_pi_apply pEa
    have htreat : Measurable
        (fun vals : (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) =>
          treatFun (m (show C from vals pUn)) (show ℝ from vals pEa)) := by
      show Measurable
        (fun vals : (∀ u : {u // u ∈ T}, swigΩ (WΩ C) u.val) =>
          if (show ℝ from vals pEa) ≤ m (show C from vals pUn) then true else false)
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le hEa ((measurable_of_finite m).comp hUn)
    exact htreat.prodMk hUn
  have hcomp := hbase.comp (measurable_pi_apply pEy) hright
  have h_fintype : Fintype.ofFinite {u // u ∈ (dgpSCM m g).unobserved} =
      Finset.Subtype.fintype (dgpSCM m g).unobserved :=
    Subsingleton.elim _ _
  rw [h_fintype] at hcomp
  exact hcomp

private lemma dgp_integral_ey_threshold (d : Bool) (x : C)
    (ht : g d x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0) ∂(dgpPO m g).μ =
      g d x := by
  change ∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (fun e : ℝ => if e ≤ g d x then (1 : ℝ) else 0) (ℓ (iEy (C := C) m g)) ∂Measure.pi
        (dgpSCM m g).latentDist =
      g d x
  haveI : ∀ i, IsProbabilityMeasure ((dgpSCM m g).latentDist i) :=
    (dgpSCM m g).isProbability_latent
  have hf_meas : Measurable (fun e : ℝ => if e ≤ g d x then (1 : ℝ) else 0) := by
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  rw [← integral_map (μ := Measure.pi (dgpSCM m g).latentDist)
    (f := fun e : ℝ => if e ≤ g d x then (1 : ℝ) else 0)
    (measurable_pi_apply (iEy (C := C) m g)).aemeasurable]
  swap
  · exact hf_meas.aestronglyMeasurable
  rw [Measure.pi_map_eval]
  have hscale : (∏ j ∈ Finset.univ.erase (iEy (C := C) m g),
      ((dgpSCM m g).latentDist j) Set.univ) = 1 := by
    simp
  rw [hscale, one_smul]
  unfold iEy dgpSCM
  change ∫ e, (if e ≤ g d x then (1 : ℝ) else 0) ∂unifLaw = g d x
  exact unifLaw_integral_Iic_indicator (g d x) ht

private lemma dgp_condExp_ey_threshold_const (d : Bool) (x : C)
    (ht : g d x ∈ Set.Icc (0 : ℝ) 1) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0 |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance]
      =ᵐ[(dgpPO m g).μ] fun _ => g d x := by
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEy (C := C) m g)
  let dxFun : SCM.LatentValues (dgpSCM m g) → Bool × C :=
    fun ℓ => (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
      ℓ (iUn (C := C) m g))
  let eInd : SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun ℓ => if eFun ℓ ≤ g d x then (1 : ℝ) else 0
  have he_sm : StronglyMeasurable[MeasurableSpace.comap eFun inferInstance] eInd := by
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap eFun inferInstance
    have he_meas : Measurable eFun := comap_measurable eFun
    have hset : MeasurableSet {ℓ : SCM.LatentValues (dgpSCM m g) | eFun ℓ ≤ g d x} :=
      measurableSet_le he_meas measurable_const
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  have hle_e : MeasurableSpace.comap eFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) := by
    dsimp [eFun]
    exact (measurable_pi_apply (iEy (C := C) m g)).comap_le
  have hdx_meas : Measurable dxFun := by
    dsimp [dxFun]
    have hUn : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show C from ℓ (iUn (C := C) m g))) :=
      measurable_pi_apply (iUn (C := C) m g)
    have hEa : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show ℝ from ℓ (iEa (C := C) m g))) :=
      measurable_pi_apply (iEa (C := C) m g)
    have htreat : Measurable
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) := by
      show Measurable
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          if (show ℝ from ℓ (iEa (C := C) m g)) ≤
            m (show C from ℓ (iUn (C := C) m g)) then true else false)
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le hEa ((measurable_of_finite m).comp hUn)
    exact htreat.prodMk hUn
  have hle_dx : MeasurableSpace.comap dxFun inferInstance ≤
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) :=
    hdx_meas.comap_le
  haveI : IsProbabilityMeasure (dgpPO m g).μ := dgpPO_isProb
  haveI : IsFiniteMeasure (dgpPO m g).μ := inferInstance
  haveI : IsFiniteMeasure ((dgpPO m g).μ.trim hle_dx) :=
    isFiniteMeasure_trim (μ := (dgpPO m g).μ) hle_dx
  have hsig : SigmaFinite ((dgpPO m g).μ.trim hle_dx) :=
    MeasureTheory.IsFiniteMeasure.toSigmaFinite ((dgpPO m g).μ.trim hle_dx)
  have hmain := by
    exact @MeasureTheory.condExp_indep_eq
      (SCM.LatentValues (dgpSCM m g)) ℝ _ _ _
      (MeasurableSpace.comap eFun inferInstance)
      (MeasurableSpace.comap dxFun inferInstance)
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g)))
      ((dgpPO m g).μ) eInd hle_e hle_dx hsig he_sm dgp_indep_ey_dx
  have hmain' :
      (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0 |
        MeasurableSpace.comap
          (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
            (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
              ℓ (iUn (C := C) m g))) inferInstance]
        =ᵐ[(dgpPO m g).μ]
          fun _ => ∫ ℓ : SCM.LatentValues (dgpSCM m g),
            (if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0) ∂(dgpPO m g).μ := by
    exact hmain
  refine hmain'.trans ?_
  exact Filter.Eventually.of_forall fun ℓ => by
    change (∫ ℓ : SCM.LatentValues (dgpSCM m g),
      (if (show ℝ from ℓ (iEy (C := C) m g)) ≤ g d x then (1 : ℝ) else 0) ∂(dgpPO m g).μ) =
      g d x
    exact dgp_integral_ey_threshold (m := m) (g := g) d x ht

/-- For [a finite standard-Borel covariate population, propensity function, and two outcome
regressions](hyp:C,m,g), if [these functions define a valid data-generating process](hyp:hv),
then [the conditional mean of the generated outcome given treatment and covariates equals the
corresponding outcome regression almost surely](goal). -/
lemma dgp_condExp_outcome_threshold_var (hv : ValidDGP m g) :
    (dgpPO m g).μ[fun ℓ : SCM.LatentValues (dgpSCM m g) =>
      outFun (C := C) g
        (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
        (ℓ (iUn (C := C) m g))
        (ℓ (iEy (C := C) m g)) |
      MeasurableSpace.comap
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
            ℓ (iUn (C := C) m g))) inferInstance]
      =ᵐ[(dgpPO m g).μ]
        fun ℓ => g
          (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)))
          (ℓ (iUn (C := C) m g)) := by
  classical
  let dxFun : SCM.LatentValues (dgpSCM m g) → Bool × C :=
    fun ℓ => (treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g)),
      ℓ (iUn (C := C) m g))
  let eFun : SCM.LatentValues (dgpSCM m g) → ℝ := fun ℓ => ℓ (iEy (C := C) m g)
  let cell : Bool × C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun p ℓ => if dxFun ℓ = p then (1 : ℝ) else 0
  let eth : Bool × C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun p ℓ => if eFun ℓ ≤ g p.1 p.2 then (1 : ℝ) else 0
  let piece : Bool × C → SCM.LatentValues (dgpSCM m g) → ℝ :=
    fun p ℓ => cell p ℓ * eth p ℓ
  have hdx_meas : Measurable dxFun := by
    dsimp [dxFun]
    have hUn : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show C from ℓ (iUn (C := C) m g))) :=
      measurable_pi_apply (iUn (C := C) m g)
    have hEa : Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        (show ℝ from ℓ (iEa (C := C) m g))) :=
      measurable_pi_apply (iEa (C := C) m g)
    have htreat : Measurable
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          treatFun (m (ℓ (iUn (C := C) m g))) (ℓ (iEa (C := C) m g))) := by
      show Measurable
        (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          if (show ℝ from ℓ (iEa (C := C) m g)) ≤
            m (show C from ℓ (iUn (C := C) m g)) then true else false)
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le hEa ((measurable_of_finite m).comp hUn)
    exact htreat.prodMk hUn
  have hle_σDX :
      MeasurableSpace.comap dxFun inferInstance ≤
        (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) :=
    hdx_meas.comap_le
  have hcell_sm : ∀ p, StronglyMeasurable[MeasurableSpace.comap dxFun inferInstance] (cell p) := by
    intro p
    have hdx_meas' :
        @Measurable (SCM.LatentValues (dgpSCM m g)) (Bool × C)
          (MeasurableSpace.comap dxFun inferInstance) inferInstance dxFun :=
      comap_measurable dxFun
    have hs :
        @MeasurableSet (SCM.LatentValues (dgpSCM m g))
          (MeasurableSpace.comap dxFun inferInstance)
          {ℓ : SCM.LatentValues (dgpSCM m g) | dxFun ℓ = p} :=
      (MeasurableSet.singleton p).preimage hdx_meas'
    letI : MeasurableSpace (SCM.LatentValues (dgpSCM m g)) :=
      MeasurableSpace.comap dxFun inferInstance
    exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
  have heth_meas : ∀ p, Measurable (eth p) := by
    intro p
    change @Measurable (SCM.LatentValues (dgpSCM m g)) ℝ
      (inferInstance : MeasurableSpace (SCM.LatentValues (dgpSCM m g))) inferInstance
      (eth p)
    dsimp [eth, eFun]
    exact Measurable.ite
      (measurableSet_le
        (show Measurable (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
          (show ℝ from ℓ (iEy (C := C) m g))) from
            measurable_pi_apply (iEy (C := C) m g))
        measurable_const)
      measurable_const measurable_const
  have heth_int : ∀ p, Integrable (eth p) (dgpPO m g).μ := by
    intro p
    exact integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) (heth_meas p) fun ℓ => by
      dsimp [eth]
      split_ifs <;> simp
  have hpiece_int : ∀ p, Integrable (piece p) (dgpPO m g).μ := by
    intro p
    refine integrable_of_measurable_zero_one (μ := (dgpPO m g).μ) ?_ ?_
    · change Measurable (piece p)
      exact ((hcell_sm p).mono hle_σDX).measurable.mul (heth_meas p)
    · intro ℓ
      dsimp [piece, cell, eth]
      split_ifs <;> simp
  have hpiece_pull : ∀ p,
      (dgpPO m g).μ[piece p | MeasurableSpace.comap dxFun inferInstance]
        =ᵐ[(dgpPO m g).μ] cell p * (fun _ => g p.1 p.2) := by
    intro p
    have hpull :
        (dgpPO m g).μ[piece p | MeasurableSpace.comap dxFun inferInstance]
          =ᵐ[(dgpPO m g).μ]
            cell p * (dgpPO m g).μ[eth p | MeasurableSpace.comap dxFun inferInstance] := by
      have hmul : piece p = cell p * eth p := rfl
      rw [hmul]
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (μ := (dgpPO m g).μ) (m := MeasurableSpace.comap dxFun inferInstance)
        (hcell_sm p) (hpiece_int p) (heth_int p)
    refine hpull.trans ?_
    have hconst :
        (dgpPO m g).μ[eth p | MeasurableSpace.comap dxFun inferInstance]
          =ᵐ[(dgpPO m g).μ] fun _ => g p.1 p.2 := by
      exact dgp_condExp_ey_threshold_const (m := m) (g := g) p.1 p.2 (hv.g_mem p.1 p.2)
    filter_upwards [hconst] with ℓ hℓ
    change cell p ℓ *
        (dgpPO m g).μ[eth p | MeasurableSpace.comap dxFun inferInstance] ℓ =
      cell p ℓ * g p.1 p.2
    exact congrArg (fun y => cell p ℓ * y) hℓ
  have hsource :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) =>
        outFun (C := C) g (dxFun ℓ).1 (dxFun ℓ).2 (eFun ℓ))
        =
      (∑ p : Bool × C, piece p) := by
    funext ℓ
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single (dxFun ℓ)]
    · dsimp [piece, cell, eth, outFun]
      simp
    · intro p _ hp
      have hp' : dxFun ℓ ≠ p := fun h => hp h.symm
      dsimp [piece, cell]
      simp [hp']
    · intro hnot
      exact (hnot (Finset.mem_univ (dxFun ℓ))).elim
  have htarget :
      (fun ℓ : SCM.LatentValues (dgpSCM m g) => g (dxFun ℓ).1 (dxFun ℓ).2) =
      (∑ p : Bool × C, cell p * fun _ : SCM.LatentValues (dgpSCM m g) => g p.1 p.2) := by
    funext ℓ
    simp only [Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_eq_single (dxFun ℓ)]
    · dsimp [cell]
      simp
    · intro p _ hp
      have hp' : dxFun ℓ ≠ p := fun h => hp h.symm
      dsimp [cell]
      simp [hp']
    · intro hnot
      exact (hnot (Finset.mem_univ (dxFun ℓ))).elim
  have hsum :
      (dgpPO m g).μ[(∑ p : Bool × C, piece p) | MeasurableSpace.comap dxFun inferInstance]
        =ᵐ[(dgpPO m g).μ]
          (∑ p : Bool × C, (dgpPO m g).μ[piece p | MeasurableSpace.comap dxFun inferInstance]) := by
    simpa using
      (MeasureTheory.condExp_finset_sum
        (μ := (dgpPO m g).μ) (s := (Finset.univ : Finset (Bool × C)))
        (f := piece) (by intro p _; exact hpiece_int p)
        (MeasurableSpace.comap dxFun inferInstance))
  refine (MeasureTheory.condExp_congr_ae (μ := (dgpPO m g).μ)
    (m := MeasurableSpace.comap dxFun inferInstance)
    (Filter.EventuallyEq.of_eq hsource)).trans ?_
  refine hsum.trans ?_
  refine (eventuallyEq_sum fun p _ => hpiece_pull p).trans ?_
  exact Filter.EventuallyEq.of_eq htarget.symm

end Causalean.Estimation.MinimaxATE.Causal
