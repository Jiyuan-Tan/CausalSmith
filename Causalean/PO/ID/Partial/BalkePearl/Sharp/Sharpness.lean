/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: sharpness construction

This file builds the canonical PO model that realises an arbitrary
feasible latent table π for a Balke-Pearl IV system.

Given `(P, S)` and a feasible π, we construct `(P', S')` such that
* `S'.cellProb = S.cellProb`,
* `S'.ATE = BPObjective π`,
* `S'.BaseAssumptions` holds.

The model has
* `V' := Fin 3` (0=Z, 1=D, 2=Y)
* `X' v := Bool` for each v
* `Ω' := Bool × (Bool × Bool × Bool × Bool)` — `(z, d0, d1, y0, y1)`
* `μ' := μ_Z ⊗ π_meas`
* `eval r ω` cascades through `Z → D → Y`, using interventions when their
  target variables are assigned and otherwise reading the latent response type.
-/

module
public import Causalean.PO.ID.Partial.BalkePearl.Sharp.CanonicalModel

/-! # Canonical identities and Balke-Pearl sharpness

This part verifies factual values, exclusion, exogeneity, and marginal identities for the
canonical model, then proves realization of every feasible table and interval value. -/

public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBalkePearlSharp

variable {P : POSystem} (S : POBalkePearlSystem P)

section BaseAssumptions

variable (π : Bool → Bool → Bool → Bool → ℝ)
  (hπ_nn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
  (hπ_sum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      π d0 d1 y0 y1 = 1)

/-! ### Factual values on the canonical model -/

/-- `S'.factualZ ω = ω.1`. -/
lemma canonical_factualZ (ω : SOmega) :
    (S' S π hπ_nn hπ_sum).factualZ ω = ω.1 := by
  change (eval Regime.empty ω ⟨0, by decide⟩) = ω.1
  rw [eval_zero]
  have : (⟨0, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
    rw [Regime.empty_target]; exact Finset.notMem_empty _
  rw [dif_neg this]

/-- `S'.factualD ω = D(ω.1)`. -/
lemma canonical_factualD (ω : SOmega) :
    (S' S π hπ_nn hπ_sum).factualD ω = dArmω ω.1 ω := by
  change (eval Regime.empty ω ⟨1, by decide⟩) = dArmω ω.1 ω
  rw [eval_one]
  have h1nin : (⟨1, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
    rw [Regime.empty_target]; exact Finset.notMem_empty _
  rw [dif_neg h1nin]
  have h0nin : (⟨0, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
    rw [Regime.empty_target]; exact Finset.notMem_empty _
  rw [eval_zero, dif_neg h0nin]

/-- `S'.factualY ω = Y(D(ω.1))`. -/
lemma canonical_factualY (ω : SOmega) :
    (S' S π hπ_nn hπ_sum).factualY ω = yArmω (dArmω ω.1 ω) ω := by
  change (eval Regime.empty ω ⟨2, by decide⟩) = yArmω (dArmω ω.1 ω) ω
  rw [eval_two]
  have h2nin : (⟨2, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
    rw [Regime.empty_target]; exact Finset.notMem_empty _
  rw [dif_neg h2nin]
  have h0nin : (⟨0, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
    rw [Regime.empty_target]; exact Finset.notMem_empty _
  have h1nin : (⟨1, by decide⟩ : SV) ∉ (Regime.empty : Regime SV SX).target := by
    rw [Regime.empty_target]; exact Finset.notMem_empty _
  rw [eval_one, dif_neg h1nin, eval_zero, dif_neg h0nin]

/-- `S'.DofZ z ω = (POBalkePearlSystem.dArm) z ω.2.1 ω.2.2.1`. -/
lemma canonical_DofZ (z : Bool) (ω : SOmega) :
    (S' S π hπ_nn hπ_sum).DofZ z ω
      = POBalkePearlSystem.dArm z ω.2.1 ω.2.2.1 := by
  change (eval (Regime.single (X := SX) ⟨0, by decide⟩ z) ω ⟨1, by decide⟩) = _
  rw [eval_one]
  have h1nin : (⟨1, by decide⟩ : SV) ∉
      (Regime.single (X := SX) (⟨0, by decide⟩ : SV) z).target := by
    rw [Regime.single_target]; intro h
    exact absurd (Finset.mem_singleton.mp h) (by decide)
  have h0in : (⟨0, by decide⟩ : SV) ∈
      (Regime.single (X := SX) (⟨0, by decide⟩ : SV) z).target := by
    rw [Regime.single_target]; exact Finset.mem_singleton_self _
  rw [dif_neg h1nin, eval_zero, dif_pos h0in, Regime.single_assign_self]
  unfold dArmω POBalkePearlSystem.dArm
  cases z <;> rfl

/-- `S'.YofD d ω = (POBalkePearlSystem.yArm) d ω.2.2.2.1 ω.2.2.2.2`. -/
lemma canonical_YofD (d : Bool) (ω : SOmega) :
    (S' S π hπ_nn hπ_sum).YofD d ω
      = POBalkePearlSystem.yArm d ω.2.2.2.1 ω.2.2.2.2 := by
  change (eval (Regime.single (X := SX) ⟨1, by decide⟩ d) ω ⟨2, by decide⟩) = _
  rw [eval_two]
  have h2nin : (⟨2, by decide⟩ : SV) ∉
      (Regime.single (X := SX) (⟨1, by decide⟩ : SV) d).target := by
    rw [Regime.single_target]; intro h
    exact absurd (Finset.mem_singleton.mp h) (by decide)
  have h1in : (⟨1, by decide⟩ : SV) ∈
      (Regime.single (X := SX) (⟨1, by decide⟩ : SV) d).target := by
    rw [Regime.single_target]; exact Finset.mem_singleton_self _
  rw [dif_neg h2nin, eval_one, dif_pos h1in, Regime.single_assign_self]
  unfold yArmω POBalkePearlSystem.yArm
  cases d <;> rfl

/-- `S'.YofZD z d ω = (POBalkePearlSystem.yArm) d ω.2.2.2.1 ω.2.2.2.2`. -/
lemma canonical_YofZD (z d : Bool) (ω : SOmega) :
    (S' S π hπ_nn hπ_sum).YofZD z d ω
      = POBalkePearlSystem.yArm d ω.2.2.2.1 ω.2.2.2.2 := by
  -- Unfold YofZD to show eval at the regimeZD.
  have hZ_eq : (S' S π hπ_nn hπ_sum).Z = (⟨0, by decide⟩ : SV) := rfl
  have hD_eq : (S' S π hπ_nn hπ_sum).D = (⟨1, by decide⟩ : SV) := rfl
  have h2nin : (⟨2, by decide⟩ : SV) ∉ ((S' S π hπ_nn hπ_sum).regimeZD z d).target := by
    unfold POBalkePearlSystem.regimeZD
    rw [Regime.sqcup_target, Regime.single_target, Regime.single_target,
      hZ_eq, hD_eq]
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact absurd (Finset.mem_singleton.mp h) (by decide)
    · exact absurd (Finset.mem_singleton.mp h) (by decide)
  have h1in : (⟨1, by decide⟩ : SV) ∈ ((S' S π hπ_nn hπ_sum).regimeZD z d).target := by
    unfold POBalkePearlSystem.regimeZD
    rw [Regime.sqcup_target]
    refine Finset.mem_union_right _ ?_
    rw [Regime.single_target, hD_eq]
    exact Finset.mem_singleton_self _
  -- The assign for D is `d`.
  have h11 : (⟨1, by decide⟩ : SV) ∉
      (Regime.single (X := SX) (⟨0, by decide⟩ : SV) z).target := by
    rw [Regime.single_target]; intro h
    exact absurd (Finset.mem_singleton.mp h) (by decide)
  have h12 : (⟨1, by decide⟩ : SV) ∈
      (Regime.single (X := SX) (⟨1, by decide⟩ : SV) d).target :=
    Finset.mem_singleton_self _
  have hAssignD :
      ((S' S π hπ_nn hπ_sum).regimeZD z d).assign ⟨1, by decide⟩ h1in = d := by
    change ((Regime.single (X := SX) (⟨0, by decide⟩ : SV) z).sqcup
             (Regime.single (X := SX) (⟨1, by decide⟩ : SV) d) _).assign _ h1in = d
    rw [sqcup_assign_right _ _ _ _ h11 h12 h1in, Regime.single_assign_self]
  change (eval ((S' S π hπ_nn hπ_sum).regimeZD z d) ω ⟨2, by decide⟩) = _
  rw [eval_two_of_not_mem _ _ h2nin, eval_one_of_mem _ _ h1in, hAssignD]
  unfold yArmω POBalkePearlSystem.yArm
  cases d <;> rfl

/-- Exclusion: `Y(z,d) = Y(d)` pointwise (and so a.e.). -/
lemma canonical_exclusion (z d : Bool) :
    (S' S π hπ_nn hπ_sum).YofZD z d =
      (S' S π hπ_nn hπ_sum).YofD d := by
  funext ω
  exact (canonical_YofZD S π hπ_nn hπ_sum z d ω).trans
    (canonical_YofD S π hπ_nn hπ_sum d ω).symm

/-- The Z-event in the canonical model is `{ω | ω.1 = z}`. -/
lemma canonical_zEvent (z : Bool) :
    (S' S π hπ_nn hπ_sum).zEvent z = {ω : SOmega | ω.1 = z} := by
  ext ω
  change (S' S π hπ_nn hπ_sum).factualZ ω = z ↔ ω.1 = z
  exact Iff.of_eq (congrArg (fun t => t = z)
    (canonical_factualZ S π hπ_nn hπ_sum ω))

/-- `μ' (S'.zEvent z) = P.μ (S.zEvent z)`. -/
lemma canonical_zEvent_measure (z : Bool) :
    (P' S π hπ_nn hπ_sum).μ ((S' S π hπ_nn hπ_sum).zEvent z) = P.μ (S.zEvent z) := by
  rw [canonical_zEvent]
  change (canonicalMeasure S π) {ω : SOmega | ω.1 = z} = P.μ (S.zEvent z)
  unfold canonicalMeasure
  -- Use Measure.prod_apply for {ω | ω.1 = z} = {z} ×ˢ Set.univ.
  have hsetEq : {ω : SOmega | ω.1 = z} = {z} ×ˢ (Set.univ : Set (Bool × Bool × Bool × Bool)) := by
    ext ω; simp [Set.mem_prod, Set.mem_singleton_iff]
  letI : IsProbabilityMeasure (piMeasure π) :=
    instIsProbPiMeasure hπ_nn hπ_sum
  rw [hsetEq, Measure.prod_prod]
  -- piMeasure univ = 1
  rw [piMeasure_univ_of_feasible hπ_nn hπ_sum, mul_one]
  -- zMeasure {z} = P.μ (S.zEvent z)
  unfold zMeasure
  rw [Measure.coe_finset_sum]
  simp only [Finset.sum_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- ∑ z' : Bool, P.μ (S.zEvent z') * Measure.dirac z' {z}
  rw [Fintype.sum_bool]
  -- Cases on z.
  cases z
  · simp [Measure.dirac_apply' _ (MeasurableSet.singleton false)]
  · simp [Measure.dirac_apply' _ (MeasurableSet.singleton true)]

/-- Positive Z probability. -/
lemma canonical_posZ (hA : S.BaseAssumptions) (z : Bool) :
    0 < (P' S π hπ_nn hπ_sum).μ ((S' S π hπ_nn hπ_sum).zVar.event z) := by
  change 0 < (P' S π hπ_nn hπ_sum).μ ((S' S π hπ_nn hπ_sum).zEvent z)
  rw [canonical_zEvent_measure]
  exact hA.posZ z

/-! ### Exogeneity: Z ⊥ cfBundle -/

/-- The factualZ on the canonical model factors through `Prod.fst`. -/
lemma canonical_factualZ_eq_fst :
    (S' S π hπ_nn hπ_sum).factualZ = fun ω : SOmega => ω.1 := by
  funext ω; exact canonical_factualZ S π hπ_nn hπ_sum ω

/-- The cfBundle's jointValue factors through `Prod.snd`: it depends only on
the latent factor. -/
lemma canonical_cfBundle_factors_through_snd :
    ∃ g : (Bool × Bool × Bool × Bool) →
        (∀ i : Fin (S' S π hπ_nn hπ_sum).cfBundle.n,
          (S' S π hπ_nn hπ_sum).cfBundle.type i),
      Measurable g ∧
        (S' S π hπ_nn hπ_sum).cfBundle.jointValue =
          (fun ω : SOmega => g ω.2) := by
  refine ⟨fun p i => ?_, ?_, ?_⟩
  · -- The bundle has 4 components: (D(false), D(true), Y(false), Y(true)).
    -- D(z) ω = dArm z ω.2.1 ω.2.2.1; Y(d) ω = yArm d ω.2.2.2.1 ω.2.2.2.2.
    -- We can express the value purely from p = ω.2.
    refine
      i.cases
        (motive := fun i => (S' S π hπ_nn hπ_sum).cfBundle.type i)
        (POBalkePearlSystem.dArm false p.1 p.2.1) ?_
    intro j
    refine
      j.cases
        (motive := fun j => (S' S π hπ_nn hπ_sum).cfBundle.type j.succ)
        (POBalkePearlSystem.dArm true p.1 p.2.1) ?_
    intro k
    refine
      k.cases
        (motive := fun k => (S' S π hπ_nn hπ_sum).cfBundle.type k.succ.succ)
        (POBalkePearlSystem.yArm false p.2.2.1 p.2.2.2) ?_
    intro l
    refine
      l.cases
        (motive := fun l => (S' S π hπ_nn hπ_sum).cfBundle.type l.succ.succ.succ)
        (POBalkePearlSystem.yArm true p.2.2.1 p.2.2.2) ?_
    exact fun m => Fin.elim0 m
  · exact measurable_of_finite _
  · funext ω i
    change (S' S π hπ_nn hπ_sum).cfBundle.jointValue ω i = _
    -- Case split on i : Fin 4.
    fin_cases i
    · -- D(false) ω = dArm false ω.2.1 ω.2.2.1
      exact (canonical_DofZ S π hπ_nn hπ_sum false ω).trans rfl
    · -- D(true) ω = dArm true ω.2.1 ω.2.2.1
      exact (canonical_DofZ S π hπ_nn hπ_sum true ω).trans rfl
    · -- Y(false) ω = yArm false ω.2.2.2.1 ω.2.2.2.2
      exact (canonical_YofD S π hπ_nn hπ_sum false ω).trans rfl
    · -- Y(true) ω = yArm true ω.2.2.2.1 ω.2.2.2.2
      exact (canonical_YofD S π hπ_nn hπ_sum true ω).trans rfl

/-- Exogeneity: Z ⊥ cfBundle under the canonical product measure. -/
lemma canonical_exogeneity :
    (P' S π hπ_nn hπ_sum).IndepCF
      (.ofFactual (S' S π hπ_nn hπ_sum).zVar)
      (S' S π hπ_nn hπ_sum).cfBundle (P' S π hπ_nn hπ_sum).μ := by
  -- Unfold IndepCF to IndepFun.
  unfold POSystem.IndepCF
  -- Pick X = id : Bool → Bool, Y = g (above).
  obtain ⟨g, hg_meas, hg⟩ :=
    canonical_cfBundle_factors_through_snd S π hπ_nn hπ_sum
  -- factualZ = ω.1, cfBundle.jointValue = g ∘ ω.2.
  have hZeq : (RegimedVar.ofFactual (S' S π hπ_nn hπ_sum).zVar).value
      = fun ω : SOmega => ω.1 := by
    funext ω
    change (S' S π hπ_nn hπ_sum).zVar.factual ω = ω.1
    exact canonical_factualZ S π hπ_nn hπ_sum ω
  rw [hZeq, hg]
  -- The product measure independence theorem.
  letI : IsProbabilityMeasure (piMeasure π) :=
    instIsProbPiMeasure hπ_nn hπ_sum
  change IndepFun (fun ω : SOmega => ω.1) (fun ω : SOmega => g ω.2)
    ((zMeasure S).prod (piMeasure π))
  exact ProbabilityTheory.indepFun_prod measurable_id hg_meas

/-- Bundle the canonical model's BaseAssumptions. -/
lemma canonical_baseAssumptions (hA : S.BaseAssumptions) :
    (S' S π hπ_nn hπ_sum).BaseAssumptions where
  consistency_D := by
    intro z ω hω
    rw [canonical_DofZ S π hπ_nn hπ_sum z ω, canonical_factualD S π hπ_nn hπ_sum ω]
    have hz : ω.1 = z := by
      have hset := canonical_zEvent S π hπ_nn hπ_sum z
      change ω ∈ (S' S π hπ_nn hπ_sum).zEvent z at hω
      rw [hset] at hω
      exact hω
    rw [hz]
    unfold dArmω POBalkePearlSystem.dArm
    rfl
  consistency_Y := by
    intro d ω hω
    rw [canonical_YofD S π hπ_nn hπ_sum d ω, canonical_factualY S π hπ_nn hπ_sum ω]
    have hd : dArmω ω.1 ω = d := by
      change (S' S π hπ_nn hπ_sum).factualD ω = d at hω
      rw [canonical_factualD S π hπ_nn hπ_sum ω] at hω
      exact hω
    rw [hd]
    unfold yArmω POBalkePearlSystem.yArm
    rfl
  exclusion   := fun z d => by
    rw [canonical_exclusion]
  exogeneity  := canonical_exogeneity S π hπ_nn hπ_sum
  posZ        := canonical_posZ S π hπ_nn hπ_sum hA

/-! ### Marginal identities -/

/-- `piMeasure π {(d0, d1, y0, y1)} = ENNReal.ofReal (π d0 d1 y0 y1)`. -/
lemma piMeasure_singleton (d0 d1 y0 y1 : Bool) :
    piMeasure π {(d0, d1, y0, y1)} = ENNReal.ofReal (π d0 d1 y0 y1) := by
  unfold piMeasure
  simp only [Measure.coe_finset_sum, Finset.sum_apply]
  have hSing : MeasurableSet ({(d0, d1, y0, y1)} : Set (Bool × Bool × Bool × Bool)) :=
    MeasurableSet.singleton _
  -- Compute each summand: it's the dirac measure scaled by π.
  -- The summand at (d0', d1', y0', y1') = ofReal(π d0' d1' y0' y1') if matches, else 0.
  have hsummand : ∀ (d0' d1' y0' y1' : Bool),
      ((ENNReal.ofReal (π d0' d1' y0' y1') • Measure.dirac (d0', d1', y0', y1') :
          Measure (Bool × Bool × Bool × Bool)) {(d0, d1, y0, y1)})
        = if (d0', d1', y0', y1') = (d0, d1, y0, y1)
            then ENNReal.ofReal (π d0' d1' y0' y1') else 0 := by
    intros d0' d1' y0' y1'
    rw [Measure.smul_apply, Measure.dirac_apply' _ hSing, smul_eq_mul]
    by_cases h : (d0', d1', y0', y1') = (d0, d1, y0, y1)
    · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr h), if_pos h, Pi.one_apply,
        mul_one]
    · rw [Set.indicator_of_notMem
            (by rw [Set.mem_singleton_iff]; exact h),
        if_neg h, mul_zero]
  simp_rw [hsummand]
  -- Now isolate the unique nonzero term.
  rw [Finset.sum_eq_single d0
    (fun d0' _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · rw [Finset.sum_eq_single d1
      (fun d1' _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)]
    · rw [Finset.sum_eq_single y0
        (fun y0' _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)]
      · rw [Finset.sum_eq_single y1
          (fun y1' _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)]
        · simp
        · simp [hne]
      · refine Finset.sum_eq_zero (fun y1' _ => ?_)
        simp [hne]
    · refine Finset.sum_eq_zero (fun y0' _ => ?_)
      refine Finset.sum_eq_zero (fun y1' _ => ?_)
      simp [hne]
  · refine Finset.sum_eq_zero (fun d1' _ => ?_)
    refine Finset.sum_eq_zero (fun y0' _ => ?_)
    refine Finset.sum_eq_zero (fun y1' _ => ?_)
    simp [hne]

/-- The canonical latent set is `Set.univ ×ˢ {(d0, d1, y0, y1)}`. -/
lemma canonical_latentSet (d0 d1 y0 y1 : Bool) :
    (S' S π hπ_nn hπ_sum).latentSet d0 d1 y0 y1
      = (Set.univ ×ˢ {(d0, d1, y0, y1)} : Set SOmega) := by
  ext ω
  rcases ω with ⟨z, d0', d1', y0', y1'⟩
  change ((S' S π hπ_nn hπ_sum).DofZ false (z, d0', d1', y0', y1') = d0 ∧
        (S' S π hπ_nn hπ_sum).DofZ true (z, d0', d1', y0', y1') = d1 ∧
        (S' S π hπ_nn hπ_sum).YofD false (z, d0', d1', y0', y1') = y0 ∧
        (S' S π hπ_nn hπ_sum).YofD true (z, d0', d1', y0', y1') = y1) ↔ _
  rw [canonical_DofZ, canonical_DofZ, canonical_YofD, canonical_YofD]
  change ((POBalkePearlSystem.dArm false d0' d1' = d0) ∧
        (POBalkePearlSystem.dArm true d0' d1' = d1) ∧
        (POBalkePearlSystem.yArm false y0' y1' = y0) ∧
        (POBalkePearlSystem.yArm true y0' y1' = y1)) ↔
      (z, d0', d1', y0', y1') ∈
        (Set.univ ×ˢ {(d0, d1, y0, y1)} : Set SOmega)
  unfold POBalkePearlSystem.dArm POBalkePearlSystem.yArm
  simp only [Bool.false_eq_true, if_false, if_true]
  refine ⟨?_, ?_⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact Set.mk_mem_prod (Set.mem_univ _) rfl
  · rintro ⟨_, h2⟩
    rw [Set.mem_singleton_iff] at h2
    -- h2 : (z, d0', d1', y0', y1').2 = (d0, d1, y0, y1)
    -- Need: conjunction of equalities.
    simp only [Prod.mk.injEq] at h2
    exact h2

/-- `μ'(latentSet) = ENNReal.ofReal (π d0 d1 y0 y1)`. -/
lemma canonical_latentSet_measure (d0 d1 y0 y1 : Bool) :
    (P' S π hπ_nn hπ_sum).μ ((S' S π hπ_nn hπ_sum).latentSet d0 d1 y0 y1)
      = ENNReal.ofReal (π d0 d1 y0 y1) := by
  rw [canonical_latentSet]
  change (canonicalMeasure S π) (Set.univ ×ˢ {(d0, d1, y0, y1)}) = _
  unfold canonicalMeasure
  letI : IsProbabilityMeasure (piMeasure π) :=
    instIsProbPiMeasure hπ_nn hπ_sum
  rw [Measure.prod_prod, zMeasure_univ, one_mul, piMeasure_singleton]

/-- `S'.latentProb = π`. -/
lemma canonical_latentProb_eq (d0 d1 y0 y1 : Bool) :
    (S' S π hπ_nn hπ_sum).latentProb d0 d1 y0 y1 = π d0 d1 y0 y1 := by
  unfold POBalkePearlSystem.latentProb
  rw [canonical_latentSet_measure]
  exact ENNReal.toReal_ofReal (hπ_nn _ _ _ _)

/-- `S'.cellProb y d z = S.cellProb y d z` for any feasible π. -/
lemma canonical_cellProb_eq (hA : S.BaseAssumptions)
    (hπ : POBalkePearlSystem.BPFeasible S hA π) (y d z : Bool) :
    (S' S π hπ_nn hπ_sum).cellProb y d z = S.cellProb y d z := by
  rw [(S' S π hπ_nn hπ_sum).cellProb_eq_sum_latent
        (canonical_baseAssumptions S π hπ_nn hπ_sum hA) y d z, hπ.marginal y d z]
  refine Finset.sum_congr rfl (fun d0 _ => ?_)
  refine Finset.sum_congr rfl (fun d1 _ => ?_)
  refine Finset.sum_congr rfl (fun y0 _ => ?_)
  refine Finset.sum_congr rfl (fun y1 _ => ?_)
  rw [canonical_latentProb_eq]

/-- `S'.ATE = BPObjective π`. -/
lemma canonical_ATE_eq :
    (S' S π hπ_nn hπ_sum).ATE = POBalkePearlSystem.BPObjective π := by
  rw [(S' S π hπ_nn hπ_sum).ATE_eq_BPObjective]
  unfold POBalkePearlSystem.BPObjective
  refine Finset.sum_congr rfl (fun d0 _ => ?_)
  refine Finset.sum_congr rfl (fun d1 _ => ?_)
  refine Finset.sum_congr rfl (fun y0 _ => ?_)
  refine Finset.sum_congr rfl (fun y1 _ => ?_)
  rw [canonical_latentProb_eq]

end BaseAssumptions

end POBalkePearlSharp

/-! ### The sharpness theorem -/

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-- **Sharpness.** Under [the Balke-Pearl IV base assumptions](hyp:hA), for [a latent
treatment-response table `π`](hyp:π) that is [feasible for the linear program —
nonnegative, summing to one, and reproducing the observed cell probabilities as its
marginals](hyp:hπ), [there exists another potential-outcome system, satisfying the same
base assumptions, whose observed cell probabilities agree with the original system's and
whose average treatment effect equals the LP objective value of `π`](goal): every feasible
latent table is realised by some potential-outcome model.

The proof builds the canonical model in `POBalkePearlSharp.canonicalPOSystem`
/ `POBalkePearlSharp.canonicalBP` and verifies its `BaseAssumptions` and
the marginal identities. -/
theorem balkePearl_sharp (hA : S.BaseAssumptions)
    (π : Bool → Bool → Bool → Bool → ℝ) (hπ : BPFeasible S hA π) :
    ∃ (P' : POSystem.{0,0,0}) (S' : POBalkePearlSystem P')
        (_hA' : S'.BaseAssumptions),
      (∀ y d z, S'.cellProb y d z = S.cellProb y d z) ∧
      S'.ATE = BPObjective π := by
  refine ⟨POBalkePearlSharp.canonicalPOSystem S π hπ.nonneg hπ.sum_one,
    POBalkePearlSharp.canonicalBP S π hπ.nonneg hπ.sum_one,
    POBalkePearlSharp.canonical_baseAssumptions S π hπ.nonneg hπ.sum_one hA,
    ?_, ?_⟩
  · intros y d z
    exact POBalkePearlSharp.canonical_cellProb_eq S π hπ.nonneg hπ.sum_one hA hπ y d z
  · exact POBalkePearlSharp.canonical_ATE_eq S π hπ.nonneg hπ.sum_one

/-- **Corollary of sharpness.** Under [the Balke-Pearl IV base assumptions](hyp:hA), for
[a real number `τ` lying in the Balke-Pearl identified interval](hyp:hτ), [there exists
another potential-outcome system, satisfying the same base assumptions, whose observed
cell probabilities agree with the original system's and whose average treatment effect
equals `τ`](goal): every value in the identified interval is the ATE of some BP-feasible
model with matching observed cell probabilities. -/
theorem balkePearl_sharp_of_mem (hA : S.BaseAssumptions)
    (τ : ℝ) (hτ : τ ∈ S.BPIdentifiedInterval hA) :
    ∃ (P' : POSystem.{0,0,0}) (S' : POBalkePearlSystem P')
        (_hA' : S'.BaseAssumptions),
      (∀ y d z, S'.cellProb y d z = S.cellProb y d z) ∧
      S'.ATE = τ := by
  obtain ⟨⟨π, hπ⟩, hτπ⟩ := hτ
  obtain ⟨P', S', hA', hcell, hATE⟩ := S.balkePearl_sharp hA π hπ
  exact ⟨P', S', hA', hcell, by rw [hATE]; exact hτπ⟩

end POBalkePearlSystem

end PO
end Causalean
