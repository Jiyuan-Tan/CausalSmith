/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional-expectation lemmas under `CondIndepFun`

* `condExp_sup_comap_eq_of_condIndep` — drop-of-conditioning: if `g ⟂ f | m`,
  conditioning `h ∘ g` on `m ⊔ σ(f)` equals conditioning on `m` alone.
* `condExp_mul_of_condIndep` — product factorization: `μ[(u∘f)(v∘g)|m] =ᵐ μ[u∘f|m]·μ[v∘g|m]`.

The weak-union, measurable-coordinate extension, and contraction consequences
are proved in `CondExp_Part2.lean`, which imports this module.
-/

module
public import Mathlib.Probability.Independence.Conditional

/-! # Conditional Expectations Under Conditional Independence

This first half proves drop-of-conditioning and product-factorization identities
implied by conditional independence. These identities express how irrelevant
conditioning information can be removed and how conditionally independent factors
separate inside conditional expectations.

The central exported lemmas are `condExp_sup_comap_eq_of_condIndep_comap` and
`condExp_sup_comap_eq_of_condIndep` for removing irrelevant conditioning
variables, `condExp_mul_of_condIndep` for factoring a product's conditional
expectation. `CondExp_Part2.lean` imports this module and adds weak union,
measurable-coordinate extension, and semigraphoid contraction. -/

@[expose] public section

namespace Causalean.Mathlib.Probability.Independence.Conditional
open _root_.MeasureTheory

open scoped MeasureTheory ProbabilityTheory
private def supPiGen {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  generatePiSystem
    ({s : Set Ω | @MeasurableSet Ω m₁ s} ∪ {s : Set Ω | @MeasurableSet Ω m₂ s})

private lemma supPiGen_isPiSystem {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem (supPiGen m₁ m₂) := by
  exact isPiSystem_generatePiSystem _

private lemma sup_eq_generateFrom_supPiGen {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    m₁ ⊔ m₂ = MeasurableSpace.generateFrom (supPiGen m₁ m₂) := by
  rw [supPiGen, generateFrom_generatePiSystem_eq]
  rw [← MeasurableSpace.generateFrom_sup_generateFrom]
  rw [show MeasurableSpace.generateFrom {s : Set Ω | @MeasurableSet Ω m₁ s} = m₁ from
    (@MeasurableSpace.generateFrom_measurableSet Ω m₁)]
  rw [show MeasurableSpace.generateFrom {s : Set Ω | @MeasurableSet Ω m₂ s} = m₂ from
    (@MeasurableSpace.generateFrom_measurableSet Ω m₂)]

private def supRects {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {R | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ A ∩ B = R}

private lemma supRects_isPiSystem {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem (supRects m₁ m₂) := by
  intro R hR Q hQ _hne
  rcases hR with ⟨A₁, B₁, hA₁, hB₁, rfl⟩
  rcases hQ with ⟨A₂, B₂, hA₂, hB₂, rfl⟩
  refine ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, ?_⟩
  ext ω
  simp [and_left_comm, and_assoc]

private lemma supPiGen_subset_rects {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω}
    {t : Set Ω} (ht : t ∈ supPiGen m₁ m₂) :
    ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ A ∩ B = t := by
  change t ∈
    generatePiSystem
      ({s : Set Ω | @MeasurableSet Ω m₁ s} ∪ {s : Set Ω | @MeasurableSet Ω m₂ s}) at ht
  have hsub :
      ({s : Set Ω | @MeasurableSet Ω m₁ s} ∪
          {s : Set Ω | @MeasurableSet Ω m₂ s}) ⊆ supRects m₁ m₂ := by
    intro u hu
    rcases hu with hu | hu
    · exact ⟨u, Set.univ, hu, MeasurableSet.univ, by simp⟩
    · exact ⟨Set.univ, u, MeasurableSet.univ, hu, by simp⟩
  exact generatePiSystem_subset_self (supRects_isPiSystem m₁ m₂) (generatePiSystem_mono hsub ht)

private theorem setIntegral_condExp_indep_indicator_one
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {S A F : Set Ω}
    (hS : MeasurableSet[MeasurableSpace.comap g inferInstance] S)
    (hA : MeasurableSet[m] A)
    (hF : MeasurableSet[MeasurableSpace.comap f inferInstance] F) :
    ∫ x in A ∩ F, (μ⟦S | m⟧) x ∂μ =
      ∫ x in A ∩ F, S.indicator (fun _ : Ω => (1 : ℝ)) x ∂μ := by
  let oneF : Ω → ℝ := F.indicator (fun _ => (1 : ℝ))
  let oneS : Ω → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hS_meas : MeasurableSet S := hg.comap_le S hS
  have hF_meas : MeasurableSet F := hf.comap_le F hF
  have hSF_meas : MeasurableSet (S ∩ F) := hS_meas.inter hF_meas
  have hF_int : MeasureTheory.Integrable oneF μ := by
    refine (MeasureTheory.integrable_indicator_iff hF_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  have hceS_sm : StronglyMeasurable[m] (μ⟦S | m⟧) := by
    exact MeasureTheory.stronglyMeasurable_condExp
  have hceS_bound : ∀ᵐ ω ∂μ, ‖(μ⟦S | m⟧) ω‖ ≤ (1 : ℝ) := by
    have h_nonneg : 0 ≤ᵐ[μ] μ⟦S | m⟧ := by
      refine MeasureTheory.condExp_nonneg (MeasureTheory.ae_of_all μ fun ω => ?_)
      by_cases hω : ω ∈ S <;> simp [hω]
    have h_le_one : μ⟦S | m⟧ ≤ᵐ[μ] (fun _ : Ω => (1 : ℝ)) := by
      have h_ind_le : oneS ≤ᵐ[μ] (fun _ : Ω => (1 : ℝ)) := by
        exact MeasureTheory.ae_of_all μ fun ω => by
          by_cases hω : ω ∈ S <;> simp [oneS, hω]
      have hmono := MeasureTheory.condExp_mono (μ := μ) (m := m)
        (f := oneS) (g := fun _ : Ω => (1 : ℝ)) ?_
        (MeasureTheory.integrable_const (1 : ℝ)) h_ind_le
      · filter_upwards [hmono] with ω hω
        simpa [MeasureTheory.condExp_const hm (1 : ℝ)] using hω
      · refine (MeasureTheory.integrable_indicator_iff hS_meas).2 ?_
        exact MeasureTheory.integrableOn_const
    filter_upwards [h_nonneg, h_le_one] with ω h0 h1
    rw [Real.norm_of_nonneg h0]
    exact h1
  have hprod_int :
      MeasureTheory.Integrable (fun ω => (μ⟦S | m⟧) ω * oneF ω) μ := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
    · exact (hceS_sm.mono hm).aestronglyMeasurable.mul hF_int.aestronglyMeasurable
    · filter_upwards [hceS_bound] with ω hω
      by_cases hωF : ω ∈ F
      · simpa [oneF, hωF, Real.norm_eq_abs] using hω
      · simp [oneF, hωF]
  have hpull :
      μ[fun ω => (μ⟦S | m⟧) ω * oneF ω | m]
        =ᵐ[μ] (μ⟦S | m⟧) * μ[oneF | m] := by
    exact MeasureTheory.condExp_stronglyMeasurable_mul_of_bound hm hceS_sm hF_int 1 hceS_bound
  have hCIsets :
      (μ⟦S ∩ F | m⟧) =ᵐ[μ] (μ⟦S | m⟧) * (μ⟦F | m⟧) := by
    have hCond : ProbabilityTheory.CondIndep m (MeasurableSpace.comap g inferInstance)
        (MeasurableSpace.comap f inferInstance) hm μ := by
      exact (ProbabilityTheory.condIndepFun_iff_condIndep (m' := m) (hm' := hm)
        (f := g) (g := f) (μ := μ)).mp hCI
    exact (ProbabilityTheory.condIndep_iff (m' := m)
      (m₁ := MeasurableSpace.comap g inferInstance)
      (m₂ := MeasurableSpace.comap f inferInstance)
      (hm' := hm) (μ := μ) hg.comap_le hf.comap_le).mp hCond S F hS hF
  have hSF_int :
      MeasureTheory.Integrable ((S ∩ F).indicator (fun _ : Ω => (1 : ℝ))) μ := by
    refine (MeasureTheory.integrable_indicator_iff hSF_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  calc
    ∫ x in A ∩ F, (μ⟦S | m⟧) x ∂μ
        = ∫ x in A, F.indicator (fun x => (μ⟦S | m⟧) x) x ∂μ := by
          rw [MeasureTheory.integral_indicator hF_meas]
          rw [Measure.restrict_restrict hF_meas]
          rw [Set.inter_comm]
    _ = ∫ x in A, (fun ω => (μ⟦S | m⟧) ω * oneF ω) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_fun (hm _ hA) ?_
          intro x _hx
          by_cases hxF : x ∈ F <;> simp [oneF, hxF]
    _ = ∫ x in A, μ[fun ω => (μ⟦S | m⟧) ω * oneF ω | m] x ∂μ := by
          rw [MeasureTheory.setIntegral_condExp hm hprod_int hA]
    _ = ∫ x in A, (fun ω => (μ⟦S | m⟧) ω * (μ⟦F | m⟧) ω) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae (hm _ hA) ?_
          exact hpull.mono fun x hx _ => hx
    _ = ∫ x in A, (μ⟦S ∩ F | m⟧) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae (hm _ hA) ?_
          exact hCIsets.symm.mono fun x hx _ => hx
    _ = ∫ x in A, (S ∩ F).indicator (fun _ : Ω => (1 : ℝ)) x ∂μ := by
          rw [MeasureTheory.setIntegral_condExp (m := m) (m₀ := mΩ) (μ := μ)
            (f := (S ∩ F).indicator (fun _ : Ω => (1 : ℝ))) hm hSF_int hA]
    _ = ∫ x in A, F.indicator oneS x ∂μ := by
          refine MeasureTheory.setIntegral_congr_fun (hm _ hA) ?_
          intro x _hx
          by_cases hxS : x ∈ S <;> by_cases hxF : x ∈ F <;> simp [oneS, hxS, hxF]
    _ = ∫ x in A ∩ F, oneS x ∂μ := by
          rw [MeasureTheory.integral_indicator hF_meas]
          rw [Measure.restrict_restrict hF_meas]
          rw [Set.inter_comm]
    _ = ∫ x in A ∩ F, S.indicator (fun _ : Ω => (1 : ℝ)) x ∂μ := rfl

/-- Under conditional independence of two variables given a σ-algebra, integrating the conditional
expectation of a constant times an event indicator over the intersection of a conditioning event
and an event determined by one variable equals integrating that indicator directly. -/
theorem setIntegral_condExp_indep_indicator
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {S A F : Set Ω}
    (hS : MeasurableSet[MeasurableSpace.comap g inferInstance] S)
    (hA : MeasurableSet[m] A)
    (hF : MeasurableSet[MeasurableSpace.comap f inferInstance] F) (c : ℝ) :
    ∫ x in A ∩ F, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ =
      ∫ x in A ∩ F, S.indicator (fun _ : Ω => c) x ∂μ := by
  let oneS : Ω → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hsmul_fun : (fun ω => c • oneS ω) = S.indicator (fun _ : Ω => c) := by
    ext ω
    by_cases hω : ω ∈ S <;> simp [oneS, hω]
  have hsmul_ae : (fun ω => c • oneS ω) =ᵐ[μ] S.indicator (fun _ : Ω => c) := by
    exact MeasureTheory.ae_of_all μ fun ω => congrFun hsmul_fun ω
  have hce : μ[S.indicator (fun _ : Ω => c) | m]
      =ᵐ[μ] fun ω => c * (μ⟦S | m⟧) ω := by
    have h1 : μ[S.indicator (fun _ : Ω => c) | m]
        =ᵐ[μ] μ[fun ω => c • oneS ω | m] := by
      exact (MeasureTheory.condExp_congr_ae hsmul_ae).symm
    have h2 := MeasureTheory.condExp_smul (μ := μ) (c := c) (f := oneS) (m := m)
    refine h1.trans ?_
    filter_upwards [h2] with ω hω
    exact hω
  calc
    ∫ x in A ∩ F, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ
        = ∫ x in A ∩ F, (fun ω => c * (μ⟦S | m⟧) ω) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae ((hm _ hA).inter (hf.comap_le _ hF)) ?_
          exact hce.mono fun x hx _ => hx
    _ = c * ∫ x in A ∩ F, (μ⟦S | m⟧) x ∂μ := by
          rw [MeasureTheory.integral_const_mul]
    _ = c * ∫ x in A ∩ F, oneS x ∂μ := by
          rw [setIntegral_condExp_indep_indicator_one hm hf hg hCI hS hA hF]
    _ = ∫ x in A ∩ F, (fun ω => c * oneS ω) x ∂μ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ∫ x in A ∩ F, S.indicator (fun _ : Ω => c) x ∂μ := by
          refine MeasureTheory.setIntegral_congr_fun ((hm _ hA).inter (hf.comap_le _ hF)) ?_
          intro x _hx
          simpa [Pi.smul_apply, smul_eq_mul] using congrFun hsmul_fun x

private theorem condExp_indicator_sup_comap_eq_of_condIndep
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {S : Set Ω}
    (hS : MeasurableSet[MeasurableSpace.comap g inferInstance] S) (c : ℝ) :
    μ[S.indicator (fun _ : Ω => c) | m ⊔ MeasurableSpace.comap f inferInstance]
      =ᵐ[μ] μ[S.indicator (fun _ : Ω => c) | m] := by
  let mf : MeasurableSpace Ω := MeasurableSpace.comap f inferInstance
  let M : MeasurableSpace Ω := m ⊔ mf
  have hmM : M ≤ mΩ := by
    dsimp [M, mf]
    exact sup_le hm hf.comap_le
  haveI : MeasureTheory.SigmaFinite (μ.trim hmM) := by infer_instance
  have hS_meas : @MeasurableSet Ω mΩ S := hg.comap_le S hS
  have hY_int : MeasureTheory.Integrable (S.indicator (fun _ : Ω => c)) μ := by
    refine (MeasureTheory.integrable_indicator_iff hS_meas).2 ?_
    exact MeasureTheory.integrableOn_const
  have hce_int : ∀ R, @MeasurableSet Ω M R → μ R < ⊤ →
      MeasureTheory.IntegrableOn (μ[S.indicator (fun _ : Ω => c) | m]) R μ := by
    intro R _hR _hμR
    exact MeasureTheory.integrable_condExp.integrableOn
  have hset : ∀ R, @MeasurableSet Ω M R →
      ∫ x in R, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ =
        ∫ x in R, S.indicator (fun _ : Ω => c) x ∂μ := by
    refine MeasurableSpace.induction_on_inter (m := M)
      (s := supPiGen m (MeasurableSpace.comap f inferInstance))
      (C := fun R _ => ∫ x in R, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ =
        ∫ x in R, S.indicator (fun _ : Ω => c) x ∂μ)
      (h_eq := ?_) (h_inter := ?_) ?empty ?basic ?compl ?iUnion
    · dsimp [M, mf]
      exact sup_eq_generateFrom_supPiGen m (MeasurableSpace.comap f inferInstance)
    · exact supPiGen_isPiSystem m (MeasurableSpace.comap f inferInstance)
    · simp
    · intro R hR
      rcases supPiGen_subset_rects
          (m₁ := m) (m₂ := MeasurableSpace.comap f inferInstance) hR with
        ⟨A, F, hA, hF, hAF⟩
      rw [← hAF]
      exact setIntegral_condExp_indep_indicator hm hf hg hCI hS hA hF c
    · intro R hR hEq
      have hRΩ : @MeasurableSet Ω mΩ R := hmM _ hR
      calc
        ∫ x in Rᶜ, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ
            = ∫ x, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ -
                ∫ x in R, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ := by
              rw [MeasureTheory.setIntegral_compl hRΩ MeasureTheory.integrable_condExp]
        _ = ∫ x, S.indicator (fun _ : Ω => c) x ∂μ -
                ∫ x in R, S.indicator (fun _ : Ω => c) x ∂μ := by
              rw [MeasureTheory.integral_condExp hm, hEq]
        _ = ∫ x in Rᶜ, S.indicator (fun _ : Ω => c) x ∂μ := by
              rw [MeasureTheory.setIntegral_compl hRΩ hY_int]
    · intro Rs hdisj hRs hEq
      have hRsΩ : ∀ i, @MeasurableSet Ω mΩ (Rs i) := fun i => hmM _ (hRs i)
      calc
        ∫ x in ⋃ i, Rs i, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ
            = ∑' i, ∫ x in Rs i, (μ[S.indicator (fun _ : Ω => c) | m]) x ∂μ := by
              rw [MeasureTheory.integral_iUnion hRsΩ hdisj
                MeasureTheory.integrable_condExp.integrableOn]
        _ = ∑' i, ∫ x in Rs i, S.indicator (fun _ : Ω => c) x ∂μ := by
              congr 1
              ext i
              exact hEq i
        _ = ∫ x in ⋃ i, Rs i, S.indicator (fun _ : Ω => c) x ∂μ := by
              rw [MeasureTheory.integral_iUnion hRsΩ hdisj hY_int.integrableOn]
  have hce_sm_M :
      @MeasureTheory.AEStronglyMeasurable Ω ℝ _ M _ (μ[S.indicator (fun _ : Ω => c) | m]) μ := by
    exact ((MeasureTheory.stronglyMeasurable_condExp (m := m) (μ := μ)
      (f := S.indicator (fun _ : Ω => c))).mono (show m ≤ M by
        dsimp [M]
        exact le_sup_left)).aestronglyMeasurable
  have huniq := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hmM hY_int hce_int
    (fun R hR _ => hset R hR) hce_sm_M
  simpa [M, mf] using huniq.symm

/-- If `g` is conditionally independent of `f` given `m`, conditioning a
`σ(g)`-measurable integrable real function on `m ⊔ σ(f)` is the same as
conditioning it on `m`, up to μ-a.e. equality. -/
theorem condExp_sup_comap_eq_of_condIndep_comap
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {Y : Ω → ℝ}
    (hY_meas :
      @Measurable Ω ℝ (MeasurableSpace.comap g inferInstance) _ Y)
    (hY_int : MeasureTheory.Integrable Y μ) :
    μ[Y | m ⊔ MeasurableSpace.comap f inferInstance] =ᵐ[μ] μ[Y | m] := by
  let mf : MeasurableSpace Ω := MeasurableSpace.comap f inferInstance
  let mg : MeasurableSpace Ω := MeasurableSpace.comap g inferInstance
  let M : MeasurableSpace Ω := m ⊔ mf
  have hmM : M ≤ mΩ := by
    dsimp [M, mf]
    exact sup_le hm hf.comap_le
  have hmg : mg ≤ mΩ := by
    dsimp [mg]
    exact hg.comap_le
  haveI : MeasureTheory.SigmaFinite (μ.trim hm) := by infer_instance
  haveI : MeasureTheory.SigmaFinite (μ.trim hmM) := by infer_instance
  haveI : MeasureTheory.SigmaFinite (μ.trim hmg) := by infer_instance
  let T_M : (Ω →₁[μ] ℝ) →L[ℝ] Ω →₁[μ] ℝ :=
    MeasureTheory.condExpL1CLM ℝ hmM μ
  let T_m : (Ω →₁[μ] ℝ) →L[ℝ] Ω →₁[μ] ℝ :=
    MeasureTheory.condExpL1CLM ℝ hm μ
  have hL1 :
      T_M (hY_int.toL1 Y) = T_m (hY_int.toL1 Y) := by
    have hP_ind :
        ∀ (c : ℝ) {s : Set Ω} (hs : MeasurableSet[mg] s) (hμs : μ s < ⊤),
          T_M (@MeasureTheory.Lp.simpleFunc.indicatorConst Ω ℝ mΩ _
              (1 : ENNReal) μ s (hmg s hs) hμs.ne c)
            =
          T_m (@MeasureTheory.Lp.simpleFunc.indicatorConst Ω ℝ mΩ _
              (1 : ENNReal) μ s (hmg s hs) hμs.ne c) := by
      intro c s hs hμs
      have hsΩ : @MeasurableSet Ω mΩ s := hmg s hs
      have hs_int : MeasureTheory.Integrable (s.indicator (fun _ : Ω => c)) μ := by
        refine (MeasureTheory.integrable_indicator_iff (μ := μ) hsΩ).2 ?_
        exact MeasureTheory.integrableOn_const
      have hind_eq :
          @MeasureTheory.Lp.simpleFunc.indicatorConst Ω ℝ mΩ _
              (1 : ENNReal) μ s (hmg s hs) hμs.ne c
            = hs_int.toL1 (s.indicator (fun _ : Ω => c)) := by
        apply MeasureTheory.Lp.ext
        refine (@MeasureTheory.indicatorConstLp_coeFn Ω ℝ mΩ (1 : ENNReal) μ _
          s (hmg s hs) hμs.ne c).trans ?_
        exact hs_int.coeFn_toL1.symm
      rw [hind_eq]
      apply MeasureTheory.Lp.ext
      have hM := MeasureTheory.condExp_ae_eq_condExpL1CLM hmM hs_int
      have hm' := MeasureTheory.condExp_ae_eq_condExpL1CLM hm hs_int
      have hdrop :
          μ[s.indicator (fun _ : Ω => c) | M]
            =ᵐ[μ] μ[s.indicator (fun _ : Ω => c) | m] := by
        dsimp [M, mf]
        exact condExp_indicator_sup_comap_eq_of_condIndep hm hf hg hCI hs c
      exact hM.symm.trans (hdrop.trans hm')
    have hP_add :
        ∀ ⦃u v : Ω → ℝ⦄, ∀ hu : MeasureTheory.MemLp u 1 μ,
          ∀ hv : MeasureTheory.MemLp v 1 μ,
          @StronglyMeasurable Ω ℝ _ mg u →
          @StronglyMeasurable Ω ℝ _ mg v →
          Disjoint (Function.support u) (Function.support v) →
          T_M (hu.toLp u) = T_m (hu.toLp u) →
          T_M (hv.toLp v) = T_m (hv.toLp v) →
          T_M (hu.toLp u + hv.toLp v) = T_m (hu.toLp u + hv.toLp v) := by
      intro u v hu hv _hu_meas _hv_meas _hdisj hu_eq hv_eq
      simp [T_M, T_m, map_add, hu_eq, hv_eq]
    have hP_closed :
        IsClosed {u : @MeasureTheory.lpMeas Ω ℝ ℝ _ _ _ mg mΩ (1 : ENNReal) μ |
          T_M (u : @MeasureTheory.Lp Ω ℝ mΩ _ (1 : ENNReal) μ) =
          T_m (u : @MeasureTheory.Lp Ω ℝ mΩ _ (1 : ENNReal) μ)} := by
      exact isClosed_eq (T_M.continuous.comp continuous_subtype_val)
        (T_m.continuous.comp continuous_subtype_val)
    exact MeasureTheory.Lp.induction_stronglyMeasurable hmg (by norm_num)
      (fun u : Ω →₁[μ] ℝ => T_M u = T_m u) hP_ind hP_add hP_closed
      (hY_int.toL1 Y) (hY_meas.stronglyMeasurable.aestronglyMeasurable.congr
        hY_int.coeFn_toL1.symm)
  have hM := MeasureTheory.condExp_ae_eq_condExpL1CLM hmM hY_int
  have hm' := MeasureTheory.condExp_ae_eq_condExpL1CLM hm hY_int
  have hL1_ae :
      (T_M (hY_int.toL1 Y) : Ω → ℝ) =ᵐ[μ]
        (T_m (hY_int.toL1 Y) : Ω → ℝ) := by
    rw [hL1]
  exact hM.trans (hL1_ae.trans hm'.symm)

/-- If [a conditioning σ-algebra is coarser than the ambient one](hyp:hm), [random elements `f`
and `g` are measurable](hyp:hf,hg), [`g` is conditionally independent of `f` given that
σ-algebra](hyp:hCI), and [a real-valued transform `h` is measurable](hyp:hh) with [`h(g)`
integrable](hyp:hhg), then [adding the information generated by `f` does not change the
conditional expectation of `h(g)`, almost everywhere](goal).

The proof reduces the concrete `h ∘ g` case to the private
`σ(g)`-measurable drop-of-conditioning helper above. -/
theorem condExp_sup_comap_eq_of_condIndep
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm g f μ)
    {h : β → ℝ} (hh : Measurable h)
    (hhg : MeasureTheory.Integrable (fun ω => h (g ω)) μ) :
    μ[fun ω => h (g ω) | m ⊔ MeasurableSpace.comap f inferInstance]
      =ᵐ[μ] μ[fun ω => h (g ω) | m] := by
  have hg_comap :
      @Measurable Ω β (MeasurableSpace.comap g inferInstance) _ g := by
    exact Measurable.of_comap_le le_rfl
  have hY_meas :
      @Measurable Ω ℝ (MeasurableSpace.comap g inferInstance) _ (fun ω => h (g ω)) := by
    exact hh.comp hg_comap
  exact condExp_sup_comap_eq_of_condIndep_comap hm hf hg hCI hY_meas hhg

/-- **Conditional-independence factorization of a product's conditional expectation.** For [a
sub-σ-algebra `m` coarser than the ambient σ-algebra](hyp:hm), [measurable maps `f` and
`g`](hyp:hf,hg) that are [conditionally independent given `m`](hyp:hCI), and [measurable real-valued
functions `u` and `v`](hyp:hu,hv) such that [`u ∘ f`](hyp:huf), [`v ∘ g`](hyp:hvg), and [their
pointwise product](hyp:huv) are all integrable, then [the conditional expectation, given `m`, of the
product `(u ∘ f)·(v ∘ g)` equals the product of the separate conditional expectations of `u ∘ f` and
`v ∘ g` given `m`](goal).

Proof structure:
1. Tower on `m ≤ m ⊔ σ(g)` (via `condExp_condExp_of_le`):
   `μ[uf·vg | m] =ᵐ μ[μ[uf·vg | m ⊔ σ(g)] | m]`.
2. `m ⊔ σ(g)`-pullout of `v ∘ g` (`condExp_mul_of_stronglyMeasurable_right`):
   `μ[uf·vg | m ⊔ σ(g)] =ᵐ μ[uf | m ⊔ σ(g)] · (v ∘ g)`.
3. Drop conditioning with `condExp_sup_comap_eq_of_condIndep` (requires
   `hCI.symm`): `μ[uf | m ⊔ σ(g)] =ᵐ μ[uf | m]`.
4. `m`-pullout of `μ[uf|m]` (`condExp_mul_of_stronglyMeasurable_left`):
   `μ[μ[uf|m] · vg | m] =ᵐ μ[uf|m] · μ[vg | m]`.

Upstream Mathlib candidate, currently complete modulo the drop-of-conditioning
helper above. -/
theorem condExp_mul_of_condIndep
    {Ω α β : Type*}
    {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {f : Ω → α} {g : Ω → β}
    (hf : Measurable f) (hg : Measurable g)
    (hCI : ProbabilityTheory.CondIndepFun m hm f g μ)
    {u : α → ℝ} {v : β → ℝ} (hu : Measurable u) (hv : Measurable v)
    (huf : MeasureTheory.Integrable (fun ω => u (f ω)) μ)
    (hvg : MeasureTheory.Integrable (fun ω => v (g ω)) μ)
    (huv : MeasureTheory.Integrable (fun ω => u (f ω) * v (g ω)) μ) :
    μ[fun ω => u (f ω) * v (g ω) | m]
      =ᵐ[μ] (μ[fun ω => u (f ω) | m]) * (μ[fun ω => v (g ω) | m]) := by
  let mg : MeasurableSpace Ω := m ⊔ MeasurableSpace.comap g inferInstance
  have hm_g : mg ≤ mΩ := by
    dsimp [mg]
    exact sup_le hm hg.comap_le
  haveI : MeasureTheory.IsFiniteMeasure (μ.trim hm_g) :=
    MeasureTheory.isFiniteMeasure_trim hm_g
  haveI : MeasureTheory.SigmaFinite (μ.trim hm_g) := inferInstance
  have hg_mg : @Measurable Ω β mg _ g := by
    exact Measurable.of_comap_le le_sup_right
  have hvg_mg :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ mg (fun ω => v (g ω)) := by
    exact (hv.comp hg_mg).stronglyMeasurable
  have huv' :
      MeasureTheory.Integrable ((fun ω => u (f ω)) * (fun ω => v (g ω))) μ := huv
  have htower :
      μ[fun ω => u (f ω) * v (g ω) | m]
        =ᵐ[μ] μ[μ[fun ω => u (f ω) * v (g ω) | mg] | m] := by
    exact (MeasureTheory.condExp_condExp_of_le
      (f := fun ω => u (f ω) * v (g ω)) (m₁ := m) (m₂ := mg) (m₀ := mΩ)
      le_sup_left hm_g).symm
  have hinner :
      μ[fun ω => u (f ω) * v (g ω) | mg]
        =ᵐ[μ] μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω)) := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_right (m := mg)
      (f := fun ω => u (f ω)) (g := fun ω => v (g ω)) hvg_mg huv' huf
  have hdrop :
      μ[fun ω => u (f ω) | mg] =ᵐ[μ] μ[fun ω => u (f ω) | m] := by
    dsimp [mg]
    exact condExp_sup_comap_eq_of_condIndep hm hg hf hCI hu huf
  have hinner_outer :
      μ[μ[fun ω => u (f ω) * v (g ω) | mg] | m]
        =ᵐ[μ] μ[μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω)) | m] := by
    exact MeasureTheory.condExp_congr_ae hinner
  have hdrop_mul :
      μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω))
        =ᵐ[μ] μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) := by
    exact hdrop.mul (Filter.EventuallyEq.refl (MeasureTheory.ae μ) (fun ω => v (g ω)))
  have hdrop_outer :
      μ[μ[fun ω => u (f ω) | mg] * (fun ω => v (g ω)) | m]
        =ᵐ[μ] μ[μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) | m] := by
    exact MeasureTheory.condExp_congr_ae hdrop_mul
  have hprod_ae :
      μ[fun ω => u (f ω) * v (g ω) | mg]
        =ᵐ[μ] μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) :=
    hinner.trans hdrop_mul
  have hprod_int :
      MeasureTheory.Integrable (μ[fun ω => u (f ω) | m] * (fun ω => v (g ω))) μ := by
    exact (MeasureTheory.integrable_condExp (m := mg)
      (f := fun ω => u (f ω) * v (g ω)) (μ := μ)).congr hprod_ae
  have hce_sm :
      @MeasureTheory.StronglyMeasurable Ω ℝ _ m (μ[fun ω => u (f ω) | m]) := by
    exact MeasureTheory.stronglyMeasurable_condExp
  have hpull :
      μ[μ[fun ω => u (f ω) | m] * (fun ω => v (g ω)) | m]
        =ᵐ[μ] μ[fun ω => u (f ω) | m] * μ[fun ω => v (g ω) | m] := by
    exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := m)
      (f := μ[fun ω => u (f ω) | m]) (g := fun ω => v (g ω))
      hce_sm hprod_int hvg
  exact htower.trans (hinner_outer.trans (hdrop_outer.trans hpull))

end Causalean.Mathlib.Probability.Independence.Conditional
