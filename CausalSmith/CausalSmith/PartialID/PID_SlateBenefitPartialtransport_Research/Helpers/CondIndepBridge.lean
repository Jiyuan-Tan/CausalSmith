import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Basic
import Causalean.PO.Conditioning.Bundle
import Causalean.PO.Conditioning.EventCondExpBundle
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Singleton conditioning-bundle bridge

This local bridge transports conditional independence given the covariate
variable to the equivalent singleton conditioning bundle.
-/

open MeasureTheory Causalean PO
open scoped ProbabilityTheory

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

/-- Given [the stated hypotheses](hyp:hf,hA,hB), [the conditional real map property holds](goal). -/
lemma conditionalReal_map {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (f : Ω → α) (hf : Measurable f) (A B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    conditionalReal (μ.map f) A B = conditionalReal μ (f ⁻¹' A) (f ⁻¹' B) := by
  unfold conditionalReal
  simp only [Measure.real, Measure.map_apply hf hB,
    Measure.map_apply hf (hA.inter hB), Set.preimage_inter]
  rfl

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {K : ℕ}
variable {P : POSystem} [StandardBorelSpace P.Ω]

/-- The x bundle is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def xBundle (S : POSlateSystem P 𝒳 K) : POCFBundle P :=
  { n := 1
    type := fun _ => 𝒳
    inst := fun _ => inferInstance
    vars := fun _ => RegimedVar.ofFactual S.xVar }

-- @node: sigma_xBundle
/-- [the sigma x bundle property holds](goal). -/
lemma sigma_xBundle (S : POSlateSystem P 𝒳 K) :
    (xBundle S).sigma = MeasurableSpace.comap S.xVar.factual inferInstance := by
  change MeasurableSpace.comap (fun ω (_ : Fin 1) => S.xVar.factual ω) inferInstance =
    MeasurableSpace.comap S.xVar.factual inferInstance
  apply le_antisymm
  · have hf : Measurable[MeasurableSpace.comap S.xVar.factual inferInstance]
        S.xVar.factual := Measurable.of_comap_le le_rfl
    have hg : Measurable (fun x : 𝒳 => fun _ : Fin 1 => x) :=
      measurable_pi_lambda _ (fun _ => measurable_id)
    exact (hg.comp hf).comap_le
  · let tuple : P.Ω → Fin 1 → 𝒳 := fun ω _ => S.xVar.factual ω
    have ht : Measurable[MeasurableSpace.comap tuple inferInstance] tuple :=
      Measurable.of_comap_le le_rfl
    have heval : Measurable (fun f : Fin 1 → 𝒳 => f 0) := measurable_pi_apply 0
    have hc := (heval.comp ht).comap_le
    simpa only [tuple, Function.comp_def] using hc

-- @node: condIndepCFBundle_of_condIndepCF
/-- [the cond indep cf bundle whenever cond indep cf property holds](goal). -/
lemma condIndepCFBundle_of_condIndepCF {α : Type*} [MeasurableSpace α]
    (S : POSlateSystem P 𝒳 K) (a : RegimedVar P α) (B : POCFBundle P)
    (h : P.CondIndepCF a B (RegimedVar.ofFactual S.xVar) P.μ) :
    P.CondIndepCFBundle a B (xBundle S) P.μ := by
  unfold POSystem.CondIndepCFBundle
  unfold POSystem.CondIndepCF at h
  have transport : ∀ (m₁ m₂ : MeasurableSpace P.Ω)
      (hm₁ : m₁ ≤ P.measΩ) (hm₂ : m₂ ≤ P.measΩ),
      m₁ = m₂ →
      ProbabilityTheory.CondIndepFun (mΩ := P.measΩ) m₁ hm₁
        a.value B.jointValue (μ := P.μ) →
      ProbabilityTheory.CondIndepFun (mΩ := P.measΩ) m₂ hm₂
        a.value B.jointValue (μ := P.μ) := by
    intro m₁ m₂ hm₁ hm₂ hm hci
    subst m₂
    exact hci
  apply transport (MeasurableSpace.comap S.xVar.factual inferInstance)
    (xBundle S).sigma S.xVar.measurable_factual.comap_le
    (xBundle S).sigma_le (sigma_xBundle S).symm
  simpa only [RegimedVar.value, RegimedVar.ofFactual, POVar.factual] using h

private lemma measurable_cfBundle_coordinate (S : POSlateSystem P 𝒳 K)
    (i : Fin S.cfBundle.n) :
    Measurable[S.cfBundle.sigma] (S.cfBundle.vars i).value := by
  exact (measurable_pi_apply i).comp S.cfBundle.measurable_jointValue_sigma

/-- [the dof z cf bundle map is measurable](goal). -/
@[fun_prop] lemma measurable_DofZ_cfBundle (S : POSlateSystem P 𝒳 K) (z : Bool) :
    Measurable[S.cfBundle.sigma] (S.DofZ z) := by
  cases z
  · have h := measurable_cfBundle_coordinate S
      ⟨0, by norm_num [POSlateSystem.cfBundle, POCFBundle.cons, POCFBundle.nil]⟩
    change Measurable[S.cfBundle.sigma] (S.DofZ false) at h
    exact h
  · have h := measurable_cfBundle_coordinate S
      ⟨1, by norm_num [POSlateSystem.cfBundle, POCFBundle.cons, POCFBundle.nil]⟩
    change Measurable[S.cfBundle.sigma] (S.DofZ true) at h
    exact h

/-- [the sof d cf bundle map is measurable](goal). -/
@[fun_prop] lemma measurable_SofD_cfBundle (S : POSlateSystem P 𝒳 K) (d : Bool) :
    Measurable[S.cfBundle.sigma] (S.SofD d) := by
  cases d
  · have h := measurable_cfBundle_coordinate S
      ⟨2, by norm_num [POSlateSystem.cfBundle, POCFBundle.cons, POCFBundle.nil]⟩
    change Measurable[S.cfBundle.sigma] (S.SofD false) at h
    exact h
  · have h := measurable_cfBundle_coordinate S
      ⟨3, by norm_num [POSlateSystem.cfBundle, POCFBundle.cons, POCFBundle.nil]⟩
    change Measurable[S.cfBundle.sigma] (S.SofD true) at h
    exact h

/-- [the yof d cf bundle map is measurable](goal). -/
@[fun_prop] lemma measurable_YofD_cfBundle (S : POSlateSystem P 𝒳 K) (d : Bool) :
    Measurable[S.cfBundle.sigma] (S.YofD d) := by
  cases d
  · have h := measurable_cfBundle_coordinate S
      ⟨4, by norm_num [POSlateSystem.cfBundle, POCFBundle.cons, POCFBundle.nil]⟩
    change Measurable[S.cfBundle.sigma] (S.YofD false) at h
    exact h
  · have h := measurable_cfBundle_coordinate S
      ⟨5, by norm_num [POSlateSystem.cfBundle, POCFBundle.cons, POCFBundle.nil]⟩
    change Measurable[S.cfBundle.sigma] (S.YofD true) at h
    exact h

/-- Extract the ordinary probability product identity on a positive finite atom from an a.e. conditional-probability product identity given a finite covariate. Given [the stated hypotheses](hyp:hX,hA,hB,hx,hprod), [the stated conclusion follows](goal). -/
lemma measureReal_inter_atom_mul_of_condExp_inter_eq_mul
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α]
    [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → α) (hX : Measurable X)
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) (x : α)
    (hx : 0 < μ.real (X ⁻¹' {x}))
    (hprod : μ⟦A ∩ B | MeasurableSpace.comap X mα⟧ =ᵐ[μ]
      μ⟦A | MeasurableSpace.comap X mα⟧ *
        μ⟦B | MeasurableSpace.comap X mα⟧) :
    μ.real ((A ∩ B) ∩ X ⁻¹' {x}) * μ.real (X ⁻¹' {x}) =
      μ.real (A ∩ X ⁻¹' {x}) * μ.real (B ∩ X ⁻¹' {x}) := by
  let m := MeasurableSpace.comap X mα
  let C : Set Ω := X ⁻¹' {x}
  have hm : m ≤ mΩ := by
    dsimp [m]
    exact hX.comap_le
  have hC : MeasurableSet[m] C := ⟨{x}, measurableSet_singleton x, rfl⟩
  have hC' : @MeasurableSet Ω mΩ C := hm C hC
  let eA : Ω → ℝ := μ⟦A | m⟧
  let eB : Ω → ℝ := μ⟦B | m⟧
  let eAB : Ω → ℝ := μ⟦A ∩ B | m⟧
  have heA : StronglyMeasurable[m] eA :=
    stronglyMeasurable_condExp (m := m) (μ := μ)
  have heB : StronglyMeasurable[m] eB :=
    stronglyMeasurable_condExp (m := m) (μ := μ)
  have heAB : StronglyMeasurable[m] eAB :=
    stronglyMeasurable_condExp (m := m) (μ := μ)
  have hne : C.Nonempty := by
    by_contra h
    dsimp [C] at h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hx
    simp at hx
  obtain ⟨ω₀, hω₀⟩ := hne
  have hconstA : ∀ ω ∈ C, eA ω = eA ω₀ := by
    intro ω hω
    exact heA.factorsThrough (by simpa [C] using hω.trans hω₀.symm)
  have hconstB : ∀ ω ∈ C, eB ω = eB ω₀ := by
    intro ω hω
    exact heB.factorsThrough (by simpa [C] using hω.trans hω₀.symm)
  have hconstAB : ∀ ω ∈ C, eAB ω = eAB ω₀ := by
    intro ω hω
    exact heAB.factorsThrough (by simpa [C] using hω.trans hω₀.symm)
  have hmul : eAB ω₀ = eA ω₀ * eB ω₀ := by
    have hp : eAB =ᵐ[μ.restrict C] eA * eB :=
      ae_mono Measure.restrict_le_self hprod
    have hi : ∫ ω in C, eAB ω ∂μ = ∫ ω in C, (eA * eB) ω ∂μ :=
      integral_congr_ae hp
    have hl : ∫ ω in C, eAB ω ∂μ = eAB ω₀ * μ.real C := by
      calc
        _ = ∫ _ in C, eAB ω₀ ∂μ := setIntegral_congr_fun hC' hconstAB
        _ = _ := by simp [Measure.real, mul_comm]
    have hr : ∫ ω in C, (eA * eB) ω ∂μ =
        (eA ω₀ * eB ω₀) * μ.real C := by
      calc
        _ = ∫ _ in C, (eA ω₀ * eB ω₀) ∂μ := by
          apply setIntegral_congr_fun hC'
          intro ω hω
          change eA ω * eB ω = eA ω₀ * eB ω₀
          rw [hconstA ω hω, hconstB ω hω]
        _ = _ := by simp [Measure.real, mul_comm]
    have hmass : μ.real C ≠ 0 := ne_of_gt hx
    rw [hl, hr] at hi
    exact (mul_right_cancel₀ hmass hi)
  have hInt (D : Set Ω) (hD : @MeasurableSet Ω mΩ D) :
      (∫ ω in C, (μ⟦D | m⟧) ω ∂μ) = μ.real (D ∩ C) := by
    rw [MeasureTheory.setIntegral_condExp (m := m) (m₀ := mΩ) (μ := μ) hm
      ((integrable_const (1 : ℝ)).indicator hD) hC]
    rw [integral_indicator hD, Measure.restrict_restrict hD]
    simp [Measure.real, Set.inter_comm]
  have hAeq : eA ω₀ * μ.real C = μ.real (A ∩ C) := by
    rw [← hInt A hA]
    calc
      _ = ∫ _ in C, eA ω₀ ∂μ := by simp [Measure.real, mul_comm]
      _ = _ := (setIntegral_congr_fun hC' hconstA).symm
  have hBeq : eB ω₀ * μ.real C = μ.real (B ∩ C) := by
    rw [← hInt B hB]
    calc
      _ = ∫ _ in C, eB ω₀ ∂μ := by simp [Measure.real, mul_comm]
      _ = _ := (setIntegral_congr_fun hC' hconstB).symm
  have hABeq : eAB ω₀ * μ.real C = μ.real ((A ∩ B) ∩ C) := by
    rw [← hInt (A ∩ B) (hA.inter hB)]
    calc
      _ = ∫ _ in C, eAB ω₀ ∂μ := by simp [Measure.real, mul_comm]
      _ = _ := (setIntegral_congr_fun hC' hconstAB).symm
  rw [← hABeq, hmul, ← hAeq, ← hBeq]
  ring

/-- On a positive finite covariate atom, conditional independence converts an observed event under one instrument arm into the corresponding event of the counterfactual bundle. Given [the stated hypotheses](hyp:hCI,hE,hL,hcons,hx,harm), [the stated conclusion follows](goal). -/
lemma conditionalReal_eq_of_condIndepCFBundle
    [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSingletonClass 𝒳]
    (S : POSlateSystem P 𝒳 K) (B : POCFBundle P)
    (hCI : P.CondIndepCFBundle (RegimedVar.ofFactual S.zVar) B (xBundle S) P.μ)
    (z : Bool) (E L : Set P.Ω) (hE : MeasurableSet E)
    (hL : MeasurableSet[MeasurableSpace.comap B.jointValue inferInstance] L)
    (hcons : ∀ᵐ ω ∂P.μ,
      (ω ∈ E ∧ S.factualZ ω = z) ↔ (ω ∈ L ∧ S.factualZ ω = z))
    (x : 𝒳) (hx : 0 < P.μ.real (S.xEvent x))
    (harm : 0 < P.μ.real (S.xEvent x ∩ S.zVar.event z)) :
    conditionalReal P.μ E (S.xEvent x ∩ S.zVar.event z) =
      conditionalReal P.μ L (S.xEvent x) := by
  let Z : Set P.Ω := S.zVar.event z
  let X : Set P.Ω := S.xEvent x
  have hZ : MeasurableSet Z :=
    S.zVar.measurable_factual (measurableSet_singleton z)
  have hL' : MeasurableSet L := B.measurable_jointValue.comap_le L hL
  have hprod :
      P.μ⟦Z ∩ L | MeasurableSpace.comap S.factualX inferInstance⟧ =ᵐ[P.μ]
        P.μ⟦Z | MeasurableSpace.comap S.factualX inferInstance⟧ *
          P.μ⟦L | MeasurableSpace.comap S.factualX inferInstance⟧ := by
    have h := (ProbabilityTheory.condIndepFun_iff
      (m' := (xBundle S).sigma) (hm' := (xBundle S).sigma_le)
      (f := (RegimedVar.ofFactual S.zVar).value) (g := B.jointValue)
      (μ := P.μ) (RegimedVar.measurable_value _) B.measurable_jointValue).mp
        hCI.toCondIndepFun Z L
        (by
          change MeasurableSet[MeasurableSpace.comap S.factualZ inferInstance] Z
          exact ⟨{z}, measurableSet_singleton z, rfl⟩) hL
    simpa [sigma_xBundle, POSlateSystem.factualX, Z, RegimedVar.value,
      RegimedVar.ofFactual, POVar.factual] using h
  have hfactor := measureReal_inter_atom_mul_of_condExp_inter_eq_mul
    P.μ S.factualX S.xVar.measurable_factual Z L hZ hL' x hx hprod
  have hobs : P.μ.real (E ∩ (X ∩ Z)) = P.μ.real ((Z ∩ L) ∩ X) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hcons] with ω hω
    apply propext
    change (ω ∈ E ∩ (X ∩ Z)) ↔ (ω ∈ (Z ∩ L) ∩ X)
    dsimp [X, Z, POSlateSystem.xEvent, POVar.event]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    dsimp [POSlateSystem.factualZ] at hω
    tauto
  unfold conditionalReal
  rw [if_pos harm, if_pos hx]
  have hfactor' :
      P.μ.real ((Z ∩ L) ∩ X) * P.μ.real X =
        P.μ.real (X ∩ Z) * P.μ.real (L ∩ X) := by
    change P.μ.real ((Z ∩ L) ∩ S.factualX ⁻¹' {x}) *
        P.μ.real (S.factualX ⁻¹' {x}) =
      P.μ.real (S.factualX ⁻¹' {x} ∩ Z) *
        P.μ.real (L ∩ S.factualX ⁻¹' {x})
    simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hfactor
  rw [hobs]
  field_simp [ne_of_gt harm, ne_of_gt hx]
  simpa [X, Z, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hfactor'


end CausalSmith.PartialID.SlateBenefitPartialTransport
