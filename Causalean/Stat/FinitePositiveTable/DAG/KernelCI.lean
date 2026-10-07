module
public import Causalean.Stat.FinitePositiveTable.DAG.Elimination
public import Causalean.Stat.FiniteFiberConditioning

/-!
# Finite-kernel conditional independence bridges

This module isolates the graph-independent part of the substrate.  It defines set-valued
conditional independence for a finite kernel, converts Causalean's measure-theoretic
`CondIndepFun` into the corresponding finite-atom cross-product equality, and relates the
set-valued predicate to the existing two-coordinate `KernelCondIndep` API.
-/

@[expose] public section

open Finset

noncomputable section

namespace Causalean.Stat.FinitePositiveTable.DAG

open Causalean.Stat.FinitePositiveTable
open MeasureTheory ProbabilityTheory

universe u uΩ uA uB uC

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}

/-- A [kernel](hyp:q), [fixed and requested random coordinate sets](hyp:fixed,S), and [profile](hyp:x)
determine [the corresponding fixed-row kernel marginal](goal) [as the sum of the kernel over all
complete profiles that agree with the given profile on every fixed and every requested
coordinate](step:1). -/
def fixedKernelMarginal (q : Kernel r) (fixed S : Finset V)
    (x : ProfileSpace r) : ℝ :=
  kernelMarginalMass q (fixed ∪ S) x

/-- A [kernel](hyp:q), [fixed, two random, and conditioning coordinate sets](hyp:fixed,X,Y,Z), and
[profile](hyp:x) determine [the fixed-row atomwise conditional-independence identity](goal):
[the fixed-row marginal over the two random sets and the conditioning set, times the fixed-row
marginal over the conditioning set, equals the product of the fixed-row marginals over each
random set joined with the conditioning set](step:1). -/
def FixedKernelCondIndepAt (q : Kernel r) (fixed X Y Z : Finset V)
    (x : ProfileSpace r) : Prop :=
  fixedKernelMarginal q fixed (X ∪ Y ∪ Z) x *
      fixedKernelMarginal q fixed Z x =
    fixedKernelMarginal q fixed (X ∪ Z) x *
      fixedKernelMarginal q fixed (Y ∪ Z) x

/-- A [kernel](hyp:q) and [fixed, two random, and conditioning coordinate sets](hyp:fixed,X,Y,Z)
determine [fixed-row conditional independence](goal) [by requiring the atomwise identity at
every profile](step:1). -/
def FixedKernelCondIndep (q : Kernel r) (fixed X Y Z : Finset V) : Prop :=
  ∀ x, FixedKernelCondIndepAt q fixed X Y Z x

private noncomputable def finiteComapCondProb
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (mu : Measure Ω) (X : Ω → T) (A : Set Ω) (x : T) : ℝ :=
  (mu.real (X ⁻¹' {x}))⁻¹ * mu.real ((X ⁻¹' {x}) ∩ A)

private lemma finiteComapCondProb_nonneg
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (mu : Measure Ω) (X : Ω → T) (A : Set Ω) (x : T) :
    0 ≤ finiteComapCondProb mu X A x :=
  mul_nonneg (inv_nonneg.mpr measureReal_nonneg) measureReal_nonneg

private lemma finiteComapCondProb_le_one
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (X : Ω → T) (A : Set Ω) (x : T) :
    finiteComapCondProb mu X A x ≤ 1 := by
  unfold finiteComapCondProb
  by_cases hzero : mu.real (X ⁻¹' {x}) = 0
  · simp [hzero]
  · rw [inv_mul_le_one₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm hzero))]
    exact measureReal_mono Set.inter_subset_left

private lemma condExp_indicator_finite_comap_local
    {Ω T : Type*} [Finite T] [MeasurableSpace T]
    [MeasurableSingletonClass T] [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (X : Ω → T) (hX : Measurable X)
    (A : Set Ω) (hA : MeasurableSet A) :
    mu[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap X inferInstance] =ᵐ[mu]
      fun omega => finiteComapCondProb mu X A (X omega) := by
  let _ := Fintype.ofFinite T
  let q : T → ℝ := finiteComapCondProb mu X A
  have hq : Measurable q := measurable_of_finite q
  have hqm : StronglyMeasurable[MeasurableSpace.comap X
      (inferInstance : MeasurableSpace T)] (q ∘ X) :=
    (hq.comp (comap_measurable X)).stronglyMeasurable
  have hqOmega : StronglyMeasurable (q ∘ X) :=
    (hq.comp hX).stronglyMeasurable
  have hq_int : Integrable (q ∘ X) mu := by
    apply Integrable.of_bound hqOmega.aestronglyMeasurable 1
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact (by norm_num : (-1 : ℝ) ≤ 0).trans
        (finiteComapCondProb_nonneg mu X A (X omega))
    · exact finiteComapCondProb_le_one mu X A (X omega)
  have hind : Integrable (A.indicator fun _ => (1 : ℝ)) mu :=
    (integrable_const 1).indicator hA
  have hversion :
      (q ∘ X) =ᵐ[mu]
        mu[A.indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap X (inferInstance : MeasurableSpace T)] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hind
    · intro x _ _
      exact hq_int.integrableOn
    · intro x hx _
      rcases hx with ⟨u, hu, rfl⟩
      classical
      let U : Finset T := Finset.univ.filter (· ∈ u)
      rw [show X ⁻¹' u = ⋃ x ∈ U, X ⁻¹' {x} by
        ext omega
        simp [U]]
      rw [integral_biUnion_finset, integral_biUnion_finset]
      · apply Finset.sum_congr rfl
        intro x hx
        have heq :
            (q ∘ X) =ᵐ[mu.restrict (X ⁻¹' {x})] fun _ => q x := by
          filter_upwards [ae_restrict_mem
            (hX (measurableSet_singleton x))] with omega homega
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at homega
          exact congrArg q homega
        rw [integral_congr_ae heq, integral_const]
        change ((mu.restrict (X ⁻¹' {x})) Set.univ).toReal * q x =
          ∫ y in X ⁻¹' {x}, A.indicator (fun _ => (1 : ℝ)) y ∂mu
        rw [Measure.restrict_apply_univ]
        rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
        unfold q finiteComapCondProb
        change mu.real (X ⁻¹' {x}) *
            ((mu.real (X ⁻¹' {x}))⁻¹ *
              mu.real ((X ⁻¹' {x}) ∩ A)) =
          ((mu.restrict (X ⁻¹' {x})) A).toReal
        rw [Measure.restrict_apply hA, Set.inter_comm A]
        change mu.real (X ⁻¹' {x}) *
            ((mu.real (X ⁻¹' {x}))⁻¹ *
              mu.real ((X ⁻¹' {x}) ∩ A)) =
          mu.real ((X ⁻¹' {x}) ∩ A)
        by_cases hzero : mu.real (X ⁻¹' {x}) = 0
        · have hsub : mu.real ((X ⁻¹' {x}) ∩ A) = 0 :=
            le_antisymm (hzero ▸ measureReal_mono Set.inter_subset_left)
              measureReal_nonneg
          simp [hzero, hsub]
        · field_simp
      · intro x _
        exact hX (measurableSet_singleton x)
      · exact Set.pairwiseDisjoint_fiber X U
      · intro x _
        exact hind.integrableOn
      · intro x _
        exact hX (measurableSet_singleton x)
      · exact Set.pairwiseDisjoint_fiber X U
      · intro x _
        exact hq_int.integrableOn
    · exact hqm.aestronglyMeasurable
  exact hversion.symm

/-- On a standard Borel space with [a finite measure](hyp:mu), let [three random elements with
finite value sets](hyp:f,g,c) be [measurable](hyp:hf,hg,hc), with [the first two conditionally
independent given the third](hyp:hci). Then for [any three values](hyp:a,b,c₀), [the measure of
the event that all three elements take these values, times the measure of the event that the
third takes its value, equals the measure of the event that the first and third take their
values times the measure of the event that the second and third take theirs](goal). -/
theorem condIndepFun_finiteAtom_crossProduct
    {Ω : Type uΩ} {A : Type uA} {B : Type uB} {C : Type uC}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (f : Ω → A) (g : Ω → B) (c : Ω → C)
    (hf : Measurable f) (hg : Measurable g) (hc : Measurable c)
    (hci : CondIndepFun (MeasurableSpace.comap c inferInstance)
      hc.comap_le f g mu)
    (a : A) (b : B) (c₀ : C) :
    mu.real (((f ⁻¹' {a}) ∩ (g ⁻¹' {b})) ∩ (c ⁻¹' {c₀})) *
        mu.real (c ⁻¹' {c₀}) =
      mu.real ((f ⁻¹' {a}) ∩ (c ⁻¹' {c₀})) *
        mu.real ((g ⁻¹' {b}) ∩ (c ⁻¹' {c₀})) := by
  classical
  let F := c ⁻¹' {c₀}
  by_cases hzero : mu.real F = 0
  · have hjoint : mu.real (((f ⁻¹' {a}) ∩ (g ⁻¹' {b})) ∩ F) = 0 :=
      le_antisymm (hzero ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
    have hfiber : mu.real ((f ⁻¹' {a}) ∩ F) = 0 :=
      le_antisymm (hzero ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
    have hgiber : mu.real ((g ⁻¹' {b}) ∩ F) = 0 :=
      le_antisymm (hzero ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
    simpa [F, hzero, hjoint, hfiber, hgiber]
  · have hci_atoms :=
      (condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mp hci
        {a} {b} (measurableSet_singleton a) (measurableSet_singleton b)
    have hjoint := condExp_indicator_finite_comap_local mu c hc
      ((f ⁻¹' {a}) ∩ (g ⁻¹' {b}))
      ((hf (measurableSet_singleton a)).inter (hg (measurableSet_singleton b)))
    have hfiber := condExp_indicator_finite_comap_local mu c hc
      (f ⁻¹' {a}) (hf (measurableSet_singleton a))
    have hgiber := condExp_indicator_finite_comap_local mu c hc
      (g ⁻¹' {b}) (hg (measurableSet_singleton b))
    have hratio : ∀ᵐ omega ∂mu,
        finiteComapCondProb mu c ((f ⁻¹' {a}) ∩ (g ⁻¹' {b})) (c omega) =
          finiteComapCondProb mu c (f ⁻¹' {a}) (c omega) *
            finiteComapCondProb mu c (g ⁻¹' {b}) (c omega) := by
      filter_upwards [hci_atoms, hjoint, hfiber, hgiber] with omega hciω hjω hfω hgω
      exact hjω.symm.trans (hciω.trans (congrArg₂ (· * ·) hfω hgω))
    have hmuF : mu F ≠ 0 := by
      intro hF
      apply hzero
      simp only [Measure.real, hF, ENNReal.toReal_zero]
    have hnebot : (ae (mu.restrict F)).NeBot := ae_restrict_neBot.mpr hmuF
    have hratioF : ∀ᵐ omega ∂mu.restrict F,
        finiteComapCondProb mu c ((f ⁻¹' {a}) ∩ (g ⁻¹' {b})) (c omega) =
          finiteComapCondProb mu c (f ⁻¹' {a}) (c omega) *
            finiteComapCondProb mu c (g ⁻¹' {b}) (c omega) :=
      hratio.filter_mono (@ae_restrict_le Ω _ mu F)
    have hmemF : ∀ᵐ omega ∂mu.restrict F, omega ∈ F :=
      ae_restrict_mem (hc (measurableSet_singleton c₀))
    letI : (ae (mu.restrict F)).NeBot := hnebot
    obtain ⟨omega, hωratio, hωF⟩ := (hratioF.and hmemF).exists
    have hcω : c omega = c₀ := by simpa [F] using hωF
    unfold finiteComapCondProb at hωratio
    simp only [hcω] at hωratio
    change (mu.real F)⁻¹ *
        mu.real (F ∩ ((f ⁻¹' {a}) ∩ (g ⁻¹' {b}))) =
      ((mu.real F)⁻¹ * mu.real (F ∩ (f ⁻¹' {a}))) *
        ((mu.real F)⁻¹ * mu.real (F ∩ (g ⁻¹' {b}))) at hωratio
    field_simp at hωratio
    simpa [F, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc, mul_comm] using hωratio

namespace PositiveDAGTableFactorization

/-- A [kernel](hyp:q), [fixed vertex set](hyp:fixed), [two vertices](hyp:a,b), [proofs that they
are unfixed](hyp:ha,hb), and [proof that they are distinct](hyp:hab) give [the equivalence
between set-valued fixed-row independence and the existing singleton kernel identity](goal). -/
theorem fixedKernelCondIndep_complement_iff_kernelCondIndep
    (q : Kernel r) (fixed : Finset V) (a b : V)
    (ha : a ∉ fixed) (hb : b ∉ fixed) (hab : a ≠ b) :
    FixedKernelCondIndep q fixed {a} {b}
        (((Finset.univ \ fixed).erase a).erase b) ↔
      KernelCondIndep q a b := by
  classical
  let Z := ((Finset.univ \ fixed).erase a).erase b
  have hfull : fixed ∪ ({a} ∪ {b} ∪ Z) = Finset.univ := by
    ext v
    by_cases hva : v = a <;> by_cases hvb : v = b <;>
      by_cases hvf : v ∈ fixed <;> simp_all [Z]
  have hcond : fixed ∪ Z = (Finset.univ.erase a).erase b := by
    ext v
    by_cases hva : v = a <;> by_cases hvb : v = b <;>
      by_cases hvf : v ∈ fixed <;> simp_all [Z]
  have hrow : fixed ∪ ({a} ∪ Z) = Finset.univ.erase b := by
    ext v
    by_cases hva : v = a <;> by_cases hvb : v = b <;>
      by_cases hvf : v ∈ fixed <;> simp_all [Z]
  have hcolumn : fixed ∪ ({b} ∪ Z) = Finset.univ.erase a := by
    ext v
    by_cases hva : v = a <;> by_cases hvb : v = b <;>
      by_cases hvf : v ∈ fixed <;> simp_all [Z]
  have hmass_full (x : ProfileSpace r) :
      kernelMarginalMass q (fixed ∪ ({a} ∪ {b} ∪ Z)) x = q x := by
    rw [hfull, kernelMarginalMass, fiberSum_univ]
  have hmass_row (x : ProfileSpace r) :
      kernelMarginalMass q (fixed ∪ ({a} ∪ Z)) x = coordinateRowMass q b x := by
    rw [hrow]
    unfold coordinateRowMass
    unfold kernelMarginalMass
    rw [← sum_fiberSum_insert_update q (S := Finset.univ.erase b) (v := b)
      (by simp) x]
    simp only [mem_univ, insert_erase, fiberSum_univ]
  have hmass_column (x : ProfileSpace r) :
      kernelMarginalMass q (fixed ∪ ({b} ∪ Z)) x = coordinateColumnMass q a x := by
    rw [hcolumn]
    unfold coordinateColumnMass
    unfold kernelMarginalMass
    rw [← sum_fiberSum_insert_update q (S := Finset.univ.erase a) (v := a)
      (by simp) x]
    simp only [mem_univ, insert_erase, fiberSum_univ]
  have hmass_rectangle (x : ProfileSpace r) :
      kernelMarginalMass q (fixed ∪ Z) x = coordinateRectangleMass q a b x := by
    rw [hcond]
    unfold kernelMarginalMass
    rw [← sum_fiberSum_insert_update q
      (S := (Finset.univ.erase a).erase b) (v := b) (by simp) x]
    have hinsert : insert b ((Finset.univ.erase a).erase b) = Finset.univ.erase a := by
      ext v
      by_cases hva : v = a <;> by_cases hvb : v = b <;> simp_all
    rw [hinsert]
    simp_rw [← sum_fiberSum_insert_update q (S := Finset.univ.erase a) (v := a)
      (by simp) (Function.update x b _)]
    simp only [mem_univ, insert_erase, fiberSum_univ]
    unfold coordinateRectangleMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro zb hzb
    apply Finset.sum_congr rfl
    intro za hza
    rw [Function.update_comm hab.symm]
  unfold FixedKernelCondIndep KernelCondIndep
  constructor <;> intro h x
  · have hx := h x
    unfold FixedKernelCondIndepAt fixedKernelMarginal at hx
    change kernelMarginalMass q (fixed ∪ ({a} ∪ {b} ∪ Z)) x *
        kernelMarginalMass q (fixed ∪ Z) x =
      kernelMarginalMass q (fixed ∪ ({a} ∪ Z)) x *
        kernelMarginalMass q (fixed ∪ ({b} ∪ Z)) x at hx
    unfold KernelCondIndepAt
    rw [hmass_full, hmass_rectangle, hmass_row, hmass_column] at hx
    exact hx
  · unfold KernelCondIndepAt at h
    unfold FixedKernelCondIndepAt fixedKernelMarginal
    rw [hmass_full, hmass_rectangle, hmass_row, hmass_column]
    exact h x

end PositiveDAGTableFactorization

end Causalean.Stat.FinitePositiveTable.DAG
