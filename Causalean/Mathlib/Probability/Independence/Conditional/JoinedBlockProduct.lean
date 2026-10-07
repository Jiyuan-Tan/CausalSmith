module
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockProduct

/-!
# Conditional products on joined training and evaluation blocks

This module factors the conditional expectation of a three-factor product when
each factor may depend on a common training block and one disjoint evaluation
block.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence

namespace Causalean.Mathlib.Probability.Independence.Conditional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, StandardBorelSpace (Ω i)]

/-- [The training block](hyp:B0), [the three evaluation blocks](hyp:B), and
[one joined-view score for each factor](hyp:η) define [the product of the three
joined-view scores](goal), [by evaluating every score on its training-plus-evaluation
coordinates and multiplying the resulting values](step:1). -/
noncomputable def joinedBlockProduct (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (η : (t : Fin 3) → ((i : {i // i ∈ B0 ∪ B t}) → Ω i.val) → ℝ) :
    (∀ i, Ω i) → ℝ :=
  fun x => ∏ t : Fin 3, η t (finsetCoordProj (B0 ∪ B t) x)

/-- [A finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain) and [pairwise
evaluation disjointness](hyp:heval), [measurable joined-view scores](hyp:η,hηmeas),
[integrable individual scores](hyp:hη), [an integrable first two-factor product](hyp:hη01),
and [an integrable three-factor product](hyp:hηprod) imply that [the conditional mean
of the joined three-block product given the training block is almost surely the product of the
three scores' conditional means given the training block](goal). -/
theorem condExp_joinedBlockProduct_of_integrable
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (η : (t : Fin 3) → ((i : {i // i ∈ B0 ∪ B t}) → Ω i.val) → ℝ)
    (hηmeas : ∀ t, Measurable (η t))
    (hη : ∀ t, Integrable
      (fun x : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) x)) (Measure.pi μ))
    (hη01 : Integrable (fun x : ∀ i, Ω i =>
      η 0 (finsetCoordProj (B0 ∪ B 0) x) *
      η 1 (finsetCoordProj (B0 ∪ B 1) x)) (Measure.pi μ))
    (hηprod : Integrable (joinedBlockProduct B0 B η) (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (joinedBlockProduct B0 B η) =ᵐ[Measure.pi μ]
    (fun x => ∏ t : Fin 3,
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ)
        (fun y : ∀ i, Ω i => η t (finsetCoordProj (B0 ∪ B t) y)) x) := by
  classical
  have _htrain := htrain
  let S01 := (B0 ∪ B 0) ∪ (B0 ∪ B 1)
  have hm : MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance ≤
      (inferInstance : MeasurableSpace (∀ i, Ω i)) :=
    Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) B0)
  have hF : (Fintype.ofFinite ι) = (inferInstance : Fintype ι) :=
    Subsingleton.elim _ _
  have hpi : @Measure.pi ι Ω (Fintype.ofFinite ι) _ μ = Measure.pi μ :=
    congrArg (fun fi : Fintype ι => @Measure.pi ι Ω fi _ μ) hF
  have hinter01 : (B0 ∪ B 0) ∩ (B0 ∪ B 1) ⊆ B0 := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hleft, hright⟩
    rcases Finset.mem_union.mp hleft with h0 | h0
    · exact h0
    rcases Finset.mem_union.mp hright with h1 | h1
    · exact h1
    exact False.elim ((Finset.disjoint_left.mp (heval (by decide : (0 : Fin 3) ≠ 1))) h0 h1)
  have hinter012 : S01 ∩ (B0 ∪ B 2) ⊆ B0 := by
    intro i hi
    rcases Finset.mem_inter.mp hi with ⟨hleft, hright⟩
    rcases Finset.mem_union.mp hright with h0 | h2
    · exact h0
    rcases Finset.mem_union.mp hleft with hleft | hleft
    · rcases Finset.mem_union.mp hleft with h0 | h0
      · exact h0
      exact False.elim ((Finset.disjoint_left.mp (heval (by decide : (0 : Fin 3) ≠ 2))) h0 h2)
    · rcases Finset.mem_union.mp hleft with h0 | h1
      · exact h0
      exact False.elim ((Finset.disjoint_left.mp (heval (by decide : (1 : Fin 3) ≠ 2))) h1 h2)
  have hCI01 : CondIndepFun
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance) hm
      (finsetCoordProj (Ω := Ω) (B0 ∪ B 0))
      (finsetCoordProj (Ω := Ω) (B0 ∪ B 1)) (Measure.pi μ) := by
    simpa only [hpi] using
      (condIndepFun_pi_of_inter_subset (Ω := Ω) μ hinter01)
  have hCI012 : CondIndepFun
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance) hm
      (finsetCoordProj (Ω := Ω) S01)
      (finsetCoordProj (Ω := Ω) (B0 ∪ B 2)) (Measure.pi μ) := by
    simpa only [hpi] using
      (condIndepFun_pi_of_inter_subset (Ω := Ω) μ hinter012)
  have h01 :=
    Causalean.Mathlib.Probability.Independence.Conditional.condExp_mul_of_condIndep
      (μ := Measure.pi μ) hm
      (measurable_finsetCoordProj (Ω := Ω) (B0 ∪ B 0))
      (measurable_finsetCoordProj (Ω := Ω) (B0 ∪ B 1))
      hCI01 (hηmeas 0) (hηmeas 1) (hη 0) (hη 1) hη01
  let F : ((i : {i // i ∈ S01}) → Ω i.val) → ℝ :=
    fun y =>
      η 0 (fun i => y ⟨i.val, Finset.mem_union.mpr
        (Or.inl i.property)⟩) *
      η 1 (fun i => y ⟨i.val, Finset.mem_union.mpr
        (Or.inr i.property)⟩)
  have hFmeas : Measurable F := by
    dsimp [F]
    apply Measurable.mul
    · exact (hηmeas 0).comp
        (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    · exact (hηmeas 1).comp
        (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  have hFint : Integrable (fun x => F (finsetCoordProj S01 x)) (Measure.pi μ) := by
    convert hη01 using 1
    ext x
    rfl
  have hprod : Integrable (fun x =>
      F (finsetCoordProj S01 x) * η 2 (finsetCoordProj (B0 ∪ B 2) x))
      (Measure.pi μ) := by
    convert hηprod using 1
    ext x
    simp only [joinedBlockProduct, Fin.prod_univ_three]
    rfl
  have hstep2 :=
    Causalean.Mathlib.Probability.Independence.Conditional.condExp_mul_of_condIndep
      (μ := Measure.pi μ) hm
      (measurable_finsetCoordProj (Ω := Ω) S01)
      (measurable_finsetCoordProj (Ω := Ω) (B0 ∪ B 2))
      hCI012 hFmeas (hηmeas 2) hFint (hη 2) hprod
  have hfun : (fun x : ∀ i, Ω i =>
      F (finsetCoordProj S01 x) * η 2 (finsetCoordProj (B0 ∪ B 2) x)) =
      joinedBlockProduct B0 B η := by
    funext x
    simp only [joinedBlockProduct, Fin.prod_univ_three]
    rfl
  have hfun01 : (fun x : ∀ i, Ω i => F (finsetCoordProj S01 x)) =
      (fun x => η 0 (finsetCoordProj (B0 ∪ B 0) x) *
        η 1 (finsetCoordProj (B0 ∪ B 1) x)) := by
    funext x
    rfl
  rw [hfun, hfun01] at hstep2
  have hfinal := hstep2.trans (h01.mul
    (Filter.EventuallyEq.refl (ae (Measure.pi μ)) _))
  filter_upwards [hfinal] with x hx
  simpa [Fin.prod_univ_three] using hx

end Causalean.Mathlib.Probability.Independence.Conditional
