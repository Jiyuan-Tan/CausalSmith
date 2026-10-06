module
public import Causalean.Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Covariance

/-!
# Conditional products on three held-out blocks

This module packages conditional independence, moment bounds, factorization,
centering, and covariance identities for products of scores evaluated on three
pairwise-disjoint coordinate blocks of a finite product experiment, conditional
on a fourth training block.  It is built from the library's binary conditional
independence and conditional-expectation factorization interfaces.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence

namespace Causalean.Mathlib.Probability.Independence.Conditional

variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, StandardBorelSpace (Ω i)]
variable (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- For [a finite product probability law](hyp:μ), a [training block and three evaluation
blocks](hyp:B0,B) whose [training and evaluation blocks are disjoint](hyp:htrain) and whose
[evaluation blocks are pairwise disjoint](hyp:heval), [the views indexed by two distinct
evaluation blocks](hyp:s,t,hst) satisfy [conditional independence given the training view](goal). -/
theorem condIndepFun_eval_pair (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 =>
      Disjoint (B s) (B t)))
    (s t : Fin 3) (hst : s ≠ t) :
    CondIndepFun
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) B0))
      (finsetCoordProj (Ω := Ω) (B s))
      (finsetCoordProj (Ω := Ω) (B t))
      (Measure.pi μ) := by
  classical
  have _htrain := htrain
  have hinter : B s ∩ B t ⊆ B0 := by
    rw [Finset.disjoint_iff_inter_eq_empty.mp (heval hst)]
    exact Finset.empty_subset B0
  have h := condIndepFun_pi_of_inter_subset (Ω := Ω) μ hinter
  have hF : (Fintype.ofFinite ι) = (inferInstance : Fintype ι) :=
    Subsingleton.elim _ _
  have hpi : @Measure.pi ι Ω (Fintype.ofFinite ι) _ μ = Measure.pi μ :=
    congrArg (fun fi : Fintype ι => @Measure.pi ι Ω fi _ μ) hF
  simpa only [hpi] using h

/-- For [a finite product probability law](hyp:μ), a [training block and three evaluation
blocks](hyp:B0,B) whose [training and evaluation blocks are disjoint](hyp:htrain) and whose
[evaluation blocks are pairwise disjoint](hyp:heval), [the combined first two evaluation views
are conditionally independent of the third given the training view](goal). -/
theorem condIndepFun_eval_union (B0 : Finset ι) (B : Fin 3 → Finset ι)
    [DecidableEq ι]
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t))) :
    CondIndepFun
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) B0))
      (finsetCoordProj (Ω := Ω) (B 0 ∪ B 1))
      (finsetCoordProj (Ω := Ω) (B 2))
      (Measure.pi μ) := by
  classical
  have _htrain := htrain
  have hdisj : Disjoint (B 0 ∪ B 1) (B 2) :=
    Finset.disjoint_union_left.mpr
      ⟨heval (by decide : (0 : Fin 3) ≠ 2),
       heval (by decide : (1 : Fin 3) ≠ 2)⟩
  have hinter : (B 0 ∪ B 1) ∩ B 2 ⊆ B0 := by
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
    exact Finset.empty_subset B0
  have h := condIndepFun_pi_of_inter_subset (Ω := Ω) μ hinter
  have hF : (Fintype.ofFinite ι) = (inferInstance : Fintype ι) :=
    Subsingleton.elim _ _
  have hpi : @Measure.pi ι Ω (Fintype.ofFinite ι) _ μ = Measure.pi μ :=
    congrArg (fun fi : Fintype ι => @Measure.pi ι Ω fi _ μ) hF
  simpa only [hpi] using h

/-- For [three coordinate blocks](hyp:B) and [one score on each block](hyp:η), the
[three-block product score](goal) is [given by evaluating each score on its block and multiplying
the three values](step:1). -/
noncomputable def threeBlockProduct (B : Fin 3 → Finset ι)
    (η : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ) :
    (∀ i, Ω i) → ℝ :=
  fun x => ∏ t : Fin 3, η t (finsetCoordProj (B t) x)

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Under [a finite product probability law](hyp:μ), [two coordinate blocks](hyp:S,T) with
[disjointness](hyp:hST), [two block scores](hyp:f,g), [their measurability](hyp:hfmeas,hgmeas),
and [integrability after pullback to the full experiment](hyp:hf,hg), [the product of the
pulled-back scores is integrable](goal). -/
theorem integrable_twoBlockProduct (S T : Finset ι) (hST : Disjoint S T)
    (f : ((i : {i // i ∈ S}) → Ω i.val) → ℝ)
    (g : ((i : {i // i ∈ T}) → Ω i.val) → ℝ)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hf : Integrable (fun x : ∀ i, Ω i => f (finsetCoordProj S x)) (Measure.pi μ))
    (hg : Integrable (fun x : ∀ i, Ω i => g (finsetCoordProj T x)) (Measure.pi μ)) :
    Integrable (fun x : ∀ i, Ω i =>
      f (finsetCoordProj S x) * g (finsetCoordProj T x)) (Measure.pi μ) := by
  have h := (indepFun_pi_of_disjoint (Ω := Ω) μ hST).comp hfmeas hgmeas
  have hF : (Fintype.ofFinite ι) = (inferInstance : Fintype ι) :=
    Subsingleton.elim _ _
  have hpi : @Measure.pi ι Ω (Fintype.ofFinite ι) _ μ = Measure.pi μ :=
    congrArg (fun fi : Fintype ι => @Measure.pi ι Ω fi _ μ) hF
  have hi : IndepFun (fun x : ∀ i, Ω i => f (finsetCoordProj S x))
      (fun x : ∀ i, Ω i => g (finsetCoordProj T x)) (Measure.pi μ) := by
    change IndepFun (fun x : ∀ i, Ω i => f (fun i => x i.val))
      (fun x : ∀ i, Ω i => g (fun i => x i.val)) (Measure.pi μ)
    simpa only [hpi, Function.comp_def] using h
  exact hi.integrable_mul hf hg

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Under [a finite product probability law](hyp:μ), [three pairwise-disjoint coordinate
blocks](hyp:B,heval), [measurable block scores](hyp:η,hηmeas), and [square-integrability of
their pullbacks](hyp:hη), [the three-block product is square-integrable](goal). -/
theorem memLp_threeBlockProduct (B : Fin 3 → Finset ι)
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (η : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (hηmeas : ∀ t, Measurable (η t))
    (hη : ∀ t, MemLp (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x))
      2 (Measure.pi μ)) :
    MemLp (threeBlockProduct B η) 2 (Measure.pi μ) := by
  classical
  let X (t : Fin 3) : (∀ i, Ω i) → ℝ :=
    fun x => η t (finsetCoordProj (B t) x)
  have hXmeas (t : Fin 3) : Measurable (X t) :=
    (hηmeas t).comp (measurable_finsetCoordProj (B t))
  have hsq (t : Fin 3) : Integrable (fun x => (X t x) ^ 2) (Measure.pi μ) :=
    (hη t).integrable_sq
  have h01 : Integrable (fun x => (X 0 x) ^ 2 * (X 1 x) ^ 2)
      (Measure.pi μ) :=
    integrable_twoBlockProduct μ (B 0) (B 1)
      (heval (by decide : (0 : Fin 3) ≠ 1))
      (fun y => (η 0 y) ^ 2) (fun y => (η 1 y) ^ 2)
      ((hηmeas 0).pow_const 2) ((hηmeas 1).pow_const 2)
      (hsq 0) (hsq 1)
  let F : ((i : {i // i ∈ B 0 ∪ B 1}) → Ω i.val) → ℝ :=
    fun y =>
      (η 0 (fun i => y ⟨i.val, Finset.mem_union.mpr (Or.inl i.property)⟩)) ^ 2 *
      (η 1 (fun i => y ⟨i.val, Finset.mem_union.mpr (Or.inr i.property)⟩)) ^ 2
  have hFmeas : Measurable F := by
    dsimp [F]
    apply Measurable.mul
    · apply Measurable.pow_const
      exact (hηmeas 0).comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    · apply Measurable.pow_const
      exact (hηmeas 1).comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  have hdisj : Disjoint (B 0 ∪ B 1) (B 2) :=
    Finset.disjoint_union_left.mpr
      ⟨heval (by decide : (0 : Fin 3) ≠ 2),
       heval (by decide : (1 : Fin 3) ≠ 2)⟩
  have hFint : Integrable (fun x => F (finsetCoordProj (B 0 ∪ B 1) x))
      (Measure.pi μ) := by
    convert h01 using 1
    ext x
    rfl
  have hprod : Integrable
      (fun x => F (finsetCoordProj (B 0 ∪ B 1) x) * (X 2 x) ^ 2)
      (Measure.pi μ) :=
    integrable_twoBlockProduct μ (B 0 ∪ B 1) (B 2) hdisj F
      (fun y => (η 2 y) ^ 2) hFmeas ((hηmeas 2).pow_const 2) hFint (hsq 2)
  apply (memLp_two_iff_integrable_sq ?_).2
  · convert hprod using 1
    ext x
    simp only [threeBlockProduct, Fin.prod_univ_three, mul_pow]
    change (X 0 x) ^ 2 * (X 1 x) ^ 2 * (X 2 x) ^ 2 =
      (X 0 x) ^ 2 * (X 1 x) ^ 2 * (X 2 x) ^ 2
    rfl
  · exact (Finset.measurable_prod _ (fun t _ => hXmeas t)).aestronglyMeasurable

omit [∀ i, StandardBorelSpace (Ω i)] in
/-- Under [a finite product probability law](hyp:μ), [three pairwise-disjoint coordinate
blocks](hyp:B,heval), [two families of measurable block scores](hyp:η,ζ,hηmeas,hζmeas), and
[square-integrability of every pulled-back score](hyp:hη,hζ), [the product of the two
three-block products is integrable](goal). -/
theorem integrable_threeBlockCross (B : Fin 3 → Finset ι)
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (η ζ : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (hηmeas : ∀ t, Measurable (η t)) (hζmeas : ∀ t, Measurable (ζ t))
    (hη : ∀ t, MemLp (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x))
      2 (Measure.pi μ))
    (hζ : ∀ t, MemLp (fun x : ∀ i, Ω i => ζ t (finsetCoordProj (B t) x))
      2 (Measure.pi μ)) :
    Integrable (fun x : ∀ i, Ω i =>
      threeBlockProduct B η x * threeBlockProduct B ζ x) (Measure.pi μ) := by
  exact (memLp_threeBlockProduct μ B heval η hηmeas hη).integrable_mul
    (memLp_threeBlockProduct μ B heval ζ hζmeas hζ)

/-- Under [a finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain), [pairwise evaluation
disjointness](hyp:heval), [measurable block scores](hyp:η,hηmeas), [integrable individual
scores](hyp:hη), [an integrable product over the first two blocks](hyp:hη01), and [an integrable
three-block product](hyp:hηprod), [the conditional mean of the three-block product is the
product of its three blockwise conditional means](goal). -/
theorem condExp_threeBlockProduct_of_integrable
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (η : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (hηmeas : ∀ t, Measurable (η t))
    (hη : ∀ t, Integrable
      (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x)) (Measure.pi μ))
    (hη01 : Integrable (fun x : ∀ i, Ω i =>
      η 0 (finsetCoordProj (B 0) x) * η 1 (finsetCoordProj (B 1) x))
      (Measure.pi μ))
    (hηprod : Integrable (threeBlockProduct B η) (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (threeBlockProduct B η) =ᵐ[Measure.pi μ]
    (fun x => ∏ t : Fin 3,
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (fun y : ∀ i, Ω i => η t (finsetCoordProj (B t) y)) x) := by
  classical
  have hm : MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance ≤
      (inferInstance : MeasurableSpace (∀ i, Ω i)) :=
    Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) B0)
  have h01 :=
    Causalean.Mathlib.Probability.Independence.Conditional.condExp_mul_of_condIndep
      (μ := Measure.pi μ) hm
      (measurable_finsetCoordProj (Ω := Ω) (B 0))
      (measurable_finsetCoordProj (Ω := Ω) (B 1))
      (condIndepFun_eval_pair μ B0 B htrain heval 0 1 (by decide))
      (hηmeas 0) (hηmeas 1) (hη 0) (hη 1) hη01
  let F : ((i : {i // i ∈ B 0 ∪ B 1}) → Ω i.val) → ℝ :=
    fun y =>
      η 0 (fun i => y ⟨i.val, Finset.mem_union.mpr (Or.inl i.property)⟩) *
      η 1 (fun i => y ⟨i.val, Finset.mem_union.mpr (Or.inr i.property)⟩)
  have hFmeas : Measurable F := by
    dsimp [F]
    apply Measurable.mul
    · exact (hηmeas 0).comp
        (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    · exact (hηmeas 1).comp
        (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  have hFint : Integrable (fun x => F (finsetCoordProj (B 0 ∪ B 1) x))
      (Measure.pi μ) := by
    convert hη01 using 1
    ext x
    rfl
  have hprod : Integrable (fun x =>
      F (finsetCoordProj (B 0 ∪ B 1) x) * η 2 (finsetCoordProj (B 2) x))
      (Measure.pi μ) := by
    convert hηprod using 1
    ext x
    simp only [threeBlockProduct, Fin.prod_univ_three]
    rfl
  have hstep2 :=
    Causalean.Mathlib.Probability.Independence.Conditional.condExp_mul_of_condIndep
      (μ := Measure.pi μ) hm
      (measurable_finsetCoordProj (Ω := Ω) (B 0 ∪ B 1))
      (measurable_finsetCoordProj (Ω := Ω) (B 2))
      (condIndepFun_eval_union μ B0 B htrain heval)
      hFmeas (hηmeas 2) hFint (hη 2) hprod
  have hfun : (fun x : ∀ i, Ω i =>
      F (finsetCoordProj (B 0 ∪ B 1) x) *
        η 2 (finsetCoordProj (B 2) x)) = threeBlockProduct B η := by
    funext x
    simp only [threeBlockProduct, Fin.prod_univ_three]
    rfl
  have hfun01 : (fun x : ∀ i, Ω i => F (finsetCoordProj (B 0 ∪ B 1) x)) =
      (fun x => η 0 (finsetCoordProj (B 0) x) *
        η 1 (finsetCoordProj (B 1) x)) := by
    funext x
    rfl
  rw [hfun, hfun01] at hstep2
  have hfinal := hstep2.trans (h01.mul
    (Filter.EventuallyEq.refl (ae (Measure.pi μ)) _))
  filter_upwards [hfinal] with x hx
  simpa [Fin.prod_univ_three] using hx

/-- Under [a finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain), [pairwise evaluation
disjointness](hyp:heval), [measurable left and right scores](hyp:η,ζ,hηmeas,hζmeas), and
[square-integrability of every block score](hyp:hη,hζ), [the conditional cross moment of the
two three-block products factors into three blockwise conditional cross moments](goal). -/
theorem condExp_threeBlockCross
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (η ζ : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (hηmeas : ∀ t, Measurable (η t)) (hζmeas : ∀ t, Measurable (ζ t))
    (hη : ∀ t, MemLp (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x))
      2 (Measure.pi μ))
    (hζ : ∀ t, MemLp (fun x : ∀ i, Ω i => ζ t (finsetCoordProj (B t) x))
      2 (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (fun x => threeBlockProduct B η x * threeBlockProduct B ζ x)
      =ᵐ[Measure.pi μ]
    (fun x => ∏ t : Fin 3,
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (fun y : ∀ i, Ω i =>
          η t (finsetCoordProj (B t) y) * ζ t (finsetCoordProj (B t) y)) x) := by
  classical
  let ξ (t : Fin 3) : ((i : {i // i ∈ B t}) → Ω i.val) → ℝ :=
    fun z => η t z * ζ t z
  have hξmeas (t : Fin 3) : Measurable (ξ t) :=
    (hηmeas t).mul (hζmeas t)
  have hξ (t : Fin 3) : Integrable
      (fun x : ∀ i, Ω i => ξ t (finsetCoordProj (B t) x)) (Measure.pi μ) :=
    (hη t).integrable_mul (hζ t)
  have hξ01 : Integrable (fun x : ∀ i, Ω i =>
      ξ 0 (finsetCoordProj (B 0) x) * ξ 1 (finsetCoordProj (B 1) x))
      (Measure.pi μ) :=
    integrable_twoBlockProduct μ (B 0) (B 1)
      (heval (by decide : (0 : Fin 3) ≠ 1))
      (ξ 0) (ξ 1) (hξmeas 0) (hξmeas 1) (hξ 0) (hξ 1)
  have hξprod : Integrable (threeBlockProduct B ξ) (Measure.pi μ) := by
    convert integrable_threeBlockCross μ B heval η ζ hηmeas hζmeas hη hζ using 1
    ext x
    simp only [threeBlockProduct, Fin.prod_univ_three]
    dsimp [ξ]
    ring
  have hfactor := condExp_threeBlockProduct_of_integrable μ B0 B htrain heval
    ξ hξmeas hξ hξ01 hξprod
  have hfun : threeBlockProduct B ξ =
      (fun x => threeBlockProduct B η x * threeBlockProduct B ζ x) := by
    funext x
    simp only [threeBlockProduct, Fin.prod_univ_three]
    dsimp [ξ]
    ring
  rw [hfun] at hfactor
  simpa only [ξ] using hfactor

/-- Under [a finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain), [pairwise evaluation
disjointness](hyp:heval), [measurable square-integrable block scores](hyp:η,hηmeas,hη), and
[conditional centering of every block score](hyp:hcenter), [the conditional mean of their
three-block product is zero](goal). -/
theorem condExp_threeBlockProduct_zero
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (η : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (hηmeas : ∀ t, Measurable (η t))
    (hη : ∀ t, MemLp (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x))
      2 (Measure.pi μ))
    (hcenter : ∀ t, condExp
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x))
        =ᵐ[Measure.pi μ] (0 : (∀ i, Ω i) → ℝ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (threeBlockProduct B η)
      =ᵐ[Measure.pi μ] (0 : (∀ i, Ω i) → ℝ) := by
  classical
  have hηint (t : Fin 3) : Integrable
      (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x)) (Measure.pi μ) :=
    (hη t).integrable (by norm_num)
  have hη01 : Integrable (fun x : ∀ i, Ω i =>
      η 0 (finsetCoordProj (B 0) x) * η 1 (finsetCoordProj (B 1) x))
      (Measure.pi μ) :=
    integrable_twoBlockProduct μ (B 0) (B 1)
      (heval (by decide : (0 : Fin 3) ≠ 1))
      (η 0) (η 1) (hηmeas 0) (hηmeas 1) (hηint 0) (hηint 1)
  have hηprod : Integrable (threeBlockProduct B η) (Measure.pi μ) :=
    (memLp_threeBlockProduct μ B heval η hηmeas hη).integrable (by norm_num)
  have hfactor := condExp_threeBlockProduct_of_integrable μ B0 B htrain heval
    η hηmeas hηint hη01 hηprod
  filter_upwards [hfactor, hcenter 0, hcenter 1, hcenter 2] with x hx h0 h1 h2
  simpa [Fin.prod_univ_three, h0, h1, h2] using hx

/-- Under [a finite product probability law](hyp:μ), [a training block and three evaluation
blocks](hyp:B0,B) with [training/evaluation disjointness](hyp:htrain), [pairwise evaluation
disjointness](hyp:heval), [measurable square-integrable left and right block
scores](hyp:η,ζ,hηmeas,hζmeas,hη,hζ),
and [conditional centering of both channels](hyp:hηcenter,hζcenter), [the conditional covariance
of the two three-block products is the product of their three blockwise conditional cross
moments](goal). -/
theorem condCov_threeBlockProduct
    (B0 : Finset ι) (B : Fin 3 → Finset ι)
    (htrain : ∀ t, Disjoint B0 (B t))
    (heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)))
    (η ζ : (t : Fin 3) → ((i : {i // i ∈ B t}) → Ω i.val) → ℝ)
    (hηmeas : ∀ t, Measurable (η t)) (hζmeas : ∀ t, Measurable (ζ t))
    (hη : ∀ t, MemLp (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x))
      2 (Measure.pi μ))
    (hζ : ∀ t, MemLp (fun x : ∀ i, Ω i => ζ t (finsetCoordProj (B t) x))
      2 (Measure.pi μ))
    (hηcenter : ∀ t, condExp
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (fun x : ∀ i, Ω i => η t (finsetCoordProj (B t) x))
        =ᵐ[Measure.pi μ] (0 : (∀ i, Ω i) → ℝ))
    (hζcenter : ∀ t, condExp
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (fun x : ∀ i, Ω i => ζ t (finsetCoordProj (B t) x))
        =ᵐ[Measure.pi μ] (0 : (∀ i, Ω i) → ℝ)) :
    (fun x =>
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (fun y => threeBlockProduct B η y * threeBlockProduct B ζ y) x -
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (threeBlockProduct B η) x *
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (threeBlockProduct B ζ) x)
      =ᵐ[Measure.pi μ]
    (fun x => ∏ t : Fin 3,
      condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
        (Measure.pi μ) (fun y : ∀ i, Ω i =>
          η t (finsetCoordProj (B t) y) * ζ t (finsetCoordProj (B t) y)) x) := by
  have hcross := condExp_threeBlockCross μ B0 B htrain heval η ζ
    hηmeas hζmeas hη hζ
  have hηzero := condExp_threeBlockProduct_zero μ B0 B htrain heval η
    hηmeas hη hηcenter
  have hζzero := condExp_threeBlockProduct_zero μ B0 B htrain heval ζ
    hζmeas hζ hζcenter
  filter_upwards [hcross, hηzero, hζzero] with x hx hηx hζx
  simpa [hηx, hζx] using hx

/-- For [a four-coordinate product probability law](hyp:ν), [left and right scores on the
three held-out coordinates](hyp:η,ζ), [their measurability](hyp:hηmeas,hζmeas), and
[square-integrability of their pullbacks](hyp:hη,hζ), [the conditional cross moment of their two
three-coordinate products factors by coordinate](goal). -/
theorem condExp_threeSingletonCross
    {X : Fin 4 → Type*} [∀ i, MeasurableSpace (X i)]
    [∀ i, StandardBorelSpace (X i)]
    (ν : (i : Fin 4) → Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (η ζ : (t : Fin 3) → X t.succ → ℝ)
    (hηmeas : ∀ t, Measurable (η t)) (hζmeas : ∀ t, Measurable (ζ t))
    (hη : ∀ t, MemLp (fun x : ∀ i, X i => η t (x t.succ)) 2 (Measure.pi ν))
    (hζ : ∀ t, MemLp (fun x : ∀ i, X i => ζ t (x t.succ)) 2 (Measure.pi ν)) :
    condExp (MeasurableSpace.comap
      (finsetCoordProj (Ω := X) ({0} : Finset (Fin 4))) inferInstance)
      (Measure.pi ν)
      (fun x : ∀ i, X i =>
        (∏ t : Fin 3, η t (x t.succ)) * (∏ t : Fin 3, ζ t (x t.succ)))
      =ᵐ[Measure.pi ν]
    (fun x => ∏ t : Fin 3,
      condExp (MeasurableSpace.comap
        (finsetCoordProj (Ω := X) ({0} : Finset (Fin 4))) inferInstance)
        (Measure.pi ν) (fun y : ∀ i, X i => η t (y t.succ) * ζ t (y t.succ)) x) := by
  classical
  let B : Fin 3 → Finset (Fin 4) := fun t => {t.succ}
  have htrain : ∀ t, Disjoint ({0} : Finset (Fin 4)) (B t) := by
    intro t
    simpa [B] using (Fin.succ_ne_zero t).symm
  have heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)) := by
    intro s t hst
    simpa [B] using (Fin.succ_injective 3).ne hst
  let ξ : (t : Fin 3) → ((i : {i // i ∈ B t}) → X i.val) → ℝ :=
    fun t z => η t (z ⟨t.succ, Finset.mem_singleton_self _⟩)
  let ψ : (t : Fin 3) → ((i : {i // i ∈ B t}) → X i.val) → ℝ :=
    fun t z => ζ t (z ⟨t.succ, Finset.mem_singleton_self _⟩)
  have hξmeas (t : Fin 3) : Measurable (ξ t) :=
    (hηmeas t).comp (measurable_pi_apply
      (⟨t.succ, Finset.mem_singleton_self _⟩ : {i // i ∈ B t}))
  have hψmeas (t : Fin 3) : Measurable (ψ t) :=
    (hζmeas t).comp (measurable_pi_apply
      (⟨t.succ, Finset.mem_singleton_self _⟩ : {i // i ∈ B t}))
  have hξ (t : Fin 3) : MemLp
      (fun x : ∀ i, X i => ξ t (finsetCoordProj (B t) x)) 2 (Measure.pi ν) := by
    exact hη t
  have hψ (t : Fin 3) : MemLp
      (fun x : ∀ i, X i => ψ t (finsetCoordProj (B t) x)) 2 (Measure.pi ν) := by
    exact hζ t
  have h := condExp_threeBlockCross ν ({0} : Finset (Fin 4)) B
    htrain heval ξ ψ hξmeas hψmeas hξ hψ
  simpa only [threeBlockProduct, finsetCoordProj, ξ, ψ, B] using h

end Causalean.Mathlib.Probability.Independence.Conditional
