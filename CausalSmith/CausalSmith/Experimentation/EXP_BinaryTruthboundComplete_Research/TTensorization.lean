import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.BlockArray
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TDualCompleteClass
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TQuarticSeparation
import Causalean.Experimentation.DesignBased.ProductBlock

/-! Tensorization of full and degree-restricted observable-margin programs. -/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- For [a number of blocks and their component experiments](hyp:B,comp), [the product schedule space](goal) collects one binary schedule for every block. -/
abbrev ProductTheta (B : ℕ) (comp : Fin B → Setup) := ∀ j, Theta (comp j)
/-- For [a number of blocks and their component experiments](hyp:B,comp), [a product coordinate](goal) records a block and one coordinate within it. -/
abbrev ProductCoordinate (B : ℕ) (comp : Fin B → Setup) := Σ j, Fin (comp j).K

/-- For [a block collection](hyp:B,comp) and [a set of product coordinates](hyp:S), [the product monomial](goal) multiplies their binary schedule entries. -/
def productMonomial (B : ℕ) (comp : Fin B → Setup)
    (S : Finset (ProductCoordinate B comp)) : ProductTheta B comp → ℝ := fun θ =>
  ∏ c ∈ S, (((θ c.1 c.2 : Fin 2) : ℕ) : ℝ)

/-- Joint supports observable under a product-assignment atom. -/
def productObservableComplex (B : ℕ) (comp : Fin B → Setup) :
    Set (Finset (ProductCoordinate B comp)) :=
  {S | ∃ w : ∀ j, (comp j).Omega, ∀ c ∈ S, c.2 ∈ (comp c.1).O (w c.1)}

/-- Span containing every cross-block observed-data interaction of total degree at most `r`. -/
noncomputable def productObservableSpan (B : ℕ) (comp : Fin B → Setup)
    (r : WithTop ℕ) : Submodule ℝ (ProductTheta B comp → ℝ) :=
  Submodule.span ℝ {u | ∃ S, S ∈ productObservableComplex B comp ∧
    (S.card : WithTop ℕ) ≤ r ∧ u = productMonomial B comp S}

/-- For [a block collection](hyp:B,comp) with [block score weights](hyp:a), [the product variance function](goal) is the weighted sum of component true variances. -/
def productVarianceFn (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ) :
    ProductTheta B comp → ℝ := fun θ =>
  ∑ j, (a j) ^ 2 * trueVarianceFn (comp j) (θ j)

/-- For [a block collection](hyp:B,comp), [score weights](hyp:a), and [a degree bound](hyp:r), [the product conservative cone](goal) contains observable rules that dominate the product variance at every schedule. -/
def productConservativeCone (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ)
    (r : WithTop ℕ) : Set (ProductTheta B comp → ℝ) :=
  {b | b ∈ productObservableSpan B comp r ∧ ∀ θ, productVarianceFn B comp a θ ≤ b θ}

/-- For [a block collection](hyp:B,comp) and [component objective distributions](hyp:q), [the product weight](goal) is their independent joint distribution over product schedules. -/
def productWeight (B : ℕ) (comp : Fin B → Setup)
    (q : ∀ j, FullSupportObjective (comp j)) : ProductTheta B comp → ℝ := fun θ =>
  ∏ j, (q j).1 (θ j)

/-- Full or degree-restricted product optimum with joint observable interactions retained. -/
noncomputable def productOptValue (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ)
    (q : ∀ j, FullSupportObjective (comp j)) (r : WithTop ℕ) : ℝ :=
  sInf ((fun b => ∑ θ, productWeight B comp q θ * b θ) ''
    productConservativeCone B comp a r)
  -- @realizes F_{\mathrm{prod}}(r=top product optimum); @realizes F_{\mathrm{prod},r}(degree-r product optimum)

/-- Add the component primal rules with the squared score weights. -/
def additiveProductRule (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ)
    (b : ∀ j, Theta (comp j) → ℝ) : ProductTheta B comp → ℝ := fun θ =>
  ∑ j, (a j) ^ 2 * b j (θ j)

/-- Tensor a family of component dual weights. -/
def tensorProductDual (B : ℕ) (comp : Fin B → Setup)
    (μ : ∀ j, Theta (comp j) → ℝ) : ProductTheta B comp → ℝ := fun θ =>
  ∏ j, μ j (θ j)

/-- Product dual weights matching every joint observable moment, including cross-block moments. -/
def productDualMarginPolytope (B : ℕ) (comp : Fin B → Setup)
    (q : ∀ j, FullSupportObjective (comp j)) : Set (ProductTheta B comp → ℝ) :=
  {μ | (∀ θ, 0 ≤ μ θ) ∧
    ∀ S ∈ productObservableComplex B comp,
      ∑ θ, μ θ * productMonomial B comp S θ =
        ∑ θ, productWeight B comp q θ * productMonomial B comp S θ}

/-- The coordinates of a product support lying in block `j`. -/
-- @node: productFiber
def productFiber (B : ℕ) (comp : Fin B → Setup)
    (S : Finset (ProductCoordinate B comp)) (j : Fin B) : Finset (Fin (comp j).K) :=
  Finset.univ.filter fun i => Sigma.mk j i ∈ S

/-- Product dual weights matching all observable moments through total degree `r`. -/
-- @node: productDegreeDualMarginSet
def productDegreeDualMarginSet (B : ℕ) (comp : Fin B → Setup)
    (q : ∀ j, FullSupportObjective (comp j)) (r : WithTop ℕ) :
    Set (ProductTheta B comp → ℝ) :=
  {μ | (∀ θ, 0 ≤ μ θ) ∧
    ∀ S ∈ productObservableComplex B comp, (S.card : WithTop ℕ) ≤ r →
      ∑ θ, μ θ * productMonomial B comp S θ =
        ∑ θ, productWeight B comp q θ * productMonomial B comp S θ}

/-- For [a product support and schedule](hyp:S,θ), [its product monomial factors into the monomials of its blockwise fibers](goal). -/
-- @node: productMonomial_eq_fiber_prod
lemma productMonomial_eq_fiber_prod (B : ℕ) (comp : Fin B → Setup)
    (S : Finset (ProductCoordinate B comp)) (θ : ProductTheta B comp) :
    productMonomial B comp S θ =
      ∏ j, monomial (comp j) (productFiber B comp S j) (θ j) := by
  classical
  have hS : S = Finset.univ.sigma (productFiber B comp S) := by
    ext c
    simp [productFiber]
  unfold productMonomial monomial
  calc
    (∏ c ∈ S, (((θ c.1 c.2 : Fin 2) : ℕ) : ℝ)) =
        ∏ c ∈ Finset.univ.sigma (productFiber B comp S),
          (((θ c.1 c.2 : Fin 2) : ℕ) : ℝ) :=
      congrArg (fun T : Finset (ProductCoordinate B comp) =>
        ∏ c ∈ T, (((θ c.1 c.2 : Fin 2) : ℕ) : ℝ)) hS
    _ = ∏ j ∈ Finset.univ, ∏ i ∈ productFiber B comp S j,
          (((θ j i : Fin 2) : ℕ) : ℝ) := Finset.prod_sigma _ _ _
    _ = _ := by simp

/-- If [a product support is jointly observable](hyp:hS), then [its fiber in any selected block is observable](goal). -/
-- @node: productFiber_observable
lemma productFiber_observable (B : ℕ) (comp : Fin B → Setup)
    {S : Finset (ProductCoordinate B comp)} (hS : S ∈ productObservableComplex B comp)
    (j : Fin B) : productFiber B comp S j ∈ observableComplex (comp j) := by
  classical
  rcases hS with ⟨w, hw⟩
  unfold observableComplex
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
  refine ⟨fun i hi => ?_, w j, fun i hi => ?_⟩
  · exact Finset.mem_univ i
  · exact hw ⟨j, i⟩ (by simpa [productFiber] using hi)

/-- For [a product support and block](hyp:S,j), [the fiber has no more coordinates than the full support](goal). -/
-- @node: productFiber_card_le
lemma productFiber_card_le (B : ℕ) (comp : Fin B → Setup)
    (S : Finset (ProductCoordinate B comp)) (j : Fin B) :
    (productFiber B comp S j).card ≤ S.card := by
  classical
  let e : Fin (comp j).K ↪ ProductCoordinate B comp :=
    Function.Embedding.sigmaMk (β := fun j => Fin (comp j).K) j
  rw [← Finset.card_map e]
  apply Finset.card_le_card
  intro c hc
  rcases Finset.mem_map.mp hc with ⟨i, hi, rfl⟩
  simpa [e, productFiber] using hi

/-- Lift one component function to the product schedule. -/
-- @node: liftProductFunction
def liftProductFunction (B : ℕ) (comp : Fin B → Setup) (j : Fin B)
    (u : Theta (comp j) → ℝ) : ProductTheta B comp → ℝ := fun θ => u (θ j)

/-- If [a component function lies in that component's observable span](hyp:hu), then [its lift to any block lies in the product observable span](goal). -/
-- @node: liftProductFunction_mem_span
lemma liftProductFunction_mem_span (B : ℕ) (comp : Fin B → Setup) (r : WithTop ℕ)
    (j : Fin B) {u : Theta (comp j) → ℝ} (hu : u ∈ observableSpan (comp j) r) :
    liftProductFunction B comp j u ∈ productObservableSpan B comp r := by
  classical
  unfold observableSpan at hu
  refine Submodule.span_induction
    (p := fun u _ => liftProductFunction B comp j u ∈ productObservableSpan B comp r)
    ?_ ?_ ?_ ?_ hu
  · intro u hu
    rcases hu with ⟨T, hT, hdeg, rfl⟩
    let e : Fin (comp j).K ↪ ProductCoordinate B comp :=
      Function.Embedding.sigmaMk (β := fun j => Fin (comp j).K) j
    let S := T.map e
    have hSobs : S ∈ productObservableComplex B comp := by
      have hT' := hT
      unfold observableComplex at hT'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
      rcases hT'.2 with ⟨z, hz⟩
      let w : ∀ k, (comp k).Omega := fun k =>
        if h : k = j then h ▸ z else
          Classical.choice
            (Causalean.Experimentation.DesignBased.FiniteDesign.nonempty_of_design
              (fun k => (comp k).design) k)
      refine ⟨w, ?_⟩
      intro c hc
      rcases Finset.mem_map.mp hc with ⟨i, hi, rfl⟩
      change i ∈ (comp j).O (w j)
      simpa [w] using hz hi
    apply Submodule.subset_span
    refine ⟨S, hSobs, ?_, ?_⟩
    · simpa [S] using hdeg
    · funext θ
      unfold liftProductFunction productMonomial monomial
      rw [show S = T.map e from rfl, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro i hi
      rfl
  · convert (productObservableSpan B comp r).zero_mem using 1
    ext θ
    simp [liftProductFunction]
  · intro u v _ _ hu hv
    convert (productObservableSpan B comp r).add_mem hu hv using 1
    ext θ
    simp [liftProductFunction]
  · intro c u _ hu
    convert (productObservableSpan B comp r).smul_mem c hu using 1
    ext θ
    simp [liftProductFunction]

/-- For [a family of component rules](hyp:b), if [every component rule is conservative at the stated degree](hyp:hb), then [their squared-weighted sum is a conservative product rule](goal). -/
-- @node: additiveProductRule_mem_cone
lemma additiveProductRule_mem_cone (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ)
    (r : WithTop ℕ) (b : ∀ j, Theta (comp j) → ℝ)
    (hb : ∀ j, b j ∈ conservativeCone (comp j) r) :
    additiveProductRule B comp a b ∈ productConservativeCone B comp a r := by
  constructor
  · change (fun θ => ∑ j, (a j) ^ 2 * b j (θ j)) ∈ productObservableSpan B comp r
    have hs : (∑ j, (a j) ^ 2 • liftProductFunction B comp j (b j)) ∈
        productObservableSpan B comp r :=
      (productObservableSpan B comp r).sum_mem fun j _ =>
        (productObservableSpan B comp r).smul_mem ((a j) ^ 2)
          (liftProductFunction_mem_span B comp r j (hb j).1)
    convert hs using 1
    ext θ
    simp [liftProductFunction, smul_eq_mul]
  · intro θ
    unfold productVarianceFn additiveProductRule
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left ((hb j).2 (θ j)) (sq_nonneg (a j))

/-- For [component dual weights and component functions](hyp:μ,u), [the product-weighted joint sum factors into the product of component sums](goal). -/
-- @node: sum_tensor_mul_prod
lemma sum_tensor_mul_prod (B : ℕ) (comp : Fin B → Setup)
    (μ : ∀ j, Theta (comp j) → ℝ) (u : ∀ j, Theta (comp j) → ℝ) :
    (∑ θ, tensorProductDual B comp μ θ * ∏ j, u j (θ j)) =
      ∏ j, ∑ x, μ j x * u j x := by
  classical
  calc
    (∑ θ, tensorProductDual B comp μ θ * ∏ j, u j (θ j)) =
        ∑ θ : ProductTheta B comp, ∏ j, (μ j (θ j) * u j (θ j)) := by
      apply Finset.sum_congr rfl
      intro θ _
      simp only [tensorProductDual]
      rw [← Finset.prod_mul_distrib]
    _ = _ := (Fintype.prod_sum fun j x => μ j x * u j x).symm

/-- If [a dual weight matches all observable moments through the degree bound](hyp:hμ), then [its total mass is one](goal). -/
-- @node: degreeDualMargin_sum_one
lemma degreeDualMargin_sum_one (E : Setup) (q : FullSupportObjective E)
    (r : WithTop ℕ) {μ : Theta E → ℝ} (hμ : μ ∈ degreeDualMarginSet E q r) :
    ∑ θ, μ θ = 1 := by
  classical
  have hnonempty : Nonempty E.Omega :=
    Causalean.Experimentation.DesignBased.FiniteDesign.nonempty_of_design
      (ι := Fin 1) (α := fun _ => E.Omega) (fun _ => E.design) 0
  let z : E.Omega := Classical.choice hnonempty
  have hempty : (∅ : Finset (Fin E.K)) ∈ observableComplex E := by
    unfold observableComplex
    simp [z]
  have h := hμ.2 ∅ hempty (by simp)
  simpa [monomial, q.2.2] using h

/-- For [component dual weights](hyp:μ), if [each weight has unit mass](hyp:hsum), then [a tensor-weighted expectation of a lifted function equals its component expectation](goal). -/
-- @node: sum_tensor_lift
lemma sum_tensor_lift (B : ℕ) (comp : Fin B → Setup)
    (μ : ∀ j, Theta (comp j) → ℝ) (hsum : ∀ j, ∑ x, μ j x = 1)
    (j : Fin B) (u : Theta (comp j) → ℝ) :
    (∑ θ, tensorProductDual B comp μ θ * u (θ j)) = ∑ x, μ j x * u x := by
  classical
  let v : ∀ k, Theta (comp k) → ℝ := fun k x =>
    if h : k = j then u (h ▸ x) else 1
  calc
    (∑ θ, tensorProductDual B comp μ θ * u (θ j)) =
        ∑ θ, tensorProductDual B comp μ θ * ∏ k, v k (θ k) := by
      apply Finset.sum_congr rfl
      intro θ _
      congr 1
      simp [v]
    _ = ∏ k, ∑ x, μ k x * v k x := sum_tensor_mul_prod B comp μ v
    _ = ∑ x, μ j x * u x := by
      simp [v, hsum]

/-- For [component dual weights](hyp:μ) and [component functions](hyp:u), if [each weight has unit mass](hyp:hsum), then [the tensor-weighted expectation of an additive rule is the sum of component expectations](goal). -/
-- @node: sum_tensor_additive
lemma sum_tensor_additive (B : ℕ) (comp : Fin B → Setup)
    (μ : ∀ j, Theta (comp j) → ℝ) (hsum : ∀ j, ∑ x, μ j x = 1)
    (c : Fin B → ℝ) (u : ∀ j, Theta (comp j) → ℝ) :
    (∑ θ, tensorProductDual B comp μ θ * ∑ j, c j * u j (θ j)) =
      ∑ j, c j * (∑ x, μ j x * u j x) := by
  calc
    (∑ θ, tensorProductDual B comp μ θ * ∑ j, c j * u j (θ j)) =
        ∑ θ, ∑ j, tensorProductDual B comp μ θ * (c j * u j (θ j)) := by
      apply Finset.sum_congr rfl
      intro θ _
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ θ, tensorProductDual B comp μ θ * (c j * u j (θ j)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ θ, tensorProductDual B comp μ θ * (c j * u j (θ j))) =
            c j * ∑ θ, tensorProductDual B comp μ θ * u j (θ j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
        _ = c j * ∑ x, μ j x * u j x := by
          rw [sum_tensor_lift B comp μ hsum j]

/-- For [full-support component objectives](hyp:q) and [component dual weights](hyp:μ), if [every weight satisfies its degree-restricted observable margins](hyp:hμ), then [their tensor product satisfies the product degree-restricted margins](goal). -/
-- @node: tensorProductDual_degree_margin
lemma tensorProductDual_degree_margin (B : ℕ) (comp : Fin B → Setup)
    (q : ∀ j, FullSupportObjective (comp j)) (r : WithTop ℕ)
    (μ : ∀ j, Theta (comp j) → ℝ)
    (hμ : ∀ j, μ j ∈ degreeDualMarginSet (comp j) (q j) r) :
    tensorProductDual B comp μ ∈ productDegreeDualMarginSet B comp q r := by
  classical
  constructor
  · intro θ
    exact Finset.prod_nonneg fun j _ => (hμ j).1 (θ j)
  · intro S hS hdeg
    have hmarg (j : Fin B) :
        (∑ x, μ j x * monomial (comp j) (productFiber B comp S j) x) =
          ∑ x, (q j).1 x * monomial (comp j) (productFiber B comp S j) x := by
      apply (hμ j).2 (productFiber B comp S j) (productFiber_observable B comp hS j)
      exact (by exact_mod_cast productFiber_card_le B comp S j :
        ((productFiber B comp S j).card : WithTop ℕ) ≤ S.card).trans hdeg
    simp_rw [productMonomial_eq_fiber_prod]
    calc
      (∑ θ, tensorProductDual B comp μ θ *
          ∏ j, monomial (comp j) (productFiber B comp S j) (θ j)) =
          ∏ j, ∑ x, μ j x * monomial (comp j) (productFiber B comp S j) x :=
        sum_tensor_mul_prod B comp μ _
      _ = ∏ j, ∑ x, (q j).1 x *
          monomial (comp j) (productFiber B comp S j) x := by simp_rw [hmarg]
      _ = ∑ θ, productWeight B comp q θ *
          ∏ j, monomial (comp j) (productFiber B comp S j) (θ j) := by
        rw [← sum_tensor_mul_prod B comp (fun j => (q j).1)]
        rfl

/-- For [full-support component objectives](hyp:q), if [a product rule is conservative](hyp:hb) and [a product dual weight satisfies the degree-restricted margins](hyp:hμ), then [the dual variance objective is no larger than the rule's objective](goal). -/
-- @node: product_degree_weak_duality
lemma product_degree_weak_duality (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ)
    (q : ∀ j, FullSupportObjective (comp j)) (r : WithTop ℕ)
    {b μ : ProductTheta B comp → ℝ} (hb : b ∈ productConservativeCone B comp a r)
    (hμ : μ ∈ productDegreeDualMarginSet B comp q r) :
    (∑ θ, μ θ * productVarianceFn B comp a θ) ≤
      ∑ θ, productWeight B comp q θ * b θ := by
  have hmargin : ∀ u ∈ productObservableSpan B comp r,
      (∑ θ, μ θ * u θ) = ∑ θ, productWeight B comp q θ * u θ := by
    intro u hu
    unfold productObservableSpan at hu
    refine Submodule.span_induction
      (p := fun u _ => (∑ θ, μ θ * u θ) =
        ∑ θ, productWeight B comp q θ * u θ) ?_ ?_ ?_ ?_ hu
    · intro u hu
      rcases hu with ⟨S, hS, hdeg, rfl⟩
      exact hμ.2 S hS hdeg
    · simp
    · intro u v _ _ hu hv
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hu, hv]
    · intro c u _ hu
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        (∑ θ, μ θ * (c * u θ)) = c * ∑ θ, μ θ * u θ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
        _ = c * ∑ θ, productWeight B comp q θ * u θ := by rw [hu]
        _ = ∑ θ, productWeight B comp q θ * (c * u θ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
  calc
    (∑ θ, μ θ * productVarianceFn B comp a θ) ≤ ∑ θ, μ θ * b θ := by
      apply Finset.sum_le_sum
      intro θ _
      exact mul_le_mul_of_nonneg_left (hb.2 θ) (hμ.1 θ)
    _ = _ := hmargin b hb.1

/-- For [a collection of component experiments, score weights, and objectives](hyp:B,comp,a,q), [the product experiment has the stated factorized objective, observable tables, optimization values, primal rules, dual weights, and witness values](goal). -/
-- @node: thm:tensorization
theorem optValue_product_tensorization (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ)
    (q : ∀ j, FullSupportObjective (comp j)) :
    (productExperiment B comp a q).objectiveWeight = productWeight B comp q ∧
    (productExperiment B comp a q).jointObservedTables = Set.univ ∧
    (∀ r : WithTop ℕ,
      productOptValue B comp a q r = ∑ j, (a j) ^ 2 * optValue (comp j) (q j) r ∧
      ∀ b : ∀ j, Theta (comp j) → ℝ,
        (∀ j, b j ∈ conservativeCone (comp j) r) →
          additiveProductRule B comp a b ∈ productConservativeCone B comp a r) ∧
    (∀ μ : ∀ j, Theta (comp j) → ℝ,
      (∀ j, μ j ∈ dualMarginSet (comp j) (q j)) →
        tensorProductDual B comp μ ∈ productDualMarginPolytope B comp q) ∧
    (∀ n : ℕ, 0 < n →
      productOptValue n (fun _ => witnessExperiment) (fun _ => (n : ℝ)⁻¹)
        (fun _ => witnessObjective) ⊤ = 107 / (72 * n) ∧
      productOptValue n (fun _ => witnessExperiment) (fun _ => (n : ℝ)⁻¹)
        (fun _ => witnessObjective) 2 = 55 / (36 * n) ∧
      productOptValue n (fun _ => witnessExperiment) (fun _ => (n : ℝ)⁻¹)
        (fun _ => witnessObjective) 3 = 55 / (36 * n) ∧
      productOptValue n (fun _ => witnessExperiment) (fun _ => (n : ℝ)⁻¹)
        (fun _ => witnessObjective) 2 -
      productOptValue n (fun _ => witnessExperiment) (fun _ => (n : ℝ)⁻¹)
          (fun _ => witnessObjective) ⊤ = 1 / (24 * n)) := by
  classical
  have htensor : ∀ (B : ℕ) (comp : Fin B → Setup) (a : Fin B → ℝ)
      (q : ∀ j, FullSupportObjective (comp j)) (r : WithTop ℕ),
      productOptValue B comp a q r = ∑ j, (a j) ^ 2 * optValue (comp j) (q j) r := by
    intro B comp a q r
    choose b hb hbval using fun j => observable_primal_attained (comp j) (q j) r
    let bp := additiveProductRule B comp a b
    have hbp : bp ∈ productConservativeCone B comp a r :=
      additiveProductRule_mem_cone B comp a r b hb
    have hqsum : ∀ j, ∑ x, (q j).1 x = 1 := fun j => (q j).2.2
    have hbpval : (∑ θ, productWeight B comp q θ * bp θ) =
        ∑ j, (a j) ^ 2 * optValue (comp j) (q j) r := by
      have h := sum_tensor_additive B comp (fun j => (q j).1) hqsum
        (fun j => (a j) ^ 2) b
      simpa [tensorProductDual, productWeight, additiveProductRule, bp, hbval] using h
    have hfnonneg : ∀ θ, 0 ≤ productVarianceFn B comp a θ := by
      intro θ
      unfold productVarianceFn
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg (sq_nonneg _)
      rw [designVarianceFn_eq_Var]
      unfold Causalean.Experimentation.DesignBased.FiniteDesign.Var
        Causalean.Experimentation.DesignBased.FiniteDesign.E
      exact Finset.sum_nonneg fun z _ =>
        mul_nonneg ((comp j).design.p_nonneg z) (sq_nonneg _)
    have hqnonneg : ∀ θ, 0 ≤ productWeight B comp q θ := by
      intro θ
      exact Finset.prod_nonneg fun j _ => ((q j).2.1 (θ j)).le
    have hupper : productOptValue B comp a q r ≤
        ∑ j, (a j) ^ 2 * optValue (comp j) (q j) r := by
      unfold productOptValue
      rw [← hbpval]
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro y ⟨u, hu, rfl⟩
        exact Finset.sum_nonneg fun θ _ =>
          mul_nonneg (hqnonneg θ) ((hfnonneg θ).trans (hu.2 θ))
      · exact ⟨bp, hbp, rfl⟩
    choose μ hμ hμval using fun j =>
      (observable_degree_strong_duality (comp j) (q j) r).2
    have hμsum : ∀ j, ∑ x, μ j x = 1 := fun j =>
      degreeDualMargin_sum_one (comp j) (q j) r (hμ j)
    let μp := tensorProductDual B comp μ
    have hμp : μp ∈ productDegreeDualMarginSet B comp q r :=
      tensorProductDual_degree_margin B comp q r μ hμ
    have hμpval : (∑ θ, μp θ * productVarianceFn B comp a θ) =
        ∑ j, (a j) ^ 2 * optValue (comp j) (q j) r := by
      have h := sum_tensor_additive B comp μ hμsum (fun j => (a j) ^ 2)
        (fun j => trueVarianceFn (comp j))
      simpa [μp, productVarianceFn, hμval] using h
    have hlower : (∑ j, (a j) ^ 2 * optValue (comp j) (q j) r) ≤
        productOptValue B comp a q r := by
      rw [← hμpval]
      unfold productOptValue
      apply le_csInf
      · exact ⟨∑ θ, productWeight B comp q θ * bp θ, ⟨bp, hbp, rfl⟩⟩
      · rintro y ⟨u, hu, rfl⟩
        exact product_degree_weak_duality B comp a q r hu hμp
    exact le_antisymm hupper hlower
  have hfullDual : ∀ μ : ∀ j, Theta (comp j) → ℝ,
      (∀ j, μ j ∈ dualMarginSet (comp j) (q j)) →
        tensorProductDual B comp μ ∈ productDualMarginPolytope B comp q := by
    intro μ hμ
    have hlocal : ∀ j, μ j ∈ degreeDualMarginSet (comp j) (q j) ⊤ := by
      intro j
      simpa [degreeDualMarginSet, dualMarginSet] using hμ j
    have hp := tensorProductDual_degree_margin B comp q ⊤ μ hlocal
    simpa [productDegreeDualMarginSet, productDualMarginPolytope] using hp
  refine ⟨rfl, rfl, ?_, hfullDual, ?_⟩
  · intro r
    exact ⟨htensor B comp a q r,
      fun b hb => additiveProductRule_mem_cone B comp a r b hb⟩
  · intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rcases witness_quartic_separation with ⟨hfull, htwo, hthree, hgap, _⟩
    have ht := htensor n (fun _ => witnessExperiment) (fun _ => (n : ℝ)⁻¹)
      (fun _ => witnessObjective)
    have htop := ht ⊤
    have htwo' := ht 2
    have hthree' := ht 3
    simp only [hfull, htwo, hthree, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin] at htop htwo' hthree'
    constructor
    · rw [htop]
      simp only [nsmul_eq_mul]
      field_simp [hn0]
    constructor
    · rw [htwo']
      simp only [nsmul_eq_mul]
      field_simp [hn0]
    constructor
    · rw [hthree']
      simp only [nsmul_eq_mul]
      field_simp [hn0]
    · rw [htwo', htop]
      simp only [nsmul_eq_mul]
      field_simp [hn0]
      ring

end CausalSmith.Experimentation.BinaryTruthbound
