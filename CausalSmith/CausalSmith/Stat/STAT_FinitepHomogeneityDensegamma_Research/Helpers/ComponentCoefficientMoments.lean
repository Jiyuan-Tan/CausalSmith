module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentCancellations

/-! Exact one- and two-node moments of normalized independent coefficient laws. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Multiplying each node weight by a node function factors its exact finite expectation. [This is the stated conclusion](goal). -/
-- @node: finite_product_weight_moment
lemma finite_product_weight_moment {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (w f : ι → α → ℝ) :
    (∑ p : ι → α, (∏ i, w i (p i)) * ∏ i, f i (p i)) =
      ∏ i, ∑ q, w i q * f i q := by
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i q => w i q * f i q)).symm

/-- A normalized product law averages a function of one node using exactly its local law. This statement assumes [the hw condition](hyp:hw). [This is the stated conclusion](goal). -/
-- @node: finite_product_weight_one_node
lemma finite_product_weight_one_node {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (w : ι → α → ℝ) (hw : ∀ i, ∑ q, w i q = 1)
    (j : ι) (f : α → ℝ) :
    (∑ p : ι → α, (∏ i, w i (p i)) * f (p j)) = ∑ q, w j q * f q := by
  have he (p : ι → α) : f (p j) = ∏ i, if i = j then f (p i) else 1 := by simp
  simp_rw [he]
  rw [finite_product_weight_moment w (fun i q => if i = j then f q else 1)]
  have hl (i : ι) : (∑ q, w i q * (if i = j then f q else 1)) =
      if i = j then ∑ q, w j q * f q else 1 := by
    by_cases h : i = j
    · subst i; simp
    · simp [h, hw]
  simp_rw [hl]
  simp

/-- Distinct coefficient nodes are independent even after fixing the disclosed node values. This statement assumes [the hw condition](hyp:hw), [the hij condition](hyp:hij). [This is the stated conclusion](goal). -/
-- @node: finite_product_weight_two_nodes
lemma finite_product_weight_two_nodes {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (w : ι → α → ℝ) (hw : ∀ i, ∑ q, w i q = 1)
    (i j : ι) (hij : i ≠ j) (f g : α → ℝ) :
    (∑ p : ι → α, (∏ k, w k (p k)) * (f (p i) * g (p j))) =
      (∑ q, w i q * f q) * ∑ q, w j q * g q := by
  have he (p : ι → α) : f (p i) * g (p j) =
      ∏ k, (if k = i then f (p k) else 1) * (if k = j then g (p k) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [he]
  rw [finite_product_weight_moment w (fun k q =>
    (if k = i then f q else 1) * (if k = j then g q else 1))]
  have hl (k : ι) :
      (∑ q, w k q * ((if k = i then f q else 1) * (if k = j then g q else 1))) =
      (if k = i then ∑ q, w i q * f q else 1) *
        (if k = j then ∑ q, w j q * g q else 1) := by
    by_cases hi : k = i
    · subst k; simp [hij]
    · by_cases hj : k = j
      · subst k; simp [Ne.symm hij]
      · simp [hi, hj, hw]
  simp_rw [hl]
  rw [Finset.prod_mul_distrib]
  simp

/-- The local copula pair has fair marginal first moments and its prescribed mixed sign moment. [This is the stated conclusion](goal). -/
-- @node: pairWeight_sign_moments
lemma pairWeight_sign_moments (ν : Bool) (g : ℝ) :
    (∑ q : Bool × Bool, pairWeight ν g q.1 q.2 * signVal q.1) = 0 ∧
    (∑ q : Bool × Bool, pairWeight ν g q.1 q.2 * signVal q.2) = 0 ∧
    (∑ q : Bool × Bool, pairWeight ν g q.1 q.2 * (signVal q.1 * signVal q.2)) =
      (if ν then 1 else 0) * kappa0 * g := by
  cases ν <;> simp [Fintype.sum_prod_type, pairWeight, signVal] <;> constructor <;> first | ring | constructor <;> ring

/-- Undisclosed nodes have zero marginal means and the exact prescribed local copula correlation. This statement assumes [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_undisclosed_node_moments
lemma conditionalPairWeight_undisclosed_node_moments (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (δ : Disclosure K) (j : Fin (K+1)) (hj : δ j = none) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * signVal (p j).1) = 0 ∧
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * signVal (p j).2) = 0 ∧
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      (signVal (p j).1 * signVal (p j).2)) =
        (if ν then 1 else 0) * kappa0 * coarseTent M σ ((j:ℝ)/K) := by
  let w (i : Fin (K+1)) (q : Bool × Bool) : ℝ := match δ i with
    | some r => if q = r then 1 else 0
    | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) q.1 q.2
  have hw (i : Fin (K+1)) : ∑ q, w i q = 1 := by
    cases hd : δ i with
    | some q => simp [w, hd]
    | none => simpa [w, hd] using pairWeight_sum ν (coarseTent M σ ((i:ℝ)/K))
  have he (f : Bool × Bool → ℝ) :
      (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * f (p j)) =
        ∑ q, pairWeight ν (coarseTent M σ ((j:ℝ)/K)) q.1 q.2 * f q := by
    change (∑ p : CoefficientPairs K, (∏ i, w i (p i)) * f (p j)) = _
    rw [finite_product_weight_one_node w hw]
    simp only [w, hj]
  rw [he (fun q => signVal q.1), he (fun q => signVal q.2),
    he (fun q => signVal q.1 * signVal q.2)]
  exact pairWeight_sign_moments ν _

/-- Distinct undisclosed nodes have zero mixed sign moments, for either choice of coordinates. This statement assumes [the hij condition](hyp:hij), [the hi condition](hyp:hi), [the hj condition](hyp:hj). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_distinct_undisclosed_moment
lemma conditionalPairWeight_distinct_undisclosed_moment (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (δ : Disclosure K) (i j : Fin (K+1)) (hij : i ≠ j)
    (hi : δ i = none) (hj : δ j = none) (r s : Bool) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      (signVal (if r then (p i).1 else (p i).2) *
        signVal (if s then (p j).1 else (p j).2))) = 0 := by
  let w (k : Fin (K+1)) (q : Bool × Bool) : ℝ := match δ k with
    | some t => if q = t then 1 else 0
    | none => pairWeight ν (coarseTent M σ ((k:ℝ)/K)) q.1 q.2
  have hw (k : Fin (K+1)) : ∑ q, w k q = 1 := by
    cases hd : δ k with
    | some q => simp [w, hd]
    | none => simpa [w, hd] using pairWeight_sum ν (coarseTent M σ ((k:ℝ)/K))
  change (∑ p : CoefficientPairs K, (∏ k, w k (p k)) *
    (signVal (if r then (p i).1 else (p i).2) *
      signVal (if s then (p j).1 else (p j).2))) = 0
  rw [finite_product_weight_two_nodes w hw i j hij
    (fun q => signVal (if r then q.1 else q.2))
    (fun q => signVal (if s then q.1 else q.2))]
  have hz : (∑ q, w i q * signVal (if r then q.1 else q.2)) = 0 := by
    simp only [w, hi]
    cases r
    · exact (pairWeight_sign_moments ν _).2.1
    · exact (pairWeight_sign_moments ν _).1
  rw [hz, zero_mul]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
