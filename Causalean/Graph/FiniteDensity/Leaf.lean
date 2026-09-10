import Causalean.Graph.FiniteDensity.Factorization

/-!
# Normalized leaf elimination

This module proves the one-coordinate analytic step behind finite Bayesian-network
marginalization: a normalized factor at a leaf can be integrated away without changing the
product of the remaining factors.
-/

open scoped ENNReal
open Set Function
open MeasureTheory

noncomputable section

namespace Causalean.Graph.FiniteDensity

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.DAG V}

/-- A [finite DAG](hyp:G), a [node](hyp:k), and a [finite node set](hyp:S) determine [the property
that the node is a leaf within that set](goal). -/
def IsLeafIn (G : Causalean.DAG V) (k : V) (S : Finset V) : Prop :=
  k ∈ S ∧ ∀ l ∈ S, l ≠ k → ¬ G.edge k l

/-- A [DAG factorization](hyp:B), [two distinct nodes](hyp:hkl), [evidence that the updated node
is not a parent of the other](hyp:hkpar), a [full assignment](hyp:v), and a [new coordinate value](hyp:x)
[leave the other node's local factor unchanged](goal). -/
theorem Factorization.factor_update_eq_of_ne_of_not_parent
    (B : Factorization G X μ) {k l : V} (hkl : k ≠ l) (hkpar : k ∉ G.parents l)
    (v : ∀ i, X i) (x : X k) :
    B.factor l (Function.update v k x) = B.factor l v := by
  -- Apply locality and show every coordinate in `insert l (parents l)` is untouched by the update.
  apply B.local_factor l
  intro i hi
  have hik : i ≠ k := by
    intro h
    subst i
    exact (Finset.mem_insert.mp hi).elim hkl hkpar
  exact Function.update_of_ne hik x v

/-- A [DAG factorization](hyp:B), a [leaf of a finite node set](hyp:hleaf), a [full assignment](hyp:v),
and a [new leaf-coordinate value](hyp:x) [leave the product of all remaining factors unchanged](goal). -/
theorem Factorization.partialDensity_erase_update_leaf
    (B : Factorization G X μ) {S : Finset V} {k : V} (hleaf : IsLeafIn G k S)
    (v : ∀ i, X i) (x : X k) :
    B.partialDensity (S.erase k) (Function.update v k x) =
      B.partialDensity (S.erase k) v := by
  -- Compare factors pointwise; leafhood rules out `k` as a parent of every retained node.
  unfold Factorization.partialDensity
  apply Finset.prod_congr rfl
  intro l hl
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  have hlS : l ∈ S := (Finset.mem_erase.mp hl).2
  apply B.factor_update_eq_of_ne_of_not_parent hlk.symm
  intro hkpar
  exact hleaf.2 l hlS hlk (G.mem_parents.mp hkpar)

/-- A [DAG factorization](hyp:B), a [leaf within a finite node set](hyp:hleaf), and a [fixed
assignment of the other coordinates](hyp:v) [show that integrating the normalized leaf factor
removes exactly that factor from the product](goal). -/
theorem Factorization.lintegral_partialDensity_leaf
    (B : Factorization G X μ) {S : Finset V} {k : V} (hleaf : IsLeafIn G k S)
    (v : ∀ i, X i) :
    ∫⁻ x, B.partialDensity S (Function.update v k x) ∂μ k =
      B.partialDensity (S.erase k) v := by
  -- Split off the leaf factor, freeze the erased product, and use `B.normalized_factor k`.
  calc
    ∫⁻ x, B.partialDensity S (Function.update v k x) ∂μ k =
        ∫⁻ x, B.factor k (Function.update v k x) *
          B.partialDensity (S.erase k) (Function.update v k x) ∂μ k := by
      congr 1
      funext x
      unfold Factorization.partialDensity
      exact (Finset.mul_prod_erase S
        (fun i ↦ B.factor i (Function.update v k x)) hleaf.1).symm
    _ = ∫⁻ x, B.factor k (Function.update v k x) *
          B.partialDensity (S.erase k) v ∂μ k := by
      congr 1
      funext x
      rw [B.partialDensity_erase_update_leaf hleaf]
    _ = (∫⁻ x, B.factor k (Function.update v k x) ∂μ k) *
          B.partialDensity (S.erase k) v := by
      rw [lintegral_mul_const]
      exact (B.measurable_factor k).comp (measurable_update v)
    _ = B.partialDensity (S.erase k) v := by
      rw [B.normalized_factor k v, one_mul]

end Causalean.Graph.FiniteDensity
