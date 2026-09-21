module
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.Chaining

/-!
# Dudley chaining: coarse-scale term

This file bounds the first, coarse-scale part of the dyadic Dudley chain. It
relates the signed empirical sum to empirical distance and proves
`partA_sup_bound`, leaving increment entropy and integral comparison to the
subsequent files.
-/

public section

namespace Causalean.Stat.Concentration

universe v u
open scoped BigOperators
open ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

variable {c : ℝ}
omit [Nonempty ι] in
/-- If [the initial radius is positive](hyp:c_pos), [the empirical function space is totally
bounded](hyp:h), and [every class member has empirical norm at most that radius](hyp:cs), then
[the distance from a class member to its level-n chain approximation is at most the level-n
dyadic radius](goal). -/
lemma empiricalDist_to_chainApprox_le_ej (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (fh : ι) (n : ℕ)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalDist S (F fh) (chainApprox c_pos h fh n) ≤ c / 2 ^ n := by
  by_cases h' : n = 0
  · simpa [chainApprox_def c_pos h, h'] using cs fh
  · rw [chainApprox_def c_pos h, if_neg h']
    exact empiricalDist_coverApprox_le_radius c_pos h fh n

/-- A signed sum of pointwise differences is at most the sample size times
the empirical distance between the two functions. -/
lemma signed_sum_le_empiricalDist (f g : Z → ℝ) (σ : Signs m) :
  ∑ i : Fin m, (σ i : ℝ) * (f (S i) - g (S i)) ≤ m * empiricalDist S f g := by
  calc
  _ = @inner ℝ (EuclideanSpace ℝ (Fin m)) _
      (WithLp.toLp 2 fun i ↦ (σ i : ℝ))
      (WithLp.toLp 2 fun i ↦ f (S i) - g (S i)) := by
    simp [inner]
    apply Finset.sum_congr rfl
    intro i hi
    exact (RCLike.inner_apply' (↑↑(σ i) : ℝ) (f (S i) - g (S i))).symm
  -- Use Cauchy-Schwarz inequality
  _ ≤ (@norm (EuclideanSpace ℝ (Fin m)) _ (WithLp.toLp 2 fun i ↦ (σ i : ℝ))) *
      (@norm (EuclideanSpace ℝ (Fin m)) _
        (WithLp.toLp 2 fun i ↦ f (S i) - g (S i))) :=
    @real_inner_le_norm (EuclideanSpace ℝ (Fin m)) _ _
      (WithLp.toLp 2 fun i ↦ (σ i : ℝ))
      (WithLp.toLp 2 fun i ↦ f (S i) - g (S i))
  _ = m * empiricalDist S f g := by
    simp [norm, empiricalNorm]
    have : (∑ i, (σ i : ℝ) ^ 2) = m := by
      have : (∑ i, (σ i : ℝ) ^ 2) = (∑ i : Fin m, 1) := by
        congr
        ext i
        obtain ⟨σi, hσi⟩ := σ i
        simp at hσi
        simp
        cases hσi with
        | inl h1 => right; rw [h1]; norm_num
        | inr h2 => left; rw [h2]
      rw [this]
      apply (Finset.sum_const 1).trans
      simp
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ←mul_assoc]
    congr
    · rw [←Real.rpow_neg (by simp), ←Real.rpow_one_add' (by simp) (by norm_num)]
      congr
      norm_num
    · norm_num

-- Part A
omit [Nonempty ι] in
/-- For [a function class evaluated on a finite sample](hyp:Z,m,ι,F,S), [a positive empirical
radius](hyp:c), [positivity of that radius](hyp:c_pos), [total boundedness of the empirical
class](hyp:h), [a uniform empirical-radius bound](hyp:cs), [a chaining level](hyp:n), [a sign
vector](hyp:σ), and [a selected function](hyp:fh), [the signed terminal approximation error is
at most the sample size times the dyadic radius at that level](goal). -/
lemma partA_sup_bound (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (n : ℕ) : ∀ (σ : Signs m) (fh : ι),
  ((∑ i : Fin m, (σ i : ℝ) *
    ((F fh) (S i) - chainApprox c_pos h fh n (S i))) ≤ (m : ℝ) * (ej c n)) := by
  intro σ fh
  unfold ej
  apply le_trans (signed_sum_le_empiricalDist (F fh) (chainApprox c_pos h fh n) σ)
  apply mul_le_mul_of_nonneg_left _ (by simp)
  exact empiricalDist_to_chainApprox_le_ej c_pos h fh n cs
  -- Part B (uses Massart's finite-class bound)
  -- We compare increments via the paired class:
  -- {(p_j(f), p_{j-1}(f)) | f ∈ F}.


end Empirical
end Causalean.Stat.Concentration
