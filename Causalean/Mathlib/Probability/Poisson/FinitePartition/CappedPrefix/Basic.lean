module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.CountFibre
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.CountPartition
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.Uniform

/-!
# Capped marked Poisson prefix identities

Finite Poisson count mixtures from a fixed iid sample agree with the
nonoverflow restriction of the marked Poisson finite-prefix law.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- For [an iid observation law](hyp:μ), [a sample size](hyp:n),
[a fixed admissible prefix length](hyp:m,h), [a prefix statistic](hyp:g), and
[an integrability condition for that statistic](hyp:hg), [averaging over uniform
permutations and fair mark vectors has the paired iid prefix expectation](goal). -/
theorem perm_mark_prefix_average_integral
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (n m : ℕ) (h : m ≤ n)
    (g : FiniteSample (X × Bool) → ℝ)
    (hg : Integrable (fun y : Fin n → X × Bool => g (prefixOfLE y m h))
      (Measure.pi (fun _ : Fin n => μ.prod fairBoolLaw))) :
    (∫ x : Fin n → X,
      ∑ perm : Equiv.Perm (Fin n),
        ∑ marks : Fin n → Bool,
          ((1 : ℝ) / ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
            (Fintype.card (Fin n → Bool) : ℝ))) *
            g (prefixOfLE (fun i => (x (perm i), marks i)) m h)
      ∂Measure.pi (fun _ : Fin n => μ)) =
    ∫ y : Fin n → X × Bool, g (prefixOfLE y m h)
      ∂Measure.pi (fun _ : Fin n => μ.prod fairBoolLaw) := by
  classical
  let ν : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => μ)
  let ρ : Measure (Fin n → Bool) := Measure.pi (fun _ : Fin n => fairBoolLaw)
  let c : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
  let d : ℝ := (Fintype.card (Fin n → Bool) : ℝ)
  have hmass (marks : Fin n → Bool) : ρ.real {marks} = 1 / d := by
    change (Measure.pi (fun _ : Fin n => fairBoolLaw)).real {marks} = _
    rw [fairMarkPi_eq_uniform_sum]
    simp [Measure.real, Measure.smul_apply, Finset.sum_apply, d]
  have hmap (perm : Equiv.Perm (Fin n)) :
      Measurable (fun z : (Fin n → X) × (Fin n → Bool) =>
        fun i => (z.1 (perm i), z.2 i)) := by
    fun_prop
  have hInt (perm : Equiv.Perm (Fin n)) :
      Integrable (fun z : (Fin n → X) × (Fin n → Bool) =>
        g (prefixOfLE (fun i => (z.1 (perm i), z.2 i)) m h)) (ν.prod ρ) := by
    change Integrable ((fun y : Fin n → X × Bool => g (prefixOfLE y m h)) ∘
      (fun z : (Fin n → X) × (Fin n → Bool) =>
        fun i => (z.1 (perm i), z.2 i))) (ν.prod ρ)
    exact (integrable_map_measure (by
      rw [map_permuted_marked_pi μ n perm]
      exact hg.aestronglyMeasurable) (hmap perm).aemeasurable).mp (by
        rw [map_permuted_marked_pi μ n perm]
        exact hg)
  have hslice (perm : Equiv.Perm (Fin n)) (x : Fin n → X) :
      (∫ marks : Fin n → Bool,
        g (prefixOfLE (fun i => (x (perm i), marks i)) m h) ∂ρ) =
      ∑ marks : Fin n → Bool,
        (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) m h) := by
    rw [integral_fintype (Integrable.of_finite)]
    simp_rw [hmass, smul_eq_mul]
  have hsection (perm : Equiv.Perm (Fin n)) :
      Integrable (fun x : Fin n → X =>
        ∑ marks : Fin n → Bool,
          (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) m h)) ν := by
    convert (hInt perm).integral_prod_left using 1
    funext x
    exact (hslice perm x).symm
  have hperm (perm : Equiv.Perm (Fin n)) :
      (∫ x : Fin n → X,
        ∑ marks : Fin n → Bool,
          (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) m h) ∂ν) =
      ∫ y : Fin n → X × Bool, g (prefixOfLE y m h)
        ∂Measure.pi (fun _ : Fin n => μ.prod fairBoolLaw) := by
    calc
      _ = ∫ z : (Fin n → X) × (Fin n → Bool),
          g (prefixOfLE (fun i => (z.1 (perm i), z.2 i)) m h) ∂ν.prod ρ := by
            rw [integral_prod _ (hInt perm)]
            simp_rw [hslice]
      _ = _ := by
        calc
          _ = ∫ y : Fin n → X × Bool, g (prefixOfLE y m h)
              ∂Measure.map
                (fun z : (Fin n → X) × (Fin n → Bool) =>
                  fun i => (z.1 (perm i), z.2 i)) (ν.prod ρ) := by
                  exact (integral_map (hmap perm).aemeasurable (by
                    rw [map_permuted_marked_pi μ n perm]
                    exact hg.aestronglyMeasurable)).symm
          _ = _ := by rw [map_permuted_marked_pi μ n perm]
  have hc : c ≠ 0 := by
    unfold c
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin n))).ne'
  have hd : d ≠ 0 := by
    unfold d
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin n → Bool)).ne'
  calc
    _ = ∫ x : Fin n → X,
        ∑ perm : Equiv.Perm (Fin n),
          (1 / c) * ∑ marks : Fin n → Bool,
            (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) m h) ∂ν := by
          congr 1
          funext x
          apply Finset.sum_congr rfl
          intro perm _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro marks _
          dsimp [c, d]
          ring
    _ = ∑ perm : Equiv.Perm (Fin n),
          (1 / c) * (∫ x : Fin n → X,
            ∑ marks : Fin n → Bool,
              (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) m h) ∂ν) := by
          rw [integral_finsetSum Finset.univ]
          · simp_rw [integral_const_mul]
          · intro perm _
            exact (hsection perm).const_mul _
    _ = _ := by
      simp_rw [hperm]
      rw [← Finset.sum_mul]
      have hweights : (∑ _perm : Equiv.Perm (Fin n), (1 / c)) = 1 := by
        simp [c, div_eq_mul_inv, hc]
      rw [hweights, one_mul]

/-- For [an iid marked observation law](hyp:ν), [a Poisson mean](hyp:lam),
[a count cap](hyp:n), [a finite-sample statistic](hyp:g), and [an integrability condition](hyp:hg),
[the finite Poisson count mixture
of admissible prefixes equals its nonoverflow finite Poisson expectation](goal). -/
theorem poisson_prefix_mixture_integral
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (lam : ℝ≥0) (n : ℕ)
    (g : FiniteSample Y → ℝ)
    (hg : Integrable g (finitePoissonSampleLaw ν lam)) :
    (∑ M : Fin (n + 1),
      (poissonMeasure lam {M.val}).toReal *
        ∫ y : Fin n → Y,
          g (prefixOfLE y M.val (Nat.le_of_lt_succ M.isLt))
          ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ z : FiniteSample Y,
        if z.count ≤ n then g z else 0
        ∂finitePoissonSampleLaw ν lam := by
  /- Apply `poisson_nonoverflow_integral_eq_sum_count_fibres` on the right,
  then rewrite each count fibre with `poisson_prefix_count_fibre_integral`.
  The latter already handles zero-Poisson-mass fibres. -/
  rw [poisson_nonoverflow_integral_eq_sum_count_fibres ν lam n g hg]
  congr 1
  funext M
  exact (poisson_prefix_count_fibre_integral ν lam n M.val
    (Nat.le_of_lt_succ M.isLt) g hg).symm

/-- For [a probability observation law](hyp:μ), [a Poisson mean](hyp:lam),
[a sample size](hyp:n), [a real statistic of finite fair-marked samples](hyp:g), and
[its integrability under the Poisson finite-sample law of fair-marked
observations](hyp:hg), [the expectation over an iid sample of size `n` of the mixture
that draws a prefix length `M ≤ n` with its Poisson probability, a uniformly random
ordering of the sample, and uniformly random Boolean marks, and evaluates the statistic
at the length-`M` prefix of the reordered marked sample, equals the expectation of the
statistic under the Poisson finite-sample law restricted to samples of at most `n`
points](goal). The Poisson weights of lengths above `n` are dropped on both sides, so
neither side is renormalized. -/
theorem capped_marked_prefix_integral
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (lam : ℝ≥0) (n : ℕ)
    (g : FiniteSample (X × Bool) → ℝ)
    (hg : Integrable g (finitePoissonSampleLaw (μ.prod fairBoolLaw) lam)) :
    (∫ x : Fin n → X,
      ∑ M : Fin (n + 1),
        ∑ perm : Equiv.Perm (Fin n),
          ∑ marks : Fin n → Bool,
            ((poissonMeasure lam {M.val}).toReal /
              ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
                (Fintype.card (Fin n → Bool) : ℝ))) *
              g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
                (Nat.le_of_lt_succ M.isLt))
      ∂Measure.pi (fun _ : Fin n => μ)) =
    ∫ z : FiniteSample (X × Bool),
      if z.count ≤ n then g z else 0
      ∂finitePoissonSampleLaw (μ.prod fairBoolLaw) lam := by
  /-
  For each admissible `M`, use `perm_mark_prefix_average_integral` to remove
  the finite permutation and mark sums. Pull the Poisson mass outside the
  integral and apply `poisson_prefix_mixture_integral` with
  `ν = μ.prod fairBoolLaw`. Derive each fixed-count integrability premise by
  restricting `hg` to the count fibre via
  `finitePoissonSampleLaw_restrict_count_eq`; zero Poisson mass fibres may be
  discarded directly.
  -/
  classical
  let ν : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => μ)
  let ρ : Measure (Fin n → Bool) := Measure.pi (fun _ : Fin n => fairBoolLaw)
  let c : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
  let d : ℝ := (Fintype.card (Fin n → Bool) : ℝ)
  have hmark (marks : Fin n → Bool) : ρ.real {marks} = 1 / d := by
    change (Measure.pi (fun _ : Fin n => fairBoolLaw)).real {marks} = _
    rw [fairMarkPi_eq_uniform_sum]
    simp [Measure.real, Measure.smul_apply, Finset.sum_apply, d]
  have hfixed (M : Fin (n + 1))
      (hmass : poissonMeasure lam {M.val} ≠ 0) :
      Integrable (fun y : Fin n → X × Bool =>
        g (prefixOfLE y M.val (Nat.le_of_lt_succ M.isLt)))
        (Measure.pi (fun _ : Fin n => μ.prod fairBoolLaw)) :=
    integrable_prefix_of_nonzero_poisson_count
      (μ.prod fairBoolLaw) lam n M.val (Nat.le_of_lt_succ M.isLt) g hg hmass
  have havg (M : Fin (n + 1))
      (hmass : poissonMeasure lam {M.val} ≠ 0) :
      Integrable (fun x : Fin n → X =>
        ∑ perm : Equiv.Perm (Fin n),
          ∑ marks : Fin n → Bool,
            (1 / (c * d)) *
              g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
                (Nat.le_of_lt_succ M.isLt))) ν := by
    apply integrable_finsetSum
    intro perm _
    have hmap : Measurable (fun z : (Fin n → X) × (Fin n → Bool) =>
        fun i => (z.1 (perm i), z.2 i)) := by fun_prop
    have hprod : Integrable (fun z : (Fin n → X) × (Fin n → Bool) =>
        g (prefixOfLE (fun i => (z.1 (perm i), z.2 i)) M.val
          (Nat.le_of_lt_succ M.isLt))) (ν.prod ρ) := by
      change Integrable ((fun y : Fin n → X × Bool =>
        g (prefixOfLE y M.val (Nat.le_of_lt_succ M.isLt))) ∘
        (fun z : (Fin n → X) × (Fin n → Bool) =>
          fun i => (z.1 (perm i), z.2 i))) (ν.prod ρ)
      exact (integrable_map_measure (by
        rw [map_permuted_marked_pi μ n perm]
        exact (hfixed M hmass).aestronglyMeasurable) hmap.aemeasurable).mp (by
          rw [map_permuted_marked_pi μ n perm]
          exact hfixed M hmass)
    have hslice (x : Fin n → X) :
        (∫ marks : Fin n → Bool,
          g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
            (Nat.le_of_lt_succ M.isLt)) ∂ρ) =
        ∑ marks : Fin n → Bool,
          (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
            (Nat.le_of_lt_succ M.isLt)) := by
      rw [integral_fintype (Integrable.of_finite)]
      simp_rw [hmark, smul_eq_mul]
    have hsection : Integrable (fun x : Fin n → X =>
        ∑ marks : Fin n → Bool,
          (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
            (Nat.le_of_lt_succ M.isLt))) ν := by
      convert hprod.integral_prod_left using 1
      funext x
      exact (hslice x).symm
    have heq : (fun x : Fin n → X =>
        ∑ marks : Fin n → Bool,
          (1 / (c * d)) * g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
            (Nat.le_of_lt_succ M.isLt))) =
        (fun x : Fin n → X => (1 / c) *
          ∑ marks : Fin n → Bool,
            (1 / d) * g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
              (Nat.le_of_lt_succ M.isLt))) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro marks _
      ring
    rw [heq]
    exact hsection.const_mul _
  have hterm (M : Fin (n + 1)) :
      Integrable (fun x : Fin n → X =>
        ∑ perm : Equiv.Perm (Fin n),
          ∑ marks : Fin n → Bool,
            ((poissonMeasure lam {M.val}).toReal / (c * d)) *
              g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
                (Nat.le_of_lt_succ M.isLt))) ν := by
    by_cases hmass : poissonMeasure lam {M.val} = 0
    · simp [hmass]
    · convert (havg M hmass).const_mul (poissonMeasure lam {M.val}).toReal using 1
      funext x
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro perm _
      apply Finset.sum_congr rfl
      intro marks _
      ring
  calc
    _ = ∑ M : Fin (n + 1),
          ∫ x : Fin n → X,
            ∑ perm : Equiv.Perm (Fin n),
              ∑ marks : Fin n → Bool,
                ((poissonMeasure lam {M.val}).toReal / (c * d)) *
                  g (prefixOfLE (fun i => (x (perm i), marks i)) M.val
                    (Nat.le_of_lt_succ M.isLt)) ∂ν := by
          exact integral_finsetSum Finset.univ (fun M _ => hterm M)
    _ = ∑ M : Fin (n + 1),
          (poissonMeasure lam {M.val}).toReal *
            ∫ y : Fin n → X × Bool,
              g (prefixOfLE y M.val (Nat.le_of_lt_succ M.isLt))
                ∂Measure.pi (fun _ : Fin n => μ.prod fairBoolLaw) := by
          apply Finset.sum_congr rfl
          intro M _
          by_cases hmass : poissonMeasure lam {M.val} = 0
          · simp [hmass]
          · have hav := perm_mark_prefix_average_integral μ n M.val
              (Nat.le_of_lt_succ M.isLt) g (hfixed M hmass)
            rw [← hav, ← integral_const_mul]
            congr 1
            funext x
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro perm _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro marks _
            dsimp [c, d]
            ring
    _ = _ := poisson_prefix_mixture_integral
      (μ.prod fairBoolLaw) lam n g hg

end Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix
