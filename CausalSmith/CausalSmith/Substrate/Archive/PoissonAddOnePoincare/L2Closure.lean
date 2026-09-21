/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Finite-support and L² closure for Poisson sequences

This module isolates the pairwise product-law variance identity and the graph-norm density
of finite-support truncations for the forward add-one operator.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators NNReal

namespace CausalSmith.Substrate.PoissonAddOnePoincare

noncomputable section

/-- The forward add-one increment of a real sequence. -/
def addOne (f : Nat → Real) (n : Nat) : Real :=
  f (n + 1) - f n

/-- The variance under a probability law is half the product-law expectation of the squared
difference of two independent copies. -/
theorem variance_eq_half_integral_prod_sq_sub
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (f : alpha → Real) (hf : MemLp f 2 mu) :
    variance f mu =
      (1 / 2 : Real) *
        ∫ z, (f z.1 - f z.2) ^ 2 ∂(mu.prod mu) := by
  -- Expand both sides with `variance_eq_sub`, use product Fubini for `f`, `f²`, and
  -- the cross term, and finish the resulting scalar identity by `ring`.
  rw [variance_eq_sub hf]
  have hfi : Integrable f mu := hf.integrable one_le_two
  have hfsq : Integrable (fun x ↦ f x ^ 2) mu := hf.integrable_sq
  have hfst : Integrable (fun z : alpha × alpha ↦ f z.1 ^ 2) (mu.prod mu) :=
    hfsq.comp_fst mu
  have hsnd : Integrable (fun z : alpha × alpha ↦ f z.2 ^ 2) (mu.prod mu) :=
    hfsq.comp_snd mu
  have hcross : Integrable (fun z : alpha × alpha ↦ f z.1 * f z.2) (mu.prod mu) :=
    hfi.mul_prod hfi
  rw [show (fun z : alpha × alpha ↦ (f z.1 - f z.2) ^ 2) =
      fun z ↦ f z.1 ^ 2 - 2 * (f z.1 * f z.2) + f z.2 ^ 2 by
        funext z
        ring]
  have hInt :
      (∫ z : alpha × alpha,
          f z.1 ^ 2 - 2 * (f z.1 * f z.2) + f z.2 ^ 2 ∂(mu.prod mu)) =
        (∫ z : alpha × alpha, f z.1 ^ 2 ∂(mu.prod mu)) -
          2 * (∫ z : alpha × alpha, f z.1 * f z.2 ∂(mu.prod mu)) +
            ∫ z : alpha × alpha, f z.2 ^ 2 ∂(mu.prod mu) := by
    calc
      _ = (∫ z : alpha × alpha, f z.1 ^ 2 - 2 * (f z.1 * f z.2) ∂(mu.prod mu)) +
          ∫ z : alpha × alpha, f z.2 ^ 2 ∂(mu.prod mu) :=
        integral_add (hfst.sub (hcross.const_mul 2)) hsnd
      _ = ((∫ z : alpha × alpha, f z.1 ^ 2 ∂(mu.prod mu)) -
          ∫ z : alpha × alpha, 2 * (f z.1 * f z.2) ∂(mu.prod mu)) +
            ∫ z : alpha × alpha, f z.2 ^ 2 ∂(mu.prod mu) := by
        rw [integral_sub hfst (hcross.const_mul 2)]
      _ = _ := by rw [integral_const_mul]
  have hfstInt :
      (∫ z : alpha × alpha, f z.1 ^ 2 ∂(mu.prod mu)) = ∫ x, f x ^ 2 ∂mu := by
    simpa using integral_fun_fst (μ := mu) (ν := mu) (fun x ↦ f x ^ 2)
  have hsndInt :
      (∫ z : alpha × alpha, f z.2 ^ 2 ∂(mu.prod mu)) = ∫ x, f x ^ 2 ∂mu := by
    simpa using integral_fun_snd (μ := mu) (ν := mu) (fun x ↦ f x ^ 2)
  have hcrossInt :
      (∫ z : alpha × alpha, f z.1 * f z.2 ∂(mu.prod mu)) =
        (∫ x, f x ∂mu) * ∫ x, f x ∂mu :=
    integral_prod_mul f f
  rw [hInt, hfstInt, hsndInt, hcrossInt]
  simp
  ring

/-- The cutoff of a sequence to indices strictly below `K`. -/
def supportTruncation (K : Nat) (f : Nat → Real) : Nat → Real :=
  fun n ↦ if n < K then f n else 0

/-- A support truncation has finite support. -/
lemma supportTruncation_finiteSupport (K : Nat) (f : Nat → Real) :
    (Function.support (supportTruncation K f)).Finite := by
  refine (Set.finite_Iio K).subset ?_
  intro n hn
  simp only [Function.mem_support] at hn
  by_contra hnot
  have hkn : ¬ n < K := by simpa using hnot
  exact hn (by simp [supportTruncation, hkn])

/-- Every finitely supported real sequence is square-integrable under a Poisson law. -/
lemma memLp_poissonMeasure_of_finiteSupport
    (lambda : NNReal) (f : Nat → Real)
    (hf : (Function.support f).Finite) :
    MemLp f 2 (poissonMeasure lambda) := by
  -- On the discrete domain measurability is automatic. Use the explicit Poisson
  -- integrability criterion; a series supported on the finite support of `f` is summable.
  refine (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).2 ?_
  rw [integrable_poissonMeasure_iff]
  apply summable_of_hasFiniteSupport
  refine hf.subset ?_
  intro n hn
  simp only [Function.mem_support] at hn ⊢
  intro hfn
  simp [hfn] at hn

/-- The add-one increment of a finitely supported real sequence is finitely supported. -/
lemma finiteSupport_addOne (f : Nat → Real)
    (hf : (Function.support f).Finite) :
    (Function.support (addOne f)).Finite := by
  -- The support is contained in `support f ∪ {n | n+1 ∈ support f}`; the successor
  -- preimage of a finite set is finite.
  have hpre : ((fun n : Nat ↦ n + 1) ⁻¹' Function.support f).Finite :=
    hf.preimage (Nat.succ_injective.injOn)
  refine (hf.union hpre).subset ?_
  intro n hn
  simp only [Function.mem_support, Set.mem_union, Set.mem_preimage] at hn ⊢
  by_contra hnot
  simp only [not_or, not_not] at hnot
  exact hn (by simp [addOne, hnot.1, hnot.2])

/-- Poisson support truncations converge to every square-integrable sequence in squared
`L²` distance. -/
theorem supportTruncation_integral_sq_tendsto_zero
    (lambda : NNReal) (f : Nat → Real)
    (hf : MemLp f 2 (poissonMeasure lambda)) :
    Tendsto
      (fun K ↦ ∫ n, (supportTruncation K f n - f n) ^ 2
        ∂(poissonMeasure lambda))
      atTop (nhds 0) := by
  -- Rewrite the integral as the weighted series and identify it with the tail of the
  -- summable nonnegative series supplied by `hf.integrable_sq`.
  let a : Nat → Real := fun n ↦
    Real.exp (-(lambda : Real)) * (lambda : Real) ^ n / Nat.factorial n * f n ^ 2
  have htail : Tendsto
      (fun K ↦ ∑' (n : {n // n ∉ (Finset.range K : Set Nat)}), a n)
      atTop (nhds 0) :=
    (tendsto_tsum_compl_atTop_zero a).comp tendsto_finset_range
  convert htail using 1
  funext K
  have hInt : Integrable
      (fun n ↦ (supportTruncation K f n - f n) ^ 2)
      (poissonMeasure lambda) := by
    refine hf.integrable_sq.mono (measurable_of_countable _).aestronglyMeasurable ?_
    filter_upwards with n
    by_cases hn : n < K
    · simp [supportTruncation, hn, sq_nonneg]
    · simp [supportTruncation, hn]
  rw [integral_poissonMeasure' hInt]
  calc
    _ = ∑' n : Nat,
        ({n : Nat | n ∉ (Finset.range K : Set Nat)}).indicator a n := by
      apply tsum_congr
      intro n
      by_cases hn : n < K <;>
        simp [a, Set.indicator, supportTruncation, hn]
    _ = _ := (tsum_subtype ({n : Nat | n ∉ (Finset.range K : Set Nat)}) a).symm

/-- If a sequence and its add-one increment are square-integrable, support truncations also
converge to its increment in squared `L²` distance. -/
theorem supportTruncation_addOne_integral_sq_tendsto_zero
    (lambda : NNReal) (f : Nat → Real)
    (hf : MemLp f 2 (poissonMeasure lambda))
    (hdf : MemLp (addOne f) 2 (poissonMeasure lambda)) :
    Tendsto
      (fun K ↦ ∫ n,
        (addOne (supportTruncation K f) n - addOne f n) ^ 2
          ∂(poissonMeasure lambda))
      atTop (nhds 0) := by
  -- The identity `f (n+1) = addOne f n + f n` makes the shifted sequence square-integrable.
  -- Its squared norm, together with that of `f`, dominates every truncated add-one error;
  -- pointwise the error is eventually zero, so dominated convergence applies.
  have hshift : MemLp (fun n ↦ f (n + 1)) 2 (poissonMeasure lambda) := by
    have h := hdf.add hf
    convert h using 1
    ext n
    simp [addOne]
  have hbound : Integrable
      (fun n ↦ 2 * (f (n + 1) ^ 2 + f n ^ 2)) (poissonMeasure lambda) :=
    (hshift.integrable_sq.add hf.integrable_sq).const_mul 2
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence
      (μ := poissonMeasure lambda)
      (F := fun K n ↦ (addOne (supportTruncation K f) n - addOne f n) ^ 2)
      (f := fun _ ↦ (0 : Real))
      (fun n ↦ 2 * (f (n + 1) ^ 2 + f n ^ 2))
      (fun K ↦ (measurable_of_countable _).aestronglyMeasurable)
      hbound
      (fun K ↦ by
        filter_upwards with n
        simp only [Real.norm_eq_abs, abs_sq]
        by_cases hn : n < K <;> by_cases hsn : n + 1 < K <;>
          simp [addOne, supportTruncation, hn, hsn] <;>
          nlinarith [sq_nonneg (f n), sq_nonneg (f (n + 1)),
            sq_nonneg (f n + f (n + 1))])
      (by
        filter_upwards with n
        apply tendsto_atTop_of_eventually_const (i₀ := n + 2)
        intro K hK
        have hn : n < K := by omega
        have hsn : n + 1 < K := by omega
        simp [addOne, supportTruncation, hn, hsn]))

/-- On a probability space, squared `L²` convergence of square-integrable functions implies
convergence of their variances. -/
theorem variance_tendsto_of_integral_sq_sub_tendsto_zero
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (f : Nat → alpha → Real) (g : alpha → Real)
    (hf : ∀ K, MemLp (f K) 2 mu) (hg : MemLp g 2 mu)
    (hconv : Tendsto (fun K ↦ ∫ x, (f K x - g x) ^ 2 ∂mu)
      atTop (nhds 0)) :
    Tendsto (fun K ↦ variance (f K) mu) atTop (nhds (variance g mu)) := by
  -- Squared L² convergence implies convergence of means and second moments by
  -- Cauchy–Schwarz on a probability space; conclude from `variance_eq_sub`.
  let d : Nat → alpha → Real := fun K x ↦ f K x - g x
  have hd (K : Nat) : MemLp (d K) 2 mu := by
    have h := (hf K).sub hg
    convert h using 1
    ext x
    rfl
  have hCS (u v : alpha → Real) (hu : MemLp u 2 mu) (hv : MemLp v 2 mu) :
      |∫ x, u x * v x ∂mu| ≤
        Real.sqrt (∫ x, u x ^ 2 ∂mu) * Real.sqrt (∫ x, v x ^ 2 ∂mu) := by
    calc
      |∫ x, u x * v x ∂mu| = ‖∫ x, u x * v x ∂mu‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ x, ‖u x * v x‖ ∂mu := norm_integral_le_integral_norm _
      _ = ∫ x, ‖u x‖ * ‖v x‖ ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_mul]
      _ ≤ (∫ x, ‖u x‖ ^ (2 : Real) ∂mu) ^ ((1 : Real) / 2) *
          (∫ x, ‖v x‖ ^ (2 : Real) ∂mu) ^ ((1 : Real) / 2) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
          (by simpa using hu) (by simpa using hv)
      _ = _ := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        congr 2 <;> apply integral_congr_ae <;> filter_upwards with x <;>
          simp [sq_abs]
  have hsqrt : Tendsto (fun K ↦ Real.sqrt (∫ x, d K x ^ 2 ∂mu)) atTop (nhds 0) := by
    have := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
    convert this using 1
    · funext K
      rfl
    · simp
  have hdconv : Tendsto (fun K ↦ ∫ x, d K x ^ 2 ∂mu) atTop (nhds 0) := by
    simpa [d] using hconv
  have hmeanDiff : Tendsto (fun K ↦ ∫ x, d K x ∂mu) atTop (nhds 0) := by
    refine squeeze_zero_norm
      (a := fun K ↦ Real.sqrt (∫ x, d K x ^ 2 ∂mu)) ?_ hsqrt
    · intro K
      simpa using
        (hCS (d K) (fun _ ↦ (1 : Real)) (hd K) (memLp_const 1))
  have hcross : Tendsto (fun K ↦ ∫ x, g x * d K x ∂mu) atTop (nhds 0) := by
    refine squeeze_zero_norm
      (a := fun K ↦ Real.sqrt (∫ x, g x ^ 2 ∂mu) *
        Real.sqrt (∫ x, d K x ^ 2 ∂mu)) ?_ ?_
    · intro K
      simpa [mul_comm] using hCS g (d K) hg (hd K)
    · simpa using ((tendsto_const_nhds : Tendsto
        (fun _ : Nat ↦ Real.sqrt (∫ x, g x ^ 2 ∂mu)) atTop
        (nhds (Real.sqrt (∫ x, g x ^ 2 ∂mu)))).mul hsqrt)
  have hmean : Tendsto (fun K ↦ ∫ x, f K x ∂mu) atTop (nhds (∫ x, g x ∂mu)) := by
    convert (tendsto_const_nhds.add hmeanDiff) using 1
    · funext K
      rw [← integral_add (hg.integrable one_le_two) ((hd K).integrable one_le_two)]
      apply integral_congr_ae
      filter_upwards with x
      simp [d]
    · simp
  have hsecond : Tendsto (fun K ↦ ∫ x, (f K x) ^ 2 ∂mu)
      atTop (nhds (∫ x, g x ^ 2 ∂mu)) := by
    convert ((tendsto_const_nhds : Tendsto
        (fun _ : Nat ↦ ∫ x, g x ^ 2 ∂mu) atTop (nhds (∫ x, g x ^ 2 ∂mu))).add
          (hdconv.add (hcross.const_mul 2))) using 1
    · funext K
      calc
        (∫ x, f K x ^ 2 ∂mu) =
            ∫ x, g x ^ 2 + (d K x ^ 2 + 2 * (g x * d K x)) ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          simp [d]
          ring
        _ = (∫ x, g x ^ 2 ∂mu) +
            ∫ x, d K x ^ 2 + 2 * (g x * d K x) ∂mu :=
          integral_add hg.integrable_sq
            ((hd K).integrable_sq.add ((MemLp.integrable_mul hg (hd K)).const_mul 2))
        _ = _ := by
          congr 1
          calc
            (∫ x, d K x ^ 2 + 2 * (g x * d K x) ∂mu) =
                (∫ x, d K x ^ 2 ∂mu) + ∫ x, 2 * (g x * d K x) ∂mu :=
              integral_add (hd K).integrable_sq
                ((MemLp.integrable_mul hg (hd K)).const_mul 2)
            _ = _ := by rw [integral_const_mul]
    · simp
  convert hsecond.sub (hmean.pow 2) using 1
  · funext K
    rw [variance_eq_sub (hf K)]
    rfl
  · rw [variance_eq_sub hg]
    rfl

end

end CausalSmith.Substrate.PoissonAddOnePoincare
