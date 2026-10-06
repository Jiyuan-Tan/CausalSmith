/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.BoundedRegularity
public import Causalean.Stat.Concentration.EntropyMethod.FiniteEmpiricalSupremum
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.Positivity

/-!
# Entropy bound for finite empirical suprema

This file applies the one-coordinate Boucheron--Lugosi--Massart estimate to every slice of the
recursive finite empirical supremum.  Boundedness supplies all Bochner-integrability hypotheses;
the recursive deletion family then feeds the resulting costs into deletion-coordinate modified
log-Sobolev tensorization.
-/

public section

open MeasureTheory

namespace Causalean.Stat.Concentration.EntropyMethod

universe u v

private lemma integrable_of_measurable_abs_le'
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsFiniteMeasure mu]
    {f : X → ℝ} {C : ℝ} (hf : Measurable f) (hC : ∀ x, |f x| ≤ C) :
    Integrable f mu := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

private lemma abs_sliceIncrement_le
    {X : Type u} {I : Type v} [Fintype I] [Nonempty I]
    (g : I → X → ℝ) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (n : ℕ) (offset : I → ℝ) (rest : Fin n → X) (x : X) :
    |finiteEmpiricalSliceIncrement I g n offset rest x| ≤ max B 1 := by
  have hwBound : -B ≤ finiteEmpiricalSliceWitness I g n offset rest x :=
    neg_le_of_abs_le (hbound _ x)
  have hlower := finiteEmpiricalSliceWitness_le_increment g n offset rest x
  have hupper' := finiteEmpiricalSliceIncrement_le_one g hupper n offset rest x
  rw [abs_le]
  exact ⟨(neg_le_neg (le_max_left B 1)).trans (hwBound.trans hlower),
    hupper'.trans (le_max_right B 1)⟩

/-- Under [coordinate probability laws `mu`](hyp:mu,hprob), a [nonempty finite score class
`g`](hyp:I,g) whose members are [measurable](hyp:hg) and [bounded by `B`](hyp:hbound), and
[offsets bounded by `A`](hyp:hoffset), the exponential tilt by [any scalar `lam`](hyp:lam) of
the [recursive `n`-coordinate empirical supremum](hyp:n,offset) satisfies [every regularity
condition required by finite entropy tensorization](goal), provided [the bounds are
nonnegative](hyp:hA,hB). -/
theorem finiteEmpiricalTensorizationRegularity
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (mu i)]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) (offset : I → ℝ)
    (hoffset : ∀ i, |offset i| ≤ A) (lam : ℝ) :
    FiniteTensorizationRegularity mu n
      (fun s => Real.exp (lam * finiteEmpiricalSupremum I g n offset s)) := by
  let K := A + (n : ℝ) * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hZ : ∀ s, |finiteEmpiricalSupremum I g n offset s| ≤ K :=
    abs_finiteEmpiricalSupremum_le g hbound n offset hoffset
  apply finiteTensorizationRegularity_of_bounded_positive mu n _
    (by fun_prop) (c := Real.exp (-|lam| * K)) (C := Real.exp (|lam| * K))
    (Real.exp_pos _)
  · intro s
    apply Real.exp_le_exp.mpr
    calc
      -|lam| * K = -(|lam| * K) := by ring
      _ ≤ -( |lam * finiteEmpiricalSupremum I g n offset s|) := by
        rw [abs_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_left (hZ s) (abs_nonneg lam))
      _ ≤ lam * finiteEmpiricalSupremum I g n offset s := neg_abs_le _
  · intro s
    apply Real.exp_le_exp.mpr
    calc
      lam * finiteEmpiricalSupremum I g n offset s ≤
          |lam * finiteEmpiricalSupremum I g n offset s| := le_abs_self _
      _ = |lam| * |finiteEmpiricalSupremum I g n offset s| := abs_mul _ _
      _ ≤ |lam| * K := mul_le_mul_of_nonneg_left (hZ s) (abs_nonneg lam)

/-- Under [a probability law `mu`](hyp:mu), a [nonempty finite centered score class
`g`](hyp:I,g,hmean) whose members are [measurable](hyp:hg) and [bounded in absolute value by
`B`](hyp:hbound) has a [nonnegative expected zero-offset empirical supremum](goal) at every
[coordinate count `n`](hyp:n). -/
theorem integral_finiteEmpiricalSupremum_nonneg
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (n : ℕ) :
    0 ≤ ∫ s, finiteEmpiricalSupremum I g n (fun _ => 0) s
      ∂Measure.pi (fun _ : Fin n => mu) := by
  let i0 : I := Classical.choice ‹Nonempty I›
  let productMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
  have hB : 0 ≤ B := (abs_nonneg (g i0 (Classical.choice
    (nonempty_of_isProbabilityMeasure mu)))).trans (hbound _ _)
  have hscoreMeas : Measurable (finiteEmpiricalScore g n (fun _ => 0) i0) :=
    measurable_finiteEmpiricalScore g hg n (fun _ => 0) i0
  have hscoreBound : ∀ s, |finiteEmpiricalScore g n (fun _ => 0) i0 s| ≤
      (n : ℝ) * B := by
    intro s
    simpa using abs_finiteEmpiricalScore_le g (A := 0) hbound n (fun _ => 0)
      (fun _ => by simp) i0 s
  have hscoreInt : Integrable (finiteEmpiricalScore g n (fun _ => 0) i0)
      productMeasure :=
    integrable_of_measurable_abs_le' hscoreMeas hscoreBound
  have hsupMeas : Measurable (finiteEmpiricalSupremum I g n (fun _ => 0)) :=
    measurable_finiteEmpiricalSupremum g hg n (fun _ => 0)
  have hsupBound : ∀ s, |finiteEmpiricalSupremum I g n (fun _ => 0) s| ≤
      (n : ℝ) * B := by
    intro s
    simpa using abs_finiteEmpiricalSupremum_le g (A := 0) hbound n (fun _ => 0)
      (fun _ => by simp) s
  have hsupInt : Integrable (finiteEmpiricalSupremum I g n (fun _ => 0))
      productMeasure :=
    integrable_of_measurable_abs_le' hsupMeas hsupBound
  have hscoreMean : ∫ s, finiteEmpiricalScore g n (fun _ => 0) i0 s
      ∂productMeasure = 0 := by
    have hcoordInt : ∀ j : Fin n,
        Integrable (fun s : Fin n → X => g i0 (s j)) productMeasure := by
      intro j
      exact integrable_comp_eval
        (integrable_of_measurable_abs_le' (hg i0) (hbound i0))
    have hsumInt : Integrable (fun s : Fin n → X => ∑ j, g i0 (s j))
        productMeasure := by
      simpa using integrable_finsetSum Finset.univ (fun j _ => hcoordInt j)
    unfold finiteEmpiricalScore
    rw [integral_add (integrable_const 0) hsumInt]
    simp only [Pi.zero_apply, integral_zero, zero_add]
    rw [integral_finsetSum Finset.univ (fun j _ => hcoordInt j)]
    apply Finset.sum_eq_zero
    intro j _
    rw [integral_comp_eval (μ := fun _ : Fin n => mu) (i := j)
      (hg i0).aestronglyMeasurable]
    exact hmean i0
  calc
    0 = ∫ s, finiteEmpiricalScore g n (fun _ => 0) i0 s ∂productMeasure :=
      hscoreMean.symm
    _ ≤ ∫ s, finiteEmpiricalSupremum I g n (fun _ => 0) s ∂productMeasure :=
      integral_mono hscoreInt hsupInt fun s =>
        finiteEmpiricalScore_le_supremum g n (fun _ => 0) s i0

/-- Under [a probability law `mu`](hyp:mu), a [nonempty finite measurable score class
`g`](hyp:I,g,hg) [bounded by `B`](hyp:hbound) has [integrable exponential tilts of its
zero-offset empirical supremum](goal) for every [coordinate count `n`](hyp:n) and [tilt
`lam`](hyp:lam). -/
theorem integrable_exp_finiteEmpiricalSupremum
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ}
    (hbound : ∀ i x, |g i x| ≤ B) (n : ℕ) (lam : ℝ) :
    Integrable (fun s => Real.exp
      (lam * finiteEmpiricalSupremum I g n (fun _ => 0) s))
      (Measure.pi (fun _ : Fin n => mu)) := by
  let K := (n : ℝ) * B
  have hZ : ∀ s, |finiteEmpiricalSupremum I g n (fun _ => 0) s| ≤ K := by
    intro s
    simpa [K] using abs_finiteEmpiricalSupremum_le g (A := 0) hbound n
      (fun _ => 0) (fun _ => by simp) s
  apply integrable_of_measurable_abs_le'
    (by fun_prop) (C := Real.exp (|lam| * K))
  intro s
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    lam * finiteEmpiricalSupremum I g n (fun _ => 0) s ≤
        |lam * finiteEmpiricalSupremum I g n (fun _ => 0) s| := le_abs_self _
    _ = |lam| * |finiteEmpiricalSupremum I g n (fun _ => 0) s| := abs_mul _ _
    _ ≤ |lam| * K := mul_le_mul_of_nonneg_left (hZ s) (abs_nonneg lam)

/-- **Finite-slice input to BLM Lemma 12.8.** Under [a probability law `mu`](hyp:mu), fix [a
nonempty finite class](hyp:I) of [measurable scores `g`](hyp:hg), [nonnegative offset and score
bounds `A,B`](hyp:hA,hB), [bounded offsets](hyp:hoffset), and [scores bounded in absolute value
and above by one](hyp:hbound,hupper). If [the scores are centered](hyp:hmean), have [second moment
at most the nonnegative proxy `sigma2`](hyp:hsecond,hsigma), and [the tilt `lam` is
nonnegative](hyp:hlam), then for [every remaining coordinate count `n`](hyp:n) and [remaining
sample `rest`](hyp:rest), [the conditional tilted Bennett deletion cost is at most the BLM factor
times the tilted deletion increment plus half the variance proxy](goal). -/
theorem finiteEmpiricalSlice_phi_cost_le
    {X : Type u} {I : Type v} [MeasurableSpace X] [Fintype I] [Nonempty I]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i))
    {A B sigma2 lam : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ i x, |g i x| ≤ B) (hupper : ∀ i x, g i x ≤ 1)
    (hmean : ∀ i, ∫ x, g i x ∂mu = 0)
    (hsigma : 0 ≤ sigma2) (hsecond : ∀ i, (∫ x, (g i x) ^ 2 ∂mu) ≤ sigma2)
    (hlam : 0 ≤ lam) (n : ℕ) (offset : I → ℝ)
    (hoffset : ∀ i, |offset i| ≤ A) (rest : Fin n → X) :
    (∫ x, Real.exp (lam *
          (finiteEmpiricalSupremum I g n offset rest +
            finiteEmpiricalSliceIncrement I g n offset rest x)) *
        blmPhi (-lam * finiteEmpiricalSliceIncrement I g n offset rest x) ∂mu) ≤
      (blmPhi (-lam) / (1 - Real.exp (-lam) / 2)) *
        ∫ x, Real.exp (lam *
            (finiteEmpiricalSupremum I g n offset rest +
              finiteEmpiricalSliceIncrement I g n offset rest x)) *
          (finiteEmpiricalSliceIncrement I g n offset rest x + sigma2 / 2) ∂mu := by
  let zi := finiteEmpiricalSupremum I g n offset rest
  let Delta := finiteEmpiricalSliceIncrement I g n offset rest
  let Y := finiteEmpiricalSliceWitness I g n offset rest
  let CDelta := max B 1
  let CZ := A + ((n : ℝ) + 1) * B
  have hDeltaMeas : Measurable Delta :=
    measurable_finiteEmpiricalSliceIncrement g hg n offset rest
  have hYMeas : Measurable Y :=
    measurable_finiteEmpiricalSliceWitness g hg n offset rest
  have hDeltaBound : ∀ x, |Delta x| ≤ CDelta :=
    abs_sliceIncrement_le g hbound hupper n offset rest
  have hYBound : ∀ x, |Y x| ≤ B := fun x => hbound _ x
  have hDelta : Integrable Delta mu :=
    integrable_of_measurable_abs_le' hDeltaMeas hDeltaBound
  have hY : Integrable Y mu :=
    integrable_of_measurable_abs_le' hYMeas hYBound
  have hDeltaSq : Integrable (fun x => Delta x ^ 2) mu := by
    apply integrable_of_measurable_abs_le' (hDeltaMeas.pow_const 2)
    intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hDeltaBound x) 2
  have hYSq : Integrable (fun x => Y x ^ 2) mu := by
    apply integrable_of_measurable_abs_le' (hYMeas.pow_const 2)
    intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYBound x) 2
  have hupdated (x : X) : ∀ i, |offset i + g i x| ≤ A + B := by
    intro i
    exact (abs_add_le _ _).trans (add_le_add (hoffset i) (hbound i x))
  have hZBound (x : X) :
      |zi + Delta x| ≤ CZ := by
    have hsup := abs_finiteEmpiricalSupremum_le g hbound n
      (fun i => offset i + g i x) (hupdated x) rest
    have hid : zi + Delta x =
        finiteEmpiricalSupremum I g n (fun i => offset i + g i x) rest := by
      dsimp [zi, Delta, finiteEmpiricalSliceIncrement]
      ring
    rw [hid]
    dsimp [CZ]
    nlinarith
  have hCZ : 0 ≤ CZ := by dsimp [CZ]; positivity
  have hExpMeas : Measurable (fun x => Real.exp (lam * (zi + Delta x))) := by
    fun_prop
  have hExp : Integrable (fun x => Real.exp (lam * (zi + Delta x))) mu := by
    apply integrable_of_measurable_abs_le' hExpMeas
    intro x
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      lam * (zi + Delta x) ≤ |lam * (zi + Delta x)| := le_abs_self _
      _ = |lam| * |zi + Delta x| := abs_mul _ _
      _ ≤ |lam| * CZ := mul_le_mul_of_nonneg_left (hZBound x) (abs_nonneg lam)
  have hExpDelta : Integrable (fun x => Real.exp (lam * (zi + Delta x)) * Delta x) mu := by
    apply integrable_of_measurable_abs_le'
      (C := Real.exp (|lam| * CZ) * CDelta) (hExpMeas.mul hDeltaMeas)
    intro x
    change |Real.exp (lam * (zi + Delta x)) * Delta x| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (lam * (zi + Delta x)) ≤ Real.exp (|lam| * CZ) := by
      apply Real.exp_le_exp.mpr
      calc
        lam * (zi + Delta x) ≤ |lam * (zi + Delta x)| := le_abs_self _
        _ = |lam| * |zi + Delta x| := abs_mul _ _
        _ ≤ |lam| * CZ := mul_le_mul_of_nonneg_left (hZBound x) (abs_nonneg lam)
    exact mul_le_mul he (hDeltaBound x) (abs_nonneg _) (Real.exp_pos _).le
  have hPhiMeas : Measurable (fun x =>
      Real.exp (lam * (zi + Delta x)) * blmPhi (-lam * Delta x)) := by
    dsimp [blmPhi]
    fun_prop
  have hPhi : Integrable (fun x =>
      Real.exp (lam * (zi + Delta x)) * blmPhi (-lam * Delta x)) mu := by
    apply integrable_of_measurable_abs_le'
      (C := Real.exp (|lam| * CZ) *
        (Real.exp (|lam| * CDelta) + |lam| * CDelta + 1)) hPhiMeas
    intro x
    let E := Real.exp (|lam| * CZ)
    let P := Real.exp (|lam| * CDelta) + |lam| * CDelta + 1
    have he : Real.exp (lam * (zi + Delta x)) ≤ E := by
      apply Real.exp_le_exp.mpr
      exact (show lam * (zi + Delta x) ≤ |lam| * CZ by
        calc
          _ ≤ |lam * (zi + Delta x)| := le_abs_self _
          _ = |lam| * |zi + Delta x| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hZBound x) (abs_nonneg lam))
    have harg : |-lam * Delta x| ≤ |lam| * CDelta := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hDeltaBound x) (abs_nonneg lam)
    have hphi : |blmPhi (-lam * Delta x)| ≤ P := by
      dsimp [blmPhi, P]
      calc
        |Real.exp (-lam * Delta x) - (-lam * Delta x) - 1| ≤
            |Real.exp (-lam * Delta x) - (-lam * Delta x)| + |(1 : ℝ)| :=
          abs_sub _ _
        _ ≤ (|Real.exp (-lam * Delta x)| + |-lam * Delta x|) + 1 := by
          simpa using add_le_add_right
            (abs_sub (Real.exp (-lam * Delta x)) (-lam * Delta x)) 1
        _ = Real.exp (-lam * Delta x) + |-lam * Delta x| + 1 := by
          rw [abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (|lam| * CDelta) + |lam| * CDelta + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right (add_le_add
            (Real.exp_le_exp.mpr (le_trans (le_abs_self _) harg)) harg) 1
    change |Real.exp (lam * (zi + Delta x)) * blmPhi (-lam * Delta x)| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he hphi (abs_nonneg _) (Real.exp_pos _).le
  have hLower : ∀ᵐ x ∂mu, Y x ≤ Delta x :=
    ae_of_all _ (finiteEmpiricalSliceWitness_le_increment g n offset rest)
  have hDeltaUpper : ∀ᵐ x ∂mu, Delta x ≤ 1 :=
    ae_of_all _ (finiteEmpiricalSliceIncrement_le_one g hupper n offset rest)
  have hYUpper : ∀ᵐ x ∂mu, Y x ≤ 1 :=
    ae_of_all _ (finiteEmpiricalSliceWitness_le_one g hupper n offset rest)
  have hYMean : 0 ≤ ∫ x, Y x ∂mu := by
    rw [integral_finiteEmpiricalSliceWitness_eq_zero mu g hmean n offset rest]
  have hDeltaMean : 0 ≤ ∫ x, Delta x ∂mu :=
    integral_finiteEmpiricalSliceIncrement_nonneg g hg hbound hupper hmean n offset rest
  have hYSecond : (∫ x, Y x ^ 2 ∂mu) ≤ sigma2 :=
    integral_finiteEmpiricalSliceWitness_sq_le mu g hsecond n offset rest
  exact blm_conditional_phi_cost_le hlam hsigma hDelta hDeltaSq hY hYSq hExp hExpDelta hPhi
    hLower hDeltaUpper hYUpper hYMean hDeltaMean hYSecond

end Causalean.Stat.Concentration.EntropyMethod
