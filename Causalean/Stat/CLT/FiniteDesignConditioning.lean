/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteDesign.MeasureBridge
public import Causalean.Stat.CLT.Martingale.Basic
public import Causalean.Stat.FiniteRaoBlackwell.DesignPushforward
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Conditional expectation for finite randomization designs

This module identifies the explicit fiber average of a statistic under an arbitrary finite design
with measure-theoretic conditional expectation given a finite-valued coarsening.  It is the bridge
needed to turn combinatorial conditional-moment calculations into martingale-array hypotheses.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat

open Causalean.Experimentation.DesignBased
open FiniteRaoBlackwell

variable {Ω B : Type*} [Fintype Ω] [Fintype B]
  [mΩ : MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [mB : MeasurableSpace B] [MeasurableSingletonClass B]

/-- Given [a finite design](hyp:D), [a finite-valued coarsening](hyp:φ), [a real statistic](hyp:f),
and [a coarsened value](hyp:b), the [finite conditional mean](goal) is the design-weighted average
of the statistic over that fiber, totalized to zero on a zero-mass fiber. -/
noncomputable def finiteConditionalMean (D : FiniteDesign Ω) (φ : Ω → B)
    (f : Ω → ℝ) (b : B) : ℝ :=
  conditionalMeanAlongMap D φ 0 (fun ω (_ : Unit) => f ω) b ()

/-- For [a finite design](hyp:D), [a finite-valued coarsening](hyp:φ), and [a real
statistic](hyp:f), [composing its explicit fiber conditional mean with the coarsening equals the
measure-theoretic conditional expectation given that coarsening](goal), almost everywhere under
the design measure. -/
theorem finiteConditionalMean_comp_ae_eq_condExp
    (D : FiniteDesign Ω) (φ : Ω → B) (f : Ω → ℝ) :
    (fun ω => finiteConditionalMean D φ f (φ ω)) =ᵐ[D.toMeasure]
      D.toMeasure[f | MeasurableSpace.comap φ inferInstance] := by
  classical
  let m0 : MeasurableSpace Ω := mΩ
  have hφ : @Measurable Ω B mΩ mB φ := measurable_of_finite φ
  let m : MeasurableSpace Ω := MeasurableSpace.comap φ mB
  have hm : m ≤ m0 := by
    simpa only [m, m0] using hφ.comap_le
  have hg : Measurable[m] (fun ω => finiteConditionalMean D φ f (φ ω)) := by
    exact (measurable_of_finite (finiteConditionalMean D φ f)).comp
      (comap_measurable φ)
  let _ : MeasurableSpace Ω := m0
  let _ : MeasurableSingletonClass Ω := by
    simpa only [m0] using (inferInstance : @MeasurableSingletonClass Ω mΩ)
  have hf : Integrable f D.toMeasure := Integrable.of_finite
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_
    hg.stronglyMeasurable.aestronglyMeasurable
  · intro s _ _
    exact (show Integrable (fun ω => finiteConditionalMean D φ f (φ ω)) D.toMeasure from
      Integrable.of_finite).integrableOn
  · intro s hs _
    have hs0 : MeasurableSet[m0] s := hm s hs
    rw [← integral_indicator hs0, ← integral_indicator hs0,
      FiniteDesign.integral_toMeasure, FiniteDesign.integral_toMeasure]
    rw [MeasurableSpace.measurableSet_comap] at hs
    obtain ⟨t, _ht, rfl⟩ := hs
    let h : Ω → B → ℝ := fun ω b => if b ∈ t then f ω else 0
    have hcond : ∀ b,
        conditionalMeanAlongMap D φ 0 h b b =
          if b ∈ t then finiteConditionalMean D φ f b else 0 := by
      intro b
      by_cases hb : b ∈ t
      · unfold finiteConditionalMean conditionalMeanAlongMap fiberNumerator
        by_cases hmass : fiberMass D φ b = 0
        · simp [hb, hmass]
        · simp only [h, hb, hmass, if_true, if_false]
      · simp only [hb, if_false, h]
        unfold conditionalMeanAlongMap fiberNumerator
        by_cases hmass : fiberMass D φ b = 0
        · simp [hmass]
        · simp only [hmass, if_false]
          have hnum : (∑ ω, if φ ω = b then D.p ω * (if b ∈ t then f ω else 0)
              else 0) = 0 := by simp [hb]
          rw [hnum, zero_div]
    calc
      D.E (Set.indicator (φ ⁻¹' t)
          (fun ω => finiteConditionalMean D φ f (φ ω))) =
          D.E (fun ω => conditionalMeanAlongMap D φ 0 h (φ ω) (φ ω)) := by
            apply D.E_congr
            intro ω
            rw [hcond]
            by_cases hω : φ ω ∈ t <;> simp [Set.indicator, hω]
      _ = D.E (fun ω => h ω (φ ω)) :=
        E_conditionalMeanAlongMap_comp D φ 0 h id
      _ = D.E (Set.indicator (φ ⁻¹' t) f) := by
        apply D.E_congr
        intro ω
        by_cases hω : φ ω ∈ t <;> simp [h, Set.indicator, hω]

section DoobArray

open Filter ProbabilityTheory

variable {Ωr : ℕ → Type*} {mΩr : (n : ℕ) → MeasurableSpace (Ωr n)}
  {μ : (n : ℕ) → Measure (Ωr n)} [∀ n, IsProbabilityMeasure (μ n)]

/-- Given [row probability spaces](hyp:Ωr,μ), [finite row lengths](hyp:rowLength),
[one filtration per row](hyp:filtration), and [square-integrable terminal
statistics](hyp:terminal,hterminal), the [Doob martingale-difference array](goal) has increment
`k` equal to the difference between the terminal statistic's conditional expectations after and
before reveal `k`. -/
noncomputable def doobMartingaleDifferenceArray
    (rowLength : ℕ → ℕ)
    (filtration : (n : ℕ) → Filtration ℕ (mΩr n))
    (terminal : (n : ℕ) → Ωr n → ℝ)
    (hterminal : ∀ n, MemLp (terminal n) 2 (μ n)) :
    MartingaleDifferenceArray Ωr μ where
  rowLength := rowLength
  increment := fun n k ω =>
    (μ n)[terminal n | filtration n (k + 1)] ω -
      (μ n)[terminal n | filtration n k] ω
  filtration := filtration
  adapted := by
    intro n k _hk
    exact stronglyMeasurable_condExp.sub
      (stronglyMeasurable_condExp.mono ((filtration n).mono (Nat.le_succ k)))
  squareIntegrable := by
    intro n k _hk
    exact (hterminal n).condExp (by norm_num) |>.sub
      ((hterminal n).condExp (by norm_num))
  condExp_zero := by
    intro n k _hk
    let M : ℕ → Ωr n → ℝ := fun j => (μ n)[terminal n | filtration n j]
    have hM : Martingale M (filtration n) (μ n) :=
      martingale_condExp (terminal n) (filtration n) (μ n)
    calc
      (μ n)[(fun ω => M (k + 1) ω - M k ω) | filtration n k] =ᵐ[μ n]
          (μ n)[M (k + 1) | filtration n k] - (μ n)[M k | filtration n k] :=
        condExp_sub (hM.integrable (k + 1)) (hM.integrable k) (filtration n k)
      _ =ᵐ[μ n] M k - M k :=
        (hM.condExp_ae_eq (Nat.le_succ k)).sub (hM.condExp_ae_eq le_rfl)
      _ =ᵐ[μ n] 0 := by simp

/-- For [a Doob martingale-difference array](hyp:rowLength,filtration,terminal,hterminal) and
[a row](hyp:n), [the sum of its active increments is the terminal conditional expectation at the
row endpoint minus its initial conditional expectation](goal). -/
theorem doobMartingaleDifferenceArray_rowSum
    (rowLength : ℕ → ℕ)
    (filtration : (n : ℕ) → Filtration ℕ (mΩr n))
    (terminal : (n : ℕ) → Ωr n → ℝ)
    (hterminal : ∀ n, MemLp (terminal n) 2 (μ n)) (n : ℕ) :
    (doobMartingaleDifferenceArray rowLength filtration terminal hterminal).rowSum n =
      fun ω => (μ n)[terminal n | filtration n (rowLength n)] ω -
        (μ n)[terminal n | filtration n 0] ω := by
  funext ω
  let g : ℕ → ℝ := fun k => (μ n)[terminal n | filtration n k] ω
  have htel : ∀ r : ℕ, (∑ k ∈ Finset.range r, (g (k + 1) - g k)) = g r - g 0 := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
        rw [Finset.sum_range_succ, ihr]
        ring
  simpa [MartingaleDifferenceArray.rowSum, doobMartingaleDifferenceArray, g] using
    htel (rowLength n)

/-- For [a martingale-difference array](hyp:A), [a truncation threshold](hyp:ε), and [a
row](hyp:n), if [every active increment is at most that threshold in absolute value](hyp:hbound),
then [the row's conditional Lindeberg sum vanishes almost everywhere](goal). -/
theorem conditionalLindeberg_ae_eq_zero_of_increment_le
    (A : MartingaleDifferenceArray Ωr μ) (ε : ℝ) (n : ℕ)
    (hbound : ∀ k, k < A.rowLength n → ∀ ω, |A.increment n k ω| ≤ ε) :
    A.conditionalLindeberg ε n =ᵐ[μ n] 0 := by
  have hterm : ∀ k, k < A.rowLength n → A.lindebergTerm ε n k =ᵐ[μ n] 0 := by
    intro k hk
    have hzero : (fun ω => if ε < |A.increment n k ω|
        then (A.increment n k ω) ^ 2 else 0) = 0 := by
      funext ω
      simp [not_lt.mpr (hbound k hk ω)]
    unfold MartingaleDifferenceArray.lindebergTerm
    rw [hzero]
    simp
  have hall : ∀ᵐ ω ∂(μ n), ∀ k ∈ Finset.range (A.rowLength n),
      A.lindebergTerm ε n k ω = 0 :=
    (Finset.eventually_all _).mpr fun k hk =>
      hterm k (Finset.mem_range.mp hk)
  filter_upwards [hall] with ω hω
  unfold MartingaleDifferenceArray.conditionalLindeberg
  simp only [Finset.sum_apply, Pi.zero_apply]
  exact Finset.sum_eq_zero fun k hk => hω k hk

/-- For [a martingale-difference array](hyp:A), if [its active increments are eventually
uniformly smaller than every positive threshold](hyp:hsmall), then [its conditional Lindeberg
condition holds](goal). -/
theorem conditionalLindeberg_tendstoInProbability_of_eventually_uniformly_small
    (A : MartingaleDifferenceArray Ωr μ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ k, k < A.rowLength n → ∀ ω, |A.increment n k ω| ≤ ε) :
    ∀ ε : ℝ, 0 < ε →
      Modes.TendstoInProbability μ (A.conditionalLindeberg ε) atTop
        (fun _ _ => 0) := by
  intro ε hε
  rw [Modes.tendstoInProbability_iff_norm]
  simp only [Real.norm_eq_abs]
  intro δ hδ
  have hevent : ∀ᶠ n in atTop,
      μ n {ω | δ ≤ |A.conditionalLindeberg ε n ω - 0|} = 0 := by
    filter_upwards [hsmall ε hε] with n hn
    have hzero := conditionalLindeberg_ae_eq_zero_of_increment_le A ε n hn
    have hset : {ω | δ ≤ |A.conditionalLindeberg ε n ω - 0|} =ᵐ[μ n]
        (∅ : Set (Ωr n)) := by
      filter_upwards [hzero] with ω hω
      simp only [Pi.zero_apply] at hω
      change (δ ≤ |A.conditionalLindeberg ε n ω - 0|) = False
      apply propext
      rw [hω]
      simp only [sub_zero, abs_zero, iff_false]
      exact not_le.mpr hδ
    rw [measure_congr hset]
    simp
  exact (Filter.tendsto_congr' hevent).mpr tendsto_const_nhds

end DoobArray

end Causalean.Stat
