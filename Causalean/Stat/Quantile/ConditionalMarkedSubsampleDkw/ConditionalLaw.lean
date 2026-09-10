import Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

/-!
# Conditional law of a Boolean-marked subsample

This module conditions a finite i.i.d. family of marked real observations on
its complete Boolean word.  It proves that the coordinates selected by a fixed
mark, reindexed in their original order, have the expected finite product law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw

/-- A finite marked iid experiment packages [the marked observation family](hyp:Z), [its
coordinatewise measurability](hyp:measurable), [mutual independence](hyp:indep), and [the common marginal law](hyp:law). -/
structure MarkedIID (Ω : Type*) [MeasurableSpace Ω] (n : ℕ)
    (μ : Measure Ω) (ν : Measure (Bool × ℝ)) where
  Z : Fin n → Ω → Bool × ℝ
  measurable : ∀ i, Measurable (Z i)
  indep : iIndepFun Z μ
  law : ∀ i, μ.map (Z i) = ν

/-- A Boolean mark factorization packages [a positive requested-mark mass](hyp:positive) and
[the identity expressing each marked outcome-set mass as that mass times the outcome law](hyp:joint). -/
structure BooleanMarkFactorization (ν : Measure (Bool × ℝ)) (a : Bool)
    (e : ℝ≥0∞) (ρ : Measure ℝ) : Prop where
  positive : e ≠ 0
  joint : ∀ B : Set ℝ, MeasurableSet B →
    ν {z | z.1 = a ∧ z.2 ∈ B} = e * ρ B

/-- Given [a finite marked iid experiment](hyp:S) and [a Boolean word](hyp:w), [the probability
of its exact-word event equals the product of its coordinatewise mark probabilities](goal). -/
lemma MarkedIID.measure_wordEvent_eq_prod {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    (S : MarkedIID Ω n μ ν) (w : Fin n → Bool) :
    μ (wordEvent S.Z w) = ∏ i, ν {z | z.1 = w i} := by
  -- Apply the finite-intersection characterization of `iIndepFun`, then each marginal map law.
  rw [show wordEvent S.Z w = ⋂ i, S.Z i ⁻¹' {z | z.1 = w i} by
    ext ω
    simp [wordEvent]]
  rw [S.indep.meas_iInter]
  · apply Finset.prod_congr rfl
    intro i _
    calc
      μ (S.Z i ⁻¹' {z | z.1 = w i}) = μ.map (S.Z i) {z | z.1 = w i} :=
        (Measure.map_apply (S.measurable i)
          ((measurableSet_singleton (w i)).preimage measurable_fst)).symm
      _ = ν {z | z.1 = w i} := by rw [S.law i]
  · intro i
    exact ⟨{z | z.1 = w i},
      (measurableSet_singleton (w i)).preimage measurable_fst, rfl⟩

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), [its mass](hyp:e),
[a probability law for selected outcomes](hyp:ρ), [a Boolean mark factorization](hyp:hfac), and
[a coordinate](hyp:i), [conditioning that coordinate's outcome on its requested mark gives the selected-outcome law](goal). -/
lemma MarkedIID.map_snd_cond_mark_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : MarkedIID Ω n μ ν) (a : Bool) (e : ℝ≥0∞) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hfac : BooleanMarkFactorization ν a e ρ) (i : Fin n) :
    Measure.map (fun ω => (S.Z i ω).2)
        μ[|{ω | (S.Z i ω).1 = a}] = ρ := by
  -- Use `Measure.ext`; `cond_apply` turns each measurable test set into the factorization ratio.
  have hmark_meas : MeasurableSet {ω | (S.Z i ω).1 = a} :=
    (measurableSet_singleton a).preimage (S.measurable i).fst
  have hνmark : ν {z | z.1 = a} = e := by
    simpa using hfac.joint Set.univ MeasurableSet.univ
  have hμmark : μ {ω | (S.Z i ω).1 = a} = e := by
    calc
      μ {ω | (S.Z i ω).1 = a} = μ.map (S.Z i) {z | z.1 = a} :=
        (Measure.map_apply (S.measurable i)
          ((measurableSet_singleton a).preimage measurable_fst)).symm
      _ = ν {z | z.1 = a} := by rw [S.law i]
      _ = e := hνmark
  have he_top : e ≠ ∞ := by
    rw [← hνmark]
    exact measure_ne_top ν _
  ext B hB
  rw [Measure.map_apply (S.measurable i).snd hB, cond_apply hmark_meas, hμmark]
  have hjoint :
      μ ({ω | (S.Z i ω).1 = a} ∩ (fun ω => (S.Z i ω).2) ⁻¹' B) = e * ρ B := by
    calc
      μ ({ω | (S.Z i ω).1 = a} ∩ (fun ω => (S.Z i ω).2) ⁻¹' B) =
          μ (S.Z i ⁻¹' {z | z.1 = a ∧ z.2 ∈ B}) := by
            congr 1
      _ = μ.map (S.Z i) {z | z.1 = a ∧ z.2 ∈ B} :=
        (Measure.map_apply (S.measurable i)
          (((measurableSet_singleton a).preimage measurable_fst).inter
            (hB.preimage measurable_snd))).symm
      _ = ν {z | z.1 = a ∧ z.2 ∈ B} := by rw [S.law i]
      _ = e * ρ B := hfac.joint B hB
  rw [hjoint, ← mul_assoc, ENNReal.inv_mul_cancel hfac.positive he_top, one_mul]

/-- Given [a finite marked iid experiment](hyp:S), [a Boolean word](hyp:w), and [positive
probability for its exact-word event](hyp:hw), [all outcome coordinates remain mutually independent after conditioning on that event](goal). -/
lemma MarkedIID.outcomes_iIndep_cond_word {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    [IsProbabilityMeasure μ]
    (S : MarkedIID Ω n μ ν) (w : Fin n → Bool)
    (hw : μ (wordEvent S.Z w) ≠ 0) :
    iIndepFun (fun i ω => (S.Z i ω).2) μ[|wordEvent S.Z w] := by
  -- Swap each pair, invoke `iIndepFun.cond`, and derive nonzero coordinate mark events from `hw`.
  have hprod : ∏ i, ν {z | z.1 = w i} ≠ 0 := by
    rw [← S.measure_wordEvent_eq_prod w]
    exact hw
  have hνmark (i : Fin n) : ν {z | z.1 = w i} ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  have hμmark (i : Fin n) : μ ((fun ω => (S.Z i ω).1) ⁻¹' {w i}) ≠ 0 := by
    calc
      μ ((fun ω => (S.Z i ω).1) ⁻¹' {w i}) =
          μ.map (S.Z i) {z | z.1 = w i} :=
        (Measure.map_apply (S.measurable i)
          ((measurableSet_singleton (w i)).preimage measurable_fst)).symm
      _ = ν {z | z.1 = w i} := by rw [S.law i]
      _ ≠ 0 := hνmark i
  have hindep : iIndepFun (fun i ω => ((S.Z i ω).2, (S.Z i ω).1)) μ := by
    simpa [Function.comp_def] using
      S.indep.comp (fun (_ : Fin n) => fun z : Bool × ℝ => (z.2, z.1))
        (fun _ => measurable_snd.prodMk measurable_fst)
  have hcond := iIndepFun.cond
    (X := fun i ω => (S.Z i ω).2) (Y := fun i ω => (S.Z i ω).1)
    (t := fun i => {w i})
    (fun i => (S.measurable i).fst) hindep hμmark
    (fun i => measurableSet_singleton (w i))
  have hevent : (⋂ i, (fun ω => (S.Z i ω).1) ⁻¹' {w i}) = wordEvent S.Z w := by
    ext ω
    simp [wordEvent]
  rw [hevent] at hcond
  exact hcond

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), [its mass](hyp:e),
[a selected-outcome law](hyp:ρ), [a Boolean mark factorization](hyp:hfac), [a Boolean word](hyp:w),
[positive probability for that word](hyp:hw), and [a selected-coordinate index](hyp:j), [that reindexed selected outcome has law ρ after conditioning on the complete word](goal). -/
lemma MarkedIID.selectedOutcome_map_cond_word_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : MarkedIID Ω n μ ν) (a : Bool) (e : ℝ≥0∞) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hfac : BooleanMarkFactorization ν a e ρ)
    (w : Fin n → Bool) (hw : μ (wordEvent S.Z w) ≠ 0)
    (j : Fin (selectedWordCount w a)) :
    Measure.map (fun ω => selectedOutcomes S.Z w a ω j)
        μ[|wordEvent S.Z w] = ρ := by
  -- `cond_iInter` shows that conditioning on the other marks does not change this marginal.
  let k : Fin n := selectedIndex w a j
  have hk : w k = a := selectedIndex_mark w a j
  have hprod : ∏ i, ν {z | z.1 = w i} ≠ 0 := by
    rw [← S.measure_wordEvent_eq_prod w]
    exact hw
  have hνmark (i : Fin n) : ν {z | z.1 = w i} ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  have hμmark (i : Fin n) : μ ((fun ω => (S.Z i ω).1) ⁻¹' {w i}) ≠ 0 := by
    calc
      μ ((fun ω => (S.Z i ω).1) ⁻¹' {w i}) =
          μ.map (S.Z i) {z | z.1 = w i} :=
        (Measure.map_apply (S.measurable i)
          ((measurableSet_singleton (w i)).preimage measurable_fst)).symm
      _ = ν {z | z.1 = w i} := by rw [S.law i]
      _ ≠ 0 := hνmark i
  have hindep : iIndepFun (fun i ω => ((S.Z i ω).2, (S.Z i ω).1)) μ := by
    simpa [Function.comp_def] using
      S.indep.comp (fun (_ : Fin n) => fun z : Bool × ℝ => (z.2, z.1))
        (fun _ => measurable_snd.prodMk measurable_fst)
  have hevent : (⋂ i, (fun ω => (S.Z i ω).1) ⁻¹' {w i}) = wordEvent S.Z w := by
    ext ω
    simp [wordEvent]
  ext B hB
  change (Measure.map (fun ω => (S.Z k ω).2) μ[|wordEvent S.Z w]) B = ρ B
  rw [Measure.map_apply ((S.measurable k).snd) hB]
  change μ[(fun ω => (S.Z k ω).2) ⁻¹' B | wordEvent S.Z w] = ρ B
  rw [← hevent]
  have hcond := cond_iInter
    (X := fun i ω => (S.Z i ω).2) (Y := fun i ω => (S.Z i ω).1)
    (f := fun i => (fun ω => (S.Z i ω).2) ⁻¹' B)
    (t := fun i => {w i}) (s := {k})
    (fun i => (S.measurable i).fst) hindep
    (fun i _ => ⟨B, hB, rfl⟩) (fun i _ => hμmark i)
    (fun i => measurableSet_singleton (w i))
  have hsingle :
      μ[(fun ω => (S.Z k ω).2) ⁻¹' B |
          ⋂ i, (fun ω => (S.Z i ω).1) ⁻¹' {w i}] =
        μ[(fun ω => (S.Z k ω).2) ⁻¹' B |
          (fun ω => (S.Z k ω).1) ⁻¹' {w k}] := by
    simpa using hcond
  rw [hsingle]
  have hmarg := congrArg (fun m : Measure ℝ => m B)
    (S.map_snd_cond_mark_eq a e ρ hfac k)
  rw [Measure.map_apply (S.measurable k).snd hB] at hmarg
  rw [hk]
  have hmarkset : (fun ω => (S.Z k ω).1) ⁻¹' {a} = {ω | (S.Z k ω).1 = a} := by
    ext ω
    simp
  rw [hmarkset]
  exact hmarg

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), [a Boolean word](hyp:w),
and [positive probability for its exact-word event](hyp:hw), [the reindexed selected outcomes remain mutually independent after conditioning on that event](goal). -/
lemma MarkedIID.selectedOutcomes_iIndep_cond_word {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    [IsProbabilityMeasure μ]
    (S : MarkedIID Ω n μ ν) (a : Bool) (w : Fin n → Bool)
    (hw : μ (wordEvent S.Z w) ≠ 0) :
    iIndepFun (fun j ω => selectedOutcomes S.Z w a ω j)
      μ[|wordEvent S.Z w] := by
  -- Precompose `outcomes_iIndep_cond_word` with the injective selected-coordinate embedding.
  simpa [selectedOutcomes] using
    iIndepFun.precomp (selectedIndex w a).injective
      (S.outcomes_iIndep_cond_word w hw)

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), and [a Boolean word](hyp:w),
[the map from a sample outcome to its reindexed selected outcome vector is measurable](goal). -/
lemma measurable_selectedOutcomes {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    (S : MarkedIID Ω n μ ν) (a : Bool) (w : Fin n → Bool) :
    Measurable (selectedOutcomes S.Z w a) := by
  -- Apply `measurable_pi_lambda`; each coordinate is a projection of `S.measurable`.
  exact measurable_pi_lambda _ fun j => (S.measurable (selectedIndex w a j)).snd

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), [its mass](hyp:e),
[a selected-outcome law](hyp:ρ), [a Boolean mark factorization](hyp:hfac), [a Boolean word](hyp:w),
and [positive probability for that word](hyp:hw), [the reindexed selected outcome vector conditioned on the word has the finite iid product law with marginal ρ](goal). -/
theorem MarkedIID.selectedOutcomes_conditionalLaw {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : MarkedIID Ω n μ ν) (a : Bool) (e : ℝ≥0∞) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hfac : BooleanMarkFactorization ν a e ρ)
    (w : Fin n → Bool) (hw : μ (wordEvent S.Z w) ≠ 0) :
    Measure.map (selectedOutcomes S.Z w a) μ[|wordEvent S.Z w] =
      Measure.pi (fun _ : Fin (selectedWordCount w a) => ρ) := by
  -- Use `iIndepFun.map_fun_eq_pi_map` and rewrite every marginal with the preceding lemma.
  calc
    Measure.map (selectedOutcomes S.Z w a) μ[|wordEvent S.Z w] =
        Measure.pi (fun j =>
          Measure.map (fun ω => selectedOutcomes S.Z w a ω j) μ[|wordEvent S.Z w]) := by
      exact iIndepFun.map_fun_eq_pi_map
        (fun j => (S.measurable (selectedIndex w a j)).snd.aemeasurable)
        (S.selectedOutcomes_iIndep_cond_word a w hw)
    _ = Measure.pi (fun _ : Fin (selectedWordCount w a) => ρ) := by
      congr 1
      funext j
      exact S.selectedOutcome_map_cond_word_eq a e ρ hfac w hw j

end Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw
