module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.PredictiveLaw
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.PoissonTail

/-!
# Marked-Poisson Taylor envelopes

This module uses mixed-moment matching to remove low-degree coefficients and bounds the remaining one-parameter four-rate envelope.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/- The two remaining steps of the comparison are kept separate.  The first
uses the matched moments to discard the low-degree signed coefficients in
each singleton mass.  The second exchanges the nonnegative coefficient sum
with the finite prior integral, then reindexes the four rates by `Fin 4` and
applies `fourRateFactorialTail_le`. -/

/-- An [experiment size](hyp:n), [parameter triple](hyp:θ), and [four Taylor indices](hyp:t,u,v,w) determine [the nonnegative marked-Poisson envelope coefficient](goal) by [multiplying the four factorial-weighted rate powers](step:1). -/
noncomputable def markedEnvelopeCoeff (n : ℝ) (θ : MarkedParam)
    (t u v w : ℕ) : ℝ :=
  (n * θ.1) ^ t / (Nat.factorial t : ℝ) *
    (n * θ.1 * θ.2.1 * θ.2.2) ^ u / (Nat.factorial u : ℝ) *
    (n * θ.1 * θ.2.1 * (1 - θ.2.2)) ^ v / (Nat.factorial v : ℝ) *
    (n * θ.1 * (1 - θ.2.1)) ^ w / (Nat.factorial w : ℝ)

/- Rewrite the singleton series using `markedEnvelopeCoeff` with the sign
  `(-1)^t`.  Subtract the two prior series.  For `t+u+v+w ≤ 3K`, use
  `integral_markedRateProduct_match`; for the other terms, bound the absolute
  difference by the sum of the two nonnegative integrals.  Finite support
  supplies summability of every coefficient series. -/

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size](hyp:hn), [nonnegative overlap margin](hyp:hε), [bounded triple priors](hyp:T), and [three observed counts](hyp:u,v,w) give [an unmatched-envelope bound on their predictive singleton difference](goal). -/
theorem abs_predictiveLaw_singleton_diff_le_unmatchedEnvelope
    {K : ℕ} (hK : 1 ≤ K) {b ε gap n : ℝ}
    (hn : 0 ≤ n) (hε : 0 ≤ ε)
    (T : TriplePriors K b ε gap) (u v w : ℕ) :
    |(predictiveLaw n T.ν₀).real {((u, v), w)} -
      (predictiveLaw n T.ν₁).real {((u, v), w)}| ≤
      ∑' t : ℕ, if 3 * K < t + u + v + w then
        (∫ θ, markedEnvelopeCoeff n θ t u v w ∂T.ν₀) +
        (∫ θ, markedEnvelopeCoeff n θ t u v w ∂T.ν₁)
      else 0 := by
  haveI := T.probability₀
  haveI := T.probability₁
  let E (t : ℕ) (θ : MarkedParam) : ℝ := markedEnvelopeCoeff n θ t u v w
  let P (t : ℕ) (θ : MarkedParam) : ℝ := θ.1 ^ t *
    (θ.1 * θ.2.1 * θ.2.2) ^ u *
    (θ.1 * θ.2.1 * (1 - θ.2.2)) ^ v *
    (θ.1 * (1 - θ.2.1)) ^ w
  let A (ν : Measure MarkedParam) (t : ℕ) : ℝ :=
    (-1 : ℝ) ^ t * ∫ θ, E t θ ∂ν
  have hErepr (t : ℕ) (θ : MarkedParam) : E t θ =
      (n ^ (t + u + v + w) /
        ((Nat.factorial t : ℝ) * (Nat.factorial u : ℝ) *
          (Nat.factorial v : ℝ) * (Nat.factorial w : ℝ))) * P t θ := by
    dsimp [E, P]
    simp only [markedEnvelopeCoeff, mul_pow, pow_add]
    ring
  have hsum_integral (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
      (hfinite : ∃ s : Finset MarkedParam, ν (s : Set MarkedParam) = 1)
      (F : ℕ → MarkedParam → ℝ)
      (hF : ∀ t, StronglyMeasurable (F t))
      (hs : ∀ θ, Summable (fun t => F t θ)) :
      Summable (fun t => ∫ θ, F t θ ∂ν) := by
    obtain ⟨s, hsμ⟩ := hfinite
    let cell : (s : Set MarkedParam) ↪ MarkedParam :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hrange : ν (Set.range cell) = ν Set.univ := by
      have heq : Set.range cell = (s : Set MarkedParam) := by
        ext θ
        simp [cell]
      rw [heq, hsμ]
      simp
    have hν := Causalean.Mathlib.MeasureTheory.measure_eq_fin_sum_smul_dirac_of_range
      ν cell (fun _ => measurableSet_singleton _) hrange
    have hint (t : ℕ) :
        (∫ θ, F t θ ∂ν) =
          ∑ i : (s : Set MarkedParam), (ν {cell i}).toReal * F t (cell i) := by
      conv_lhs => rw [hν]
      rw [integral_finsetSum_measure (by
        intro i hi
        exact (integrable_dirac' (hF t) (by simp)).smul_measure
          (measure_ne_top ν {cell i}))]
      simp only [integral_smul_measure, integral_dirac' _ _ (hF t), smul_eq_mul]
    simp_rw [hint]
    classical
    have hsum : ∀ q : Finset (s : Set MarkedParam),
        Summable (fun t => ∑ i ∈ q, (ν {cell i}).toReal * F t (cell i)) := by
      intro q
      induction q using Finset.induction_on with
      | empty => simp
      | @insert a q ha ih =>
          simp only [Finset.sum_insert ha]
          exact ((hs (cell a)).mul_left _).add ih
    simpa only [Finset.sum_attach] using hsum Finset.univ
  have hEpoint (θ : MarkedParam) : Summable (fun t => E t θ) := by
    have h := (Real.summable_pow_div_factorial (n * θ.1)).mul_right
      (((n * θ.1 * θ.2.1 * θ.2.2) ^ u / (Nat.factorial u : ℝ)) *
       ((n * θ.1 * θ.2.1 * (1 - θ.2.2)) ^ v / (Nat.factorial v : ℝ)) *
       ((n * θ.1 * (1 - θ.2.1)) ^ w / (Nat.factorial w : ℝ)))
    simpa only [E, markedEnvelopeCoeff, mul_assoc, div_eq_mul_inv] using h
  have hEmeas (t : ℕ) : StronglyMeasurable (E t) := by
    dsimp [E, markedEnvelopeCoeff]
    fun_prop
  have hsumE₀ : Summable (fun t => ∫ θ, E t θ ∂T.ν₀) :=
    hsum_integral T.ν₀ T.finite₀ E hEmeas hEpoint
  have hsumE₁ : Summable (fun t => ∫ θ, E t θ ∂T.ν₁) :=
    hsum_integral T.ν₁ T.finite₁ E hEmeas hEpoint
  have hsupport (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
      (hs : ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ ε ≤ θ.2.1 ∧
        θ.2.1 ≤ 1 - ε ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1) :
      ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ 0 ≤ θ.2.1 ∧
        θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1 := by
    apply le_antisymm
    · calc
        ν {θ : MarkedParam | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ 0 ≤ θ.2.1 ∧
          θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} ≤ ν Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    · calc
        (1 : ENNReal) = ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ ε ≤ θ.2.1 ∧
          θ.2.1 ≤ 1 - ε ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} := hs.symm
        _ ≤ _ := measure_mono (by
          intro θ hθ
          rcases hθ with ⟨hp₀, hp₁, hπ₀, hπ₁, hμ₀, hμ₁⟩
          exact ⟨hp₀, hp₁, hε.trans hπ₀,
            hπ₁.trans (sub_le_self 1 hε), hμ₀, hμ₁⟩)
  have hs₀ := hsupport T.ν₀ T.supported₀
  have hs₁ := hsupport T.ν₁ T.supported₁
  have hEnonneg (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
      (hs : ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ 0 ≤ θ.2.1 ∧
        θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1)
      (t : ℕ) : 0 ≤ ∫ θ, E t θ ∂ν := by
    apply integral_nonneg_of_ae
    have hae : ∀ᵐ θ ∂ν, θ ∈ {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧
        0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} :=
      (mem_ae_iff_prob_eq_one (by measurability)).2 hs
    filter_upwards [hae] with θ hθ
    rcases hθ with ⟨hp₀, hp₁, hπ₀, hπ₁, hμ₀, hμ₁⟩
    dsimp [E, markedEnvelopeCoeff]
    positivity
  have hAabs (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
      (hs : ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ 0 ≤ θ.2.1 ∧
        θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1)
      (t : ℕ) : |A ν t| = ∫ θ, E t θ ∂ν := by
    dsimp [A]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (hEnonneg ν hs t)]
  have hsumA₀ : Summable (A T.ν₀) := by
    apply Summable.of_abs
    simpa only [hAabs T.ν₀ hs₀] using hsumE₀
  have hsumA₁ : Summable (A T.ν₁) := by
    apply Summable.of_abs
    simpa only [hAabs T.ν₁ hs₁] using hsumE₁
  have hcoef (ν : Measure MarkedParam) [IsProbabilityMeasure ν] (t : ℕ) :
      ((-n) ^ t * n ^ (u + v + w) /
        ((Nat.factorial t : ℝ) * (Nat.factorial u : ℝ) *
          (Nat.factorial v : ℝ) * (Nat.factorial w : ℝ))) *
        (∫ θ, P t θ ∂ν) = A ν t := by
    have hi : (∫ θ, E t θ ∂ν) =
        (n ^ (t + u + v + w) /
          ((Nat.factorial t : ℝ) * (Nat.factorial u : ℝ) *
            (Nat.factorial v : ℝ) * (Nat.factorial w : ℝ))) *
          (∫ θ, P t θ ∂ν) := by
      simp_rw [hErepr, integral_const_mul]
    change _ = (-1 : ℝ) ^ t * ∫ θ, E t θ ∂ν
    rw [hi, show -n = (-1 : ℝ) * n by ring, mul_pow]
    simp only [pow_add]
    ring
  have hpred (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
      (hfinite : ∃ s : Finset MarkedParam, ν (s : Set MarkedParam) = 1)
      (hs : ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ 0 ≤ θ.2.1 ∧
        θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1) :
      (predictiveLaw n ν).real {((u, v), w)} = ∑' t, A ν t := by
    rw [predictiveLaw_singleton_eq_tsum_markedRateProduct hn ν hfinite hs u v w]
    apply tsum_congr
    intro t
    exact hcoef ν t
  have hmatch (t : ℕ) (hd : t + u + v + w ≤ 3 * K) :
      A T.ν₀ t = A T.ν₁ t := by
    dsimp [A]
    congr 1
    simp_rw [hErepr, integral_const_mul]
    congr 1
    exact integral_markedRateProduct_match hK T t u v w hd
  let D (t : ℕ) : ℝ := A T.ν₀ t - A T.ν₁ t
  let B (t : ℕ) : ℝ :=
    (∫ θ, E t θ ∂T.ν₀) + (∫ θ, E t θ ∂T.ν₁)
  have hsumD : Summable D := hsumA₀.sub hsumA₁
  have hsumB : Summable B := hsumE₀.add hsumE₁
  have hbound (t : ℕ) : |D t| ≤ B t := by
    dsimp [D, B]
    calc
      |A T.ν₀ t - A T.ν₁ t| ≤ |A T.ν₀ t| + |A T.ν₁ t| := abs_sub _ _
      _ = (∫ θ, E t θ ∂T.ν₀) + (∫ θ, E t θ ∂T.ν₁) := by
        rw [hAabs T.ν₀ hs₀ t, hAabs T.ν₁ hs₁ t]
  have hsumDt : Summable (fun t => if 3 * K < t + u + v + w then D t else 0) := by
    have hi := hsumD.indicator {t | 3 * K < t + u + v + w}
    have heq : (fun t => if 3 * K < t + u + v + w then D t else 0) =
        Set.indicator {t | 3 * K < t + u + v + w} D := by
      funext t
      simp [Set.indicator_apply]
    rw [heq]
    exact hi
  have hsumBt : Summable (fun t => if 3 * K < t + u + v + w then B t else 0) := by
    have hi := hsumB.indicator {t | 3 * K < t + u + v + w}
    have heq : (fun t => if 3 * K < t + u + v + w then B t else 0) =
        Set.indicator {t | 3 * K < t + u + v + w} B := by
      funext t
      simp [Set.indicator_apply]
    rw [heq]
    exact hi
  calc
    |(predictiveLaw n T.ν₀).real {((u, v), w)} -
      (predictiveLaw n T.ν₁).real {((u, v), w)}| = |∑' t, D t| := by
        rw [hpred T.ν₀ T.finite₀ hs₀, hpred T.ν₁ T.finite₁ hs₁]
        rw [← hsumA₀.tsum_sub hsumA₁]
    _ = |∑' t, if 3 * K < t + u + v + w then D t else 0| := by
        congr 1
        apply tsum_congr
        intro t
        by_cases ht : 3 * K < t + u + v + w
        · simp [ht]
        · simp [ht, D, hmatch t (by omega)]
    _ ≤ ∑' t, |if 3 * K < t + u + v + w then D t else 0| := by
        have hnorm : Summable (fun t =>
            ‖if 3 * K < t + u + v + w then D t else 0‖) := by
          simpa only [Real.norm_eq_abs] using hsumDt.abs
        simpa only [Real.norm_eq_abs] using
          (norm_tsum_le_tsum_norm (f := fun t =>
            if 3 * K < t + u + v + w then D t else 0) hnorm)
    _ ≤ ∑' t, if 3 * K < t + u + v + w then B t else 0 := by
        apply hsumDt.abs.tsum_le_tsum
        · intro t
          by_cases ht : 3 * K < t + u + v + w
          · simpa only [if_pos ht] using hbound t
          · simp [ht]
        · exact hsumBt
    _ = _ := rfl

/- For each parameter, the nonnegative coefficient series is
  `fourRateFactorialTail K` at rates `np`, `npπμ`, `npπ(1-μ)`, `np(1-π)`.
  Those rates sum to `2np ≤ 2nb`.  Exchange the countable coefficient sum
  with the integral using the finite atomic support of the prior. -/

/- At a fixed bounded parameter, identify the coefficient with the four-rate
  product indexed by `q : Fin 4 → ℕ`, using the rates in the module comment.
  The rates are nonnegative, and their sum is `2*n*θ.1 ≤ 2*n*b`.
  For summability, reuse the `hsum` argument in `fourRateFactorialTail_le`:
  partition by total degree, whose fiber sums are factorial coefficients.
  Then apply `fourRateFactorialTail_le` to the identified series. -/

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size and support bound](hyp:hn,hb), and a [parameter triple whose arrival, propensity, and response coordinates obey the stated bounds](hyp:θ,hp₀,hp₁,hπ₀,hπ₁,hμ₀,hμ₁) give [a summable unmatched coefficient series bounded by the factorial tail](goal). -/
theorem unmatchedEnvelopeCoeff_pointwise_le_tail
    {K : ℕ} (hK : 1 ≤ K) {n b : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b)
    (θ : MarkedParam) (hp₀ : 0 ≤ θ.1) (hp₁ : θ.1 ≤ b)
    (hπ₀ : 0 ≤ θ.2.1) (hπ₁ : θ.2.1 ≤ 1)
    (hμ₀ : 0 ≤ θ.2.2) (hμ₁ : θ.2.2 ≤ 1) :
    Summable (fun q : Fin 4 → ℕ =>
      if 3 * K < q 0 + q 1 + q 2 + q 3 then
        markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3)
      else 0) ∧
    (∑' q : Fin 4 → ℕ,
      if 3 * K < q 0 + q 1 + q 2 + q 3 then
        markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3)
      else 0) ≤ unmatchedTail K n b := by
  classical
  let r : Fin 4 → ℝ := ![n * θ.1,
    n * θ.1 * θ.2.1 * θ.2.2,
    n * θ.1 * θ.2.1 * (1 - θ.2.2),
    n * θ.1 * (1 - θ.2.1)]
  have hr : ∀ i, 0 ≤ r i := by
    intro i
    fin_cases i <;> simp [r] <;> positivity
  have hrate : (∑ i, r i) ≤ 2 * n * b := by
    have hp : n * θ.1 ≤ n * b := mul_le_mul_of_nonneg_left hp₁ hn
    simp only [Fin.sum_univ_four]
    dsimp [r]
    nlinarith [mul_nonneg (mul_nonneg hn hp₀) hπ₀,
      mul_nonneg (mul_nonneg hn hp₀) (sub_nonneg.mpr hπ₁),
      mul_nonneg (mul_nonneg (mul_nonneg hn hp₀) hπ₀) hμ₀]
  let s (m : ℕ) : Finset (Fin 4 → ℕ) := Finset.piAntidiag Finset.univ m
  let a (q : Fin 4 → ℕ) : ℝ := ∏ i, r i ^ q i / (Nat.factorial (q i) : ℝ)
  let f (q : Fin 4 → ℕ) : ℝ :=
    if 3 * K < ∑ i, q i then a q else 0
  have ha (q : Fin 4 → ℕ) : 0 ≤ a q := by
    dsimp [a]
    apply Finset.prod_nonneg
    intro i _
    exact div_nonneg (pow_nonneg (hr i) _) (by positivity)
  have hf (q : Fin 4 → ℕ) : 0 ≤ f q := by
    dsimp [f]
    split_ifs with h
    · exact ha q
    · exact le_refl 0
  have hs_mem (m : ℕ) (q : Fin 4 → ℕ) :
      q ∈ s m ↔ (∑ i, q i) = m := by
    simp [s, Finset.mem_piAntidiag]
  have hfactor (q : Fin 4 → ℕ) :
      a q = (Nat.multinomial Finset.univ q : ℝ) *
        (∏ i, r i ^ q i) / (Nat.factorial (∑ i, q i) : ℝ) := by
    have hn := Nat.multinomial_spec (Finset.univ : Finset (Fin 4)) q
    have hn' : (∏ i, (Nat.factorial (q i) : ℝ)) *
        (Nat.multinomial Finset.univ q : ℝ) =
        (Nat.factorial (∑ i, q i) : ℝ) := by exact_mod_cast hn
    dsimp [a]
    rw [Finset.prod_div_distrib]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [← hn']
    ring
  have hdegree (m : ℕ) :
      ∑ q ∈ s m, a q = (∑ i, r i) ^ m / (Nat.factorial m : ℝ) := by
    calc
      ∑ q ∈ s m, a q =
          ∑ q ∈ s m, (Nat.multinomial Finset.univ q : ℝ) *
            (∏ i, r i ^ q i) / (Nat.factorial m : ℝ) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [hfactor q, (hs_mem m q).mp hq]
      _ = (∑ i, r i) ^ m / (Nat.factorial m : ℝ) := by
            simp only [div_eq_mul_inv, ← Finset.sum_mul]
            rw [Finset.sum_pow_eq_sum_piAntidiag]
  have hfiber (m : ℕ) :
      ∑' q : {q // q ∈ s m}, f q =
        if 3 * K < m then (∑ i, r i) ^ m / (Nat.factorial m : ℝ) else 0 := by
    rw [Finset.tsum_subtype (s m) f]
    by_cases hm : 3 * K < m
    · simp only [if_pos hm]
      rw [← hdegree m]
      apply Finset.sum_congr rfl
      intro q hq
      simp [f, (hs_mem m q).mp hq, hm]
    · simp only [if_neg hm]
      apply Finset.sum_eq_zero
      intro q hq
      simp [f, (hs_mem m q).mp hq, hm]
  have hbase : Summable (fun m : ℕ =>
      if 3 * K < m then (∑ i, r i) ^ m / (Nat.factorial m : ℝ) else 0) := by
    have heq : (fun m : ℕ =>
        if 3 * K < m then (∑ i, r i) ^ m / (Nat.factorial m : ℝ) else 0) =
        ({m : ℕ | 3 * K < m}.indicator fun m =>
          (∑ i, r i) ^ m / (Nat.factorial m : ℝ)) := by
      funext m
      simp [Set.indicator_apply]
    rw [heq]
    exact (Real.summable_pow_div_factorial (∑ i, r i)).indicator
      {m : ℕ | 3 * K < m}
  have houter : Summable (fun m : ℕ => ∑' q : {q // q ∈ s m}, f q) := by
    simpa only [hfiber] using hbase
  have hsum : Summable f := by
    apply (summable_partition hf (s := fun m => (s m : Set (Fin 4 → ℕ))) (by
      intro q
      refine ⟨∑ i, q i, ?_, ?_⟩
      · exact (hs_mem _ _).2 rfl
      · intro m hm
        exact (hs_mem _ _).1 hm |>.symm)).2
    constructor
    · intro m
      haveI : Finite (s m : Set (Fin 4 → ℕ)) := (s m).finite_toSet.to_subtype
      exact Summable.of_finite
    · simpa only [Finset.coe_sort_coe] using houter
  have hcoeff (q : Fin 4 → ℕ) :
      f q = if 3 * K < q 0 + q 1 + q 2 + q 3 then
        markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3) else 0 := by
    simp only [f, a, Fin.sum_univ_four, Fin.prod_univ_four]
    simp [r, markedEnvelopeCoeff]
    split_ifs <;> ring
  have hfun : f = (fun q : Fin 4 → ℕ =>
      if 3 * K < q 0 + q 1 + q 2 + q 3 then
        markedEnvelopeCoeff n θ (q 0) (q 1) (q 2) (q 3) else 0) :=
    funext hcoeff
  have htail : (∑' q, f q) ≤ unmatchedTail K n b := by
    change fourRateFactorialTail K r ≤ unmatchedTail K n b
    exact fourRateFactorialTail_le K hK r hr (2 * n * b) hrate
  constructor
  · rw [← hfun]
    exact hsum
  · rw [← hfun]
    exact htail

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
