module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.BiasVariance
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Algebra.Order.Chebyshev

/-! Conditional averaging contracts squared risk. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: finite_weighted_square_with_remainder
/-- Given [the specified inputs and assumptions](hyp:ι,s,w,a,c,hw,hmass), [the stated mathematical conclusion holds](goal). -/
lemma finite_weighted_square_with_remainder {ι : Type*} (s : Finset ι)
    (w a : ι → ℝ) (c : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmass : ∑ i ∈ s, w i ≤ 1) :
    ((∑ i ∈ s, w i * a i) - c) ^ 2 ≤
      (1 - ∑ i ∈ s, w i) * c ^ 2 +
        ∑ i ∈ s, w i * (a i - c) ^ 2 := by
  have hc : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    (show Even (2 : ℕ) by decide).convexOn_pow
  have hj := hc.map_add_sum_le hw
    (show (1 - ∑ i ∈ s, w i) + ∑ i ∈ s, w i = 1 by ring)
    (by simp : ∀ i ∈ s, a i - c ∈ Set.univ)
    (sub_nonneg.mpr hmass) (by simp : -c ∈ Set.univ)
  have he : (∑ i ∈ s, w i * a i) - c =
      (1 - ∑ i ∈ s, w i) * (-c) + ∑ i ∈ s, w i * (a i - c) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  simpa only [smul_eq_mul, Function.comp_apply, neg_sq, he] using hj

-- @node: finite_uniform_square
/-- Given [the specified inputs and assumptions](hyp:ι,f,c), [the stated mathematical conclusion holds](goal). -/
lemma finite_uniform_square {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (c : ℝ) :
    ((∑ i : ι, f i) / (Fintype.card ι : ℝ) - c)^2 ≤
      (∑ i : ι, (f i - c)^2) / (Fintype.card ι : ℝ) := by
  have h := sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset ι)) (f := fun i => f i - c)
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have he : (∑ i : ι, (f i - c)) / (Fintype.card ι : ℝ) =
      (∑ i : ι, f i) / (Fintype.card ι : ℝ) - c := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [← he]
  simpa using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P), [the stated mathematical conclusion holds](goal). -/
lemma mixed_count_derandomization (n d : ℕ) (q : ℝ) (P : FullLaw d) :
    deterministicRisk (mixedCountEstimator n d q) P ≤
      auxiliaryMixedRisk n q P := by
  classical
  let w : ℕ → ℝ := fun k =>
    (poissonMeasure ((n : ℝ≥0) / 2)).real ({k} : Set ℕ)
  let a : (Fin n → ObsRecord d) → ℕ → ℝ := fun sample k =>
    if h : k ≤ n then
      (∑ assign : Fin k → Fin 3,
        auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign) /
        (3 : ℝ) ^ k
    else 0
  have hw (k : ℕ) : 0 ≤ w k := measureReal_nonneg
  have hmass : (∑ k ∈ Finset.range (n + 1), w k) ≤ 1 := by
    have h := MeasureTheory.sum_measureReal_le_measureReal_univ
      (μ := poissonMeasure ((n : ℝ≥0) / 2))
      (s := Finset.range (n + 1)) (t := fun k : ℕ => ({k} : Set ℕ))
    have hm : ∀ k ∈ Finset.range (n + 1), MeasurableSet ({k} : Set ℕ) :=
      fun _ _ => MeasurableSet.singleton _
    have hd : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
        (fun k : ℕ => ({k} : Set ℕ)) := by
      intro i hi j hj hij
      exact Set.disjoint_singleton.mpr hij
    simpa [w] using h hm hd
  have hpoint (sample : Fin n → ObsRecord d) :
      (mixedCountEstimator n d q sample - ate P) ^ 2 ≤
      (∑ k ∈ Finset.range (n + 1),
        if h : k ≤ n then w k *
          ((∑ assign : Fin k → Fin 3,
            (auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign -
              ate P) ^ 2) / (3 : ℝ) ^ k)
        else 0) +
        (1 - ∑ k ∈ Finset.range (n + 1), w k) * (ate P) ^ 2 := by
    have houter := finite_weighted_square_with_remainder
      (Finset.range (n + 1)) w (a sample) (ate P)
      (fun k _ => hw k) hmass
    have hinner (k : ℕ) (h : k ≤ n) :
        (a sample k - ate P) ^ 2 ≤
          (∑ assign : Fin k → Fin 3,
            (auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign -
              ate P) ^ 2) / (3 : ℝ) ^ k := by
      simpa [a, h] using finite_uniform_square
        (fun assign : Fin k → Fin 3 =>
          auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign)
        (ate P)
    have hsum :
        (∑ k ∈ Finset.range (n + 1), w k * (a sample k - ate P) ^ 2) ≤
        (∑ k ∈ Finset.range (n + 1),
          if h : k ≤ n then w k *
            ((∑ assign : Fin k → Fin 3,
              (auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign -
                ate P) ^ 2) / (3 : ℝ) ^ k)
          else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      have h : k ≤ n := by simpa using hk
      simpa only [a, dif_pos h] using
        mul_le_mul_of_nonneg_left (hinner k h) (hw k)
    have he : mixedCountEstimator n d q sample =
        ∑ k ∈ Finset.range (n + 1), w k * a sample k := by
      simp [mixedCountEstimator, w, a]
    rw [he]
    linarith
  letI : IsProbabilityMeasure P.1 := P.2
  haveI : IsProbabilityMeasure (P.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1)
  haveI : IsProbabilityMeasure (sampleLaw n P) := by
    unfold sampleLaw
    infer_instance
  change (∫ sample, (mixedCountEstimator n d q sample - ate P) ^ 2
    ∂(sampleLaw n P)) ≤
    ∫ sample, (∑ k ∈ Finset.range (n + 1),
      if h : k ≤ n then w k *
        ((∑ assign : Fin k → Fin 3,
          (auxiliaryMixedValue n q (fun i => sample (Fin.castLE h i)) assign -
            ate P) ^ 2) / (3 : ℝ) ^ k)
      else 0) +
      (1 - ∑ k ∈ Finset.range (n + 1), w k) * (ate P) ^ 2
      ∂(sampleLaw n P)
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun sample => sq_nonneg _)
  · exact Integrable.of_finite
  · exact Filter.Eventually.of_forall hpoint

end CausalSmith.Stat.MarRareqLogfrontier
