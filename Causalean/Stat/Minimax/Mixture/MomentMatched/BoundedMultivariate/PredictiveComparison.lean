module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.PredictiveTail
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.ProductTV
public import Causalean.Stat.Minimax.TotalVariation

/-!
# Marked-Poisson predictive total variation

This module turns the integrated Taylor tail into one-cell and finite-product total-variation bounds for marked-Poisson predictions.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size and support bound](hyp:hn,hb), [nonnegative overlap margin](hyp:hε), and [bounded triple priors](hyp:T) give [a one-cell marked-Poisson total-variation bound by the unmatched tail](goal). -/
theorem tvDist_predictiveLaw_le_unmatchedTail {K : ℕ} (hK : 1 ≤ K)
    {b ε gap n : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (T : TriplePriors K b ε gap) :
    Causalean.Stat.tvDist (predictiveLaw n T.ν₀) (predictiveLaw n T.ν₁) ≤
      unmatchedTail K n b := by
  letI : IsProbabilityMeasure T.ν₀ := T.probability₀
  letI : IsProbabilityMeasure T.ν₁ := T.probability₁
  letI : IsProbabilityMeasure (predictiveLaw n T.ν₀) :=
    predictiveLaw_isProbability n T.ν₀
  letI : IsProbabilityMeasure (predictiveLaw n T.ν₁) :=
    predictiveLaw_isProbability n T.ν₁
  let S : Set MarkedParam := {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧
    0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1}
  have hsub : {θ : MarkedParam | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧ ε ≤ θ.2.1 ∧
      θ.2.1 ≤ 1 - ε ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} ⊆ S := by
    rintro θ ⟨hp0, hpb, hεπ, hπε, hμ0, hμ1⟩
    exact ⟨hp0, hpb, hε.trans hεπ, hπε.trans (by linarith), hμ0, hμ1⟩
  have hs0 : T.ν₀ S = 1 := by
    apply le_antisymm prob_le_one
    rw [← T.supported₀]
    exact measure_mono hsub
  have hs1 : T.ν₁ S = 1 := by
    apply le_antisymm prob_le_one
    rw [← T.supported₁]
    exact measure_mono hsub
  let E (ν : Measure MarkedParam) (z : (ℕ × ℕ) × ℕ) : ℝ :=
    ∑' t : ℕ, if 3 * K < t + z.1.1 + z.1.2 + z.2 then
      ∫ θ, markedEnvelopeCoeff n θ t z.1.1 z.1.2 z.2 ∂ν else 0
  obtain ⟨hEt0, hE0, htail0⟩ :=
    tsum_unmatchedEnvelope_integral_le_tail hK hn hb T.ν₀ T.finite₀ hs0
  obtain ⟨hEt1, hE1, htail1⟩ :=
    tsum_unmatchedEnvelope_integral_le_tail hK hn hb T.ν₁ T.finite₁ hs1
  have hpoint (z : (ℕ × ℕ) × ℕ) :
      |(predictiveLaw n T.ν₀).real {z} - (predictiveLaw n T.ν₁).real {z}| ≤
        E T.ν₀ z + E T.ν₁ z := by
    rcases z with ⟨⟨u, v⟩, w⟩
    calc
      _ ≤ ∑' t : ℕ, if 3 * K < t + u + v + w then
          (∫ θ, markedEnvelopeCoeff n θ t u v w ∂T.ν₀) +
          (∫ θ, markedEnvelopeCoeff n θ t u v w ∂T.ν₁) else 0 :=
        abs_predictiveLaw_singleton_diff_le_unmatchedEnvelope hn hε T u v w
      _ = ∑' t : ℕ, (
          (if 3 * K < t + u + v + w then
            ∫ θ, markedEnvelopeCoeff n θ t u v w ∂T.ν₀ else 0) +
          (if 3 * K < t + u + v + w then
            ∫ θ, markedEnvelopeCoeff n θ t u v w ∂T.ν₁ else 0)) := by
        apply tsum_congr
        intro t
        split_ifs <;> simp
      _ = E T.ν₀ ((u, v), w) + E T.ν₁ ((u, v), w) := by
        simpa only [E] using
          (hEt0 ((u, v), w)).tsum_add (hEt1 ((u, v), w))
  have hEsum : Summable (fun z => E T.ν₀ z + E T.ν₁ z) := hE0.add hE1
  have hlhs : Summable (fun z : (ℕ × ℕ) × ℕ =>
      |(predictiveLaw n T.ν₀).real {z} - (predictiveLaw n T.ν₁).real {z}|) := by
    apply Summable.of_nonneg_of_le (f := fun z => E T.ν₀ z + E T.ν₁ z)
    · intro z
      positivity
    · exact hpoint
    · exact hEsum
  calc
    Causalean.Stat.tvDist (predictiveLaw n T.ν₀) (predictiveLaw n T.ν₁) ≤
        (∑' z : (ℕ × ℕ) × ℕ,
          |(predictiveLaw n T.ν₀).real {z} -
            (predictiveLaw n T.ν₁).real {z}|) / 2 :=
      by simpa [div_eq_mul_inv, mul_comm] using
        Causalean.Stat.tvDist_le_half_tsum_singleton_abs
          (predictiveLaw n T.ν₀) (predictiveLaw n T.ν₁)
    _ ≤ (∑' z : (ℕ × ℕ) × ℕ, (E T.ν₀ z + E T.ν₁ z)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact Summable.tsum_le_tsum hpoint hlhs hEsum
    _ = ((∑' z, E T.ν₀ z) + ∑' z, E T.ν₁ z) / 2 := by
      rw [hE0.tsum_add hE1]
    _ ≤ (unmatchedTail K n b + unmatchedTail K n b) / 2 := by
      gcongr
    _ = unmatchedTail K n b := by ring

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size and support bound](hyp:hn,hb), [nonnegative overlap margin](hyp:hε), and [bounded triple priors](hyp:T) give [the explicit factorial upper bound on one-cell predictive total variation](goal). -/
theorem tvDist_predictiveLaw_le_factorial {K : ℕ} (hK : 1 ≤ K)
    {b ε gap n : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (T : TriplePriors K b ε gap) :
    Causalean.Stat.tvDist (predictiveLaw n T.ν₀) (predictiveLaw n T.ν₁) ≤
      Real.exp (2 * n * b) * (2 * n * b) ^ (3 * K + 1) /
        (Nat.factorial (3 * K + 1) : ℝ) := by
  exact (tvDist_predictiveLaw_le_unmatchedTail hK hn hb hε T).trans
    (unmatchedTail_le_factorial K hn hb)

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size and support bound](hyp:hn,hb), [nonnegative overlap margin](hyp:hε), and [a finite family of bounded triple priors](hyp:T) give [a finite-product predictive total-variation bound by the sum of one-cell unmatched tails](goal). -/
theorem tvDist_productPredictive_le_sum {d K : ℕ} (hK : 1 ≤ K)
    {b ε gap n : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (T : Fin d → TriplePriors K b ε gap) :
    Causalean.Stat.tvDist
      (Measure.pi fun i : Fin d => predictiveLaw n (T i).ν₀)
      (Measure.pi fun i : Fin d => predictiveLaw n (T i).ν₁) ≤
        ∑ _i : Fin d, unmatchedTail K n b := by
  letI : ∀ i : Fin d, IsProbabilityMeasure (predictiveLaw n (T i).ν₀) :=
    fun i => by
      letI := (T i).probability₀
      exact predictiveLaw_isProbability n (T i).ν₀
  letI : ∀ i : Fin d, IsProbabilityMeasure (predictiveLaw n (T i).ν₁) :=
    fun i => by
      letI := (T i).probability₁
      exact predictiveLaw_isProbability n (T i).ν₁
  calc
    _ ≤ ∑ i : Fin d,
        Causalean.Stat.tvDist (predictiveLaw n (T i).ν₀)
          (predictiveLaw n (T i).ν₁) :=
      tvDist_pi_le_sum_heterogeneous _ _
    _ ≤ ∑ _i : Fin d, unmatchedTail K n b := by
      apply Finset.sum_le_sum
      intro i hi
      exact tvDist_predictiveLaw_le_unmatchedTail hK hn hb hε (T i)

/-- A [positive matching degree](hyp:hK), [nonnegative experiment size and support bound](hyp:hn,hb), [nonnegative overlap margin](hyp:hε), and [a family of d bounded triple-prior pairs](hyp:T), one per cell, have [independent marked-Poisson predictive laws whose total variation distance is at most d · e^(2nb) · (2nb)^(3K+1) / (3K+1)!](goal). -/
theorem tvDist_productPredictive_le_factorial {d K : ℕ} (hK : 1 ≤ K)
    {b ε gap n : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (T : Fin d → TriplePriors K b ε gap) :
    Causalean.Stat.tvDist
      (Measure.pi fun i : Fin d => predictiveLaw n (T i).ν₀)
      (Measure.pi fun i : Fin d => predictiveLaw n (T i).ν₁) ≤
        (d : ℝ) * (Real.exp (2 * n * b) *
          (2 * n * b) ^ (3 * K + 1) /
            (Nat.factorial (3 * K + 1) : ℝ)) := by
  calc
    _ ≤ ∑ _i : Fin d, unmatchedTail K n b :=
      tvDist_productPredictive_le_sum hK hn hb hε T
    _ = (d : ℝ) * unmatchedTail K n b := by simp
    _ ≤ (d : ℝ) * (Real.exp (2 * n * b) *
          (2 * n * b) ^ (3 * K + 1) /
            (Nat.factorial (3 * K + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (unmatchedTail_le_factorial K hn hb)
        (by positivity)

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
