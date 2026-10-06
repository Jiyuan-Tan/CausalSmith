module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.ObservedAtoms
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.PrefixTransfer

/-! # Fixed-size predictive comparison for the normalized paired priors

The exact observed-atom identity identifies the conditional count law with
independent Poisson counts from the normalized marks. The shared normalizer
is at least one half, so the four-n experiment loses at most sixteen over n
when converted to its fixed-size ordered prefix.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
open scoped ENNReal NNReal

-- @node: paired_predictive_tv_le_count_tv_add_inverse
/-- The exact normalized paired predictives are compared by their count
mixtures with a uniform prefix-transfer loss of sixteen divided by n. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma paired_predictive_tv_le_count_tv_add_inverse (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    Causalean.Stat.tvDist
      (priorPredictive n d q (pairedPrior n d q hn hd hq).1)
      (priorPredictive n d q (pairedPrior n d q hn hd hq).2) ≤
    Causalean.Stat.tvDist (mixedCountLaw n d q (-1) hn hd hq)
      (mixedCountLaw n d q 1 hn hd hq) + 16 / (n : ℝ) := by
  letI : MeasurableSpace (Theta n d) := ⊤
  letI : MeasurableSingletonClass (Theta n d) := ⟨fun _ => trivial⟩
  let π := thetaLaw n d q hn hd hq
  let P (σ : ℝ) (hσ : σ ∈ Set.Icc (-1) 1) : Kernel (Theta n d) (Obs d) :=
    ⟨fun θ => (observedLaw (pairedFullLaw n d q σ hn hd hq hσ θ)).toMeasure,
      measurable_of_finite _⟩
  haveI (σ : ℝ) (hσ : σ ∈ Set.Icc (-1) 1) (θ : Theta n d) :
      IsProbabilityMeasure (P σ hσ θ) := by
    dsimp [P]
    infer_instance
  let S : Theta n d → ℝ≥0 := fun θ => Real.toNNReal (normalizationJ n d θ)
  let u : ℝ≥0 := Real.toNNReal (4 * (n : ℝ))
  have hmean (θ : Theta n d) : (2 : ℝ) * n ≤ (u * S θ : ℝ≥0) := by
    have hJ := normalizationJ_ge_half n d θ hn
    have hJ0 := normalizationJ_pos n d q hn hd hq θ
    change 2 * (n : ℝ) ≤
      ((Real.toNNReal (4 * (n : ℝ)) * Real.toNNReal (normalizationJ n d θ) : ℝ≥0) : ℝ)
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ hJ0.le]
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hfixed (σ : ℝ) (hσ : σ ∈ Set.Icc (-1) 1) :
      fixedMixture π.toMeasure (P σ hσ) n =
        pairedPredictive n d q σ hn hd hq hσ := by
    rw [fixedMixture, pmf_bind_eq_finite_mixture]
    rfl
  have hcount (σ : ℝ) (hσ : σ ∈ Set.Icc (-1) 1) :
      π.toMeasure.bind (fun θ => independentPoissonCountLaw (P σ hσ θ) (u * S θ)) =
        mixedCountLaw n d q σ hn hd hq := by
    rw [pmf_bind_eq_finite_mixture]
    unfold mixedCountLaw
    apply Finset.sum_congr rfl
    intro θ _
    congr 1
    exact (conditionalCountLaw_eq_independentPoissonCountLaw n d q σ hn hd hq hσ θ).symm
  let fallback : Fin n → Obs d := fun _ => ⟨⟨0, hd⟩, false, false, true, false⟩
  have h := randomScale_fixed_tv_le_count_tv_add_inverse π.toMeasure
    (P (-1) (by norm_num)) (P 1 (by norm_num)) S u n hn fallback hmean
  rw [hfixed, hfixed, hcount, hcount] at h
  rw [pairedPredictive_minus_eq, pairedPredictive_plus_eq] at h
  exact h

end CausalSmith.Stat.MarNearcompleteFrontier
