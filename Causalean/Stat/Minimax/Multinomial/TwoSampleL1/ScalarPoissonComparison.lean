module
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.AggregatePoisson
public import Causalean.Stat.Minimax.Mixture.MomentMatched.SupportLocalized
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarMomentPriors
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPoissonLikelihood
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPriorMeasure
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Predictive comparison for a balanced Poisson pair

A scalar perturbation raises one cell intensity and lowers its partner by the
same amount. Equal scalar moments cancel the low-degree terms of the two-cell
Poisson likelihood. This module isolates the quantitative remaining tail.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- The Poisson count-pair predictive law formed from one of two finite scalar
moment priors. The Boolean index selects the first or second prior. -/
noncomputable def scalarPoissonPredictive {L : ℕ} (P : ScalarMomentPriors L)
    (lambda t : ℝ) (side : Bool) : Measure (ℕ × ℕ) :=
  Causalean.Stat.mixture
    (fun i => ENNReal.ofReal (if side then P.w₁ i else P.w₀ i))
    (fun i => scalarPoissonPairLaw lambda t (P.node i))

/-- Given [a positive-degree moment prior](hyp:P,hL), [a nonnegative Poisson intensity and bounded nonnegative tilt](hyp:lambda,t,hlambda,ht,ht1), and [the scale budget](hyp:hscale), [the scalar predictive distance is bounded by the moment remainder](goal). -/
theorem scalarPoissonPredictive_tv_le {L : ℕ} (P : ScalarMomentPriors L)
    (hL : 1 ≤ L) (lambda t : ℝ) (hlambda : 0 ≤ lambda)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hscale : 100 * lambda * t ^ 2 ≤ (L : ℝ)) :
    Causalean.Stat.tvDist
      (scalarPoissonPredictive P lambda t false)
      (scalarPoissonPredictive P lambda t true) ≤
        (2 : ℝ) ^ (-(L : ℝ) / 4) := by
  classical
  by_cases hzero : lambda = 0
  · have hlaw (u : ℝ) : scalarPoissonPairLaw lambda t u =
        scalarPoissonPairLaw lambda t 0 := by
      simp [scalarPoissonPairLaw, hzero]
    have hpredict : scalarPoissonPredictive P lambda t false =
        scalarPoissonPredictive P lambda t true := by
      ext A hA
      simp only [scalarPoissonPredictive, Causalean.Stat.mixture_apply, hlaw]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hw0 : ∑ i : Fin P.m, ENNReal.ofReal (P.w₀ i) = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.w₀_nonneg i), P.w₀_sum]
        norm_num
      have hw1 : ∑ i : Fin P.m, ENNReal.ofReal (P.w₁ i) = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => P.w₁_nonneg i), P.w₁_sum]
        norm_num
      simpa [hw0, hw1]
    rw [hpredict]
    simpa [Causalean.Stat.tvDist] using
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(L : ℝ) / 4))
  have hlambda' : 0 < lambda := lt_of_le_of_ne hlambda (Ne.symm hzero)
  letI : IsSFiniteKernel (aggregatePoissonKernelOfRealRate
      (fun u => lambda * (1 + t * u))) := by
    unfold aggregatePoissonKernelOfRealRate
    apply Kernel.IsSFiniteKernel.withDensity
    simp
  letI : IsSFiniteKernel (aggregatePoissonKernelOfRealRate
      (fun u => lambda * (1 - t * u))) := by
    unfold aggregatePoissonKernelOfRealRate
    apply Kernel.IsSFiniteKernel.withDensity
    simp
  let K : Kernel ℝ (ℕ × ℕ) :=
    (aggregatePoissonKernelOfRealRate (fun u => lambda * (1 + t * u))).prod
      (aggregatePoissonKernelOfRealRate (fun u => lambda * (1 - t * u)))
  have hkernel (r : ℝ → ℝ) (hr : Measurable r) (u : ℝ) :
      aggregatePoissonKernelOfRealRate r u = poissonMeasure (Real.toNNReal (r u)) := by
    rw [aggregatePoissonKernelOfRealRate, Kernel.withDensity_apply]
    · apply Measure.ext_of_singleton
      intro n
      rw [withDensity_apply _ (measurableSet_singleton n), poissonMeasure_singleton]
      simp
    · apply measurable_from_prod_countable_left
      intro n
      fun_prop
  have hKfiber (u : ℝ) : K u = scalarPoissonPairLaw lambda t u := by
    dsimp [K, scalarPoissonPairLaw]
    rw [Kernel.prod_apply,
      hkernel _ (by fun_prop) u, hkernel _ (by fun_prop) u]
  let Q : Measure (ℕ × ℕ) := scalarPoissonPairLaw lambda t 0
  let π₀ : Measure ℝ := scalarMomentPrior P false
  let π₁ : Measure ℝ := scalarMomentPrior P true
  letI : IsProbabilityMeasure π₀ := scalarMomentPrior_isProbability P false
  letI : IsProbabilityMeasure π₁ := scalarMomentPrior_isProbability P true
  have hQ : IsProbabilityMeasure Q := by
    dsimp [Q, scalarPoissonPairLaw]
    infer_instance
  letI : IsProbabilityMeasure Q := hQ
  have hK : ∀ u, IsProbabilityMeasure (K u) := by
    intro u
    rw [hKfiber]
    unfold scalarPoissonPairLaw
    infer_instance
  have hmeas : Measurable (fun p : ℝ × (ℕ × ℕ) =>
      scalarPoissonPairLikelihood t p.1 p.2) := by
    unfold scalarPoissonPairLikelihood
    fun_prop
  have hnonneg : ∀ u : ℝ, |u| ≤ 1 → ∀ z, 0 ≤ scalarPoissonPairLikelihood t u z := by
    intro u hu z
    have htu : -1 ≤ t * u ∧ t * u ≤ 1 := by
      constructor <;> nlinarith [(abs_le.mp hu).1, (abs_le.mp hu).2]
    unfold scalarPoissonPairLikelihood
    exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
  have hdensity : ∀ u : ℝ, |u| ≤ 1 →
      K u = Q.withDensity (fun z => ENNReal.ofReal (scalarPoissonPairLikelihood t u z)) := by
    intro u hu
    have htu : -1 ≤ t * u ∧ t * u ≤ 1 := by
      constructor <;> nlinarith [(abs_le.mp hu).1, (abs_le.mp hu).2]
    rw [hKfiber]
    exact scalarPoissonPairLaw_eq_withDensity lambda t u hlambda'
      (by linarith) (by linarith)
  have hinner : ∀ u : ℝ, |u| ≤ 1 → ∀ v : ℝ, |v| ≤ 1 →
      (∫ z, scalarPoissonPairLikelihood t u z * scalarPoissonPairLikelihood t v z ∂Q) =
        Real.exp ((2 * lambda * t ^ 2) * u * v) := by
    intro u _ v _
    exact scalarPoissonPairLikelihood_inner lambda t u v hlambda
  have hsupp0 : π₀ {u : ℝ | |u| ≤ 1} = 1 := scalarMomentPrior_supported P false
  have hsupp1 : π₁ {u : ℝ | |u| ≤ 1} = 1 := scalarMomentPrior_supported P true
  have hmom : ∀ n ≤ L, (∫ u, u ^ n ∂π₀) = ∫ u, u ^ n ∂π₁ := by
    intro n hn
    exact scalarMomentPrior_moments_eq P n hn
  have htv := Causalean.Stat.Minimax.MomentMatchedMixture.momentMatchedMixture_tv_le_sqrt_tail_of_supported
      π₀ π₁ K Q
      (scalarPoissonPairLikelihood t) hK (2 * lambda * t ^ 2) 1 L
      (by positivity) (by norm_num) hmeas hnonneg hdensity hinner hsupp0 hsupp1 hmom
  have hpred (side : Bool) :
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        (scalarMomentPrior P side) K = scalarPoissonPredictive P lambda t side := by
    ext A hA
    rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ K hA]
    simp only [scalarMomentPrior, lintegral_finsetSum_measure, lintegral_smul_measure,
      lintegral_dirac, scalarPoissonPredictive, Causalean.Stat.mixture_apply,
      smul_eq_mul]
    simp only [hKfiber]
  rw [hpred false, hpred true] at htv
  calc
    _ ≤ Real.sqrt (Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L
      ((2 * lambda * t ^ 2) * 1 ^ 2)) := htv
    _ ≤ (2 : ℝ) ^ (-(L : ℝ) / 4) := by
      let z : ℝ := 2 * lambda * t ^ 2
      have hz : 0 ≤ z := by dsimp [z]; positivity
      have hzL : z ≤ (L : ℝ) / 50 := by
        dsimp [z]
        linarith
      have hterm (n : ℕ) (hLn : L < n) :
          z ^ n / (n.factorial : ℝ) ≤ (1 / 4 : ℝ) ^ n := by
        have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le L) hLn
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
        have he : 0 < Real.exp 1 := Real.exp_pos 1
        have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
          rw [Real.one_le_sqrt]
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith [Real.pi_gt_three]
        have hbase : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
        have hfac : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
          calc
            _ ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) *
                ((n : ℝ) / Real.exp 1) ^ n := by nlinarith
            _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
        have hbasepos : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
        have hratio_nonneg : 0 ≤ z * Real.exp 1 / (n : ℝ) := by positivity
        have hratio : z * Real.exp 1 / (n : ℝ) ≤ (1 / 4 : ℝ) := by
          have hLnR : (L : ℝ) ≤ n := by exact_mod_cast hLn.le
          have he3 : z * Real.exp 1 ≤ 3 * z :=
            by simpa [mul_comm] using
              (mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hz)
          have haux : z * Real.exp 1 ≤ (1 / 4 : ℝ) * n := by
            linarith
          exact (div_le_iff₀ hnR).2 haux
        calc
          z ^ n / (n.factorial : ℝ) ≤
              z ^ n / (((n : ℝ) / Real.exp 1) ^ n) :=
            div_le_div_of_nonneg_left (pow_nonneg hz n) hbasepos hfac
          _ = (z * Real.exp 1 / (n : ℝ)) ^ n := by
            rw [← div_pow]
            congr 1
            field_simp
          _ ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ hratio_nonneg hratio n
      let f : ℕ → ℝ := fun n => if L < n then z ^ n / (n.factorial : ℝ) else 0
      let g : ℕ → ℝ := fun n => if L < n then (1 / 4 : ℝ) ^ n else 0
      have hq : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
        summable_geometric_of_norm_lt_one (by norm_num)
      have hg : Summable g := by
        apply hq.of_nonneg_of_le
        · intro n
          dsimp [g]
          positivity
        · intro n
          dsimp [g]
          split_ifs
          · exact le_refl _
          · positivity
      have hf_nonneg : ∀ n, 0 ≤ f n := by
        intro n
        dsimp [f]
        positivity
      have hfg : ∀ n, f n ≤ g n := by
        intro n
        dsimp [f, g]
        split_ifs with hn
        · exact hterm n hn
        · rfl
      have hf : Summable f := hg.of_nonneg_of_le hf_nonneg hfg
      have hgeo : (∑' n : ℕ, g n) ≤ (1 / 4 : ℝ) ^ L := by
        have hzero_sum :
            ((Finset.range (L + 1)).sum (fun n : ℕ => g n)) = 0 := by
          apply Finset.sum_eq_zero
          intro n hn
          have hnle : n ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
          simp [g, Nat.not_lt_of_ge hnle]
        rw [← hg.sum_add_tsum_nat_add (L + 1), hzero_sum, zero_add]
        simp only [show ∀ n : ℕ, L < n + (L + 1) by omega, if_true, g, pow_add]
        rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num)]
        norm_num [pow_succ]
        have hp : 0 ≤ (1 / 4 : ℝ) ^ L := pow_nonneg (by norm_num) L
        nlinarith
      have htail :
          Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L z ≤
            (1 / 4 : ℝ) ^ L := by
        unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
        change (∑' n, f n) ≤ _
        exact (hf.tsum_le_tsum hfg hg).trans hgeo
      have hsqrt : Real.sqrt
          (Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L z) ≤
          (1 / 2 : ℝ) ^ L := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, htail.trans_eq ?_⟩
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega
      have hpow : (1 / 2 : ℝ) ^ L = (2 : ℝ) ^ (-(L : ℝ)) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      simpa only [one_pow, mul_one, z] using
        hsqrt.trans (hpow ▸ Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) (by have := Nat.cast_nonneg (α := ℝ) L; linarith))

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
