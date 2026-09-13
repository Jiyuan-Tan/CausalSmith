import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.Certificate
import Causalean.Stat.Minimax.MomentMatchedMixture.SupportLocalized
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.WithDensity

/-!
# Aggregate affine-Poisson moment-matched mixtures

This module isolates the analytic core needed by the marked experiment.  It
combines the treated counts before marking, leaving two independent Poisson
counts whose affine rates add to `t * p`.  The resulting Jordan-prior mixture
is controlled by the standard exponential-Gram moment-matching bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- The [defined object](goal) is determined by the displayed assumptions and is given by [the following defining expression](step:1).  The two-count observation consisting of aggregate treated and aggregate
control counts. -/
abbrev AggregatePoissonObservation := ℕ × ℕ

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1). -/
def aggregateTreatedRate (ε a t p : ℝ) : ℝ := t * ε * (p + a)

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1). -/
def aggregateControlRate (ε a t p : ℝ) : ℝ :=
  t * ((1 - ε) * p - ε * a)

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  The explicit pair of independent Poisson laws with aggregate treated and
control rates. -/
noncomputable def aggregatePoissonLaw
    (ε a t p : ℝ) : Measure AggregatePoissonObservation :=
  (poissonMeasure (Real.toNNReal (aggregateTreatedRate ε a t p))).prod
    (poissonMeasure (Real.toNNReal (aggregateControlRate ε a t p)))

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  Every aggregate two-count law is a probability measure. -/
noncomputable instance aggregatePoissonLaw_isProbabilityMeasure
    (ε a t p : ℝ) : IsProbabilityMeasure (aggregatePoissonLaw ε a t p) := by
  unfold aggregatePoissonLaw
  infer_instance

private noncomputable def aggregatePoissonKernelOfRealRate
    (r : ℝ → ℝ) : Kernel ℝ ℕ :=
  (Kernel.const ℝ Measure.count).withDensity fun p n =>
    ENNReal.ofReal (Real.exp (-(Real.toNNReal (r p) : ℝ)) *
      (Real.toNNReal (r p) : ℝ) ^ n / Nat.factorial n)

private noncomputable instance aggregatePoissonKernelOfRealRate_isSFinite
    (r : ℝ → ℝ) : IsSFiniteKernel (aggregatePoissonKernelOfRealRate r) := by
  unfold aggregatePoissonKernelOfRealRate
  apply Kernel.IsSFiniteKernel.withDensity
  simp

private theorem aggregatePoissonKernelOfRealRate_apply
    (r : ℝ → ℝ) (hr : Measurable r) (p : ℝ) :
    aggregatePoissonKernelOfRealRate r p = poissonMeasure (Real.toNNReal (r p)) := by
  rw [aggregatePoissonKernelOfRealRate, Kernel.withDensity_apply]
  · apply Measure.ext_of_singleton
    intro n
    rw [withDensity_apply _ (measurableSet_singleton n), poissonMeasure_singleton]
    simp
  · apply measurable_from_prod_countable_left
    intro n
    fun_prop

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t) and is given by [the following defining expression](step:1).  The aggregate affine-Poisson experiment as a kernel from latent mass to
the treated/control count pair. -/
noncomputable def aggregatePoissonKernel (ε a t : ℝ) :
    Kernel ℝ AggregatePoissonObservation :=
  (aggregatePoissonKernelOfRealRate (aggregateTreatedRate ε a t)).prod
    (aggregatePoissonKernelOfRealRate (aggregateControlRate ε a t))

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t), [the latent mass](hyp:p).  The aggregate kernel fibre is the explicit product-Poisson law. -/
theorem aggregatePoissonKernel_apply (ε a t p : ℝ) :
    aggregatePoissonKernel ε a t p = aggregatePoissonLaw ε a t p := by
  unfold aggregatePoissonKernel aggregatePoissonLaw
  rw [Kernel.prod_apply,
    aggregatePoissonKernelOfRealRate_apply _ (by
      change Measurable (fun p : ℝ => t * ε * (p + a))
      fun_prop),
    aggregatePoissonKernelOfRealRate_apply _ (by
      change Measurable (fun p : ℝ => t * ((1 - ε) * p - ε * a))
      fun_prop)]

private noncomputable def affinePoissonLikelihood
    (q s θ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-s * θ) * (1 + s * θ / q) ^ n

private lemma measurable_affinePoissonLikelihood (q s : ℝ) :
    Measurable (fun z : ℝ × ℕ => affinePoissonLikelihood q s z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro n
  unfold affinePoissonLikelihood
  fun_prop

private lemma affinePoissonLikelihood_nonnegative
    (q s θ : ℝ) (hq : 0 < q) (hr : 0 ≤ q + s * θ) (n : ℕ) :
    0 ≤ affinePoissonLikelihood q s θ n := by
  unfold affinePoissonLikelihood
  apply mul_nonneg (Real.exp_pos _).le (pow_nonneg _ _)
  rw [show 1 + s * θ / q = (q + s * θ) / q by field_simp]
  positivity

private lemma poisson_power_mgf (q : NNReal) (u : ℝ) :
    (∫ n : ℕ, u ^ n ∂poissonMeasure q) =
      Real.exp ((q : ℝ) * (u - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [show (fun n : ℕ => Real.exp (-(q : ℝ)) * (q : ℝ) ^ n /
      (n.factorial : ℝ) * u ^ n) =
      fun n => Real.exp (-(q : ℝ)) * (((q : ℝ) * u) ^ n /
        (n.factorial : ℝ)) by
    funext n
    rw [mul_pow]
    ring]
  rw [tsum_mul_left]
  rw [show (∑' n : ℕ, ((q : ℝ) * u) ^ n / (n.factorial : ℝ)) =
      Real.exp ((q : ℝ) * u) by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((q : ℝ) * u)).tsum_eq]
  rw [← Real.exp_add]
  congr 1
  ring

private lemma poisson_affine_eq_withDensity
    (q s θ : ℝ) (hq : 0 < q) (hr : 0 ≤ q + s * θ) :
    poissonMeasure (Real.toNNReal (q + s * θ)) =
      (poissonMeasure (Real.toNNReal q)).withDensity
        (fun n => ENNReal.ofReal (affinePoissonLikelihood q s θ n)) := by
  apply Measure.ext_of_singleton
  intro n
  rw [withDensity_apply _ (measurableSet_singleton n)]
  simp [poissonMeasure_singleton]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  have hlik : 0 ≤ affinePoissonLikelihood q s θ n :=
    affinePoissonLikelihood_nonnegative q s θ hq hr n
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hlik]
  rw [max_eq_left hr, max_eq_left hq.le]
  unfold affinePoissonLikelihood
  rw [show 1 + s * θ / q = (q + s * θ) / q by field_simp, div_pow]
  field_simp
  have hexp : Real.exp (-(q + s * θ)) =
      Real.exp (-q) * Real.exp (-(s * θ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

private lemma affinePoissonLikelihood_inner
    (q s θ θ' : ℝ) (hq : 0 < q) :
    (∫ n : ℕ, affinePoissonLikelihood q s θ n *
        affinePoissonLikelihood q s θ' n ∂poissonMeasure (Real.toNNReal q)) =
      Real.exp ((s ^ 2 / q) * θ * θ') := by
  rw [show (fun n : ℕ => affinePoissonLikelihood q s θ n *
      affinePoissonLikelihood q s θ' n) = fun n =>
        (Real.exp (-s * θ) * Real.exp (-s * θ')) *
          (((1 + s * θ / q) * (1 + s * θ' / q)) ^ n) by
    funext n
    simp only [affinePoissonLikelihood, mul_pow]
    ring]
  rw [integral_const_mul, poisson_power_mgf,
    Real.coe_toNNReal _ hq.le, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

private noncomputable def aggregateCenteredLikelihood
    (qT qC sT sC θ : ℝ) (z : AggregatePoissonObservation) : ℝ :=
  affinePoissonLikelihood qT sT θ z.1 *
    affinePoissonLikelihood qC sC θ z.2

private lemma measurable_aggregateCenteredLikelihood (qT qC sT sC : ℝ) :
    Measurable (fun z : ℝ × AggregatePoissonObservation =>
      aggregateCenteredLikelihood qT qC sT sC z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro z
  unfold aggregateCenteredLikelihood affinePoissonLikelihood
  fun_prop

private lemma aggregateCenteredLikelihood_nonnegative
    (qT qC sT sC θ : ℝ) (hqT : 0 < qT) (hqC : 0 < qC)
    (hrT : 0 ≤ qT + sT * θ) (hrC : 0 ≤ qC + sC * θ)
    (z : AggregatePoissonObservation) :
    0 ≤ aggregateCenteredLikelihood qT qC sT sC θ z := by
  exact mul_nonneg
    (affinePoissonLikelihood_nonnegative qT sT θ hqT hrT z.1)
    (affinePoissonLikelihood_nonnegative qC sC θ hqC hrC z.2)

private lemma aggregatePoissonLaw_centered_eq_withDensity
    (ε a t c θ qT qC sT sC : ℝ)
    (hqT : 0 < qT) (hqC : 0 < qC)
    (hrT : 0 ≤ qT + sT * θ) (hrC : 0 ≤ qC + sC * θ)
    (hT : aggregateTreatedRate ε a t (θ + c) = qT + sT * θ)
    (hC : aggregateControlRate ε a t (θ + c) = qC + sC * θ) :
    aggregatePoissonLaw ε a t (θ + c) =
      ((poissonMeasure (Real.toNNReal qT)).prod
        (poissonMeasure (Real.toNNReal qC))).withDensity
          (fun z => ENNReal.ofReal
            (aggregateCenteredLikelihood qT qC sT sC θ z)) := by
  unfold aggregatePoissonLaw
  rw [hT, hC, poisson_affine_eq_withDensity qT sT θ hqT hrT,
    poisson_affine_eq_withDensity qC sC θ hqC hrC,
    prod_withDensity
      (measurable_of_countable _)
      (measurable_of_countable _)]
  apply withDensity_congr_ae
  filter_upwards with z
  rw [aggregateCenteredLikelihood,
    ENNReal.ofReal_mul
      (affinePoissonLikelihood_nonnegative qT sT θ hqT hrT z.1)]

private lemma aggregateCenteredLikelihood_inner
    (qT qC sT sC θ θ' : ℝ) (hqT : 0 < qT) (hqC : 0 < qC) :
    (∫ z : AggregatePoissonObservation,
        aggregateCenteredLikelihood qT qC sT sC θ z *
          aggregateCenteredLikelihood qT qC sT sC θ' z
      ∂(poissonMeasure (Real.toNNReal qT)).prod
        (poissonMeasure (Real.toNNReal qC))) =
      Real.exp ((sT ^ 2 / qT + sC ^ 2 / qC) * θ * θ') := by
  rw [show (fun z : AggregatePoissonObservation =>
      aggregateCenteredLikelihood qT qC sT sC θ z *
        aggregateCenteredLikelihood qT qC sT sC θ' z) = fun z =>
      (affinePoissonLikelihood qT sT θ z.1 *
        affinePoissonLikelihood qT sT θ' z.1) *
      (affinePoissonLikelihood qC sC θ z.2 *
        affinePoissonLikelihood qC sC θ' z.2) by
    funext z
    simp only [aggregateCenteredLikelihood]
    ring]
  rw [integral_prod_mul
      (fun n => affinePoissonLikelihood qT sT θ n *
        affinePoissonLikelihood qT sT θ' n)
      (fun n => affinePoissonLikelihood qC sC θ n *
        affinePoissonLikelihood qC sC θ' n),
    affinePoissonLikelihood_inner qT sT θ θ' hqT,
    affinePoissonLikelihood_inner qC sC θ θ' hqC,
    ← Real.exp_add]
  congr 1
  ring

/-- The [defined object](goal) is determined by [the latent prior](hyp:π), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the aggregate intensity](hyp:t) and is given by [the following defining expression](step:1).  Mixing the aggregate affine-Poisson kernel against a latent prior gives
its prior-predictive treated/control count law. -/
noncomputable def aggregatePoissonPredictive
    (π : Measure ℝ) (ε a t : ℝ) : Measure AggregatePoissonObservation :=
  Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π
    (aggregatePoissonKernel ε a t)

private lemma geometric_quarter_tail (L : ℕ) :
    (∑' n : ℕ, if L < n then (1 / 4 : ℝ) ^ n else 0) ≤ (1 / 4 : ℝ) ^ L := by
  have hq : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hf : Summable (fun n : ℕ => if L < n then (1 / 4 : ℝ) ^ n else 0) := by
    apply hq.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      split_ifs
      · rfl
      · positivity
  have hzero :
      ((Finset.range (L + 1)).sum
        fun n : ℕ => if L < n then (1 / 4 : ℝ) ^ n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnle : n ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [if_neg (Nat.not_lt_of_ge hnle)]
  rw [← hf.sum_add_tsum_nat_add (L + 1), hzero, zero_add]
  simp only [show ∀ n : ℕ, L < n + (L + 1) by omega, if_true, pow_add]
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num)]
  norm_num [pow_succ]
  have hp : 0 ≤ (1 / 4 : ℝ) ^ L := pow_nonneg (by norm_num) L
  nlinarith

private lemma exponential_term_le_quarter_pow
    (L n : ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hzL : z ≤ (L : ℝ) / (16 * Real.exp 1)) (hLn : L < n) :
    z ^ n / (n.factorial : ℝ) ≤ (1 / 4 : ℝ) ^ n := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le L) hLn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  have hbase : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hfac :
      ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n ≤
          Real.sqrt (2 * Real.pi * (n : ℝ)) *
            ((n : ℝ) / Real.exp 1) ^ n := by
              nlinarith
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  have hbasepos : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hratio_nonneg : 0 ≤ z * Real.exp 1 / (n : ℝ) := by positivity
  have hratio : z * Real.exp 1 / (n : ℝ) ≤ (1 / 16 : ℝ) := by
    calc
      z * Real.exp 1 / (n : ℝ) ≤
          ((L : ℝ) / (16 * Real.exp 1)) * Real.exp 1 / (n : ℝ) := by
            gcongr
      _ = (L : ℝ) / (16 * (n : ℝ)) := by field_simp
      _ ≤ 1 / 16 := by
        rw [div_le_iff₀ (by positivity)]
        calc
          (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLn.le
          _ = 1 / 16 * (16 * (n : ℝ)) := by ring
  calc
    z ^ n / (n.factorial : ℝ) ≤
        z ^ n / (((n : ℝ) / Real.exp 1) ^ n) :=
      div_le_div_of_nonneg_left (pow_nonneg hz n) hbasepos hfac
    _ = (z * Real.exp 1 / (n : ℝ)) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ (1 / 16 : ℝ) ^ n := pow_le_pow_left₀ hratio_nonneg hratio n
    _ ≤ (1 / 4 : ℝ) ^ n := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- The [stated conclusion](goal) follows from [the tail-scale constant](hyp:A), [positive tail-scale constant](hyp:hA).  A square root of an exponential-series tail is uniformly geometric in
the matching degree when its argument is at most a sufficiently small fixed
multiple of that degree. -/
theorem exists_geometric_sqrt_exponentialSeriesTail_bound
    (A : ℝ) (hA : 0 < A) :
    ∃ b D ρ : ℝ, 0 < b ∧ 0 < D ∧ ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (L : ℕ) (x : ℝ), 0 ≤ x → x ≤ b * L →
        Real.sqrt
            (Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L
              (A * x)) ≤
          D * ρ ^ L := by
  refine ⟨1 / (16 * A * Real.exp 1), 1, 1 / 2, by positivity, by norm_num,
    ⟨by norm_num, by norm_num⟩, ?_⟩
  intro L x hx hband
  obtain rfl | hL := L.eq_zero_or_pos
  · have hxle : x ≤ 0 := by simpa using hband
    have hxeq : x = 0 := le_antisymm hxle hx
    subst x
    have htailzero :
        Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail 0 0 = 0 := by
      unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
      rw [show (fun n : ℕ =>
          if 0 < n then (0 : ℝ) ^ n / (n.factorial : ℝ) else 0) = 0 by
        funext n
        split_ifs with hn
        · simp [zero_pow (Nat.ne_of_gt hn)]
        · rfl]
      exact tsum_zero
    simp only [mul_zero]
    rw [htailzero, Real.sqrt_zero, pow_zero]
    norm_num
  have hz : 0 ≤ A * x := mul_nonneg hA.le hx
  have hzL : A * x ≤ (L : ℝ) / (16 * Real.exp 1) := by
    calc
      A * x ≤ A * ((1 / (16 * A * Real.exp 1)) * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hband hA.le
      _ = (L : ℝ) / (16 * Real.exp 1) := by field_simp
  let f : ℕ → ℝ := fun n =>
    if L < n then (A * x) ^ n / (n.factorial : ℝ) else 0
  let g : ℕ → ℝ := fun n =>
    if L < n then (1 / 4 : ℝ) ^ n else 0
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
      · rfl
      · positivity
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    positivity
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    dsimp [f, g]
    split_ifs with hn
    · exact exponential_term_le_quarter_pow L n (A * x) hz hzL hn
    · rfl
  have hf : Summable f := hg.of_nonneg_of_le hf_nonneg hfg
  have htail :
      Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L (A * x) ≤
        (1 / 4 : ℝ) ^ L := by
    unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
    change (∑' n, f n) ≤ _
    exact (hf.tsum_le_tsum hfg hg).trans (geometric_quarter_tail L)
  rw [one_mul, Real.sqrt_le_iff]
  refine ⟨by positivity, htail.trans_eq ?_⟩
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  omega

namespace NormalizedFiniteSignedMomentCertificate

private lemma positivePrior_le_two_variation
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.positivePrior ≤ (2 : ℝ≥0∞) • C.signedMeasure.variation := by
  intro s
  rw [positivePrior, variation_eq_absoluteMeasure, absoluteMeasure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hcoef : ENNReal.ofReal (2 * max (C.weight i) 0) ≤
      2 * ENNReal.ofReal |C.weight i| := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (le_abs_self _)) 2
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcoef bot_le

private lemma negativePrior_le_two_variation
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L) :
    C.negativePrior ≤ (2 : ℝ≥0∞) • C.signedMeasure.variation := by
  intro s
  rw [negativePrior, variation_eq_absoluteMeasure, absoluteMeasure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hcoef : ENNReal.ofReal (2 * max (-C.weight i) 0) ≤
      2 * ENNReal.ofReal |C.weight i| := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (neg_le_abs _)) 2
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcoef bot_le

private lemma jordanPriors_ae_of_variation
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L) {P : ℝ → Prop}
    (hP : ∀ᵐ p ∂C.signedMeasure.variation, P p) :
    (∀ᵐ p ∂C.positivePrior, P p) ∧ ∀ᵐ p ∂C.negativePrior, P p := by
  constructor
  · exact (Measure.absolutelyContinuous_of_le_smul
      (positivePrior_le_two_variation C)).ae_le hP
  · exact (Measure.absolutelyContinuous_of_le_smul
      (negativePrior_le_two_variation C)).ae_le hP

private lemma integrable_pow_of_Icc_support
    (π : Measure ℝ) [IsProbabilityMeasure π] (l u : ℝ)
    (hsupp : ∀ᵐ x ∂π, x ∈ Set.Icc l u) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) π := by
  apply Integrable.of_bound (by fun_prop) (max |l| |u| ^ n)
  filter_upwards [hsupp] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg x) _ n
  rw [abs_le]
  constructor
  · calc
      -max |l| |u| ≤ -|l| := neg_le_neg (le_max_left _ _)
      _ ≤ l := neg_abs_le l
      _ ≤ x := hx.1
  · exact hx.2.trans (le_trans (le_abs_self u) (le_max_right _ _))

private lemma centered_map_moments_eq
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (l u c : ℝ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc l u)
    (n : ℕ) (hn : n ≤ L) :
    (∫ θ, θ ^ n ∂Measure.map (fun p : ℝ => p - c) C.positivePrior) =
      ∫ θ, θ ^ n ∂Measure.map (fun p : ℝ => p - c) C.negativePrior := by
  rcases jordanPriors_ae_of_variation C hsupp with ⟨hsuppP, hsuppN⟩
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [sub_pow]
  rw [integral_finsetSum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    simp_rw [integral_mul_const, integral_const_mul]
    rw [C.jordanPriors_moments_eq j
      (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hn)]
  · intro j hj
    exact (((integrable_pow_of_Icc_support C.negativePrior l u hsuppN j).const_mul
      ((-1 : ℝ) ^ (j + n))).mul_const (c ^ (n - j))).mul_const (n.choose j : ℝ)
  · intro j hj
    exact (((integrable_pow_of_Icc_support C.positivePrior l u hsuppP j).const_mul
      ((-1 : ℝ) ^ (j + n))).mul_const (c ^ (n - j))).mul_const (n.choose j : ℝ)

private lemma measure_set_eq_one_of_ae_mem
    (π : Measure ℝ) [IsProbabilityMeasure π] (s : Set ℝ)
    (hs : MeasurableSet s) (hae : ∀ᵐ x ∂π, x ∈ s) : π s = 1 := by
  have hcompl : π sᶜ = 0 := by
    rw [ae_iff] at hae
    change π {a | a ∉ s} = 0
    exact hae
  rw [← compl_compl s, measure_compl hs.compl (measure_ne_top π _), hcompl,
    measure_univ]
  simp

private lemma centered_map_supported
    (π : Measure ℝ) [IsProbabilityMeasure π] (l u c R : ℝ)
    (hc : c = (l + u) / 2) (hR : R = (u - l) / 2)
    (hsupp : ∀ᵐ p ∂π, p ∈ Set.Icc l u) :
    (Measure.map (fun p : ℝ => p - c) π) {θ | |θ| ≤ R} = 1 := by
  letI : IsProbabilityMeasure (Measure.map (fun p : ℝ => p - c) π) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply measure_set_eq_one_of_ae_mem _ _
    (measurableSet_le continuous_abs.measurable measurable_const)
  change ∀ᵐ θ ∂Measure.map (fun p : ℝ => p - c) π, |θ| ≤ R
  rw [ae_map_iff (by fun_prop)
    (measurableSet_le continuous_abs.measurable measurable_const)]
  filter_upwards [hsupp] with p hp
  rw [abs_le]
  constructor <;> rw [hc, hR] <;> linarith [hp.1, hp.2]

private lemma priorPredictive_centered_map
    (π : Measure ℝ) (K : Kernel ℝ AggregatePoissonObservation) (c : ℝ) :
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        (Measure.map (fun p : ℝ => p - c) π)
        (K.comap (fun θ : ℝ => θ + c) (by fun_prop)) =
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π K := by
  apply Measure.ext
  intro s hs
  rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _ hs,
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _ hs,
    lintegral_map
      ((K.comap (fun θ : ℝ => θ + c) (by fun_prop)).measurable_coe hs)
      (by fun_prop)]
  apply lintegral_congr
  intro p
  simp

private lemma exponentialSeriesTail_mono (L : ℕ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L x ≤
      Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hsumY : Summable (fun n : ℕ => y ^ n / (n.factorial : ℝ)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp y).summable
  have htailY : Summable (fun n : ℕ =>
      if L < n then y ^ n / (n.factorial : ℝ) else 0) := by
    apply hsumY.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      split_ifs
      · rfl
      · positivity
  have htailX : Summable (fun n : ℕ =>
      if L < n then x ^ n / (n.factorial : ℝ) else 0) := by
    apply htailY.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      split_ifs
      · gcongr
      · rfl
  unfold Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
  apply htailX.tsum_le_tsum _ htailY
  intro n
  split_ifs
  · gcongr
  · rfl

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ).  For fixed overlap geometry, the aggregate affine-Poisson mixtures of the
positive and negative Jordan priors satisfy a square-root exponential-tail TV
bound with argument proportional to `t * B`. -/
theorem exists_aggregatePoisson_jordan_sqrt_tail_bound
    (ε κ : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκ : κ = (1 - 2 * ε) / ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ {ι : Type*} [Fintype ι] {L : ℕ}
        (C : NormalizedFiniteSignedMomentCertificate ι L)
        (a B t : ℝ),
        0 < a → 0 < B → 0 < t →
        (∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) →
        Causalean.Stat.tvDist
            (aggregatePoissonPredictive C.positivePrior ε a t)
            (aggregatePoissonPredictive C.negativePrior ε a t) ≤
          Real.sqrt
            (Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail L
              (A * (t * B))) := by
  have hden : 0 < 1 - 2 * ε := by nlinarith
  have hκpos : 0 < κ := by rw [hκ]; positivity
  let A : ℝ := 2 * ε + 2 * (1 - ε) ^ 2 / ε
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro ι _ L C a B t ha hB ht hsupp
  let l : ℝ := a / κ
  let c : ℝ := (l + B) / 2
  let R : ℝ := (B - l) / 2
  let qT : ℝ := t * ε * (c + a)
  let qC : ℝ := t * ((1 - ε) * c - ε * a)
  let sT : ℝ := t * ε
  let sC : ℝ := t * (1 - ε)
  let lambda : ℝ := sT ^ 2 / qT + sC ^ 2 / qC
  let πP : Measure ℝ := Measure.map (fun p : ℝ => p - c) C.positivePrior
  let πN : Measure ℝ := Measure.map (fun p : ℝ => p - c) C.negativePrior
  let Kc : Kernel ℝ AggregatePoissonObservation :=
    (aggregatePoissonKernel ε a t).comap (fun θ : ℝ => θ + c) (by fun_prop)
  let Q : Measure AggregatePoissonObservation :=
    (poissonMeasure (Real.toNNReal qT)).prod
      (poissonMeasure (Real.toNNReal qC))
  let likelihood : ℝ → AggregatePoissonObservation → ℝ :=
    aggregateCenteredLikelihood qT qC sT sC
  have hlB : l ≤ B := by
    rcases hsupp.exists with ⟨p, hp⟩
    exact hp.1.trans hp.2
  have hlpos : 0 < l := div_pos ha hκpos
  have ha_le : a ≤ κ * B := by
    simpa [mul_comm] using
      (div_le_iff₀ hκpos).mp (by simpa [l] using hlB)
  have hcontrol_l : 0 < (1 - ε) * l - ε * a := by
    have hinv : κ⁻¹ = ε / (1 - 2 * ε) := by rw [hκ, inv_div]
    have hden' : 1 - ε * 2 ≠ 0 := by nlinarith
    have hid : (1 - ε) * l - ε * a = a * ε ^ 2 / (1 - 2 * ε) := by
      dsimp [l]
      rw [div_eq_mul_inv, hinv]
      field_simp [hden']
      ring
    rw [hid]
    positivity
  have hcontrol_B : ε * B ≤ (1 - ε) * B - ε * a := by
    have hκmul : ε * κ = 1 - 2 * ε := by
      rw [hκ]
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left ha_le hε.le]
  have hc_ge_halfB : B / 2 ≤ c := by
    dsimp [c]
    nlinarith [hlpos.le]
  have hRnonneg : 0 ≤ R := by dsimp [R]; linarith
  have hRleB : R ≤ B := by dsimp [R]; nlinarith [hlpos.le]
  have hqT_lower : t * ε * (B / 2) ≤ qT := by
    dsimp [qT]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg ht.le hε.le)
    linarith [ha]
  have hqT : 0 < qT := lt_of_lt_of_le (by positivity) hqT_lower
  have hqC_lower : t * (ε * B / 2) ≤ qC := by
    dsimp [qC, c]
    have hcidentity : (1 - ε) * ((l + B) / 2) - ε * a =
        (((1 - ε) * l - ε * a) + ((1 - ε) * B - ε * a)) / 2 := by ring
    rw [hcidentity]
    have : ε * B / 2 ≤
        (((1 - ε) * l - ε * a) + ((1 - ε) * B - ε * a)) / 2 := by
      nlinarith [hcontrol_l, hcontrol_B]
    exact mul_le_mul_of_nonneg_left this ht.le
  have hqC : 0 < qC := lt_of_lt_of_le (by positivity) hqC_lower
  have hlambda : 0 ≤ lambda := by
    dsimp [lambda]
    positivity
  have hcenter_mem (θ : ℝ) (hθ : |θ| ≤ R) : θ + c ∈ Set.Icc l B := by
    rw [abs_le] at hθ
    constructor <;> dsimp [c, R] at * <;> linarith
  have hrates (θ : ℝ) (hθ : |θ| ≤ R) :
      0 ≤ qT + sT * θ ∧ 0 ≤ qC + sC * θ := by
    have hp := hcenter_mem θ hθ
    constructor
    · have : 0 < θ + c + a := lt_of_lt_of_le
        (add_pos hlpos ha) (by linarith [hp.1])
      dsimp [qT, sT]
      nlinarith [mul_pos (mul_pos ht hε) this]
    · have hc0 : 0 ≤ (1 - ε) * (θ + c) - ε * a :=
        (le_of_lt hcontrol_l).trans (by
          have he1 : 0 ≤ 1 - ε := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hp.1 he1])
      dsimp [qC, sC]
      nlinarith [mul_nonneg ht.le hc0]
  have hparamT (θ : ℝ) :
      aggregateTreatedRate ε a t (θ + c) = qT + sT * θ := by
    dsimp [aggregateTreatedRate, qT, sT]
    ring
  have hparamC (θ : ℝ) :
      aggregateControlRate ε a t (θ + c) = qC + sC * θ := by
    dsimp [aggregateControlRate, qC, sC]
    ring
  haveI : IsProbabilityMeasure πP := by
    dsimp [πP]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure πN := by
    dsimp [πN]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  have hKprob : ∀ θ, IsProbabilityMeasure (Kc θ) := by
    intro θ
    dsimp [Kc]
    rw [aggregatePoissonKernel_apply]
    infer_instance
  have hmeas : Measurable (fun z : ℝ × AggregatePoissonObservation =>
      likelihood z.1 z.2) := by
    exact measurable_aggregateCenteredLikelihood qT qC sT sC
  have hnonneg : ∀ θ, |θ| ≤ R → ∀ z, 0 ≤ likelihood θ z := by
    intro θ hθ z
    exact aggregateCenteredLikelihood_nonnegative qT qC sT sC θ hqT hqC
      (hrates θ hθ).1 (hrates θ hθ).2 z
  have hdensity : ∀ θ, |θ| ≤ R →
      Kc θ = Q.withDensity fun z => ENNReal.ofReal (likelihood θ z) := by
    intro θ hθ
    dsimp [Kc, Q, likelihood]
    rw [aggregatePoissonKernel_apply]
    exact aggregatePoissonLaw_centered_eq_withDensity ε a t c θ qT qC sT sC
      hqT hqC (hrates θ hθ).1 (hrates θ hθ).2 (hparamT θ) (hparamC θ)
  have hinner : ∀ θ, |θ| ≤ R → ∀ θ', |θ'| ≤ R →
      ∫ z, likelihood θ z * likelihood θ' z ∂Q =
        Real.exp (lambda * θ * θ') := by
    intro θ hθ θ' hθ'
    exact aggregateCenteredLikelihood_inner qT qC sT sC θ θ' hqT hqC
  rcases jordanPriors_ae_of_variation C hsupp with ⟨hsuppP, hsuppN⟩
  have hsuppπP : πP {θ | |θ| ≤ R} = 1 := by
    exact centered_map_supported C.positivePrior l B c R rfl rfl hsuppP
  have hsuppπN : πN {θ | |θ| ≤ R} = 1 := by
    exact centered_map_supported C.negativePrior l B c R rfl rfl hsuppN
  have hmom : ∀ n ≤ L, ∫ θ, θ ^ n ∂πP = ∫ θ, θ ^ n ∂πN := by
    intro n hn
    exact centered_map_moments_eq C l B c hsupp n hn
  have hlambdaR : lambda * R ^ 2 ≤ A * (t * B) := by
    have hqTbound : sT ^ 2 / qT ≤ 2 * t * ε / B := by
      rw [div_le_iff₀ hqT]
      have := hqT_lower
      dsimp [sT]
      field_simp
      nlinarith
    have hqCbound : sC ^ 2 / qC ≤ 2 * t * (1 - ε) ^ 2 / (ε * B) := by
      rw [div_le_iff₀ hqC]
      have := hqC_lower
      dsimp [sC]
      field_simp
      nlinarith [sq_nonneg (1 - ε)]
    have hR2 : R ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg R, sq_nonneg B]
    dsimp [lambda, A]
    calc
      (sT ^ 2 / qT + sC ^ 2 / qC) * R ^ 2 ≤
          (2 * t * ε / B + 2 * t * (1 - ε) ^ 2 / (ε * B)) * R ^ 2 := by
            gcongr
      _ ≤ (2 * t * ε / B + 2 * t * (1 - ε) ^ 2 / (ε * B)) * B ^ 2 := by
            gcongr
      _ = (2 * ε + 2 * (1 - ε) ^ 2 / ε) * (t * B) := by
            field_simp
  have htv :=
    Causalean.Stat.Minimax.MomentMatchedMixture.momentMatchedMixture_tv_le_sqrt_tail_of_supported
      πP πN Kc Q likelihood hKprob lambda R L hlambda hRnonneg hmeas hnonneg
      hdensity hinner hsuppπP hsuppπN hmom
  rw [priorPredictive_centered_map C.positivePrior (aggregatePoissonKernel ε a t) c,
    priorPredictive_centered_map C.negativePrior (aggregatePoissonKernel ε a t) c] at htv
  exact htv.trans (Real.sqrt_le_sqrt
    (exponentialSeriesTail_mono L (mul_nonneg hlambda (sq_nonneg R)) hlambdaR))

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ).  For fixed overlap geometry, moment matching makes the two aggregate
Jordan-prior predictive laws geometrically close whenever `t * B` is at most
a sufficiently small multiple of the matching degree. -/
theorem exists_geometric_aggregatePoisson_jordan_tv_bound
    (ε κ : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκ : κ = (1 - 2 * ε) / ε) :
    ∃ b D ρ : ℝ, 0 < b ∧ 0 < D ∧ ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ {ι : Type*} [Fintype ι] {L : ℕ}
        (C : NormalizedFiniteSignedMomentCertificate ι L)
        (a B t : ℝ),
        0 < a → 0 < B → 0 < t →
        (∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) →
        t * B ≤ b * L →
        Causalean.Stat.tvDist
            (aggregatePoissonPredictive C.positivePrior ε a t)
            (aggregatePoissonPredictive C.negativePrior ε a t) ≤
          D * ρ ^ L := by
  rcases exists_aggregatePoisson_jordan_sqrt_tail_bound ε κ hε hεhalf hκ with
    ⟨A, hA, htail⟩
  rcases exists_geometric_sqrt_exponentialSeriesTail_bound A hA with
    ⟨b, D, ρ, hb, hD, hρ, hgeom⟩
  refine ⟨b, D, ρ, hb, hD, hρ, ?_⟩
  intro ι _ L C a B t ha hB ht hsupp hband
  exact (htail C a B t ha hB ht hsupp).trans
    (hgeom L (t * B) (mul_nonneg ht.le hB.le) hband)

end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
