import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.AggregatePoisson.Analytic

/-!
# Aggregate Poisson Jordan-prior bounds

This module turns the finite signed certificate into geometric total-variation bounds for aggregate affine-Poisson mixtures.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

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

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ), [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the positive shift](hyp:a), [the support upper bound](hyp:B), [the aggregate intensity](hyp:t).  For fixed overlap geometry, the aggregate affine-Poisson mixtures of the
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

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ), [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the positive shift](hyp:a), [the support upper bound](hyp:B), [the aggregate intensity](hyp:t).  For fixed overlap geometry, moment matching makes the two aggregate
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
