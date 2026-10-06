module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.SyntheticKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Main
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.DimensionPadding
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedMixedCountUpper

/-! TZengFixedPositivityPolynomialFrontier for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: zeng_zero_control_risk_le_minimax
/-- Given [the specified inputs and assumptions](hyp:n,d,ε), [the stated mathematical conclusion holds](goal). -/
lemma zeng_zero_control_risk_le_minimax (n d : ℕ) (ε : ℝ) :
    zengZeroControlRisk n d ε ≤ zengMinimaxRisk n d ε := by
  let T₀ : ZengEstimator n d :=
    ⟨Kernel.const _ (Measure.dirac 0), inferInstance, by
      intro s
      simp [Kernel.const_apply]⟩
  haveI : Nonempty (ZengEstimator n d) := ⟨T₀⟩
  let φ : {P : ZengLaw d // P ∈ zengZeroControlClass d ε} →
      {P : ZengLaw d // P ∈ zengDiscreteClass d ε} :=
    fun P => ⟨P.1, P.2.1⟩
  unfold zengZeroControlRisk zengMinimaxRisk
  apply Causalean.Stat.minimaxValue_mono_class_of_nonneg φ
  · intro T P
    exact (zeng_squaredRisk_bounds ε T P.1 P.2.1).1
  · intro T P
    exact (zeng_squaredRisk_bounds ε T P.1 P.2).1
  · intro T
    refine ⟨4, ?_⟩
    rintro y ⟨P, rfl⟩
    exact (zeng_squaredRisk_bounds ε T P.1 P.2).2
  · intro T P
    exact le_refl _

-- @node: zeng_parametric_minimax_lower
/-- [the stated mathematical conclusion holds](goal). -/
lemma zeng_parametric_minimax_lower :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (ε : ℝ), 1 ≤ n → 1 ≤ d →
        0 < ε → ε < 1 / 2 →
          c / n ≤ zengMinimaxRisk n d ε := by
  obtain ⟨c, hc, hparam⟩ := zeng_parametric_lower
  refine ⟨c, hc, ?_⟩
  intro n d ε hn hd hε0 hε1
  exact (hparam n d ε hn hd ⟨hε0, hε1⟩).trans
    (zeng_zero_control_risk_le_minimax n d ε)

-- @node: thetaPoly_pointwise_jensen
/-- Given [the specified inputs and assumptions](hyp:n,d,ε,θ,s), [the stated mathematical conclusion holds](goal). -/
lemma thetaPoly_pointwise_jensen (n d : ℕ) (ε θ : ℝ)
    (s : Fin n → ZengRecord d) :
    (thetaPoly n d ε s - θ) ^ 2 ≤
      (∑ u : Fin n → Bool,
        (mixedCountEstimator n d ε
          (fun i => syntheticRecord (s i) (u i)) - θ) ^ 2) / (2 : ℝ) ^ n := by
  let f : (Fin n → Bool) → ℝ := fun u =>
    mixedCountEstimator n d ε (fun i => syntheticRecord (s i) (u i)) - θ
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp
  have hcardR : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hsum : (∑ u : Fin n → Bool, f u) =
      (2 : ℝ) ^ n * (thetaPoly n d ε s - θ) := by
    simp only [f, Finset.sum_sub_distrib]
    simp [thetaPoly, hcard]
    field_simp
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n → Bool)))
    (f := f)
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat, hsum] at hcs
  change (thetaPoly n d ε s - θ) ^ 2 ≤
    (∑ u : Fin n → Bool, f u ^ 2) / (2 : ℝ) ^ n
  apply (le_div_iff₀ hcardR).2
  nlinarith [sq_nonneg ((2 : ℝ) ^ n)]

-- @node: thetaPoly_regular
/-- Given [the specified inputs and assumptions](hyp:n,d,ε), [the stated mathematical conclusion holds](goal). -/
lemma thetaPoly_regular (n d : ℕ) (ε : ℝ) :
    Measurable (thetaPoly n d ε) ∧
      ∀ s, thetaPoly n d ε s ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · exact measurable_of_finite _
  · intro s
    have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
      simp
    have hcardR : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hlo : -((2 : ℝ) ^ n) ≤
        ∑ u : Fin n → Bool,
          mixedCountEstimator n d ε (fun i => syntheticRecord (s i) (u i)) := by
      calc
        -((2 : ℝ) ^ n) =
            ∑ _u : Fin n → Bool, (-1 : ℝ) := by simp [hcard]
        _ ≤ _ := Finset.sum_le_sum (fun u _ => (mixed_count_estimator_regular n d ε).2 _ |>.1)
    have hhi : (∑ u : Fin n → Bool,
          mixedCountEstimator n d ε (fun i => syntheticRecord (s i) (u i))) ≤
        (2 : ℝ) ^ n := by
      calc
        _ ≤ ∑ _u : Fin n → Bool, (1 : ℝ) :=
          Finset.sum_le_sum (fun u _ => (mixed_count_estimator_regular n d ε).2 _ |>.2)
        _ = (2 : ℝ) ^ n := by simp [hcard]
    change -1 ≤ (∑ u : Fin n → Bool,
        mixedCountEstimator n d ε (fun i => syntheticRecord (s i) (u i))) /
        (2 : ℝ) ^ n ∧
      (∑ u : Fin n → Bool,
        mixedCountEstimator n d ε (fun i => syntheticRecord (s i) (u i))) /
        (2 : ℝ) ^ n ≤ 1
    constructor
    · exact (le_div_iff₀ hcardR).2 (by nlinarith)
    · exact (div_le_iff₀ hcardR).2 (by nlinarith)

-- @node: thetaPoly_risk_le_synthetic_average
/-- Given [the specified inputs and assumptions](hyp:n,d,ε,P), [the stated mathematical conclusion holds](goal). -/
lemma thetaPoly_risk_le_synthetic_average (n d : ℕ) (ε : ℝ)
    (P : ZengLaw d) :
    zengDeterministicRisk (thetaPoly n d ε) P ≤
      ∫ s, (∑ u : Fin n → Bool,
        (mixedCountEstimator n d ε
          (fun i => syntheticRecord (s i) (u i)) - zengATE P) ^ 2) /
        (2 : ℝ) ^ n ∂(zengSampleLaw n P) := by
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure (zengSampleLaw n P) := by
    unfold zengSampleLaw
    infer_instance
  unfold zengDeterministicRisk
  have hint : Integrable
      (fun s : Fin n → ZengRecord d =>
        (∑ u : Fin n → Bool,
          (mixedCountEstimator n d ε
            (fun i => syntheticRecord (s i) (u i)) - zengATE P) ^ 2) /
          (2 : ℝ) ^ n) (zengSampleLaw n P) := Integrable.of_finite
  exact integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun s => sq_nonneg _)) hint
    (Filter.Eventually.of_forall (thetaPoly_pointwise_jensen n d ε (zengATE P)))

-- @node: zengMinimaxRisk_le_thetaPoly_worst
/-- Given [the specified inputs and assumptions](hyp:n,d,ε), [the stated mathematical conclusion holds](goal). -/
lemma zengMinimaxRisk_le_thetaPoly_worst (n d : ℕ) (ε : ℝ) :
    zengMinimaxRisk n d ε ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d ε}) =>
          zengDeterministicRisk (thetaPoly n d ε) P.1) () := by
  have hregular := thetaPoly_regular n d ε
  let T : ZengEstimator n d :=
    ⟨Kernel.deterministic (thetaPoly n d ε) hregular.1,
      inferInstance, by
        intro s
        rw [Kernel.deterministic_apply, Measure.dirac_apply]
        rw [Set.indicator_of_mem (hregular.2 s)]
        rfl⟩
  have hrisk : ∀ (T : ZengEstimator n d)
      (P : {P : ZengLaw d // P ∈ zengDiscreteClass d ε}),
      0 ≤ zengSquaredRisk T P.1 := by
    intro T P
    exact integral_nonneg (fun s => integral_nonneg (fun y => sq_nonneg _))
  have hval : zengMinimaxRisk n d ε ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d ε}) =>
          zengSquaredRisk T P.1) () := by
    exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hrisk T
  have heq :
      (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d ε}) =>
        zengSquaredRisk T P.1) =
      (fun (_ : Unit) P => zengDeterministicRisk (thetaPoly n d ε) P.1) := by
    funext _ P
    simp [zengSquaredRisk, zengDeterministicRisk, T, Kernel.deterministic_apply]
  rw [heq] at hval
  exact hval

-- @node: synthetic_coin_average_integral
/-- Given [the specified inputs and assumptions](hyp:n,d,s,F), [the stated mathematical conclusion holds](goal). -/
lemma synthetic_coin_average_integral (n d : ℕ)
    (s : Fin n → ZengRecord d) (F : (Fin n → ObsRecord d) → ℝ) :
    (∫ o, F o ∂(syntheticProductLaw s)) =
      (∑ u : Fin n → Bool,
        F (fun i => syntheticRecord (s i) (u i))) / (2 : ℝ) ^ n := by
  let coinPi : Measure (Fin n → Bool) :=
    Measure.pi (fun _ : Fin n => SyntheticCompletion.fairCoin)
  letI : IsProbabilityMeasure coinPi := by
    dsimp [coinPi]
    infer_instance
  have hmap : syntheticProductLaw s =
      coinPi.map (fun u i => syntheticRecord (s i) (u i)) := by
    simpa [coinPi, SyntheticCompletion.fairCoin] using
      syntheticProductLaw_eq_coin_map s
  rw [hmap, integral_map (measurable_of_finite _).aemeasurable
    (measurable_of_finite _).aestronglyMeasurable]
  rw [integral_fintype (Integrable.of_finite)]
  have hcoin (u : Fin n → Bool) : coinPi.real {u} = 1 / (2 : ℝ) ^ n := by
    have hsingle (b : Bool) : (SyntheticCompletion.fairCoin {b}).toReal =
        (1 / 2 : ℝ) := by
      cases b <;> simp [SyntheticCompletion.fairCoin]
    change ((Measure.pi (fun _ : Fin n => SyntheticCompletion.fairCoin)) {u}).toReal = _
    rw [Measure.pi_singleton]
    rw [ENNReal.toReal_prod]
    simp_rw [hsingle]
    simp [Finset.prod_const]
  simp_rw [hcoin]
  simp only [smul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv, one_mul]
  ring

-- @node: thetaPoly_risk_le_completion_risk
/-- Given [the specified inputs and assumptions](hyp:n,d,ε,P,Pstar,hsample,htarget), [the stated mathematical conclusion holds](goal). -/
lemma thetaPoly_risk_le_completion_risk {n d : ℕ} {ε : ℝ}
    (P : ZengLaw d) (Pstar : FullLaw d)
    (hsample : (zengSampleLaw n P).bind syntheticProductLaw = sampleLaw n Pstar)
    (htarget : ate Pstar = zengATE P) :
    zengDeterministicRisk (thetaPoly n d ε) P ≤
      deterministicRisk (mixedCountEstimator n d ε) Pstar := by
  let F : (Fin n → ObsRecord d) → ℝ := fun o =>
    (mixedCountEstimator n d ε o - zengATE P) ^ 2
  have hmeas : Measurable (syntheticProductLaw (n := n) (d := d)) :=
    measurable_of_finite _
  have hFbind : Integrable F ((zengSampleLaw n P).bind syntheticProductLaw) := by
    rw [hsample]
    letI : IsProbabilityMeasure Pstar.1 := Pstar.2
    letI : IsProbabilityMeasure (Pstar.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs Pstar.1)
    unfold sampleLaw
    exact Integrable.of_finite
  have hinner (s : Fin n → ZengRecord d) :
      (∫ o, F o ∂syntheticProductLaw s) =
        (∑ u : Fin n → Bool,
          (mixedCountEstimator n d ε
            (fun i => syntheticRecord (s i) (u i)) - zengATE P) ^ 2) /
          (2 : ℝ) ^ n := by
    exact synthetic_coin_average_integral n d s F
  calc
    zengDeterministicRisk (thetaPoly n d ε) P ≤
        ∫ s, (∑ u : Fin n → Bool,
          (mixedCountEstimator n d ε
            (fun i => syntheticRecord (s i) (u i)) - zengATE P) ^ 2) /
          (2 : ℝ) ^ n ∂(zengSampleLaw n P) :=
      thetaPoly_risk_le_synthetic_average n d ε P
    _ = ∫ o, F o ∂((zengSampleLaw n P).bind syntheticProductLaw) := by
      rw [Causalean.Mathlib.MeasureTheory.integral_bind hmeas hFbind]
      simp_rw [hinner]
    _ = deterministicRisk (mixedCountEstimator n d ε) Pstar := by
      rw [hsample]
      simpa [F, deterministicRisk, htarget]

-- @node: thetaPoly_uniform_upper
/-- [the stated mathematical conclusion holds](goal). -/
lemma thetaPoly_uniform_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ) (ε : ℝ), 1 ≤ n → 1 ≤ d → 0 < ε → ε < 1 / 2 →
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d ε}) =>
            zengDeterministicRisk (thetaPoly n d ε) P.1) () ≤
          C * frontierRate n d ε := by
  obtain ⟨C, hC, hupper⟩ := unrestricted_mixed_count_upper
  refine ⟨C, hC, ?_⟩
  intro n d ε hn hd hε hεhalf
  unfold Causalean.Stat.worstCaseRiskReal
  by_cases hne : Nonempty {P : ZengLaw d // P ∈ zengDiscreteClass d ε}
  · letI := hne
    apply ciSup_le
    intro P
    obtain ⟨Pstar, hclass, hiid, hsample, htarget⟩ :=
      synthetic_randomization_kernel hn hε hεhalf P.1 P.2
    have hrisk := thetaPoly_risk_le_completion_risk (ε := ε) P.1 Pstar hsample htarget
    have hbound := hupper n d ε Pstar hclass hiid
    nlinarith [hrisk, hbound.1, hbound.2.1]
  · haveI : IsEmpty {P : ZengLaw d // P ∈ zengDiscreteClass d ε} :=
      not_nonempty_iff.mp hne
    simp
    have hrate : 0 ≤ frontierRate n d ε := by
      unfold frontierRate
      have hN : 0 < effectiveSize n ε := by
        unfold effectiveSize
        positivity
      positivity
    exact mul_nonneg hC.le hrate

-- @node: zeng_frontierRate_le_fixedQRate_mul
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma zeng_frontierRate_le_fixedQRate_mul (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1) :
    frontierRate n d q ≤ ((1 - Real.log q) / q) ^ 2 * fixedQRate n d := by
  let N := effectiveSize n q
  let L := logScale n q
  let L₁ := Real.log (Real.exp 1 + n)
  let K := (1 - Real.log q) / q
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : 0 < N := mul_pos hn0 hq
  have hL : 1 ≤ L := by
    dsimp [L, logScale]
    rw [Real.le_log_iff_exp_le (by positivity)]
    dsimp [N, effectiveSize] at *
    linarith
  have hL₁ : 0 < L₁ := by
    dsimp [L₁]
    apply Real.log_pos
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogq : Real.log q ≤ 0 := Real.log_nonpos hq.le hq1
  have hlogbound : L₁ ≤ (1 - Real.log q) * L := by
    have harg : Real.exp 1 + (n : ℝ) ≤ (Real.exp 1 + N) / q := by
      apply (le_div_iff₀ hq).2
      dsimp [N, effectiveSize]
      nlinarith [Real.exp_pos (1 : ℝ)]
    have hbase : L₁ ≤ L - Real.log q := by
      calc
        L₁ ≤ Real.log ((Real.exp 1 + N) / q) :=
          Real.log_le_log (by positivity) harg
        _ = L - Real.log q := by
          rw [Real.log_div (by positivity) (ne_of_gt hq)]
          rfl
    have hprod := mul_nonneg (neg_nonneg.mpr hlogq) (sub_nonneg.mpr hL)
    nlinarith
  have hK : 1 ≤ K := by
    dsimp [K]
    apply (le_div_iff₀ hq).2
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hD : 0 < N * L := mul_pos hN (by linarith)
  have hD₁ : 0 < (n : ℝ) * L₁ := mul_pos hn0 hL₁
  have hDen : (n : ℝ) * L₁ ≤ K * (N * L) := by
    calc
      (n : ℝ) * L₁ ≤ (n : ℝ) * ((1 - Real.log q) * L) :=
        mul_le_mul_of_nonneg_left hlogbound hn0.le
      _ = K * (N * L) := by
        dsimp [K, N, effectiveSize]
        field_simp
  have hfirst : N⁻¹ ≤ K ^ 2 * (n : ℝ)⁻¹ := by
    have hqK : q * K = 1 - Real.log q := by
      dsimp [K]
      field_simp
    have hK2 : 1 ≤ q * K ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hlogq)]
    have hN_eq : N = (n : ℝ) * q := rfl
    have h : 1 / N ≤ K ^ 2 / (n : ℝ) := by
      apply (div_le_div_iff₀ hN hn0).2
      rw [hN_eq]
      nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hK2)]
    simpa [one_div, div_eq_mul_inv] using h
  have hsecond : ((d : ℝ) / (N * L)) ^ 2 ≤
      K ^ 2 * ((d : ℝ) / ((n : ℝ) * L₁)) ^ 2 := by
    have hdiv : (d : ℝ) / (N * L) ≤ K * ((d : ℝ) / ((n : ℝ) * L₁)) := by
      have h : (d : ℝ) / (N * L) ≤ (K * d) / ((n : ℝ) * L₁) := by
        apply (div_le_div_iff₀ hD hD₁).2
        have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hDen)]
      convert h using 1 <;> ring
    have hleft : 0 ≤ (d : ℝ) / (N * L) := div_nonneg (Nat.cast_nonneg _) hD.le
    nlinarith [sq_nonneg (K * ((d : ℝ) / ((n : ℝ) * L₁)) -
      ((d : ℝ) / (N * L)))]
  have hr0 : 0 ≤ (n : ℝ)⁻¹ + ((d : ℝ) / ((n : ℝ) * L₁)) ^ 2 := by positivity
  have hsum : N⁻¹ + ((d : ℝ) / (N * L)) ^ 2 ≤
      K ^ 2 * ((n : ℝ)⁻¹ + ((d : ℝ) / ((n : ℝ) * L₁)) ^ 2) := by
    nlinarith [hfirst, hsecond]
  dsimp [frontierRate, fixedQRate, N, L, L₁, K] at *
  calc
    min 1 ((effectiveSize n q)⁻¹ +
        ((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2) ≤
      min 1 (K ^ 2 * ((n : ℝ)⁻¹ + ((d : ℝ) /
        ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2)) :=
          min_le_min_left 1 hsum
    _ ≤ K ^ 2 * min 1 ((n : ℝ)⁻¹ + ((d : ℝ) /
        ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2) := by
          rcases le_total ((n : ℝ)⁻¹ + ((d : ℝ) /
            ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2) 1 with h | h
          · rw [min_eq_right h]
            exact (min_le_right _ _)
          · rw [min_eq_left h]
            exact (min_le_left _ _).trans (by nlinarith [sq_nonneg K])

-- @node: zeng_minimax_upper_fixedQ
/-- Given [the specified inputs and assumptions](hyp:ε,hε,hεhalf), [the stated mathematical conclusion holds](goal). -/
lemma zeng_minimax_upper_fixedQ (ε : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
      zengMinimaxRisk n d ε ≤ Cε * fixedQRate n d := by
  obtain ⟨C, hC, hupper⟩ := thetaPoly_uniform_upper
  let K := ((1 - Real.log ε) / ε) ^ 2
  have hlog : Real.log ε ≤ 0 :=
    Real.log_nonpos hε.le (by linarith)
  have hK : 0 < K := by
    dsimp [K]
    exact pow_pos (div_pos (by linarith) hε) _
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro n d hn hd
  calc
    zengMinimaxRisk n d ε ≤
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d ε}) =>
            zengDeterministicRisk (thetaPoly n d ε) P.1) () :=
      zengMinimaxRisk_le_thetaPoly_worst n d ε
    _ ≤ C * frontierRate n d ε :=
      hupper n d ε hn hd hε hεhalf
    _ ≤ C * (K * fixedQRate n d) :=
      mul_le_mul_of_nonneg_left
        (zeng_frontierRate_le_fixedQRate_mul n d ε hn hε (by linarith)) hC.le
    _ = (C * K) * fixedQRate n d := by ring

-- @node: zeng_minimax_lower_fixedQ
/-- Given [the specified inputs and assumptions](hyp:hZeng_of_gate,ε,hε,hεhalf), [the stated mathematical conclusion holds](goal). -/
lemma zeng_minimax_lower_fixedQ (hZeng_of_gate : ZengTheoremTwoLower)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
      c * fixedQRate n d ≤ zengMinimaxRisk n d ε := by
  obtain ⟨c₀, cdim, n₀, hc₀, hcdim, hgate⟩ :=
    hZeng_of_gate ε hε hεhalf
  obtain ⟨cp, hcp, hparam⟩ := zeng_parametric_minimax_lower
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (2 / cdim)
  let N := max (max n₀ 3) N₁
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  let csat := c₀ * (cdim / 2) ^ 2
  have hcsat : 0 < csat := by dsimp [csat]; positivity
  let c := min (cp / N) (min c₀ csat)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (div_pos hcp (by exact_mod_cast hNpos)) (lt_min hc₀ hcsat)
  refine ⟨c, hc, ?_⟩
  intro n d hn hd
  have hrate_nonneg : 0 ≤ fixedQRate n d := by
    unfold fixedQRate
    exact le_min (by norm_num) (by positivity)
  have hrate_one : fixedQRate n d ≤ 1 := by
    unfold fixedQRate
    exact min_le_left _ _
  by_cases hnlarge : N ≤ n
  · have hn₀ : n₀ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hnlarge)
    have hn3 : 3 ≤ n := le_trans (le_max_right n₀ 3) (le_trans (le_max_left _ _) hnlarge)
    have hnposR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 1 < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hnposR]
      have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      exact Real.exp_one_lt_d9.trans (by nlinarith)
    have hlogpos : 0 < Real.log n := lt_trans zero_lt_one hlog
    have hden : 0 < (n : ℝ) * Real.log n := mul_pos hnposR hlogpos
    have hN₁n : N₁ ≤ n := le_trans (le_max_right (max n₀ 3) N₁) hnlarge
    have htwo : 2 ≤ cdim * n * Real.log n := by
      have hbase : 2 ≤ cdim * n := by
        have hcN : 2 / cdim ≤ (n : ℝ) := hN₁.trans (by exact_mod_cast hN₁n)
        exact (div_le_iff₀ hcdim).mp hcN |>.trans_eq (by ring)
      nlinarith [mul_nonneg (show 0 ≤ cdim * n by positivity) (sub_nonneg.mpr hlog.le)]
    by_cases hdim : (d : ℝ) ≤ cdim * n * Real.log n
    · have hpublished := (hgate n d hn₀ hd hdim).trans
          (zeng_zero_control_risk_le_minimax n d ε)
      have hlog_le : Real.log n ≤ Real.log (Real.exp 1 + n) := by
        exact Real.log_le_log hnposR (by nlinarith [Real.exp_pos 1])
      have hden' : 0 < (n : ℝ) * Real.log (Real.exp 1 + n) := by
        apply mul_pos hnposR
        apply Real.log_pos
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [Real.exp_pos 1]
      have hfrac : (d : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n)) ≤
          (d : ℝ) / ((n : ℝ) * Real.log n) := by
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden
          (mul_le_mul_of_nonneg_left hlog_le hnposR.le)
      have hraw : fixedQRate n d ≤ (n : ℝ)⁻¹ +
          ((d : ℝ) / ((n : ℝ) * Real.log n)) ^ 2 := by
        unfold fixedQRate
        calc
          min 1 ((n : ℝ)⁻¹ + ((d : ℝ) /
              ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2) ≤
              (n : ℝ)⁻¹ + ((d : ℝ) /
                ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2 := min_le_right _ _
          _ ≤ _ := by
            have hf₀ : 0 ≤ (d : ℝ) /
                ((n : ℝ) * Real.log (Real.exp 1 + n)) := by positivity
            have hf₁ : 0 ≤ (d : ℝ) /
                ((n : ℝ) * Real.log n) := by positivity
            nlinarith [mul_nonneg (sub_nonneg.mpr hfrac) (add_nonneg hf₀ hf₁)]
      have hc_le : c ≤ c₀ := (min_le_right _ _).trans (min_le_left _ _)
      calc
        c * fixedQRate n d ≤ c * ((n : ℝ)⁻¹ +
            ((d : ℝ) / ((n : ℝ) * Real.log n)) ^ 2) :=
          mul_le_mul_of_nonneg_left hraw hc.le
        _ ≤ c₀ * ((n : ℝ)⁻¹ +
            ((d : ℝ) / ((n : ℝ) * Real.log n)) ^ 2) :=
          mul_le_mul_of_nonneg_right hc_le (by positivity)
        _ ≤ zengMinimaxRisk n d ε := hpublished
    · let r := ⌊cdim * n * Real.log n⌋₊
      have hrpos : 1 ≤ r := by
        dsimp [r]
        exact Nat.floor_pos.mpr (le_trans (by norm_num) htwo)
      have hrleA : (r : ℝ) ≤ cdim * n * Real.log n := by
        dsimp [r]
        exact Nat.floor_le (by positivity)
      have hrle : r ≤ d := by
        exact_mod_cast hrleA.trans (le_of_not_ge hdim)
      have hrhalf : cdim / 2 * ((n : ℝ) * Real.log n) ≤ r := by
        have hfloor := Nat.sub_one_lt_floor (cdim * n * Real.log n)
        dsimp [r]
        have hhalf : cdim / 2 * ((n : ℝ) * Real.log n) ≤
            cdim * n * Real.log n - 1 := by nlinarith
        exact hhalf.trans hfloor.le
      have hpublished := (hgate n r hn₀ hrpos hrleA).trans
        (zeng_zero_control_risk_le_minimax n r ε)
      have hmono := zengMinimaxRisk_mono_dimension (n := n) hrpos hrle ε
      have hratio : cdim / 2 ≤ (r : ℝ) /
          ((n : ℝ) * Real.log n) := (le_div_iff₀ hden).2 (by simpa using hrhalf)
      have hsatlower : csat ≤ c₀ * ((n : ℝ)⁻¹ +
          ((r : ℝ) / ((n : ℝ) * Real.log n)) ^ 2) := by
        dsimp [csat]
        have hc0nonneg := hc₀.le
        have hsq : (cdim / 2) ^ 2 ≤
            ((r : ℝ) / ((n : ℝ) * Real.log n)) ^ 2 := by nlinarith
        nlinarith [mul_nonneg hc0nonneg (inv_nonneg.mpr hnposR.le)]
      have hc_le_sat : c ≤ csat := (min_le_right _ _).trans (min_le_right _ _)
      calc
        c * fixedQRate n d ≤ c := by nlinarith
        _ ≤ csat := hc_le_sat
        _ ≤ c₀ * ((n : ℝ)⁻¹ +
            ((r : ℝ) / ((n : ℝ) * Real.log n)) ^ 2) := hsatlower
        _ ≤ zengZeroControlRisk n r ε := hgate n r hn₀ hrpos hrleA
        _ ≤ zengMinimaxRisk n r ε := zeng_zero_control_risk_le_minimax n r ε
        _ ≤ zengMinimaxRisk n d ε := hmono
  · have hnN : n ≤ N := by omega
    have hcpN : cp / N ≤ cp / n := by
      exact div_le_div_of_nonneg_left hcp.le (by exact_mod_cast hn) (by exact_mod_cast hnN)
    have hc_le : c ≤ cp / N := min_le_left _ _
    calc
      c * fixedQRate n d ≤ c := by nlinarith
      _ ≤ cp / N := hc_le
      _ ≤ cp / n := hcpN
      _ ≤ zengMinimaxRisk n d ε := hparam n d ε hn hd hε hεhalf



-- @node: thm:zeng-fixed-positivity-polynomial-frontier
/-- Given [the specified inputs and assumptions](hyp:hZeng_of_gate), [the stated mathematical conclusion holds](goal). -/
theorem zeng_fixed_positivity_polynomial_frontier
    (hZeng_of_gate : ZengTheoremTwoLower) :
    ∃ C_univ : ℝ, 0 < C_univ ∧
      (∀ (n d : ℕ) (ε : ℝ), 1 ≤ n → 1 ≤ d → 0 < ε → ε < 1 / 2 →
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d ε}) =>
            zengDeterministicRisk (thetaPoly n d ε) P.1) () ≤
          C_univ * frontierRate n d ε) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ cε Cε : ℝ, 0 < cε ∧ cε ≤ Cε ∧
          ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
            cε * fixedQRate n d ≤ zengMinimaxRisk n d ε ∧
            zengMinimaxRisk n d ε ≤ Cε * fixedQRate n d) := by
  obtain ⟨C, hC, hupper⟩ := thetaPoly_uniform_upper
  refine ⟨C, hC, hupper, ?_⟩
  intro ε hε hεhalf
  obtain ⟨Cu, hCu, hupperFixed⟩ :=
    zeng_minimax_upper_fixedQ ε hε hεhalf
  obtain ⟨c, hc, hlower⟩ :=
    zeng_minimax_lower_fixedQ hZeng_of_gate ε hε hεhalf
  let Cε := max Cu c
  refine ⟨c, Cε, hc, le_max_right _ _, ?_⟩
  intro n d hn hd
  have hrate : 0 ≤ fixedQRate n d := by
    unfold fixedQRate
    exact le_min (by norm_num) (by positivity)
  refine ⟨hlower n d hn hd, ?_⟩
  exact (hupperFixed n d hn hd).trans
    (mul_le_mul_of_nonneg_right (le_max_left Cu c) hrate)

end CausalSmith.Stat.MarRareqLogfrontier
