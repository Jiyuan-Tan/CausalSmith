module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.SyntheticKernel
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Main
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedMixedCountUpper
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TZengFixedPositivityPolynomialFrontier
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedCompleteArrivalFrontier

/-! TUnrestrictedFixedQMinimaxFrontier for the finite rare-arrival experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: fixedQRate_le_frontierRate
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma fixedQRate_le_frontierRate (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1) :
    fixedQRate n d ≤ frontierRate n d q := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : 0 < effectiveSize n q := mul_pos hn0 hq
  have hNle : effectiveSize n q ≤ n := by
    unfold effectiveSize
    nlinarith
  have hlogpos : 0 < logScale n q := by
    unfold logScale
    apply Real.log_pos
    have he : 1 < Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    linarith
  have hlogle : logScale n q ≤ Real.log (Real.exp 1 + n) := by
    unfold logScale
    exact Real.log_le_log (by positivity) (by linarith)
  have hden : 0 < effectiveSize n q * logScale n q :=
    mul_pos hN hlogpos
  have hden' : effectiveSize n q * logScale n q ≤
      (n : ℝ) * Real.log (Real.exp 1 + n) := by
    apply mul_le_mul hNle hlogle hlogpos.le (by positivity)
  have hfirst : (n : ℝ)⁻¹ ≤ (effectiveSize n q)⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le hN hNle
  have hsecond :
      ((d : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n))) ^ 2 ≤
        ((d : ℝ) / (effectiveSize n q * logScale n q)) ^ 2 := by
    have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg d) hden hden'
    have hdenBig : 0 < (n : ℝ) * Real.log (Real.exp 1 + n) :=
      lt_of_lt_of_le hden hden'
    have hdiv0 : 0 ≤ (d : ℝ) / ((n : ℝ) * Real.log (Real.exp 1 + n)) :=
      div_nonneg (Nat.cast_nonneg d) hdenBig.le
    nlinarith
  unfold fixedQRate frontierRate
  exact min_le_min_left 1 (add_le_add hfirst hsecond)

-- @node: frontierRate_le_fixedQRate_mul
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hq1), [the stated mathematical conclusion holds](goal). -/
lemma frontierRate_le_fixedQRate_mul (n d : ℕ) (q : ℝ)
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

-- @node: unrestricted_fixed_q_frontier_upper
/-- [the stated mathematical conclusion holds](goal). -/
lemma unrestricted_fixed_q_frontier_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (q : ℝ),
      1 ≤ n → 1 ≤ d → 0 < q → q < 1 / 2 →
      unrestrictedMinimaxRisk n d q ≤ C * frontierRate n d q := by
  obtain ⟨C, hC, hupper⟩ := unrestricted_mixed_count_upper
  refine ⟨C, hC, ?_⟩
  intro n d q hn hd hq hqhalf
  let f := mixedCountEstimator n d q
  have hf := mixed_count_estimator_regular n d q
  let T : Estimator n d :=
    Estimator.ofMap f hf
  have hrisk : ∀ (T : Estimator n d)
      (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}),
      0 ≤ squaredRisk T P.1 := by
    intro T P
    exact integral_nonneg (fun s => integral_nonneg (fun y => sq_nonneg _))
  have hval : unrestrictedMinimaxRisk n d q ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) =>
          deterministicRisk f P.1) () := by
    have h := Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hrisk T
    calc
      unrestrictedMinimaxRisk n d q ≤
          Causalean.Stat.worstCaseRiskReal
            (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) =>
              squaredRisk T P.1) () := by
                simpa only [unrestrictedMinimaxRisk,
                  Causalean.Stat.worstCaseRiskReal] using h
      _ = _ := by
        congr 1
        funext _ P
        simp [squaredRisk, deterministicRisk, T, Estimator.ofMap, Kernel.deterministic_apply]
  refine le_trans hval ?_
  unfold Causalean.Stat.worstCaseRiskReal
  by_cases hne : Nonempty
      {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}
  · letI := hne
    apply ciSup_le
    intro P
    obtain ⟨hriskP, hrateP, _⟩ := hupper n d q P.1 P.2 (sampleLaw_iid n P.1)
    exact hriskP.trans hrateP
  · haveI : IsEmpty {P : FullLaw d // UnrestrictedArrivalModelClass n d q P} :=
      not_nonempty_iff.mp hne
    simp
    have hrate : 0 ≤ frontierRate n d q := by
      have hN : 0 < effectiveSize n q := by
        unfold effectiveSize
        exact mul_pos (by exact_mod_cast hn) hq
      have hexp : (1 : ℝ) < Real.exp 1 := by
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      have hlog : 0 < logScale n q := by
        unfold logScale
        exact Real.log_pos (by linarith)
      unfold frontierRate
      exact le_min (by norm_num) (by positivity)
    exact mul_nonneg hC.le hrate

-- @node: unrestricted_fixed_q_polynomial_upper
/-- Given [the specified inputs and assumptions](hyp:q,hq,hqhalf), [the stated mathematical conclusion holds](goal). -/
lemma unrestricted_fixed_q_polynomial_upper (q : ℝ)
    (hq : 0 < q) (hqhalf : q < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
      unrestrictedMinimaxRisk n d q ≤ C * fixedQRate n d := by
  obtain ⟨C, hC, hupper⟩ := unrestricted_fixed_q_frontier_upper
  let K := ((1 - Real.log q) / q) ^ 2
  have hK : 0 < K := by
    dsimp [K]
    have hlog : Real.log q ≤ 0 :=
      Real.log_nonpos hq.le (by linarith)
    exact pow_pos (div_pos (by linarith) hq) _
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro n d hn hd
  calc
    unrestrictedMinimaxRisk n d q ≤ C * frontierRate n d q :=
      hupper n d q hn hd hq hqhalf
    _ ≤ C * (K * fixedQRate n d) :=
      mul_le_mul_of_nonneg_left
        (frontierRate_le_fixedQRate_mul n d q hn hq (by linarith)) hC.le
    _ = (C * K) * fixedQRate n d := by ring

-- @node: zengMinimaxRisk_le_unrestrictedMinimaxRisk
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hqhalf), [the stated mathematical conclusion holds](goal). -/
lemma zengMinimaxRisk_le_unrestrictedMinimaxRisk (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hq : 0 < q) (hqhalf : q < 1 / 2) :
    zengMinimaxRisk n d q ≤ unrestrictedMinimaxRisk n d q := by
  let φ : {P : ZengLaw d // P ∈ zengDiscreteClass d q} →
      {P : FullLaw d // UnrestrictedArrivalModelClass n d q P} := fun P =>
    ⟨(synthetic_randomization_kernel hn hq hqhalf P.1 P.2).choose,
      (synthetic_randomization_kernel hn hq hqhalf P.1 P.2).choose_spec.1⟩
  let T₀ : Estimator n d :=
    Estimator.ofMap (fun _ => 0) ⟨measurable_const, by intro s; norm_num⟩
  letI : Nonempty (Estimator n d) := ⟨T₀⟩
  have hr : ∀ (T : ZengEstimator n d)
      (P : {P : ZengLaw d // P ∈ zengDiscreteClass d q}),
      0 ≤ zengSquaredRisk T P.1 := by
    intro T P
    exact (zeng_squaredRisk_bounds q T P.1 P.2).1
  unfold zengMinimaxRisk unrestrictedMinimaxRisk
  apply Causalean.Stat.minimaxValue_le_minimaxValue
    (Causalean.Stat.bddBelow_range_worstCaseRisk hr)
  intro T
  refine ⟨syntheticPullbackEstimator T, ?_⟩
  change Causalean.Stat.worstCaseRiskReal
      (fun (_ : Unit) (P : {P : ZengLaw d // P ∈ zengDiscreteClass d q}) =>
        zengSquaredRisk (syntheticPullbackEstimator T) P.1) () ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) =>
          squaredRisk T P.1) ()
  apply Causalean.Stat.worstCaseRisk_mono_class_of_nonneg φ
  · refine ⟨4, ?_⟩
    rintro r ⟨P, rfl⟩
    exact (unrestricted_squaredRisk_bounds T P.1).2
  · intro P
    exact (unrestricted_squaredRisk_bounds T P.1).1
  · intro P
    have hspec :=
      (synthetic_randomization_kernel hn hq hqhalf P.1 P.2).choose_spec
    exact le_of_eq (syntheticPullbackEstimator_risk_eq T P.1 (φ P).1
      hspec.2.2.1 hspec.2.2.2)

-- @node: thm:unrestricted-fixed-q-minimax-frontier
/-- Given [the cited lower-bound gate](hyp:hZeng_of_gate), [the unrestricted fixed-positivity minimax risk matches the frontier](goal). -/
theorem unrestricted_fixed_q_minimax_frontier
    (hZeng_of_gate : ZengTheoremTwoLower) :
    ∀ q : ℝ, 0 < q → q < 1 / 2 →
      -- @realizes \(\underline c(q)\)(fixed-q lower constant)
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ -- @realizes \(\overline C(q)\)(fixed-q upper constant)
        ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
          c * fixedQRate n d ≤ unrestrictedMinimaxRisk n d q ∧
          unrestrictedMinimaxRisk n d q ≤ C * fixedQRate n d ∧
          c * frontierRate n d q ≤ unrestrictedMinimaxRisk n d q ∧
          unrestrictedMinimaxRisk n d q ≤ C * frontierRate n d q := by
  intro q hq hqhalf
  obtain ⟨C₁, hC₁, hupperFront⟩ := unrestricted_fixed_q_frontier_upper
  obtain ⟨C₂, hC₂, hupperPoly⟩ :=
    unrestricted_fixed_q_polynomial_upper q hq hqhalf
  have hLower : ∃ c : ℝ, 0 < c ∧
      ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d →
        c * frontierRate n d q ≤ unrestrictedMinimaxRisk n d q := by
    obtain ⟨_, _, _, hZfixed⟩ :=
      zeng_fixed_positivity_polynomial_frontier hZeng_of_gate
    obtain ⟨cε, _, hcε, _, hzlower⟩ := hZfixed q hq hqhalf
    let K := ((1 - Real.log q) / q) ^ 2
    have hK : 0 < K := by
      dsimp [K]
      have hlog : Real.log q ≤ 0 :=
        Real.log_nonpos hq.le (by linarith)
      exact pow_pos (div_pos (by linarith) hq) _
    refine ⟨cε / K, div_pos hcε hK, ?_⟩
    intro n d hn hd
    calc
      (cε / K) * frontierRate n d q ≤
          (cε / K) * (K * fixedQRate n d) := by
            exact mul_le_mul_of_nonneg_left
              (frontierRate_le_fixedQRate_mul n d q hn hq (by linarith))
              (div_nonneg hcε.le hK.le)
      _ = cε * fixedQRate n d := by field_simp
      _ ≤ zengMinimaxRisk n d q := (hzlower n d hn hd).1
      _ ≤ unrestrictedMinimaxRisk n d q :=
        zengMinimaxRisk_le_unrestrictedMinimaxRisk n d q hn hq hqhalf
  obtain ⟨c, hc, hlower⟩ := hLower
  let C := max C₁ C₂ + c
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_left C₁ C₂]
  refine ⟨c, C, hc, by dsimp [C]; linarith [le_max_left C₁ C₂], ?_⟩
  intro n d hn hd
  have hfixed : 0 ≤ fixedQRate n d := by
    unfold fixedQRate
    exact le_min (by norm_num) (by positivity)
  have hfront : 0 ≤ frontierRate n d q := by
    unfold frontierRate
    have hN : 0 ≤ effectiveSize n q := by
      unfold effectiveSize
      positivity
    exact le_min (by norm_num)
      (add_nonneg (inv_nonneg.mpr hN) (sq_nonneg _))
  have hC₁ : C₁ ≤ C := by dsimp [C]; linarith [le_max_left C₁ C₂]
  have hC₂ : C₂ ≤ C := by dsimp [C]; linarith [le_max_right C₁ C₂]
  refine ⟨?_, ?_, hlower n d hn hd, ?_⟩
  · exact (mul_le_mul_of_nonneg_left
      (fixedQRate_le_frontierRate n d q hn hq (by linarith)) hc.le).trans
      (hlower n d hn hd)
  · exact (hupperPoly n d hn hd).trans
      (mul_le_mul_of_nonneg_right hC₂ hfixed)
  · exact (hupperFront n d q hn hd hq hqhalf).trans
      (mul_le_mul_of_nonneg_right hC₁ hfront)

end CausalSmith.Stat.MarRareqLogfrontier
