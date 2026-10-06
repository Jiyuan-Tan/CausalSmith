module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Inversion
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.TMatchedRiskFrontier
/-! Honest private expected-length frontier, explicit inversion identity, and uniform equivalence
to the scalar absolute-risk frontier. -/
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- Clipping a numerator commutes with division by a positive denominator.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:b,z,hb). -/
-- @node: clip_div_positive
lemma clip_div_positive (b z : ℝ) (hb : 0 < b) :
    clip (-b) b z / b = clip (-1) 1 (z / b) := by
  unfold clip
  rw [← max_div_div_right hb.le, ← min_div_div_right hb.le]
  simp [hb.ne']

/-- At legal public parameters the acceptance hull is the released interval.  [the theorem's stated inputs and assumptions](hyp:hn,hk,hh), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,epsilon). -/
-- @node: inversionMap_eq_intervalMap
lemma inversionMap_eq_intervalMap (n k : ℕ) (epsilon h : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hh : 0 < h) :
    inversionMap n epsilon h k = intervalMap n epsilon h k := by
  funext v
  have hb : 0 < max (d0 n h k) (v 1) :=
    lt_of_lt_of_le (info_d0_pos n k h hn hk hh).2 (le_max_left _ _)
  rw [inversionMap_eq_endpoints, if_pos hb, clip_div_positive _ _ hb]
  rfl

/-- Public tuning uses the same interval on both release branches.  [the theorem's stated inputs and assumptions](hyp:hn,he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon). -/
-- @node: optimalIntervalHandle_eq_publicTunedInterval
lemma optimalIntervalHandle_eq_publicTunedInterval (n : ℕ) (epsilon : ℝ)
    (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    optimalIntervalHandle n epsilon = publicTunedInterval n epsilon := by
  classical
  by_cases hr : 1 / 8 ≤ rate n epsilon
  · simp only [optimalIntervalHandle, publicTunedInterval, if_pos hr]
  · have hp := public_tuning_parameters n epsilon hn he (lt_of_not_ge hr)
    simp only [optimalIntervalHandle, publicTunedInterval, hr, ↓reduceIte, Ihk]
    congr 1
    exact inversionMap_eq_intervalMap n (tunedK n epsilon) epsilon
      (tunedH n epsilon) (by omega) (by omega) hp.1

/-- An interval containing two ordered points contains the open span between them.  [the theorem's stated inputs and assumptions](hyp:ha,hb), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:c,a,b). -/
-- @node: interval_span_subset
lemma interval_span_subset (c : IntervalCode) (a b : ℝ)
    (ha : a ∈ c.toSet) (hb : b ∈ c.toSet) : Set.Ioo a b ⊆ c.toSet := by
  cases c with
  | inl u => simp [IntervalCode.toSet] at ha
  | inr p =>
    rcases p with ⟨l, u, lc, uc⟩
    intro x hx
    simp only [IntervalCode.toSet, Set.mem_ofPred_eq] at ha hb ⊢
    have hax := EReal.coe_lt_coe hx.1
    have hxb := EReal.coe_lt_coe hx.2
    constructor
    · cases lc <;> simp only [Bool.false_eq_true, ↓reduceIte] at ha ⊢
      · exact ha.1.trans hax
      · exact (ha.1.trans_lt hax).le
    · cases uc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
      · exact hxb.trans hb.2
      · exact (hxb.trans_le hb.2).le

/-- Simultaneous containment forces Lebesgue length even for unbounded codes.  [the theorem's stated inputs and assumptions](hyp:h0,h1), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:c,Delta). -/
-- @node: interval_leb_ge_span
lemma interval_leb_ge_span (c : IntervalCode) (Delta : ℝ)
    (h0 : 0 ∈ c.toSet) (h1 : Delta ∈ c.toSet) :
    ENNReal.ofReal Delta ≤ c.leb := by
  have h := measure_mono (μ := (volume : Measure ℝ))
    (interval_span_subset c 0 Delta h0 h1)
  simpa [IntervalCode.leb, Real.volume_Ioo] using h

/-- A finite class prior inherits honesty at its common target.  [the theorem's stated inputs and assumptions](hyp:hs,I,target,hF,hhonest), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s,F). -/
-- @node: finite_prior_coverage_lower
lemma finite_prior_coverage_lower (n s : ℕ) (F : Fin s → CausalLaw)
    (hs : 0 < s) (I : Kernel (Dataset n) IntervalCode) [IsMarkovKernel I]
    (target : ℝ) (hF : ∀ i, CompleteModel (F i) ∧ theta (F i) = target)
    (hhonest : ∀ P, CompleteModel P → 9 / 10 ≤ coverage n I P) :
    9 / 10 ≤ (I ∘ₘ finiteProductMixture n s F).real {c | target ∈ c.toSet} := by
  let : IsProbabilityMeasure (finiteProductMixture n s F) :=
    finiteProductMixture_probability n s F hs
  have hmass : ENNReal.ofReal (9 / 10 : ℝ) ≤
      (I ∘ₘ finiteProductMixture n s F) {c | target ∈ c.toSet} := by
    rw [finiteProductMixture, Measure.comp_smul, prior_comp_finsetSum,
      Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    have hrow : ∀ i : Fin s, ENNReal.ofReal (9 / 10 : ℝ) ≤
        (I ∘ₘ dataLaw n (F i)) {c | target ∈ c.toSet} := by
      intro i
      let : IsProbabilityMeasure (Pobs (F i)) :=
        Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
      let : IsProbabilityMeasure (dataLaw n (F i)) := by unfold dataLaw; infer_instance
      have hc := hhonest (F i) (hF i).1
      unfold coverage at hc
      rw [(hF i).2] at hc
      rw [← ENNReal.ofReal_toReal (measure_ne_top (I ∘ₘ dataLaw n (F i)) _)]
      exact ENNReal.ofReal_le_ofReal hc
    calc
      _ = (s : ℝ≥0∞)⁻¹ * ∑ _i : Fin s, ENNReal.ofReal (9 / 10 : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, ENNReal.inv_mul_cancel
          (by exact_mod_cast (Nat.ne_of_gt hs)) (by simp), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hrow i) (zero_le)
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hmass

/-- Prior expected length is no greater than maximal class expected length.  [the theorem's stated inputs and assumptions](hyp:hs,I,hF), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s,F). -/
-- @node: finite_prior_length_le_worstLength
lemma finite_prior_length_le_worstLength (n s : ℕ) (F : Fin s → CausalLaw)
    (hs : 0 < s) (I : Kernel (Dataset n) IntervalCode)
    (hF : ∀ i, CompleteModel (F i)) :
    (∫⁻ c, c.leb ∂(I ∘ₘ finiteProductMixture n s F)) ≤ worstLength n I := by
  rw [finiteProductMixture, Measure.comp_smul, prior_comp_finsetSum,
    lintegral_smul_measure, lintegral_finsetSum_measure]
  have hbound : ∀ i : Fin s, (∫⁻ c, c.leb ∂(I ∘ₘ dataLaw n (F i))) ≤
      worstLength n I := fun i => le_iSup_of_le (F i) (le_iSup_of_le (hF i) le_rfl)
  calc
    _ ≤ (s : ℝ≥0∞)⁻¹ * ∑ _i : Fin s, worstLength n I :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbound i) (zero_le)
    _ = worstLength n I := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel
        (by exact_mod_cast (Nat.ne_of_gt hs)) (by simp), one_mul]

/-- Two honest finite priors force simultaneous containment under the null output law.  [the theorem's stated inputs and assumptions](hyp:F0,F1,hs0,hs1,I,Delta,hd,hF0,hF1,hhonest,htv), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s0,s1). -/
-- @node: finite_priors_interval_lower
lemma finite_priors_interval_lower (n s0 s1 : ℕ)
    (F0 : Fin s0 → CausalLaw) (F1 : Fin s1 → CausalLaw)
    (hs0 : 0 < s0) (hs1 : 0 < s1) (I : Kernel (Dataset n) IntervalCode)
    [IsMarkovKernel I] (Delta : ℝ) (hd : 0 ≤ Delta)
    (hF0 : ∀ i, CompleteModel (F0 i) ∧ theta (F0 i) = 0)
    (hF1 : ∀ i, CompleteModel (F1 i) ∧ theta (F1 i) = Delta)
    (hhonest : ∀ P, CompleteModel P → 9 / 10 ≤ coverage n I P)
    (htv : TV (I ∘ₘ finiteProductMixture n s0 F0)
      (I ∘ₘ finiteProductMixture n s1 F1) ≤ 1 / 4) :
    ENNReal.ofReal ((11 / 20) * Delta) ≤ worstLength n I := by
  let L0 := I ∘ₘ finiteProductMixture n s0 F0
  let L1 := I ∘ₘ finiteProductMixture n s1 F1
  let : IsProbabilityMeasure (finiteProductMixture n s0 F0) :=
    finiteProductMixture_probability n s0 F0 hs0
  let : IsProbabilityMeasure (finiteProductMixture n s1 F1) :=
    finiteProductMixture_probability n s1 F1 hs1
  let E0 : Set IntervalCode := {c | 0 ∈ c.toSet}
  let E1 : Set IntervalCode := {c | Delta ∈ c.toSet}
  have hm0 : MeasurableSet E0 := measurableSet_interval_contains 0
  have hm1 : MeasurableSet E1 := measurableSet_interval_contains Delta
  have hc0 : 9 / 10 ≤ L0.real E0 :=
    finite_prior_coverage_lower n s0 F0 hs0 I 0 hF0 hhonest
  have hc1 : 9 / 10 ≤ L1.real E1 :=
    finite_prior_coverage_lower n s1 F1 hs1 I Delta hF1 hhonest
  have hgap := Causalean.Stat.measureReal_sub_le_tvDist (μ := L0) (ν := L1) hm1
  change TV L0 L1 ≤ 1 / 4 at htv
  have hboth : 11 / 20 ≤ L0.real (E0 ∩ E1) := by
    have hu := measureReal_union_add_inter (μ := L0) (s := E0) hm1
    have hb : L0.real (E0 ∪ E1) ≤ 1 := measureReal_le_one
    linarith
  have hmass : ENNReal.ofReal (11 / 20 : ℝ) ≤ L0 (E0 ∩ E1) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top L0 _)]
    exact ENNReal.ofReal_le_ofReal hboth
  have hind : (∫⁻ c, (E0 ∩ E1).indicator (fun _ => ENNReal.ofReal Delta) c ∂L0) =
      ENNReal.ofReal Delta * L0 (E0 ∩ E1) := by
    rw [lintegral_indicator (hm0.inter hm1)]
    simp
  calc
    _ = ENNReal.ofReal Delta * ENNReal.ofReal (11 / 20 : ℝ) := by
      rw [← ENNReal.ofReal_mul hd]
      congr 1
      ring
    _ ≤ ENNReal.ofReal Delta * L0 (E0 ∩ E1) :=
      mul_le_mul_of_nonneg_left hmass (zero_le)
    _ = ∫⁻ c, (E0 ∩ E1).indicator (fun _ => ENNReal.ofReal Delta) c ∂L0 := hind.symm
    _ ≤ ∫⁻ c, c.leb ∂L0 := by
      apply lintegral_mono
      intro c
      by_cases hc : c ∈ E0 ∩ E1
      · rw [Set.indicator_of_mem hc]
        exact interval_leb_ge_span c Delta hc.1 hc.2
      · rw [Set.indicator_of_notMem hc]
        exact zero_le
    _ ≤ worstLength n I := finite_prior_length_le_worstLength n s0 F0 hs0 I
      (fun i => (hF0 i).1)

/-- [The explicit inversion kernel equals the conservative tuned interval and attains honest
coverage and optimal maximal expected length. The scalar and interval frontiers are uniformly
comparable with the stated numerical constants.](goal)
The [public parameters and their domains](hyp:n,epsilon,hn,he) and
the [Efron--Stein gate](hyp:efronStein_of_gate),
[bounded-differences gate](hyp:boundedDifferences_of_gate), and
[Cayley gate](hyp:cayley_of_gate) specify the conditional scope. -/
-- @node: thm:sharp-interval-frontier
theorem sharp_interval_frontier (efronStein_of_gate : EfronSteinReplacement)
    (boundedDifferences_of_gate : BoundedDifferencesMGF) (cayley_of_gate : CayleyLabeledTreeCount)
    (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    ell n epsilon = rate n epsilon ∧ cI = (2 : ℝ)^(-20 : ℤ) ∧ CI = (2 : ℝ)^22 ∧
    0 < ell n epsilon ∧ 0 < cI ∧ 0 < CI ∧
    optimalIntervalHandle n epsilon = publicTunedInterval n epsilon ∧
    IsMarkovKernel (optimalIntervalHandle n epsilon) ∧
    PrivateKernel n epsilon (optimalIntervalHandle n epsilon) ∧
    ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ)*rate n epsilon) ≤ privateHonestLength n epsilon ∧
    privateHonestLength n epsilon ≤ worstLength n (optimalIntervalHandle n epsilon) ∧
    worstLength n (optimalIntervalHandle n epsilon) ≤ ENNReal.ofReal (2^22*rate n epsilon) ∧
    (∀ P, CompleteModel P → 9/10 ≤ coverage n (optimalIntervalHandle n epsilon) P) ∧
    ENNReal.ofReal ((2 : ℝ)^(-38 : ℤ))*privateMinimaxRisk n epsilon ≤
      privateHonestLength n epsilon ∧
    privateHonestLength n epsilon ≤ ENNReal.ofReal (2^42)*privateMinimaxRisk n epsilon := by
  have hr : 0 < rate n epsilon := rate_pos n epsilon (by omega)
  have hhandle := optimalIntervalHandle_eq_publicTunedInterval n epsilon hn he
  obtain ⟨s0, s1, F0, F1, Delta, hs0, hs1, hd, hF0, hF1, _, htv⟩ :=
    frontier_testing_priors boundedDifferences_of_gate cayley_of_gate n epsilon hn he
  have hd0 : 0 ≤ Delta := le_trans (by positivity) hd
  have hlower : ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ) * rate n epsilon) ≤
      privateHonestLength n epsilon := by
    unfold privateHonestLength
    refine le_iInf fun I => le_iInf fun hI => ?_
    let : IsMarkovKernel I := hI.1
    have htest := finite_priors_interval_lower n s0 s1 F0 F1 hs0 hs1 I Delta hd0
      hF0 hF1 hI.2.2 (htv IntervalCode I hI.2.1)
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) htest
    have hscale : (2 : ℝ)^(-20 : ℤ) ≤ (11 / 20) * (2 : ℝ)^(-14 : ℤ) := by norm_num
    calc
      _ ≤ ((11 / 20) * (2 : ℝ)^(-14 : ℤ)) * rate n epsilon :=
        mul_le_mul_of_nonneg_right hscale hr.le
      _ = (11 / 20) * ((2 : ℝ)^(-14 : ℤ) * rate n epsilon) := by ring
      _ ≤ (11 / 20) * Delta := mul_le_mul_of_nonneg_left hd (by norm_num)
  obtain ⟨_, _, _, _, _, _, _, _, _, hmarkov, hprivate, _, hlength, hcoverage⟩ :=
    uniform_private_upper efronStein_of_gate n 2 epsilon (1 / 4) hn (by omega) he
      ⟨by norm_num, le_rfl⟩
  have hfeasible : privateHonestLength n epsilon ≤
      worstLength n (publicTunedInterval n epsilon) :=
    iInf_le_of_le (publicTunedInterval n epsilon)
      (iInf_le_of_le ⟨hmarkov, hprivate, hcoverage⟩ le_rfl)
  have hfront := matched_risk_frontier efronStein_of_gate boundedDifferences_of_gate
    cayley_of_gate n epsilon hn he
  have hcompareLower : ENNReal.ofReal ((2 : ℝ)^(-38 : ℤ)) *
      privateMinimaxRisk n epsilon ≤ privateHonestLength n epsilon := by
    calc
      _ ≤ ENNReal.ofReal ((2 : ℝ)^(-38 : ℤ)) *
          ENNReal.ofReal (2^18 * rate n epsilon) :=
        mul_le_mul_of_nonneg_left hfront.2.1 (zero_le)
      _ = ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ) * rate n epsilon) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        norm_num
        ring
      _ ≤ _ := hlower
  have hcompareUpper : privateHonestLength n epsilon ≤
      ENNReal.ofReal (2^42) * privateMinimaxRisk n epsilon := by
    calc
      _ ≤ ENNReal.ofReal (2^22 * rate n epsilon) := hfeasible.trans hlength
      _ = ENNReal.ofReal (2^42 : ℝ) *
          ENNReal.ofReal ((2 : ℝ)^(-20 : ℤ) * rate n epsilon) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        norm_num
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfront.1 (zero_le)
  rw [hhandle]
  exact ⟨rfl, rfl, rfl, hr, by norm_num [cI], by norm_num [CI], rfl,
    hmarkov, hprivate, hlower, hfeasible, hlength, hcoverage, hcompareLower, hcompareUpper⟩
end CausalSmith.Stat.PrivateCateRoughdesign
