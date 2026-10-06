module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.HwSupport
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorExpectation

/-! # HW chronological median tail and expectation

The finite model-specific radius transports arbitrary-start Chebyshev bounds
to the actual observed law, while the unit bias envelope makes every quantitative
bound independent of that radius. Chronological median concentration and layer
cake give the conservative-depth selector bound in equations (66)--(70).
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open MeasureTheory
open scoped ENNReal

/-- The conservative HW depth leaves at least half of each block usable. For
[the sample size](hyp:n), [the mixing scale](hyp:t0), and [the policy-overlap scale](hyp:zeta),
this establishes [the Hu–Wager conservative depth half result](goal). -/
-- @node: hw_conservativeDepth_half
lemma hw_conservativeDepth_half (n : Nat) (t0 zeta : ℝ) :
    2 * conservativeDepth n t0 zeta ≤ n := by
  have h : conservativeDepth n t0 zeta ≤ n / 2 := min_le_left _ _
  omega

/-- The HW rule maximizes the clipped candidate estimates, giving the same deterministic regret
comparison as equation (70). For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), [the model](hyp:m),
[the sample size assumption](hyp:hn), and [the observed word](hyp:w), this establishes
[the Hu–Wager block regret bound max error result](goal). -/
-- @node: hw_block_regret_le_maxError
lemma hw_block_regret_le_maxError {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hn : 4 ≤ blockLen T M) (w : ObsView T m.nX) :
    simpleRegret m ((hwBlockSelector T M
      (lt_of_lt_of_le (by norm_num : 0 < 2) m.list_size) t0 zeta).1
        m.nX m.Mx.b m.Mx.E w) ≤
      2 * (⨆ i, |candidateEstimate T M m.nX
        (conservativeDepth (blockLen T M) t0 zeta) m.Mx.b m.Mx.E w i -
          policyValue m i|) := by
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : 0 < 2) m.list_size
  change (⨆ i, policyValue m i) - policyValue m
    (blockSelectorRaw T M hM (fun n ↦ conservativeDepth n t0 zeta)
      m.nX m.Mx.b m.Mx.E w) ≤ _
  exact selector_argmax_regret_le_maxError hM (policyValue m)
    (candidateEstimate T M m.nX (conservativeDepth (blockLen T M) t0 zeta)
      m.Mx.b m.Mx.E w)
    (blockSelectorRaw T M hM (fun n ↦ conservativeDepth n t0 zeta)
      m.nX m.Mx.b m.Mx.E w)
    (fun i ↦ selector_block_maximizes T M m.nX hM
      (fun n ↦ conservativeDepth n t0 zeta) m.Mx.b m.Mx.E w hn i)

/-- The actual block past-event inequality has a unit bias coefficient in the HW class. The
finite radius supplies the law identity but drops out of the bound. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
[the block index](hyp:ell), [the past](hyp:past), [the past assumption](hyp:hpast),
[the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the Hu–Wager actual block chebyshev past real result](goal). -/
-- @node: hw_actual_block_chebyshev_past_real
lemma hw_actual_block_chebyshev_past_real {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (ell : Fin (numBlocks M)) (past : Set (ObsView T m.nX))
    (hpast : MeasurableSet[selectorObservedPast T m.nX
      (ell.val * blockLen T M)] past) (j : Fin M) (k : Nat)
    (hk : 2 * k ≤ blockLen T M) (hn : 4 ≤ blockLen T M) (x : ℝ) (hx : 0 < x) :
    ((obsLaw m.Mx.toRawB) (past ∩ {w |
      mixingAlpha t0 ^ k *
        (1 + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0))) + x <
          |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|})).toReal ≤
      (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (blockLen T M - k : Nat)) / x ^ 2) * ((obsLaw m.Mx.toRawB) past).toReal := by
  obtain ⟨C, hC⟩ := hw_exists_policyListClass_radius t0 zeta m hClass
  have htail := selector_actual_block_chebyshev_past_real t0 zeta C m hC
    ell past hpast j k hk hn x hx
  have hq : overlapRadius C ≤ 1 := by
    unfold overlapRadius
    apply (div_le_one (by linarith [hC.C_ge_one])).mpr
    linarith
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add_left hq (1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0))))
    (pow_nonneg (show 0 ≤ mixingAlpha t0 from Real.exp_nonneg _) k)
  letI : IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) htail
  rintro w ⟨hp, hw⟩
  exact ⟨hp, lt_of_le_of_lt (add_le_add_left hb x) hw⟩

/-- The conservative-depth HW estimates satisfy the simultaneous clipped median tail, by direct
chronological past-event products, as in (67)--(68). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
[the history length](hyp:k), [the history length assumption](hyp:hk),
[the sample size assumption](hyp:hn), [the observed state](hyp:x), [the reward symbol](hyp:r),
[the observed state assumption](hyp:hx), [the r0 assumption](hyp:hr0),
[the r1 assumption](hyp:hr1), and [the ratio assumption](hyp:hratio), this establishes
[the Hu–Wager candidate estimate max tail actual result](goal). -/
-- @node: hw_candidateEstimate_max_tail_actual
lemma hw_candidateEstimate_max_tail_actual {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (k : Nat) (hk : 2 * k ≤ blockLen T M) (hn : 4 ≤ blockLen T M)
    (x r : ℝ) (hx : 0 < x) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hratio : ((1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (k + 1) / (blockLen T M - k : Nat)) / x ^ 2 ≤ r ^ 2) :
    (obsLaw m.Mx.toRawB) {w |
      mixingAlpha t0 ^ k *
        (1 + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0))) + x <
      ⨆ j, |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j - policyValue m j|} ≤
      min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ numBlocks M)) := by
  obtain ⟨C, hC⟩ := hw_exists_policyListClass_radius t0 zeta m hClass
  letI : IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  apply selector_candidateEstimate_max_tail_of_past t0 zeta C m hC k
    (obsLaw m.Mx.toRawB)
    (fun ell ↦ selectorObservedPast T m.nX (ell.val * blockLen T M))
    (fun ell ↦ selectorObservedPast_le T m.nX _) _ r hr0 hr1
  · intro j ell ell' h
    exact selector_block_bad_measurable_past T M m.nX k m.Mx.b (m.Mx.E j)
      ell ell' h _ (policyValue m j)
  · intro j ell past hpast
    exact (hw_actual_block_chebyshev_past_real t0 zeta m hClass
      ell past hpast j k hk hn x hx).trans
      (mul_le_mul_of_nonneg_right hratio ENNReal.toReal_nonneg)

/-- The HW selector inherits the simultaneous median tail with a doubled threshold via the
deterministic maximizing-regret inequality. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
[the sample size assumption](hyp:hn), [the observed state](hyp:x), [the reward symbol](hyp:r),
[the observed state assumption](hyp:hx), [the r0 assumption](hyp:hr0),
[the r1 assumption](hyp:hr1), and [the ratio assumption](hyp:hratio), this establishes
[the Hu–Wager block regret tail actual result](goal). -/
-- @node: hw_block_regret_tail_actual
lemma hw_block_regret_tail_actual {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (hn : 4 ≤ blockLen T M) (x r : ℝ) (hx : 0 < x)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hratio : ((1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (conservativeDepth (blockLen T M) t0 zeta + 1) /
        (blockLen T M - conservativeDepth (blockLen T M) t0 zeta : Nat)) / x ^ 2 ≤ r ^ 2) :
    (obsLaw m.Mx.toRawB) {w |
      2 * (mixingAlpha t0 ^ conservativeDepth (blockLen T M) t0 zeta *
        (1 + 1 / ((blockLen T M -
          conservativeDepth (blockLen T M) t0 zeta : Nat) * (1 - mixingAlpha t0))) + x) <
        simpleRegret m ((hwBlockSelector T M
          (lt_of_lt_of_le (by norm_num) m.list_size) t0 zeta).1
            m.nX m.Mx.b m.Mx.E w)} ≤
      min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ numBlocks M)) := by
  apply le_trans (measure_mono ?_)
    (hw_candidateEstimate_max_tail_actual t0 zeta m hClass _
      (hw_conservativeDepth_half _ _ _) hn x r hx hr0 hr1 hratio)
  intro w hw
  have hreg := hw_block_regret_le_maxError t0 zeta m hn w
  simp only [Set.mem_ofPred_eq] at hw ⊢
  linarith

/-- The HW regret tail holds at every threshold above the block standard deviation, with the
polynomial envelope in equations (68)--(69). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
and [the sample size assumption](hyp:hn), this establishes
[the Hu–Wager block regret tail actual sd result](goal). -/
-- @node: hw_block_regret_tail_actual_sd
lemma hw_block_regret_tail_actual_sd {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (hn : 4 ≤ blockLen T M) :
    let k := conservativeDepth (blockLen T M) t0 zeta
    let σ := Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
      4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
        (blockLen T M - k : Nat))
    ∀ x : ℝ, 0 < x → σ ≤ x →
      (obsLaw m.Mx.toRawB) {w |
        2 * (mixingAlpha t0 ^ k *
          (1 + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0))) + x) <
          simpleRegret m ((hwBlockSelector T M
            (lt_of_lt_of_le (by norm_num) m.list_size) t0 zeta).1
              m.nX m.Mx.b m.Mx.E w)} ≤
        min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * σ / x) ^ numBlocks M)) := by
  dsimp only
  intro x hx hσ
  have hL : 1 < policyFactor zeta := by
    unfold policyFactor
    exact Real.one_lt_exp_iff.mpr hClass.zeta_pos
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos)
  have hv : 0 ≤ ((1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (conservativeDepth (blockLen T M) t0 zeta + 1) /
        (blockLen T M - conservativeDepth (blockLen T M) t0 zeta : Nat)) := by positivity
  have ht := hw_block_regret_tail_actual t0 zeta m hClass hn x
    (Real.sqrt ((1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (conservativeDepth (blockLen T M) t0 zeta + 1) /
        (blockLen T M - conservativeDepth (blockLen T M) t0 zeta : Nat)) / x)
    hx (by positivity) ((div_le_one hx).mpr hσ)
    (by rw [div_pow, Real.sq_sqrt hv])
  simpa only [mul_div_assoc] using ht

/-- Integrating the actual HW median tail by layer cake proves the conservative-depth
bias-plus-deviation expectation bound, equations (69)--(70). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
and [the sample size assumption](hyp:hn), this establishes
[the Hu–Wager block expected regret bound bias sd result](goal). -/
-- @node: hw_block_expectedRegret_le_bias_sd
lemma hw_block_expectedRegret_le_bias_sd {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (hn : 4 ≤ blockLen T M) :
    let k := conservativeDepth (blockLen T M) t0 zeta
    let b := mixingAlpha t0 ^ k *
      (1 + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0)))
    let σ := Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
      4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
        (blockLen T M - k : Nat))
    expectedRegret (hwBlockSelector T M (by have := m.list_size; omega) t0 zeta) m ≤
      2 * b + 8 * Real.exp 1 * σ := by
  dsimp only
  let k := conservativeDepth (blockLen T M) t0 zeta
  let b := mixingAlpha t0 ^ k *
    (1 + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0)))
  let σ := Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
    4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
      (blockLen T M - k : Nat))
  let sel := hwBlockSelector T M (lt_of_lt_of_le (by norm_num : 0 < 2) m.list_size)
    t0 zeta
  let μ := obsLaw m.Mx.toRawB
  let R := fun w ↦ simpleRegret m (sel.1 m.nX m.Mx.b m.Mx.E w)
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    unfold obsLaw
    have hobs : Measurable (@obsProj T m.nX m.nH) := by fun_prop
    exact Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hL : 1 < policyFactor zeta := by
    unfold policyFactor
    exact Real.one_lt_exp_iff.mpr hClass.zeta_pos
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos)
  have hk := hw_conservativeDepth_half (blockLen T M) t0 zeta
  have hN : (0 : ℝ) < (blockLen T M - k : Nat) := by
    exact_mod_cast (show 0 < blockLen T M - k by dsimp [k]; omega)
  have hσ : 0 < σ := by
    dsimp only [σ]
    apply Real.sqrt_pos.mpr
    positivity
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hscale : σ ≤ 2 * Real.exp 1 * σ := by nlinarith [hσ.le]
  obtain ⟨C, hC⟩ := hw_exists_policyListClass_radius t0 zeta m hClass
  have hbnd := selector_integral_le_of_square_tail μ R b (2 * Real.exp 1 * σ)
    (selector_simpleRegret_integrable t0 zeta C sel m hC) (by positivity) ?_
  · change (∫ w, R w ∂μ) ≤ 2 * b + 8 * Real.exp 1 * σ
    nlinarith [hbnd]
  · intro x hx
    have hxpos : 0 < x := (by positivity : 0 < 2 * Real.exp 1 * σ).trans_le hx
    have ht := hw_block_regret_tail_actual_sd t0 zeta m hClass hn
      x hxpos (hscale.trans hx)
    apply (ht.trans (min_le_right _ _)).trans
    exact selector_median_tail_square_envelope M (numBlocks M) σ x
      (by have := m.list_size; omega)
      (by have := selector_numBlocks_ge_three M; omega)
      (selector_numBlocks_log_bounds M m.list_size).1 hσ.le hxpos hx

end CausalSmith.Stat.PomdpPolicyclassRegret
