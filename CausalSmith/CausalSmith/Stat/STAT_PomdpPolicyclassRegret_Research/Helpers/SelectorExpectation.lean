module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorLayercake
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorActualBlock
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockMoments
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorBlockHistory
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorBlockTails
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorChronologicalPast

/-! # Uniform upper regret bound for the observable block selector -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open MeasureTheory
open scoped BigOperators ENNReal

/-- Clipping keeps an estimate in the reward interval. For [the observed state](hyp:x), this
establishes [the selector clip unit result](goal). -/
-- @node: selector_clip_unit
lemma selector_clip_unit (x : ℝ) : clipUnit01 x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- Clipping cannot enlarge error around any legal stationary reward value. For
[the observed state](hyp:x), [the parameter](hyp:θ), and [the parameter assumption](hyp:hθ),
this establishes [the selector clip error bound result](goal). -/
-- @node: selector_clip_error_le
lemma selector_clip_error_le (x θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    |clipUnit01 x - θ| ≤ |x - θ| := by
  rcases hθ with ⟨hθ0, hθ1⟩
  by_cases hx0 : x < 0
  · rw [clipUnit01, min_eq_right (by linarith), max_eq_left hx0.le]
    rw [abs_of_nonpos (by linarith : 0 - θ ≤ 0),
      abs_of_nonpos (by linarith : x - θ ≤ 0)]
    linarith
  · by_cases hx1 : 1 < x
    · rw [clipUnit01, min_eq_left hx1.le, max_eq_right (by norm_num)]
      rw [abs_of_nonneg (by linarith : 0 ≤ 1 - θ),
        abs_of_nonneg (by linarith : 0 ≤ x - θ)]
      linarith
    · rw [clipUnit01, min_eq_right (le_of_not_gt hx1),
        max_eq_right (le_of_not_gt hx0)]

/-- The specified tie rule really selects a maximizer. For [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the candidate score](hyp:score), and
[the i](hyp:i), this establishes [the selector smallest maximizer spec result](goal). -/
-- @node: selector_smallestMaximizer_spec
lemma selector_smallestMaximizer_spec (M : Nat) (hM : 0 < M)
    (score : Fin M → ℝ) (i : Fin M) :
    score i ≤ score (smallestMaximizer M hM score) := by
  classical
  exact (Finset.mem_filter.mp
    (Finset.min'_mem _ (maximizer_nonempty M hM score))).2 i

/-- The block selector maximizes its clipped scores when blocks are long enough. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the observed-state count](hyp:nX), [the candidate-policy count assumption](hyp:hM),
[the history depth](hyp:depth), [the behavior policy](hyp:b),
[the candidate-policy list](hyp:E), [the observed word](hyp:w),
[the sample size assumption](hyp:hn), and [the i](hyp:i), this establishes
[the selector block maximizes result](goal). -/
-- @node: selector_block_maximizes
lemma selector_block_maximizes (T M nX : Nat) (hM : 0 < M)
    (depth : Nat → Nat) (b : Policy nX) (E : Fin M → Policy nX)
    (w : ObsView T nX) (hn : 4 ≤ blockLen T M) (i : Fin M) :
    candidateEstimate T M nX (depth (blockLen T M)) b E w i ≤
      candidateEstimate T M nX (depth (blockLen T M)) b E w
        (blockSelectorRaw T M hM depth nX b E w) := by
  rw [blockSelectorRaw, if_neg (not_lt.mpr hn)]
  exact selector_smallestMaximizer_spec M hM _ i

/-- Any score maximizer loses at most twice a uniform coordinate error. This is the
deterministic comparison in equation (13) of the roadmap. For
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the value](hyp:value), [the candidate score](hyp:score), [the selected](hyp:selected),
[the δ](hyp:δ), [the max assumption](hyp:hmax), and [the err assumption](hyp:herr), this
establishes [the selector argmax regret bound result](goal). -/
-- @node: selector_argmax_regret_le
lemma selector_argmax_regret_le {M : Nat} (hM : 0 < M)
    (value score : Fin M → ℝ) (selected : Fin M) (δ : ℝ)
    (hmax : ∀ i, score i ≤ score selected)
    (herr : ∀ i, |score i - value i| ≤ δ) :
    (⨆ i, value i) - value selected ≤ 2 * δ := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hpoint : ∀ i, value i ≤ value selected + 2 * δ := by
    intro i
    have hi := (abs_le.mp (herr i)).1
    have hs := (abs_le.mp (herr selected)).2
    have hm := hmax i
    linarith
  have hsup := ciSup_le hpoint
  linarith

/-- A finite vector admits the uniform error used in equation (13). For
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the value](hyp:value), [the candidate score](hyp:score), [the selected](hyp:selected), and
[the max assumption](hyp:hmax), this establishes
[the selector argmax regret bound max error result](goal). -/
-- @node: selector_argmax_regret_le_maxError
lemma selector_argmax_regret_le_maxError {M : Nat} (hM : 0 < M)
    (value score : Fin M → ℝ) (selected : Fin M)
    (hmax : ∀ i, score i ≤ score selected) :
    (⨆ i, value i) - value selected ≤ 2 * (⨆ i, |score i - value i|) := by
  apply selector_argmax_regret_le hM value score selected _ hmax
  intro i
  exact le_ciSup (Finite.bddAbove_range (fun i : Fin M ↦ |score i - value i|)) i

/-- The model's stationary candidate values are genuine unit-interval rewards. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), and [the candidate index](hyp:j), this establishes
[the selector policy value unit result](goal). -/
-- @node: selector_policyValue_unit
lemma selector_policyValue_unit {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M) :
    policyValue m j ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := (phiw_list_target_stationary t0 zeta C m hClass j).1
  have hg := phiw_list_reward_regression_unit m (m.Mx.E j)
    (hClass.action_overlap j).1
  change (∑ s, listStationaryLaw m (m.Mx.E j) s *
    listRewardRegression m (m.Mx.E j) s) ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact Finset.sum_nonneg fun s _ ↦ mul_nonneg (hd.1 s) (hg s).1
  · calc
      _ ≤ ∑ s, listStationaryLaw m (m.Mx.E j) s * 1 :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hg s).2 (hd.1 s)
      _ = 1 := by simpa using hd.2

/-- Simple regret is nonnegative and at most one, including the short-block branch. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), and [the candidate index](hyp:j), this establishes
[the selector simple regret unit result](goal). -/
-- @node: selector_simpleRegret_unit
lemma selector_simpleRegret_unit {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M) :
    simpleRegret m j ∈ Set.Icc (0 : ℝ) 1 := by
  let : Nonempty (Fin M) := ⟨j⟩
  obtain ⟨hj0, hj1⟩ := selector_policyValue_unit t0 zeta C m hClass j
  have hsup : (⨆ i, policyValue m i) ≤ 1 :=
    ciSup_le fun i ↦ (selector_policyValue_unit t0 zeta C m hClass i).2
  have hle := le_ciSup (Finite.bddAbove_range (policyValue m)) j
  unfold simpleRegret
  constructor <;> linarith

/-- Clipping the candidate medians preserves their coordinatewise error bound. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the history length](hyp:k), [the observed word](hyp:w), and
[the candidate index](hyp:j), this establishes
[the selector candidate estimate error bound result](goal). -/
-- @node: selector_candidateEstimate_error_le
lemma selector_candidateEstimate_error_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (k : Nat) (w : ObsView T m.nX) (j : Fin M) :
    |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j - policyValue m j| ≤
      |blockMedian T M m.nX k m.Mx.b (m.Mx.E j) w - policyValue m j| := by
  exact selector_clip_error_le _ _ (selector_policyValue_unit t0 zeta C m hClass j)

/-- The observable selector's regret is controlled by the largest clipped score error. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the sample size assumption](hyp:hn), and [the observed word](hyp:w), this establishes
[the selector block regret bound max error result](goal). -/
-- @node: selector_block_regret_le_maxError
lemma selector_block_regret_le_maxError {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hn : 4 ≤ blockLen T M) (w : ObsView T m.nX) :
    simpleRegret m ((blockSelector T M
      (lt_of_lt_of_le (by norm_num : 0 < 2) m.list_size) t0 zeta C).1
        m.nX m.Mx.b m.Mx.E w) ≤
      2 * (⨆ i, |candidateEstimate T M m.nX
        (adaptiveDepth (blockLen T M) t0 zeta C) m.Mx.b m.Mx.E w i -
          policyValue m i|) := by
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : 0 < 2) m.list_size
  change (⨆ i, policyValue m i) - policyValue m
    (blockSelectorRaw T M hM (fun n ↦ adaptiveDepth n t0 zeta C)
      m.nX m.Mx.b m.Mx.E w) ≤ _
  exact selector_argmax_regret_le_maxError hM (policyValue m)
    (candidateEstimate T M m.nX (adaptiveDepth (blockLen T M) t0 zeta C)
      m.Mx.b m.Mx.E w)
    (blockSelectorRaw T M hM (fun n ↦ adaptiveDepth n t0 zeta C)
      m.nX m.Mx.b m.Mx.E w)
    (fun i ↦ selector_block_maximizes T M m.nX hM
      (fun n ↦ adaptiveDepth n t0 zeta C) m.Mx.b m.Mx.E w hn i)

/-- Any legal observable selector has measurable simple regret. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the observable selector](hyp:sel), and [the model](hyp:m),
this establishes [the selector simple regret measurability result](goal). -/
-- @node: selector_simpleRegret_measurable
@[fun_prop]
lemma selector_simpleRegret_measurable {T M : Nat}
    (sel : ObservableSelector T M) (m : ModelIndex T M) :
    Measurable (fun w ↦ simpleRegret m (sel.1 m.nX m.Mx.b m.Mx.E w)) := by
  first
  | fun_prop
  | exact (measurable_of_finite (simpleRegret m)).comp (sel.2 m.nX m.Mx.b m.Mx.E)

/-- Bounded rewards give regret integrability for free; no regularity premise is added. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the observable selector](hyp:sel), [the model](hyp:m), and [the class assumption](hyp:hClass),
this establishes [the selector simple regret integrability result](goal). -/
-- @node: selector_simpleRegret_integrable
lemma selector_simpleRegret_integrable {T M : Nat} (t0 zeta C : ℝ)
    (sel : ObservableSelector T M) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) :
    Integrable (fun w ↦ simpleRegret m (sel.1 m.nX m.Mx.b m.Mx.E w))
      (obsLaw m.Mx.toRawB) := by
  let : IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
    unfold obsLaw
    have hobs : Measurable (@obsProj T m.nX m.nH) := by
      fun_prop
    exact Measure.isProbabilityMeasure_map hobs.aemeasurable
  apply Integrable.of_mem_Icc 0 1 (selector_simpleRegret_measurable sel m).aemeasurable
  exact Filter.Eventually.of_forall fun w ↦
    selector_simpleRegret_unit t0 zeta C m hClass _

/-- The universal regret cap handles small blocks and the truncated frontier. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the observable selector](hyp:sel), [the model](hyp:m), and [the class assumption](hyp:hClass),
this establishes [the selector expected regret unit result](goal). -/
-- @node: selector_expectedRegret_unit
lemma selector_expectedRegret_unit {T M : Nat} (t0 zeta C : ℝ)
    (sel : ObservableSelector T M) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) :
    expectedRegret sel m ∈ Set.Icc (0 : ℝ) 1 := by
  let : IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
    unfold obsLaw
    have hobs : Measurable (@obsProj T m.nX m.nH) := by
      fun_prop
    exact Measure.isProbabilityMeasure_map hobs.aemeasurable
  constructor
  · apply integral_nonneg
    intro w
    exact (selector_simpleRegret_unit t0 zeta C m hClass _).1
  · calc
      expectedRegret sel m ≤ ∫ _ : ObsView T m.nX, (1 : ℝ) ∂obsLaw m.Mx.toRawB :=
        integral_mono_ae (selector_simpleRegret_integrable t0 zeta C sel m hClass)
          (integrable_const 1) (Filter.Eventually.of_forall fun w ↦
            (selector_simpleRegret_unit t0 zeta C m hClass _).2)
      _ = 1 := by simp

/-- A large clipped coordinate error still supplies a half-size subset of bad raw blocks. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the history length](hyp:k), [the observed word](hyp:w),
[the candidate index](hyp:j), [the δ](hyp:δ), and [the err assumption](hyp:herr), this
establishes [the selector candidate estimate bad witness result](goal). -/
-- @node: selector_candidateEstimate_bad_witness
lemma selector_candidateEstimate_bad_witness {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (k : Nat) (w : ObsView T m.nX) (j : Fin M) (δ : ℝ)
    (herr : δ < |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j -
      policyValue m j|) :
    ∃ S : Finset (Fin (numBlocks M)), S.card = (numBlocks M + 1) / 2 ∧
      ∀ ell ∈ S, δ < |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w -
        policyValue m j| := by
  apply selector_blockMedian_bad_witness
  exact herr.trans_le (selector_candidateEstimate_error_le t0 zeta C m hClass k w j)

/-- Clipping preserves the median union bound for each candidate's estimation error. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the history length](hyp:k), [the candidate index](hyp:j),
[the δ](hyp:δ), and [the measure](hyp:μ), this establishes
[the selector candidate estimate tail union result](goal). -/
-- @node: selector_candidateEstimate_tail_union
lemma selector_candidateEstimate_tail_union {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (k : Nat) (j : Fin M) (δ : ℝ) (μ : Measure (ObsView T m.nX)) :
    μ {w | δ < |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j -
      policyValue m j|} ≤
      ∑ S ∈ Finset.univ.powersetCard ((numBlocks M + 1) / 2),
        μ {w | ∀ ell ∈ S, δ < |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w -
          policyValue m j|} := by
  apply le_trans (measure_mono ?_)
    (selector_blockMedian_tail_union T M m.nX k m.Mx.b (m.Mx.E j) μ
      (policyValue m j) δ)
  intro w hw
  exact hw.trans_le (selector_candidateEstimate_error_le t0 zeta C m hClass k w j)

/-- Equation (11) for the actual clipped candidate estimates follows from adapted conditional
bounds on their raw block errors. The trajectory-specific conditional block law is a separate
input, not an independence premise. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the history length](hyp:k), [the measure](hyp:μ),
[the observed history](hyp:history), [the model assumption](hyp:hm), [the δ](hyp:δ),
[the reward symbol](hyp:r), [the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1),
[the before assumption](hyp:hbefore), and [the cond assumption](hyp:hcond), this establishes
[the selector candidate estimate max tail of cond exp result](goal). -/
-- @node: selector_candidateEstimate_max_tail_of_condExp
lemma selector_candidateEstimate_max_tail_of_condExp {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (k : Nat) (μ : Measure (ObsView T m.nX)) [IsProbabilityMeasure μ]
    (history : Fin (numBlocks M) → MeasurableSpace (ObsView T m.nX))
    (hm : ∀ ell, history ell ≤ (inferInstance : MeasurableSpace (ObsView T m.nX)))
    (δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbefore : ∀ j ell ell', ell < ell' →
      MeasurableSet[history ell'] {w | δ <
        |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|})
    (hcond : ∀ j ell, μ[({w | δ <
      |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|}).indicator
        (fun _ ↦ (1 : ℝ)) | history ell] ≤ᵐ[μ] fun _ ↦ r ^ 2) :
    μ {w | δ < ⨆ j, |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j -
      policyValue m j|} ≤ min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ numBlocks M)) := by
  let : Nonempty (Fin M) := ⟨⟨0, lt_of_lt_of_le (by norm_num) m.list_size⟩⟩
  have hbad : ∀ j ell, MeasurableSet {w | δ <
      |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|} := by
    intro j ell
    apply measurableSet_lt <;> fun_prop
  have hmed := selector_simultaneous_median_tail_of_condExp μ
    (selector_numBlocks_odd M) history hm
    (fun j ↦ blockScore T M m.nX k m.Mx.b (m.Mx.E j)) (policyValue m)
    δ r hr0 hr1 hbad hbefore hcond
  apply le_min (prob_le_one) (le_trans (measure_mono ?_) hmed)
  intro w hw
  obtain ⟨j, hj⟩ := (lt_ciSup_iff (Finite.bddAbove_range
    (fun j : Fin M ↦ |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j -
      policyValue m j|))).mp hw
  exact ⟨j, hj.trans_le (selector_candidateEstimate_error_le t0 zeta C m hClass k w j)⟩

/-- Equation (11) for the actual clipped candidate estimates follows from adapted past-event
bounds on their raw block errors. The trajectory-specific past-event block bound is a separate
input, not an independence premise. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the history length](hyp:k), [the measure](hyp:μ),
[the observed history](hyp:history), [the model assumption](hyp:hm), [the δ](hyp:δ),
[the reward symbol](hyp:r), [the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1),
[the before assumption](hyp:hbefore), and [the step assumption](hyp:hstep), this establishes
[the selector candidate estimate max tail of past result](goal). -/
-- @node: selector_candidateEstimate_max_tail_of_past
lemma selector_candidateEstimate_max_tail_of_past {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (k : Nat) (μ : Measure (ObsView T m.nX)) [IsProbabilityMeasure μ]
    (history : Fin (numBlocks M) → MeasurableSpace (ObsView T m.nX))
    (hm : ∀ ell, history ell ≤ (inferInstance : MeasurableSpace (ObsView T m.nX)))
    (δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbefore : ∀ j ell ell', ell < ell' →
      MeasurableSet[history ell'] {w | δ <
        |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|})
    (hstep : ∀ j ell past, MeasurableSet[history ell] past →
      (μ (past ∩ {w | δ <
        |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|})).toReal ≤
          r ^ 2 * (μ past).toReal) :
    μ {w | δ < ⨆ j, |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j -
      policyValue m j|} ≤ min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ numBlocks M)) := by
  let : Nonempty (Fin M) := ⟨⟨0, lt_of_lt_of_le (by norm_num) m.list_size⟩⟩
  have hbad : ∀ j ell, MeasurableSet {w | δ <
      |blockScore T M m.nX k m.Mx.b (m.Mx.E j) ell w - policyValue m j|} := by
    intro j ell
    apply measurableSet_lt <;> fun_prop
  have hmed := selector_simultaneous_median_tail_of_past μ
    (selector_numBlocks_odd M) history hm
    (fun j ↦ blockScore T M m.nX k m.Mx.b (m.Mx.E j)) (policyValue m)
    δ r hr0 hr1 hbad hbefore hstep
  apply le_min (prob_le_one) (le_trans (measure_mono ?_) hmed)
  intro w hw
  obtain ⟨j, hj⟩ := (lt_ciSup_iff (Finite.bddAbove_range
    (fun j : Fin M ↦ |candidateEstimate T M m.nX k m.Mx.b m.Mx.E w j -
      policyValue m j|))).mp hw
  exact ⟨j, hj.trans_le (selector_candidateEstimate_error_le t0 zeta C m hClass k w j)⟩

/-- The maximizing selector inherits the simultaneous median tail with threshold doubled, by the
deterministic regret comparison in equation (13). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the sample size assumption](hyp:hn), [the measure](hyp:μ),
[the observed history](hyp:history), [the model assumption](hyp:hm), [the δ](hyp:δ),
[the reward symbol](hyp:r), [the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1),
[the before assumption](hyp:hbefore), and [the step assumption](hyp:hstep), this establishes
[the selector block regret tail of past result](goal). -/
-- @node: selector_block_regret_tail_of_past
lemma selector_block_regret_tail_of_past {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hn : 4 ≤ blockLen T M) (μ : Measure (ObsView T m.nX)) [IsProbabilityMeasure μ]
    (history : Fin (numBlocks M) → MeasurableSpace (ObsView T m.nX))
    (hm : ∀ ell, history ell ≤ (inferInstance : MeasurableSpace (ObsView T m.nX)))
    (δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbefore : ∀ j ell ell', ell < ell' →
      MeasurableSet[history ell'] {w | δ <
        |blockScore T M m.nX (adaptiveDepth (blockLen T M) t0 zeta C) m.Mx.b (m.Mx.E j) ell w - policyValue m j|})
    (hstep : ∀ j ell past, MeasurableSet[history ell] past →
      (μ (past ∩ {w | δ <
        |blockScore T M m.nX (adaptiveDepth (blockLen T M) t0 zeta C) m.Mx.b (m.Mx.E j) ell w - policyValue m j|})).toReal ≤
          r ^ 2 * (μ past).toReal) :
    μ {w | 2 * δ < simpleRegret m
      ((blockSelector T M (lt_of_lt_of_le (by norm_num) m.list_size)
        t0 zeta C).1 m.nX m.Mx.b m.Mx.E w)} ≤
      min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ numBlocks M)) := by
  apply le_trans (measure_mono ?_)
    (selector_candidateEstimate_max_tail_of_past t0 zeta C m hClass
      (adaptiveDepth (blockLen T M) t0 zeta C) μ history hm δ r hr0 hr1 hbefore hstep)
  intro w hw
  have hreg := selector_block_regret_le_maxError t0 zeta C m hn w
  simp only [Set.mem_setOf_eq] at hw
  change δ < ⨆ j, |candidateEstimate T M m.nX
    (adaptiveDepth (blockLen T M) t0 zeta C) m.Mx.b m.Mx.E w j - policyValue m j|
  linarith

/-- For the actual observation law, the history and adaptation inputs to chronological median
concentration are provided by the block construction. Only the quantitative past-event
inequality remains to be established. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the sample size assumption](hyp:hn), [the δ](hyp:δ),
[the reward symbol](hyp:r), [the r0 assumption](hyp:hr0), [the r1 assumption](hyp:hr1), and
[the step assumption](hyp:hstep), this establishes
[the selector block regret tail actual of past bound result](goal). -/
-- @node: selector_block_regret_tail_actual_of_past_bound
lemma selector_block_regret_tail_actual_of_past_bound {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hn : 4 ≤ blockLen T M) (δ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hstep : ∀ j ell past,
      MeasurableSet[selectorObservedPast T m.nX (ell.val * blockLen T M)] past →
      ((obsLaw m.Mx.toRawB) (past ∩ {w | δ <
        |blockScore T M m.nX (adaptiveDepth (blockLen T M) t0 zeta C)
          m.Mx.b (m.Mx.E j) ell w - policyValue m j|})).toReal ≤
        r ^ 2 * ((obsLaw m.Mx.toRawB) past).toReal) :
    (obsLaw m.Mx.toRawB) {w | 2 * δ < simpleRegret m
      ((blockSelector T M (lt_of_lt_of_le (by norm_num) m.list_size)
        t0 zeta C).1 m.nX m.Mx.b m.Mx.E w)} ≤
      min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ numBlocks M)) := by
  letI : IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  apply selector_block_regret_tail_of_past t0 zeta C m hClass hn
    (obsLaw m.Mx.toRawB)
    (fun ell ↦ selectorObservedPast T m.nX (ell.val * blockLen T M))
    (fun ell ↦ selectorObservedPast_le T m.nX _) δ r hr0 hr1
  · intro j ell ell' h
    exact selector_block_bad_measurable_past T M m.nX _ m.Mx.b (m.Mx.E j)
      ell ell' h δ (policyValue m j)
  · exact hstep

/-- The actual observable selector has the simultaneous median regret tail from equation (11).
The ratio premise is purely numerical; every trajectory past-event bound is derived from the
model class and arbitrary-start moments. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the sample size assumption](hyp:hn),
[the observed state](hyp:x), [the reward symbol](hyp:r),
[the observed state assumption](hyp:hx), [the r0 assumption](hyp:hr0),
[the r1 assumption](hyp:hr1), and [the ratio assumption](hyp:hratio), this establishes
[the selector block regret tail actual result](goal). -/
-- @node: selector_block_regret_tail_actual
lemma selector_block_regret_tail_actual {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hn : 4 ≤ blockLen T M) (x r : ℝ) (hx : 0 < x)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hratio : ((1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (adaptiveDepth (blockLen T M) t0 zeta C + 1) /
        (blockLen T M - adaptiveDepth (blockLen T M) t0 zeta C : Nat)) / x ^ 2 ≤ r ^ 2) :
    (obsLaw m.Mx.toRawB) {w |
      2 * (mixingAlpha t0 ^ adaptiveDepth (blockLen T M) t0 zeta C *
        (overlapRadius C + 1 / ((blockLen T M -
          adaptiveDepth (blockLen T M) t0 zeta C : Nat) * (1 - mixingAlpha t0))) + x) <
        simpleRegret m ((blockSelector T M
          (lt_of_lt_of_le (by norm_num) m.list_size) t0 zeta C).1
            m.nX m.Mx.b m.Mx.E w)} ≤
      min 1 ((M : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ numBlocks M)) := by
  apply selector_block_regret_tail_actual_of_past_bound t0 zeta C m hClass hn
    _ r hr0 hr1
  intro j ell past hpast
  have hk : 2 * adaptiveDepth (blockLen T M) t0 zeta C ≤ blockLen T M := by
    have hd : adaptiveDepth (blockLen T M) t0 zeta C ≤ blockLen T M / 2 := by
      unfold adaptiveDepth
      split_ifs
      · omega
      · exact min_le_left _ _
    omega
  have htail := selector_actual_block_chebyshev_past_real t0 zeta C m hClass
    ell past hpast j _ hk hn x hx
  apply htail.trans
  exact mul_le_mul_of_nonneg_right hratio ENNReal.toReal_nonneg

/-- Equation (11) for the actual maximizing selector, at the prescribed depth and every
threshold above its arbitrary-start standard deviation. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), and [the sample size assumption](hyp:hn), this establishes
[the selector block regret tail actual sd result](goal). -/
-- @node: selector_block_regret_tail_actual_sd
lemma selector_block_regret_tail_actual_sd {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hn : 4 ≤ blockLen T M) :
    let k := adaptiveDepth (blockLen T M) t0 zeta C
    let σ := Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
      4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
        (blockLen T M - k : Nat))
    ∀ x : ℝ, 0 < x → σ ≤ x →
      (obsLaw m.Mx.toRawB) {w |
        2 * (mixingAlpha t0 ^ k *
          (overlapRadius C + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0))) + x) <
          simpleRegret m ((blockSelector T M
            (lt_of_lt_of_le (by norm_num) m.list_size) t0 zeta C).1
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
      policyFactor zeta ^ (adaptiveDepth (blockLen T M) t0 zeta C + 1) /
        (blockLen T M - adaptiveDepth (blockLen T M) t0 zeta C : Nat)) := by positivity
  have ht := selector_block_regret_tail_actual t0 zeta C m hClass hn x
    (Real.sqrt ((1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
      policyFactor zeta ^ (adaptiveDepth (blockLen T M) t0 zeta C + 1) /
        (blockLen T M - adaptiveDepth (blockLen T M) t0 zeta C : Nat)) / x)
    hx (by positivity) ((div_le_one hx).mpr hσ)
    (by rw [div_pow, Real.sq_sqrt hv])
  simpa only [mul_div_assoc] using ht

/-- Layer-cake integration of the actual median tail gives equation (16)'s
bias-plus-standard-deviation expectation bound. The universal coefficient 8e uses an
inverse-square envelope of the polynomial tail from equation (11). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), and [the sample size assumption](hyp:hn), this establishes
[the selector block expected regret bound bias sd result](goal). -/
-- @node: selector_block_expectedRegret_le_bias_sd
lemma selector_block_expectedRegret_le_bias_sd {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hn : 4 ≤ blockLen T M) :
    let k := adaptiveDepth (blockLen T M) t0 zeta C
    let b := mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0)))
    let σ := Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
      4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
        (blockLen T M - k : Nat))
    expectedRegret (blockSelector T M (by have := m.list_size; omega) t0 zeta C) m ≤
      2 * b + 8 * Real.exp 1 * σ := by
  dsimp only
  let k := adaptiveDepth (blockLen T M) t0 zeta C
  let b := mixingAlpha t0 ^ k *
    (overlapRadius C + 1 / ((blockLen T M - k : Nat) * (1 - mixingAlpha t0)))
  let σ := Real.sqrt ((1 + 2 / (policyFactor zeta - 1) +
    4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
      (blockLen T M - k : Nat))
  let sel := blockSelector T M (lt_of_lt_of_le (by norm_num : 0 < 2) m.list_size)
    t0 zeta C
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
  have hN : (0 : ℝ) < (blockLen T M - k : Nat) := by
    exact_mod_cast (selector_adaptiveDepth_usable (blockLen T M) t0 zeta C
      (by omega)).1
  have hσ : 0 < σ := by
    dsimp only [σ]
    apply Real.sqrt_pos.mpr
    positivity
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hscale : σ ≤ 2 * Real.exp 1 * σ := by nlinarith [hσ.le]
  have hbnd := selector_integral_le_of_square_tail μ R b (2 * Real.exp 1 * σ)
    (selector_simpleRegret_integrable t0 zeta C sel m hClass) (by positivity) ?_
  · change (∫ w, R w ∂μ) ≤ 2 * b + 8 * Real.exp 1 * σ
    nlinarith [hbnd]
  · intro x hx
    have hxpos : 0 < x := (by positivity : 0 < 2 * Real.exp 1 * σ).trans_le hx
    have ht := selector_block_regret_tail_actual_sd t0 zeta C m hClass hn
      x hxpos (hscale.trans hx)
    apply (ht.trans (min_le_right _ _)).trans
    exact selector_median_tail_square_envelope M (numBlocks M) σ x
      (by have := m.list_size; omega)
      (by have := selector_numBlocks_ge_three M; omega)
      (selector_numBlocks_log_bounds M m.list_size).1 hσ.le hxpos hx

end CausalSmith.Stat.PomdpPolicyclassRegret
