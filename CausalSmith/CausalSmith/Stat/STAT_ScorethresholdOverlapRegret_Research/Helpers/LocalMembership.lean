module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.LowerPairs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Legality of the small-effect alternatives

The local tuning pays for the margin and joint effect-propensity envelope.
The concrete construction supplies the remaining probability and causal clauses.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory

/-- The block's effect magnitude is its positive amplitude; off the block it is one. -/
-- @node: blockPair_local_magnitude
lemma blockPair_local_magnitude (m q h x : ℝ) (σ : Bool) (hh : 0 ≤ h) :
    effectMagnitude (blockPair m q h σ) x = if x ≤ m then h else 1 := by
  cases σ <;> by_cases hx : x ≤ m <;>
    norm_num [effectMagnitude, blockPair, blockMeanOne, blockMeanZero, hx, abs_of_nonneg hh]

/-- Only the small-effect block can enter the public margin window. -/
-- @node: blockPair_local_margin
lemma blockPair_local_margin (α m q h : ℝ) (σ : Bool)
    (hα : 0 < α) (hm : 0 ≤ m) (hm1 : m ≤ 1) (hh : 0 < h)
    (hmass : m ≤ Cm*h^α) : MarginCondition (blockPair m q h σ) α := by
  haveI : IsProbabilityMeasure (blockPair m q h σ).PX := by
    rw [blockPair_score_uniform]
    exact uniformRandomizer_probability
  intro u hu hu0
  have huHalf : u ≤ 1/2 := hu0
  by_cases hsmall : u < h
  · have hs : {x | 0 < effectMagnitude (blockPair m q h σ) x ∧
        effectMagnitude (blockPair m q h σ) x ≤ u} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        blockPair_local_magnitude m q h x σ hh.le]
      split_ifs <;> simp [not_le.mpr hsmall, show ¬(1:ℝ) ≤ u by linarith]
    rw [hs]
    simp only [measureReal_empty]
    unfold Cm
    positivity
  · have hsub : {x | 0 < effectMagnitude (blockPair m q h σ) x ∧
        effectMagnitude (blockPair m q h σ) x ≤ u} ⊆ {x | x ≤ m} := by
      intro x hx
      by_contra hxm
      change ¬x ≤ m at hxm
      change 0 < effectMagnitude (blockPair m q h σ) x ∧
        effectMagnitude (blockPair m q h σ) x ≤ u at hx
      simp only [blockPair_local_magnitude m q h x σ hh.le, if_neg hxm] at hx
      linarith [hx.2]
    calc
      _ ≤ (blockPair m q h σ).PX.real {x | x ≤ m} := measureReal_mono hsub
      _ = m := blockPair_block_mass m q h σ hm hm1
      _ ≤ Cm*h^α := hmass
      _ ≤ Cm*u^α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hh.le (le_of_not_gt hsmall) hα.le) (by norm_num [Cm])

/-- In the admissible propensity window, the local tuning pays the entire block mass. -/
-- @node: localPair_window_budget
lemma localPair_window_budget (α γ θ : ℝ) (n : ℕ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (hh : 0 < hLoc α γ θ n) (u v : ℝ) (hu : 0 < u)
    (hv : 0 < v) (hqv : qLoc α γ θ n ≤ v) (hvwindow : v ≤ u^γ) :
    mLoc α γ θ n ≤ Co θ*u^α*v^θ := by
  have he : betaExp α γ θ * (α/γ+θ) = α := by
    unfold betaExp
    field_simp
  have hp : (qLoc α γ θ n)^(α/γ+θ) = (hLoc α γ θ n)^α := by
    rw [qLoc, ← Real.rpow_mul hh.le, he]
  have hpow : v^(α/γ) ≤ u^α := by
    calc
      _ ≤ (u^γ)^(α/γ) := Real.rpow_le_rpow hv.le hvwindow (by positivity)
      _ = u^α := by
        rw [← Real.rpow_mul hu.le]
        congr 1
        field_simp
  have hblock : (hLoc α γ θ n)^α ≤ u^α*v^θ := by
    calc
      _ = (qLoc α γ θ n)^(α/γ+θ) := hp.symm
      _ ≤ v^(α/γ+θ) := Real.rpow_le_rpow (by unfold qLoc; positivity) hqv
        (by positivity)
      _ = v^(α/γ)*v^θ := Real.rpow_add hv _ _
      _ ≤ u^α*v^θ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hv.le _)
  have hc : 1 ≤ Co θ := by
    unfold Co
    exact Real.one_le_rpow (by norm_num) (by positivity)
  calc
    mLoc α γ θ n ≤ (hLoc α γ θ n)^α := by unfold mLoc; nlinarith [Real.rpow_nonneg hh.le α]
    _ ≤ u^α*v^θ := hblock
    _ ≤ Co θ*u^α*v^θ := by
      nlinarith [mul_le_mul_of_nonneg_right hc
        (mul_nonneg (Real.rpow_nonneg hu.le α) (Real.rpow_nonneg hv.le θ))]

/-- The joint event is either empty, contained in the block, or costs at most total probability. -/
-- @node: localPair_envelope
lemma localPair_envelope (α γ θ : ℝ) (n : ℕ) (σ : Bool)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (hm : 0 ≤ mLoc α γ θ n) (hm1 : mLoc α γ θ n ≤ 1)
    (hq : qLoc α γ θ n ≤ 1/2) (hh : 0 < hLoc α γ θ n) :
    GlobalJointEnvelope (localPair α γ θ n σ) α γ θ := by
  haveI : IsProbabilityMeasure (localPair α γ θ n σ).PX := by
    rw [localPair, blockPair_score_uniform]
    exact uniformRandomizer_probability
  intro u v hu hu2 hv hvwindow
  have hwindow : v ≤ u^γ := by simpa [co] using hvwindow
  let E := {x | overlap (localPair α γ θ n σ) x ≤ v ∧
    0 < effectMagnitude (localPair α γ θ n σ) x ∧
    effectMagnitude (localPair α γ θ n σ) x ≤ u}
  change (localPair α γ θ n σ).PX.real E ≤ _
  by_cases hoff : ∃ x ∈ E, mLoc α γ θ n < x
  · obtain ⟨x, hx, hmx⟩ := hoff
    have hx' := hx
    change overlap (blockPair _ _ _ σ) x ≤ v ∧
      0 < effectMagnitude (blockPair _ _ _ σ) x ∧
      effectMagnitude (blockPair _ _ _ σ) x ≤ u at hx'
    simp only [blockPair_overlap _ _ _ _ σ hq,
      blockPair_local_magnitude _ _ _ _ σ hh.le, if_neg (not_le.mpr hmx)] at hx'
    have hU : 1 ≤ u^α := Real.one_le_rpow hx'.2.2 hα.le
    have hV : (1/2:ℝ)^θ ≤ v^θ := Real.rpow_le_rpow (by norm_num) hx'.1 hθ.le
    have hc : 0 ≤ Co θ := by unfold Co; positivity
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ Co θ*(1/2:ℝ)^θ := by rw [highPair_off_block_budget]; norm_num
      _ ≤ Co θ*u^α*v^θ := by
        nlinarith [mul_le_mul_of_nonneg_left hV hc,
          mul_le_mul_of_nonneg_left hU (mul_nonneg hc (Real.rpow_nonneg hv.le θ))]
  · have hsub : E ⊆ {x | x ≤ mLoc α γ θ n} := by
      intro x hx
      by_contra hn
      exact hoff ⟨x, hx, lt_of_not_ge hn⟩
    by_cases hne : E.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxm : x ≤ mLoc α γ θ n := hsub hx
      have hx' := hx
      change overlap (blockPair _ _ _ σ) x ≤ v ∧
        0 < effectMagnitude (blockPair _ _ _ σ) x ∧
        effectMagnitude (blockPair _ _ _ σ) x ≤ u at hx'
      simp only [blockPair_overlap _ _ _ _ σ hq,
        blockPair_local_magnitude _ _ _ _ σ hh.le, if_pos hxm] at hx'
      calc
        _ ≤ (localPair α γ θ n σ).PX.real {x | x ≤ mLoc α γ θ n} := measureReal_mono hsub
        _ = mLoc α γ θ n := blockPair_block_mass _ _ _ σ hm hm1
        _ ≤ Co θ*u^α*v^θ := localPair_window_budget α γ θ n hα hγ hθ hh u v hu hv hx'.1 hwindow
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp only [measureReal_empty]
      unfold Co
      positivity

/-- Both local canonical policies are thresholds, up to the score-null cutoff endpoint. -/
-- @node: localPair_canonical_threshold
lemma localPair_canonical_threshold (α γ θ : ℝ) (n : ℕ) (σ : Bool)
    (hm : 0 ≤ mLoc α γ θ n) (hm1 : mLoc α γ θ n ≤ 1)
    (hh : 0 < hLoc α γ θ n) : CanonicalThreshold (localPair α γ θ n σ) := by
  cases σ
  · refine ⟨rightThr (mLoc α γ θ n), ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr ⟨_, ⟨hm, hm1⟩, fun _ _ => rfl⟩))
    · rw [localPair, blockPair_score_uniform]
      have hnull : uniformRandomizer {mLoc α γ θ n} = 0 :=
        le_antisymm ((Measure.restrict_le_self _).trans (by simp)) zero_le
      have hne : ∀ᵐ x ∂uniformRandomizer, x ≠ mLoc α γ θ n := by
        simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using hnull
      filter_upwards [hne] with x hx
      by_cases hxm : x ≤ mLoc α γ θ n
      · have hlt : x < mLoc α γ θ n := lt_of_le_of_ne hxm hx
        norm_num [canonicalPolicy, blockPair, blockMeanOne, blockMeanZero,
          rightThr, hxm, not_le.mpr hlt, not_le.mpr (neg_neg_of_pos hh)]
      · norm_num [canonicalPolicy, blockPair, blockMeanOne, blockMeanZero,
          rightThr, hxm, le_of_lt (lt_of_not_ge hxm)]
  · refine ⟨fun _ => true, Or.inr (Or.inl (fun _ _ => rfl)), ?_⟩
    apply Filter.Eventually.of_forall
    intro x
    simp only [canonicalPolicy, localPair, blockPair, blockMeanOne, blockMeanZero,
      ]
    split_ifs <;> norm_num [hh.le]

/-- All local tuning parameters eventually enter the construction's legal window. -/
-- @node: localPair_scales_eventually
lemma localPair_scales_eventually (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < n ∧ (0 < mLoc α γ θ n ∧ mLoc α γ θ n ≤ 1) ∧
      (0 < qLoc α γ θ n ∧ qLoc α γ θ n ≤ 1/2) ∧
      (0 < hLoc α γ θ n ∧ hLoc α γ θ n ≤ 1/2) := by
  have hb : 0 < betaExp α γ θ := by unfold betaExp; positivity
  have hd : 0 < DExp α γ θ := by unfold DExp; positivity
  have ht : Filter.Tendsto (fun n : ℕ => 64*(n:ℝ)) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 64)).2 tendsto_natCast_atTop_atTop
  have hh : Filter.Tendsto (hLoc α γ θ) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < 1/DExp α γ θ)).comp ht
  have hq : Filter.Tendsto (qLoc α γ θ) Filter.atTop (nhds 0) := hh.rpow_const_nhds_zero hb
  have hm : Filter.Tendsto (mLoc α γ θ) Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun n => hLoc α γ θ n ^ α / 8) _ _
    simpa using (hh.rpow_const_nhds_zero hα).div_const 8
  filter_upwards [Filter.eventually_ge_atTop 1,
    hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)),
    hq.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)),
    hm.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn hh hq hm
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  have hhpos : 0 < hLoc α γ θ n := by unfold hLoc; positivity
  exact ⟨hn0, ⟨by unfold mLoc; positivity, hm.le⟩,
    ⟨by unfold qLoc; positivity, hq.le⟩, hhpos, hh.le⟩

/-- Local alternatives satisfy the same triangular class. -/
-- @node: localPair_mem_lawClass
lemma localPair_mem_lawClass (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ σ : Bool,
      LawClass α γ θ n (localPair α γ θ n σ) (localLogger α γ θ n) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (localPair_scales_eventually α γ θ hα hγ hθ)
  refine ⟨N, ?_⟩
  intro n hn σ
  obtain ⟨hn0, ⟨hm, hm1⟩, ⟨hq, hqhalf⟩, ⟨hh, hhhalf⟩⟩ := hN n hn
  have he (x : ℝ) : 0 < localLogger α γ θ n x ∧ localLogger α γ θ n x < 1 := by
    unfold localLogger blockLogger
    split_ifs <;> constructor <;> linarith
  refine {
    exponents := ⟨hα, hγ, hθ⟩
    sampleSize := hn0
    wf := ?_
    iid := blockPair_iid _ _ _ σ n
    score := blockPair_score_borel _ _ _ σ
    consistent := blockPair_consistency _ _ _ σ
    exchangeable := blockPair_exchangeability _ _ _ σ hq.le (by linarith)
    bounded := blockPair_bounded_potentials _ _ _ σ
    effectBound := ?_
    known := fun _ _ => rfl
    loggerSpace := fun x _ => he x
    positive := Filter.Eventually.of_forall he
    margin := blockPair_local_margin _ _ _ _ σ hα hm.le hm1 hh ?_
    envelope := localPair_envelope α γ θ n σ hα hγ hθ hm.le hm1 hqhalf hh
    canonical := localPair_canonical_threshold α γ θ n σ hm.le hm1 hh }
  · refine ⟨blockPair_probability _ _ _ σ,
      blockPair_full_score_support _ _ _ σ,
      blockPair_observed_support _ _ _ σ, ?_, ?_, ?_, ?_⟩
    · exact (blockLogger_measurable _ _).comp measurable_subtype_coe
    · fun_prop
    · exact blockPair_logger_identity _ _ _ σ hq.le (by linarith)
    · exact blockPair_effect_identity _ _ _ σ (by linarith) (by linarith)
  · apply Filter.Eventually.of_forall
    intro x
    change effectMagnitude (blockPair _ _ _ σ) x ≤ 2
    rw [blockPair_local_magnitude _ _ _ _ σ hh.le]
    split_ifs <;> linarith
  · unfold mLoc Cm
    nlinarith [Real.rpow_nonneg hh.le α]

end CausalSmith.Stat.ScorethresholdOverlapRegret
