module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.BlockConstruction
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.LearnerRisk
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.RowInformation
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.TotalVariation

/-! # Score-threshold overlap regret — same-logger lower experiments

The concrete potential-outcome law uses Mathlib measures and four uniform coins.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @env: S6
variable (α γ θ : ℝ) (n : ℕ) (σ : Bool)

/-- Local effect size. -/
noncomputable def hLoc (α γ θ : ℝ) (n : ℕ) : ℝ :=
  (64*(n:ℝ)) ^ (-(1/DExp α γ θ)) -- @realizes hloc((64n)^(-1/D))
/-- Local weak-arm propensity. -/
noncomputable def qLoc (α γ θ : ℝ) (n : ℕ) : ℝ :=
  hLoc α γ θ n ^ betaExp α γ θ -- @realizes qloc(hLoc^beta)
/-- Local block mass. -/
noncomputable def mLoc (α γ θ : ℝ) (n : ℕ) : ℝ :=
  hLoc α γ θ n ^ α / 8 -- @realizes mloc(hLoc^alpha/8)
/-- Shared local logger. -/
noncomputable def localLogger (α γ θ : ℝ) (n : ℕ) : ℝ → ℝ :=
  blockLogger (mLoc α γ θ n) (qLoc α γ θ n)

-- @node: def:local-pair
/-- Small-effect two-point row law, indexed by sign `σ`. -/
noncomputable def localPair (α γ θ : ℝ) (n : ℕ) (σ : Bool) : RowLaw :=
  blockPair (mLoc α γ θ n) (qLoc α γ θ n) (hLoc α γ θ n) σ -- @realizes Plocsigma(two local alternatives); @realizes sigma(Bool signs ±1)

/-- High-effect size. -/
noncomputable def hHi : ℝ := 1/2 -- @realizes hhi(h_hi=1/2)
/-- High-effect weak-arm propensity. -/
noncomputable def qHi (θ : ℝ) (n : ℕ) : ℝ :=
  (64*(n:ℝ)) ^ (-(1/(θ+1))) -- @realizes qhi((64n)^(-1/(theta+1)))
/-- High-effect block mass. -/
noncomputable def mHi (α θ : ℝ) (n : ℕ) : ℝ :=
  min (1/8) ((2:ℝ)^(θ+2-α)) * qHi θ n ^ θ -- @realizes mhi(min(1/8,2^(theta+2-alpha))*qHi^theta)
/-- Shared high-effect logger. -/
noncomputable def highLogger (α θ : ℝ) (n : ℕ) : ℝ → ℝ :=
  blockLogger (mHi α θ n) (qHi θ n)

-- @node: def:high-pair
/-- High-effect same-logger two-point law. -/
noncomputable def highPair (α θ : ℝ) (n : ℕ) (σ : Bool) : RowLaw :=
  blockPair (mHi α θ n) (qHi θ n) hHi σ -- @realizes Phisigma(two high-effect alternatives)

-- @node: highPair_true_canonical
/-- The positive high-effect alternative treats at every score. -/
lemma highPair_true_canonical (α θ : ℝ) (n : ℕ) :
    canonicalPolicy (highPair α θ n true) = (fun _ => true) := by
  funext x
  simp only [canonicalPolicy, highPair, blockPair, blockMeanOne, blockMeanZero,
    hHi, decide_eq_true_eq]
  split_ifs <;> norm_num

-- @node: highPair_false_canonical_off_boundary
/-- The negative alternative agrees with the right threshold away from its cutoff. -/
lemma highPair_false_canonical_off_boundary (α θ : ℝ) (n : ℕ) (x : ℝ)
    (hx : x ≠ mHi α θ n) :
    canonicalPolicy (highPair α θ n false) x = rightThr (mHi α θ n) x := by
  by_cases h : x ≤ mHi α θ n
  · have hlt : x < mHi α θ n := lt_of_le_of_ne h hx
    simp [canonicalPolicy, highPair, blockPair, blockMeanOne, blockMeanZero,
      hHi, rightThr, h, not_le.mpr hlt]
  · have hgt : mHi α θ n < x := lt_of_not_ge h
    simp [canonicalPolicy, highPair, blockPair, blockMeanOne, blockMeanZero,
      rightThr, h, le_of_lt hgt]
    norm_num

/-- The negative high-effect rule is the right threshold modulo its null endpoint. -/
-- @node: highPair_false_canonical_ae
lemma highPair_false_canonical_ae (α θ : ℝ) (n : ℕ) :
    canonicalPolicy (highPair α θ n false) =ᵐ[(highPair α θ n false).PX]
      rightThr (mHi α θ n) := by
  rw [highPair, blockPair_score_uniform]
  have hnull : uniformRandomizer {mHi α θ n} = 0 := by
    apply le_antisymm _ zero_le
    exact (Measure.restrict_le_self _).trans (by simp)
  have hne : ∀ᵐ x ∂uniformRandomizer, x ≠ mHi α θ n := by
    simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using hnull
  filter_upwards [hne] with x hx
  exact highPair_false_canonical_off_boundary α θ n x hx

/-- The high-effect construction has magnitude one half on the scarce block and one elsewhere. -/
-- @node: blockPair_high_magnitude
lemma blockPair_high_magnitude (m q x : ℝ) (σ : Bool) :
    effectMagnitude (blockPair m q hHi σ) x = if x ≤ m then 1/2 else 1 := by
  cases σ <;> simp only [effectMagnitude, blockPair, blockMeanOne, blockMeanZero, hHi]
  all_goals split_ifs <;> norm_num

/-- The weak-arm propensity equals the block propensity when it is at most one half. -/
-- @node: blockPair_overlap
lemma blockPair_overlap (m q x : ℝ) (h : ℝ) (σ : Bool) (hq : q ≤ 1/2) :
    overlap (blockPair m q h σ) x = if x ≤ m then q else 1/2 := by
  unfold overlap blockPair blockLogger
  by_cases hx : x ≤ m
  · simp [hx, min_eq_left (by linarith : q ≤ 1-q)]
  · norm_num [hx]

/-- The scarce score block has its displayed mass under the constructed uniform marginal. -/
-- @node: blockPair_block_mass
lemma blockPair_block_mass (m q h : ℝ) (σ : Bool) (hm : 0 ≤ m) (hm1 : m ≤ 1) :
    (blockPair m q h σ).PX.real {x | x ≤ m} = m := by
  rw [blockPair_score_uniform]
  change (volume.restrict (Set.Icc (0:ℝ) 1)).real (Set.Iic m) = m
  rw [measureReal_restrict_apply measurableSet_Iic]
  have hs : Set.Iic m ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 m := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hxm, hx0, hx1⟩
      exact ⟨hx0, hxm⟩
    · rintro ⟨hx0, hxm⟩
      exact ⟨hxm, hx0, hxm.trans hm1⟩
  rw [hs, Real.volume_real_Icc_of_le hm]
  ring

/-- The small-effect margin condition for the high pair reduces to its block mass. -/
-- @node: blockPair_high_margin
lemma blockPair_high_margin (α m q : ℝ) (σ : Bool)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hmargin : m ≤ Cm*(1/2:ℝ)^α) :
    MarginCondition (blockPair m q hHi σ) α := by
  haveI : IsProbabilityMeasure (blockPair m q hHi σ).PX := by
    rw [blockPair_score_uniform]
    exact uniformRandomizer_probability
  intro u hu hu0
  have huHalf : u ≤ 1/2 := hu0
  by_cases hsmall : u < 1/2
  · have hs : {x | 0 < effectMagnitude (blockPair m q hHi σ) x ∧
        effectMagnitude (blockPair m q hHi σ) x ≤ u} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, blockPair_high_magnitude]
      split_ifs <;> simp <;> linarith
    rw [hs]
    simp only [measureReal_empty]
    unfold Cm
    positivity
  · have heq : u = 1/2 := by linarith
    subst u
    have hs : {x | 0 < effectMagnitude (blockPair m q hHi σ) x ∧
        effectMagnitude (blockPair m q hHi σ) x ≤ 1/2} = {x | x ≤ m} := by
      ext x
      simp only [Set.mem_setOf_eq, blockPair_high_magnitude]
      split_ifs <;> norm_num <;> linarith
    rw [hs, blockPair_block_mass m q hHi σ hm hm1]
    exact hmargin

/-- The global joint envelope follows from the retuned block coefficient and the off-block probability bound. -/
-- @node: blockPair_high_envelope
lemma blockPair_high_envelope (α γ θ m q : ℝ) (σ : Bool)
    (hα : 0 < α) (hθ : 0 < θ) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hq : 0 < q) (hqhalf : q ≤ 1/2)
    (hmass : m ≤ Co θ*(1/2:ℝ)^α*q^θ)
    (hoff : 1 ≤ Co θ*(1/2:ℝ)^θ) :
    GlobalJointEnvelope (blockPair m q hHi σ) α γ θ := by
  haveI : IsProbabilityMeasure (blockPair m q hHi σ).PX := by
    rw [blockPair_score_uniform]
    exact uniformRandomizer_probability
  intro u v hu hu2 hv hvwindow
  let E := {x | overlap (blockPair m q hHi σ) x ≤ v ∧
    0 < effectMagnitude (blockPair m q hHi σ) x ∧
    effectMagnitude (blockPair m q hHi σ) x ≤ u}
  change (blockPair m q hHi σ).PX.real E ≤ _
  by_cases hoffEvent : ∃ x ∈ E, m < x
  · obtain ⟨x, hx, hmx⟩ := hoffEvent
    have hx' := hx
    change overlap (blockPair m q hHi σ) x ≤ v ∧
      0 < effectMagnitude (blockPair m q hHi σ) x ∧
      effectMagnitude (blockPair m q hHi σ) x ≤ u at hx'
    simp only [blockPair_overlap m q x hHi σ hqhalf,
      blockPair_high_magnitude m q x σ, if_neg (not_le.mpr hmx)] at hx'
    have hU : 1 ≤ u^α := Real.one_le_rpow hx'.2.2 hα.le
    have hV : (1/2:ℝ)^θ ≤ v^θ :=
      Real.rpow_le_rpow (by norm_num) hx'.1 hθ.le
    calc
      (blockPair m q hHi σ).PX.real E ≤ 1 := measureReal_le_one
      _ ≤ Co θ*(1/2:ℝ)^θ := hoff
      _ ≤ Co θ*u^α*v^θ := by
        have hc : 0 ≤ Co θ := by unfold Co; positivity
        nlinarith [mul_le_mul_of_nonneg_left hV hc,
          mul_le_mul_of_nonneg_left hU (mul_nonneg hc (Real.rpow_nonneg hv.le θ))]
  · have hsub : E ⊆ {x | x ≤ m} := by
      intro x hx
      by_contra hn
      exact hoffEvent ⟨x, hx, lt_of_not_ge hn⟩
    by_cases hne : E.Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxm : x ≤ m := hsub hx
      have hx' := hx
      change overlap (blockPair m q hHi σ) x ≤ v ∧
        0 < effectMagnitude (blockPair m q hHi σ) x ∧
        effectMagnitude (blockPair m q hHi σ) x ≤ u at hx'
      simp only [blockPair_overlap m q x hHi σ hqhalf,
        blockPair_high_magnitude m q x σ, if_pos hxm] at hx'
      have hU := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1/2) hx'.2.2 hα.le
      have hV := Real.rpow_le_rpow hq.le hx'.1 hθ.le
      calc
        (blockPair m q hHi σ).PX.real E ≤
            (blockPair m q hHi σ).PX.real {x | x ≤ m} := measureReal_mono hsub
        _ = m := blockPair_block_mass m q hHi σ hm hm1
        _ ≤ Co θ*(1/2:ℝ)^α*q^θ := hmass
        _ ≤ Co θ*u^α*v^θ := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hU (by unfold Co; positivity)
          · exact hV
          · positivity
          · unfold Co
            positivity
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp only [measureReal_empty]
      unfold Co
      positivity

/-- The retuned coefficient equals the envelope constant at effect magnitude one half. -/
-- @node: highPair_coefficient_identity
lemma highPair_coefficient_identity (α θ : ℝ) :
    Co θ*(1/2:ℝ)^α = (2:ℝ)^(θ+2-α) := by
  have hh : (1/2:ℝ)^α = (2:ℝ)^(-α) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
  rw [hh, Co, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1

/-- The public envelope constant pays for the entire off-block region. -/
-- @node: highPair_off_block_budget
lemma highPair_off_block_budget (θ : ℝ) :
    Co θ*(1/2:ℝ)^θ = 4 := by
  rw [highPair_coefficient_identity θ θ]
  norm_num

/-- The retuned high-effect pair satisfies the global joint envelope whenever its scales are legal. -/
-- @node: highPair_envelope
lemma highPair_envelope (α γ θ : ℝ) (n : ℕ) (σ : Bool)
    (hα : 0 < α) (hθ : 0 < θ)
    (hq : 0 < qHi θ n) (hqhalf : qHi θ n ≤ 1/2)
    (hm1 : mHi α θ n ≤ 1) :
    GlobalJointEnvelope (highPair α θ n σ) α γ θ := by
  have hm : 0 ≤ mHi α θ n := by unfold mHi; positivity
  have hmass : mHi α θ n ≤ Co θ*(1/2:ℝ)^α*(qHi θ n)^θ := by
    rw [highPair_coefficient_identity]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _)
      (Real.rpow_nonneg hq.le _)
  exact blockPair_high_envelope α γ θ (mHi α θ n) (qHi θ n) σ
    hα hθ hm hm1 hq hqhalf hmass (by rw [highPair_off_block_budget]; norm_num)

/-- The supplied high-effect logger is strictly between zero and one at every score. -/
-- @node: highPair_logger_positive
lemma highPair_logger_positive (α θ : ℝ) (n : ℕ)
    (hq : 0 < qHi θ n) (hqhalf : qHi θ n ≤ 1/2) (x : ℝ) :
    0 < highLogger α θ n x ∧ highLogger α θ n x < 1 := by
  unfold highLogger blockLogger
  split_ifs <;> constructor <;> linarith

/-- The high pair satisfies the margin condition once its vanishing block mass is below the public margin budget. -/
-- @node: highPair_margin
lemma highPair_margin (α θ : ℝ) (n : ℕ) (σ : Bool)
    (hm1 : mHi α θ n ≤ 1)
    (hmargin : mHi α θ n ≤ Cm*(1/2:ℝ)^α) :
    MarginCondition (highPair α θ n σ) α := by
  apply blockPair_high_margin α (mHi α θ n) (qHi θ n) σ
  · unfold mHi qHi
    positivity
  · exact hm1
  · exact hmargin

/-- Both high-effect signs obey the effect bound required by law-class membership. -/
-- @node: highPair_effect_bound
lemma highPair_effect_bound (α θ : ℝ) (n : ℕ) (σ : Bool) :
    ∀ᵐ x ∂(highPair α θ n σ).PX, |(highPair α θ n σ).tau x| ≤ 2 := by
  apply Filter.Eventually.of_forall
  intro x
  change effectMagnitude (blockPair (mHi α θ n) (qHi θ n) hHi σ) x ≤ 2
  rw [blockPair_high_magnitude]
  split_ifs <;> norm_num

/-- Strict positivity of the shared logger gives the high-pair positivity condition. -/
-- @node: highPair_positivity
lemma highPair_positivity (α θ : ℝ) (n : ℕ) (σ : Bool)
    (hq : 0 < qHi θ n) (hqhalf : qHi θ n ≤ 1/2) :
    Positivity (highPair α θ n σ) (highLogger α θ n) := by
  exact Filter.Eventually.of_forall (highPair_logger_positive α θ n hq hqhalf)

/-- The high-pair propensity vanishes at the polynomial scale in the roadmap. -/
-- @node: qHi_tendsto_zero
lemma qHi_tendsto_zero (θ : ℝ) (hθ : 0 < θ) :
    Filter.Tendsto (qHi θ) Filter.atTop (nhds 0) := by
  have hn : Filter.Tendsto (fun n : ℕ => (64:ℝ)*(n:ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop (by positivity : 0 < 1/(θ+1))).comp hn

/-- The retuned block mass also vanishes for every positive high-tail exponent. -/
-- @node: mHi_tendsto_zero
lemma mHi_tendsto_zero (α θ : ℝ) (hθ : 0 < θ) :
    Filter.Tendsto (mHi α θ) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun n => min (1/8) ((2:ℝ)^(θ+2-α)) *
    (qHi θ n)^θ) Filter.atTop (nhds 0)
  simpa only [mul_zero] using
    ((qHi_tendsto_zero θ hθ).rpow_const_nhds_zero hθ).const_mul
      (min (1/8) ((2:ℝ)^(θ+2-α)))

/-- At positive sample sizes both high-pair scales are strictly positive. -/
-- @node: highPair_scales_positive
lemma highPair_scales_positive (α θ : ℝ) (n : ℕ) (hn : 0 < n) :
    0 < qHi θ n ∧ 0 < mHi α θ n := by
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hq : 0 < qHi θ n := by unfold qHi; positivity
  exact ⟨hq, mul_pos (lt_min (by norm_num) (by positivity))
    (Real.rpow_pos_of_pos hq _)⟩

/-- A common sample-size cutoff makes the propensity, block mass, and margin budget legal. -/
-- @node: highPair_scales_eventually
lemma highPair_scales_eventually (α θ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < n ∧ 0 < qHi θ n ∧ qHi θ n ≤ 1/2 ∧
      0 < mHi α θ n ∧ mHi α θ n ≤ 1 ∧ mHi α θ n ≤ Cm*(1/2:ℝ)^α := by
  have hbudget : (0:ℝ) < Cm*(1/2:ℝ)^α := by unfold Cm; positivity
  have hq := (qHi_tendsto_zero θ hθ).eventually_lt_const (by norm_num : (0:ℝ) < 1/2)
  have hm := (mHi_tendsto_zero α θ hθ).eventually_lt_const (by norm_num : (0:ℝ) < 1)
  have hb := (mHi_tendsto_zero α θ hθ).eventually_lt_const hbudget
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      0 < n ∧ 0 < qHi θ n ∧ qHi θ n ≤ 1/2 ∧
      0 < mHi α θ n ∧ mHi α θ n ≤ 1 ∧ mHi α θ n ≤ Cm*(1/2:ℝ)^α := by
    filter_upwards [Filter.eventually_ge_atTop 1, hq, hm, hb] with n hn hqn hmn hbn
    have hn0 : 0 < n := by omega
    obtain ⟨hpq, hpm⟩ := highPair_scales_positive α θ n hn0
    exact ⟨hn0, hpq, hqn.le, hpm, hmn.le, hbn.le⟩
  exact Filter.eventually_atTop.mp hall

/-- Both signs have a canonical threshold policy with the score-null endpoint convention. -/
-- @node: highPair_canonical_threshold
lemma highPair_canonical_threshold (α θ : ℝ) (n : ℕ) (σ : Bool)
    (hm : 0 ≤ mHi α θ n) (hm1 : mHi α θ n ≤ 1) :
    CanonicalThreshold (highPair α θ n σ) := by
  cases σ
  · refine ⟨rightThr (mHi α θ n), ?_, (highPair_false_canonical_ae α θ n).symm⟩
    exact Or.inr (Or.inr (Or.inr ⟨mHi α θ n, ⟨hm, hm1⟩, fun _ _ => rfl⟩))
  · refine ⟨fun _ => true, Or.inr (Or.inl (fun _ _ => rfl)), ?_⟩
    rw [highPair_true_canonical]

/-- The constructed conditional effect is a measurable step function. -/
@[fun_prop]
-- @node: blockPair_tau_measurable
lemma blockPair_tau_measurable (m q h : ℝ) (σ : Bool) :
    Measurable (blockPair m q h σ).tau := by
  change Measurable (fun x => blockMeanOne m h σ x - blockMeanZero m x)
  fun_prop

/-- The full-row score is supported on the same public interval as its marginal. -/
-- @node: blockPair_full_score_support
lemma blockPair_full_score_support (m q h : ℝ) (σ : Bool) :
    (blockPair m q h σ).full {o | o.X ∉ Set.Icc (0:ℝ) 1} = 0 := by
  have hs := (blockPair_score_borel m q h σ).2
  have hX : Measurable FullRow.X := (comap_measurable _).fst
  rw [RowLaw.PX, Measure.map_apply hX measurableSet_Icc.compl] at hs
  exact hs

/-- Consistency and bounded potentials put the observed outcome in the public range. -/
-- @node: blockPair_observed_support
lemma blockPair_observed_support (m q h : ℝ) (σ : Bool) :
    (blockPair m q h σ).full {o | o.Y ∉ Set.Icc (-1:ℝ) 1} = 0 := by
  apply ae_iff.mp
  filter_upwards [blockPair_consistency m q h σ, blockPair_bounded_potentials m q h σ]
    with o hc hb
  rw [hc]
  cases o.A <;> simp_all

-- @node: lem:high-membership
/-- High alternatives satisfy every class condition and share their logger. -/
lemma highPair_mem_lawClass (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ σ : Bool,
      LawClass α γ θ n (highPair α θ n σ) (highLogger α θ n) ∧
      (σ = true → canonicalPolicy (highPair α θ n σ) = (fun _ => true)) ∧
      (σ = false → canonicalPolicy (highPair α θ n σ) =ᵐ[(highPair α θ n σ).PX]
        rightThr (mHi α θ n)) := by
  have hmembership : ∃ N : ℕ, ∀ n ≥ N, ∀ σ : Bool,
      LawClass α γ θ n (highPair α θ n σ) (highLogger α θ n) := by
    obtain ⟨N, hN⟩ := highPair_scales_eventually α θ hθ
    refine ⟨N, ?_⟩
    intro n hn σ
    obtain ⟨hn0, hq, hqhalf, hm, hm1, hmargin⟩ := hN n hn
    refine {
      exponents := ⟨hα, hγ, hθ⟩
      sampleSize := hn0
      wf := ?_
      iid := blockPair_iid _ _ _ σ n
      score := blockPair_score_borel _ _ _ σ
      consistent := blockPair_consistency _ _ _ σ
      exchangeable := ?_
      bounded := blockPair_bounded_potentials _ _ _ σ
      effectBound := highPair_effect_bound α θ n σ
      known := fun _ _ => rfl
      loggerSpace := fun x _ => highPair_logger_positive α θ n hq hqhalf x
      positive := highPair_positivity α θ n σ hq hqhalf
      margin := highPair_margin α θ n σ hm1 hmargin
      envelope := highPair_envelope α γ θ n σ hα hθ hq hqhalf hm1
      canonical := highPair_canonical_threshold α θ n σ hm.le hm1 }
    · refine ⟨blockPair_probability _ _ _ σ,
        blockPair_full_score_support _ _ _ σ,
        blockPair_observed_support _ _ _ σ, ?_, ?_, ?_, ?_⟩
      · exact (blockLogger_measurable _ _).comp measurable_subtype_coe
      · fun_prop
      · exact blockPair_logger_identity _ _ _ σ hq.le (by linarith)
      · exact blockPair_effect_identity _ _ _ σ (by norm_num [hHi]) (by norm_num [hHi])
    · exact blockPair_exchangeability _ _ _ σ hq.le (by linarith)
  obtain ⟨N, hN⟩ := hmembership
  refine ⟨N, ?_⟩
  intro n hn σ
  refine ⟨hN n hn σ, ?_, ?_⟩
  · intro hσ
    subst σ
    exact highPair_true_canonical α θ n
  · intro hσ
    subst σ
    exact highPair_false_canonical_ae α θ n

/-- The high-pair tuning fixes the propensity power at the inverse sample scale. -/
-- @node: highPair_propensity_power
lemma highPair_propensity_power (θ : ℝ) (n : ℕ)
    (hθ : 0 < θ) (hn : 0 < n) :
    (qHi θ n)^(θ+1) = (64*(n:ℝ))⁻¹ := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  rw [qHi, ← Real.rpow_mul (by positivity)]
  have he : -(1/(θ+1))*(θ+1) = -1 := by
    have hd : θ+1 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  rw [he, Real.rpow_neg_one]

/-- The product information budget equals the public block coefficient divided by 32. -/
-- @node: highPair_information_scale
lemma highPair_information_scale (α θ : ℝ) (n : ℕ)
    (hθ : 0 < θ) (hn : 0 < n) :
    8*(n:ℝ)*mHi α θ n*qHi θ n*hHi^2 =
      min (1/8) ((2:ℝ)^(θ+2-α))/32 := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hq := (highPair_scales_positive α θ n hn).1
  calc
    _ = 2 * min (1/8) ((2:ℝ)^(θ+2-α)) *
        (n:ℝ) * (qHi θ n)^(θ+1) := by
      rw [mHi, hHi, Real.rpow_add hq, Real.rpow_one]
      ring
    _ = _ := by
      rw [highPair_propensity_power θ n hθ hn]
      field_simp
      <;> ring

/-- The retuned high-pair information budget is uniformly at most one 256th. -/
-- @node: highPair_information_budget
lemma highPair_information_budget (α θ : ℝ) (n : ℕ)
    (hθ : 0 < θ) (hn : 0 < n) :
    8*(n:ℝ)*mHi α θ n*qHi θ n*hHi^2 ≤ 1/256 := by
  rw [highPair_information_scale α θ n hθ hn]
  exact (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans
    (by norm_num)

/-- The high-pair block separation is exactly a positive coefficient times the
high-effect risk power, as in the final step of the two-point roadmap. -/
-- @node: highPair_risk_scale
lemma highPair_risk_scale (α θ : ℝ) (n : ℕ) (hn : 0 < n) :
    (3/8:ℝ)*mHi α θ n*hHi =
      (3 * min (1/8) ((2:ℝ)^(θ+2-α)) / 16 *
        (64:ℝ)^(-(θ/(θ+1)))) * (n:ℝ)^(-(θ/(θ+1))) := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hp : (qHi θ n)^θ =
      (64:ℝ)^(-(θ/(θ+1))) * (n:ℝ)^(-(θ/(θ+1))) := by
    rw [qHi, ← Real.rpow_mul (by positivity)]
    have he : -(1/(θ+1))*θ = -(θ/(θ+1)) := by ring
    rw [he, Real.mul_rpow (by norm_num) hn'.le]
  rw [mHi, hHi, hp]
  ring

/-- The two high-effect disagreement losses sum to the block effect, and
all losses outside the block are nonnegative, for every binary policy. -/
-- @node: highPair_disagreement_sum_bound
lemma highPair_disagreement_sum_bound (α θ : ℝ) (n : ℕ)
    (φ : ℝ → Bool) (x : ℝ) :
    hHi * (if x ≤ mHi α θ n then (1:ℝ) else 0) ≤
      effectMagnitude (highPair α θ n true) x *
        (if φ x = canonicalPolicy (highPair α θ n true) x then (0:ℝ) else 1) +
      effectMagnitude (highPair α θ n false) x *
        (if φ x = canonicalPolicy (highPair α θ n false) x then (0:ℝ) else 1) := by
  by_cases hx : x ≤ mHi α θ n
  · cases hp : φ x <;>
      norm_num [highPair, blockPair, effectMagnitude, canonicalPolicy,
        blockMeanOne, blockMeanZero, hHi, hx, hp]
  · have hnonneg (σ : Bool) : 0 ≤
        effectMagnitude (highPair α θ n σ) x *
          (if φ x = canonicalPolicy (highPair α θ n σ) x then (0:ℝ) else 1) := by
      unfold effectMagnitude
      positivity
    simpa [hx] using add_nonneg (hnonneg true) (hnonneg false)

/-- The welfare identity turns the pointwise high-pair separation into a
regret-sum lower bound for any Borel binary policy, including nonthreshold policies. -/
-- @node: highPair_policy_regret_sum
lemma highPair_policy_regret_sum (α γ θ : ℝ) (n : ℕ)
    (hplus : LawClass α γ θ n (highPair α θ n true) (highLogger α θ n))
    (hminus : LawClass α γ θ n (highPair α θ n false) (highLogger α θ n))
    (hm : 0 ≤ mHi α θ n) (hm1 : mHi α θ n ≤ 1)
    (φ : ℝ → Bool) (hφ : φ ∈ binaryPolicyClass) :
    mHi α θ n * hHi ≤ rawRegret (highPair α θ n true) φ +
      rawRegret (highPair α θ n false) φ := by
  have hp := regret_eq_effect_disagreement α γ θ n _ _ hplus φ hφ
  have hn := regret_eq_effect_disagreement α γ θ n _ _ hminus φ hφ
  simp only [regret, RowLaw.toWellFormedLaw] at hp hn
  rw [hp, hn]
  have hi (σ : Bool) (hσ : LawClass α γ θ n
      (highPair α θ n σ) (highLogger α θ n)) :
      Integrable (fun x => effectMagnitude (highPair α θ n σ) x *
        (if φ x = canonicalPolicy (highPair α θ n σ) x then (0:ℝ) else 1))
        uniformRandomizer := by
    have h := effectDisagreement_integrable α γ θ n _ _ hσ φ hφ
    simpa only [highPair, blockPair_score_uniform] using h
  have hPX (σ : Bool) : (highPair α θ n σ).PX = uniformRandomizer :=
    blockPair_score_uniform _ _ _ _
  rw [hPX true, hPX false]
  rw [← integral_add (hi true hplus) (hi false hminus)]
  haveI := uniformRandomizer_probability
  have hb : Integrable (fun x => hHi *
      (if x ≤ mHi α θ n then (1:ℝ) else 0)) uniformRandomizer := by
    have heq : (fun x => hHi * (if x ≤ mHi α θ n then (1:ℝ) else 0)) =
        (Set.Iic (mHi α θ n)).indicator (fun _ => hHi) := by
      ext x
      by_cases hx : x ≤ mHi α θ n <;> simp [Set.indicator, hx]
    rw [heq]
    exact (integrable_const hHi).indicator measurableSet_Iic
  have hbound := integral_mono hb ((hi true hplus).add (hi false hminus))
    (highPair_disagreement_sum_bound α θ n φ)
  have hmass : (∫ x, hHi * (if x ≤ mHi α θ n then (1:ℝ) else 0)
      ∂uniformRandomizer) = mHi α θ n * hHi := by
    rw [integral_const_mul, uniformRandomizer_coin_integral _ hm hm1]
    ring
  rw [hmass] at hbound
  exact hbound

/-- The policy separation and TV comparison give the risk floor for every
jointly Borel family, under arbitrary parameter laws with small testing distance. -/
-- @node: highPair_family_risk_floor
lemma highPair_family_risk_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (α γ θ : ℝ) (n : ℕ)
    (hplus : LawClass α γ θ n (highPair α θ n true) (highLogger α θ n))
    (hminus : LawClass α γ θ n (highPair α θ n false) (highLogger α θ n))
    (hm : 0 < mHi α θ n) (hm1 : mHi α θ n ≤ 1)
    (ψ : Ω → ℝ → Bool)
    (hψ : Measurable (fun z : Ω × Set.Icc (0:ℝ) 1 => ψ z.1 z.2))
    (htv : Causalean.Stat.tvDist μ ν < 1/4) :
    (3/8:ℝ)*mHi α θ n*hHi ≤
      max (∫ w, rawRegret (highPair α θ n true) (ψ w) ∂μ)
        (∫ w, rawRegret (highPair α θ n false) (ψ w) ∂ν) := by
  have hp := rawRegret_family_integrable μ α γ θ n _ _ hplus ψ hψ
  have hn := rawRegret_family_integrable ν α γ θ n _ _ hminus ψ hψ
  have hmn := rawRegret_family_measurable α γ θ n _ _ hminus ψ hψ
  have hsep (w : Ω) : mHi α θ n*hHi ≤
      rawRegret (highPair α θ n true) (ψ w) +
      rawRegret (highPair α θ n false) (ψ w) := by
    apply highPair_policy_regret_sum α γ θ n hplus hminus hm.le hm1
    exact hψ.comp (measurable_const.prodMk measurable_id)
  have hK : 0 < mHi α θ n*hHi := mul_pos hm (by norm_num [hHi])
  simpa only [mul_assoc] using lowerInformation_separated_loss_floor μ ν _ _ hp hn hmn
    (fun w => (rawRegret_bounds α γ θ n _ _ hplus (ψ w)).1)
    (fun w => (rawRegret_bounds α γ θ n _ _ hminus (ψ w)).1)
    (mHi α θ n*hHi) hK hsep htv

/-- Supported-domain joint measurability suffices for the all-procedure
high-pair risk floor; no measurability on invalid data is imposed. -/
-- @node: highPair_learner_risk_floor
lemma highPair_learner_risk_floor (α γ θ : ℝ) (n : ℕ)
    (hplus : LawClass α γ θ n (highPair α θ n true) (highLogger α θ n))
    (hminus : LawClass α γ θ n (highPair α θ n false) (highLogger α θ n))
    (hm : 0 < mHi α θ n) (hm1 : mHi α θ n ≤ 1)
    (htv : Causalean.Stat.tvDist (experiment (highPair α θ n true) n)
      (experiment (highPair α θ n false) n) < 1/4)
    (Φ : Learner n) (hΦ : LearnerClass n Φ) :
    (3/8:ℝ)*mHi α θ n*hHi ≤
      max (∫ du, rawRegret (highPair α θ n true)
          (fun x => Φ (highLogger α θ n) du.1 du.2 x)
          ∂experiment (highPair α θ n true) n)
        (∫ du, rawRegret (highPair α θ n false)
          (fun x => Φ (highLogger α θ n) du.1 du.2 x)
          ∂experiment (highPair α θ n false) n) := by
  have he : Measurable (fun x : Set.Icc (0:ℝ) 1 => highLogger α θ n x) :=
    (blockLogger_measurable _ _).comp measurable_subtype_coe
  obtain ⟨ψ, hψ, hvalid⟩ := learner_family_representative n (highLogger α θ n)
    he hplus.loggerSpace Φ hΦ
  have hreg (σ : Bool)
      (hσ : LawClass α γ θ n (highPair α θ n σ) (highLogger α θ n)) :
      (∫ du, rawRegret (highPair α θ n σ) (ψ du)
        ∂experiment (highPair α θ n σ) n) =
      ∫ du, rawRegret (highPair α θ n σ)
        (fun x => Φ (highLogger α θ n) du.1 du.2 x)
        ∂experiment (highPair α θ n σ) n := by
    apply integral_congr_ae
    filter_upwards [learner_input_support_ae α γ θ n _ _ hσ] with du hdu
    exact rawRegret_eq_of_eqOn_score α γ θ n _ _ hσ _ _
      (hvalid du.1 du.2 hdu.1 hdu.2)
  haveI := experiment_isProbability _ n hplus.wf
  haveI := experiment_isProbability _ n hminus.wf
  have hb := highPair_family_risk_floor _ _ α γ θ n hplus hminus hm hm1 ψ hψ htv
  rw [hreg true hplus, hreg false hminus] at hb
  exact hb

-- @node: lem:high-information-all-procedure
/-- χ²/TV separation and the risk floor for every fixed-logger randomized learner. -/
lemma high_information_all_procedure (α γ θ : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        Causalean.Stat.chiSqDiv (highPair α θ n true).obsLaw
          (highPair α θ n false).obsLaw
          ≤ 8*mHi α θ n*qHi θ n*hHi^2 ∧
        Causalean.Stat.tvDist (experiment (highPair α θ n true) n)
          (experiment (highPair α θ n false) n) =
          Causalean.Stat.tvDist (sampleLaw (highPair α θ n true) n)
            (sampleLaw (highPair α θ n false) n) ∧
        Causalean.Stat.tvDist (experiment (highPair α θ n true) n)
          (experiment (highPair α θ n false) n) < 1/4 ∧
        (∀ Φ : Learner n, LearnerClass n Φ →
          max (∫ du, rawRegret (highPair α θ n true)
                (fun x => Φ (highLogger α θ n) du.1 du.2 x)
                ∂experiment (highPair α θ n true) n)
              (∫ du, rawRegret (highPair α θ n false)
                (fun x => Φ (highLogger α θ n) du.1 du.2 x)
                ∂experiment (highPair α θ n false) n)
            ≥ c1*mHi α θ n*hHi ∧
          c1*mHi α θ n*hHi = c2*(n:ℝ)^(-(θ/(θ+1)))) := by
  refine ⟨3/8, 3 * min (1/8) ((2:ℝ)^(θ+2-α)) / 16 *
    (64:ℝ)^(-(θ/(θ+1))), by norm_num, by positivity, ?_⟩
  have hcontent :
      ∀ᶠ n : ℕ in Filter.atTop,
        Causalean.Stat.chiSqDiv (highPair α θ n true).obsLaw
          (highPair α θ n false).obsLaw
          ≤ 8*mHi α θ n*qHi θ n*hHi^2 ∧
        Causalean.Stat.tvDist (experiment (highPair α θ n true) n)
          (experiment (highPair α θ n false) n) < 1/4 := by
    obtain ⟨N, hmem⟩ := highPair_mem_lawClass α γ θ hα hγ hθ
    obtain ⟨Ns, hs⟩ := highPair_scales_eventually α θ hθ
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_ge_atTop Ns]
      with n hn hns
    obtain ⟨hn0, hq, hqhalf, hm, hm1, hmargin⟩ := hs n hns
    have hrow : Causalean.Stat.chiSqDiv (highPair α θ n true).obsLaw
        (highPair α θ n false).obsLaw ≤ 8*mHi α θ n*qHi θ n*hHi^2 :=
      blockPair_obsLaw_sign_chiSqDiv_bound _ _ _ hm.le hm1 hq.le
        (by linarith) (by norm_num [hHi]) (by norm_num [hHi])
    haveI : IsProbabilityMeasure (highPair α θ n true).obsLaw :=
      blockPair_obsLaw_probability (mHi α θ n) (qHi θ n) hHi true
    haveI : IsProbabilityMeasure (highPair α θ n false).obsLaw :=
      blockPair_obsLaw_probability (mHi α θ n) (qHi θ n) hHi false
    have hb : (n:ℝ) * Causalean.Stat.chiSqDiv (highPair α θ n true).obsLaw
        (highPair α θ n false).obsLaw ≤ 1/256 := by
      calc
        _ ≤ (n:ℝ) * (8*mHi α θ n*qHi θ n*hHi^2) :=
          mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg n)
        _ = 8*(n:ℝ)*mHi α θ n*qHi θ n*hHi^2 := by ring
        _ ≤ _ := highPair_information_budget α θ n hθ hn0
    have hsample := lowerInformation_product_tv_small
      (highPair α θ n true).obsLaw (highPair α θ n false).obsLaw
      (blockPair_obsLaw_sign_absolutelyContinuous _ _ _
        (by norm_num [hHi]) (by norm_num [hHi]))
      (blockPair_obsLaw_sign_sq_integrable _ _ _
        (by norm_num [hHi]) (by norm_num [hHi])) n hb
    refine ⟨hrow, ?_⟩
    rw [lowerInformation_experiment_tv _ _ n (hmem n hn true).1.wf
      (hmem n hn false).1.wf]
    exact hsample
  obtain ⟨N, hmem⟩ := highPair_mem_lawClass α γ θ hα hγ hθ
  obtain ⟨Nscale, hscale⟩ := highPair_scales_eventually α θ hθ
  filter_upwards [hcontent, Filter.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop N, Filter.eventually_ge_atTop Nscale]
      with n hcontent hn hnN hnScale
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have htv := lowerInformation_experiment_tv (highPair α θ n true)
    (highPair α θ n false) n (hmem n hnN true).1.wf (hmem n hnN false).1.wf
  refine ⟨hcontent.1, htv, hcontent.2, ?_⟩
  intro Φ hΦ
  exact ⟨highPair_learner_risk_floor α γ θ n (hmem n hnN true).1
    (hmem n hnN false).1 (hscale n hnScale).2.2.2.1
    (hscale n hnScale).2.2.2.2.1 hcontent.2 Φ hΦ,
    highPair_risk_scale α θ n hn0⟩


end CausalSmith.Stat.ScorethresholdOverlapRegret
