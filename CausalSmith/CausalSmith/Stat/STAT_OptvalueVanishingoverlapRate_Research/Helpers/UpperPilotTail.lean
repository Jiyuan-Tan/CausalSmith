module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilot
public import Causalean.Stat.Concentration.Poisson.EmpiricalRadius.Product

/-! # Pilot localization and bad-coordinate moments

Roadmap (15)--(16): the actual truncated pilot interval fails only on the
empirical-radius bad event. Marginal Poisson concentration bounds its
probability and its second and fourth deviation-plus-width moments. A union
bound controls failure of the four-coordinate rectangle, including null atoms.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped BigOperators NNReal

/-- The paper's pilot width is exactly the library's empirical Poisson radius. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,m), the [stated conclusion](goal) holds. -/
lemma pilotHalfWidth_eq_empiricalRadius (H : ℝ) (hH : 0 < H)
    (m : ℝ≥0) (L : ℝ) (Np : Fin 4 → ℕ) (j : Fin 4) :
    pilotHalfWidthFormula H hH m L Np j = empiricalRadius H m (L / m) (Np j) := by
  simp only [pilotHalfWidthFormula, pilotCenterFormula, empiricalRadius, mul_div_assoc]

/-- For a nonnegative true atom, truncation at zero does not change the criterion for failure of its pilot interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hq), the [stated conclusion](goal) holds. -/
lemma pilotInterval_failure_iff (H : ℝ) (hH : 0 < H) (m L q : ℝ)
    (hq : 0 ≤ q) (Np : Fin 4 → ℕ) (j : Fin 4) :
    q ∉ Set.Icc (pilotLower H hH m L Np j) (pilotUpperFormula H hH m L Np j) ↔
      pilotHalfWidthFormula H hH m L Np j < |pilotCenterFormula m Np j - q| := by
  have hmem : q ∈ Set.Icc (pilotLower H hH m L Np j)
      (pilotUpperFormula H hH m L Np j) ↔
      |pilotCenterFormula m Np j - q| ≤ pilotHalfWidthFormula H hH m L Np j := by
    simp only [Set.mem_Icc, pilotLower, pilotUpperFormula, max_le_iff, hq, true_and,
      abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  exact hmem.not.trans not_le

-- @node: pilotCoordinate_score_pow_integrable
/-- Every power through four of a coordinate's deviation-plus-width score is integrable under its Poisson law. This derives the regularity needed for (16). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hH,hL,ht), the [stated conclusion](goal) holds. -/
lemma pilotCoordinate_score_pow_integrable (q m : ℝ≥0) (hm : 0 < m)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) (t : ℕ) (ht : t ≤ 4) :
    Integrable (fun w : ℕ =>
      (|(w : ℝ) / m - q| + empiricalRadius H m (L / m) w) ^ t)
      (poissonMeasure (m * q)) := by
  have hraw := integrable_score_pow (m * q) hL ht
  have hH0 : 0 ≤ H := universalH_pos.le.trans hH
  apply (hraw.const_mul ((H / universalH / (m : ℝ)) ^ t)).mono'
    (Measurable.of_discrete.aestronglyMeasurable)
  apply ae_of_all
  intro w
  have hs := empiricalRadius_score_le_raw q m hm H L hH hL w
  have hscore0 : 0 ≤ |(w : ℝ) / m - q| + empiricalRadius H m (L / m) w := by
    unfold empiricalRadius
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hscore0 t)]
  have hp := pow_le_pow_left₀ hscore0 hs t
  calc
    _ ≤ (H / universalH * (score universalH L (m * q) w / (m : ℝ))) ^ t := hp
    _ = _ := by rw [mul_pow, div_pow, div_pow]; ring

/-- Roadmap (16), for moment orders two and four, on the actual coordinate failure event. The larger library bad event also controls the width score; no tail or integrability premise is added. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,ht), the [stated conclusion](goal) holds. -/
lemma pilotInterval_bad_moment_le (q m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (j : Fin 4) (t : ℕ) (ht : t = 2 ∨ t = 4) :
    (∫ w : ℕ, if (q : ℝ) ∉ Set.Icc
        (pilotLower H hHpos m L (fun _ => w) j)
        (pilotUpperFormula H hHpos m L (fun _ => w) j) then
      (|pilotCenterFormula m (fun _ => w) j - q| +
        pilotHalfWidthFormula H hHpos m L (fun _ => w) j) ^ t else 0
      ∂poissonMeasure (m * q)) ≤
      (H / universalH) ^ t * scalarBadMomentConstant t * Real.exp (-20 * L) *
        (Real.sqrt ((q : ℝ) * L / m) + L / m) ^ t := by
  classical
  let B : Set ℕ := {w | normalizedDeviation m q w >
    empiricalRadius H m (L / m) w / 4}
  have ht4 : t ≤ 4 := by rcases ht with rfl | rfl <;> omega
  have hi := (pilotCoordinate_score_pow_integrable q m hm H L hH hL t ht4).indicator
    (show MeasurableSet B from Set.to_countable _ |>.measurableSet)
  have hmono : (∫ w : ℕ, if (q : ℝ) ∉ Set.Icc
        (pilotLower H hHpos m L (fun _ => w) j)
        (pilotUpperFormula H hHpos m L (fun _ => w) j) then
      (|pilotCenterFormula m (fun _ => w) j - q| +
        pilotHalfWidthFormula H hHpos m L (fun _ => w) j) ^ t else 0
      ∂poissonMeasure (m * q)) ≤
      ∫ w : ℕ, B.indicator (fun w =>
        (normalizedDeviation m q w + empiricalRadius H m (L / m) w) ^ t) w
        ∂poissonMeasure (m * q) := by
    apply integral_mono_of_nonneg (ae_of_all _ fun w => by
      change (0 : ℝ) ≤ _
      split_ifs
      · exact le_rfl
      · apply pow_nonneg
        unfold pilotHalfWidthFormula
        positivity) hi
    apply ae_of_all
    intro w
    have hwidth0 : 0 ≤ empiricalRadius H m (L / m) w := by
      unfold empiricalRadius
      positivity
    by_cases hw : (q : ℝ) ∈ Set.Icc
        (pilotLower H hHpos m L (fun _ => w) j)
        (pilotUpperFormula H hHpos m L (fun _ => w) j)
    · simp only [if_neg (not_not.mpr hw)]
      by_cases hb : w ∈ B
      · rw [Set.indicator_of_mem hb]
        apply pow_nonneg
        exact add_nonneg (abs_nonneg _) hwidth0
      · rw [Set.indicator_of_notMem hb]
    · have hfail := (pilotInterval_failure_iff H hHpos m L q q.coe_nonneg
        (fun _ => w) j).mp hw
      rw [pilotHalfWidth_eq_empiricalRadius] at hfail
      have hb : w ∈ B := by
        change empiricalRadius H m (L / m) w / 4 < |(w : ℝ) / m - q|
        exact lt_of_le_of_lt (by linarith) hfail
      simp only [if_pos hw, Set.indicator_of_mem hb, pilotCenterFormula,
        pilotHalfWidth_eq_empiricalRadius]
      exact le_rfl
  apply hmono.trans
  change (∫ w : ℕ, (if normalizedDeviation m q w >
      empiricalRadius H m (L / m) w / 4 then
      (normalizedDeviation m q w + empiricalRadius H m (L / m) w) ^ t else 0)
      ∂poissonMeasure (m * q)) ≤ _
  rcases ht with rfl | rfl
  · exact poisson_empiricalRadius_bad_second_moment q m hm H L hH hL
  · exact poisson_empiricalRadius_bad_fourth_moment q m hm H L hH hL

/-- The marginal moment estimate (16) transports to the actual random pilot counts by their Poisson laws. Independence is unnecessary for this step. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hlaw,ht), the [stated conclusion](goal) holds. -/
lemma pilotCoordinate_bad_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0)
    (m : ℝ≥0) (hm : 0 < m) (H : ℝ) (hHpos : 0 < H) (L : ℝ)
    (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (j : Fin 4) (t : ℕ) (ht : t = 2 ∨ t = 4) :
    (∫ ω, if (q j : ℝ) ∉ Set.Icc
        (pilotLower H hHpos m L (fun i => W i ω) j)
        (pilotUpperFormula H hHpos m L (fun i => W i ω) j) then
      (|pilotCenterFormula m (fun i => W i ω) j - q j| +
        pilotHalfWidthFormula H hHpos m L (fun i => W i ω) j) ^ t else 0 ∂μ) ≤
      (H / universalH) ^ t * scalarBadMomentConstant t * Real.exp (-20 * L) *
        (Real.sqrt ((q j : ℝ) * L / m) + L / m) ^ t := by
  classical
  let f : ℕ → ℝ := fun w => if (q j : ℝ) ∉ Set.Icc
      (pilotLower H hHpos m L (fun _ => w) j)
      (pilotUpperFormula H hHpos m L (fun _ => w) j) then
    (|pilotCenterFormula m (fun _ => w) j - q j| +
      pilotHalfWidthFormula H hHpos m L (fun _ => w) j) ^ t else 0
  have he := (hlaw j).integral_comp
    (show AEStronglyMeasurable f (poissonMeasure (m * q j)) from
      Measurable.of_discrete.aestronglyMeasurable)
  simp only [Function.comp_def] at he
  change (∫ ω, f (W j ω) ∂μ) ≤ _
  rw [he]
  exact pilotInterval_bad_moment_le (q j) m hm H hHpos L hH hL j t ht

/-- The full four-coordinate localization rectangle fails with probability at most eight times the exponential scalar tail (15). Only marginal laws are used, so no joint independence or positive cell mass is assumed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0)
    (m : ℝ≥0) (hm : 0 < m) (H : ℝ) (hHpos : 0 < H) (L : ℝ)
    (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ) :
    μ {ω | (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω))} ≤
      ENNReal.ofReal (8 * Real.exp (-40 * L)) := by
  classical
  let B : Fin 4 → Set Ω := fun j => {ω | normalizedDeviation m (q j) (W j ω) >
    empiricalRadius H m (L / m) (W j ω) / 4}
  have hsub : {ω | (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω))} ⊆ ⋃ j, B j := by
    intro ω hω
    change ¬ ∀ j, (q j : ℝ) ∈ Set.Icc
      (pilotLower H hHpos m L (fun j => W j ω) j)
      (pilotUpperFormula H hHpos m L (fun j => W j ω) j) at hω
    obtain ⟨j, hj⟩ := not_forall.mp hω
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    have hfail := (pilotInterval_failure_iff H hHpos m L (q j) (q j).coe_nonneg
      (fun j => W j ω) j).mp hj
    rw [pilotHalfWidth_eq_empiricalRadius] at hfail
    have hw0 : 0 ≤ empiricalRadius H m (L / m) (W j ω) := by
      unfold empiricalRadius
      positivity
    change empiricalRadius H m (L / m) (W j ω) / 4 <
      |(W j ω : ℝ) / m - q j|
    exact lt_of_le_of_lt (by linarith) hfail
  have hB (j : Fin 4) : μ (B j) ≤ ENNReal.ofReal (2 * Real.exp (-40 * L)) := by
    rw [(hlaw j).measure_eq (show MeasurableSet {w : ℕ |
      normalizedDeviation m (q j) w > empiricalRadius H m (L / m) w / 4} from
        Set.to_countable _ |>.measurableSet)]
    exact poisson_empiricalRadius_bad_probability (q j) m hm H L hH hL
  calc
    _ ≤ μ (⋃ j, B j) := measure_mono hsub
    _ ≤ ∑' j, μ (B j) := measure_iUnion_le B
    _ ≤ ∑' _j : Fin 4, ENNReal.ofReal (2 * Real.exp (-40 * L)) :=
      ENNReal.tsum_le_tsum hB
    _ = ENNReal.ofReal (8 * Real.exp (-40 * L)) := by
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast]
      norm_num only [Nat.cast_ofNat]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

/-- Failure of the actual pilot rectangle is contained in the empirical-radius bad union used by the independent-product moment theorem. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hH,hL), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_failure_subset_empiricalBadAny {Ω : Type*}
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0)
    (H : ℝ) (hH : 0 < H) (L : ℝ) (hL : 0 ≤ L) :
    {ω | (fun j => (q j : ℝ)) ∉ pilotRectangle
      (pilotLower H hH m L (fun j => W j ω))
      (pilotUpperFormula H hH m L (fun j => W j ω))} ⊆
      empiricalBadAny W H L m q := by
  intro ω hω
  change ¬ ∀ j, (q j : ℝ) ∈ Set.Icc
    (pilotLower H hH m L (fun j => W j ω) j)
    (pilotUpperFormula H hH m L (fun j => W j ω) j) at hω
  obtain ⟨j, hj⟩ := not_forall.mp hω
  have hf := (pilotInterval_failure_iff H hH m L (q j) (q j).coe_nonneg
    (fun j => W j ω) j).mp hj
  rw [pilotHalfWidth_eq_empiricalRadius] at hf
  have hw : 0 ≤ empiricalRadius H m (L / m) (W j ω) := by
    unfold empiricalRadius
    exact mul_nonneg hH.le (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  exact ⟨j, lt_of_le_of_lt (by linarith) hf⟩

-- @node: pilotAggregateScore_pow_integrable
/-- All four-coordinate score powers needed for the bad-pilot comparison are integrable, derived from the marginal Poisson laws rather than assumed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hH,hL,hW,hlaw,ht), the [stated conclusion](goal) holds. -/
lemma pilotAggregateScore_pow_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0)
    (m : ℝ≥0) (hm : 0 < m) (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (t : ℕ) (ht : t = 1 ∨ t = 2 ∨ t = 4) :
    Integrable (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) μ := by
  have ht4 : t ≤ 4 := by rcases ht with rfl | rfl | rfl <;> omega
  have hi (j : Fin 4) : Integrable (fun ω =>
      (normalizedDeviation m (q j) (W j ω) +
        empiricalRadius H m (L / m) (W j ω)) ^ t) μ := by
    have h := pilotCoordinate_score_pow_integrable (q j) m hm H L hH hL t ht4
    rw [← (hlaw j).map_eq] at h
    exact h.comp_aemeasurable (hlaw j).aemeasurable
  have hdom := (integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul
    ((4 : ℝ) ^ (t - 1))
  have hn (j : Fin 4) (ω : Ω) : 0 ≤ normalizedDeviation m (q j) (W j ω) +
      empiricalRadius H m (L / m) (W j ω) := by
    have hH0 := universalH_pos.le.trans hH
    unfold normalizedDeviation empiricalRadius
    positivity
  apply hdom.mono'
  · unfold empiricalAggregateScore normalizedDeviation empiricalRadius
    fun_prop
  · apply ae_of_all
    intro ω
    unfold empiricalAggregateScore
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pow_nonneg (Finset.sum_nonneg (fun j _ => hn j ω)) t)]
    rcases ht with rfl | rfl | rfl
    · simp
    · simpa using (pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset (Fin 4))) (fun j _ => hn j ω) 1)
    · simpa using (pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset (Fin 4))) (fun j _ => hn j ω) 3)

open Classical in
/-- Roadmap (16) jointly controls every coordinate's score on failure of any coordinate. This retains the cross-coordinate terms needed in (22), which a sum of the scalar bad moments alone does not control. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hW,hlaw,hind,ht), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_aggregate_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (hind : iIndepFun W μ) (t : ℕ) (ht : t = 1 ∨ t = 2 ∨ t = 4) :
    (∫ ω, if (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      (∑ j : Fin 4, (|pilotCenterFormula m (fun i => W i ω) j - q j| +
        pilotHalfWidthFormula H hHpos m L (fun i => W i ω) j)) ^ t else 0 ∂μ) ≤
      (H / universalH) ^ t * productMomentConstant 4 t * Real.exp (-20 * L) *
        (Real.sqrt ((∑ j, (q j : ℝ)) * L / m) + L / m) ^ t := by
  classical
  have hsub := pilotRectangle_failure_subset_empiricalBadAny W q m H hHpos L (by linarith)
  have hi := (pilotAggregateScore_pow_integrable μ W q m hm H L hH hL hW hlaw t ht).indicator
    (show MeasurableSet (empiricalBadAny W H L m q) by
      unfold empiricalBadAny normalizedDeviation empiricalRadius
      measurability)
  have hn (ω : Ω) : 0 ≤ empiricalAggregateScore W H L m q ω := by
    have hH0 := universalH_pos.le.trans hH
    unfold empiricalAggregateScore normalizedDeviation empiricalRadius
    positivity
  have hmono : (∫ ω, if (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      (∑ j : Fin 4, (|pilotCenterFormula m (fun i => W i ω) j - q j| +
        pilotHalfWidthFormula H hHpos m L (fun i => W i ω) j)) ^ t else 0 ∂μ) ≤
      ∫ ω, (empiricalBadAny W H L m q).indicator
        (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) ω ∂μ := by
    apply integral_mono_of_nonneg
    · apply ae_of_all
      intro ω
      simp only [pilotHalfWidth_eq_empiricalRadius, pilotCenterFormula]
      change 0 ≤ if _ then (empiricalAggregateScore W H L m q ω) ^ t else 0
      split_ifs
      · exact le_rfl
      · exact pow_nonneg (hn ω) t
    · exact hi
    · apply ae_of_all
      intro ω
      dsimp only
      by_cases hf : (fun j => (q j : ℝ)) ∉ pilotRectangle
          (pilotLower H hHpos m L (fun j => W j ω))
          (pilotUpperFormula H hHpos m L (fun j => W j ω))
      · rw [if_pos hf, Set.indicator_of_mem (hsub hf)]
        simp only [empiricalAggregateScore, normalizedDeviation, pilotCenterFormula,
          pilotHalfWidth_eq_empiricalRadius]
        exact le_rfl
      · rw [if_neg hf]
        exact Set.indicator_nonneg (fun ω _ => pow_nonneg (hn ω) t) _
  exact hmono.trans (independent_poisson_empiricalRadius_badAny_moment_four
    μ W q m hm hW hlaw hind ht H L hH hL)

-- @node: pilotMidpoint_total_abs_error_le_score
/-- The total pilot midpoint displacement is bounded by the joint score, including pilots whose intervals fail to contain the true vector. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hH,hL), the [stated conclusion](goal) holds. -/
lemma pilotMidpoint_total_abs_error_le_score {Ω : Type*}
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hH : 0 < H) (L : ℝ) (hL : 0 ≤ L) (ω : Ω) :
    (∑ j : Fin 4, |pilotMidpoint H hH m L (fun i => W i ω) j - q j|) ≤
      empiricalAggregateScore W H L m q ω := by
  unfold empiricalAggregateScore
  apply Finset.sum_le_sum
  intro j _
  simpa only [pilotCenterFormula, normalizedDeviation, pilotHalfWidth_eq_empiricalRadius] using
    pilotMidpoint_abs_error_le H hH m L (NNReal.coe_pos.mpr hm) hL
      (fun i => W i ω) (fun i => (q i : ℝ)) j

open Classical in
/-- Joint bad-pilot moments also control movement of the actual midpoint. This supplies the unweighted center-displacement component of (22b) without separating the random midpoint from the rectangle-failure event. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hW,hlaw,hind,ht), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_midpoint_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (hind : iIndepFun W μ) (t : ℕ) (ht : t = 1 ∨ t = 2 ∨ t = 4) :
    (∫ ω, if (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      (∑ j : Fin 4, |pilotMidpoint H hHpos m L (fun i => W i ω) j - q j|) ^ t
      else 0 ∂μ) ≤
      (H / universalH) ^ t * productMomentConstant 4 t * Real.exp (-20 * L) *
        (Real.sqrt ((∑ j, (q j : ℝ)) * L / m) + L / m) ^ t := by
  classical
  let B : Set Ω := {ω | (fun j => (q j : ℝ)) ∉ pilotRectangle
      (pilotLower H hHpos m L (fun j => W j ω))
      (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hi := (pilotAggregateScore_pow_integrable μ W q m hm H L hH hL hW hlaw t ht).indicator hB
  have hmono : (∫ ω, if ω ∈ B then
      (∑ j : Fin 4, |pilotMidpoint H hHpos m L (fun i => W i ω) j - q j|) ^ t
      else 0 ∂μ) ≤
      ∫ ω, B.indicator (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) ω ∂μ := by
    apply integral_mono_of_nonneg
    · apply ae_of_all
      intro ω
      dsimp only
      split_ifs <;> positivity
    · exact hi
    · apply ae_of_all
      intro ω
      dsimp only
      by_cases hb : ω ∈ B
      · rw [if_pos hb, Set.indicator_of_mem hb]
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => abs_nonneg _))
          (pilotMidpoint_total_abs_error_le_score W q m hm H hHpos L (by linarith) ω) t
      · rw [if_neg hb, Set.indicator_of_notMem hb]
  apply hmono.trans
  convert pilotRectangle_bad_aggregate_moment_le μ W q m hm H hHpos L hH hL
    hW hlaw hind t ht using 1
  · congr 1
  · apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hb : ω ∈ B
    · simp [Set.indicator_of_mem hb, show (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) from hb,
        empiricalAggregateScore, normalizedDeviation, pilotCenterFormula,
        pilotHalfWidth_eq_empiricalRadius]
    · simp [Set.indicator_of_notMem hb, show ¬ (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) from hb]

end CausalSmith.Stat.OptvalueVanishingoverlapRate
