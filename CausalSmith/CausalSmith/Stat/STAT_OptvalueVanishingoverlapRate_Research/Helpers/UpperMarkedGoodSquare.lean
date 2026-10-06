module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedConditioning

/-! # Integrated good-pilot moments and active risk

Fixed-pilot Jackson approximation and clipping bounds are averaged using
the actual independent marked vectors. This proves the occupied-cell
first- and first- and second-moment inputss of roadmap (29), retaining the squared approximation
term rather than absorbing it into factorial variance.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.Concentration.PoissonSelfNormalized
open scoped BigOperators NNReal

open Classical in
/-- One universal degree tuning proves the integrated good-pilot occupied cell bias and squared loss for the implemented statistic. All count laws, independence, localization and integrability inputs are discharged. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_occupied_good_moments_tuning_exists :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {n d : ℕ}, 1 ≤ n → 1 ≤ d →
      ∀ (P : DiscreteLaw d) (ε : ℝ), 0 < ε → ε ≤ 1 → ObservedClass ε P →
      ∀ (H : ℝ) (hHpos : 0 < H), universalH ≤ H → 1 ≤ H →
      ∀ (x : Fin d), 0 < cellMass P x →
      let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)
      let B := 512 * (H * (H + 2)) * Real.sqrt 2 *
        (1 / (κ / 2) + 1 / (κ / 2) ^ 2) *
        (Real.sqrt (cellMass P x / (poissonIntensityFormula n * ε * logAlphabet d)) +
          1 / (poissonIntensityFormula n * ε * logAlphabet d))
      (∫ s, if s ∈ markedPoissonGoodPilot n P H hHpos x then
        (markedPoissonCellValue n d H hHpos κ ε x s -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
        2 * A * (d : ℝ) ^ (1 / 16 : ℝ) *
          (∫ s, markedPoissonClippingScale n d H hHpos ε x s ^ 2 ∂μ) + 2 * B ^ 2 ∧
      |∫ s, if s ∈ markedPoissonGoodPilot n P H hHpos x then
        markedPoissonCellValue n d H hHpos κ ε x s -
          armwiseExtensionFormula ε (cellVector P x) else 0 ∂μ| ≤
        B + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) *
          (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ) := by
  classical
  obtain ⟨κ, A, hκ, hA, htune⟩ := observed_pilotClippedCellValue_target_tuning_exists
  refine ⟨κ, A, hκ, hA, ?_⟩
  intro n d hn hd P ε hε hε1 hP H hHpos hH hHlarge x hp
  dsimp only
  let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
    ((n : ℝ≥0) / 4)
  let B := 512 * (H * (H + 2)) * Real.sqrt 2 *
    (1 / (κ / 2) + 1 / (κ / 2) ^ 2) *
    (Real.sqrt (cellMass P x / (poissonIntensityFormula n * ε * logAlphabet d)) +
      1 / (poissonIntensityFormula n * ε * logAlphabet d))
  let E : (Fin 4 → ℕ) → Prop := fun v => cellVector P x ∈
    pilotRectangle (pilotLower H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
      (pilotUpperFormula H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
  let T : (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℝ := fun v w =>
    clippedCellValueFormula ε (jacksonDegree κ d) d (poissonIntensityFormula n)
      (pilotMidpoint H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
      (pilotRadiusFormula H hHpos (poissonIntensityFormula n) (logAlphabet d) v) w
  let S : (Fin 4 → ℕ) → ℝ := fun v => clippingScaleFormula ε
    (pilotMidpoint H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
    (pilotRadiusFormula H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
  let f : (Fin 4 → ℕ) × (Fin 4 → ℕ) → ℝ := fun z =>
    if E z.1 then (T z.1 z.2 - armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0
  let g : (Fin 4 → ℕ) → ℝ := fun v =>
    2 * A * (d : ℝ) ^ (1 / 16 : ℝ) * S v ^ 2 + 2 * B ^ 2
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  have hT := markedPoissonCellValue_memLp_two hn hd P H hHpos hH κ ε hε hε1 x
  have hS := markedPoissonClippingScale_memLp_two hn hd P H hHpos hH ε hε hε1 x
  constructor
  ·
    have hf : Integrable (fun s => f (markedPoissonCellCounts true x s,
        markedPoissonCellCounts false x s)) μ := by
      have hi := ((hT.sub (memLp_const (armwiseExtensionFormula ε (cellVector P x)))).indicator
        (markedPoissonGoodPilot_measurableSet n P H hHpos x)).integrable_sq
      convert hi using 1
      funext s
      rw [Set.indicator_apply]
      change (if E (markedPoissonCellCounts true x s) then _ ^ 2 else 0) =
        (if E (markedPoissonCellCounts true x s) then _ else 0) ^ 2
      split_ifs
      · rfl
      · simp
    have hg : Integrable (fun s => g (markedPoissonCellCounts true x s)) μ := by
      exact (hS.integrable_sq.const_mul _).add (integrable_const _)
    have hfixed (v : Fin 4 → ℕ) :
        (∫ s, f (v, markedPoissonCellCounts false x s) ∂μ) ≤ g v := by
      by_cases hv : E v
      · have hlaw (j : Fin 4) : HasLaw (fun s => markedPoissonCellCounts false x s j)
            (poissonMeasure ⟨poissonIntensityFormula n * cellVector P x j,
              mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ := by
          have hr : (⟨poissonIntensityFormula n * cellVector P x j,
              mul_nonneg hm.le ENNReal.toReal_nonneg⟩ : ℝ≥0) =
              ((n : ℝ≥0) / (8 : ℝ≥0)) * (P.pmf (x, decide (j.val / 2 = 1),
                decide (j.val % 2 = 1))).toNNReal := by
            apply NNReal.coe_injective
            rfl
          rw [hr]
          exact markedCount_poisson_hasLaw P n false x j
        have ht := (htune μ hd ε P hε hP x hp
          (fun j s => markedPoissonCellCounts false x s j) H hHpos hHlarge
          (poissonIntensityFormula n) hm v hlaw (markedPoissonEvaluation_iIndepFun P n x) hv).2
        simpa only [f, hv, if_true, T, g, S, B] using ht
      · simp only [f, hv, if_false, integral_zero]
        dsimp [g]
        positivity
    have hbound := markedPoissonCellCounts_integral_le_of_fixedPilot P n x f g hf hg
      (fun z => by dsimp [f]; split_ifs <;> positivity) hfixed
    have hright : (∫ s, g (markedPoissonCellCounts true x s) ∂μ) =
        2 * A * (d : ℝ) ^ (1 / 16 : ℝ) *
          (∫ s, markedPoissonClippingScale n d H hHpos ε x s ^ 2 ∂μ) + 2 * B ^ 2 := by
      change (∫ s, 2 * A * (d : ℝ) ^ (1 / 16 : ℝ) *
        markedPoissonClippingScale n d H hHpos ε x s ^ 2 + 2 * B ^ 2 ∂μ) = _
      rw [integral_add (hS.integrable_sq.const_mul _) (integrable_const _),
        integral_const_mul]
      simp [μ]
    rw [hright] at hbound
    exact hbound
  ·
    let f₁ : (Fin 4 → ℕ) × (Fin 4 → ℕ) → ℝ := fun z =>
      if E z.1 then T z.1 z.2 - armwiseExtensionFormula ε (cellVector P x) else 0
    let g₁ : (Fin 4 → ℕ) → ℝ := fun v =>
      B + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) * S v
    have hf₁ : Integrable (fun s => f₁ (markedPoissonCellCounts true x s,
        markedPoissonCellCounts false x s)) μ := by
      exact ((hT.sub (memLp_const (armwiseExtensionFormula ε (cellVector P x)))).indicator
        (markedPoissonGoodPilot_measurableSet n P H hHpos x)).integrable (by norm_num)
    have hg₁ : Integrable (fun s => g₁ (markedPoissonCellCounts true x s)) μ := by
      exact (integrable_const _).add ((hS.integrable (by norm_num)).const_mul _)
    have hfixed (v : Fin 4 → ℕ) :
        |∫ s, f₁ (v, markedPoissonCellCounts false x s) ∂μ| ≤ g₁ v := by
      by_cases hv : E v
      · have hlaw (j : Fin 4) : HasLaw (fun s => markedPoissonCellCounts false x s j)
            (poissonMeasure ⟨poissonIntensityFormula n * cellVector P x j,
              mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ := by
          have hr : (⟨poissonIntensityFormula n * cellVector P x j,
              mul_nonneg hm.le ENNReal.toReal_nonneg⟩ : ℝ≥0) =
              ((n : ℝ≥0) / (8 : ℝ≥0)) * (P.pmf (x, decide (j.val / 2 = 1),
                decide (j.val % 2 = 1))).toNNReal := by
            apply NNReal.coe_injective
            rfl
          rw [hr]
          exact markedCount_poisson_hasLaw P n false x j
        have ht := (htune μ hd ε P hε hP x hp
          (fun j s => markedPoissonCellCounts false x s j) H hHpos hHlarge
          (poissonIntensityFormula n) hm v hlaw (markedPoissonEvaluation_iIndepFun P n x) hv).1
        have hi : Integrable (fun s => T v (markedPoissonCellCounts false x s)) μ := by
          exact (integrable_const _).sup ((integrable_const _).inf
            ((factorialCellValue_memLp_two μ
              (fun j s => markedPoissonCellCounts false x s j) _ hlaw
              (markedPoissonEvaluation_iIndepFun P n x) ε (jacksonDegree κ d)
              (poissonIntensityFormula n)
              (pilotMidpoint H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
              (pilotRadiusFormula H hHpos (poissonIntensityFormula n) (logAlphabet d) v)).integrable
                (by norm_num)))
        simp only [f₁, hv, if_true]
        rw [integral_sub hi (integrable_const _)]
        simpa [integral_const, μ, T, g₁, S, B] using ht
      · simp only [f₁, hv, if_false, integral_zero, abs_zero]
        have hL := logAlphabet_pos hd
        dsimp [g₁, B]
        have hSpos : 0 ≤ S v := by
          exact (clippingScale_pos ε
            (pilotMidpoint H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
            (pilotRadiusFormula H hHpos (poissonIntensityFormula n) (logAlphabet d) v)
            (pilotMidpoint_nonneg H hHpos _ _ hm v)
            (pilotRadius_pos H hHpos _ _ hm (logAlphabet_pos hd) v)).le
        positivity
    have hbound := markedPoissonCellCounts_abs_integral_le_of_fixedPilot P n x
      f₁ g₁ hf₁ hg₁ hfixed
    have hright : (∫ s, g₁ (markedPoissonCellCounts true x s) ∂μ) =
        B + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) *
          (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ) := by
      change (∫ s, B + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) *
        markedPoissonClippingScale n d H hHpos ε x s ∂μ) = _
      rw [integral_add (integrable_const _) ((hS.integrable (by norm_num)).const_mul _)]
      simp only [integral_const_mul, integral_const]
      simp [μ, B]
    rw [hright] at hbound
    exact hbound

open Classical in
/-- One universal degree tuning proves the integrated good-pilot occupied cell loss for the implemented statistic. All count laws, independence, localization and integrability inputs are discharged. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_occupied_good_sq_tuning_exists :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {n d : ℕ}, 1 ≤ n → 1 ≤ d →
      ∀ (P : DiscreteLaw d) (ε : ℝ), 0 < ε → ε ≤ 1 → ObservedClass ε P →
      ∀ (H : ℝ) (hHpos : 0 < H), universalH ≤ H → 1 ≤ H →
      ∀ (x : Fin d), 0 < cellMass P x →
      let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)
      let B := 512 * (H * (H + 2)) * Real.sqrt 2 *
        (1 / (κ / 2) + 1 / (κ / 2) ^ 2) *
        (Real.sqrt (cellMass P x / (poissonIntensityFormula n * ε * logAlphabet d)) +
          1 / (poissonIntensityFormula n * ε * logAlphabet d))
      (∫ s, if s ∈ markedPoissonGoodPilot n P H hHpos x then
        (markedPoissonCellValue n d H hHpos κ ε x s -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
        2 * A * (d : ℝ) ^ (1 / 16 : ℝ) *
          (∫ s, markedPoissonClippingScale n d H hHpos ε x s ^ 2 ∂μ) + 2 * B ^ 2 := by
  obtain ⟨κ, A, hκ, hA, ht⟩ := markedPoissonCellValue_occupied_good_moments_tuning_exists
  refine ⟨κ, A, hκ, hA, ?_⟩
  intro n d hn hd P ε hε hε1 hP H hHpos hH hHlarge x hp
  exact (ht hn hd P ε hε hε1 hP H hHpos hH hHlarge x hp).1

-- @node: markedPoissonClippingScale_nonneg
/-- The actual pilot clipping scale is nonnegative at every finite sample. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hH), the [stated conclusion](goal) holds. -/
lemma markedPoissonClippingScale_nonneg {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (H : ℝ) (hH : 0 < H) (ε : ℝ) (x : Fin d)
    (s : FiniteSample (Obs d × Bool)) :
    0 ≤ markedPoissonClippingScale n d H hH ε x s := by
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  unfold markedPoissonClippingScale
  exact (clippingScale_pos ε _ _ (pilotMidpoint_nonneg H hH _ _ hm _)
    (pilotRadius_pos H hH _ _ hm (logAlphabet_pos hd) _)).le

/-- Equations (19), (20), (22), and (28) yield the active-branch risk for the implemented uncapped statistic. Both good-pilot content inputs are proved here, including null cells, with the same universal degree tuning. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hHpos,hH,hHlarge), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_active_rate_tuning_exists
    (H : ℝ) (hHpos : 0 < H) (hH : universalH ≤ H) (hHlarge : 1 ≤ H) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ {n d : ℕ}, 1 ≤ n → 1 ≤ d →
      ∀ (P : DiscreteLaw d) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      ObservedClass ε P → (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε →
      Causalean.Stat.sqRisk
        (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
          ((n : ℝ≥0) / 4))
        (markedPoissonStatistic n d H hHpos κ ε) (observedValue P) ≤
          C * ((d : ℝ) / (poissonIntensityFormula n * ε * logAlphabet d)) := by
  classical
  obtain ⟨κ, A, hκ, hA, ht⟩ := markedPoissonCellValue_occupied_good_moments_tuning_exists
  let D := 512 * (H * (H + 2)) * Real.sqrt 2 *
    (1 / (κ / 2) + 1 / (κ / 2) ^ 2)
  let Dnull := 64 * H / (κ / 2) ^ 2
  let De := D + Dnull
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDnull : 0 ≤ Dnull := by dsimp [Dnull]; positivity
  have hDe : 0 ≤ De := add_nonneg hD hDnull
  obtain ⟨C, hC, hrate⟩ := markedPoissonStatistic_goodPilotEstimates_rate_le
    H hHpos hH κ (2 * A) (De + A) (2 * De ^ 2) (by positivity) (by positivity)
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro n d hn hd P ε hε hεhalf hP hactive
  have hε1 : ε ≤ 1 := by linarith
  let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
    ((n : ℝ≥0) / 4)
  let Q (x : Fin d) := Real.sqrt (cellMass P x /
    (poissonIntensityFormula n * ε * logAlphabet d)) +
      1 / (poissonIntensityFormula n * ε * logAlphabet d)
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  have hL := logAlphabet_pos hd
  have hQ (x : Fin d) : 0 ≤ Q x := by dsimp [Q]; positivity
  have hs (x : Fin d) : 0 ≤ ∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ :=
    integral_nonneg (markedPoissonClippingScale_nonneg hn hd H hHpos ε x)
  have hs₂ (x : Fin d) : 0 ≤ ∫ s, markedPoissonClippingScale n d H hHpos ε x s ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  apply hrate hn hd P ε hε hεhalf hP hactive
  · intro x
    by_cases hp : 0 < cellMass P x
    · have hb := (ht hn hd P ε hε hε1 hP H hHpos hH hHlarge x hp).1
      change (∫ s, if s ∈ markedPoissonGoodPilot n P H hHpos x then
        (markedPoissonCellValue n d H hHpos κ ε x s -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
        2 * A * (d : ℝ) ^ (1 / 16 : ℝ) *
          (∫ s, markedPoissonClippingScale n d H hHpos ε x s ^ 2 ∂μ) +
          2 * (D * Q x) ^ 2 at hb
      apply hb.trans
      have hsq : (D * Q x) ^ 2 ≤ (De * Q x) ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg hD (hQ x))
        exact mul_le_mul_of_nonneg_right (by dsimp [De]; linarith) (hQ x)
      dsimp only [Q]
      nlinarith [hsq]
    · have hp0 : cellMass P x = 0 := le_antisymm (le_of_not_gt hp)
        (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun y _ => ENNReal.toReal_nonneg)))
      have hb := (markedPoissonCellValue_null_good_moments_le hn hd P x hp0
        H hHpos κ ε hκ hε hε1).1
      have hQnull : Q x = 1 / (poissonIntensityFormula n * ε * logAlphabet d) := by
        simp [Q, hp0]
      change (∫ s, if s ∈ markedPoissonGoodPilot n P H hHpos x then
        (markedPoissonCellValue n d H hHpos κ ε x s -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
          (Dnull * (1 / (poissonIntensityFormula n * ε * logAlphabet d))) ^ 2 at hb
      rw [← hQnull] at hb
      apply hb.trans
      have hsq : (Dnull * Q x) ^ 2 ≤ (De * Q x) ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg hDnull (hQ x))
        exact mul_le_mul_of_nonneg_right (by dsimp [De]; linarith) (hQ x)
      have hv : 0 ≤ 2 * A * (d : ℝ) ^ (1 / 16 : ℝ) *
          (∫ s, markedPoissonClippingScale n d H hHpos ε x s ^ 2 ∂μ) := by
        positivity
      dsimp only [Q]
      nlinarith [hsq, sq_nonneg (De * Q x)]
  · intro x
    have hdPow : 0 ≤ (d : ℝ) ^ (-(3 / 16 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hw : 0 ≤ (d : ℝ) ^ (-(3 / 16 : ℝ)) *
        (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ) :=
      mul_nonneg hdPow (hs x)
    by_cases hp : 0 < cellMass P x
    · have hb := (ht hn hd P ε hε hε1 hP H hHpos hH hHlarge x hp).2
      apply hb.trans
      change D * Q x + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) *
        (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ) ≤ _
      change D * Q x + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) *
        (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ) ≤
          (De + A) * (Q x + (d : ℝ) ^ (-(3 / 16 : ℝ)) *
            (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ))
      calc
        _ ≤ (De + A) * Q x + (De + A) * ((d : ℝ) ^ (-(3 / 16 : ℝ)) *
            (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (by dsimp only [De]; linarith) (hQ x)
          · simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_right (show A ≤ De + A by linarith) hw
        _ = _ := by ring
    · have hp0 : cellMass P x = 0 := le_antisymm (le_of_not_gt hp)
        (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun y _ => ENNReal.toReal_nonneg)))
      have hb := (markedPoissonCellValue_null_good_moments_le hn hd P x hp0
        H hHpos κ ε hκ hε hε1).2
      apply hb.trans
      change Dnull * (1 / (poissonIntensityFormula n * ε * logAlphabet d)) ≤
          (De + A) * (Q x + (d : ℝ) ^ (-(3 / 16 : ℝ)) *
            (∫ s, markedPoissonClippingScale n d H hHpos ε x s ∂μ))
      have hQnull : Q x = 1 / (poissonIntensityFormula n * ε * logAlphabet d) := by
        simp [Q, hp0]
      rw [← hQnull]
      calc
        _ ≤ (De + A) * Q x := mul_le_mul_of_nonneg_right
          (by dsimp only [De]; linarith) (hQ x)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hw)
          (add_nonneg hDe hA.le)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
