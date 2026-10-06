module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotRegularity

/-! # Coordinate moments on failed pilot rectangles

The fourth marginal score moment and the rectangle failure probability give
an exponentially small second moment for each coordinate on any pilot failure.
Unlike an aggregate mass bound, this retains each coordinate's true mass for
the armwise inverse-propensity weighting in roadmap (22b). The actual
pilot-center functional inherits these moments through the armwise modulus;
summing outcome masses retains one inverse-overlap power in its mass term.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped BigOperators NNReal


-- @node: pilotCoordinate_score_integral_pow_le
/-- Every coordinate score moment through degree four has its own true-mass scale, obtained from the marginal Poisson law and the raw-score comparison. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hH,hL,hlaw,ht), the [stated conclusion](goal) holds. -/
lemma pilotCoordinate_score_integral_pow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0)
    (m : ℝ≥0) (hm : 0 < m) (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (j : Fin 4) (t : ℕ) (ht : t ≤ 4) :
    (∫ ω, (normalizedDeviation m (q j) (W j ω) +
        empiricalRadius H m (L / m) (W j ω)) ^ t ∂μ) ≤
      (H / universalH) ^ t * scalarMomentConstant t *
        (Real.sqrt ((q j : ℝ) * L / m) + L / m) ^ t := by
  let c : ℝ := H / universalH / (m : ℝ)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (div_nonneg (universalH_pos.le.trans hH) universalH_pos.le) m.coe_nonneg
  have hi : Integrable (fun ω => (score universalH L (m * q j) (W j ω)) ^ t) μ := by
    have h := integrable_score_pow (m * q j) hL ht
    rw [← (hlaw j).map_eq] at h
    exact h.comp_aemeasurable (hlaw j).aemeasurable
  have he := (hlaw j).integral_comp
    (Measurable.of_discrete.aestronglyMeasurable (f := fun w : ℕ =>
      (score universalH L (m * q j) w) ^ t))
  simp only [Function.comp_def] at he
  calc
    _ ≤ ∫ ω, c ^ t * (score universalH L (m * q j) (W j ω)) ^ t ∂μ := by
      apply integral_mono_of_nonneg
      · apply ae_of_all
        intro ω
        have := universalH_pos.le.trans hH
        unfold normalizedDeviation empiricalRadius
        positivity
      · exact hi.const_mul _
      · apply ae_of_all
        intro ω
        have hs := empiricalRadius_score_le_raw (q j) m hm H L hH hL (W j ω)
        have hn : 0 ≤ normalizedDeviation m (q j) (W j ω) +
            empiricalRadius H m (L / m) (W j ω) := by
          have := universalH_pos.le.trans hH
          unfold normalizedDeviation empiricalRadius
          positivity
        convert pow_le_pow_left₀ hn hs t using 1
        dsimp [c]
        ring
    _ = c ^ t * ∫ w : ℕ, (score universalH L (m * q j) w) ^ t
        ∂poissonMeasure (m * q j) := by
      rw [integral_const_mul, he]
    _ ≤ c ^ t * (scalarMomentConstant t * (localScale (m * q j) L) ^ t) :=
      mul_le_mul_of_nonneg_left (poisson_score_moment (m * q j) hL ht) (pow_nonneg hc t)
    _ = _ := by
      rw [show c ^ t * (scalarMomentConstant t * (localScale (m * q j) L) ^ t) =
        (H / universalH) ^ t * scalarMomentConstant t *
          (localScale (m * q j) L / (m : ℝ)) ^ t by
            dsimp [c]; rw [div_pow, div_pow]; ring]
      rw [empiricalRadius_localScale_div (q j) m hm L hL]

open Classical in
/-- Even when a different coordinate fails localization, a coordinate's second score moment is exponentially small with its own mass scale. Hölder uses the marginal fourth moment and the full rectangle failure probability; no coordinate independence is needed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_coordinate_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ) (j : Fin 4) :
    (∫ ω, if (fun i => (q i : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun i => W i ω))
        (pilotUpperFormula H hHpos m L (fun i => W i ω)) then
      (normalizedDeviation m (q j) (W j ω) +
        empiricalRadius H m (L / m) (W j ω)) ^ 2 else 0 ∂μ) ≤
      Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
        Real.exp (-20 * L) *
        (Real.sqrt ((q j : ℝ) * L / m) + L / m) ^ 2 := by
  classical
  let B : Set Ω := {ω | (fun i => (q i : ℝ)) ∉ pilotRectangle
    (pilotLower H hHpos m L (fun i => W i ω))
    (pilotUpperFormula H hHpos m L (fun i => W i ω))}
  let S : Ω → ℝ := fun ω => normalizedDeviation m (q j) (W j ω) +
    empiricalRadius H m (L / m) (W j ω)
  let a : ℝ := Real.sqrt ((q j : ℝ) * L / m) + L / m
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hi4 : Integrable (fun ω => S ω ^ 4) μ := by
    have h := pilotCoordinate_score_pow_integrable (q j) m hm H L hH hL 4 (by omega)
    rw [← (hlaw j).map_eq] at h
    exact h.comp_aemeasurable (hlaw j).aemeasurable
  have hS : MemLp (fun ω => S ω ^ 2) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by dsimp [S]; fun_prop)).2
    simpa only [← pow_mul] using hi4
  have hp : μ.real B ≤ 8 * Real.exp (-40 * L) := by
    have h := pilotRectangle_bad_probability_le μ W q m hm H hHpos L hH hL hlaw
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hs := pilotCoordinate_score_integral_pow_le μ W q m hm H L hH hL hlaw j 4 (by omega)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun ω => S ω ^ 2) (g := B.indicator (fun _ => (1 : ℝ)))
    (ae_of_all _ fun ω => sq_nonneg _) 
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (by simpa using hS)
    (by simpa using (memLp_const (1 : ℝ) (p := (2 : ENNReal)) (μ := μ)).indicator hB)
  have hmul (ω : Ω) : S ω ^ 2 * B.indicator (fun _ => (1 : ℝ)) ω =
      B.indicator (fun ω => S ω ^ 2) ω := by by_cases h : ω ∈ B <;> simp [h]
  have hone (ω : Ω) : (B.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ) =
      B.indicator (fun _ => (1 : ℝ)) ω := by by_cases h : ω ∈ B <;> simp [h]
  have hpow (ω : Ω) : (S ω ^ 2) ^ (2 : ℝ) = S ω ^ 4 := by
    rw [Real.rpow_two, ← pow_mul]
  simp_rw [hmul, hone, hpow, ← Real.sqrt_eq_rpow] at hh
  rw [integral_indicator_const _ hB] at hh
  simp only [smul_eq_mul, mul_one] at hh
  have hb := mul_le_mul (Real.sqrt_le_sqrt hs) (Real.sqrt_le_sqrt hp)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hc : 0 ≤ H / universalH := div_nonneg hHpos.le universalH_pos.le
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hconstant := (scalarMomentConstant_pos 4).le
  have he : Real.sqrt ((H / universalH) ^ 4 * scalarMomentConstant 4 * a ^ 4) *
      Real.sqrt (8 * Real.exp (-40 * L)) =
      Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
        Real.exp (-20 * L) * a ^ 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    have hexp : Real.exp (-40 * L) = Real.exp (-20 * L) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have heq : (H / universalH) ^ 4 * scalarMomentConstant 4 * a ^ 4 *
        (8 * Real.exp (-40 * L)) =
        (Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
          Real.exp (-20 * L) * a ^ 2) ^ 2 := by
      rw [hexp, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by
        have := (scalarMomentConstant_pos 4).le; positivity)]
      ring
    rw [heq, Real.sqrt_sq (by positivity)]
  simpa only [B, S, a, Set.indicator, Set.mem_ofPred_eq] using
    (hh.trans hb).trans_eq he

open Classical in
/-- A weighted coordinate score retains each weight next to its own true-mass scale on rectangle failure. This is the finite Cauchy–Schwarz assembly needed before substituting inverse arm propensities in roadmap (22b). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hW,hlaw,hw), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_weightedScore_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ)
    (w : Fin 4 → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (∫ ω, if (fun j => (q j : ℝ)) ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      (∑ j, w j * (normalizedDeviation m (q j) (W j ω) +
        empiricalRadius H m (L / m) (W j ω))) ^ 2 else 0 ∂μ) ≤
      4 * (Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
        Real.exp (-20 * L)) *
        ∑ j, w j ^ 2 * (Real.sqrt ((q j : ℝ) * L / m) + L / m) ^ 2 := by
  classical
  let B : Set Ω := {ω | (fun j => (q j : ℝ)) ∉ pilotRectangle
    (pilotLower H hHpos m L (fun j => W j ω))
    (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  let S : Fin 4 → Ω → ℝ := fun j ω => normalizedDeviation m (q j) (W j ω) +
    empiricalRadius H m (L / m) (W j ω)
  let C : ℝ := Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
    Real.exp (-20 * L)
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hi (j : Fin 4) : Integrable (B.indicator (fun ω => S j ω ^ 2)) μ := by
    have h := pilotCoordinate_score_pow_integrable (q j) m hm H L hH hL 2 (by omega)
    rw [← (hlaw j).map_eq] at h
    exact (h.comp_aemeasurable (hlaw j).aemeasurable).indicator hB
  have hn (j : Fin 4) (ω : Ω) : 0 ≤ S j ω := by
    have := universalH_pos.le.trans hH
    dsimp [S]; unfold normalizedDeviation empiricalRadius; positivity
  have hs (j : Fin 4) : (∫ ω, B.indicator (fun ω => S j ω ^ 2) ω ∂μ) ≤
      C * (Real.sqrt ((q j : ℝ) * L / m) + L / m) ^ 2 := by
    simpa only [B, S, C, Set.indicator, Set.mem_ofPred_eq] using
      pilotRectangle_bad_coordinate_integral_sq_le μ W q m hm H hHpos L hH hL hW hlaw j
  calc
    _ ≤ ∫ ω, 4 * ∑ j, w j ^ 2 * B.indicator (fun ω => S j ω ^ 2) ω ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun ω => by dsimp only; split_ifs <;> positivity
      · exact (integrable_finsetSum Finset.univ (fun j _ => (hi j).const_mul _)).const_mul 4
      · apply ae_of_all
        intro ω
        by_cases hb : ω ∈ B
        · change (if ω ∈ B then (∑ j, w j * S j ω) ^ 2 else 0) ≤ _
          rw [if_pos hb]
          simp only [Set.indicator_of_mem hb]
          simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, pow_one, mul_pow] using
            pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin 4)))
              (fun j _ => mul_nonneg (hw j) (hn j ω)) 1
        · change (if ω ∈ B then _ else 0) ≤ _
          simp [hb]
    _ = 4 * ∑ j, w j ^ 2 * ∫ ω, B.indicator (fun ω => S j ω ^ 2) ω ∂μ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun j _ => (hi j).const_mul _)]
      simp_rw [integral_const_mul]
    _ ≤ 4 * ∑ j, w j ^ 2 * (C *
        (Real.sqrt ((q j : ℝ) * L / m) + L / m) ^ 2) := by
      gcongr with j
      exact hs j
    _ = _ := by
      change 4 * ∑ j, w j ^ 2 * (C * _) = (4 * C) * ∑ j, w j ^ 2 * _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

open Classical in
/-- The actual pilot-center functional has an exponentially small second moment on rectangle failure. Each inverse propensity remains attached to its own coordinate mass, before any overlap-floor simplification. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,m,hm,hHpos,hH,hL,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_cellValue_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ε : ℝ) (P : DiscreteLaw d) (hε : 0 < ε)
    (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (W : Fin 4 → Ω → ℕ) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ) :
    (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      (armwiseExtensionFormula ε (pilotMidpoint H hHpos m L (fun j => W j ω)) -
        armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
      64 * (Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
        Real.exp (-20 * L)) *
        ∑ a : Bool, (cellMass P x / armMass P a x) ^ 2 *
          ∑ y : Bool, (Real.sqrt (jointMass P x a y * L / m) + L / m) ^ 2 := by
  classical
  let q : Fin 4 → ℝ≥0 := fun j => ⟨cellVector P x j, ENNReal.toReal_nonneg⟩
  have hqcoe (j : Fin 4) : (q j : ℝ) = cellVector P x j := rfl
  have hqfun : (fun j => (q j : ℝ)) = cellVector P x := funext hqcoe
  let w : Fin 4 → ℝ := fun j => cellMass P x / armMass P (decide (2 ≤ j.val)) x
  let B : Set Ω := {ω | cellVector P x ∉ pilotRectangle
    (pilotLower H hHpos m L (fun j => W j ω))
    (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  let S : Ω → ℝ := fun ω => ∑ j, w j * (normalizedDeviation m (q j) (W j ω) +
    empiricalRadius H m (L / m) (W j ω))
  have hw (j : Fin 4) : 0 ≤ w j := by
    dsimp [w]
    exact div_nonneg hp.le (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hi (j : Fin 4) : Integrable (fun ω =>
      (normalizedDeviation m (q j) (W j ω) +
        empiricalRadius H m (L / m) (W j ω)) ^ 2) μ := by
    have h := pilotCoordinate_score_pow_integrable (q j) m hm H L hH hL 2 (by omega)
    rw [← (hlaw j).map_eq] at h
    exact h.comp_aemeasurable (hlaw j).aemeasurable
  have hS : MemLp S 2 μ := by
    apply memLp_finsetSum
    intro j _
    exact ((memLp_two_iff_integrable_sq (by fun_prop)).2 (hi j)).const_mul (w j)
  have hpoint (ω : Ω) : |armwiseExtensionFormula ε
      (pilotMidpoint H hHpos m L (fun j => W j ω)) -
        armwiseExtensionFormula ε (cellVector P x)| ≤ 4 * S ω := by
    have h := pilotCellValue_abs_error_le ε P hε hP x hp H hHpos m L
      (NNReal.coe_pos.mpr hm) (by linarith) (fun j => W j ω)
    convert h using 1 <;>
      simp [S, w, hqcoe, Fin.sum_univ_succ, cellIdx,
        normalizedDeviation, pilotCenterFormula, pilotHalfWidth_eq_empiricalRadius] <;> ring
  have hb := pilotRectangle_bad_weightedScore_integral_sq_le μ W q m hm H hHpos L
    hH hL hW hlaw w hw
  calc
    _ ≤ ∫ ω, 16 * B.indicator (fun ω => S ω ^ 2) ω ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun ω => by dsimp only; split_ifs <;> positivity
      · exact ((memLp_two_iff_integrable_sq hS.aestronglyMeasurable).1 hS).indicator hB
          |>.const_mul 16
      · apply ae_of_all
        intro ω
        by_cases h : ω ∈ B
        · change (if ω ∈ B then _ else 0) ≤ 16 * B.indicator (fun ω => S ω ^ 2) ω
          rw [if_pos h, Set.indicator_of_mem h]
          have hs : 0 ≤ S ω := Finset.sum_nonneg fun j _ =>
            mul_nonneg (hw j) (by
              have := universalH_pos.le.trans hH
              unfold normalizedDeviation empiricalRadius
              positivity)
          have hpow := pow_le_pow_left₀ (abs_nonneg _) (hpoint ω) 2
          simpa only [sq_abs, mul_pow, show (4 : ℝ) ^ 2 = 16 by norm_num] using hpow
        · change (if ω ∈ B then _ else 0) ≤ _
          simp [h]
    _ = 16 * ∫ ω, B.indicator (fun ω => S ω ^ 2) ω ∂μ := integral_const_mul _ _
    _ ≤ 16 * (4 * (Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
        Real.exp (-20 * L)) *
        ∑ j, w j ^ 2 * (Real.sqrt ((q j : ℝ) * L / m) + L / m) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [B, S, hqfun, Set.indicator, Set.mem_ofPred_eq] using hb
    _ = _ := by
      simp only [w, hqcoe]
      simp [Fin.sum_univ_succ, cellVector, jointMass]
      ring


-- @node: inverseArm_coordinate_scale_sq_sum_le
/-- Summing the two outcome masses before applying overlap preserves one inverse-overlap power in the mass term of the bad-pilot second moment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hε,hδ,hq₀,hq₁,hsum,hfloor), the [stated conclusion](goal) holds. -/
lemma inverseArm_coordinate_scale_sq_sum_le {p s q₀ q₁ δ ε : ℝ}
    (hp : 0 < p) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hq₀ : 0 ≤ q₀) (hq₁ : 0 ≤ q₁) (hsum : q₀ + q₁ = s)
    (hfloor : ε * p ≤ s) :
    (p / s) ^ 2 * ((Real.sqrt (q₀ * δ) + δ) ^ 2 +
      (Real.sqrt (q₁ * δ) + δ) ^ 2) ≤
      8 * (p * δ / ε + (δ / ε) ^ 2) := by
  have hs : 0 < s := lt_of_lt_of_le (mul_pos hε hp) hfloor
  have hw : p / s ≤ 1 / ε := by
    apply (div_le_div_iff₀ hs hε).2
    simpa only [one_mul, mul_one, mul_comm] using hfloor
  have hsumSq : (Real.sqrt (q₀ * δ) + δ) ^ 2 +
      (Real.sqrt (q₁ * δ) + δ) ^ 2 ≤ 2 * (s * δ + 2 * δ ^ 2) := by
    have h₀ := add_sq_le (a := Real.sqrt (q₀ * δ)) (b := δ)
    have h₁ := add_sq_le (a := Real.sqrt (q₁ * δ)) (b := δ)
    rw [Real.sq_sqrt (mul_nonneg hq₀ hδ)] at h₀
    rw [Real.sq_sqrt (mul_nonneg hq₁ hδ)] at h₁
    nlinarith [hsum]
  have hmass : (p / s) ^ 2 * (s * δ) ≤ p * δ / ε := by
    calc
      _ = (p * δ) * (p / s) := by field_simp
      _ ≤ (p * δ) * (1 / ε) := mul_le_mul_of_nonneg_left hw (mul_nonneg hp.le hδ)
      _ = _ := by ring
  have hlinear : (p / s) ^ 2 * δ ^ 2 ≤ (δ / ε) ^ 2 := by
    have h := pow_le_pow_left₀ (div_nonneg hp.le hs.le) hw 2
    have h' := mul_le_mul_of_nonneg_right h (sq_nonneg δ)
    convert h' using 1 <;> first | rfl | ring
  have h := mul_le_mul_of_nonneg_left hsumSq (sq_nonneg (p / s))
  nlinarith [div_nonneg (mul_nonneg hp.le hδ) hε.le]

open Classical in
/-- The center-value component of roadmap (22) has the required normalized mass and overlap scales on failed rectangles, without coordinate independence. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,m,hm,hHpos,hH,hL,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_cellValue_normalized_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ε : ℝ) (P : DiscreteLaw d) (hε : 0 < ε)
    (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (W : Fin 4 → Ω → ℕ) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ) :
    (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      (armwiseExtensionFormula ε (pilotMidpoint H hHpos m L (fun j => W j ω)) -
        armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
      1024 * (Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
        Real.exp (-20 * L)) *
        (cellMass P x * L / (m * ε) + L ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2)) := by
  have hb := pilotRectangle_bad_cellValue_integral_sq_le μ ε P hε hP x hp W m hm
    H hHpos L hH hL hW hlaw
  let C : ℝ := Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 *
    Real.exp (-20 * L)
  have hscale (a : Bool) : (cellMass P x / armMass P a x) ^ 2 *
      ∑ y : Bool, (Real.sqrt (jointMass P x a y * L / m) + L / m) ^ 2 ≤
      8 * (cellMass P x * L / (m * ε) + L ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2)) := by
    have hmass : totalMassVecFormula (cellVector P x) = cellMass P x := by
      simp [totalMassVecFormula, armMassVecFormula, cellVector, cellMass, cellIdx]; ring
    have hfloor : ε * cellMass P x ≤ armMass P a x := by
      rw [← anchoredDenom_cellVector_eq_armMass ε P hP x hp a, ← hmass]
      exact le_max_right _ _
    have h := inverseArm_coordinate_scale_sq_sum_le hp hε
      (div_nonneg (by linarith : 0 ≤ L) m.coe_nonneg)
      (show 0 ≤ jointMass P x a false from ENNReal.toReal_nonneg)
      (show 0 ≤ jointMass P x a true from ENNReal.toReal_nonneg)
      (show jointMass P x a false + jointMass P x a true = armMass P a x by
        simp [armMass, jointMass]; ring) hfloor
    convert h using 1 <;> simp [mul_div_assoc] <;> first | rfl | (ring <;> simp)
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset Bool)) => hscale a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
    Nat.cast_ofNat] at hsum
  apply hb.trans
  have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 64 * C by dsimp [C]; positivity)
  convert h using 1 <;> dsimp only [C] <;> first | rfl | ring

open Classical in
/-- The center-error first moment on failed rectangles follows from its normalized second moment and the exponentially small failure probability. This completes the center component of roadmap (22), retaining the square root of one inverse-overlap power in the mass term. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hP,hp,m,hm,hHpos,hH,hL,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_cellValue_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ε : ℝ) (P : DiscreteLaw d) (hε : 0 < ε)
    (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (W : Fin 4 → Ω → ℕ) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ) :
    (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      |armwiseExtensionFormula ε (pilotMidpoint H hHpos m L (fun j => W j ω)) -
        armwiseExtensionFormula ε (cellVector P x)| else 0 ∂μ) ≤
      Real.sqrt (8 * (1024 * Real.sqrt (8 * scalarMomentConstant 4) *
        (H / universalH) ^ 2)) * Real.exp (-30 * L) *
        (Real.sqrt (cellMass P x * L / (m * ε)) + L / (m * ε)) := by
  classical
  let q : Fin 4 → ℝ≥0 := fun j => ⟨cellVector P x j, ENNReal.toReal_nonneg⟩
  let B : Set Ω := {ω | cellVector P x ∉ pilotRectangle
    (pilotLower H hHpos m L (fun j => W j ω))
    (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  let S : Ω → ℝ := fun ω => |armwiseExtensionFormula ε
    (pilotMidpoint H hHpos m L (fun j => W j ω)) -
      armwiseExtensionFormula ε (cellVector P x)|
  let C : ℝ := 1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2
  let a : ℝ := cellMass P x * L / (m * ε)
  let b : ℝ := L / (m * ε)
  let s : ℝ := Real.sqrt a + b
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hcenter : MemLp (fun ω => armwiseExtensionFormula ε
      (pilotMidpoint H hHpos m L (fun j => W j ω))) 2 μ := by
    have hmass := pilotTotalMass_memLp_two μ W q m hm H hHpos L hH hL hW hlaw
    apply hmass.of_le
    · first | fun_prop | exact ((Measurable.of_discrete (f := fun z : Fin 4 → ℕ =>
          armwiseExtensionFormula ε (pilotMidpoint H hHpos m L z))).comp
        (measurable_pi_lambda _ hW)).aestronglyMeasurable
    · apply ae_of_all
      intro ω
      have hb := pilotMidpoint_nonneg H hHpos m L (NNReal.coe_pos.mpr hm) (fun j => W j ω)
      have hf := armwiseExtension_nonneg_le_totalMassVec hε hb
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf.1]
      exact hf.2.trans (le_abs_self _)
  have hS : MemLp S 2 μ := (hcenter.sub (memLp_const _)).abs
  have hSn (ω : Ω) : 0 ≤ S ω := abs_nonneg _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hs : 0 ≤ s := add_nonneg (Real.sqrt_nonneg _) hb
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hprob : μ.real B ≤ 8 * Real.exp (-40 * L) := by
    have hp := pilotRectangle_bad_probability_le μ W q m hm H hHpos L hH hL hlaw
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hp).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hsecond : (∫ ω, B.indicator (fun ω => S ω ^ 2) ω ∂μ) ≤
      C * Real.exp (-20 * L) * s ^ 2 := by
    have h := pilotRectangle_bad_cellValue_normalized_le μ ε P hε hP x hp W m hm
      H hHpos L hH hL hW hlaw
    have hab : a + b ^ 2 ≤ s ^ 2 := by
      dsimp [s]
      nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
    have he : L ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2) = b ^ 2 := by dsimp [b]; ring
    simp only [he, ← mul_assoc] at h
    change _ ≤ C * Real.exp (-20 * L) * (a + b ^ 2) at h
    simpa only [Set.indicator, B, S, Set.mem_ofPred_eq, sq_abs] using
      h.trans (mul_le_mul_of_nonneg_left hab (mul_nonneg hC (Real.exp_nonneg _)))
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := B.indicator S) (g := B.indicator (fun _ => (1 : ℝ)))
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun ω _ => hSn ω) ω)
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (by simpa using hS.indicator hB)
    (by simpa using (memLp_const (1 : ℝ) (p := (2 : ENNReal)) (μ := μ)).indicator hB)
  have hmul (ω : Ω) : B.indicator S ω * B.indicator (fun _ => (1 : ℝ)) ω =
      B.indicator S ω := by by_cases h : ω ∈ B <;> simp [h]
  have hsq (ω : Ω) : (B.indicator S ω) ^ (2 : ℝ) =
      B.indicator (fun ω => S ω ^ 2) ω := by
    by_cases h : ω ∈ B <;> simp [h]
  have hone (ω : Ω) : (B.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ) =
      B.indicator (fun _ => (1 : ℝ)) ω := by by_cases h : ω ∈ B <;> simp [h]
  simp_rw [hmul, hsq, hone, ← Real.sqrt_eq_rpow] at hholder
  rw [integral_indicator_const _ hB] at hholder
  simp only [smul_eq_mul, mul_one] at hholder
  have hbound := mul_le_mul (Real.sqrt_le_sqrt hsecond) (Real.sqrt_le_sqrt hprob)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have heq : Real.sqrt (C * Real.exp (-20 * L) * s ^ 2) *
      Real.sqrt (8 * Real.exp (-40 * L)) =
      Real.sqrt (8 * C) * Real.exp (-30 * L) * s := by
    rw [← Real.sqrt_mul (by positivity)]
    have hexp : Real.exp (-20 * L) * Real.exp (-40 * L) =
        Real.exp (-30 * L) ^ 2 := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have he : C * Real.exp (-20 * L) * s ^ 2 * (8 * Real.exp (-40 * L)) =
        (Real.sqrt (8 * C) * Real.exp (-30 * L) * s) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      rw [← hexp]
      ring
    rw [he, Real.sqrt_sq (by positivity)]
  simpa only [Set.indicator, B, S, C, s, a, b, Set.mem_ofPred_eq] using
    (hholder.trans hbound).trans_eq heq

end CausalSmith.Stat.OptvalueVanishingoverlapRate
