module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.AdmissibleOutcomeTail
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BalancedMeasurability
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.AnalysisScale
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountAdmissibility
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.QuadraticTilt
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.SelectedScaleUnion
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.SelectedScaleNormalization
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.TailExpectation
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Risk
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_FiniteBandwidth
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.MeasureTheory.Integral.Gamma

/-! # Probability and integration bounds for count-based adaptation

The analysis-scale count failure and selected-level outcome tails assemble
roadmap (6)--(11). The final rate theorem imports these supporting bounds.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal

-- @node: selectorHandle_range
/-- The selected fit and the empty-grid fallback both stay in the outcome range. -/
lemma selectorHandle_range {d n : ℕ} (sample : Fin n → Obs d)
    (β M : ℝ) (hM : 0 ≤ M) (x : Fin d → ℝ) :
    selectorHandle sample β M x ∈ Set.Icc (-M) M := by
  classical
  unfold selectorHandle
  split_ifs
  · exact balancedEstimator_range sample _ β M hM x
  · exact ⟨by linarith, hM⟩

-- @node: selectorHandle_supLoss_le_two_mul
/-- The adaptive loss is bounded even when no scale is admissible. -/
lemma selectorHandle_supLoss_le_two_mul {d n : ℕ} (sample : Fin n → Obs d)
    (β γ C L M : ℝ) (P : Law d) (hP : LawClass d β γ C L M P) :
    supLoss (selectorHandle sample β M) P.mu1 ≤ ENNReal.ofReal (2 * M) := by
  apply supLoss_le_two_mul_of_range
  · intro x _
    exact selectorHandle_range sample β M hP.parameters.2.2.2.2.2.le x
  · exact hP.semantics.2.2.2.2.1

-- @node: gaussianTail_goodEvent_lintegral_le
/-- Roadmap (10)--(11): integrate the Gaussian tail on a measurable good event,
then pay the uniform loss bound times the probability of its complement. -/
lemma gaussianTail_goodEvent_lintegral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ENNReal)
    (A : Set Ω) (hA : MeasurableSet A) (hf : AEMeasurable f μ)
    (b s K c H : ℝ) (hb : 0 ≤ b) (hs : 0 < s) (hK : 0 < K)
    (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ x, f x ≤ ENNReal.ofReal H)
    (htail : ∀ u : ℝ, 1 ≤ u → u * s ≤ H →
      μ.real {x | x ∈ A ∧ ENNReal.ofReal (b + u * s) < f x} ≤
        K * Real.exp (-c * u ^ 2)) :
    (∫⁻ x, f x ∂μ) ≤ ENNReal.ofReal
      (((1 + K) * Real.exp c / c) * (b + s) + H * μ.real Aᶜ) := by
  classical
  have hindBound (x : Ω) : A.indicator f x ≤ ENNReal.ofReal H := by
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx] using hbound x
    · simp only [Set.indicator_of_notMem hx]; exact bot_le
  have hgood := gaussianTail_ennreal_lintegral_le μ (A.indicator f)
    (hf.indicator hA)
    (fun x => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hindBound x))
    b s K c hb hs hK hc (by
      intro u hu
      have hevent : {x | ENNReal.ofReal (b + u * s) < A.indicator f x} =
          {x | x ∈ A ∧ ENNReal.ofReal (b + u * s) < f x} := by
        ext x
        by_cases hx : x ∈ A <;> simp [hx]
      by_cases hcut : u * s ≤ H
      · rw [hevent]
        exact htail u hu hcut
      · have hempty : {x | ENNReal.ofReal (b + u * s) < A.indicator f x} = ∅ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact not_lt_of_ge ((hindBound x).trans
            (ENNReal.ofReal_le_ofReal (by linarith)))
        rw [hempty]
        simp only [measureReal_empty]
        positivity)
  have hbad : (∫⁻ x in Aᶜ, f x ∂μ) ≤ ENNReal.ofReal (H * μ.real Aᶜ) := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, ENNReal.ofReal H ∂μ := lintegral_mono hbound
      _ = ENNReal.ofReal H * μ Aᶜ := by simp
      _ = _ := by
        rw [show μ Aᶜ = ENNReal.ofReal (μ.real Aᶜ) from
          (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm,
          ← ENNReal.ofReal_mul hH]
  rw [← lintegral_add_compl f hA, ← lintegral_indicator hA f]
  apply (add_le_add hgood hbad).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The rank series decays exponentially in a tilt bounded below by one.
This is the analytic summation in equation (6) of the adaptation roadmap. -/
-- @node: stretchedExponentialSeries_largeTilt
lemma stretchedExponentialSeries_largeTilt (p r : ℝ) (hp : 0 < p) (hr : 1 ≤ r) :
    (∑' k : ℕ, Real.exp (-r * (k + 1 : ℝ) ^ p)) ≤
      Real.exp (-r / 2) * ∑' k : ℕ, Real.exp (-(1 / 2 : ℝ) * (k + 1 : ℝ) ^ p) := by
  have hr0 : 0 ≤ r := by linarith
  have hu : 1 ≤ Real.sqrt r := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
  have h := stretchedExponentialSeries_factor 1 p (Real.sqrt r) (by norm_num) hp hu
  simpa only [Real.sq_sqrt hr0, neg_one_mul, one_mul, neg_div] using h

/-- Ordered masses turn the count-failure union into an exponential bound
without a factor depending on the number of dyadic cells. The two displayed
scale conditions are the deterministic conditions on the analysis scale in (4)--(6). -/
-- @node: selectorAdmissible_failure_exponential
lemma selectorAdmissible_failure_exponential (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ a K c : ℝ, 0 < a ∧ 0 < K ∧ 0 < c ∧
      ∀ (P : Law d), LawClass d β γ C L M P →
        ∀ (n j : ℕ), 0 < n →
          (∀ Q : Fin d → Fin (2 ^ j), 2 * (selectorThreshold j β : ℝ) ≤
            (n : ℝ) * minimumTreatedMass P j (polynomialOrder β)
              (normingSubcells d β).radius Q) →
          1 ≤ (1 - Real.exp (-1) - 1 / 2) * (n : ℝ) * a *
            (dyadicWidth j) ^ effectiveDimension d γ →
          (P.sample n).real {sample | ¬ selectorAdmissible sample j β} ≤
            K * Real.exp (-c * (n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ) := by
  obtain ⟨a, ha, hsum⟩ := minimumTreatedMass_exponentialSum_le d β γ C L M hparam
  let δ : ℝ := 1 - Real.exp (-1) - 1 / 2
  let p : ℝ := 1 / tailExponent γ
  let S : ℝ := ∑' k : ℕ, Real.exp (-(1 / 2 : ℝ) * (k + 1 : ℝ) ^ p)
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  have hδ : 0 < δ := countTilt_one_positive
  have hp : 0 < p := one_div_pos.mpr (sub_pos.mpr hparam.2.2.1)
  have hS : 0 ≤ S := tsum_nonneg (fun _ => Real.exp_nonneg _)
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (show Nonempty (MultiIndex d (polynomialOrder β)) from inferInstance)
  refine ⟨a, R * (S + 1), δ * a / 2, ha, by positivity, by positivity, ?_⟩
  intro P hP n j hn hmean htilt
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let r : ℝ := δ * (n : ℝ) * a * (dyadicWidth j) ^ effectiveDimension d γ
  have hr : 1 ≤ r := htilt
  have hseries := stretchedExponentialSeries_largeTilt p r hp hr
  calc
    _ ≤ R * ∑ Q : Fin d → Fin (2 ^ j), Real.exp (-δ * (n : ℝ) *
        minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q) :=
      selectorAdmissible_failure_le_sum P β γ C L M hP hn j hmean
    _ ≤ R * ∑' k : ℕ, Real.exp (-r * (k + 1 : ℝ) ^ p) := by
      apply mul_le_mul_of_nonneg_left _ hR.le
      have h := hsum P hP j (δ * n) (mul_pos hδ hn')
      have heq : -(δ * (n : ℝ)) * (a * (dyadicWidth j) ^ effectiveDimension d γ) = -r := by
        dsimp [r]; ring
      simpa only [heq, neg_mul, p] using h
    _ ≤ R * (Real.exp (-r / 2) * S) := mul_le_mul_of_nonneg_left hseries hR.le
    _ ≤ (R * (S + 1)) * Real.exp (-r / 2) := by
      have h := mul_le_mul_of_nonneg_left (show S ≤ S + 1 by linarith)
        (mul_nonneg hR.le (Real.exp_nonneg (-r / 2)))
      nlinarith only [h]
    _ = _ := by
      congr 2
      dsimp [r]
      ring

/-- Equation (6) under a single deterministic scale condition: ordered
masses ensure all expected counts exceed twice the threshold. -/
-- @node: selectorAdmissible_failure_of_analysisScale
lemma selectorAdmissible_failure_of_analysisScale (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ a K c : ℝ, 0 < a ∧ 0 < K ∧ 0 < c ∧
      ∀ (P : Law d), LawClass d β γ C L M P →
        ∀ (n j : ℕ), 0 < n →
          2 * (selectorThreshold j β : ℝ) ≤ (n : ℝ) * a *
            (dyadicWidth j) ^ effectiveDimension d γ →
          (P.sample n).real {sample | ¬ selectorAdmissible sample j β} ≤
            K * Real.exp (-c * (n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ) := by
  obtain ⟨a₁, ha₁, hlower⟩ := minimumTreatedMass_uniform_lower d β γ C L M hparam
  obtain ⟨a₂, K, c, ha₂, hK, hc, hfailure⟩ :=
    selectorAdmissible_failure_exponential d β γ C L M hparam
  let δ : ℝ := 1 - Real.exp (-1) - 1 / 2
  let a : ℝ := min a₁ (δ * a₂)
  have hδ : 0 < δ := countTilt_one_positive
  have ha : 0 < a := lt_min ha₁ (mul_pos hδ ha₂)
  refine ⟨a, K, c, ha, hK, hc, ?_⟩
  intro P hP n j hn hscale
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hw : 0 ≤ (dyadicWidth j) ^ effectiveDimension d γ := by positivity
  apply hfailure P hP n j hn
  · intro Q
    calc
      _ ≤ (n : ℝ) * a * (dyadicWidth j) ^ effectiveDimension d γ := hscale
      _ ≤ (n : ℝ) * a₁ * (dyadicWidth j) ^ effectiveDimension d γ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) hn') hw
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hlower P hP j Q) hn'
  · have hthreshold : 1 ≤ (selectorThreshold j β : ℝ) := by
      have h := selectorThreshold_lower j β
      have hw1 : dyadicWidth j ≤ 1 := by
        unfold dyadicWidth
        exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
      have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hw1
        (show -(2 * β) ≤ 0 by linarith [hparam.2.1])
      exact hp.trans h
    have hmono := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_right a₁ (δ * a₂)) hn') hw
    change 1 ≤ δ * (n : ℝ) * a₂ * (dyadicWidth j) ^ effectiveDimension d γ
    nlinarith only [hscale, hthreshold, hmono]

/-- Roadmap (9): the integral test and the Gamma integral control the
rank series for every positive tilt, including tilts smaller than one. -/
-- @node: stretchedExponentialSeries_smallTilt
lemma stretchedExponentialSeries_smallTilt (p r : ℝ) (hp : 0 < p) (hr : 0 < r) :
    (∑' k : ℕ, Real.exp (-r * (k + 1 : ℝ) ^ p)) ≤
      r ^ (-(1 / p)) * (1 / p) * Real.Gamma (1 / p) := by
  let f : ℝ → ℝ := fun x => Real.exp (-r * x ^ p)
  have hanti : AntitoneOn f (Set.Ici 0) := by
    intro x hx y _ hxy
    apply Real.exp_monotone
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx hxy hp.le) hr.le)
  have hint : IntegrableOn f (Set.Ioi 0) := by
    simpa only [f, Real.rpow_zero, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := p) (s := 0) (b := r)
        (by norm_num) hp hr)
  have hsum := hanti.tsum_add_one_le_integral hint (fun _ _ => Real.exp_nonneg _)
  have heval : (∫ x in Set.Ioi (0 : ℝ), f x) =
      r ^ (-(1 / p)) * (1 / p) * Real.Gamma (1 / p) := by
    simpa only [f, Real.rpow_zero, one_mul, zero_add, neg_div] using
      (integral_rpow_mul_exp_neg_mul_rpow (p := p) (q := 0) (b := r)
        hp (by norm_num) hr)
  rw [heval] at hsum
  simpa only [f, Nat.cast_add, Nat.cast_one] using hsum

/-- Equation (9) applied to the actual ordered subcell masses yields the
polynomial tilt bound used in the selected-scale union bound (8)--(10). -/
-- @node: minimumTreatedMass_exponentialSum_smallTilt
lemma minimumTreatedMass_exponentialSum_smallTilt (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ a : ℝ, 0 < a ∧ ∀ (P : Law d), LawClass d β γ C L M P →
      ∀ (j : ℕ) (r : ℝ), 0 < r →
        (∑ Q : Fin d → Fin (2 ^ j), Real.exp (-r *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q)) ≤
        (r * (a * (dyadicWidth j) ^ effectiveDimension d γ)) ^ (-tailExponent γ) *
          tailExponent γ * Real.Gamma (tailExponent γ) := by
  obtain ⟨a, ha, hsum⟩ := minimumTreatedMass_exponentialSum_le d β γ C L M hparam
  refine ⟨a, ha, ?_⟩
  intro P hP j r hr
  have hq : 0 < tailExponent γ := sub_pos.mpr hparam.2.2.1
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have htilt : 0 < r * (a * (dyadicWidth j) ^ effectiveDimension d γ) := by positivity
  have h := stretchedExponentialSeries_smallTilt (1 / tailExponent γ)
    (r * (a * (dyadicWidth j) ^ effectiveDimension d γ)) (one_div_pos.mpr hq) htilt
  have hinv : 1 / (1 / tailExponent γ) = tailExponent γ := by simp
  rw [hinv] at h
  apply (hsum P hP j r hr).trans
  simpa only [neg_mul, mul_assoc] using h

/-- Summing the admissible-count Laplace bound and using equation (9)
controls all cells with no factor equal to the number of cells. This is the
count component of equations (7)--(8); the outcome-noise bound is separate. -/
-- @node: admissible_count_laplace_sum_smallTilt
lemma admissible_count_laplace_sum_smallTilt (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ a : ℝ, 0 < a ∧ ∀ (P : Law d), LawClass d β γ C L M P →
      ∀ (n j : ℕ), 0 < n → ∀ (s : ℝ), 0 < s →
        (∑ Q : Fin d → Fin (2 ^ j), ∫ sample,
          {sample | selectorAdmissible sample j β}.indicator
            (fun sample => Real.exp (-s * (minimumCellCount sample true j
              (polynomialOrder β) (normingSubcells d β).radius Q : ℝ))) sample
              ∂P.sample n) ≤
          Real.exp (-s * (selectorThreshold j β : ℝ) / 2) *
            (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) *
              (((n : ℝ) * (1 - Real.exp (-(s / 2))) *
                (a * (dyadicWidth j) ^ effectiveDimension d γ)) ^ (-tailExponent γ) *
                  tailExponent γ * Real.Gamma (tailExponent γ)) := by
  classical
  obtain ⟨a, ha, hsum⟩ := minimumTreatedMass_exponentialSum_smallTilt
    d β γ C L M hparam
  refine ⟨a, ha, ?_⟩
  intro P hP n j hn s hs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 < 1 - Real.exp (-(s / 2)) := by
    have hlt : Real.exp (-(s / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  let E : ℝ := Real.exp (-s * (selectorThreshold j β : ℝ) / 2)
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  calc
    _ ≤ ∑ Q : Fin d → Fin (2 ^ j), E * (R *
        Real.exp (-(n : ℝ) * minimumTreatedMass P j (polynomialOrder β)
          (normingSubcells d β).radius Q * (1 - Real.exp (-(s / 2))))) := by
      apply Finset.sum_le_sum
      intro Q _
      exact admissible_count_laplace_split P β γ C L M hP hn j Q s hs.le
    _ = (E * R) * ∑ Q : Fin d → Fin (2 ^ j),
        Real.exp (-((n : ℝ) * (1 - Real.exp (-(s / 2)))) *
          minimumTreatedMass P j (polynomialOrder β) (normingSubcells d β).radius Q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      rw [← mul_assoc]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (hsum P hP j ((n : ℝ) * (1 - Real.exp (-(s / 2)))) (mul_pos hn' hδ))
        (mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg _))

/-- Roadmap (4)--(6) with the analysis scale constructed, including grid
membership and a uniform exponential bound for its inadmissibility. The
multiplier depends on the tail class only in the analysis, never in the selector. -/
-- @node: selector_analysisScale_failure
lemma selector_analysisScale_failure (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ A K c : ℝ, 1 ≤ A ∧ 0 < K ∧ 0 < c ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → 1 ≤ n → ∃ j : ℕ,
        j ≤ selectorMaxLevel d n β ∧
        A * rateWidth d n β γ ≤ dyadicWidth j ∧
        dyadicWidth j < 2 * A * rateWidth d n β γ ∧
        ∀ P : Law d, LawClass d β γ C L M P →
          (P.sample n).real {sample | ¬ selectorAdmissible sample j β} ≤
            K * Real.exp (-c * (n : ℝ) * (dyadicWidth j) ^ effectiveDimension d γ) := by
  obtain ⟨a, K, c, ha, hK, hc, hfailure⟩ :=
    selectorAdmissible_failure_of_analysisScale d β γ C L M hparam
  have hden : 0 < 2 * β + effectiveDimension d γ := by
    have := effectiveDimension_pos hparam.1 hparam.2.2.1
    linarith [hparam.2.1]
  obtain ⟨A, hA, hlarge⟩ := analysisMultiplier_exists ha hden
  obtain ⟨N, hscale⟩ := analysisScale_exists hparam.1 hparam.2.1 hparam.2.2.1
    ha hA hlarge
  refine ⟨A, K, c, hA, hK, hc, N, ?_⟩
  intro n hn hn1
  obtain ⟨j, hgrid, hlo, hhi, hcount⟩ := hscale n hn hn1
  refine ⟨j, hgrid, hlo, hhi, ?_⟩
  intro P hP
  exact hfailure P hP n j (by omega) hcount

/-- The constructed analysis scale has a measurable admissibility event
whose failure probability is eventually bounded by the target rate. This
closes the bad-event term after roadmap (11), uniformly over the law class. -/
-- @node: selector_analysisScale_failure_rate
lemma selector_analysisScale_failure_rate (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 < K ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → 1 ≤ n → ∃ j : ℕ,
        j ≤ selectorMaxLevel d n β ∧
        A * rateWidth d n β γ ≤ dyadicWidth j ∧
        dyadicWidth j < 2 * A * rateWidth d n β γ ∧
        MeasurableSet {sample : Fin n → Obs d | selectorAdmissible sample j β} ∧
        ∀ P : Law d, LawClass d β γ C L M P →
          (P.sample n).real {sample | ¬ selectorAdmissible sample j β} ≤
            K * rate d n β γ := by
  obtain ⟨A, K, c, hA, hK, hc, Nscale, hscale⟩ :=
    selector_analysisScale_failure d β γ C L M hparam
  obtain ⟨Nexp, hexp⟩ := analysisScale_exponential_le_rate
    hparam.1 hparam.2.1 hparam.2.2.1 hc
  refine ⟨A, K, hA, hK, max Nscale Nexp, ?_⟩
  intro n hn hn1
  obtain ⟨j, hgrid, hlo, hhi, hbad⟩ :=
    hscale n ((le_max_left _ _).trans hn) hn1
  refine ⟨j, hgrid, hlo, hhi, selectorAdmissible_measurableSet d n j β, ?_⟩
  intro P hP
  apply (hbad P hP).trans
  apply mul_le_mul_of_nonneg_left _ hK.le
  apply hexp n ((le_max_right _ _).trans hn) hn1 j
  have hw : 0 ≤ rateWidth d n β γ := by unfold rateWidth; positivity
  have hwide : rateWidth d n β γ ≤ A * rateWidth d n β γ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hw
  exact hwide.trans hlo

/-- Ranking the actual masses and applying the Gamma integral completes
roadmap (8)--(9) for the loss of the selector on a specified selected level. -/
-- @node: selectorHandle_selectedLevel_smallTilt
lemma selectorHandle_selectedLevel_smallTilt (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B c a : ℝ, 0 < B ∧ 0 < c ∧ 0 < a ∧ ∀ (n j : ℕ) (P : Law d),
      LawClass d β γ C L M P → 0 < n → ∀ t : ℝ, 0 < t →
        (P.sample n).real {sample |
          (∃ h : (admissibleLevels sample β).Nonempty,
            (admissibleLevels sample β).max' h = j) ∧
          ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t) <
            supLoss (selectorHandle sample β M) P.mu1} ≤
          (2 * (Fintype.card (MultiIndex d (polynomialOrder β)) : ℝ) ^ 2) *
            Real.exp (-(c * t ^ 2 / M ^ 2) * (selectorThreshold j β : ℝ) / 2) *
              (((n : ℝ) * (1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2))) *
                (a * (dyadicWidth j) ^ effectiveDimension d γ)) ^ (-tailExponent γ) *
                  tailExponent γ * Real.Gamma (tailExponent γ)) := by
  obtain ⟨B, c, hB, hc, htail⟩ := selectorHandle_selectedLevel_tail
    d β γ C L M hparam
  obtain ⟨a, ha, hsum⟩ := minimumTreatedMass_exponentialSum_smallTilt
    d β γ C L M hparam
  refine ⟨B, c, a, hB, hc, ha, ?_⟩
  intro n j P hP hn t ht
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hM : 0 < M := hparam.2.2.2.2.2
  have hs : 0 < c * t ^ 2 / M ^ 2 / 2 := by positivity
  have hδ : 0 < 1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2)) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)
    linarith
  apply (htail n j P hP hn t ht.le).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := hsum P hP j
    ((n : ℝ) * (1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2)))) (mul_pos hn' hδ)
  convert h using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro Q _
  congr 1
  ring

/-- Roadmap (8) with the actual binomial half-tilt replaced by a quadratic
power and the count threshold replaced by the bandwidth power. All constants
are uniform in the selected level, law, sample size, and bounded deviation. -/
-- @node: selectorHandle_selectedLevel_quadraticTail
lemma selectorHandle_selectedLevel_quadraticTail (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B K c a : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧ 0 < a ∧
      ∀ (n j : ℕ) (P : Law d), LawClass d β γ C L M P → 0 < n →
        ∀ t : ℝ, 0 < t → t ≤ 2 * M →
          (P.sample n).real {sample |
            (∃ h : (admissibleLevels sample β).Nonempty,
              (admissibleLevels sample β).max' h = j) ∧
            ENNReal.ofReal (B * L * (dyadicWidth j) ^ β + t) <
              supLoss (selectorHandle sample β M) P.mu1} ≤
            K * Real.exp (-c * t ^ 2 / M ^ 2 *
              (dyadicWidth j) ^ (-(2 * β))) *
              ((n : ℝ) * a * (dyadicWidth j) ^ effectiveDimension d γ *
                (t ^ 2 / M ^ 2)) ^ (-tailExponent γ) := by
  obtain ⟨B, c, a, hB, hc, ha, htail⟩ :=
    selectorHandle_selectedLevel_smallTilt d β γ C L M hparam
  have hM : 0 < M := hparam.2.2.2.2.2
  have hq : 0 < tailExponent γ := sub_pos.mpr hparam.2.2.1
  obtain ⟨k, hk, hpower⟩ := quadraticHalfTilt_inversePower_le c M
    (tailExponent γ) hc hM hq
  let R : ℝ := Fintype.card (MultiIndex d (polynomialOrder β))
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (show Nonempty (MultiIndex d (polynomialOrder β)) from inferInstance)
  have hGamma : 0 < Real.Gamma (tailExponent γ) := Real.Gamma_pos_of_pos hq
  refine ⟨B, 2 * R ^ 2 * (tailExponent γ * Real.Gamma (tailExponent γ)),
    c / 2, a * k, hB, by positivity, by positivity, by positivity, ?_⟩
  intro n j P hP hn t ht htM
  have hw : 0 < (n : ℝ) * (a * (dyadicWidth j) ^ effectiveDimension d γ) := by
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
    positivity
  have hp := hpower t ((n : ℝ) *
    (a * (dyadicWidth j) ^ effectiveDimension d γ)) ht htM hw
  have hexp : Real.exp (-(c * t ^ 2 / M ^ 2) *
      (selectorThreshold j β : ℝ) / 2) ≤
      Real.exp (-(c / 2) * t ^ 2 / M ^ 2 *
        (dyadicWidth j) ^ (-(2 * β))) := by
    apply Real.exp_monotone
    have h := mul_le_mul_of_nonneg_left (selectorThreshold_lower j β)
      (show 0 ≤ c * t ^ 2 / M ^ 2 / 2 by positivity)
    convert neg_le_neg h using 1 <;> ring
  have hδ : 0 < 1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2)) := by
    have hlt := Real.exp_lt_one_iff.mpr
      (neg_neg_of_pos (show 0 < c * t ^ 2 / M ^ 2 / 2 by positivity))
    linarith
  have hbase : (n : ℝ) * (a * (dyadicWidth j) ^ effectiveDimension d γ) *
      (k * t ^ 2 / M ^ 2) =
      (n : ℝ) * (a * k) * (dyadicWidth j) ^ effectiveDimension d γ *
        (t ^ 2 / M ^ 2) := by ring
  rw [hbase] at hp
  apply (htail n j P hP hn t ht).trans
  have hboth := mul_le_mul hexp hp
    (Real.rpow_pos_of_pos (mul_pos hw hδ) _).le (Real.exp_nonneg _)
  have h := mul_le_mul_of_nonneg_left hboth
    (show 0 ≤ 2 * R ^ 2 * (tailExponent γ * Real.Gamma (tailExponent γ)) by positivity)
  have hbase' : (n : ℝ) * (1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2))) *
      (a * (dyadicWidth j) ^ effectiveDimension d γ) =
      (n : ℝ) * (a * (dyadicWidth j) ^ effectiveDimension d γ) *
        (1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2))) := by ring
  rw [hbase']
  convert h using 1 <;> dsimp [R] <;> ring

/-- The probabilistic assembly of (8)--(10), before deterministic scale
normalization. No factor proportional to the size of the selector grid appears. -/
-- @node: selectorHandle_goodEvent_quadraticTail_sum
lemma selectorHandle_goodEvent_quadraticTail_sum (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B K c a : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧ 0 < a ∧
      ∀ (n j₀ : ℕ) (P : Law d), LawClass d β γ C L M P → 0 < n →
        j₀ ≤ selectorMaxLevel d n β →
        ∀ t : ℝ, 0 < t → t ≤ 2 * M →
          (P.sample n).real {sample | selectorAdmissible sample j₀ β ∧
            ENNReal.ofReal (B * L * (dyadicWidth j₀) ^ β + t) <
              supLoss (selectorHandle sample β M) P.mu1} ≤
            ∑ j ∈ Finset.Icc j₀ (selectorMaxLevel d n β),
              K * Real.exp (-c * t ^ 2 / M ^ 2 *
                (dyadicWidth j) ^ (-(2 * β))) *
                ((n : ℝ) * a * (dyadicWidth j) ^ effectiveDimension d γ *
                  (t ^ 2 / M ^ 2)) ^ (-tailExponent γ) := by
  obtain ⟨B, K, c, a, hB, hK, hc, ha, htail⟩ :=
    selectorHandle_selectedLevel_quadraticTail d β γ C L M hparam
  refine ⟨B, K, c, a, hB, hK, hc, ha, ?_⟩
  intro n j₀ P hP hn hgrid t ht htM
  apply (selectorHandle_goodEvent_le_selectedLevel_sum P β γ C L M hP
    hn j₀ hgrid B t hB.le).trans
  apply Finset.sum_le_sum
  intro j _
  exact htail n j P hP hn t ht htM

/-- Roadmap (10) for the actual adaptive loss, at any analysis level whose
sample balance is at least one. The constant is independent of the grid size. -/
-- @node: selectorHandle_goodEvent_gaussianTail
lemma selectorHandle_goodEvent_gaussianTail (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ B K c : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧
      ∀ (n j₀ : ℕ) (P : Law d), LawClass d β γ C L M P → 0 < n →
        j₀ ≤ selectorMaxLevel d n β →
        1 ≤ (n : ℝ) * (dyadicWidth j₀) ^ (effectiveDimension d γ + 2 * β) →
        ∀ u : ℝ, 1 ≤ u → u * M * (dyadicWidth j₀) ^ β ≤ 2 * M →
          (P.sample n).real {sample | selectorAdmissible sample j₀ β ∧
            ENNReal.ofReal (B * L * (dyadicWidth j₀) ^ β +
              u * M * (dyadicWidth j₀) ^ β) <
                supLoss (selectorHandle sample β M) P.mu1} ≤
            K * Real.exp (-c * u ^ 2) := by
  obtain ⟨B, K, c, a, hB, hK, hc, ha, htail⟩ :=
    selectorHandle_goodEvent_quadraticTail_sum d β γ C L M hparam
  have hq : 0 < tailExponent γ := sub_pos.mpr hparam.2.2.1
  obtain ⟨G, hG, hseries⟩ := selectedScale_quadratic_interval_gaussianTail
    β (effectiveDimension d γ) (tailExponent γ) c hparam.2.1 hq hc
  refine ⟨B, K * a ^ (-tailExponent γ) * G, c / 2,
    hB, by positivity, by positivity, ?_⟩
  intro n j₀ P hP hn hgrid hbalance u hu hcut
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh : 0 < dyadicWidth j₀ := by unfold dyadicWidth; positivity
  have hM : 0 < M := hparam.2.2.2.2.2
  have ht : 0 < u * M * (dyadicWidth j₀) ^ β := by positivity
  have hpower : ((n : ℝ) * a * (dyadicWidth j₀) ^
      (effectiveDimension d γ + 2 * β)) ^ (-tailExponent γ) ≤
      a ^ (-tailExponent γ) := by
    apply Real.rpow_le_rpow_of_nonpos ha
    · nlinarith [mul_le_mul_of_nonneg_left hbalance ha.le]
    · linarith
  apply (htail n j₀ P hP hn hgrid _ ht hcut).trans
  apply (hseries j₀ (selectorMaxLevel d n β) ((n : ℝ) * a) M K u
    (by positivity) hM hK.le hu).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpower hK.le)
    (show 0 ≤ G * Real.exp (-c * u ^ 2 / 2) by positivity)
  have he : -c * u ^ 2 / 2 = -(c / 2) * u ^ 2 := by ring
  simpa only [he, mul_assoc] using h

end CausalSmith.Stat.GlobalTailDesignRobustCate
