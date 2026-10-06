module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_LowerPairMembership
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.TwoLawRisk
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BandwidthRate

/-! # Sharp minimax lower bound

The binary witnesses separate at the cube corner. Evaluating any measurable
curve estimator there gives the two-law metric reduction of (S15)--(S18).
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory InformationTheory
open scoped ENNReal

/-- Risk at the lower cube corner is bounded by the full sup-norm risk. -/
-- @node: cornerRisk_le_lawRisk
lemma cornerRisk_le_lawRisk {d n : ℕ} (P : Law d)
    (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ) :
    (∫⁻ s, ENNReal.ofReal (dist (f s (fun _ => 0)) (P.mu1 (fun _ => 0)))
      ∂P.sample n) ≤ lawRisk P f P.mu1 := by
  apply lintegral_mono
  intro s
  have hzero : (fun _ : Fin d => (0 : ℝ)) ∈ cube d := by
    intro i hi
    exact ⟨le_rfl, by norm_num⟩
  exact (show ENNReal.ofReal (dist (f s (fun _ => 0)) (P.mu1 (fun _ => 0))) ≤
    supLoss (f s) P.mu1 from by
      simpa only [Real.dist_eq, supLoss] using
        (le_iSup (fun x : cube d => ENNReal.ofReal |f s x - P.mu1 x|) ⟨_, hzero⟩))

/-- A pair in the law class with KL at most one sixteenth forces the
roadmap's three-sixteenths separation floor for every admissible estimator. -/
-- @node: lowerPair_minimax_bound
lemma lowerPair_minimax_bound (d n j : ℕ) (β γ C L M δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ M / 4)
    (hp : LawClass d β γ C L M
      (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M true))
    (hm : LawClass d β γ C L M
      (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M false))
    (hKL : klDiv
      (Measure.pi (fun _ : Fin n =>
        (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M true).obs))
      (Measure.pi (fun _ : Fin n =>
        (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M false).obs)) ≤
        ENNReal.ofReal (1 / 16 : ℝ)) :
    ENNReal.ofReal (3 * δ * (dyadicWidth j) ^ β / 8) ≤
      minimaxRisk d n β γ C L M := by
  let Pp := lowerPair d β (tailExponent γ) (dyadicWidth j) δ M true
  let Pm := lowerPair d β (tailExponent γ) (dyadicWidth j) δ M false
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hh1 : dyadicWidth j ≤ 1 := by
    unfold dyadicWidth
    rw [one_div]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hq : 0 < tailExponent γ := by
    unfold tailExponent
    linarith [hp.parameters.2.2.1]
  have hprob (sign : Bool) : IsProbabilityMeasure
      (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M sign).obs :=
    lowerPair_obs_isProbabilityMeasure d β (tailExponent γ) (dyadicWidth j) δ M
      hp.parameters.1 hq hp.parameters.2.1 hδ.le hh hh1
      hp.parameters.2.2.2.2.2 hsmall sign
  letI : IsProbabilityMeasure Pp.obs := hprob true
  letI : IsProbabilityMeasure Pm.obs := hprob false
  have hsamp (sign : Bool) :
      (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M sign).sample n =
      Measure.pi (fun _ : Fin n =>
        (lowerPair d β (tailExponent γ) (dyadicWidth j) δ M sign).obs) := rfl
  have hKL' : klDiv (Pp.sample n) (Pm.sample n) ≤ ENNReal.ofReal (1 / 16 : ℝ) := hKL
  have hfin : klDiv (Pp.sample n) (Pm.sample n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL'
  have hroot : Real.sqrt ((klDiv (Pp.sample n) (Pm.sample n)).toReal) ≤ 1 / 4 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL'
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16)] at ht
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith⟩
  have hgap : dist (Pp.mu1 (fun _ => 0)) (Pm.mu1 (fun _ => 0)) =
      2 * δ * (dyadicWidth j) ^ β := by
    change dist (witnessMean d β δ (dyadicWidth j) true (fun _ => 0))
      (witnessMean d β δ (dyadicWidth j) false (fun _ => 0)) = _
    simp only [Real.dist_eq, witnessMean, Bool.false_eq_true, ↓reduceIte,
      zero_div, witnessBump_zero, mul_one, one_mul]
    rw [show δ * (dyadicWidth j) ^ β - -1 * δ * (dyadicWidth j) ^ β =
      2 * δ * (dyadicWidth j) ^ β by ring, abs_of_pos (by positivity)]
  unfold minimaxRisk
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  letI : IsProbabilityMeasure (Pp.sample n) := by rw [hsamp true]; infer_instance
  letI : IsProbabilityMeasure (Pm.sample n) := by rw [hsamp false]; infer_instance
  have htwo := two_law_metric_risk (Pp.sample n) (Pm.sample n)
    (Pp.mu1 (fun _ => 0)) (Pm.mu1 (fun _ => 0))
    ⟨fun s => f s (fun _ => 0), hf.1 _⟩ (by rw [hgap]; positivity) hfin
  have hfloor : ENNReal.ofReal (3 * δ * (dyadicWidth j) ^ β / 8) ≤
      max (lawRisk Pp f Pp.mu1) (lawRisk Pm f Pm.mu1) := by
    apply le_trans _ (htwo.trans (max_le_max
      (cornerRisk_le_lawRisk Pp f) (cornerRisk_le_lawRisk Pm f)))
    apply ENNReal.ofReal_le_ofReal
    rw [hgap]
    have ha : 0 < δ * (dyadicWidth j) ^ β := by positivity
    nlinarith
  apply hfloor.trans
  apply max_le
  · exact le_iSup_of_le Pp (le_iSup_of_le hp le_rfl)
  · exact le_iSup_of_le Pm (le_iSup_of_le hm le_rfl)

/-- Choose the fixed scale multiplier in roadmap (S13). -/
-- @node: small_kl_scale
lemma small_kl_scale {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ K * a ^ t ≤ 1 / 16 := by
  let a := min 1 ((1 / (16 * K)) ^ t⁻¹)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  refine ⟨a, ha, min_le_left _ _, ?_⟩
  have hpow : a ^ t ≤ 1 / (16 * K) := by
    calc
      a ^ t ≤ ((1 / (16 * K)) ^ t⁻¹) ^ t :=
        Real.rpow_le_rpow ha.le (min_le_right _ _) ht.le
      _ = _ := Real.rpow_inv_rpow (by positivity) ht.ne'
  have := mul_le_mul_of_nonneg_left hpow hK.le
  have hcancel : K * (1 / (16 * K)) = 1 / 16 := by field_simp
  rwa [hcancel] at this

/-- The continuous balancing width cancels the sample-size factor in KL. -/
-- @node: rateWidth_information_eq
lemma rateWidth_information_eq {d n : ℕ} {β γ : ℝ}
    (hn : 1 ≤ n) (ht : 2 * β + effectiveDimension d γ ≠ 0) :
    (n : ℝ) * (rateWidth d n β γ) ^ (2 * β + effectiveDimension d γ) = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold rateWidth
  rw [← Real.rpow_mul hn'.le]
  have hexp : (-1 / (2 * β + effectiveDimension d γ)) *
      (2 * β + effectiveDimension d γ) = -1 := by field_simp
  rw [hexp, Real.rpow_neg_one, mul_inv_cancel₀ hn'.ne']

/-- The fixed-class binary witnesses force the sharp minimax lower rate,
by the small KL scale, dyadic rounding, and the two-law risk floor. -/
-- @node: minimax_lower_rate
lemma minimax_lower_rate (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * rate d n β γ) ≤ minimaxRisk d n β γ C L M := by
  obtain ⟨δ₀, K, hδ₀, hK, hpair⟩ := lower_pair_membership d β γ C L M hparam
  have ht : 0 < 2 * β + effectiveDimension d γ := by
    have := effectiveDimension_pos hparam.1 hparam.2.2.1
    linarith [hparam.2.1]
  obtain ⟨a, ha, ha1, hbudget⟩ := small_kl_scale hK ht
  let δ := min δ₀ (M / 4)
  have hδ : 0 < δ := lt_min hδ₀ (by linarith [hparam.2.2.2.2.2])
  refine ⟨3 * δ * (a / 2) ^ β / 8, by positivity, ?_⟩
  intro n hn
  have hw : 0 < rateWidth d n β γ := by unfold rateWidth; positivity
  have hw1 : rateWidth d n β γ ≤ 1 := by
    unfold rateWidth
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
    exact (div_neg_of_neg_of_pos (by norm_num) ht).le
  let j := Nat.ceil (Real.log (a * rateWidth d n β γ)⁻¹ / Real.log 2)
  have hround : a * rateWidth d n β γ / 2 < dyadicWidth j ∧
      dyadicWidth j ≤ a * rateWidth d n β γ :=
    dyadicWidth_rounding (mul_pos ha hw) ((mul_le_mul_of_nonneg_left hw1 ha.le).trans
      (by simpa using ha1))
  obtain ⟨hp, hm, hsep, hkl⟩ := hpair δ j n hδ (min_le_left _ _) hn
  have hinfo : K * (n : ℝ) * (dyadicWidth j) ^
      (2 * β + effectiveDimension d γ) ≤ 1 / 16 := by
    calc
      _ ≤ K * (n : ℝ) * (a * rateWidth d n β γ) ^
          (2 * β + effectiveDimension d γ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow (by unfold dyadicWidth; positivity) hround.2 ht.le
      _ = K * a ^ (2 * β + effectiveDimension d γ) := by
        rw [Real.mul_rpow ha.le hw.le]
        have hc := rateWidth_information_eq (d := d) (β := β) (γ := γ) hn ht.ne'
        calc
          _ = K * a ^ (2 * β + effectiveDimension d γ) *
              ((n : ℝ) * (rateWidth d n β γ) ^ (2 * β + effectiveDimension d γ)) := by ring
          _ = _ := by rw [hc, mul_one]
      _ ≤ _ := hbudget
  have hfloor := lowerPair_minimax_bound d n j β γ C L M δ hδ
    (min_le_right _ _) hp hm (hkl.trans (ENNReal.ofReal_le_ofReal hinfo))
  apply le_trans _ hfloor
  apply ENNReal.ofReal_le_ofReal
  have hb : (a / 2) ^ β * rate d n β γ ≤ (dyadicWidth j) ^ β := by
    rw [← rateWidth_bias_eq hn, ← Real.mul_rpow (by positivity) hw.le]
    apply Real.rpow_le_rpow (by positivity) _ hparam.2.1.le
    nlinarith [hround.1]
  have := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3 * δ / 8 by positivity)
  nlinarith

end CausalSmith.Stat.GlobalTailDesignRobustCate
