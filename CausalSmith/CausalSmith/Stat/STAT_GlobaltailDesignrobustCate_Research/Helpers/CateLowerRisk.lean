module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerExchangeability
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.MinimaxLower

/-! # Two-law reduction for the compatible zero-control CATE subclass

The corner evaluation and Pinsker risk floor implement (C33). The dyadic
scale assembly implements (C32), keeping the compatible-witness information
bound as an explicit obligation rather than assuming it in the paper theorem.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory InformationTheory
open scoped ENNReal

/-- Risk at the lower cube corner is bounded by the full sup-norm risk. -/
-- @node: cornerCATERisk_le_lawRisk
lemma cornerCATERisk_le_lawRisk {d n : ℕ} (P : Law d)
    (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ) :
    (∫⁻ s, ENNReal.ofReal (dist (f s (fun _ => 0)) (P.tau (fun _ => 0)))
      ∂P.sample n) ≤ lawRisk P f P.tau := by
  apply lintegral_mono
  intro s
  have hzero : (fun _ : Fin d => (0 : ℝ)) ∈ cube d := by
    intro i hi
    exact ⟨le_rfl, by norm_num⟩
  exact (show ENNReal.ofReal (dist (f s (fun _ => 0)) (P.tau (fun _ => 0))) ≤
    supLoss (f s) P.tau from by
      simpa only [Real.dist_eq, supLoss] using
        (le_iSup (fun x : cube d => ENNReal.ofReal |f s x - P.tau x|) ⟨_, hzero⟩))

/-- A pair in the law class with KL at most one sixteenth forces the
roadmap's three-sixteenths separation floor for every admissible estimator. -/
-- @node: cateLowerPair_minimax_bound
lemma cateLowerPair_minimax_bound (d n j : ℕ) (β γ C L M κ s δ : ℝ)
    (hδ : 0 < δ)
    (hp : CATEClass d β γ C L M κ
      (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M true))
    (hm : CATEClass d β γ C L M κ
      (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M false))
    (hKL : klDiv
      (Measure.pi (fun _ : Fin n =>
        (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M true).obs))
      (Measure.pi (fun _ : Fin n =>
        (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M false).obs)) ≤
        ENNReal.ofReal (1 / 16 : ℝ)) :
    ENNReal.ofReal (3 * δ * (dyadicWidth j) ^ β / 8) ≤
      zeroControlCATERisk d n β γ C L M κ := by
  let Pp := cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M true
  let Pm := cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M false
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hprob (sign : Bool) : IsProbabilityMeasure
      (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M sign).obs := by
    have hfull : IsProbabilityMeasure
        (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M sign).full := by
      cases sign
      · exact hm.iid.1
      · exact hp.iid.1
    letI : IsProbabilityMeasure
        (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M sign).full := hfull
    have ho : Measurable (observe (d := d)) := by
      unfold observe
      apply Measurable.prodMk (by fun_prop)
      apply Measurable.prodMk (by fun_prop)
      exact Measurable.ite
        ((measurableSet_singleton true).preimage (by fun_prop))
        (by fun_prop) (by fun_prop)
    exact Measure.isProbabilityMeasure_map
      (μ := (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M sign).full)
      ho.aemeasurable
  letI : IsProbabilityMeasure Pp.obs := hprob true
  letI : IsProbabilityMeasure Pm.obs := hprob false
  have hsamp (sign : Bool) :
      (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M sign).sample n =
      Measure.pi (fun _ : Fin n =>
        (cateLowerPair d β (tailExponent γ) s (dyadicWidth j) δ M sign).obs) := rfl
  have hKL' : klDiv (Pp.sample n) (Pm.sample n) ≤ ENNReal.ofReal (1 / 16 : ℝ) := hKL
  have hfin : klDiv (Pp.sample n) (Pm.sample n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL'
  have hroot : Real.sqrt ((klDiv (Pp.sample n) (Pm.sample n)).toReal) ≤ 1 / 4 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL'
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16)] at ht
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by nlinarith⟩
  have hgap : dist (Pp.tau (fun _ => 0)) (Pm.tau (fun _ => 0)) =
      2 * δ * (dyadicWidth j) ^ β := by
    dsimp only [Pp, Pm]
    rw [cateLowerPair_tau, cateLowerPair_tau]
    change dist (witnessMean d β δ (dyadicWidth j) true (fun _ => 0))
      (witnessMean d β δ (dyadicWidth j) false (fun _ => 0)) = _
    simp only [Real.dist_eq, witnessMean, Bool.false_eq_true, ↓reduceIte,
      zero_div, witnessBump_zero, mul_one, one_mul]
    rw [show δ * (dyadicWidth j) ^ β - -1 * δ * (dyadicWidth j) ^ β =
      2 * δ * (dyadicWidth j) ^ β by ring, abs_of_pos (by positivity)]
  unfold zeroControlCATERisk
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  letI : IsProbabilityMeasure (Pp.sample n) := by rw [hsamp true]; infer_instance
  letI : IsProbabilityMeasure (Pm.sample n) := by rw [hsamp false]; infer_instance
  have htwo := two_law_metric_risk (Pp.sample n) (Pm.sample n)
    (Pp.tau (fun _ => 0)) (Pm.tau (fun _ => 0))
    ⟨fun s => f s (fun _ => 0), hf.1 _⟩ (by rw [hgap]; positivity) hfin
  have hfloor : ENNReal.ofReal (3 * δ * (dyadicWidth j) ^ β / 8) ≤
      max (lawRisk Pp f Pp.tau) (lawRisk Pm f Pm.tau) := by
    apply le_trans _ (htwo.trans (max_le_max
      (cornerCATERisk_le_lawRisk Pp f) (cornerCATERisk_le_lawRisk Pm f)))
    apply ENNReal.ofReal_le_ofReal
    rw [hgap]
    have ha : 0 < δ * (dyadicWidth j) ^ β := by positivity
    nlinarith
  apply hfloor.trans
  apply max_le
  · exact le_iSup_of_le Pp (le_iSup_of_le hp (le_iSup_of_le (show ∀ x ∈ cube d, Pp.mu0 x = 0 from fun _ _ => rfl) le_rfl))
  · exact le_iSup_of_le Pm (le_iSup_of_le hm (le_iSup_of_le (show ∀ x ∈ cube d, Pm.mu0 x = 0 from fun _ _ => rfl) le_rfl))

/-- Roadmap (C32)--(C33): an information bound for the constructed compatible
pair gives the sharp zero-control CATE lower rate. This assembly does not
assert the information bound; the caller must prove it for the actual pair. -/
-- @node: cateLowerPair_lower_rate_of_information
lemma cateLowerPair_lower_rate_of_information (d : ℕ) (β γ C L M κ δ₀ : ℝ)
    (hparam : ParameterDomain d β γ C L M) (hδ₀ : 0 < δ₀)
    (hclass : ∀ (h δ : ℝ), 0 ≤ δ → δ ≤ δ₀ → 0 < h → h ≤ 1 →
      ∀ sign : Bool,
        let P := cateLowerPair d β (tailExponent γ) (C ^ (-1 / tailExponent γ)) h δ M sign
        CATEClass d β γ C L M κ P ∧ ∀ x ∈ cube d, P.mu0 x = 0)
    (hinfo : ∀ (n j : ℕ), 1 ≤ n →
      klDiv
        ((cateLowerPair d β (tailExponent γ) (C ^ (-1 / tailExponent γ))
          (dyadicWidth j) δ₀ M true).sample n)
        ((cateLowerPair d β (tailExponent γ) (C ^ (-1 / tailExponent γ))
          (dyadicWidth j) δ₀ M false).sample n) ≤
        ENNReal.ofReal ((n : ℝ) * (dyadicWidth j) ^
          (2 * β + effectiveDimension d γ))) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * rate d n β γ) ≤
        zeroControlCATERisk d n β γ C L M κ := by
  have ht : 0 < 2 * β + effectiveDimension d γ := by
    have := effectiveDimension_pos hparam.1 hparam.2.2.1
    linarith [hparam.2.1]
  obtain ⟨a, ha, ha1, hbudget⟩ := small_kl_scale (K := 1) (by norm_num) ht
  let δ := δ₀
  have hδ : 0 < δ := hδ₀
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
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hh1 : dyadicWidth j ≤ 1 :=
    hround.2.trans ((mul_le_mul_of_nonneg_left hw1 ha.le).trans (by simpa using ha1))
  have hp := (hclass (dyadicWidth j) δ hδ.le le_rfl hh hh1 true).1
  have hm := (hclass (dyadicWidth j) δ hδ.le le_rfl hh hh1 false).1
  have hkl := hinfo n j hn
  have hinfo : (1 : ℝ) * (n : ℝ) * (dyadicWidth j) ^
      (2 * β + effectiveDimension d γ) ≤ 1 / 16 := by
    calc
      _ ≤ (1 : ℝ) * (n : ℝ) * (a * rateWidth d n β γ) ^
          (2 * β + effectiveDimension d γ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow (by unfold dyadicWidth; positivity) hround.2 ht.le
      _ = (1 : ℝ) * a ^ (2 * β + effectiveDimension d γ) := by
        rw [Real.mul_rpow ha.le hw.le]
        have hc := rateWidth_information_eq (d := d) (β := β) (γ := γ) hn ht.ne'
        calc
          _ = (1 : ℝ) * a ^ (2 * β + effectiveDimension d γ) *
              ((n : ℝ) * (rateWidth d n β γ) ^ (2 * β + effectiveDimension d γ)) := by ring
          _ = _ := by rw [hc, mul_one]
      _ ≤ _ := hbudget
  have hfloor := cateLowerPair_minimax_bound d n j β γ C L M κ
    (C ^ (-1 / tailExponent γ)) δ hδ hp hm (hkl.trans (ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hinfo)))
  apply le_trans _ hfloor
  apply ENNReal.ofReal_le_ofReal
  have hb : (a / 2) ^ β * rate d n β γ ≤ (dyadicWidth j) ^ β := by
    rw [← rateWidth_bias_eq hn, ← Real.mul_rpow (by positivity) hw.le]
    apply Real.rpow_le_rpow (by positivity) _ hparam.2.1.le
    nlinarith [hround.1]
  have := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3 * δ / 8 by positivity)
  nlinarith

end CausalSmith.Stat.GlobalTailDesignRobustCate
