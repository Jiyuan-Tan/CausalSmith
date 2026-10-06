module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleConstruction
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TruncationMoments
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperTruncation

/-! Conditional oracle score moments, truncation bias, and localization bias. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params)

/-- A finite p-moment envelope controls the bias and second moment of a truncated score. -/
-- @node: score_truncation_moment_bounds
lemma score_truncation_moment_bounds {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (f : Ω → ℝ) (hf : Measurable f)
    (p T M : ℝ) (hp : 1 < p ∧ p ≤ 2) (hT : 0 < T) (hM : 0 ≤ M)
    (hQ : ∫⁻ y, ENNReal.ofReal (|f y|^p) ∂Q ≤ ENNReal.ofReal M) :
    Integrable f Q ∧
    |(∫ y, f y ∂Q) - ∫ y, trunc T (f y) ∂Q| ≤ M*T^(1-p) ∧
    (∫ y, (trunc T (f y))^2 ∂Q) ≤ M*T^(2-p) := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp.1
  have hpnonneg : 0 ≤ p := hp0.le
  have htr : Measurable (fun y => trunc T (f y)) := (measurable_trunc T).comp hf
  have hmp : Integrable (fun y => |f y|^p) Q := by
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun y => by positivity)).2 ?_⟩
    exact hQ.trans_lt ENNReal.ofReal_lt_top
  have hfirst : Integrable f Q := by
    have h := integrable_norm_rpow_of_le hf.aestronglyMeasurable
      (by norm_num : (0 : ℝ) ≤ 1) hp0.le hp.1.le
      (by simpa only [Real.norm_eq_abs] using hmp)
    apply (integrable_norm_iff hf.aestronglyMeasurable).1
    simpa using h
  have hmoment : (∫ y, |f y|^p ∂Q) ≤ M := by
    rw [← ENNReal.ofReal_le_ofReal_iff hM]
    rw [ofReal_integral_eq_lintegral_ofReal hmp (ae_of_all _ fun y => by positivity)]
    exact hQ
  have ht : Integrable (fun y => trunc T (f y)) Q := by
    apply hfirst.mono htr.aestronglyMeasurable
    exact ae_of_all _ fun y => by
      by_cases hy : |f y| ≤ T <;> simp [trunc, hy, Real.norm_eq_abs]
  refine ⟨hfirst, ?_, ?_⟩
  · rw [← integral_sub hfirst ht]
    calc
      |∫ y, f y - trunc T (f y) ∂Q| ≤ ∫ y, |f y - trunc T (f y)| ∂Q := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun y => f y - trunc T (f y))
      _ ≤ ∫ y, T^(1-p) * |f y|^p ∂Q :=
        integral_mono (hfirst.sub ht).abs (hmp.const_mul _) fun y =>
          truncation_tail_pointwise p T (f y) hp.1 hT
      _ = T^(1-p) * ∫ y, |f y|^p ∂Q := integral_const_mul _ _
      _ ≤ M*T^(1-p) := by nlinarith [Real.rpow_pos_of_pos hT (1-p)]
  · have hs : Integrable (fun y => (trunc T (f y))^2) Q := by
      apply (hmp.const_mul (T^(2-p))).mono' (htr.pow_const 2).aestronglyMeasurable
      exact ae_of_all _ fun y => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (trunc T (f y)))] using
          truncation_square_pointwise p T (f y) ⟨hp0, hp.2⟩ hT
    calc
      (∫ y, (trunc T (f y))^2 ∂Q) ≤ ∫ y, T^(2-p) * |f y|^p ∂Q :=
        integral_mono hs (hmp.const_mul _) fun y =>
          truncation_square_pointwise p T (f y) ⟨hp0, hp.2⟩ hT
      _ = T^(2-p) * ∫ y, |f y|^p ∂Q := integral_const_mul _ _
      _ ≤ M*T^(2-p) := by nlinarith [Real.rpow_pos_of_pos hT (2-p)]

/-- Overlap makes clipping the revealed model propensity an identity. -/
-- @node: suppliedScore_eq_model
lemma suppliedScore_eq_model (law : ObservedLaw) (hm : InModel κ law) (o : O) :
    suppliedScore (sideE law) o = scoreZ law.e o := by
  have hcont : Continuous law.e := hm.propensityHolder.1
  have he : (fun x => max (1/4) (min (sideE law x) (3/4))) = law.e := by
    funext x
    simp only [sideE, continuousVersion, dif_pos hcont, ContinuousMap.coe_mk]
    rw [min_eq_left (hm.overlap x).2, max_eq_right (hm.overlap x).1]
  unfold suppliedScore
  rw [he]

/-- The original conditional mean versions give the revealed score's conditional mean. -/
-- @node: oracle_score_mean
lemma oracle_score_mean (law : ObservedLaw) (hm : InModel κ law) :
    ∀ᵐ x ∂design, law.e x*(∫ y, scoreZ law.e (x,true,y) ∂law.Q true x) +
      (1-law.e x)*(∫ y, scoreZ law.e (x,false,y) ∂law.Q false x) = law.tau x := by
  have h0 := law.mean0_version
  have h1 := law.mean1_version
  rw [hm.uniform] at h0 h1
  filter_upwards [h0, h1] with x hx0 hx1
  have he : law.e x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (hm.overlap x).1)
  have hc : 1-law.e x ≠ 0 := ne_of_gt (by linarith [(hm.overlap x).2])
  simp only [scoreZ, A, X, Y, Bool.false_eq_true, ↓reduceIte]
  rw [integral_div, integral_div, integral_neg, ← hx0, ← hx1]
  field_simp [he, hc]
  ring

/-- Each overlap-bounded inverse weight inflates the original p-moment by at most four to p. -/
-- @node: oracle_inverse_weight_moment
lemma oracle_inverse_weight_moment (p d : ℝ) (hp : 0 ≤ p) (hd : 1/4 ≤ d)
    (Q : Measure ℝ) (hQ : ∫⁻ y, ENNReal.ofReal (|y|^p) ∂Q ≤ 10) :
    (∫⁻ y, ENNReal.ofReal (|y/d|^p) ∂Q) ≤ ENNReal.ofReal ((4 : ℝ)^p) * 10 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hinv : d⁻¹ ≤ 4 := by
    have hi : 1/d ≤ 4 := (div_le_iff₀ hdpos).2 (by linarith)
    simpa only [one_div] using hi
  have hw (y : ℝ) : |y/d|^p ≤ (4 : ℝ)^p * |y|^p := by
    rw [abs_div, abs_of_pos hdpos, div_eq_mul_inv,
      Real.mul_rpow (abs_nonneg _) (inv_nonneg.mpr hdpos.le)]
    calc
      |y|^p * (d⁻¹)^p ≤ |y|^p * (4 : ℝ)^p :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (inv_nonneg.mpr hdpos.le) hinv hp) (by positivity)
      _ = (4 : ℝ)^p * |y|^p := mul_comm _ _
  calc
    (∫⁻ y, ENNReal.ofReal (|y/d|^p) ∂Q)
        ≤ ∫⁻ y, ENNReal.ofReal ((4 : ℝ)^p) * ENNReal.ofReal (|y|^p) ∂Q := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hw y)
    _ = ENNReal.ofReal ((4 : ℝ)^p) * ∫⁻ y, ENNReal.ofReal (|y|^p) ∂Q :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((4 : ℝ)^p) * 10 := mul_le_mul_right hQ _

/-- The two original arm moments and overlap imply the oracle's conditional moment envelope. -/
-- @node: oracle_score_moment
lemma oracle_score_moment (hκ : κ.Valid) (law : ObservedLaw) (hm : InModel κ law) :
    ∀ᵐ x ∂design,
      ENNReal.ofReal (law.e x)*(∫⁻ y, ENNReal.ofReal (|scoreZ law.e (x,true,y)|^κ.p) ∂law.Q true x) +
      ENNReal.ofReal (1-law.e x)*(∫⁻ y, ENNReal.ofReal (|scoreZ law.e (x,false,y)|^κ.p) ∂law.Q false x) ≤
        ENNReal.ofReal (oracleMoment κ) := by
  have hp : 0 ≤ κ.p := by linarith [hκ.1.1]
  filter_upwards [hm.conditionalMoment] with x hx
  have ht := oracle_inverse_weight_moment κ.p (law.e x) hp (hm.overlap x).1
    (law.Q true x) (hx true)
  have hf := oracle_inverse_weight_moment κ.p (1-law.e x) hp
    (by linarith [(hm.overlap x).2]) (law.Q false x) (hx false)
  simp only [scoreZ, A, X, Y, Bool.false_eq_true, ↓reduceIte, neg_div, abs_neg]
  calc
    _ ≤ ENNReal.ofReal (law.e x) * (ENNReal.ofReal ((4 : ℝ)^κ.p) * 10) +
        ENNReal.ofReal (1-law.e x) * (ENNReal.ofReal ((4 : ℝ)^κ.p) * 10) :=
      add_le_add (mul_le_mul_right ht _) (mul_le_mul_right hf _)
    _ = ENNReal.ofReal (oracleMoment κ) := by
      rw [← add_mul, ← ENNReal.ofReal_add (law.e_range x).1
        (sub_nonneg.mpr (law.e_range x).2)]
      simp only [add_sub_cancel, ENNReal.ofReal_one, one_mul]
      rw [oracleMoment, ENNReal.ofReal_mul (by norm_num)]
      norm_num [mul_comm]

/-- Truncating the overlap-weighted score incurs the conditional tail bias and square envelope. -/
-- @node: oracle_conditional_truncation_bounds
lemma oracle_conditional_truncation_bounds (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ x ∂design,
      |law.e x*(∫ y, trunc T (scoreZ law.e (x,true,y)) ∂law.Q true x) +
        (1-law.e x)*(∫ y, trunc T (scoreZ law.e (x,false,y)) ∂law.Q false x) -
        law.tau x| ≤ oracleMoment κ*T^(1-κ.p) ∧
      law.e x*(∫ y, (trunc T (scoreZ law.e (x,true,y)))^2 ∂law.Q true x) +
        (1-law.e x)*(∫ y, (trunc T (scoreZ law.e (x,false,y)))^2 ∂law.Q false x) ≤
        oracleMoment κ*T^(2-κ.p) := by
  have hp : 0 ≤ κ.p := by linarith [hκ.1.1]
  have hM : 0 ≤ oracleMoment κ := by unfold oracleMoment; positivity
  have hMeq : ENNReal.ofReal ((4 : ℝ)^κ.p)*10 = ENNReal.ofReal (oracleMoment κ) := by
    rw [oracleMoment, ENNReal.ofReal_mul (by norm_num)]
    norm_num [mul_comm]
  filter_upwards [hm.conditionalMoment, oracle_score_mean κ law hm] with x hx hmean
  have henv (a : Bool) :
      (∫⁻ y, ENNReal.ofReal (|scoreZ law.e (x,a,y)|^κ.p) ∂law.Q a x) ≤
        ENNReal.ofReal (oracleMoment κ) := by
    cases a
    · have h := oracle_inverse_weight_moment κ.p (1-law.e x) hp
        (by linarith [(hm.overlap x).2]) (law.Q false x) (hx false)
      simpa only [scoreZ, A, X, Y, Bool.false_eq_true, ↓reduceIte,
        neg_div, abs_neg, hMeq] using h
    · have h := oracle_inverse_weight_moment κ.p (law.e x) hp
        (hm.overlap x).1 (law.Q true x) (hx true)
      simpa only [scoreZ, A, X, Y, ↓reduceIte, hMeq] using h
  have hb (a : Bool) := score_truncation_moment_bounds
    (law.Q a x) (fun y => scoreZ law.e (x,a,y))
    (by unfold scoreZ A X Y; dsimp only; split_ifs <;> fun_prop) κ.p T (oracleMoment κ) hκ.1 hT hM (henv a)
  have he := law.e_range x
  have hc : 0 ≤ 1-law.e x := sub_nonneg.mpr he.2
  constructor
  · rw [← hmean]
    have hid (u v r s : ℝ) : law.e x*u+(1-law.e x)*v -
        (law.e x*r+(1-law.e x)*s) = law.e x*(u-r)+(1-law.e x)*(v-s) := by ring
    rw [hid]
    let u := (∫ y, trunc T (scoreZ law.e (x,true,y)) ∂law.Q true x) -
      ∫ y, scoreZ law.e (x,true,y) ∂law.Q true x
    let v := (∫ y, trunc T (scoreZ law.e (x,false,y)) ∂law.Q false x) -
      ∫ y, scoreZ law.e (x,false,y) ∂law.Q false x
    have hu : |u| ≤ oracleMoment κ*T^(1-κ.p) := by
      dsimp [u]; rw [abs_sub_comm]; exact (hb true).2.1
    have hv : |v| ≤ oracleMoment κ*T^(1-κ.p) := by
      dsimp [v]; rw [abs_sub_comm]; exact (hb false).2.1
    change |law.e x*u+(1-law.e x)*v| ≤ _
    calc
      _ ≤ |law.e x*u|+|(1-law.e x)*v| := abs_add_le _ _
      _ = law.e x*|u|+(1-law.e x)*|v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg he.1, abs_of_nonneg hc]
      _ ≤ law.e x*(oracleMoment κ*T^(1-κ.p)) +
          (1-law.e x)*(oracleMoment κ*T^(1-κ.p)) := add_le_add
        (mul_le_mul_of_nonneg_left hu he.1)
        (mul_le_mul_of_nonneg_left hv hc)
      _ = oracleMoment κ*T^(1-κ.p) := by ring
  · calc
      _ ≤ law.e x*(oracleMoment κ*T^(2-κ.p)) +
          (1-law.e x)*(oracleMoment κ*T^(2-κ.p)) := add_le_add
        (mul_le_mul_of_nonneg_left (hb true).2.2 he.1)
        (mul_le_mul_of_nonneg_left (hb false).2.2 hc)
      _ = oracleMoment κ*T^(2-κ.p) := by ring

/-- The normalized local effect average differs from the point target by its Holder modulus. -/
-- @node: oracle_localization_bias
lemma oracle_localization_bias (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) :
    |h⁻¹ * ∫ x in window h, law.tau x-law.theta ∂design| ≤ 20*h^κ.γ := by
  apply covariance_normalized_integral_bound h hh
  intro x hx
  have hdist : |(x : ℝ)-(xstar : ℝ)| ≤ h := by
    change (x : ℝ) ∈ Icc (1/2-h/2) (1/2+h/2) at hx
    change |(x : ℝ)-1/2| ≤ h
    exact abs_le.mpr ⟨by linarith [hx.1, hh.1], by linarith [hx.2, hh.1]⟩
  exact (hm.effectHolder.2.2 x xstar).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hdist hκ.2.2.2.1.le) (by norm_num))

/-- Localization of the conditional score bounds gives the bias and square envelopes
needed for the iid sample calculation, without smoothness of the truncated score mean. -/
-- @node: oracle_local_truncation_bounds
lemma oracle_local_truncation_bounds (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h T : ℝ) (hh : 0 < h ∧ h ≤ 1) (hT : 0 < T) :
    |h⁻¹ * ∫ x in window h,
      law.e x*(∫ y, trunc T (scoreZ law.e (x,true,y)) ∂law.Q true x) +
        (1-law.e x)*(∫ y, trunc T (scoreZ law.e (x,false,y)) ∂law.Q false x) -
        law.theta ∂design| ≤ 20*h^κ.γ + oracleMoment κ*T^(1-κ.p) ∧
    h⁻¹ * (∫ x in window h,
      law.e x*(∫ y, (trunc T (scoreZ law.e (x,true,y)))^2 ∂law.Q true x) +
        (1-law.e x)*(∫ y, (trunc T (scoreZ law.e (x,false,y)))^2 ∂law.Q false x)
        ∂design) ≤ oracleMoment κ*T^(2-κ.p) := by
  have hb := ae_restrict_of_ae (s := window h) (oracle_conditional_truncation_bounds κ hκ law hm T hT)
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  constructor
  · apply upper_normalized_integral_bound_ae h hh
    filter_upwards [hb, ae_restrict_mem hw] with x hx hxw
    have hdist : |(x : ℝ)-(xstar : ℝ)| ≤ h := by
      change (x : ℝ) ∈ Icc (1/2-h/2) (1/2+h/2) at hxw
      change |(x : ℝ)-1/2| ≤ h
      exact abs_le.mpr ⟨by linarith [hxw.1, hh.1], by linarith [hxw.2, hh.1]⟩
    have ht : |law.tau x-law.theta| ≤ 20*h^κ.γ :=
      (hm.effectHolder.2.2 x xstar).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) hdist hκ.2.2.2.1.le) (by norm_num))
    have hi := abs_sub_le
      (law.e x*(∫ y, trunc T (scoreZ law.e (x,true,y)) ∂law.Q true x) +
        (1-law.e x)*(∫ y, trunc T (scoreZ law.e (x,false,y)) ∂law.Q false x))
      (law.tau x) law.theta
    linarith [hx.1]
  · apply (le_abs_self _).trans
    apply upper_normalized_integral_bound_ae h hh
    filter_upwards [hb] with x hx
    have hn : 0 ≤ law.e x*(∫ y, (trunc T (scoreZ law.e (x,true,y)))^2 ∂law.Q true x) +
        (1-law.e x)*(∫ y, (trunc T (scoreZ law.e (x,false,y)))^2 ∂law.Q false x) :=
      add_nonneg (mul_nonneg (law.e_range x).1 (integral_nonneg fun _ => sq_nonneg _))
        (mul_nonneg (sub_nonneg.mpr (law.e_range x).2) (integral_nonneg fun _ => sq_nonneg _))
    rw [abs_of_nonneg hn]
    exact hx.2

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
