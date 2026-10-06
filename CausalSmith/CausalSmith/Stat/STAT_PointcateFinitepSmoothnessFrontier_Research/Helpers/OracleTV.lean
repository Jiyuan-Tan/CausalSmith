module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleLower
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product

/-! Rare-mark total-variation comparison for the oracle lower alternatives. -/
public section
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The conditional event mass is an explicit two-atom perturbation of the zero-outcome law. -/
-- @node: oracle_lower_record_event
lemma oracle_lower_record_event (κ : Params) (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n)
    (ε : Bool) (x : unitInterval) (s : Set (Bool × ℝ)) (hs : MeasurableSet s) :
    (recordKernel (fun _ => 1/2) measurable_const (oracleLowerKernel κ n ε) x).real s =
      (1/2 : ℝ) * ((1-oracleLowerEffect κ n ε x/oracleLowerAmplitude κ n) *
        (if (true, (0 : ℝ)) ∈ s then 1 else 0) +
        (oracleLowerEffect κ n ε x/oracleLowerAmplitude κ n) *
        (if (true, oracleLowerAmplitude κ n) ∈ s then 1 else 0)) +
      (1/2 : ℝ) * (if (false, (0 : ℝ)) ∈ s then 1 else 0) := by
  have hw := oracle_lower_mixing_bounds κ n hd ε x
  have hprod (a : Bool) (μ : Measure ℝ) :
      (Measure.dirac a).prod μ = μ.map (Prod.mk a) := by
    rw [Measure.prod, Measure.dirac_bind (measurable_of_countable _)]
  simp only [recordKernel, Kernel.coe_mk, recordMeasure, oracleLowerKernel,
    oracleLowerOutcomeMeasure, Bool.false_eq_true, ↓reduceIte, hprod, measureReal_def,
    Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_prodMk_left hs,
    Measure.dirac_apply' _ (hs.preimage measurable_prodMk_left),
    Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  split_ifs <;> norm_num [ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw.2), ENNReal.toReal_ofReal hw.1]
  all_goals rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  all_goals norm_num [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw.2), ENNReal.toReal_ofReal hw.1]

  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw.2), ENNReal.toReal_ofReal hw.1]
  ring

/-- Moving rare treated mass from zero to the mark changes any event by at most half its mixing probability. -/
-- @node: oracle_lower_record_event_gap
lemma oracle_lower_record_event_gap (κ : Params) (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n)
    (x : unitInterval) (s : Set (Bool × ℝ)) (hs : MeasurableSet s) :
    |(recordKernel (fun _ => 1/2) measurable_const (oracleLowerKernel κ n true) x).real s -
      (recordKernel (fun _ => 1/2) measurable_const (oracleLowerKernel κ n false) x).real s| ≤
      (1/2 : ℝ)*(oracleLowerEffect κ n true x/oracleLowerAmplitude κ n) := by
  rw [oracle_lower_record_event κ n hd true x s hs,
    oracle_lower_record_event κ n hd false x s hs]
  simp only [oracleLowerEffect, Bool.false_eq_true, ↓reduceIte, zero_div, sub_zero,
    zero_mul, add_zero, one_mul]
  have hw := (oracle_lower_mixing_bounds κ n hd true x).1
  simp only [oracleLowerEffect, ↓reduceIte] at hw
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

/-- The triangular cutoff is supported in the window of twice its radius and is at most one. -/
-- @node: oracle_lower_cutoff_integral
lemma oracle_lower_cutoff_integral (κ : Params) (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n) :
    (∫ x : unitInterval, max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n) ∂design) ≤
      2*oracleLowerH κ n := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let k := fun x : unitInterval => max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n)
  have hh := (oracle_lower_scale_bounds κ n hd).1
  have h2 : 2*oracleLowerH κ n ≤ 1 := by
    have hp : 0 < κ.p := by linarith [hd.1.1.1]
    have hq : 0 < qExp κ := div_pos (sub_pos.mpr hd.1.1.1) hp
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hg := hd.1.2.2.2.1
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hn1
      (show -qExp κ/(κ.γ+qExp κ) ≤ 0 from
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) (by positivity))
    unfold oracleLowerH oracleH
    linarith
  have hm : Measurable k := by dsimp [k]; fun_prop
  have hi : Integrable k design := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact (oracle_lower_cutoff_bounds κ n hd x x).1.2
  have hw : MeasurableSet (window (2*oracleLowerH κ n)) := by
    exact measurableSet_Icc.preimage (by fun_prop)
  have hb (x : unitInterval) : k x ≤ (window (2*oracleLowerH κ n)).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ window (2*oracleLowerH κ n)
    · rw [Set.indicator_of_mem hx]
      exact (oracle_lower_cutoff_bounds κ n hd x x).1.2
    · rw [Set.indicator_of_notMem hx]
      have hab : oracleLowerH κ n ≤ |(x : ℝ)-1/2| := by
        by_contra! h
        have h' := abs_lt.mp h
        apply hx
        change 1/2-(2*oracleLowerH κ n)/2 ≤ (x : ℝ) ∧
          (x : ℝ) ≤ 1/2+(2*oracleLowerH κ n)/2
        constructor <;> linarith
      dsimp [k]
      rw [max_eq_left (by have h : (1 : ℝ) ≤ |(x : ℝ)-1/2|/oracleLowerH κ n := (le_div_iff₀ hh).2 (by simpa using hab); linarith :
        1-|(x : ℝ)-1/2|/oracleLowerH κ n ≤ 0)]
  have h := integral_mono hi ((integrable_const (1 : ℝ)).indicator hw) hb
  rw [integral_indicator hw, integral_const, smul_eq_mul,
    measureReal_def, Measure.restrict_apply_univ, design_window _ ⟨by positivity, h2⟩,
    ENNReal.toReal_ofReal (by positivity), mul_one] at h
  exact h

/-- Integrating the conditional rare-mark comparison bounds one-record total variation. -/
-- @node: oracle_lower_single_tv
lemma oracle_lower_single_tv (κ : Params) (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n) :
    Causalean.Stat.tvDist (oracleLowerLaw κ n true).P (oracleLowerLaw κ n false).P ≤
      oracleLowerH κ n * (oracleLowerT κ n/oracleLowerAmplitude κ n) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let K (ε : Bool) := recordKernel (fun _ => 1/2) measurable_const (oracleLowerKernel κ n ε)
  letI (ε : Bool) : IsMarkovKernel (K ε) :=
    recordKernel_markov _ _ half_range _ (oracle_lower_versions κ n hd ε).1
  have hreal (ε : Bool) (s : Set O) (hs : MeasurableSet s) :
      (oracleLowerLaw κ n ε).P.real s = ∫ x, (K ε x).real (Prod.mk x ⁻¹' s) ∂design := by
    change ((oracleLowerLaw κ n ε).P s).toReal = _
    simp only [oracleLowerLaw, dif_pos hd, lawFromUniform, uniformRecord]
    rw [Measure.compProd_apply hs, ← integral_toReal]
    · rfl
    · exact (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
    · filter_upwards [] with x
      exact measure_lt_top (K ε x) _
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨s, hs⟩
  have hi (ε : Bool) : Integrable (fun x => (K ε x).real (Prod.mk x ⁻¹' s)) design := by
    apply Integrable.of_bound (by
      exact (Kernel.measurable_kernel_prodMk_left hs).ennreal_toReal.aestronglyMeasurable) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  let w := fun x : unitInterval => (1/2 : ℝ)*(oracleLowerEffect κ n true x/oracleLowerAmplitude κ n)
  have hw : Integrable w design := by
    apply Integrable.of_bound (by dsimp [w]; simp only [oracleLowerEffect, ↓reduceIte]; fun_prop) 1
    filter_upwards [] with x
    have hb := oracle_lower_mixing_bounds κ n hd true x
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [w]; exact mul_nonneg (by norm_num) hb.1)]
    dsimp [w]
    linarith
  rw [hreal true s hs, hreal false s hs, ← integral_sub (hi true) (hi false)]
  calc
    _ ≤ ∫ x, |(K true x).real (Prod.mk x ⁻¹' s) -
        (K false x).real (Prod.mk x ⁻¹' s)| ∂design := abs_integral_le_integral_abs
    _ ≤ ∫ x, w x ∂design := integral_mono ((hi true).sub (hi false)).abs hw
      (fun x => oracle_lower_record_event_gap κ n hd x _ (hs.preimage measurable_prodMk_left))
    _ = (oracleLowerT κ n/oracleLowerAmplitude κ n)/2 *
        ∫ x : unitInterval, max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n) ∂design := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [w, oracleLowerEffect]
      ring
    _ ≤ (oracleLowerT κ n/oracleLowerAmplitude κ n)/2 * (2*oracleLowerH κ n) :=
      mul_le_mul_of_nonneg_left (oracle_lower_cutoff_integral κ n hd) (by
        have hb := oracle_lower_scale_bounds κ n hd
        exact div_nonneg (div_nonneg hb.2.2.1.le (by linarith [hb.2.2.2.2])) (by norm_num))
    _ = _ := by ring

/-- The rare-mark mixing scale is the effect amplitude raised to inverse heavy-tail power. -/
-- @node: oracle_lower_mixing_power
lemma oracle_lower_mixing_power (κ : Params) (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n) :
    oracleLowerT κ n/oracleLowerAmplitude κ n = oracleLowerT κ n^(1/qExp κ) := by
  have ht := (oracle_lower_scale_bounds κ n hd).2.2.1
  have hp : 0 < κ.p := by linarith [hd.1.1.1]
  have hp1 : κ.p-1 ≠ 0 := ne_of_gt (sub_pos.mpr hd.1.1.1)
  unfold oracleLowerAmplitude
  conv_lhs => lhs; rw [← Real.rpow_one (oracleLowerT κ n)]
  rw [← Real.rpow_sub ht]
  congr 1
  unfold qExp
  field_simp
  <;> ring

/-- The lower bandwidth and rare mixing power cancel all sample-size powers. -/
-- @node: oracle_lower_rare_budget
lemma oracle_lower_rare_budget (κ : Params) (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n) :
    (n : ℝ)*oracleLowerH κ n*(oracleLowerT κ n/oracleLowerAmplitude κ n) ≤ 1/4 := by
  have hp : 0 < κ.p := by linarith [hd.1.1.1]
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hd.1.1.1) hp
  have hg := hd.1.2.2.2.1
  have hh := (oracle_lower_scale_bounds κ n hd).1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hho : 0 < oracleH κ n := by unfold oracleH; positivity
  have ht : oracleLowerT κ n ≤ oracleH κ n^κ.γ := by
    have hle : oracleLowerH κ n ≤ oracleH κ n := by unfold oracleLowerH; linarith
    have h := Real.rpow_le_rpow hh.le hle hg.le
    have hnonneg := Real.rpow_nonneg hh.le κ.γ
    unfold oracleLowerT
    linarith
  have hmix := Real.rpow_le_rpow (oracle_lower_scale_bounds κ n hd).2.2.1.le ht
    (by positivity : 0 ≤ 1/qExp κ)
  rw [← Real.rpow_mul hho.le] at hmix
  have hcancel : (n : ℝ)*oracleH κ n*(oracleH κ n^(κ.γ*(1/qExp κ))) = 1 := by
    unfold oracleH
    rw [← Real.rpow_mul hn.le]
    conv_lhs => lhs; lhs; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    have he : 1 + -qExp κ/(κ.γ+qExp κ) +
        (-qExp κ/(κ.γ+qExp κ))*(κ.γ*(1/qExp κ)) = 0 := by
      field_simp
      <;> ring
    rw [he, Real.rpow_zero]
  rw [oracle_lower_mixing_power κ n hd]
  calc
    _ ≤ (n : ℝ)*oracleLowerH κ n*(oracleH κ n^(κ.γ*(1/qExp κ))) :=
      mul_le_mul_of_nonneg_left hmix (by positivity)
    _ = ((n : ℝ)*oracleH κ n*(oracleH κ n^(κ.γ*(1/qExp κ))))/4 := by
      unfold oracleLowerH
      ring
    _ = 1/4 := by rw [hcancel]

/-- Product tensorization and the shared seed give the oracle roadmap's original-experiment TV bound. -/
-- @node: oracle_lower_joint_tv
lemma oracle_lower_joint_tv (κ : Params) (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n) :
    Causalean.Stat.tvDist (jointLaw n (oracleLowerLaw κ n true).P)
      (jointLaw n (oracleLowerLaw κ n false).P) ≤ 1/4 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hseed := two_prior_seed_tv
    (Measure.pi fun _ : Fin n => (oracleLowerLaw κ n true).P)
    (Measure.pi fun _ : Fin n => (oracleLowerLaw κ n false).P) design
  change Causalean.Stat.tvDist
    ((Measure.pi fun _ : Fin n => (oracleLowerLaw κ n true).P).prod design)
    ((Measure.pi fun _ : Fin n => (oracleLowerLaw κ n false).P).prod design) ≤ _
  rw [hseed]
  calc
    _ ≤ (n : ℝ)*Causalean.Stat.tvDist (oracleLowerLaw κ n true).P
        (oracleLowerLaw κ n false).P :=
      Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_pi_iid_le n _ _
    _ ≤ (n : ℝ)*(oracleLowerH κ n*(oracleLowerT κ n/oracleLowerAmplitude κ n)) :=
      mul_le_mul_of_nonneg_left (oracle_lower_single_tv κ n hd) (by positivity)
    _ ≤ 1/4 := by
      rw [← mul_assoc]
      exact oracle_lower_rare_budget κ n hd

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
