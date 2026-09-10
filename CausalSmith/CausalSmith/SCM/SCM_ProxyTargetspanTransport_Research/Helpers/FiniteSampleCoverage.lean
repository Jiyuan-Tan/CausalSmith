import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Basic
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Sampling

set_option linter.style.longLine false

/-! Coordinate concentration and deterministic projection helpers for finite-sample coverage. -/

open scoped BigOperators
open Finset Matrix MeasureTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

-- @node: coverageProxyIndicator
/-- [The treatment, proxy value, environment](hyp:x,w,e) determine [the indicator of the specified environment, proxy, and treatment cell](goal). -/
def coverageProxyIndicator {E W X Y : Type*}
    [DecidableEq E] [DecidableEq W] [DecidableEq X]
    (x : X) (w : W) (e : E) : (E × W × X × Y) → ℝ :=
  fun o => if o.1 = e ∧ o.2.1 = w ∧ o.2.2.1 = x then 1 else 0

-- @node: integral_coverageProxyIndicator
/-- [the observed-law integral of the proxy-cell indicator equals the corresponding proxy moment](goal). -/
lemma integral_coverageProxyIndicator
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (Mdl : LatentShiftSCM E U W X Y) (x : X) (w : W) (e : E) :
    ∫ o, coverageProxyIndicator x w e o ∂observedMeasure Mdl = proxyMomentMatrix Mdl x w e := by
  rw [observedMeasure, PMF.integral_eq_sum]
  simp only [observedPMF, PMF.ofFintype_apply, Fintype.sum_prod_type]
  simp_rw [ENNReal.toReal_ofReal (observedLaw_nonneg Mdl _ _ _ _)]
  simp only [coverageProxyIndicator, proxyMomentMatrix]
  rw [Fintype.sum_eq_single e (by intro e' hne; simp [hne])]
  rw [Fintype.sum_eq_single w (by intro w' hne; simp [hne])]
  rw [Fintype.sum_eq_single x (by intro x' hne; simp [hne])]
  simp

-- @node: source_proxy_coordinate_tail
/-- Given [positivity of the source sample size, the source i.i.d. sampling condition, nonnegativity of the deviation radius](hyp:hns,hs,hr), [each empirical source proxy coordinate satisfies the stated Hoeffding tail bound](goal). -/
lemma source_proxy_coordinate_tail
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (Mdl : LatentShiftSCM E U W X Y) (x : X) (w : W) (e : E)
    (ns nt : ℕ) (hns : 0 < ns) (mu : Measure (Omega E W X Y ns nt))
    [IsProbabilityMeasure mu] (hs : SourceIidSampling Mdl ns nt mu)
    (r : ℝ) (hr : 0 ≤ r) :
    mu.real {s | r ≤ |finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e|} ≤
      2 * Real.exp (-2 * ns * r ^ 2) := by
  let g := coverageProxyIndicator (Y := Y) x w e
  let A : Set (Fin ns → E × W × X × Y) :=
    {s | r ≤ |(ns : ℝ)⁻¹ * ∑ i, g (s i) - ∫ o, g o ∂observedMeasure Mdl|}
  have hg : Measurable g := measurable_of_finite _
  have hgb : ∀ᵐ o ∂observedMeasure Mdl, g o ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with o
    dsimp [g, coverageProxyIndicator]
    split_ifs <;> norm_num
  have hA : MeasurableSet A := A.toFinite.measurableSet
  have hh := pi_hoeffding_cell (observedMeasure Mdl) g hg hgb ns hns r hr
  have hevent : {s : Omega E W X Y ns nt |
      r ≤ |finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e|} =
      sourceBlock ns nt ⁻¹' A := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    dsimp [A, g]
    rw [integral_coverageProxyIndicator]
    rfl
  rw [hevent]
  have hmap : (mu.map (sourceBlock (E := E) (W := W) (X := X) (Y := Y) ns nt)).real A =
      mu.real (sourceBlock ns nt ⁻¹' A) := by
    have hf : Measurable (sourceBlock (E := E) (W := W) (X := X) (Y := Y) ns nt) :=
      measurable_fst
    exact congrArg ENNReal.toReal (Measure.map_apply hf hA)
  rw [← hmap, hs]
  exact hh

-- @node: coverageOutcomeIndicator
/-- [The treatment, outcome, environment](hyp:x,y,e) determine [the indicator of the specified environment, treatment, and outcome cell](goal). -/
def coverageOutcomeIndicator {E W X Y : Type*}
    [DecidableEq E] [DecidableEq X] [DecidableEq Y]
    (x : X) (y : Y) (e : E) : (E × W × X × Y) → ℝ :=
  fun o => if o.1 = e ∧ o.2.2.1 = x ∧ o.2.2.2 = y then 1 else 0

-- @node: integral_coverageOutcomeIndicator
/-- [the observed-law integral of the outcome-cell indicator equals the corresponding outcome moment](goal). -/
lemma integral_coverageOutcomeIndicator
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y) (e : E) :
    ∫ o, coverageOutcomeIndicator (W := W) x y e o ∂observedMeasure Mdl =
      outcomeMomentVector Mdl x y e := by
  rw [observedMeasure, PMF.integral_eq_sum]
  simp only [observedPMF, PMF.ofFintype_apply, Fintype.sum_prod_type]
  simp_rw [ENNReal.toReal_ofReal (observedLaw_nonneg Mdl _ _ _ _)]
  simp only [coverageOutcomeIndicator, outcomeMomentVector, unconditionalBalancingMoments]
  rw [Fintype.sum_eq_single e (by intro e' hne; simp [hne])]
  symm
  apply Finset.sum_congr rfl
  intro w' _
  rw [Fintype.sum_eq_single x (by intro x' hne; simp [hne])]
  rw [Fintype.sum_eq_single y (by intro y' hne; simp [hne])]
  simp

-- @node: source_outcome_coordinate_tail
/-- Given [positivity of the source sample size, the source i.i.d. sampling condition, nonnegativity of the deviation radius](hyp:hns,hs,hr), [each empirical source outcome coordinate satisfies the stated Hoeffding tail bound](goal). -/
lemma source_outcome_coordinate_tail
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y) (e : E)
    (ns nt : ℕ) (hns : 0 < ns) (mu : Measure (Omega E W X Y ns nt))
    [IsProbabilityMeasure mu] (hs : SourceIidSampling Mdl ns nt mu)
    (r : ℝ) (hr : 0 ≤ r) :
    mu.real {s | r ≤ |finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e|} ≤
      2 * Real.exp (-2 * ns * r ^ 2) := by
  let g := coverageOutcomeIndicator (W := W) x y e
  let A : Set (Fin ns → E × W × X × Y) :=
    {s | r ≤ |(ns : ℝ)⁻¹ * ∑ i, g (s i) - ∫ o, g o ∂observedMeasure Mdl|}
  have hg : Measurable g := measurable_of_finite _
  have hgb : ∀ᵐ o ∂observedMeasure Mdl, g o ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with o
    dsimp [g, coverageOutcomeIndicator]
    split_ifs <;> norm_num
  have hA : MeasurableSet A := A.toFinite.measurableSet
  have hh := pi_hoeffding_cell (observedMeasure Mdl) g hg hgb ns hns r hr
  have hevent : {s : Omega E W X Y ns nt |
      r ≤ |finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e|} =
      sourceBlock ns nt ⁻¹' A := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    dsimp [A, g]
    rw [integral_coverageOutcomeIndicator]
    rfl
  rw [hevent]
  have hmap : (mu.map (sourceBlock (E := E) (W := W) (X := X) (Y := Y) ns nt)).real A =
      mu.real (sourceBlock ns nt ⁻¹' A) := by
    have hf : Measurable (sourceBlock (E := E) (W := W) (X := X) (Y := Y) ns nt) :=
      measurable_fst
    exact congrArg ENNReal.toReal (Measure.map_apply hf hA)
  rw [← hmap, hs]
  exact hh

-- @node: target_proxy_coordinate_tail
/-- Given [positivity of the target sample size, the target i.i.d. sampling condition, nonnegativity of the deviation radius](hyp:hnt,ht,hr), [each empirical target-proxy coordinate satisfies the stated Hoeffding tail bound](goal). -/
lemma target_proxy_coordinate_tail
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (Mdl : LatentShiftSCM E U W X Y) (w : W)
    (ns nt : ℕ) (hnt : 0 < nt) (mu : Measure (Omega E W X Y ns nt))
    [IsProbabilityMeasure mu] (ht : TargetIidSampling Mdl ns nt mu)
    (r : ℝ) (hr : 0 ≤ r) :
    mu.real {s | r ≤ |finEmpTargetProxy nt s w - targetProxyVector Mdl w|} ≤
      2 * Real.exp (-2 * nt * r ^ 2) := by
  let g := targetCellIndicator w
  let A : Set (Fin nt → W) :=
    {s | r ≤ |(nt : ℝ)⁻¹ * ∑ i, g (s i) - ∫ z, g z ∂targetProxyMeasure Mdl|}
  have hg : Measurable g := measurable_of_finite _
  have hgb : ∀ᵐ z ∂targetProxyMeasure Mdl, g z ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with z
    dsimp [g, targetCellIndicator]
    split_ifs <;> norm_num
  have hA : MeasurableSet A := A.toFinite.measurableSet
  have hh := pi_hoeffding_cell (targetProxyMeasure Mdl) g hg hgb nt hnt r hr
  have hevent : {s : Omega E W X Y ns nt |
      r ≤ |finEmpTargetProxy nt s w - targetProxyVector Mdl w|} =
      targetBlock ns nt ⁻¹' A := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    dsimp [A, g]
    rw [integral_targetCellIndicator]
    rfl
  rw [hevent]
  have hmap : (mu.map (targetBlock (E := E) (W := W) (X := X) (Y := Y) ns nt)).real A =
      mu.real (targetBlock ns nt ⁻¹' A) := by
    have hf : Measurable (targetBlock (E := E) (W := W) (X := X) (Y := Y) ns nt) :=
      measurable_snd
    exact congrArg ENNReal.toReal (Measure.map_apply hf hA)
  rw [← hmap, ht]
  exact hh

-- @node: radius_tail_exact
/-- Given [positivity of the coordinate count, the genuine-row or nonnegative-size condition, positivity of the nominal level, the nominal level being below one](hyp:hL,hn,ha0,ha1), [the chosen logarithmic radius makes the union-bound tail factor equal the nominal level divided by the coordinate count](goal). -/
lemma radius_tail_exact (E W : Type*) [Fintype E] [Fintype W]
    (hL : 0 < coordinateCount E W) (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    2 * Real.exp (-2 * n * sourceRadius E W n alpha ^ 2) =
      alpha / coordinateCount E W := by
  have hratio : 1 < 2 * (coordinateCount E W : ℝ) / alpha := by
    have hLc : (1 : ℝ) ≤ coordinateCount E W := by exact_mod_cast hL
    apply (lt_div_iff₀ ha0).2
    nlinarith
  have hlog : 0 ≤ Real.log (2 * coordinateCount E W / alpha) :=
    (Real.log_pos hratio).le
  rw [sourceRadius, Real.sq_sqrt (div_nonneg hlog (by positivity))]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  rw [show -2 * (n : ℝ) * (Real.log (2 * coordinateCount E W / alpha) /
      (2 * n)) = - Real.log (2 * coordinateCount E W / alpha) by field_simp]
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

-- @node: simultaneous_coordinate_concentration
/-- Given [positivity of the source sample size, positivity of the target sample size, the source i.i.d. sampling condition, the target i.i.d. sampling condition](hyp:hns,hnt,hs,ht), [the two-sample law assigns probability at least one minus the nominal level to simultaneous accuracy of every empirical source and target coordinate](goal). -/
lemma simultaneous_coordinate_concentration
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y)
    (ns nt : ℕ) (hns : 0 < ns) (hnt : 0 < nt)
    (mu : Measure (Omega E W X Y ns nt)) [IsProbabilityMeasure mu]
    (hs : SourceIidSampling Mdl ns nt mu) (ht : TargetIidSampling Mdl ns nt mu)
    (alpha : Set.Ioo (0 : ℝ) 1) :
    1 - (alpha : ℝ) ≤ mu.real {s |
      (∀ w e, |finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e| <
        sourceRadius E W ns alpha) ∧
      (∀ e, |finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e| <
        sourceRadius E W ns alpha) ∧
      (∀ w, |finEmpTargetProxy nt s w - targetProxyVector Mdl w| <
        targetRadius E W nt alpha)} := by
  let I := (W × E) ⊕ E ⊕ W
  let bad : I → Set (Omega E W X Y ns nt) := fun i => match i with
    | Sum.inl (w, e) => {s | sourceRadius E W ns alpha ≤
        |finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e|}
    | Sum.inr (Sum.inl e) => {s | sourceRadius E W ns alpha ≤
        |finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e|}
    | Sum.inr (Sum.inr w) => {s | targetRadius E W nt alpha ≤
        |finEmpTargetProxy nt s w - targetProxyVector Mdl w|}
  have hE : 0 < Fintype.card E := Fintype.card_pos_iff.mpr Mdl.environment_nonempty
  have hW : 0 < Fintype.card W :=
    lt_of_lt_of_le (lt_of_lt_of_le (by omega : 0 < 2) Mdl.latent_card) Mdl.proxy_card
  have hL : 0 < coordinateCount E W := by unfold coordinateCount; omega
  have hrs : 0 ≤ sourceRadius E W ns alpha := Real.sqrt_nonneg _
  have hrt : 0 ≤ targetRadius E W nt alpha := Real.sqrt_nonneg _
  have htail : ∀ i, mu.real (bad i) ≤ (alpha : ℝ) / coordinateCount E W := by
    intro i
    rcases i with ⟨w, e⟩ | e | w
    · change mu.real {s | sourceRadius E W ns alpha ≤
          |finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e|} ≤ _
      apply le_trans (source_proxy_coordinate_tail Mdl x w e ns nt hns mu hs _ hrs)
      exact le_of_eq (radius_tail_exact E W hL ns hns alpha alpha.2.1 alpha.2.2)
    · change mu.real {s | sourceRadius E W ns alpha ≤
          |finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e|} ≤ _
      apply le_trans (source_outcome_coordinate_tail Mdl x y e ns nt hns mu hs _ hrs)
      exact le_of_eq (radius_tail_exact E W hL ns hns alpha alpha.2.1 alpha.2.2)
    · change mu.real {s | targetRadius E W nt alpha ≤
          |finEmpTargetProxy nt s w - targetProxyVector Mdl w|} ≤ _
      apply le_trans (target_proxy_coordinate_tail Mdl w ns nt hnt mu ht _ hrt)
      exact le_of_eq (by
        change 2 * Real.exp (-2 * nt * sourceRadius E W nt alpha ^ 2) =
          (alpha : ℝ) / coordinateCount E W
        exact radius_tail_exact E W hL nt hnt alpha alpha.2.1 alpha.2.2)
  have hunion : mu.real (⋃ i, bad i) ≤ (alpha : ℝ) := by
    calc
      mu.real (⋃ i, bad i) ≤ ∑ i, mu.real (bad i) := measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _i : I, ((alpha : ℝ) / coordinateCount E W) :=
        Finset.sum_le_sum fun i _ => htail i
      _ = alpha := by
        simp [I, coordinateCount]
        field_simp
        ring
  let good : Set (Omega E W X Y ns nt) := {s |
      (∀ w e, |finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e| <
        sourceRadius E W ns alpha) ∧
      (∀ e, |finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e| <
        sourceRadius E W ns alpha) ∧
      (∀ w, |finEmpTargetProxy nt s w - targetProxyVector Mdl w| <
        targetRadius E W nt alpha)}
  have hgood : good = (⋃ i, bad i)ᶜ := by
    ext s
    simp only [good, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · rintro ⟨hH, hz, hb⟩ i
      rcases i with ⟨w, e⟩ | e | w
      · exact not_le_of_gt (hH w e)
      · exact not_le_of_gt (hz e)
      · exact not_le_of_gt (hb w)
    · intro h
      refine ⟨fun w e => lt_of_not_ge (h (Sum.inl (w, e))),
        fun e => lt_of_not_ge (h (Sum.inr (Sum.inl e))),
        fun w => lt_of_not_ge (h (Sum.inr (Sum.inr w)))⟩
  change 1 - (alpha : ℝ) ≤ mu.real good
  rw [hgood, probReal_compl_eq_one_sub (omega_measurableSet _ _ _)]
  linarith

-- @node: interventionalProb_mem_unitInterval
/-- [every model interventional probability lies in the closed unit interval](goal). -/
lemma interventionalProb_mem_unitInterval
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    (Mdl : LatentShiftSCM E U W X Y) (x : X) (y : Y) :
    interventionalProb Mdl x y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold interventionalProb
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun w _ =>
      mul_nonneg (mul_nonneg (Mdl.q_nonneg u) (Mdl.M_nonneg w u))
        (Mdl.f_nonneg x y u w)
  · calc
      interventionalProb Mdl x y
          ≤ ∑ u, ∑ w, Mdl.q u * Mdl.M w u * 1 := by
            unfold interventionalProb
            apply Finset.sum_le_sum
            intro u _
            apply Finset.sum_le_sum
            intro w _
            apply mul_le_mul_of_nonneg_left
            · rw [← Mdl.f_col x u w]
              exact Finset.single_le_sum (fun y' _ => Mdl.f_nonneg x y' u w)
                (Finset.mem_univ y)
            · exact mul_nonneg (Mdl.q_nonneg u) (Mdl.M_nonneg w u)
      _ = 1 := by
        calc
          _ = ∑ u, Mdl.q u * ∑ w, Mdl.M w u := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro w _
            ring
          _ = 1 := by simp [Mdl.M_col, Mdl.q_sum]

-- @node: mem_concentrationProjectionSet_of_good
/-- Given [the positive latent-shift condition, membership of the chosen weights in the balancing fiber, the hgood condition](hyp:hM,hlam,hgood), [simultaneous coordinate accuracy and an exact balancing vector place the true interventional probability in the concentration projection set](goal). -/
lemma mem_concentrationProjectionSet_of_good
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    (Mdl : LatentShiftSCM E U W X Y) (hM : PositiveLatentShiftClass Mdl)
    (x : X) (y : Y) (lam : E → ℝ)
    (hlam : lam ∈ balancingFiber (condProxyMatrix Mdl x) (targetProxyVector Mdl))
    (ns nt : ℕ) (alpha : Set.Ioo (0 : ℝ) 1) (s : Omega E W X Y ns nt)
    (hgood :
      (∀ w e, |finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e| <
        sourceRadius E W ns alpha) ∧
      (∀ e, |finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e| <
        sourceRadius E W ns alpha) ∧
      (∀ w, |finEmpTargetProxy nt s w - targetProxyVector Mdl w| <
        targetRadius E W nt alpha)) :
    interventionalProb Mdl x y ∈ concentrationProjectionSet
      (finEmpProxyMoment ns x s) (finEmpOutcomeMoment ns x y s)
      (finEmpTargetProxy nt s) ns nt alpha := by
  let kappa := unconditionalWeightMap (observedLaw Mdl) x
    (targetProxyVector Mdl) ⟨lam, hlam⟩
  have hk := (observable_factorization Mdl hM x y).2.2.2.2.1 lam hlam
  refine ⟨interventionalProb_mem_unitInterval Mdl x y, kappa, ?_, ?_⟩
  · intro w
    change |(finEmpProxyMoment ns x s).mulVec kappa w - finEmpTargetProxy nt s w| ≤ _
    have hk_w := congrFun hk.1 w
    simp only [Matrix.mulVec, dotProduct] at hk_w
    have heq : (finEmpProxyMoment ns x s).mulVec kappa w - finEmpTargetProxy nt s w =
        (∑ e, (finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e) * kappa e) +
          (targetProxyVector Mdl w - finEmpTargetProxy nt s w) := by
      simp only [Matrix.mulVec, dotProduct] at hk_w ⊢
      calc
        _ = (∑ e, finEmpProxyMoment ns x s w e * kappa e) -
              (∑ e, proxyMomentMatrix Mdl x w e * kappa e) +
              (targetProxyVector Mdl w - finEmpTargetProxy nt s w) := by
                rw [hk_w]
                ring
        _ = _ := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro e _
          ring
    rw [heq]
    calc
      _ ≤ |∑ e, (finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e) * kappa e| +
          |targetProxyVector Mdl w - finEmpTargetProxy nt s w| := abs_add_le _ _
      _ ≤ (∑ e, |(finEmpProxyMoment ns x s w e - proxyMomentMatrix Mdl x w e) * kappa e|) +
          targetRadius E W nt alpha := add_le_add (Finset.abs_sum_le_sum_abs _ _)
            (by exact le_of_lt (by simpa [abs_sub_comm] using hgood.2.2 w))
      _ ≤ sourceRadius E W ns alpha * l1Norm kappa + targetRadius E W nt alpha := by
        apply add_le_add
        rw [l1Norm, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro e _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (le_of_lt (hgood.1 w e)) (abs_nonneg _)
        exact le_rfl
  · have heq : dotProduct (finEmpOutcomeMoment ns x y s) kappa - interventionalProb Mdl x y =
        ∑ e, (finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e) * kappa e := by
      rw [← hk.2]
      simp only [dotProduct]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [heq]
    calc
      _ ≤ ∑ e, |(finEmpOutcomeMoment ns x y s e - outcomeMomentVector Mdl x y e) * kappa e| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ sourceRadius E W ns alpha * l1Norm kappa := by
        rw [l1Norm, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro e _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (le_of_lt (hgood.2.1 e)) (abs_nonneg _)
end CausalSmith.SCM.ProxyTargetspanTransport
