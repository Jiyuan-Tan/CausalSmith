module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairZeroAmplitude

/-! # Uniqueness of the fair endpoint center

Clearing the positive risk denominators factors the endpoint matching equation.
Its second factor is strictly negative throughout the prescribed bracket, so
nonzero effect and amplitude force the literal selected root to be the center.
-/
public section
noncomputable section
open scoped BigOperators ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The residual factor in endpoint matching is strictly negative throughout
the fair bracket for every nonnegative exponential increment. [the documented result](goal) Under [the stated assumptions](hyp:hξ). Under [the stated assumptions](hyp:hd). -/
-- @node: fairEndpoint_residual_negative
lemma fairEndpoint_residual_negative (d δ ξ : ℝ) (hd : 0 ≤ d)
    (hξ : ξ ∈ Set.Icc (3/10 : ℝ) (1/2)) :
    -25*δ^2*d + 25*d*ξ^2 - 15*d*ξ - 6*d + 25*ξ - 15 < 0 := by
  have hξpos : 0 ≤ ξ := by linarith [hξ.1]
  have hquad : ξ^2 ≤ ξ/2 := by nlinarith [hξ.2]
  have hmul := mul_nonneg hd (sub_nonneg.mpr hquad)
  have hδ := mul_nonneg (sq_nonneg δ) hd
  have hx := mul_nonneg hd hξpos
  nlinarith [hξ.2]

/-- [Clearing the endpoint risk denominators factors the exact matching
residual, retaining the amplitude square needed for the removable extension. [the documented result](goal) Under [the stated assumptions](hyp:hp,hm,hc,he). -/
-- @node: fairEndpoint_rational_factor
lemma fairEndpoint_rational_factor (d δ ξ e : ℝ)
    (hp : 1+d*(ξ+δ) ≠ 0) (hm : 1+d*(ξ-δ) ≠ 0)
    (hc : 1+(e-1)*ξ ≠ 0)
    (he : e*((3/5)*(1+(2/5)*d)+d*δ^2) =
      (d+1)*((3/5)*(1+(2/5)*d)-(3/2)*d*δ^2)) :
    (((d+1)*(ξ+δ)/(1+d*(ξ+δ)) +
      (d+1)*(ξ-δ)/(1+d*(ξ-δ)))/2 - e*ξ/(1+(e-1)*ξ)) *
      (1+d*(ξ+δ))*(1+d*(ξ-δ))*(1+(e-1)*ξ)*
        ((3/5)*(1+(2/5)*d)+d*δ^2) =
    -d*δ^2*(d+1)*(5*ξ-2)*
      (-25*δ^2*d+25*d*ξ^2-15*d*ξ-6*d+25*ξ-15)/50 := by
  let H := (d+1)*(ξ+δ)*(1+d*(ξ-δ))*(1+(e-1)*ξ) +
    (d+1)*(ξ-δ)*(1+d*(ξ+δ))*(1+(e-1)*ξ) -
    2*e*ξ*(1+d*(ξ+δ))*(1+d*(ξ-δ))
  calc
    _ = ((3/5)*(1+(2/5)*d)+d*δ^2)*H/2 := by
      dsimp [H]
      have hc' : 1+ξ*(e-1) ≠ 0 := by simpa [mul_comm] using hc
      field_simp [hp,hm,hc,hc']
      <;> ring
    _ = _ := by
      dsimp [H]
      linear_combination ξ*(-δ^2*d+d*ξ^2-d*ξ+ξ-1)*he

/-- The explicit log correction supplies the rational comparator odds after
clearing its positive logarithm denominators. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ). -/
-- @node: comparatorEffect_corrected_odds
lemma comparatorEffect_corrected_odds (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100) :
    Real.exp (comparatorEffect t δ)*
      ((3/5)*(1+(2/5)*(Real.exp t-1))+(Real.exp t-1)*δ^2) =
      ((Real.exp t-1)+1)*((3/5)*(1+(2/5)*(Real.exp t-1))-
        (3/2)*(Real.exp t-1)*δ^2) := by
  have he := comparatorEffect_exp_formula t δ ht hδ
  obtain ⟨hB,ha,hb,_,_⟩ := fair_matching_denominators t δ ht hδ
  have hd : 0 ≤ Real.exp t-1 := ht.1.trans (fair_exp_increment_bounds t ht).1
  field_simp (disch := positivity) at he
  linear_combination (1/50)*he

/-- [The rational comparator odds and endpoint risk matching have only the
asymmetric center as a bracket solution off the two removable axes. [the documented result](goal) Under [the stated assumptions](hyp:hξ,hp,hm,hc,he,hmatch). Under [the stated assumptions](hyp:hd,hδ). -/
-- @node: fairEndpoint_rational_unique
lemma fairEndpoint_rational_unique (d δ ξ e : ℝ) (hd : 0 < d) (hδ : δ ≠ 0)
    (hξ : ξ ∈ Set.Icc (3/10 : ℝ) (1/2))
    (hp : 1+d*(ξ+δ) ≠ 0) (hm : 1+d*(ξ-δ) ≠ 0)
    (hc : 1+(e-1)*ξ ≠ 0)
    (he : e*((3/5)*(1+(2/5)*d)+d*δ^2) =
      (d+1)*((3/5)*(1+(2/5)*d)-(3/2)*d*δ^2))
    (hmatch : ((d+1)*(ξ+δ)/(1+d*(ξ+δ)) +
      (d+1)*(ξ-δ)/(1+d*(ξ-δ)))/2 = e*ξ/(1+(e-1)*ξ)) :
    ξ = 2/5 := by
  let H := (d+1)*(ξ+δ)*(1+d*(ξ-δ))*(1+(e-1)*ξ) +
    (d+1)*(ξ-δ)*(1+d*(ξ+δ))*(1+(e-1)*ξ) -
    2*e*ξ*(1+d*(ξ+δ))*(1+d*(ξ-δ))
  have hH : H = 0 := by
    dsimp [H]
    have hc' : 1+ξ*(e-1) ≠ 0 := by simpa [mul_comm] using hc
    field_simp [hp,hm,hc,hc'] at hmatch
    linear_combination hmatch
  have hfactor : d*δ^2*(d+1)*(5*ξ-2)*
      (-25*δ^2*d+25*d*ξ^2-15*d*ξ-6*d+25*ξ-15) = 0 := by
    calc
      _ = -25*(((3/5)*(1+(2/5)*d)+d*δ^2)*H -
        2*ξ*(-δ^2*d+d*ξ^2-d*ξ+ξ-1)*
          (e*((3/5)*(1+(2/5)*d)+d*δ^2) -
            (d+1)*((3/5)*(1+(2/5)*d)-(3/2)*d*δ^2))) := by dsimp [H]; ring
      _ = 0 := by rw [hH,he]; ring
  have hres := fairEndpoint_residual_negative d δ ξ hd.le hξ
  have hbase : d*δ^2*(d+1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hd.ne' (pow_ne_zero 2 hδ)) (by linarith)
  have hz := (mul_eq_zero.mp hfactor).resolve_right (ne_of_lt hres)
  have hx := (mul_eq_zero.mp hz).resolve_left hbase
  linarith

/-- [Exact endpoint singleton matching identifies any bracket root with the
fixed center whenever effect and amplitude are both nonzero. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hξ,hu,hne,hroot). -/
-- @node: fairEquation_endpoint_unique_off_axes
lemma fairEquation_endpoint_unique_off_axes (t δ ξ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hξ : ξ ∈ Set.Ioo (3/10 : ℝ) (1/2)) (hu : u = 0 ∨ u = 1)
    (hne : t*δ ≠ 0) (hroot : fairEquation t δ ξ u = 0) : ξ = 2/5 := by
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (mul_ne_zero_iff.mp hne).1.symm
  have hd : 0 < Real.exp t-1 := by
    have h := Real.exp_lt_exp.mpr htpos
    simpa using sub_pos.mpr h
  have hξ' : ξ ∈ Set.Icc (3/10 : ℝ) (1/2) := ⟨hξ.1.le,hξ.2.le⟩
  have hmatch := fair_matching_of_equation t δ ξ u ht hδ hξ' hroot
  rw [fair_endpoint_sign_average (fun z => riskShift t (ξ+δ*z)) u hu] at hmatch
  simp only [mul_one,mul_neg_one,← sub_eq_add_neg] at hmatch
  have hp : 0 < 1+(Real.exp t-1)*(ξ+δ) := by
    have hx : 0 ≤ ξ+δ := by linarith [(abs_le.mp hδ).1,hξ.1]
    positivity
  have hm : 0 < 1+(Real.exp t-1)*(ξ-δ) := by
    have hx : 0 ≤ ξ-δ := by linarith [(abs_le.mp hδ).2,hξ.1]
    positivity
  have hc : 0 < 1+(Real.exp (comparatorEffect t δ)-1)*ξ := by
    have hpos := Real.exp_pos (comparatorEffect t δ)
    nlinarith [hξ.1,hξ.2]
  have he := comparatorEffect_exp_formula t δ ht hδ
  obtain ⟨hB,ha,hb,_,_⟩ := fair_matching_denominators t δ ht hδ
  have hcorr : Real.exp (comparatorEffect t δ)*
      ((3/5)*(1+(2/5)*(Real.exp t-1))+(Real.exp t-1)*δ^2) =
      ((Real.exp t-1)+1)*((3/5)*(1+(2/5)*(Real.exp t-1))-
        (3/2)*(Real.exp t-1)*δ^2) := by
    exact comparatorEffect_corrected_odds t δ ht hδ
  apply fairEndpoint_rational_unique (Real.exp t-1) δ ξ
    (Real.exp (comparatorEffect t δ)) hd (mul_ne_zero_iff.mp hne).2 hξ'
    hp.ne' hm.ne' hc.ne' hcorr
  simpa only [riskShift,sub_add_cancel] using hmatch

/-- [The literal endpoint selector equals the center throughout the full effect
range away from the removable axes. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hu,hne). -/
-- @node: fairRoot_endpoint_center_off_axes
lemma fairRoot_endpoint_center_off_axes (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hu : u = 0 ∨ u = 1) (hne : t*δ ≠ 0) : fairRoot t δ u = 2/5 := by
  obtain ⟨hb,he⟩ := fairRoot_endpoint_spec t δ u ht hδ hu
  exact fairEquation_endpoint_unique_off_axes t δ _ u ht hδ hb hu hne he

/-- [The endpoint factorization survives Taylor normalization off the axes;
the amplitude square cancels without changing the risk residual. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hξ,hne). -/
-- @node: fairEquation_endpoint_factor_off_axes
lemma fairEquation_endpoint_factor_off_axes (t δ ξ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hξ : ξ ∈ Set.Icc (3/10 : ℝ) (1/2)) (hne : δ ≠ 0) :
    t*fairEquation t δ ξ 0 *
      (1+(Real.exp t-1)*(ξ+δ))*(1+(Real.exp t-1)*(ξ-δ))*
      (1+(Real.exp (comparatorEffect t δ)-1)*ξ)*
      ((3/5)*(1+(2/5)*(Real.exp t-1))+(Real.exp t-1)*δ^2) =
    -(Real.exp t-1)*Real.exp t*(5*ξ-2)*
      (-25*δ^2*(Real.exp t-1)+25*(Real.exp t-1)*ξ^2-
        15*(Real.exp t-1)*ξ-6*(Real.exp t-1)+25*ξ-15)/50 := by
  have hd : 0 ≤ Real.exp t-1 := ht.1.trans (fair_exp_increment_bounds t ht).1
  have hp : 0 < 1+(Real.exp t-1)*(ξ+δ) := by
    have hx : 0 ≤ ξ+δ := by linarith [(abs_le.mp hδ).1,hξ.1]
    positivity
  have hm : 0 < 1+(Real.exp t-1)*(ξ-δ) := by
    have hx : 0 ≤ ξ-δ := by linarith [(abs_le.mp hδ).2,hξ.1]
    positivity
  have hc : 0 < 1+(Real.exp (comparatorEffect t δ)-1)*ξ := by
    nlinarith [Real.exp_pos (comparatorEffect t δ),hξ.1,hξ.2]
  have hf := fairEndpoint_rational_factor (Real.exp t-1) δ ξ
    (Real.exp (comparatorEffect t δ)) hp.ne' hm.ne' hc.ne'
    (comparatorEffect_corrected_odds t δ ht hδ)
  have hN : fairNumerator t δ ξ 0 =
      (riskShift t (ξ+δ)+riskShift t (ξ-δ))/2 -
        riskShift (comparatorEffect t δ) ξ := by
    unfold fairNumerator
    rw [fair_endpoint_sign_average (fun z => riskShift t (ξ+δ*z)) 0 (Or.inl rfl)]
    simp only [mul_one,mul_neg_one,← sub_eq_add_neg]
  simp only [sub_add_cancel] at hf
  change ((riskShift t (ξ+δ)+riskShift t (ξ-δ))/2 -
    riskShift (comparatorEffect t δ) ξ)*
    (1+(Real.exp t-1)*(ξ+δ))*(1+(Real.exp t-1)*(ξ-δ))*
    (1+(Real.exp (comparatorEffect t δ)-1)*ξ)*
    ((3/5)*(1+(2/5)*(Real.exp t-1))+(Real.exp t-1)*δ^2) = _ at hf
  rw [← hN,← fairEquation_mul_parameters t δ ξ 0 ht hδ hξ] at hf
  apply mul_left_cancel₀ (pow_ne_zero 2 hne)
  calc
    _ = t*δ^2*fairEquation t δ ξ 0 *
      (1+(Real.exp t-1)*(ξ+δ))*(1+(Real.exp t-1)*(ξ-δ))*
      (1+(Real.exp (comparatorEffect t δ)-1)*ξ)*
      ((3/5)*(1+(2/5)*(Real.exp t-1))+(Real.exp t-1)*δ^2) := by ring
    _ = _ := hf.trans (by ring)

/-- [Continuity of the actual Taylor extension preserves the factored endpoint
equation at zero amplitude, throughout the closed effect range. [the documented result](goal) Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairEquation_endpoint_factor_zero_amplitude
lemma fairEquation_endpoint_factor_zero_amplitude (t ξ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4))
    (hξ : ξ ∈ Set.Icc (3/10 : ℝ) (1/2)) :
    t*fairEquation t 0 ξ 0 * (1+(Real.exp t-1)*ξ)^3 *
      ((3/5)*(1+(2/5)*(Real.exp t-1))) =
    -(Real.exp t-1)*Real.exp t*(5*ξ-2)*
      (25*(Real.exp t-1)*ξ^2-15*(Real.exp t-1)*ξ-
        6*(Real.exp t-1)+25*ξ-15)/50 := by
  let f : ℝ → ℝ := fun D => t*fairEquation t D ξ 0 *
    (1+(Real.exp t-1)*(ξ+D))*(1+(Real.exp t-1)*(ξ-D))*
    (1+(Real.exp (comparatorEffect t D)-1)*ξ)*
    ((3/5)*(1+(2/5)*(Real.exp t-1))+(Real.exp t-1)*D^2)
  let g : ℝ → ℝ := fun D => -(Real.exp t-1)*Real.exp t*(5*ξ-2)*
    (-25*D^2*(Real.exp t-1)+25*(Real.exp t-1)*ξ^2-
      15*(Real.exp t-1)*ξ-6*(Real.exp t-1)+25*ξ-15)/50
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) (1/100)) := by
    intro D hD
    have hδ : |D| ≤ 1/100 := by rw [abs_of_nonneg hD.1]; exact hD.2
    have hbox : ![t,D,ξ,0] ∈ fairTaylorParameterRegion :=
      (fairTaylorParameterRegion_mem _).mpr
        ⟨ht,hδ,hξ,by change (0 : ℝ) ∈ Set.Icc 0 1; constructor <;> norm_num⟩
    have hpH : ContDiffAt ℝ ∞ (fun x : ℝ => ![t,x,ξ,0]) D := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    have hpC : ContDiffAt ℝ ⊤ (fun x : ℝ => ![t,x]) D := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    have hH : ContinuousAt (fun x => fairEquation t x ξ 0) D := by
      have hh := (fairEquation_contDiffAt ![t,D,ξ,0] hbox).comp D hpH
      exact hh.continuousAt
    have hC : ContinuousAt (fun x => comparatorEffect t x) D := by
      have hh := (comparatorEffect_contDiffAt ![t,D] ht hδ).comp D hpC
      exact hh.continuousAt
    apply ContinuousAt.continuousWithinAt
    dsimp [f]
    fun_prop
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) (1/100)) := by dsimp [g]; fun_prop
  have he : Set.EqOn f g (Set.Ioo (0 : ℝ) (1/100)) := by
    intro D hD
    exact fairEquation_endpoint_factor_off_axes t D ξ ht
      (by rw [abs_of_pos hD.1]; exact hD.2.le) hξ hD.1.ne'
  have hz := he.of_subset_closure hf hg Set.Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1/100)])
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1/100) by constructor <;> norm_num)
  dsimp [f,g] at hz
  simp only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero,sub_zero,
    comparatorEffect_zero_amplitude] at hz
  convert hz using 1 <;> ring

/-- The zero-amplitude normalized equation has a unique bracket root for the
entire effect range; its position independence comes from unit sign variance. [the documented result](goal) Under [the stated assumptions](hyp:ht,hu,hξ,he). -/
-- @node: fairEquation_zero_amplitude_unique
lemma fairEquation_zero_amplitude_unique (t u ξ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hξ : ξ ∈ Set.Ioo (3/10 : ℝ) (1/2))
    (he : fairEquation t 0 ξ u = 0) : ξ = 2/5 := by
  by_cases hz : t = 0
  · subst t
    exact fairEquation_zero_effect_unique 0 u ξ (by norm_num) hu hξ he
  have hξ' : ξ ∈ Set.Icc (3/10 : ℝ) (1/2) := ⟨hξ.1.le,hξ.2.le⟩
  rw [fairEquation_zero_amplitude_endpoint t ξ u ht hξ'] at he
  have hf := fairEquation_endpoint_factor_zero_amplitude t ξ ht hξ'
  rw [he] at hf
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hd : 0 < Real.exp t-1 := by
    have h := Real.exp_lt_exp.mpr htpos
    simpa using sub_pos.mpr h
  have hres := fairEndpoint_residual_negative (Real.exp t-1) 0 ξ hd.le hξ'
  simp only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul,sub_zero,zero_add] at hres
  have hproduct : (5*ξ-2)*(25*(Real.exp t-1)*ξ^2-15*(Real.exp t-1)*ξ-
      6*(Real.exp t-1)+25*ξ-15) = 0 := by
    have hn : -(Real.exp t-1)*Real.exp t ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hd.ne') (Real.exp_pos t).ne'
    have hzero : -(Real.exp t-1)*Real.exp t*(5*ξ-2)*
        (25*(Real.exp t-1)*ξ^2-15*(Real.exp t-1)*ξ-
          6*(Real.exp t-1)+25*ξ-15) = 0 := by linarith [hf]
    apply mul_left_cancel₀ hn
    simpa only [mul_zero,mul_assoc] using hzero
  have hcenter := (mul_eq_zero.mp hproduct).resolve_right (ne_of_lt hres)
  linarith

/-- [The actual zero-amplitude selector is the fixed asymmetric center on the
whole prescribed effect and spatial ranges. [the documented result](goal) Under [the stated assumptions](hyp:ht,hu). -/
-- @node: fairRoot_zero_amplitude
lemma fairRoot_zero_amplitude (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    fairRoot t 0 u = 2/5 := by
  obtain ⟨hb,he⟩ := fairRoot_zero_amplitude_spec t u ht
  exact fairEquation_zero_amplitude_unique t u _ ht hu hb he

/-- Both spatial endpoint selectors equal the center, including effect and
amplitude zero, uniformly on the complete prescribed effect range. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hu). -/
-- @node: fairRoot_endpoint_center
lemma fairRoot_endpoint_center (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hu : u = 0 ∨ u = 1) : fairRoot t δ u = 2/5 := by
  have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hu with rfl | rfl <;> constructor <;> norm_num
  by_cases htzero : t = 0
  · subst t
    exact fairRoot_zero_effect δ u hδ hu'
  by_cases hδzero : δ = 0
  · subst δ
    exact fairRoot_zero_amplitude t u ht hu'
  exact fairRoot_endpoint_center_off_axes t δ u ht hδ hu (mul_ne_zero htzero hδzero)

/-- At zero amplitude the normalized fair equation has strictly separated
signs on the whole selector bracket, uniformly over the closed effect range. [the documented result](goal) Under [the stated assumptions](hyp:ht,hu). -/
-- @node: fairEquation_zero_amplitude_bracket_signs
lemma fairEquation_zero_amplitude_bracket_signs (t u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    fairEquation t 0 (3/10) u < 0 ∧ 0 < fairEquation t 0 (1/2) u := by
  by_cases hz : t = 0
  · subst t
    rw [fairEquation_zero_effect 0 (3/10) u (by norm_num)
      (by constructor <;> norm_num) hu,
      fairEquation_zero_effect 0 (1/2) u (by norm_num)
      (by constructor <;> norm_num) hu]
    norm_num
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hd : 0 < Real.exp t-1 := by
    have h := Real.exp_lt_exp.mpr htpos
    simpa using sub_pos.mpr h
  have hsign (ξ : ℝ) (hξ : ξ ∈ Set.Icc (3/10 : ℝ) (1/2)) :
      (fairEquation t 0 ξ 0 < 0 ↔ 5*ξ-2 < 0) ∧
      (0 < fairEquation t 0 ξ 0 ↔ 0 < 5*ξ-2) := by
    have hf := fairEquation_endpoint_factor_zero_amplitude t ξ ht hξ
    have hK := fairEndpoint_residual_negative (Real.exp t-1) 0 ξ hd.le hξ
    simp only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul,sub_zero,zero_add] at hK
    have hx : 0 ≤ ξ := by linarith [hξ.1]
    let A := t*(1+(Real.exp t-1)*ξ)^3*((3/5)*(1+(2/5)*(Real.exp t-1)))
    let B := -(Real.exp t-1)*Real.exp t*
      (25*(Real.exp t-1)*ξ^2-15*(Real.exp t-1)*ξ-6*(Real.exp t-1)+25*ξ-15)/50
    have hA : 0 < A := by dsimp [A]; positivity
    have hB : 0 < B := by
      dsimp [B]
      exact div_pos (mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hd) (Real.exp_pos t)) hK) (by norm_num)
    have heq : fairEquation t 0 ξ 0 * A = (5*ξ-2)*B := by
      dsimp [A,B]
      linear_combination hf
    constructor <;> constructor <;> intro h <;> nlinarith only [hA,hB,heq,h]
  rw [fairEquation_zero_amplitude_endpoint t (3/10) u ht (by constructor <;> norm_num),
    fairEquation_zero_amplitude_endpoint t (1/2) u ht (by constructor <;> norm_num)]
  exact ⟨(hsign (3/10) (by constructor <;> norm_num)).1.mpr (by norm_num),
    (hsign (1/2) (by constructor <;> norm_num)).2.mpr (by norm_num)⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier
