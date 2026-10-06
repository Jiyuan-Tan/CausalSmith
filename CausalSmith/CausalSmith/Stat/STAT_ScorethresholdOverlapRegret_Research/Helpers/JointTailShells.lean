module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.JointTailPowers

/-! # Score-threshold overlap regret — global joint-tail bias

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @node: jointTail_margin_all_u
/-- The margin bound extends past its public window by the probability bound. -/
lemma jointTail_margin_all_u (P : RowLaw) (α u : ℝ)
    (hα : 0 < α) (hP : IsProbabilityMeasure P.PX)
    (hmargin : MarginCondition P α) (hu : 0 < u) :
    P.PX.real {x | 0 < effectMagnitude P x ∧ effectMagnitude P x ≤ u} ≤
      max Cm ((2:ℝ)^α) * u^α := by
  let : IsProbabilityMeasure P.PX := hP
  by_cases hwindow : u ≤ u0
  · calc
      P.PX.real {x | 0 < effectMagnitude P x ∧ effectMagnitude P x ≤ u}
          ≤ Cm * u^α := hmargin u hu hwindow
      _ ≤ max Cm ((2:ℝ)^α) * u^α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hu.le _)
  · have huHalf : 1/2 < u := by
      simpa [u0] using lt_of_not_ge hwindow
    have hpow : 1 ≤ (2*u)^α :=
      Real.one_le_rpow (by linarith) hα.le
    have hmul : (2*u)^α = (2:ℝ)^α * u^α := by
      rw [Real.mul_rpow (by norm_num) hu.le]
    calc
      P.PX.real {x | 0 < effectMagnitude P x ∧ effectMagnitude P x ≤ u}
          ≤ 1 := measureReal_le_one
      _ ≤ (2:ℝ)^α * u^α := by simpa only [← hmul] using hpow
      _ ≤ max Cm ((2:ℝ)^α) * u^α :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hu.le _)

-- @node: jointTail_envelope_extended
/-- The joint envelope can be applied at a larger effect cutoff while keeping
the original event on the left. This is the monotonicity step in the
small-overlap branch of the bias proof. -/
lemma jointTail_envelope_extended (P : RowLaw) (α γ θ u v w : ℝ)
    (hprob : IsProbabilityMeasure P.PX)
    (hP : GlobalJointEnvelope P α γ θ)
    (hu : 0 < u) (huw : u ≤ w) (hw : w ≤ 2)
    (hv : 0 < v) (hvw : v ≤ co*w^γ) :
    P.PX.real {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ u} ≤ Co θ*w^α*v^θ := by
  let : IsProbabilityMeasure P.PX := hprob
  have hw0 : 0 < w := lt_of_lt_of_le hu huw
  calc
    P.PX.real {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ u} ≤
      P.PX.real {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ w} := by
          apply measureReal_mono
          · intro x hx
            exact ⟨hx.1, hx.2.1, hx.2.2.trans huw⟩
          · exact measure_ne_top P.PX _
    _ ≤ Co θ*w^α*v^θ := hP w v hw0 hw hv hvw

-- @node: jointTail_envelope_max
/-- The joint tail is controlled at the larger of the requested effect cutoff
and the effect scale induced by the overlap cutoff. -/
lemma jointTail_envelope_max (P : RowLaw) (α γ θ u v : ℝ)
    (hγ : 0 < γ) (hprob : IsProbabilityMeasure P.PX)
    (hP : GlobalJointEnvelope P α γ θ)
    (hu : 0 < u) (hu2 : u ≤ 2) (hv : 0 < v) (hvhalf : v ≤ 1/2) :
    P.PX.real {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ u} ≤
      Co θ * (max u (v^(1/γ)))^α * v^θ := by
  have hv1 : v ≤ 1 := by linarith
  have he : 0 < (1/γ : ℝ) := by positivity
  have hpow : v^(1/γ) ≤ 1 := by
    calc
      v^(1/γ) ≤ (1:ℝ)^(1/γ) := Real.rpow_le_rpow hv.le hv1 he.le
      _ = 1 := by simp
  have hw2 : max u (v^(1/γ)) ≤ 2 := max_le hu2 (by linarith)
  have hvpow : v ≤ (max u (v^(1/γ)))^γ := by
    have hmono : (v^(1/γ))^γ ≤ (max u (v^(1/γ)))^γ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hv.le _) (le_max_right _ _) hγ.le
    have hid : (v^(1/γ))^γ = v := by
      rw [← Real.rpow_mul hv.le]
      field_simp
      simp
    simpa only [hid] using hmono
  exact jointTail_envelope_extended P α γ θ u v (max u (v^(1/γ)))
    hprob hP hu (le_max_left _ _) hw2 hv (by simpa [co] using hvpow)

-- @node: jointTail_two_envelopes
/-- Both terms in the joint-tail minimum used for dyadic shell bounds. -/
lemma jointTail_two_envelopes (P : RowLaw) (α γ θ u v : ℝ)
    (hα : 0 < α) (hγ : 0 < γ)
    (hprob : IsProbabilityMeasure P.PX)
    (hmargin : MarginCondition P α)
    (henvelope : GlobalJointEnvelope P α γ θ)
    (hu : 0 < u) (hu2 : u ≤ 2) (hv : 0 < v) (hvhalf : v ≤ 1/2) :
    P.PX.real {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ u} ≤
      min (max Cm ((2:ℝ)^α) * u^α)
        (Co θ * (max u (v^(1/γ)))^α * v^θ) := by
  let : IsProbabilityMeasure P.PX := hprob
  apply le_min
  · calc
      P.PX.real {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧
          effectMagnitude P x ≤ u} ≤
        P.PX.real {x | 0 < effectMagnitude P x ∧
          effectMagnitude P x ≤ u} := by
            apply measureReal_mono
            · intro x hx
              exact hx.2
            · exact measure_ne_top P.PX _
      _ ≤ max Cm ((2:ℝ)^α) * u^α :=
        jointTail_margin_all_u P α u hα hprob hmargin hu
  · exact jointTail_envelope_max P α γ θ u v hγ hprob henvelope
      hu hu2 hv hvhalf

-- @node: jointTail_deleted_negative_bound
/-- The global envelope controls the deleted negative-effect region once the
conditional effect is bounded by the potential-outcome range. -/
lemma jointTail_deleted_negative_bound (P : RowLaw) (α γ θ a : ℝ)
    (hprob : IsProbabilityMeasure P.PX)
    (henvelope : GlobalJointEnvelope P α γ θ)
    (hmag : ∀ᵐ x ∂P.PX, effectMagnitude P x ≤ 2)
    (ha : 0 < a) (hawindow : a ≤ co * (2:ℝ)^γ) :
    P.PX.real {x | overlap P x < a ∧ P.tau x < 0} ≤
      Co θ * (2:ℝ)^α * a^θ := by
  letI := hprob
  have hsub : {x | overlap P x < a ∧ P.tau x < 0} ≤ᵐ[P.PX]
      {x | overlap P x ≤ a ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2} := by
    filter_upwards [hmag] with x hx hs
    refine ⟨le_of_lt hs.1, ?_, hx⟩
    exact abs_pos.mpr (ne_of_lt hs.2)
  have hmono : P.PX.real {x | overlap P x < a ∧ P.tau x < 0} ≤
      P.PX.real {x | overlap P x ≤ a ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2} := by
    exact ENNReal.toReal_mono (measure_ne_top P.PX _) (measure_mono_ae hsub)
  exact hmono.trans (henvelope 2 a (by norm_num) le_rfl ha hawindow)

-- @node: jointTail_retained_shell_event_bound
/-- A retained overlap shell lies inside one joint-tail rectangle with a
constant effect cutoff. -/
lemma jointTail_retained_shell_event_bound (P : RowLaw) (a q : ℝ)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q) :
    {x | q ≤ overlap P x ∧ overlap P x < 2*q ∧
      0 < effectMagnitude P x ∧
      effectMagnitude P x ≤ 2*offsetG a P.logger x} ⊆
    {x | overlap P x ≤ 2*q ∧ 0 < effectMagnitude P x ∧
      effectMagnitude P x ≤ 2*a/q} := by
  intro x hx
  rcases hx with ⟨hql, hqu, ht, htg⟩
  have hp : 0 < overlap P x := lt_of_lt_of_le hq hql
  have hg : offsetG a P.logger x ≤ a/q := by
    calc
      offsetG a P.logger x ≤ a / overlap P x := by
        unfold offsetG overlap
        exact min_le_right _ _
      _ ≤ a/q := div_le_div_of_nonneg_left ha.le hq hql
  refine ⟨le_of_lt hqu, ht, ?_⟩
  calc
    effectMagnitude P x ≤ 2*offsetG a P.logger x := htg
    _ ≤ 2*(a/q) := mul_le_mul_of_nonneg_left hg (by norm_num)
    _ = 2*a/q := by ring

-- @node: jointTail_retained_shell_integrand_bound
/-- On a retained overlap shell, the offset-weighted bias integrand is
bounded by a constant times the indicator of one joint-tail rectangle. -/
lemma jointTail_retained_shell_integrand_bound (P : RowLaw) (a q : ℝ)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q) (x : ℝ) :
    offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
          0 < effectMagnitude P x ∧
          effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ≤
      (a/q) *
      (if overlap P x ≤ 2*q ∧ 0 < effectMagnitude P x ∧
          effectMagnitude P x ≤ 2*a/q then (1:ℝ) else 0) := by
  by_cases hs : q ≤ overlap P x ∧ overlap P x < 2*q ∧
      0 < effectMagnitude P x ∧
      effectMagnitude P x ≤ 2*offsetG a P.logger x
  · have hr := jointTail_retained_shell_event_bound P a q ha hqa hq hs
    change overlap P x ≤ 2*q ∧ 0 < effectMagnitude P x ∧
      effectMagnitude P x ≤ 2*a/q at hr
    simp only [if_pos hs, if_pos hr, mul_one]
    have hp : 0 < overlap P x := lt_of_lt_of_le hq hs.1
    calc
      offsetG a P.logger x ≤ a / overlap P x := by
        unfold offsetG overlap
        exact min_le_right _ _
      _ ≤ a/q := div_le_div_of_nonneg_left ha.le hq hs.1
  · simp only [if_neg hs, mul_zero]
    split_ifs <;> positivity

-- @node: jointTail_retained_shell_envelope
/-- The two public tail conditions bound each retained dyadic shell. -/
lemma jointTail_retained_shell_envelope (P : RowLaw) (α γ θ a q : ℝ)
    (hα : 0 < α) (hγ : 0 < γ)
    (hprob : IsProbabilityMeasure P.PX)
    (hmargin : MarginCondition P α)
    (henvelope : GlobalJointEnvelope P α γ θ)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q)
    (hqhalf : 2*q ≤ 1/2) :
    P.PX.real {x | q ≤ overlap P x ∧ overlap P x < 2*q ∧
      0 < effectMagnitude P x ∧
      effectMagnitude P x ≤ 2*offsetG a P.logger x} ≤
    min (max Cm ((2:ℝ)^α) * (2*a/q)^α)
      (Co θ * (max (2*a/q) ((2*q)^(1/γ)))^α * (2*q)^θ) := by
  letI := hprob
  have hu : 0 < 2*a/q := by positivity
  have hu2 : 2*a/q ≤ 2 := by
    apply (div_le_iff₀ hq).2
    nlinarith
  have hv : 0 < 2*q := by positivity
  calc
    P.PX.real {x | q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x} ≤
      P.PX.real {x | overlap P x ≤ 2*q ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*a/q} :=
          measureReal_mono (jointTail_retained_shell_event_bound P a q ha hqa hq)
    _ ≤ _ := jointTail_two_envelopes P α γ θ (2*a/q) (2*q)
      hα hγ hprob hmargin henvelope hu hu2 hv hqhalf

-- @node: jointTail_rectangle_nullMeasurable
/-- The joint-tail rectangle is measurable modulo the score law, even when
conditional-mean versions are only specified on the supported score interval. -/
lemma jointTail_rectangle_nullMeasurable (P : RowLaw) (hwf : WellFormed P)
    (u v : ℝ) :
    NullMeasurableSet {x | overlap P x ≤ v ∧ 0 < effectMagnitude P x ∧
      effectMagnitude P x ≤ u} P.PX := by
  have hl := logger_aemeasurable P hwf
  have ht := score_tau_aemeasurable P hwf
  have hp : AEMeasurable (overlap P) P.PX := by
    unfold overlap
    fun_prop
  have hm : AEMeasurable (effectMagnitude P) P.PX := by
    unfold effectMagnitude
    fun_prop
  exact (nullMeasurableSet_le hp aemeasurable_const).inter
    ((nullMeasurableSet_lt aemeasurable_const hm).inter
      (nullMeasurableSet_le hm aemeasurable_const))

-- @node: jointTail_retained_shell_integral_mass
/-- Integration of the pointwise shell comparison converts offset weight
into the shell scale times the mass of a joint-tail rectangle. -/
lemma jointTail_retained_shell_integral_mass (P : RowLaw) (a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) ≤
      (a/q) * P.PX.real {x | overlap P x ≤ 2*q ∧
        0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2*a/q} := by
  letI := hprob
  let E := {x | overlap P x ≤ 2*q ∧ 0 < effectMagnitude P x ∧
    effectMagnitude P x ≤ 2*a/q}
  have hE : NullMeasurableSet E P.PX :=
    jointTail_rectangle_nullMeasurable P hwf (2*a/q) (2*q)
  have hupper : Integrable (E.indicator (fun _ => a/q)) P.PX :=
    (integrable_const (a/q)).indicator₀ hE
  have hnonneg : ∀ᵐ x ∂P.PX, 0 ≤ offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) := by
    apply ae_of_all
    intro x
    split_ifs with hx
    · have hp : 0 ≤ overlap P x := (hq.trans_le hx.1).le
      change 0 ≤ min 1 (a / overlap P x) * 1
      exact mul_nonneg (le_min (by norm_num) (div_nonneg ha.le hp)) (by norm_num)
    · simp
  have hbound := integral_mono_of_nonneg hnonneg hupper
    (ae_of_all _ fun x => by
      simpa only [E, Set.indicator, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero]
        using jointTail_retained_shell_integrand_bound P a q ha hqa hq x)
  rw [integral_indicator₀ hE, setIntegral_const, smul_eq_mul] at hbound
  simpa only [E, mul_comm] using hbound

-- @node: jointTail_retained_shell_integral_envelope
/-- Each retained dyadic shell contributes its offset scale times the
minimum of the margin and joint-envelope bounds from the paper. -/
lemma jointTail_retained_shell_integral_envelope (P : RowLaw) (α γ θ a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ)
    (hmargin : MarginCondition P α)
    (henvelope : GlobalJointEnvelope P α γ θ)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q) (hqhalf : 2*q ≤ 1/2) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) ≤
    (a/q) * min (max Cm ((2:ℝ)^α) * (2*a/q)^α)
      (Co θ * (max (2*a/q) ((2*q)^(1/γ)))^α * (2*q)^θ) := by
  have hu : 0 < 2*a/q := by positivity
  have hu2 : 2*a/q ≤ 2 := (div_le_iff₀ hq).2 (by nlinarith)
  exact (jointTail_retained_shell_integral_mass P a q hwf hprob ha hqa hq).trans
    (mul_le_mul_of_nonneg_left
      (jointTail_two_envelopes P α γ θ (2*a/q) (2*q) hα hγ hprob
        hmargin henvelope hu hu2 (by positivity) hqhalf) (by positivity))

-- @node: jointTail_retained_above_cutoff_integral_margin
/-- The entire retained region above a cutoff is bounded by the margin
alone. This includes overlap exactly one half and the final dyadic shell. -/
lemma jointTail_retained_above_cutoff_integral_margin (P : RowLaw) (α a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hmargin : MarginCondition P α)
    (ha : 0 < a) (hq : 0 < q) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) ≤
      (a/q) * (max Cm ((2:ℝ)^α) * (2*a/q)^α) := by
  letI := hprob
  have ht := score_tau_aemeasurable P hwf
  have hm : AEMeasurable (effectMagnitude P) P.PX := by
    unfold effectMagnitude
    fun_prop
  let E := {x | 0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2*a/q}
  have hE : NullMeasurableSet E P.PX :=
    (nullMeasurableSet_lt aemeasurable_const hm).inter
      (nullMeasurableSet_le hm aemeasurable_const)
  have hupper : Integrable (E.indicator (fun _ => a/q)) P.PX :=
    (integrable_const (a/q)).indicator₀ hE
  have hnonneg : ∀ᵐ x ∂P.PX, 0 ≤ offsetG a P.logger x *
      (if q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) := by
    apply ae_of_all
    intro x
    split_ifs with hx
    · change 0 ≤ min 1 (a / overlap P x) * 1
      exact mul_nonneg (le_min (by norm_num)
        (div_nonneg ha.le (hq.trans_le hx.1).le)) (by norm_num)
    · simp
  have hbound := integral_mono_of_nonneg hnonneg hupper (ae_of_all _ fun x => by
    by_cases hx : q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x
    · have hg : offsetG a P.logger x ≤ a/q := by
        calc
          offsetG a P.logger x ≤ a / overlap P x := min_le_right _ _
          _ ≤ a/q := div_le_div_of_nonneg_left ha.le hq hx.1
      have he : x ∈ E := ⟨hx.2.1, hx.2.2.trans (by
        simpa only [mul_div_assoc] using
          mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 2))⟩
      simp only [if_pos hx, mul_one, Set.indicator_of_mem he]
      exact hg
    · simp only [if_neg hx, mul_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) x)
  rw [integral_indicator₀ hE, setIntegral_const, smul_eq_mul] at hbound
  calc
    _ ≤ (a/q) * P.PX.real E := by simpa only [E, mul_comm] using hbound
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (jointTail_margin_all_u P α (2*a/q) hα hprob hmargin (by positivity))
      (by positivity)

-- @node: jointTail_retained_upper_region
/-- Above the upper transition, the entire retained bias has the local
power. The margin bound handles the endpoint at overlap one half directly. -/
lemma jointTail_retained_upper_region (P : RowLaw) (α γ θ a : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ)
    (hmargin : MarginCondition P α) (ha : 0 < a) :
    (∫ x, offsetG a P.logger x *
      (if a ^ (betaExp α γ θ / (betaExp α γ θ + 1)) ≤ overlap P x ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) ≤
      (max Cm ((2:ℝ)^α) * (2:ℝ)^α) * a ^ sLoc α γ θ := by
  have hb : 0 < betaExp α γ θ := by unfold betaExp; positivity
  have hd : betaExp α γ θ + 1 ≠ 0 := ne_of_gt (by positivity)
  let q := a ^ (betaExp α γ θ / (betaExp α γ θ + 1))
  have hq : 0 < q := Real.rpow_pos_of_pos ha _
  have hratio : a/q = a ^ (1/(betaExp α γ θ + 1)) := by
    have he : 1 - betaExp α γ θ / (betaExp α γ θ + 1) =
        1 / (betaExp α γ θ + 1) := by field_simp; ring
    rw [← he, Real.rpow_sub ha, Real.rpow_one]
  have hpower : (a/q) * (2*a/q)^α = (2:ℝ)^α * a ^ sLoc α γ θ := by
    rw [mul_div_assoc, Real.mul_rpow (by norm_num) (by positivity), hratio,
      ← Real.rpow_mul ha.le]
    calc
      _ = (2:ℝ)^α * (a ^ (1/(betaExp α γ θ + 1)) *
          a ^ ((1/(betaExp α γ θ + 1))*α)) := by ring
      _ = (2:ℝ)^α * a ^ sLoc α γ θ := by
        rw [← Real.rpow_add ha]
        congr 2
        unfold sLoc
        ring
  calc
    _ ≤ (a/q) * (max Cm ((2:ℝ)^α) * (2*a/q)^α) :=
      jointTail_retained_above_cutoff_integral_margin P α a q hwf hprob
        hα hmargin ha hq
    _ = _ := by
      calc
        _ = max Cm ((2:ℝ)^α) * ((a/q) * (2*a/q)^α) := by ring
        _ = _ := by rw [hpower]; ring


/-- Factoring the fixed dyadic constants out of the joint envelope leaves
one freely chosen scale that dominates both effect and overlap cutoffs. -/
-- @node: jointTail_retained_shell_normalized
lemma jointTail_retained_shell_normalized (P : RowLaw) (α γ θ a q w : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ)
    (hmargin : MarginCondition P α) (henvelope : GlobalJointEnvelope P α γ θ)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q) (hqhalf : 2*q ≤ 1/2)
    (hwa : a/q ≤ w) (hwq : q^(1/γ) ≤ w) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) ≤
      (Co θ * (max 2 ((2:ℝ)^(1/γ)))^α * (2:ℝ)^θ) *
        (a/q) * w^α * q^θ := by
  have hw : 0 ≤ w := (div_pos ha hq).le.trans hwa
  have hK : 0 ≤ max 2 ((2:ℝ)^(1/γ)) := le_trans (by norm_num) (le_max_left _ _)
  have hcut : max (2*a/q) ((2*q)^(1/γ)) ≤
      max 2 ((2:ℝ)^(1/γ)) * w := by
    apply max_le
    · calc
        2*a/q = 2*(a/q) := by ring
        _ ≤ 2*w := mul_le_mul_of_nonneg_left hwa (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
    · rw [Real.mul_rpow (by norm_num) hq.le]
      exact (mul_le_mul_of_nonneg_left hwq (by positivity)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)
  calc
    _ ≤ (a/q) * min (max Cm ((2:ℝ)^α) * (2*a/q)^α)
        (Co θ * (max (2*a/q) ((2*q)^(1/γ)))^α * (2*q)^θ) :=
      jointTail_retained_shell_integral_envelope P α γ θ a q hwf hprob
        hα hγ hmargin henvelope ha hqa hq hqhalf
    _ ≤ (a/q) * (Co θ * (max (2*a/q) ((2*q)^(1/γ)))^α * (2*q)^θ) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ ≤ (a/q) * (Co θ * (max 2 ((2:ℝ)^(1/γ)) * w)^α * (2*q)^θ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by unfold Co; positivity)
      exact Real.rpow_le_rpow (by positivity) hcut hα.le
    _ = _ := by
      rw [Real.mul_rpow hK hw, Real.mul_rpow (by norm_num) hq.le]
      ring

/-- Below the first transition, each retained shell has the lower-region
power in the paper's three-region bias decomposition. -/
-- @node: jointTail_retained_lower_shell
lemma jointTail_retained_lower_shell (P : RowLaw) (α γ θ a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ)
    (hmargin : MarginCondition P α) (henvelope : GlobalJointEnvelope P α γ θ)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q) (hqhalf : 2*q ≤ 1/2)
    (hcut : q ≤ a^(γ/(γ+1))) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) ≤
      (Co θ * (max 2 ((2:ℝ)^(1/γ)))^α * (2:ℝ)^θ) *
        a^(α+1) * q^(θ-α-1) := by
  have hb := jointTail_retained_shell_normalized P α γ θ a q (a/q)
    hwf hprob hα hγ hmargin henvelope ha hqa hq hqhalf le_rfl
    (jointTail_lower_cutoff_dominates γ a q hγ ha hq hcut)
  calc
    _ ≤ _ := hb
    _ = _ := by
      simpa only [mul_assoc] using congrArg
        (fun z : ℝ => (Co θ * (max 2 ((2:ℝ)^(1/γ)))^α * (2:ℝ)^θ) * z)
        (jointTail_lower_shell_power α θ a q ha hq)

/-- Between the transitions, each retained shell has the middle-region
power in the paper's three-region bias decomposition. -/
-- @node: jointTail_retained_middle_shell
lemma jointTail_retained_middle_shell (P : RowLaw) (α γ θ a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ)
    (hmargin : MarginCondition P α) (henvelope : GlobalJointEnvelope P α γ θ)
    (ha : 0 < a) (hqa : a ≤ q) (hq : 0 < q) (hqhalf : 2*q ≤ 1/2)
    (hcut : a^(γ/(γ+1)) ≤ q) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) ≤
      (Co θ * (max 2 ((2:ℝ)^(1/γ)))^α * (2:ℝ)^θ) *
        a * q^(θ+α/γ-1) := by
  have hb := jointTail_retained_shell_normalized P α γ θ a q (q^(1/γ))
    hwf hprob hα hγ hmargin henvelope ha hqa hq hqhalf
    (jointTail_middle_cutoff_dominates γ a q hγ ha hq hcut) le_rfl
  calc
    _ ≤ _ := hb
    _ = _ := by
      simpa only [mul_assoc] using congrArg
        (fun z : ℝ => (Co θ * (max 2 ((2:ℝ)^(1/γ)))^α * (2:ℝ)^θ) * z)
        (jointTail_middle_shell_power α γ θ a q ha hq)

end CausalSmith.Stat.ScorethresholdOverlapRegret
