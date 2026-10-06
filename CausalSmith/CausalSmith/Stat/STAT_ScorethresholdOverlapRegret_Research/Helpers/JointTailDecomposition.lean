module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.JointTailShells

/-! # Joint-tail bias — finite retained-shell decomposition

The retained bias integral splits exactly into dyadic overlap shells and a
final upper region. The upper region includes its lower endpoint, so the
partition remains valid for arbitrary score laws with atoms.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators

/-- The retained bias integrand is integrable at every positive overlap cutoff.
The cutoff itself bounds the offset, without requiring inverse-weight integrability. -/
-- @node: jointTail_retained_integrable
@[fun_prop] lemma jointTail_retained_integrable (P : RowLaw) (a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (ha : 0 < a) (hq : 0 < q) :
    Integrable (fun x => offsetG a P.logger x *
      (if q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0)) P.PX := by
  let _ := hprob
  have hl := logger_aemeasurable P hwf
  have ht := score_tau_aemeasurable P hwf
  have hp : AEMeasurable (overlap P) P.PX := by unfold overlap; fun_prop
  have hm : AEMeasurable (effectMagnitude P) P.PX := by
    unfold effectMagnitude; fun_prop
  have hg : AEMeasurable (offsetG a P.logger) P.PX := by
    unfold offsetG; fun_prop
  have hE : NullMeasurableSet {x | q ≤ overlap P x ∧
      0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2*offsetG a P.logger x} P.PX :=
    (nullMeasurableSet_le aemeasurable_const hp).inter
      ((nullMeasurableSet_lt aemeasurable_const hm).inter
        (nullMeasurableSet_le hm (aemeasurable_const.mul hg)))
  have hmeas : AEMeasurable (fun x => offsetG a P.logger x *
      (if q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0)) P.PX := by
    convert hg.indicator₀ hE using 1
    ext x
    simp [Set.indicator, mul_ite]
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  apply ae_of_all
  intro x
  split_ifs with hx
  · rw [mul_one, Real.norm_eq_abs, abs_of_nonneg]
    · exact min_le_left _ _
    · exact le_min zero_le_one (div_nonneg ha.le (hq.trans_le hx.1).le)
  · simp

/-- Restricting a retained region to one half-open overlap shell preserves integrability. -/
-- @node: jointTail_shell_integrable
@[fun_prop] lemma jointTail_shell_integrable (P : RowLaw) (a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (ha : 0 < a) (hq : 0 < q) :
    Integrable (fun x => offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧
        0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2*offsetG a P.logger x
        then (1:ℝ) else 0)) P.PX := by
  have hl := logger_aemeasurable P hwf
  have hp : AEMeasurable (overlap P) P.PX := by unfold overlap; fun_prop
  have hE := nullMeasurableSet_lt hp (aemeasurable_const (b := 2*q))
  convert (jointTail_retained_integrable P a q hwf hprob ha hq).indicator₀ hE using 1 <;> try rfl
  ext x
  by_cases h : overlap P x < 2*q <;> simp [Set.indicator, h]

/-- Splitting at twice the overlap cutoff assigns the boundary to the upper region. -/
-- @node: jointTail_retained_split
lemma jointTail_retained_split (P : RowLaw) (a q : ℝ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (ha : 0 < a) (hq : 0 < q) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) =
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ overlap P x < 2*q ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) +
    (∫ x, offsetG a P.logger x *
      (if 2*q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) := by
  rw [← integral_add (jointTail_shell_integrable P a q hwf hprob ha hq)
    (jointTail_retained_integrable P a (2*q) hwf hprob ha (by positivity))]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  by_cases hqX : q ≤ overlap P x
  · by_cases h2qX : 2*q ≤ overlap P x
    · have hn : ¬ overlap P x < 2*q := not_lt.mpr h2qX
      simp [hqX, h2qX, hn]
    · have hlt : overlap P x < 2*q := lt_of_not_ge h2qX
      simp [hqX, h2qX, hlt]
  · have h2qX : ¬ 2*q ≤ overlap P x := by linarith
    simp [hqX, h2qX]

/-- Iterating the exact split gives a finite dyadic partition with an upper tail.
No mass at the final cutoff, including overlap one half, is lost. -/
-- @node: jointTail_retained_dyadic_decomposition
lemma jointTail_retained_dyadic_decomposition (P : RowLaw) (a q : ℝ) (N : ℕ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (ha : 0 < a) (hq : 0 < q) :
    (∫ x, offsetG a P.logger x *
      (if q ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) =
    (∑ k ∈ Finset.range N, ∫ x, offsetG a P.logger x *
      (if q*(2:ℝ)^k ≤ overlap P x ∧ overlap P x < 2*(q*(2:ℝ)^k) ∧
        0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2*offsetG a P.logger x
        then (1:ℝ) else 0) ∂P.PX) +
    (∫ x, offsetG a P.logger x *
      (if q*(2:ℝ)^N ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then (1:ℝ) else 0) ∂P.PX) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ,
      jointTail_retained_split P a (q*(2:ℝ)^N) hwf hprob ha (by positivity)]
    have he : q*(2:ℝ)^(N+1) = 2*(q*(2:ℝ)^N) := by rw [pow_succ]; ring
    rw [he]
    ring

/-- The bias is bounded by finitely many joint-tail shell estimates plus the
margin-controlled final region. This is the analytic bridge to dyadic summation. -/
-- @node: jointTail_bias_finite_shell_bound
lemma jointTail_bias_finite_shell_bound (P : RowLaw) (α γ θ a : ℝ) (N : ℕ)
    (hwf : WellFormed P) (hprob : IsProbabilityMeasure P.PX)
    (hα : 0 < α) (hγ : 0 < γ)
    (hmargin : MarginCondition P α) (henvelope : GlobalJointEnvelope P α γ θ)
    (hmag : ∀ᵐ x ∂P.PX, effectMagnitude P x ≤ 2)
    (ha : 0 < a) (hawindow : a ≤ co * (2 : ℝ) ^ γ)
    (hgrid : ∀ k ∈ Finset.range N, 2 * (a * (2 : ℝ) ^ k) ≤ 1 / 2) :
    biasFunctional P a ≤ Co θ*(2:ℝ)^α*a^θ +
      (∑ k ∈ Finset.range N, (a/(a*(2:ℝ)^k)) *
        min (max Cm ((2:ℝ)^α) * (2*a/(a*(2:ℝ)^k))^α)
          (Co θ * (max (2*a/(a*(2:ℝ)^k))
            ((2*(a*(2:ℝ)^k))^(1/γ)))^α * (2*(a*(2:ℝ)^k))^θ)) +
      (a/(a*(2:ℝ)^N)) *
        (max Cm ((2:ℝ)^α) * (2*a/(a*(2:ℝ)^N))^α) := by
  have hscale (k : ℕ) : a ≤ a*(2:ℝ)^k := by
    have hpow : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    nlinarith
  have hs :
      (∑ k ∈ Finset.range N, ∫ x, offsetG a P.logger x *
        (if a*(2:ℝ)^k ≤ overlap P x ∧ overlap P x < 2*(a*(2:ℝ)^k) ∧
          0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2*offsetG a P.logger x
          then (1:ℝ) else 0) ∂P.PX) ≤
      ∑ k ∈ Finset.range N, (a/(a*(2:ℝ)^k)) *
        min (max Cm ((2:ℝ)^α) * (2*a/(a*(2:ℝ)^k))^α)
          (Co θ * (max (2*a/(a*(2:ℝ)^k))
            ((2*(a*(2:ℝ)^k))^(1/γ)))^α * (2*(a*(2:ℝ)^k))^θ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact jointTail_retained_shell_integral_envelope P α γ θ a (a*(2:ℝ)^k)
      hwf hprob hα hγ hmargin henvelope ha (hscale k) (by positivity) (hgrid k hk)
  unfold biasFunctional
  rw [jointTail_retained_dyadic_decomposition P a a N hwf hprob ha ha]
  have hd := jointTail_deleted_negative_bound P α γ θ a hprob henvelope
    hmag ha hawindow
  have hu := jointTail_retained_above_cutoff_integral_margin P α a (a*(2:ℝ)^N)
    hwf hprob hα hmargin ha (by positivity)
  exact (add_le_add hd (add_le_add hs hu)).trans_eq (by ring)

end CausalSmith.Stat.ScorethresholdOverlapRegret
