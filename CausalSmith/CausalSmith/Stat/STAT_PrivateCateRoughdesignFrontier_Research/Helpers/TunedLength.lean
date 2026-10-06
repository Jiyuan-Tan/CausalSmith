module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TuningEnvelope
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.UpperGuarantees
/-! Uniform expected interval length under the public tuning, including its fallback branch. -/
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The tuned variance envelope bounds twice the conservative interval radius.  [the theorem's stated inputs and assumptions](hyp:he,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: tuned_interval_radius_le
lemma tuned_interval_radius_le (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hr : rate n epsilon < 1 / 8) :
    2 * Real.sqrt (10 * Vbound n epsilon (tunedH n epsilon) (tunedK n epsilon)) ≤
      2^22 * rate n epsilon := by
  have hv := tuned_Vbound_le n epsilon hn he hr
  have hr0 := (rate_pos n epsilon (by omega)).le
  have hs : Real.sqrt (10 * Vbound n epsilon (tunedH n epsilon) (tunedK n epsilon)) ≤
      2^21 * rate n epsilon := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (rate n epsilon)]
  nlinarith

/-- The public full-range fallback has length two under every model law.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P). -/
-- @node: full_interval_expectedLength
lemma full_interval_expectedLength (n : ℕ) (P : CausalLaw) :
    expectedLength n (Kernel.const (Dataset n) (Measure.dirac (closedInterval (-1) 1))) P = 2 := by
  let : IsProbabilityMeasure (Pobs P) := by
    unfold Pobs
    exact Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  unfold expectedLength
  change (∫⁻ c, c.leb ∂(dataLaw n P).bind
    (fun _ => Measure.dirac (closedInterval (-1) 1))) = 2
  rw [Measure.bind_const, measure_univ, one_smul, lintegral_dirac]
  rw [closedInterval_leb]
  norm_num

/-- The tuned interval obeys the stated expected-length rate at every law, from the deterministic
radius bound on the active branch and the full-range length on the fallback branch.  [the theorem's stated inputs and assumptions](hyp:he,P), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: publicTunedInterval_expectedLength_le
lemma publicTunedInterval_expectedLength_le (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (P : CausalLaw) :
    expectedLength n (publicTunedInterval n epsilon) P ≤
      ENNReal.ofReal (2^22 * rate n epsilon) := by
  classical
  unfold publicTunedInterval
  split_ifs with hr
  · rw [full_interval_expectedLength]
    have hb : (2 : ℝ) ≤ 2^22 * rate n epsilon := by nlinarith
    calc
      (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb
  · exact (Ihk_expectedLength_le n _ epsilon _ he.1 P).trans
      (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans
        (tuned_interval_radius_le n epsilon hn he (lt_of_not_ge hr))))

/-- Taking the supremum over the full model preserves the public interval-length bound.  [the theorem's stated inputs and assumptions](hyp:he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: publicTunedInterval_worstLength_le
lemma publicTunedInterval_worstLength_le (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) :
    worstLength n (publicTunedInterval n epsilon) ≤ ENNReal.ofReal (2^22 * rate n epsilon) := by
  unfold worstLength
  exact iSup_le fun P => iSup_le fun _ => publicTunedInterval_expectedLength_le n epsilon hn he P

end CausalSmith.Stat.PrivateCateRoughdesign
