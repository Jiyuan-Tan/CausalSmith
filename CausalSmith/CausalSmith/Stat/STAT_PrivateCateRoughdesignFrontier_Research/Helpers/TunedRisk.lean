module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TunedLength
/-! Absolute risk from the squared-error envelope under public tuning. -/
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Young's quadratic inequality converts a second moment to an absolute first moment.  [the theorem's stated inputs and assumptions](hyp:t,B,hB,hmse), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:Q). -/
-- @node: absolute_moment_le_of_squared_moment
lemma absolute_moment_le_of_squared_moment (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (t B : ℝ) (hB : 0 < B)
    (hmse : (∫⁻ u, ENNReal.ofReal ((u-t)^2) ∂Q) ≤ ENNReal.ofReal (B^2)) :
    (∫⁻ u, ENNReal.ofReal |u-t| ∂Q) ≤ ENNReal.ofReal B := by
  have hy (u : ℝ) : |u-t| ≤ (2*B)⁻¹ * (u-t)^2 + B/2 := by
    rw [inv_mul_eq_div]
    have hs := sq_nonneg (|u-t|-B)
    have heq : (2*B) * ((u-t)^2 / (2*B) + B/2) = (u-t)^2 + B^2 := by
      field_simp
    apply (mul_le_mul_iff_right₀ (show 0 < 2*B by positivity)).mp
    rw [heq]
    nlinarith [sq_abs (u-t)]
  calc
    (∫⁻ u, ENNReal.ofReal |u-t| ∂Q) ≤
        ∫⁻ u, ENNReal.ofReal ((2*B)⁻¹) * ENNReal.ofReal ((u-t)^2) +
          ENNReal.ofReal (B/2) ∂Q := by
      apply lintegral_mono
      intro u
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hy u)
    _ = ENNReal.ofReal ((2*B)⁻¹) * (∫⁻ u, ENNReal.ofReal ((u-t)^2) ∂Q) +
        ENNReal.ofReal (B/2) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul]
      · simp
      · fun_prop
    _ ≤ ENNReal.ofReal ((2*B)⁻¹) * ENNReal.ofReal (B^2) + ENNReal.ofReal (B/2) :=
      add_le_add (mul_le_mul le_rfl hmse zero_le zero_le) le_rfl
    _ = ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      ring

/-- The data-independent zero release has absolute risk at most one throughout the model.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,hP). -/
-- @node: zero_release_scalarRisk_le
lemma zero_release_scalarRisk_le (n : ℕ) (P : CausalLaw) (hP : CompleteModel P) :
    scalarRisk n (Kernel.const (Dataset n) (Measure.dirac 0)) P ≤ 1 := by
  letI : IsProbabilityMeasure (Pobs P) := by
    unfold Pobs
    exact Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  unfold scalarRisk
  change (∫⁻ u, ENNReal.ofReal |u-theta P| ∂(dataLaw n P).bind
    (fun _ => Measure.dirac 0)) ≤ 1
  rw [Measure.bind_const, measure_univ, one_smul, lintegral_dirac]
  have ht := theta_mem_Icc P hP
  have ha : |0-theta P| ≤ 1 := by rw [zero_sub, abs_neg]; exact abs_le.mpr ht
  simpa using ENNReal.ofReal_le_ofReal ha

/-- The active tuned scalar release attains the absolute-risk rate from its second moment.  [the theorem's stated inputs and assumptions](hyp:he,hr,P,hmse), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,epsilon,hn). -/
-- @node: tuned_scalarRisk_le_of_squared_error_le
lemma tuned_scalarRisk_le_of_squared_error_le (n : ℕ) (epsilon : ℝ) (hn : 2 ≤ n)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hr : rate n epsilon < 1/8)
    (P : CausalLaw)
    (hmse : (∫⁻ u, ENNReal.ofReal ((u-theta P)^2)
      ∂(Thk n epsilon (tunedH n epsilon) (tunedK n epsilon) ∘ₘ dataLaw n P)) ≤
      ENNReal.ofReal (Vbound n epsilon (tunedH n epsilon) (tunedK n epsilon))) :
    scalarRisk n (Thk n epsilon (tunedH n epsilon) (tunedK n epsilon)) P ≤
      ENNReal.ofReal (2^18 * rate n epsilon) := by
  letI : IsProbabilityMeasure (Pobs P) := by
    unfold Pobs
    exact Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  letI := (Thk_private n (tunedK n epsilon) epsilon (tunedH n epsilon) he.1
    (public_tuning_parameters n epsilon hn he hr).1
    (by have hp := public_tuning_parameters n epsilon hn he hr; omega)).markov
  have hv := tuned_Vbound_le n epsilon hn he hr
  have hb : Vbound n epsilon (tunedH n epsilon) (tunedK n epsilon) ≤
      (2^18 * rate n epsilon)^2 := by nlinarith [sq_nonneg (rate n epsilon)]
  exact absolute_moment_le_of_squared_moment _ _ _
    (by have hp := rate_pos n epsilon (by omega); positivity)
    (hmse.trans (ENNReal.ofReal_le_ofReal hb))

/-- The fallback and active tuning branches give the uniform scalar-risk rate once the
uniform statistical second moment has been proved. The result uses [the stated assumptions](hyp:hn,he,hmse) and establishes [the displayed conclusion](goal). -/
-- @node: publicTunedRelease_worstRisk_of_squared_error_le
lemma publicTunedRelease_worstRisk_of_squared_error_le (n : ℕ) (epsilon : ℝ)
    (hn : 2 ≤ n) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (hmse : ∀ (k : ℕ) (h : ℝ), 2 ≤ k → (0 < h ∧ h ≤ 1/4) →
      ∀ P : CausalLaw, CompleteModel P →
        (∫⁻ u, ENNReal.ofReal ((u-theta P)^2) ∂(Thk n epsilon h k ∘ₘ dataLaw n P)) ≤
          ENNReal.ofReal (Vbound n epsilon h k)) :
    worstRisk n (publicTunedRelease n epsilon) ≤ ENNReal.ofReal (2^18 * rate n epsilon) := by
  classical
  unfold worstRisk
  refine iSup_le fun P => iSup_le fun hP => ?_
  unfold publicTunedRelease
  split_ifs with hr
  · have hb : (1 : ℝ) ≤ 2^18 * rate n epsilon := by nlinarith
    exact (zero_release_scalarRisk_le n P hP).trans (by
      simpa using ENNReal.ofReal_le_ofReal hb)
  · have hr' := lt_of_not_ge hr
    have hp := public_tuning_parameters n epsilon hn he hr'
    exact tuned_scalarRisk_le_of_squared_error_le n epsilon hn he hr' P
      (hmse _ _ hp.2.2.1 ⟨hp.1, hp.2.1⟩ P hP)

end CausalSmith.Stat.PrivateCateRoughdesign
