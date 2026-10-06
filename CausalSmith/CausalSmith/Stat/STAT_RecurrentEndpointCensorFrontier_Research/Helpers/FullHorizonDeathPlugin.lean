module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RemainingMeanIdentification
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.TerminalDeathVariationEnergy

/-! # Full-horizon replacement of future recurrence marks

Proof roadmap (38)--(40): choose a strict horizon using the uniform terminal
expectation envelope, then apply localized plug-in consistency. This proves
replacement for the actual future-mark death studentizer without predictability
of its estimated remaining mean.
-/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- An eventual terminal bound can be used at a strict, nonnegative horizon. -/
-- @node: exists_strict_study_horizon_of_eventually
lemma exists_strict_study_horizon_of_eventually {Q : ℝ → Prop}
    (hQ : ∀ᶠ T in nhdsWithin 1 (Icc (0 : ℝ) 1), Q T) :
    ∃ T : ℝ, 0 ≤ T ∧ T < 1 ∧ Q T := by
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhdsWithin_iff.mp hQ
  let r : ℝ := min (δ / 2) (1 / 2)
  have hr : 0 < r := lt_min (half_pos hδ) (by norm_num)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hr1 : r ≤ 1 / 2 := min_le_right _ _
  refine ⟨1 - r, by linarith, by linarith, hb ?_⟩
  constructor
  · rw [Metric.mem_ball, Real.dist_eq, show 1 - r - 1 = -r by ring,
      abs_neg, abs_of_pos hr]
    exact hrδ
  · constructor <;> linarith

/-- Estimated future recurrence marks may be replaced by the deterministic
remaining target in the full death optional variation, in probability under
the model class alone. -/
-- @node: fullDeathVariation_plugin_probability_tendsto_zero
lemma fullDeathVariation_plugin_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |localizedDeathVariation a s 1 (remainingMeanHat c a s) -
        localizedDeathVariation a s 1 (remainingTarget c P a 0)|}) atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n => hl.trans_le measureReal_nonneg)
  · intro η hη
    obtain ⟨T, hT0, hT1, htail⟩ := exists_strict_study_horizon_of_eventually
      (tailDeathVariation_envelope_probability_uniform_small c P hP hk a
        (half_pos hε) (half_pos hη))
    have hlocal := (localizedDeathVariation_plugin_probability_tendsto_zero
      c P hP hk a hT0 hT1 (ε / 2) (half_pos hε)).eventually
        (gt_mem_nhds (half_pos hη))
    filter_upwards [hlocal, eventually_ge_atTop 1] with n hn hn1
    have hb := fullDeathVariation_plugin_probability_le_local_and_tail c P hP a n
      (ε := ε) hT1.le
    have ht := htail n (show 0 < n by omega)
    exact hb.trans_lt (by linarith)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
