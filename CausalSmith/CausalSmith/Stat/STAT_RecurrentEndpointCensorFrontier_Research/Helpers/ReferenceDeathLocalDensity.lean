module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedArmModel
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ReferenceDeathTail
public import Causalean.Stat.RecurrentEvent.HazardDensity

/-!
# Local density of the reference death law

This module rewrites the promoted finite-horizon death density in the paper's
survival-times-hazard notation on the study window.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The promoted hazard generates the paper survival on the study window. -/
lemma promotedArmHazard_survival_eq {c : ClassConstants} {P : SubjectLaw}
    (hP : ModelClass c P) (a : Arm) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.RecurrentEvent.hazardSurvival (promotedArmHazard P a) t =
      survival P a t := by
  unfold Causalean.Stat.RecurrentEvent.hazardSurvival survival
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
    have hut : u ∈ Set.uIcc (0 : ℝ) t := hu
    rw [Set.uIcc_of_le ht.1] at hut
    exact ⟨hut.1, hut.2.trans ht.2⟩
  exact promotedArmHazard_coe hP a hu'

/-- On `[0,1)`, the original death law has density paper survival times paper hazard. -/
lemma armDeathEventLaw_restrict_Ico_eq_withDensity {c : ClassConstants}
    {P : SubjectLaw} (hP : ModelClass c P) (a : Arm) :
    (armDeathEventLaw P a).restrict (Set.Ico 0 1) =
      (volume.restrict (Set.Ico 0 1)).withDensity
        (fun t => ENNReal.ofReal (survival P a t * P.hazard a t)) := by
  have hd := (promotedArmModel P hP a).death_law_restrict_eq_withDensity
  have hd' : (armDeathEventLaw P a).restrict (Set.Ico 0 1) =
      (volume.restrict (Set.Ico 0 1)).withDensity
        (fun t => ENNReal.ofReal
          (Causalean.Stat.RecurrentEvent.hazardSurvival (promotedArmHazard P a) t) *
            (promotedArmHazard P a t : ENNReal)) := by
    simpa only [armDeathEventLaw, promotedArmModel_deathLaw,
      promotedArmModel_horizon, promotedArmModel_hazard] using hd
  rw [hd']
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  rw [promotedArmHazard_survival_eq hP a ht', ENNReal.coe_nnreal_eq,
    promotedArmHazard_coe hP a ht']
  exact (ENNReal.ofReal_mul (p := survival P a t) (q := P.hazard a t)
    (le_of_lt (Real.exp_pos _))).symm

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
