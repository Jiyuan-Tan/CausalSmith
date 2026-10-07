module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance

/-!
# Deterministic support identities for the subcritical influence function

The armwise influence is supported on observations assigned to that arm.
Since the two treatment arms are disjoint, their pointwise product vanishes
and the squared contrast splits into the sum of armwise squares without a
probabilistic independence argument.
-/

public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- An armwise influence is zero away from its treatment arm. -/
lemma subcriticalInfluence_eq_zero_of_treatment_ne (c : ClassConstants) (P : SubjectLaw)
    (a : Arm) (o : ObsHistory) (ha : o.treatment ≠ a) :
    subcriticalInfluence c P a o = 0 := by
  simp [subcriticalInfluence, ha]

/-- The two armwise influences have disjoint pointwise support. -/
lemma subcriticalInfluence_crossArm_mul (c : ClassConstants) (P : SubjectLaw)
    (o : ObsHistory) :
    subcriticalInfluence c P true o * subcriticalInfluence c P false o = 0 := by
  cases h : o.treatment <;>
    simp [subcriticalInfluence_eq_zero_of_treatment_ne, h]

/-- The squared influence contrast is the sum of its armwise squares. -/
lemma subcriticalInfluence_contrast_sq (c : ClassConstants) (P : SubjectLaw)
    (o : ObsHistory) :
    (subcriticalInfluence c P true o - subcriticalInfluence c P false o) ^ 2 =
      (subcriticalInfluence c P true o) ^ 2 +
        (subcriticalInfluence c P false o) ^ 2 := by
  have hcross := subcriticalInfluence_crossArm_mul c P o
  ring_nf at hcross ⊢
  linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
