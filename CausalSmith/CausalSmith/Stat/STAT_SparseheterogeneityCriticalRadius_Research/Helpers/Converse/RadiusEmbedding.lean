module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.FixedSampleSupport

/-! Monotone embedding of the radius-zero class into every supplied radius. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open Set

/-- An exactly homogeneous law remains admissible at every supplied radius in
`[0,2]`.  This is the class embedding used for the parametric `1/n` floor. -/
-- keep: public class-embedding endpoint for the parametric lower-bound branch
lemma radiusZeroClass_to_radius {n : ℕ} {M rho : ℝ}
    (P : KnownRadiusClass n M 0) (hrho : rho ∈ Set.Icc (0 : ℝ) 2) :
    ∃ Q : KnownRadiusClass n M rho, Q.law = P.law := by
  let Q : KnownRadiusClass n M rho :=
    { P with
      radius := by
        refine ⟨hrho, ?_⟩
        intro k hk
        have hz := P.radius.2 k hk
        have hdev :
            DiscreteAteHeterogeneityFrontier.cellDeviation P.law k = 0 := by
          apply abs_eq_zero.mp
          exact le_antisymm (by simpa using hz) (abs_nonneg _)
        rw [hdev, abs_zero]
        exact mul_nonneg hrho.1 (by linarith [P.M_ge_one]) }
  exact ⟨Q, rfl⟩

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
