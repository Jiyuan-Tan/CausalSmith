import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Witness32
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.T1_FiniteResponseConverse
import Mathlib.Analysis.Convex.Intrinsic

/-! # Exact thirty-two-type refinement certificate -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open Set

/-- The explicit witness incidence is nonnegative and column-stochastic. -/
lemma witness32Incidence_stochastic :
    (∀ o t, 0 ≤ witness32Incidence o t) ∧
      (∀ t, ∑ o, witness32Incidence o t = 1) := by
  sorry

/-- The generic finite geometry represented by the explicit table. -/
noncomputable def witness32Geometry : SLCCIncidence (Fin 12) (Fin 32) (Fin 8) where
  B := witness32Incidence
  B_nonnegative := witness32Incidence_stochastic.1
  B_column_sum := witness32Incidence_stochastic.2
  h := witness32Target
  h_binary := by intro i; simp [witness32Target]
  K := witness32Coarsening

/-- Every legal type has a displayed representative with the same two trial
responses and the same untrialed target. -/
def Witness32CompleteQuotientCover : Prop :=
  ∀ t : LegalResponseType witness32Design, ∃ i : Fin 32,
    (∀ j : Fin 2,
      let c := witness32Design.config (witness32Design.trialPolicy j)
        t.raw.stratum
      t.raw.actionResponse c = witness32Action i c ∧
      t.raw.outcomeResponse c = witness32Outcome i c ∧
      (t.raw.actionResponse c = true →
        t.raw.truth = decide (16 ≤ i.val))) ∧
    targetVector witness32Design t = witness32Target i

/-- The explicit rational twelve-cell vectors in the table's row order. -/
noncomputable def witness32LawExplicit : Fin 12 → ℝ :=
  ![4/96, 4/96, 1/96, 13/96, 3/96, 23/96,
    4/96, 4/96, 3/96, 11/96, 1/96, 25/96]

noncomputable def witness32LawCircExplicit : Fin 12 → ℝ :=
  ![68/1600, 68/1600, 17/1600, 216/1600, 51/1600, 380/1600,
    68/1600, 68/1600, 51/1600, 182/1600, 17/1600, 414/1600]

/-- All legality, quotient-cover, exact endpoint, rational-law, and
relative-interior claims of the thirty-two-type certificate. -/
-- @node: thm:complete-32-type-refinement-certificate
theorem complete_32_type_refinement_certificate :
    Function.Injective witness32Type ∧
    Witness32CompleteQuotientCover ∧
    (∀ o : Fin 12, ∃ i : Fin 32, witness32Incidence o i = 1 / 2) ∧
    (∀ pi, Witness32Parameter pi →
      lowerEndpoint witness32Geometry (witness32Law pi) = pi 0 + pi 1 ∧
      upperEndpoint witness32Geometry (witness32Law pi) = pi 0 + pi 1 + pi 3 ∧
      (blindEndpointPrograms witness32Geometry (witness32Law pi)).1 = pi 0 ∧
      (blindEndpointPrograms witness32Geometry (witness32Law pi)).2 = 1) ∧
    witness32Law witness32Pi0 = witness32LawExplicit ∧
    witness32Law witness32PiCirc = witness32LawCircExplicit ∧
    lowerEndpoint witness32Geometry (witness32Law witness32Pi0) = 1 / 2 ∧
    upperEndpoint witness32Geometry (witness32Law witness32Pi0) = 3 / 4 ∧
    (blindEndpointPrograms witness32Geometry (witness32Law witness32Pi0)).1 = 1 / 4 ∧
    (blindEndpointPrograms witness32Geometry (witness32Law witness32Pi0)).2 = 1 ∧
    lowerEndpoint witness32Geometry (witness32Law witness32PiCirc) = 397 / 800 ∧
    upperEndpoint witness32Geometry (witness32Law witness32PiCirc) = 601 / 800 ∧
    (blindEndpointPrograms witness32Geometry (witness32Law witness32PiCirc)).1 = 99 / 400 ∧
    (blindEndpointPrograms witness32Geometry (witness32Law witness32PiCirc)).2 = 1 ∧
    witness32Law witness32Pi0 ∈ intrinsicInterior ℝ (observablePolytope witness32Geometry) ∧
    witness32Law witness32PiCirc ∈ intrinsicInterior ℝ (observablePolytope witness32Geometry) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
