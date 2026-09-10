import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Witnesses
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.TSparseWitnessCertificate
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic edge perturbation

The lemma states the path integral identity, analytic nonidentity certificate,
isolated-zero property, and arbitrarily small stratum-preserving perturbation.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Direct-edge contrast along the identity-target affine path. -/
def affinePathContrast {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    (θ : StratumPoint G s) {j i : Fin n} (hji : G.edge j i) (t : ℝ) : ℝ :=
  let θt := affinePathExtension s θ hji t
  secondMomentContrast (canonicalObservedWorld G θt (Equiv.refl (Fin n))) j i

/-- The explicit rational-integral expression for the direct-edge path contrast. -/
def affinePathContrastIntegral {n : ℕ} {G : Causalean.DAG (Fin n)}
    (s : SignVector n) (θ : StratumPoint G s) {j i : Fin n}
    (hji : G.edge j i) (t : ℝ) : ℝ :=
  let θt := affinePathExtension s θ hji t
  ∫ v in latentCube n,
    (θt.q i (v i)) ^ 2 * (θt.q j (v j) - θt.p j v) *
      (∏ l ∈ (Finset.univ.erase i).erase j, θt.p l v) / θt.p i v

-- @node: lem:analytic-edge-perturbation
/-- Every edge admits arbitrarily small stratum-preserving affine perturbations with nonzero
second-moment contrast; the contrast has the stated analytic integral and isolated zeros. -/
lemma analytic_edge_perturbation
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (θs : StratumPoint G s) {j i : Fin n} (hji : G.edge j i)
    (hIntervention : OnePerfectInterventionPerNode G θs.1
      (canonicalObservedWorld G θs.1 (Equiv.refl (Fin n)))) :
    (∃ O : Set ℝ, IsOpen O ∧ Set.Icc (0 : ℝ) 1 ⊆ O ∧
      (∀ t ∈ O, affinePathContrast s θs hji t =
        affinePathContrastIntegral s θs hji t) ∧
      AnalyticOnNhd ℝ (affinePathContrast s θs hji) O ∧
      ∀ t ∈ O, affinePathContrast s θs hji t = 0 →
        ∃ ε > 0, ∀ u ∈ Set.Ioo (t - ε) (t + ε), u ≠ t →
          affinePathContrast s θs hji u ≠ 0) ∧
    affinePathContrast s θs hji 1 ≠ 0 ∧
    (∀ N ∈ 𝓝 θs.1, ∃ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1},
      affinePath s θs hji ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩ ∈ N ∧
      ModelStratum G s (affinePath s θs hji
        ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩) ∧
      affinePathContrast s θs hji t.1 ≠ 0) := by sorry

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
