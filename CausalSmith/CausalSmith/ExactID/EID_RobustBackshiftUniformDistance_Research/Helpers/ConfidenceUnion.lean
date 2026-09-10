import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.MatrixMargins
import Mathlib.Data.Rat.Defs

/-!
# Set-valued confidence unions

Finite subset consensus, arbitrary covariance-region selections, honest-region radius, and the
resulting population compatibility union.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator ENNReal

-- @env: S3
variable {p m c : ℕ}

/-- The four prespecified rational true-instance margins. -/
structure MarginParameters where
  gammaLower : ℚ -- @realizes gamma0(positive rational affine-separation lower bound)
  gammaLower_pos : 0 < gammaLower -- @realizes gamma0(gamma0 > 0)
  zetaLower : ℚ -- @realizes zeta0(rational normalization-slack lower bound)
  zetaLower_pos : 0 < zetaLower -- @realizes zeta0(zeta0 > 0)
  zetaLower_le_one : zetaLower ≤ 1 -- @realizes zeta0(zeta0 ≤ 1)
  conditionUpper : ℚ -- @realizes kappabar(rational condition-number upper bound)
  one_le_conditionUpper : 1 ≤ conditionUpper -- @realizes kappabar(kappabar ≥ 1)
  scaleUpper : ℚ -- @realizes Mbar(rational scale upper bound)
  one_le_scaleUpper : 1 ≤ scaleUpper -- @realizes Mbar(Mbar ≥ 1)

/-- Positive sample-size indices. -/
abbrev PositiveSampleSize := {n : ℕ // 0 < n}

/-- An inference index and a complete positive-sample-size-indexed family of arbitrary nonempty
PSD covariance regions at the fixed confidence level. -/
structure InferenceWorld (p m : ℕ) where
  sampleSize : PositiveSampleSize -- @realizes n(positive integer current sample size)
  alpha : ℝ -- @realizes alpha(real nominal noncoverage level)
  alpha_pos : 0 < alpha -- @realizes alpha(alpha > 0)
  alpha_lt_one : alpha < 1 -- @realizes alpha(alpha < 1)
  regions : PositiveSampleSize → Environment m → Set (RealMatrix p)
    -- @realizes Calpha(complete family indexed by every positive sample size)
  regions_nonempty : ∀ n e, (regions n e).Nonempty
    -- @realizes Calpha(each indexed region nonempty)
  regions_psd : ∀ n e A, A ∈ regions n e → A.PosSemidef
    -- @realizes Calpha(each indexed region contained in PSDp)

/-- The covariance regions selected at the inference world's current positive sample size. -/
def InferenceWorld.currentRegions (V : InferenceWorld p m) :
    Environment m → Set (RealMatrix p) :=
  V.regions V.sampleSize

/-- The per-subset full exact solution set used by subset consensus. -/
def subsetFeasible (p m : ℕ) (K : Finset (Environment m))
    (covarianceFamily : Environment m → RealMatrix p) : Set (RealMatrix p) :=
  {A | A ∈ admissibleSet p ∧
    ∃ Psi : RealMatrix p, Psi.PosSemidef ∧
      ∃ t : Environment m → Fin p → ℝ,
        (∀ e ∈ K, ∀ j, 0 ≤ t e j) ∧
        ∀ e ∈ K,
          covarianceFamily e = A⁻¹ * (Psi + Matrix.diagonal (t e)) * A⁻¹.transpose}

-- @node: def:subset-consensus
/-- Set-theoretic union of all full feasibility solution sets on exactly `m-c` slots.

@realizes SubsetConsensus(union over all h-subsets)
-/
noncomputable def subsetConsensus (p m c : ℕ)
    (covarianceFamily : PSDCovarianceFamily p m) : Set (RealMatrix p) :=
  ⋃ K ∈ (Finset.univ : Finset (Environment m)).powersetCard (honestCount m c),
    subsetFeasible p m K covarianceFamily.1

/-- Subset consensus is extensionally the replacement compatibility set. -/
private lemma subsetConsensus_eq_compatibleSet (p m c : ℕ)
    (covarianceFamily : PSDCovarianceFamily p m) :
    subsetConsensus p m c covarianceFamily = compatibleSet p m c covarianceFamily := by
  ext A
  constructor
  · intro hA
    simp only [subsetConsensus, Set.mem_iUnion] at hA
    rcases hA with ⟨K, hA⟩
    rcases hA with ⟨hK, hA⟩
    have hKcard : K.card = honestCount m c :=
      (Finset.mem_powersetCard.mp hK).2
    rcases hA with ⟨hAdm, Psi, hPsi, t, ht, hEq⟩
    exact ⟨hAdm, K, hKcard.ge, Psi, hPsi, t, ht, hEq⟩
  · intro hA
    rcases hA with ⟨hAdm, K, hKcard, Psi, hPsi, t, ht, hEq⟩
    obtain ⟨K', hK'sub, hK'card⟩ := Finset.exists_subset_card_eq hKcard
    simp only [subsetConsensus, Set.mem_iUnion]
    refine ⟨K', ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K', hK'card⟩
    · exact ⟨hAdm, Psi, hPsi, t,
        fun e he j ↦ ht e (hK'sub he) j,
        fun e he ↦ hEq e (hK'sub he)⟩

-- @node: def:honest-region-radius
/-- Extended honest-slot radius of arbitrary matrix regions around the population covariances.

@realizes rRadius(maximum over honest slots of regional operator radius)
-/
noncomputable def honestRegionRadius (V : InferenceWorld p m)
    (H : Finset (Environment m))
    (covarianceFamily : PSDCovarianceFamily p m) : ℝ≥0∞ :=
  ⨆ e ∈ H, ⨆ Gamma ∈ V.currentRegions e, edist Gamma (covarianceFamily.1 e)

-- @node: def:confidence-union
/-- Union of population compatibility sets over all simultaneous covariance-region selections.

@realizes Ualpha(set-theoretic confidence union indexed by n and alpha)
-/
noncomputable def confidenceUnion (c : ℕ) (V : InferenceWorld p m) : Set (RealMatrix p) :=
  ⋃ (Gamma : Environment m → RealMatrix p)
      (hGamma : ∀ e, Gamma e ∈ V.currentRegions e),
    compatibleSet p m c
      ⟨Gamma, fun e ↦ V.regions_psd V.sampleSize e (Gamma e) (hGamma e)⟩

end CausalSmith.ExactID.RobustBackshiftUniformDistance
