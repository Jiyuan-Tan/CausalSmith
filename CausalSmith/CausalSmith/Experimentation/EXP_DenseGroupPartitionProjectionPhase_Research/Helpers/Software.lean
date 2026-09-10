import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Asymptotics
import Mathlib.Analysis.Matrix.Order

/-!
# Versioned software contracts

The declarations in this file are cited logical gates.  They expose only the
mathematical claims attributed to the pinned `clubSandwich` and `sandwich`
sources; no Lean proof of package semantics is asserted.
-/

open scoped BigOperators Matrix

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

/-- Algebraic semantics of an unweighted full-column-rank OLS fit with
possibly unequal cluster sizes, including fitted-observation residuals and the
normal equations. -/
noncomputable def UnweightedFullRankLmFit {G p : ℕ} (m : Fin G → ℕ)
    (X : ∀ g, Matrix (Fin (m g)) (Fin p) ℝ)
    (y e : ∀ g, Fin (m g) → ℝ) : Prop :=
  ∃ beta : Fin p → ℝ,
    (∀ g i, e g i = y g i - ∑ j, X g i j * beta j) ∧
    (∀ j, ∑ g, ∑ i, X g i j * e g i = 0) ∧
    let gram := ∑ g, (X g)ᵀ * X g
    gram * gram⁻¹ = 1 ∧ gram⁻¹ * gram = 1

/-- The observable configuration and return value of a `clubSandwich::vcovCR`
call. -/
structure ClubSandwichCall (p : ℕ) where
  version : _root_.String
  vcovType : _root_.String
  targetOmitted : Bool
  inverseVarOmitted : Bool
  formOmitted : Bool
  identityTarget : Bool
  clustersAreGroups : Bool
  result : Matrix (Fin p) (Fin p) ℝ

/-- The pinned version-0.7.0 default CR2 call used in the paper. -/
def pinnedClubSandwichCall {p : ℕ} (Sigma : Matrix (Fin p) (Fin p) ℝ) :
    ClubSandwichCall p where
  version := "0.7.0"
  vcovType := "CR2"
  targetOmitted := true
  inverseVarOmitted := true
  formOmitted := true
  identityTarget := true
  clustersAreGroups := true
  result := Sigma

/-- The observable configuration and return value of a `sandwich::bread` call. -/
structure SandwichBreadCall (p : ℕ) where
  version : _root_.String
  fittedObservations : ℕ
  unweighted : Bool
  result : Matrix (Fin p) (Fin p) ℝ

/-- The pinned version-3.1-3 unweighted bread call used in the paper. -/
def pinnedSandwichBreadCall {p : ℕ} (Nobs : ℕ)
    (bread : Matrix (Fin p) (Fin p) ℝ) : SandwichBreadCall p where
  version := "3.1-3"
  fittedObservations := Nobs
  unweighted := true
  result := bread

/-- The CR2 cluster meat corresponding to arbitrarily sized block matrices and
residual vectors. -/
noncomputable def cr2Meat {G p : ℕ} (m : Fin G → ℕ)
    (X : ∀ g, Matrix (Fin (m g)) (Fin p) ℝ)
    (e : ∀ g, Fin (m g) → ℝ)
    (A : ∀ g, Matrix (Fin (m g)) (Fin (m g)) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ g, (X g)ᵀ * A g * Matrix.vecMulVec (e g) (e g) * (A g)ᵀ * X g

/-- James E. Pustejovsky (2026), `clubSandwich` version 0.7.0 source package,
CRAN, R/lm.R lines 47--52 and 70--72; R/S3-methods.R lines 21--33 and 63--65;
R/clubSandwich.R lines 167--175, 216--225, 237--287; and
R/CR-adjustments.R lines 5--7 and 22--42.  The source tarball SHA-256 is
`f3cd9cd5840022b8d1354dce3e7e4a820edcd47411b9f95bdd200c4e040032ed`.
For an unweighted full-rank fit with an arbitrary fitted-observation count and
arbitrarily sized cluster-row blocks, identity working target, and positive-definite
cluster leverage complements, the returned CR2 matrix is the stated sandwich. -/
-- @node: lem:clubsandwich-cr2-software-contract
def ClubSandwichCR2Contract {G p : ℕ} (m : Fin G → ℕ) (Nobs : ℕ)
    (call : ClubSandwichCall p)
    (X : ∀ g, Matrix (Fin (m g)) (Fin p) ℝ)
    (y : ∀ g, Fin (m g) → ℝ)
    (e : ∀ g, Fin (m g) → ℝ)
    (H A : ∀ g, Matrix (Fin (m g)) (Fin (m g)) ℝ)
    (bread breadTilde : Matrix (Fin p) (Fin p) ℝ) : Sort 0 :=
  call.version = "0.7.0" ∧ call.vcovType = "CR2" ∧
  call.targetOmitted = true ∧ call.inverseVarOmitted = true ∧
  call.formOmitted = true ∧ call.identityTarget = true ∧
  call.clustersAreGroups = true ∧
  Nobs = ∑ g, m g ∧
  (UnweightedFullRankLmFit m X y e →
    (∀ g, H g = X g * ((∑ g, (X g)ᵀ * X g)⁻¹) * (X g)ᵀ) →
    (∀ g, Matrix.PosDef (1 - H g)) →
    (∀ g, Matrix.PosDef (A g) ∧ A g = (A g)ᵀ ∧
      A g * A g * (1 - H g) = 1) →
    breadTilde = ((Nobs : ℝ)⁻¹) • bread →
    call.result = breadTilde * cr2Meat m X e A * breadTilde)

/-- Achim Zeileis and Thomas Lumley (2026), `sandwich` version 3.1-3 source
package, CRAN, R/bread.R lines 10--15.  The source tarball SHA-256 is
`960006cf4fcbada936b43acd04ddd8c0d1255570f41dda046ce778873f546134`.
For a full-column-rank unweighted `lm` fit with arbitrarily sized cluster-row
blocks, `bread` is the fitted-observation count times the inverse Gram matrix. -/
-- @node: lem:sandwich-lm-bread-contract
def SandwichLmBreadContract {G p : ℕ} (m : Fin G → ℕ) (Nobs : ℕ)
    (call : SandwichBreadCall p)
    (X : Matrix (Fin Nobs) (Fin p) ℝ)
    (Xblock : ∀ g, Matrix (Fin (m g)) (Fin p) ℝ)
    (y e : ∀ g, Fin (m g) → ℝ) : Sort 0 :=
  call.version = "3.1-3" ∧ call.fittedObservations = Nobs ∧
  call.unweighted = true ∧
  Nobs = ∑ g, m g ∧
  (UnweightedFullRankLmFit m Xblock y e →
    Xᵀ * X = ∑ g, (Xblock g)ᵀ * Xblock g →
    call.result = (Nobs : ℝ) • ((Xᵀ * X)⁻¹))

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
