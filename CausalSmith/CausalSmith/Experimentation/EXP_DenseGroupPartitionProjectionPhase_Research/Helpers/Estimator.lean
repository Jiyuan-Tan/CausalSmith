import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.PartitionDesign
import Causalean.Experimentation.DesignBased.Estimators.DifferenceInMeans

/-!
# PAME, exact variance, and scalar CR2 statistics

This file defines the estimand and estimator on the two-stage assignment space,
the exact design variance, the independent-group leading term, the degree-one
correction, and the equal-group scalar CR2 statistic.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

/-- Treated-group fraction. -/
noncomputable def pFrac (G G1 : ℕ) (_hG1pos : 0 < G1) (_hG1lt : G1 < G) : ℝ :=
  (G1 : ℝ) / (G : ℝ)
  -- @realizes p_n(G1 divided by G)

/-- The observed group mean under its assigned arm. -/
noncomputable def obsGroupMean {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (w : PartitionTuple n M G × TreatmentSpace G G1) (g : Fin G) : ℝ :=
  if g ∈ w.2.1 then armTable n M Y true (w.1.1 g)
  else armTable n M Y false (w.1.1 g)
  -- @realizes H^{\mathrm{obs}}_{ng}(assigned-arm group mean)

/-- Finite-population PAME. -/
noncomputable def pame (n M : ℕ) (hM : M ≤ n) (Y : PotentialOutcome n M) : ℝ :=
  (slice n M hM).E (armTable n M Y true) -
    (slice n M hM).E (armTable n M Y false)
  -- @realizes \tau_n(slice mean arm contrast)

/-- Difference in realized treated and control group means. -/
noncomputable def pameHat {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (_hG1pos : 0 < G1) (_hG1lt : G1 < G)
    (w : PartitionTuple n M G × TreatmentSpace G G1) : ℝ :=
  (∑ g ∈ w.2.1, armTable n M Y true (w.1.1 g)) / (G1 : ℝ) -
    (∑ g ∈ (Finset.univ.filter fun g : Fin G => g ∉ w.2.1),
      armTable n M Y false (w.1.1 g)) / ((G - G1 : ℕ) : ℝ)
  -- @realizes \widehat\tau_n(realized group difference in means)

/-- The estimand and its design-based estimator, exposed jointly as required by
the paper's definition. -/
-- @node: def:pame-estimator
noncomputable def pameAndEstimator {n M G G1 : ℕ} (hM : M ≤ n)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (Y : PotentialOutcome n M) :
    ℝ × ((PartitionTuple n M G × TreatmentSpace G G1) → ℝ) :=
  (pame n M hM Y, pameHat Y hG1pos hG1lt)
  -- @realizes \tau_n(slice estimand) @realizes \widehat\tau_n(design estimator)

/-- Exact design variance of the PAME estimator. -/
noncomputable def sigmaSq {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (hMG : M * G ≤ n) (hG1pos : 0 < G1) (hG1lt : G1 < G) : ℝ :=
  (randomPartitionDesign n M G G1 hMG (Nat.le_of_lt hG1lt)).Var
    (pameHat Y hG1pos hG1lt)
  -- @realizes \sigma_n^2(exact two-stage design variance)

/-- Independent-group leading variance. -/
noncomputable def indepGroupVar (n M G G1 : ℕ) (hM : M ≤ n)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (Y : PotentialOutcome n M) : ℝ :=
  armVar n M hM Y true / pFrac G G1 hG1pos hG1lt +
    armVar n M hM Y false / (1 - pFrac G G1 hG1pos hG1lt)
  -- @realizes R_n(V1 over p plus V0 over one minus p)

/-- Degree-one energy of the arm-table contrast. -/
noncomputable def degreeOneEnergy (n M : ℕ) (hMpos : 0 < M) (hM : M ≤ n)
    (J : JohnsonProjections n M) (Y : PotentialOutcome n M) : ℝ :=
  sliceNorm n M hM
    (J.proj ⟨1, by omega⟩ (fun A => armTable n M Y true A - armTable n M Y false A)) ^ 2
  -- @realizes E_{\tau,1,n}(squared norm of degree-one arm difference)

/-- Both deterministic quantities entering the dense variance correction. -/
structure DenseCorrectionValues where
  degreeOne : ℝ
  leadingVariance : ℝ

/-- The paper's degree-one energy and independent-group leading variance,
constructed together from a genuine Johnson projection family. -/
-- @node: def:dense-correction
noncomputable def denseCorrection (n M G G1 : ℕ) (hMpos : 0 < M) (hM : M ≤ n)
    (hG1pos : 0 < G1) (hG1lt : G1 < G) (J : JohnsonProjections n M)
    (Y : PotentialOutcome n M) : DenseCorrectionValues where
  degreeOne := degreeOneEnergy n M hMpos hM J Y
  leadingVariance := indepGroupVar n M G G1 hM hG1pos hG1lt Y
  -- @realizes E_{\tau,1,n}(degree-one energy) @realizes R_n(interior leading variance)

/-- The realized groups in arm `z`. -/
def realizedArmSet {G G1 : ℕ} (w : PartitionTuple n M G × TreatmentSpace G G1)
    (z : Arm) : Finset (Fin G) :=
  if z then w.2.1 else Finset.univ \ w.2.1

/-- The fixed number of groups in arm `z`. -/
def armCount (G G1 : ℕ) (z : Arm) : ℕ := if z then G1 else G - G1

/-- Realized mean within one treatment arm. -/
noncomputable def armObsMean {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (w : PartitionTuple n M G × TreatmentSpace G G1) (z : Arm) : ℝ :=
  (∑ g ∈ realizedArmSet w z, obsGroupMean Y w g) / (armCount G G1 z : ℝ)

/-- Within-arm sample variance with the paper's `G_z - 1` denominator. -/
noncomputable def armSampleVar {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (w : PartitionTuple n M G × TreatmentSpace G G1) (z : Arm)
    (_hArm : 2 ≤ armCount G G1 z) : ℝ :=
  (∑ g ∈ realizedArmSet w z,
      (obsGroupMean Y w g - armObsMean Y w z) ^ 2) /
    ((armCount G G1 z - 1 : ℕ) : ℝ)
  -- @realizes s_{z,n}^2(within-arm sample variance)

-- @node: def:cr2-statistic
/-- Equal-group scalar CR2 statistic. -/
noncomputable def cr2Var {n M G G1 : ℕ} (Y : PotentialOutcome n M)
    (hG1 : 2 ≤ G1) (hG0 : 2 ≤ G - G1)
    (w : PartitionTuple n M G × TreatmentSpace G G1) : ℝ :=
  armSampleVar Y w true (by simpa [armCount] using hG1) / (G1 : ℝ) +
    armSampleVar Y w false (by simpa [armCount] using hG0) / ((G - G1 : ℕ) : ℝ)
  -- @realizes \widehat V_{\mathrm{CR2},n}(s1 squared over G1 plus s0 squared over G0)

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
