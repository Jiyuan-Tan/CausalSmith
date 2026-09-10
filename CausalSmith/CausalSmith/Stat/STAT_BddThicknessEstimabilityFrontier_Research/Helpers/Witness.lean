import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Geometry
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.TubeCoords
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Testing
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.Estimator
import Mathlib.Probability.Distributions.Gaussian.Real
import Causalean.Mathlib.InformationTheory.GaussianKL
import Causalean.Mathlib.InformationTheory.ProductKLLeCam

/-! # Circular thinning witnesses and tent perturbations -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- Signed distance to the unit circle. -/
noncomputable def signedRadius (z : Score) : ℝ := ‖z‖ - 1
  -- @realizes \rho(‖z‖₂-1)

/-- The symmetric tube about the unit circle. -/
def circularTube (h0 : ℝ) : Set Score := {z | |signedRadius z| ≤ h0}
  -- @realizes \mathcal T({|rho(z)|≤h₀})

/-- Unit-circle boundary used by the witness. -/
def unitCircle : Set Score := Metric.sphere 0 1

/-- Normalizing mass for the pervasive tube density. -/
noncomputable def pervasiveNormalizer (κ h0 : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in circularTube h0, ENNReal.ofReal (|signedRadius z| ^ (κ - 2))

/-- The normalized pervasive score density. -/
noncomputable def pervasiveTubeDensity (κ h0 : ℝ) (z : Score) : ℝ≥0∞ :=
  (circularTube h0).indicator (fun z => ENNReal.ofReal (|signedRadius z| ^ (κ - 2))) z /
    pervasiveNormalizer κ h0
  -- @realizes f_{\kappa}^{\mathrm{perv}}(normalized |rho|^(kappa-2) tube density)

/-- Normalizing mass for the isolated-site tube density. -/
noncomputable def isolatedNormalizer (κ h0 : ℝ) (xstar : Score) : ℝ≥0∞ :=
  ∫⁻ z in circularTube h0,
    ENNReal.ofReal (min 1 ((dist z xstar / h0) ^ (κ - 2)))

/-- The normalized isolated-site score density. -/
noncomputable def isolatedTubeDensity (κ h0 : ℝ) (xstar z : Score) : ℝ≥0∞ :=
  (circularTube h0).indicator
    (fun z => ENNReal.ofReal (min 1 ((dist z xstar / h0) ^ (κ - 2)))) z /
      isolatedNormalizer κ h0 xstar
  -- @realizes f_{\kappa}^{\mathrm{iso}}(normalized single-site tube density)

-- @env: S4
variable (κ h0 σ : ℝ) (xstar : Score)
  -- @realizes x_{\star}(fixed point on S¹)

/-- A score law coupled to two independent centered Gaussian potential outcomes. -/
noncomputable def independentGaussianLatentLaw (score : Measure Score) (σ : ℝ) :
    Measure LatentUnit :=
  Measure.map (fun p : Score × (ℝ × ℝ) => (p.2.1, p.2.2, p.1))
    (score.prod ((gaussianReal 0 (Real.toNNReal (σ ^ 2))).prod
      (gaussianReal 0 (Real.toNNReal (σ ^ 2)))))

-- @node: def:circular-thinning-witnesses
/-- Exact specification of the two circular zero-trace Gaussian baseline laws.
The score-law and observed-law equalities pin all auxiliary densities to the
corresponding full law. -/
def circularThinningWitness (Pperv Piso : BoundaryLaw) (κ h0 σ : ℝ)
    (xstar : Score) : Prop := by
  classical
  exact 2 < κ ∧ 0 < h0 ∧ h0 < 1 ∧ 0 < σ ∧ xstar ∈ unitCircle ∧
  (∀ P ∈ ({Pperv, Piso} : Set BoundaryLaw),
    P.region 1 = {z | signedRadius z ≤ 0} ∧
    P.region 0 = {z | 0 < signedRadius z} ∧
    P.latentLaw = independentGaussianLatentLaw P.scoreLaw σ ∧
    SharpAssignment P ∧ Consistency P ∧
    (∀ t z, z ∈ sideSupport P t → P.sideRegression t z = 0) ∧
    (∀ t z, z ∈ assignmentBoundary P → P.sideTrace t z = 0)) ∧
  Pperv.scoreLaw = volume.withDensity (pervasiveTubeDensity κ h0) ∧
  Piso.scoreLaw = volume.withDensity (isolatedTubeDensity κ h0 xstar) ∧
  Pperv.observedLaw = Measure.map (fun z : Score × ℝ => (z.2, z.1))
    (Pperv.scoreLaw.prod (gaussianReal 0 (Real.toNNReal (σ ^ 2)))) ∧
  Piso.observedLaw = Measure.map (fun z : Score × ℝ => (z.2, z.1))
    (Piso.scoreLaw.prod (gaussianReal 0 (Real.toNNReal (σ ^ 2))))
  -- @realizes P_{\kappa}^{\mathrm{perv},0}(zero-trace pervasive Gaussian baseline)
  -- @realizes P_{\kappa}^{\mathrm{iso},0}(zero-trace isolated Gaussian baseline)

/-- A scale-`h` cone tent centered at `x`. -/
noncomputable def coneTent (x : Score) (h : ℝ) (z : Score) : ℝ :=
  max 0 (1 - dist z x / h)
  -- @realizes \psi_{j,h}((1-d(z,x_j)/h)_+; index zero handled below)

/-- A pervasive site set is maximal and `3h`-separated on the circle. -/
def PervasiveSites (sites : Finset Score) (h : ℝ) : Prop :=
  (↑sites : Set Score) ⊆ unitCircle ∧
    Metric.IsSeparated (Real.toNNReal (3 * h)) (↑sites : Set Score) ∧
    ∀ x ∈ unitCircle, ∃ y ∈ sites, dist x y < 3 * h
  -- @realizes \Xi_h^{\mathrm{perv}}(maximal 3h-separated circle set)

/-- The exact latent law with independent equal-variance Gaussian shifts. -/
noncomputable def gaussianShiftLatentLaw (score : Measure Score) (shift : Score → ℝ)
    (σ : ℝ) : Measure LatentUnit :=
  Measure.map (fun p : Score × (ℝ × ℝ) =>
      (-shift p.1 + p.2.1, shift p.1 + p.2.2, p.1))
    (score.prod ((gaussianReal 0 (Real.toNNReal (σ ^ 2))).prod
      (gaussianReal 0 (Real.toNNReal (σ ^ 2)))))

/-- One member of a tent experiment, with its latent and observed laws pinned. -/
def GaussianTentMember (base Q : BoundaryLaw) (center : Score) (active : Bool)
    (h L σ : ℝ) : Prop := by
  classical
  exact let shift := fun z => if active then (L * h / 4) * coneTent center h z else 0
  Q.region = base.region ∧ Q.scoreLaw = base.scoreLaw ∧
    Q.latentLaw = gaussianShiftLatentLaw base.scoreLaw shift σ ∧
    SharpAssignment Q ∧ Consistency Q ∧
    (∀ z, z ∈ sideSupport Q 1 → Q.sideRegression 1 z = shift z) ∧
    (∀ z, z ∈ sideSupport Q 0 → Q.sideRegression 0 z = -shift z) ∧
    (∀ x, x ∈ assignmentBoundary Q → Q.sideTrace 1 x = shift x) ∧
    (∀ x, x ∈ assignmentBoundary Q → Q.sideTrace 0 x = -shift x)

/-- The isolated two-law Le Cam family, without a pervasive-site premise. -/
def isolatedTentPerturbedLaw (base : BoundaryLaw) (family : Fin 2 → BoundaryLaw)
    (xstar : Score) (h h0 L σ : ℝ) : Prop :=
  xstar ∈ unitCircle ∧ 0 < h ∧ h ≤ h0 / 6 ∧ 0 < L ∧ 0 < σ ∧
    GaussianTentMember base (family 0) xstar false h L σ ∧
    GaussianTentMember base (family 1) xstar true h L σ
  -- @realizes \mathbb P_{\kappa,j,h}^{\mathrm{iso}}(two-law isolated Gaussian tent family)

-- @node: def:fano-tent-family
/-- The pervasive Fano and isolated two-law tent experiments, realized together. -/
def tentPerturbedLaw {M : ℕ} (pervasiveBase isolatedBase : BoundaryLaw)
    (κ : ℝ) (pervasiveFamily : Fin (M + 1) → BoundaryLaw)
    (isolatedFamily : Fin 2 → BoundaryLaw) (centers : Fin M → Score)
    (xstar : Score) (h h0 L σ : ℝ) : Prop :=
  0 < h ∧ h ≤ h0 / 6 ∧ 0 < L ∧ 0 < σ ∧ Function.Injective centers ∧
    circularThinningWitness pervasiveBase isolatedBase κ h0 σ xstar ∧
    PervasiveSites (Finset.univ.image centers) h ∧
    GaussianTentMember pervasiveBase (pervasiveFamily 0) (0 : Score) false h L σ ∧
    (∀ j : Fin M,
      GaussianTentMember pervasiveBase (pervasiveFamily j.succ) (centers j) true h L σ) ∧
    isolatedTentPerturbedLaw isolatedBase isolatedFamily xstar h h0 L σ
  -- @realizes \mathbb P_{\kappa,j,h}^{\mathrm{perv}}(pervasive Gaussian tent laws)
  -- @realizes \mathbb P_{\kappa,j,h}^{\mathrm{iso}}(two-law isolated Gaussian tent family)

-- @node: lem:circular-witness-membership
/-- The two circular baseline laws realize the pervasive and isolated classes
with constants uniform over the declared exponent range. -/
lemma circularWitness_membership (κbar L σ h0 : ℝ) (xstar : Score)
    (hκbar : 2 < κbar) (hL : 0 < L) (hσ : 0 < σ)
    (hxstar : xstar ∈ unitCircle) (hh0 : 0 < h0 ∧ h0 < 1) :
    ∃ cm Cm : ℝ, 0 < cm ∧ cm < Cm ∧ ∀ κ, 2 < κ → κ ≤ κbar →
      ∃ Pperv Piso : BoundaryLaw,
        circularThinningWitness Pperv Piso κ h0 σ xstar ∧
        PervasiveThinningClass Pperv L σ cm Cm κ h0 ∧
        IsolatedThinningClass Piso L σ cm Cm κ h0 ∧
        (∀ t z, z ∈ sideSupport Pperv t → Pperv.sideRegression t z = 0) ∧
        (∀ t z, z ∈ assignmentBoundary Pperv → Pperv.sideTrace t z = 0) ∧
        (∀ t z, z ∈ sideSupport Piso t → Piso.sideRegression t z = 0) ∧
        (∀ t z, z ∈ assignmentBoundary Piso → Piso.sideTrace t z = 0) := by
  sorry -- BLOCKER: needs-substrate(circular-tube weighted side-mass and unit-circle packing bounds)

-- @node: lem:fano-tent-validity
/-- Small tents preserve class membership, have circle-packing size `h⁻¹`,
and incur product KL of order `n L² h^(κ+2)/σ²`; active traces differ by
`Lh/2`. -/
lemma tentFamily_validity (κ L σ cm Cm h0 : ℝ)
    (Pperv Piso : BoundaryLaw)
    (hwitness : circularThinningWitness Pperv Piso κ h0 σ xstar)
    (hpervBase : PervasiveThinningClass Pperv L σ cm Cm κ h0)
    (hisoBase : IsolatedThinningClass Piso L σ cm Cm κ h0) :
    ∃ hstar cpack Cpack CKL : ℝ,
      0 < hstar ∧ hstar ≤ h0 / 6 ∧ 0 < cpack ∧ cpack ≤ Cpack ∧ 0 < CKL ∧
      ∀ h : ℝ, 0 < h → h ≤ hstar →
      ∃ (M : ℕ) (centers : Fin M → Score)
        (Qperv : Fin (M + 1) → BoundaryLaw) (Qiso : Fin 2 → BoundaryLaw),
        tentPerturbedLaw Pperv Piso κ Qperv Qiso centers xstar h h0 L σ ∧
        (∀ j, PervasiveThinningClass (Qperv j) L σ cm Cm κ h0) ∧
        (∀ j, IsolatedThinningClass (Qiso j) L σ cm Cm κ h0) ∧
        cpack / h ≤ (M : ℝ) ∧ (M : ℝ) ≤ Cpack / h ∧
        (∀ j : Fin M, (Qperv j.succ).sideTrace 1 (centers j) = L * h / 4 ∧
          (Qperv j.succ).sideTrace 0 (centers j) = -(L * h / 4) ∧
          traceContrast (Qperv j.succ) (centers j) = L * h / 2) ∧
        (Qiso 1).sideTrace 1 xstar = L * h / 4 ∧
        (Qiso 1).sideTrace 0 xstar = -(L * h / 4) ∧
        traceContrast (Qiso 1) xstar = L * h / 2 ∧
        ∀ n : ℕ,
        (∀ j k : Fin (M + 1),
          InformationTheory.klDiv (observedSampleLaw (Qperv j) n)
            (observedSampleLaw (Qperv k) n) ≤
              ENNReal.ofReal (CKL * n * L ^ 2 * h ^ (κ + 2) / σ ^ 2)) ∧
        InformationTheory.klDiv (observedSampleLaw (Qiso 1) n)
            (observedSampleLaw (Qiso 0) n) ≤
              ENNReal.ofReal (CKL * n * L ^ 2 * h ^ (κ + 2) / σ ^ 2) := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
