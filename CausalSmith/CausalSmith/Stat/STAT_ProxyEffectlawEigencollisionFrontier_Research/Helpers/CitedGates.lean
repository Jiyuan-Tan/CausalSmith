import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Basic
import Causalean.Mathlib.MeasureTheory.CompactArgminSelection

/-! Explicit cited logical gates used by the paper. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

/-- A nominal handle for the parameter class and recovery regime defined in the published VMW
paper.  Its fields deliberately carry no local characterization: the cited gates below are the
only bridge from these publication-level names to the conditions displayed in this development. -/
structure PublishedVMWScopeHandle where
  model : ∀ (k dx dz : ℕ), Measure (FullData k dx dz) → Prop
  assumption4 : ∀ (k dx dz : ℕ), Measure (FullData k dx dz) → Prop
  recoveryRegime : ∀ (k dx dz : ℕ), Measure (FullData k dx dz) → Prop
  /-- The published Theorem 7.2 estimator, whose three components are the treatment effects,
  anchor-normalized feature matrix, and simplex-projected mixture weights. -/
  theorem72Estimator : ∀ (k dx dz n : ℕ), (Fin n → Obs dx dz) →
    (Fin k → ℝ) × RectMatrix dx k × (Fin k → ℝ)

/-- The nominal published VMW parameter-class membership predicate. -/
def PublishedVMWModel (publishedScope : PublishedVMWScopeHandle) {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) : Prop :=
  publishedScope.model k dx dz P

/-- A nominal record of quantitative margins imposed by a published model specification. -/
structure PublishedVMWMarginRecord where
  latentArmMargin : Option ℝ
  proxySingularMargin : Option ℝ

/-- The qualitative conditions listed in VMW Assumptions 1--2 and §4.2.  In particular, this
predicate has no numerical latent-positivity or singular-value margin parameter. -/
def PublishedVMWQualitativeConditions {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] : Prop :=
  ReferenceProxySeparation P ∧
  TargetProxySeparation P ∧
  CausalConsistency P ∧
  ArmwiseLatentIgnorability P ∧
  Function.Injective (Matrix.toEuclideanLin (referenceFeature P false)) ∧
  Function.Injective (Matrix.toEuclideanLin (referenceFeature P true)) ∧
  Function.Injective (Matrix.toEuclideanLin (targetFeature P)) ∧
  ∀ u t, 0 < P.real (latentCell u t)

/-- The published qualitative scope fixes neither this paper's latent-arm margin nor its proxy
singular-value margin. -/
def PublishedVMWNoFixedMargins (publishedMargins : PublishedVMWMarginRecord) : Prop :=
  publishedMargins.latentArmMargin = none ∧
  publishedMargins.proxySingularMargin = none

/-- The local nearest-point wrapper, with the local top measurable-space instance adapted to the
canonical Euclidean Borel instance used by the discharged Causalean theorem. -/
lemma borelMeasurable_nearestPoint_selector :
    ∀ (d : ℕ) (K : Set (Euc d)), K.Nonempty → IsCompact K →
      ∃ Pi : Euc d → Euc d, Measurable Pi ∧
        ∀ s, Pi s ∈ K ∧ dist s (Pi s) = Metric.infDist s K := by
  intro d K hKne hK
  exact
    _root_.Causalean.Mathlib.MeasureTheory.borelMeasurable_nearestPoint_selector K hK hKne

/-- Brown and Purves (1973), Corollary 1, specialized to a compact Euclidean action space and an
arbitrary jointly continuous loss: the argmin correspondence admits a Borel measurable selector.
DOI 10.1214/aos/1176342510. -/
-- @node: lem:borel-nearest-point-selector
lemma borelMeasurable_compactLoss_selector :
    ∀ (d : ℕ) (K : Set (Euc d)) (dS : Euc d → Euc d → ℝ),
      K.Nonempty → IsCompact K → Continuous (Function.uncurry dS) →
      ∃ Pi : Euc d → Euc d, Measurable Pi ∧
        ∀ s, Pi s ∈ K ∧ ∀ q ∈ K, dS s (Pi s) ≤ dS s q := by
  intro d K dS hKne hK hdS
  exact
    _root_.Causalean.Mathlib.MeasureTheory.borelMeasurable_compact_argmin_selector
      K hK hKne (Function.uncurry dS) hdS.measurable
      (fun s => (hdS.comp (continuous_const.prodMk continuous_id)).continuousOn)

/-- Virk, Mazaheri, and Wu (2026), arXiv:2607.10926v1, Assumptions 1--2 and §4.2.
The cited correspondence says that the displayed qualitative proxy independences, consistency,
armwise ignorability, full column ranks, and strict latent positivity are the published model scope;
the source does not impose this paper's fixed quantitative margins. -/
-- @node: lem:vmw-model-scope
def VMWModelScope (publishedScope : PublishedVMWScopeHandle)
    (publishedMargins : PublishedVMWMarginRecord) : Sort 0 :=
  PublishedVMWNoFixedMargins publishedMargins ∧
  ∀ (k dx dz : ℕ) (P : Measure (FullData k dx dz)) (_hP : IsProbabilityMeasure P),
    letI := _hP
    PublishedVMWModel publishedScope P ↔ PublishedVMWQualitativeConditions P

/-- The paper's quantitative model membership implies all of the qualitative conditions; the
cited gate is used separately to identify those conditions with the published scope. -/
lemma ucvmwModel_publishedQualitativeConditions
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hdom : CoreParameterDomain k dx dz L pi0 sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    PublishedVMWQualitativeConditions P := by
  rcases hdom with ⟨hk, hkx, hkz, hL, hpi, hpiMax, hsigma, hsigmaMax⟩
  have injective_of_margin {rows : ℕ} (A : RectMatrix rows k)
      (hA : sigma0 ≤ signalMinSingular A) :
      Function.Injective (Matrix.toEuclideanLin A) := by
    rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hik : i ≤ k - 1 := by
      simpa using (Nat.le_sub_one_of_lt (by simpa using hi))
    exact lt_of_lt_of_le (lt_of_lt_of_le hsigma hA)
      ((Matrix.toEuclideanLin A).singularValues_antitone hik)
  exact ⟨hM.referenceProxySeparation, hM.targetProxySeparation, hM.consistency,
    hM.latentIgnorability, injective_of_margin _ hM.proxyRankMargin.1,
    injective_of_margin _ hM.proxyRankMargin.2.1,
    injective_of_margin _ hM.proxyRankMargin.2.2,
    fun u t => lt_of_lt_of_le hpi (hM.latentArmPositivity u t)⟩

/-- The qualitative simple-effect separation condition used by the published recovery regime. -/
def PublishedSpectralSeparation {k : ℕ} (tau : Fin k → ℝ) : Prop :=
  ∀ u v, u ≠ v → tau u ≠ tau v

/-- The full-column-rank requirement called Assumption 2 in the cited VMW paper. -/
def PublishedVMWAssumption2 {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] : Prop :=
  Function.Injective (Matrix.toEuclideanLin (referenceFeature P false)) ∧
  Function.Injective (Matrix.toEuclideanLin (referenceFeature P true)) ∧
  Function.Injective (Matrix.toEuclideanLin (targetFeature P))

/-- The strict latent positivity requirement used by the cited VMW recovery theorem. -/
def PublishedVMWStrictLatentPositivity {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] : Prop :=
  ∀ u t, 0 < P.real (latentCell u t)

/-- The nominal proposition called Assumption 4 in the published VMW paper.  Its mathematical
content remains attached to the publication handle rather than being replaced by an arbitrary
proposition chosen by a consumer. -/
def PublishedVMWAssumption4 (publishedScope : PublishedVMWScopeHandle) {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) : Prop :=
  publishedScope.assumption4 k dx dz P

/-- The positive-dimensional domain on which the cited VMW model and recovery statements apply. -/
def VMWPositiveDimensionDomain (k dx dz : ℕ) : Prop :=
  0 < k ∧ k ≤ dx ∧ k ≤ dz

/-- The columns form a population top-`k` right singular basis of the stacked proxy moment. -/
def PublishedVMWTopRightSingularBasis {k dx dz : ℕ}
    (s : SummarySpace dx dz) (basis : SignalBasis dx k) : Prop :=
  ∀ j : Fin k,
    Matrix.mulVec ((stackedProxyMoment s).transpose * stackedProxyMoment s)
        (fun i => basis.V i j) =
      (singularValue (stackedProxyMoment s) j.val) ^ 2 • (fun i => basis.V i j)

/-- The law-level content of VMW Assumption 4: admissible positive dimensions, finite positive
envelopes for the target proxy and the two proxy products, positive marginal treatment-arm
probabilities, and a positive population singular-value margin.  Sample-size and confidence-level
conditions belong to the recovery theorem, not to this predicate. -/
def ConcreteVMWAssumption4 {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P] : Prop :=
  VMWPositiveDimensionDomain k dx dz ∧
  ∃ LX LZX LYZX pi sigma : ℝ,
    0 < LX ∧ 0 < LZX ∧ 0 < LYZX ∧ 0 < pi ∧ 0 < sigma ∧
    BoundedTargetProxy (L := LX) P ∧
    BoundedProxyProduct (L := LZX) P ∧
    BoundedOutcomeProxyProduct (L := LYZX) P ∧
    (∀ t : Bool, pi ≤ P.real {w | w.T = t}) ∧
    ∃ basis : SignalBasis dx k,
      PublishedVMWTopRightSingularBasis (obsSummary P) basis ∧
      sigma ≤ singularValue (stackedProxyMoment (obsSummary P)) (k - 1) ∧
      ∀ t : Bool,
        sigma ≤ singularValue (observedProxyMoment (obsSummary P) t * basis.V) (k - 1)

/-- The nominal published Theorem 7.2 recovery-regime membership predicate. -/
def PublishedVMWRecoveryRegime (publishedScope : PublishedVMWScopeHandle) {k dx dz : ℕ}
    (P : Measure (FullData k dx dz)) : Prop :=
  publishedScope.recoveryRegime k dx dz P

/-- The theorem-level part of published VMW Theorem 7.2, kept separate from both population-law
predicates.  The universal constants are outermost.  For the published estimator, the displayed
sample-size and radius conditions imply one event of probability at least `1 - eta` on which the
treatment effects, anchor-normalized feature columns, and simplex-projected mixture weights obey
their three simultaneous bounds. -/
def PublishedVMWTheorem72FiniteSampleRecovery
    (publishedScope : PublishedVMWScopeHandle) : Prop :=
  ∃ cW cMom cReg cTau cB cAnc cMu c0 : ℝ,
    0 < cW ∧ 0 < cMom ∧ 0 < cReg ∧ 0 < cTau ∧ 0 < cB ∧
    0 < cAnc ∧ 0 < cMu ∧ 0 < c0 ∧
    ∀ (k dx dz : ℕ) (P : Measure (FullData k dx dz))
      (_hP : IsProbabilityMeasure P) (n : ℕ) (eta : ℝ),
      letI := _hP
      VMWPositiveDimensionDomain k dx dz →
      PublishedVMWRecoveryRegime publishedScope P →
      0 < eta → eta < 1 →
      ∀ (LX LZX LYZX pi sigma delta alphaAnc : ℝ) (basis : SignalBasis dx k),
        0 < LX ∧ 0 < LZX ∧ 0 < LYZX ∧ 0 < pi ∧ 0 < sigma ∧
        BoundedTargetProxy (L := LX) P ∧
        BoundedProxyProduct (L := LZX) P ∧
        BoundedOutcomeProxyProduct (L := LYZX) P ∧
        pi = min (P.real {w | w.T = false}) (P.real {w | w.T = true}) ∧
        PublishedVMWTopRightSingularBasis (obsSummary P) basis ∧
        sigma = min (singularValue (stackedProxyMoment (obsSummary P)) (k - 1))
          (min
            (singularValue (observedProxyMoment (obsSummary P) false * basis.V) (k - 1))
            (singularValue (observedProxyMoment (obsSummary P) true * basis.V) (k - 1))) →
        ((k = 1 ∧ delta = 0) ∨
          (2 ≤ k ∧ 0 < delta ∧
            (∀ u v : Fin k, u ≠ v → delta ≤ |latentEffect P u - latentEffect P v|) ∧
            ∃ u v : Fin k, u ≠ v ∧ delta = |latentEffect P u - latentEffect P v|)) →
        0 < alphaAnc ∧
          (∀ u : Fin k, alphaAnc ≤
            (‖(WithLp.toLp 2 (fun i ↦ targetFeature P i u) : Euc dx)‖)⁻¹) ∧
          (∃ u : Fin k, alphaAnc =
            (‖(WithLp.toLp 2 (fun i ↦ targetFeature P i u) : Euc dx)‖)⁻¹) →
        let LQ := max LZX LYZX
        let MX := max
          ‖matrixCLM (observedProxyMoment (obsSummary P) false)‖
          ‖matrixCLM (observedProxyMoment (obsSummary P) true)‖
        let MY := max
          ‖matrixCLM (observedOutcomeProxyMoment (obsSummary P) false)‖
          ‖matrixCLM (observedOutcomeProxyMoment (obsSummary P) true)‖
        let Bt := (targetFeature P).transpose
        let kappaB := ‖matrixCLM Bt‖ * ‖matrixCLM (genuinePenroseInverse Bt)‖
        let GammaX := 1 + cW * MX / sigma
        let GammaY := 1 + cW * MY / sigma
        let kappaZX := GammaY + 6 * GammaX * (MY / sigma + GammaY)
        let lambdaStar := Real.log (16 * (dx + dz : ℝ) / eta)
        let rootTerm := Real.sqrt (lambdaStar / (n * pi))
        let momentRadius := cMom * LQ * rootTerm
        let gapInv := if k = 1 then 0 else delta⁻¹
        let rTau := cTau * kappaB * kappaZX * LQ / sigma * rootTerm
        let rB := cB * LQ * (kappaB ^ 2 * kappaZX * gapInv / sigma + 1 / sigma) *
          rootTerm
        let epsB := cAnc * (alphaAnc ^ 2)⁻¹ * rB
        let epsMu := cMu * LX * Real.sqrt (lambdaStar / n)
        let sigmaB := singularValue (targetFeature P) (k - 1)
        let Mmu := ‖(WithLp.toLp 2 (obsSummary P).mX : Euc dx)‖
        cReg * lambdaStar ≤ n * pi →
        momentRadius ≤ cReg * sigma / GammaX →
        (k = 1 ∨ rTau < delta / 2) →
        rB ≤ c0 * alphaAnc →
        Real.sqrt k * epsB ≤ sigmaB / 2 →
        1 - eta ≤ (sampleLaw (n := n) P).real
          {sample | ∃ rho : Equiv.Perm (Fin k),
            (∀ u : Fin k,
              |(publishedScope.theorem72Estimator k dx dz n sample).1 (rho u) -
                latentEffect P u| ≤ rTau) ∧
            (∀ u : Fin k,
              ‖(WithLp.toLp 2 (fun i ↦
                (publishedScope.theorem72Estimator k dx dz n sample).2.1 i (rho u) -
                  targetFeature P i u) : Euc dx)‖ ≤ epsB) ∧
            (∀ u : Fin k,
              0 ≤ (publishedScope.theorem72Estimator k dx dz n sample).2.2 u) ∧
            (∑ u : Fin k,
              (publishedScope.theorem72Estimator k dx dz n sample).2.2 u) = 1 ∧
            ‖(WithLp.toLp 2 (fun u ↦
              (publishedScope.theorem72Estimator k dx dz n sample).2.2 (rho u) -
                latentMass P u) : Euc k)‖ ≤
              2 / sigmaB * epsMu + 6 * Mmu * Real.sqrt k / sigmaB ^ 2 * epsB}

/-- Virk, Mazaheri, and Wu (2026), arXiv:2607.10926v1, Assumption 3 and Theorem 7.2.
The cited recovery regime remains inside the standing Assumption 1 proxy-separation, consistency,
and armwise-ignorability conditions and the anchor normalization; it additionally requires
Assumption 2, strict latent positivity, Assumption 4, and spectral separation.  Theorem 7.2
separately quantifies the sample size and confidence level, imposes its displayed sample-size and
radius conditions, applies its stated estimator, and gives simultaneous high-probability bounds
for the effects, anchor-normalized feature matrix, and simplex-projected mixture proportions.
None of those theorem-level data is a field of either population-law predicate below. -/
-- @node: lem:vmw-separated-recovery-scope
def VMWSeparatedRecoveryScope (publishedScope : PublishedVMWScopeHandle) : Sort 0 :=
  (∀ (k dx dz : ℕ) (P : Measure (FullData k dx dz))
      (_hP : IsProbabilityMeasure P),
      letI := _hP
      VMWPositiveDimensionDomain k dx dz →
        (PublishedVMWAssumption4 publishedScope P ↔ ConcreteVMWAssumption4 P)) ∧
  (∀ (k dx dz : ℕ) (P : Measure (FullData k dx dz))
      (_hP : IsProbabilityMeasure P),
      letI := _hP
      VMWPositiveDimensionDomain k dx dz →
        (PublishedVMWRecoveryRegime publishedScope P ↔
          ReferenceProxySeparation P ∧
          TargetProxySeparation P ∧
          CausalConsistency P ∧
          ArmwiseLatentIgnorability P ∧
          AnchorNormalization P ∧
          PublishedVMWAssumption2 P ∧
          PublishedVMWStrictLatentPositivity P ∧
          ConcreteVMWAssumption4 P ∧
          PublishedSpectralSeparation (latentEffect P))) ∧
  PublishedVMWTheorem72FiniteSampleRecovery publishedScope

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
