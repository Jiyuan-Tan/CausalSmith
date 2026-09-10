import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.GapFreeModulusBridge
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.AmbientOperatorBridge
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.OutcomeFactorization
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.RealDiagonalizationBridge
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelRealDiagonalization
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelSpectralCertificate
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.GapFreeClosureAssembly
import CausalSmith.Substrate.CollisionSafeSpectralLaw.Composition
import CausalSmith.Substrate.CollisionSafeSpectralLaw.MoorePenrose

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

/-- Gap-free Lipschitz modulus for quotient effect laws and its positive-law continuous
extension. -/
-- @node: thm:gap-free-positive-measure-modulus
theorem gap_free_positive_measure_modulus
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ) (hk : 2 ≤ k) (hkx : k ≤ dx)
    (hkz : k ≤ dz) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hpiMax : pi0 ≤ 1 / (2 * k : ℝ)) (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ Cmod : ℝ, 0 < Cmod ∧ -- @realizes \(C_{\mathrm{mod}}\)(positive modulus constant)
      (∀ (P Q : ModelLaw k dx dz L pi0 sigma0),
        AtomicLaw.LawModulo.wass1 (by letI := P.prob; exact quotientLaw P.P P.model)
            (by letI := Q.prob; exact quotientLaw Q.P Q.model) ≤
          Cmod * dS P.summary Q.summary) ∧
      ∃ Fbar : {q // q ∈ summaryClosure k dx dz L pi0 sigma0} →
          AtomicLaw.LawModulo k (effectRadius dz L sigma0),
        Continuous Fbar ∧ Measurable Fbar ∧
        (∀ q q', AtomicLaw.LawModulo.wass1 (Fbar q) (Fbar q') ≤
          Cmod * dS q.1 q'.1) ∧
        (∀ Q : ModelLaw k dx dz L pi0 sigma0,
          Fbar ⟨Q.summary, subset_closure ⟨Q, rfl⟩⟩ = by
            letI := Q.prob
            exact quotientLaw Q.P Q.model) ∧
        ∀ Gbar : {q // q ∈ summaryClosure k dx dz L pi0 sigma0} →
            AtomicLaw.LawModulo k (effectRadius dz L sigma0),
          Continuous Gbar →
          (∀ q q', AtomicLaw.LawModulo.wass1 (Gbar q) (Gbar q') ≤
            Cmod * dS q.1 q'.1) →
          (∀ Q : ModelLaw k dx dz L pi0 sigma0,
            Gbar ⟨Q.summary, subset_closure ⟨Q, rfl⟩⟩ = by
              letI := Q.prob
              exact quotientLaw Q.P Q.model) →
          ∀ q, Gbar q = Fbar q := by
  let kappa := conditionBound dx k L sigma0
  let Cbase := kappa * effectRadius dz L sigma0 +
    L * ((dx : ℝ) ^ 2 * kappa ^ 2) *
      (3 * (pi0 * sigma0 ^ 2)⁻¹ ^ 2 * L + (pi0 * sigma0 ^ 2)⁻¹)
  let Cmod := Cbase + 1
  have hkappa : 0 ≤ kappa := conditionBound_nonneg dx k (by linarith) hsigma
  have hCbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    have hradius : 0 ≤ effectRadius dz L sigma0 := by unfold effectRadius; positivity
    positivity
  have hCmod : 0 < Cmod := by dsimp [Cmod]; linarith
  have hmodel : ∀ (P Q : ModelLaw k dx dz L pi0 sigma0),
      AtomicLaw.LawModulo.wass1 (by letI := P.prob; exact quotientLaw P.P P.model)
          (by letI := Q.prob; exact quotientLaw Q.P Q.model) ≤
        Cmod * dS P.summary Q.summary := by
    intro P Q
    letI hPprob := P.prob
    letI hQprob := Q.prob
    obtain ⟨DP, hkP, hRP, hrepP⟩ := model_realDiagonalization_certificate
      P.P hk hkx hkz hL hpi hpiMax hsigma hsigmaMax P.model
    obtain ⟨DQ, hkQ, hRQ, hrepQ⟩ := model_realDiagonalization_certificate
      Q.P hk hkx hkz hL hpi hpiMax hsigma hsigmaMax Q.model
    have hraw := AmbientOperatorBridge.modelLaw_wass1_le_dS_of_certificates
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax P Q DP DQ
      hrepP hrepQ hkappa hkP hkQ hRP hRQ
    calc
      _ ≤ Cbase * dS P.summary Q.summary := by simpa [Cbase, kappa] using hraw
      _ ≤ Cmod * dS P.summary Q.summary := by
        have hdS : 0 ≤ dS P.summary Q.summary := by unfold dS; positivity
        gcongr
        dsimp [Cmod]
        linarith
  let s := admissibleImage k dx dz L pi0 sigma0
  let f : s → AtomicLaw.LawModulo k (effectRadius dz L sigma0) :=
    publishedQuotientFunctional k dx dz L pi0 sigma0
  have hf_model (Q : ModelLaw k dx dz L pi0 sigma0) :
      f ⟨Q.summary, by exact ⟨Q, rfl⟩⟩ = by
        letI := Q.prob
        exact quotientLaw Q.P Q.model := by
    let R : ModelLaw k dx dz L pi0 sigma0 :=
      Classical.choose (show Q.summary ∈ s by exact ⟨Q, rfl⟩)
    have hRsummary : R.summary = Q.summary :=
      Classical.choose_spec (show Q.summary ∈ s by exact ⟨Q, rfl⟩)
    have hw := hmodel R Q
    have hzero : AtomicLaw.LawModulo.wass1
        (by letI := R.prob; exact quotientLaw R.P R.model)
        (by letI := Q.prob; exact quotientLaw Q.P Q.model) = 0 := by
      apply le_antisymm
      · simpa [hRsummary] using hw
      · exact AtomicLaw.LawModulo.wass1_nonneg _ _
    apply AtomicLaw.LawModulo.eq_of_wass1_eq_zero
    simpa [f, publishedQuotientFunctional, R] using hzero
  have hf_control : ∀ x y : s, dist (f x) (f y) ≤ Cmod * dS x.1 y.1 := by
    intro x y
    let P : ModelLaw k dx dz L pi0 sigma0 := Classical.choose x.property
    let Q : ModelLaw k dx dz L pi0 sigma0 := Classical.choose y.property
    have hP : P.summary = x.1 := Classical.choose_spec x.property
    have hQ : Q.summary = y.1 := Classical.choose_spec y.property
    simpa [AtomicLaw.LawModulo.dist_eq_wass1, f, publishedQuotientFunctional, P, Q,
      hP, hQ] using hmodel P Q
  let A : ℝ := 4 * entryNormConstant dz dx + dx
  have hA : 0 ≤ A := by
    dsimp [A]
    have hdx0 : (0 : ℝ) ≤ dx := Nat.cast_nonneg dx
    nlinarith [entryNormConstant_nonneg dz dx]
  let Kmetric : NNReal := ⟨Cmod * A, mul_nonneg hCmod.le hA⟩
  have hf_metric : LipschitzWith Kmetric f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (f x) (f y) ≤ Cmod * dS x.1 y.1 := hf_control x y
      _ ≤ Cmod * (A * dist x y) := by
        gcongr
        exact dS_le_dist_mul x.1 y.1
      _ = (Kmetric : ℝ) * dist x y := by
        change Cmod * (A * dist x y) = (Cmod * A) * dist x y
        ring
  obtain ⟨Fbar, hFcont, hFbound, hFext, hFunique⟩ :=
    GapFreeClosureAssembly.exists_unique_extension_with_control s f dS hf_metric
      (dS_continuous dx dz) hf_control
  refine ⟨Cmod, hCmod, hmodel, Fbar, hFcont, hFcont.measurable, ?_, ?_, ?_⟩
  · intro q q'
    simpa [AtomicLaw.LawModulo.dist_eq_wass1] using hFbound q q'
  · intro Q
    exact (hFext ⟨Q.summary, ⟨Q, rfl⟩⟩).trans (hf_model Q)
  · intro Gbar hGcont _hGlip hGmodel q
    apply hFunique Gbar hGcont
    intro x
    let Q : ModelLaw k dx dz L pi0 sigma0 := Classical.choose x.property
    have hQ : Q.summary = x.1 := Classical.choose_spec x.property
    have hGQ := hGmodel Q
    calc
      Gbar ⟨x.1, subset_closure x.property⟩ =
          Gbar ⟨Q.summary, subset_closure ⟨Q, rfl⟩⟩ := by
        congr 1
        apply Subtype.ext
        exact hQ.symm
      _ = (by letI := Q.prob; exact quotientLaw Q.P Q.model) := hGQ
      _ = f ⟨Q.summary, ⟨Q, rfl⟩⟩ := (hf_model Q).symm
      _ = f x := by
        congr 1
        apply Subtype.ext
        exact hQ

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
