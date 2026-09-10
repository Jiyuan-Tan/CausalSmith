import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TObservedVMWMarginInclusion
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.GapFreeModulusBridge
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.OutcomeFactorization
import CausalSmith.Substrate.CollisionSafeSpectralLaw.MoorePenrose
import CausalSmith.Substrate.CollisionSafeSpectralLaw.Composition

/-!
Paper-local perturbation bounds for the ambient outcome-weighted Moore--Penrose contrast.
The bounds allow both row and column spaces to move and therefore remain valid across
unrelated choices of signal coordinates.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped Matrix.Norms.L2Operator

namespace AmbientOperatorBridge

open CausalSmith.Substrate.CollisionSafeSpectralLaw
open Causalean.Mathlib.Probability

/-- The basis-free ambient effect contrast formed from the two observed arm summaries. -/
-- @node: ambientOperatorBridge_ambientEffectOperator
noncomputable def ambientEffectOperator {dx dz : ℕ} (s : SummarySpace dx dz) :
    RectMatrix dx dx :=
  moorePenroseInverse s.M1 * s.N1 - moorePenroseInverse s.M0 * s.N0

/-- A single outcome-weighted Moore--Penrose product is stable under simultaneous movement of
the proxy moment and outcome-weighted moment, assuming only equal rank and a singular margin. -/
-- @node: ambientOperatorBridge_norm_product_difference
lemma norm_product_difference {dx dz : ℕ} (M M' N N' : RectMatrix dz dx)
    {r : ℕ} {s L : ℝ} (hs : 0 < s)
    (hrM : M.rank = r) (hrM' : M'.rank = r)
    (hmM : s ≤ singularValue M (r - 1))
    (hmM' : s ≤ singularValue M' (r - 1))
    (hN : ‖N‖ ≤ L) :
    ‖moorePenroseInverse M * N - moorePenroseInverse M' * N'‖ ≤
      3 * s⁻¹ ^ 2 * ‖M - M'‖ * L + s⁻¹ * ‖N - N'‖ := by
  have hmp := norm_moorePenrose_sub_le_of_singularMargin M M' hrM hrM' hs hmM hmM'
  have hinv := norm_moorePenroseInverse_le_inv M' hrM' hs hmM'
  have hsplit : moorePenroseInverse M * N - moorePenroseInverse M' * N' =
      (moorePenroseInverse M - moorePenroseInverse M') * N +
        moorePenroseInverse M' * (N - N') := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hsplit]
  calc
    ‖(moorePenroseInverse M - moorePenroseInverse M') * N +
        moorePenroseInverse M' * (N - N')‖ ≤
        ‖(moorePenroseInverse M - moorePenroseInverse M') * N‖ +
          ‖moorePenroseInverse M' * (N - N')‖ := norm_add_le _ _
    _ ≤ ‖moorePenroseInverse M - moorePenroseInverse M'‖ * ‖N‖ +
          ‖moorePenroseInverse M'‖ * ‖N - N'‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ 3 * s⁻¹ ^ 2 * ‖M - M'‖ * L + s⁻¹ * ‖N - N'‖ := by
      have hL0 : 0 ≤ L := (norm_nonneg N).trans hN
      gcongr

/-- The ambient two-arm contrast is Lipschitz in the paper's five-block summary metric.  This is
the model-local product-triangle bridge from the moving-space Moore--Penrose estimate. -/
-- @node: ambientOperatorBridge_norm_ambientEffectOperator_sub_le
lemma norm_ambientEffectOperator_sub_le {dx dz r : ℕ}
    (p q : SummarySpace dx dz) {s L : ℝ} (hs : 0 < s) (hL : 0 ≤ L)
    (hrp0 : p.M0.rank = r) (hrq0 : q.M0.rank = r)
    (hrp1 : p.M1.rank = r) (hrq1 : q.M1.rank = r)
    (hmp0 : s ≤ singularValue p.M0 (r - 1))
    (hmq0 : s ≤ singularValue q.M0 (r - 1))
    (hmp1 : s ≤ singularValue p.M1 (r - 1))
    (hmq1 : s ≤ singularValue q.M1 (r - 1))
    (hNp0 : ‖p.N0‖ ≤ L) (hNp1 : ‖p.N1‖ ≤ L) :
    ‖ambientEffectOperator p - ambientEffectOperator q‖ ≤
      (3 * s⁻¹ ^ 2 * L + s⁻¹) * dS p q := by
  let C : ℝ := 3 * s⁻¹ ^ 2 * L + s⁻¹
  have hsInv : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hcoefM : 3 * s⁻¹ ^ 2 * L ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right hsInv
  have hcoefN : s⁻¹ ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_left (by positivity)
  have h0 := norm_product_difference p.M0 q.M0 p.N0 q.N0 hs
    hrp0 hrq0 hmp0 hmq0 hNp0
  have h1 := norm_product_difference p.M1 q.M1 p.N1 q.N1 hs
    hrp1 hrq1 hmp1 hmq1 hNp1
  have h0' : ‖moorePenroseInverse p.M0 * p.N0 -
      moorePenroseInverse q.M0 * q.N0‖ ≤
      C * (‖p.M0 - q.M0‖ + ‖p.N0 - q.N0‖) := by
    calc
      _ ≤ 3 * s⁻¹ ^ 2 * ‖p.M0 - q.M0‖ * L +
          s⁻¹ * ‖p.N0 - q.N0‖ := h0
      _ = (3 * s⁻¹ ^ 2 * L) * ‖p.M0 - q.M0‖ +
          s⁻¹ * ‖p.N0 - q.N0‖ := by ring
      _ ≤ C * ‖p.M0 - q.M0‖ + C * ‖p.N0 - q.N0‖ := by gcongr
      _ = C * (‖p.M0 - q.M0‖ + ‖p.N0 - q.N0‖) := by ring
  have h1' : ‖moorePenroseInverse p.M1 * p.N1 -
      moorePenroseInverse q.M1 * q.N1‖ ≤
      C * (‖p.M1 - q.M1‖ + ‖p.N1 - q.N1‖) := by
    calc
      _ ≤ 3 * s⁻¹ ^ 2 * ‖p.M1 - q.M1‖ * L +
          s⁻¹ * ‖p.N1 - q.N1‖ := h1
      _ = (3 * s⁻¹ ^ 2 * L) * ‖p.M1 - q.M1‖ +
          s⁻¹ * ‖p.N1 - q.N1‖ := by ring
      _ ≤ C * ‖p.M1 - q.M1‖ + C * ‖p.N1 - q.N1‖ := by gcongr
      _ = C * (‖p.M1 - q.M1‖ + ‖p.N1 - q.N1‖) := by ring
  have hsplit : ambientEffectOperator p - ambientEffectOperator q =
      (moorePenroseInverse p.M1 * p.N1 - moorePenroseInverse q.M1 * q.N1) -
      (moorePenroseInverse p.M0 * p.N0 - moorePenroseInverse q.M0 * q.N0) := by
    simp only [ambientEffectOperator]
    abel
  rw [hsplit]
  calc
    ‖(moorePenroseInverse p.M1 * p.N1 - moorePenroseInverse q.M1 * q.N1) -
        (moorePenroseInverse p.M0 * p.N0 - moorePenroseInverse q.M0 * q.N0)‖ ≤
        ‖moorePenroseInverse p.M1 * p.N1 - moorePenroseInverse q.M1 * q.N1‖ +
        ‖moorePenroseInverse p.M0 * p.N0 - moorePenroseInverse q.M0 * q.N0‖ :=
      norm_sub_le _ _
    _ ≤ C * (‖p.M1 - q.M1‖ + ‖p.N1 - q.N1‖) +
        C * (‖p.M0 - q.M0‖ + ‖p.N0 - q.N0‖) := add_le_add h1' h0'
    _ ≤ C * dS p q := by
      unfold dS
      change C * (‖p.M1 - q.M1‖ + ‖p.N1 - q.N1‖) +
          C * (‖p.M0 - q.M0‖ + ‖p.N0 - q.N0‖) ≤
        C * (‖p.M0 - q.M0‖ + ‖p.M1 - q.M1‖ +
          ‖p.N0 - q.N0‖ + ‖p.N1 - q.N1‖ +
          Real.sqrt (∑ i, (p.mX i - q.mX i) ^ 2))
      have hsqrt : 0 ≤ Real.sqrt (∑ i, (p.mX i - q.mX i) ^ 2) := Real.sqrt_nonneg _
      nlinarith

/-- The mean-coordinate block is dominated by the full five-block summary distance. -/
-- @node: ambientOperatorBridge_norm_mX_sub_le_dS
lemma norm_mX_sub_le_dS {dx dz : ℕ} (p q : SummarySpace dx dz) :
    ‖(WithLp.toLp 2 (p.mX - q.mX) : Euc dx)‖ ≤ dS p q := by
  rw [EuclideanSpace.norm_eq]
  unfold dS
  have h0 : 0 ≤ ‖matrixCLM (p.M0 - q.M0)‖ := norm_nonneg _
  have h1 : 0 ≤ ‖matrixCLM (p.M1 - q.M1)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖matrixCLM (p.N0 - q.N0)‖ := norm_nonneg _
  have h3 : 0 ≤ ‖matrixCLM (p.N1 - q.N1)‖ := norm_nonneg _
  simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  linarith

/-- For a full-column-rank rectangular matrix, its Moore--Penrose inverse is a genuine
left inverse.  This is the cancellation used when the proxy factorization is restricted to
the latent signal coordinates. -/
-- @node: ambientOperatorBridge_moorePenroseInverse_mul_eq_one_of_injective
lemma moorePenroseInverse_mul_eq_one_of_injective {rows cols : ℕ}
    (A : RectMatrix rows cols)
    (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    moorePenroseInverse A * A = (1 : RectMatrix cols cols) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  apply hA
  have hpenrose := (moorePenroseInverse_spec A).1
  apply PiLp.ext
  intro i
  have hmatrix : A * (moorePenroseInverse A * A) = A := by
    rw [← Matrix.mul_assoc, hpenrose]
  simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
    congrArg (fun M : RectMatrix rows cols => Matrix.mulVec M x i) hmatrix

/-- The Moore--Penrose inverse of a product of two full-column-rank factors is the
reverse product of their Moore--Penrose inverses. -/
-- @node: ambientOperatorBridge_moorePenroseInverse_mul_transpose
lemma moorePenroseInverse_mul_transpose {rows cols r : ℕ}
    (C : RectMatrix rows r) (B : RectMatrix cols r)
    (hC : Function.Injective (Matrix.toEuclideanLin C))
    (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    moorePenroseInverse (C * B.transpose) =
      (moorePenroseInverse B).transpose * moorePenroseInverse C := by
  have hCleft := moorePenroseInverse_mul_eq_one_of_injective C hC
  have hBleft := moorePenroseInverse_mul_eq_one_of_injective B hB
  have hBtrans : B.transpose * (moorePenroseInverse B).transpose =
      (1 : RectMatrix r r) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hBleft
  let G := (moorePenroseInverse B).transpose * moorePenroseInverse C
  have hspec : IsMoorePenroseInverse (C * B.transpose) G := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [G, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B.transpose, hBtrans, Matrix.one_mul,
        ← Matrix.mul_assoc (moorePenroseInverse C), hCleft, Matrix.one_mul]
    · simp only [G, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (moorePenroseInverse C), hCleft, Matrix.one_mul,
        ← Matrix.mul_assoc B.transpose, hBtrans, Matrix.one_mul]
    · have hMG : (C * B.transpose) * G = C * moorePenroseInverse C := by
        simp only [G, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc B.transpose, hBtrans, Matrix.one_mul]
      rw [hMG]
      exact (moorePenroseInverse_spec C).2.2.1
    · have hGM : G * (C * B.transpose) =
          (moorePenroseInverse B).transpose * B.transpose := by
        simp only [G, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (moorePenroseInverse C), hCleft, Matrix.one_mul]
      rw [hGM]
      have hsym := (moorePenroseInverse_spec B).2.2.1
      have heq : (moorePenroseInverse B).transpose * B.transpose =
          B * moorePenroseInverse B := by
        simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hsym
      rw [heq, hsym]
  exact isMoorePenroseInverse_unique (moorePenroseInverse_spec _) hspec

/-- Cancelling a full-rank proxy factorization identifies the ambient outcome operator as
the target-feature conjugation of the latent diagonal outcome means. -/
-- @node: ambientOperatorBridge_moorePenrose_outcome_factorization
lemma moorePenrose_outcome_factorization {rows cols r : ℕ}
    (C : RectMatrix rows r) (B : RectMatrix cols r) (mu : Fin r → ℝ)
    (hC : Function.Injective (Matrix.toEuclideanLin C))
    (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    moorePenroseInverse (C * B.transpose) *
        (C * Matrix.diagonal mu * B.transpose) =
      (moorePenroseInverse B).transpose * Matrix.diagonal mu * B.transpose := by
  rw [moorePenroseInverse_mul_transpose C B hC hB]
  have hCleft := moorePenroseInverse_mul_eq_one_of_injective C hC
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (moorePenroseInverse C), hCleft, Matrix.one_mul]

/-- The model's basis-free ambient contrast is exactly the target-feature conjugation of
the diagonal latent treatment effects. -/
-- @node: ambientOperatorBridge_model_ambientEffectOperator_factorization
lemma model_ambientEffectOperator_factorization
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ambientEffectOperator (obsSummary P) =
      (moorePenroseInverse (targetFeature P)).transpose *
        Matrix.diagonal (latentEffect P) * (targetFeature P).transpose := by
  let B := targetFeature P
  have hinj {rows : ℕ} (A : RectMatrix rows k)
      (hmargin : sigma0 ≤ signalMinSingular A) :
      Function.Injective (Matrix.toEuclideanLin A) := by
    rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hik : i ≤ k - 1 := by
      simpa using (Nat.le_sub_one_of_lt (by simpa using hi))
    exact lt_of_lt_of_le (lt_of_lt_of_le hsigma hmargin)
      ((Matrix.toEuclideanLin A).singularValues_antitone hik)
  have hB : Function.Injective (Matrix.toEuclideanLin B) :=
    hinj B hM.proxyRankMargin.2.2
  have harm (t : Bool) :
      Function.Injective (Matrix.toEuclideanLin
        (referenceFeature P t * latentArmWeights P t)) := by
    have hA : Function.Injective (Matrix.toEuclideanLin (referenceFeature P t)) := by
      cases t
      · exact hinj _ hM.proxyRankMargin.1
      · exact hinj _ hM.proxyRankMargin.2.1
    have hD := latentArmWeights_injective P hpi hM.latentArmPositivity t
    intro x y hxy
    apply hD
    apply hA
    apply PiLp.ext
    intro i
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      congrArg (fun z : Euc dz => z.ofLp i) hxy
  have ht (t : Bool) :
      moorePenroseInverse (observedProxyMoment (obsSummary P) t) *
          observedOutcomeProxyMoment (obsSummary P) t =
        (moorePenroseInverse B).transpose * Matrix.diagonal (latentMean P t) * B.transpose := by
    rw [observedProxyMoment_factorization P hk hkx hL hpi hM t,
      observedOutcomeProxyMoment_factorization P hk hpi hM t]
    exact moorePenrose_outcome_factorization
      (referenceFeature P t * latentArmWeights P t) B (latentMean P t) (harm t) hB
  simp only [ambientEffectOperator]
  change moorePenroseInverse (observedProxyMoment (obsSummary P) true) *
      observedOutcomeProxyMoment (obsSummary P) true -
      moorePenroseInverse (observedProxyMoment (obsSummary P) false) *
      observedOutcomeProxyMoment (obsSummary P) false = _
  rw [ht true, ht false]
  unfold B latentEffect
  have hdiag : Matrix.diagonal (fun u => latentMean P true u - latentMean P false u) =
      Matrix.diagonal (latentMean P true) - Matrix.diagonal (latentMean P false) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  rw [hdiag]
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- Every model-generated arm moment has exactly the latent rank.  This packages the
lower-rank consequence of the observed singular margin with the upper-rank consequence of
the latent factorization, in the form required by the moving-space Moore--Penrose estimate. -/
-- @node: ambientOperatorBridge_model_summary_rank_eq
lemma model_summary_rank_eq {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (t : Bool) :
    (observedProxyMoment (obsSummary P) t).rank = k := by
  let M := observedProxyMoment (obsSummary P) t
  have hfac := observedProxyMoment_factorization P hk hkx hL hpi hM t
  have hmargin := observedProxyMoment_minSingular_of_factorization
    P hk hpi hsigma hM t hfac
  have hpos : 0 < singularValue M (k - 1) :=
    lt_of_lt_of_le (mul_pos hpi (sq_pos_of_pos hsigma)) (by simpa [M] using hmargin)
  have hlower : k ≤ M.rank := by
    have hlt : k - 1 < Module.finrank ℝ (Matrix.toEuclideanLin M).range :=
      (Matrix.toEuclideanLin M).singularValues_pos_iff_lt_finrank_range.mp hpos
    have hrank : Module.finrank ℝ (Matrix.toEuclideanLin M).range = M.rank := by
      exact (M.rank_eq_finrank_range_toLin
        (EuclideanSpace.basisFun (Fin dz) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin dx) ℝ).toBasis).symm
    rw [hrank] at hlt
    omega
  have hupper : M.rank ≤ k := by
    rw [show M = referenceFeature P t * latentArmWeights P t *
        (targetFeature P).transpose by simpa [M] using hfac]
    exact (Matrix.rank_mul_le_left
      (referenceFeature P t * latentArmWeights P t) (targetFeature P).transpose).trans
      (Matrix.rank_le_width _)
  change M.rank = k
  omega

/-- Model membership supplies, simultaneously in both arms, all quantitative hypotheses used
by the ambient Moore--Penrose perturbation bound. -/
-- @node: ambientOperatorBridge_model_summary_ambient_bounds
lemma model_summary_ambient_bounds {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    (∀ t : Bool,
      (observedProxyMoment (obsSummary P) t).rank = k ∧
      pi0 * sigma0 ^ 2 ≤ singularValue (observedProxyMoment (obsSummary P) t) (k - 1) ∧
      ‖matrixCLM (observedOutcomeProxyMoment (obsSummary P) t)‖ ≤ L) ∧
      ‖(WithLp.toLp 2 (obsSummary P).mX : Euc dx)‖ ≤ L := by
  have hEnv := observedSummary_envelopes_of_model P hk hkx hL hpi hM
  refine ⟨?_, ?_⟩
  · intro t
    refine ⟨model_summary_rank_eq P hk hkx hL hpi hsigma hM t, ?_, ?_⟩
    · exact observedProxyMoment_minSingular_of_factorization P hk hpi hsigma hM t
        (observedProxyMoment_factorization P hk hkx hL hpi hM t)
    · cases t with
      | false => simpa [observedOutcomeProxyMoment] using (hEnv.1 false).2
      | true => simpa [observedOutcomeProxyMoment] using (hEnv.1 true).2
  · exact hEnv.2

/-- The model anchor makes the first ambient coordinate the all-ones right anchor in latent
coordinates.  This is the paper-local identity `Bᵀ e₁ = 1` used by the spectral-law
representation certificate. -/
-- @node: ambientOperatorBridge_targetFeature_transpose_firstBasis
lemma targetFeature_transpose_firstBasis {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    Matrix.mulVec (targetFeature P).transpose (firstBasis dx) = fun _ => 1 := by
  have hdx : 0 < dx := lt_of_lt_of_le (by omega : 0 < k) hkx
  funext u
  let i0 : Fin dx := ⟨0, hdx⟩
  have hclass : 0 < P (latentClass u) := by
    exact lt_of_lt_of_le
      (latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u false)
      (MeasureTheory.measure_mono fun _ hw => hw.1)
  have hanchor : ∀ᵐ w ∂P.restrict (latentClass u), w.X i0 = 1 :=
    MeasureTheory.ae_restrict_of_ae (hM.anchor.mono fun w hw => hw i0 rfl)
  let _ : MeasureTheory.IsProbabilityMeasure
      (normalizedRestrict P (latentClass u)) :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hclass
  have hmean : targetFeature P i0 u = 1 := by
    rw [targetFeature, conditionalMean_eq_normalizedRestrictedIntegral hclass]
    unfold normalizedRestrictedIntegral
    rw [MeasureTheory.integral_congr_ae ((ae_normalizedRestrict_iff hclass).mpr hanchor)]
    simp
  have hfirst : firstBasis dx = Pi.single i0 1 := by
    funext i
    by_cases hi : i = i0
    · subst i
      simp [firstBasis, i0]
    · have hval : i.val ≠ 0 := fun hz => hi (Fin.ext hz)
      simp [firstBasis, hi, hval]
  rw [hfirst]
  simp [Matrix.mulVec, hmean]

/-- The canonical right anchor has Euclidean norm one whenever the ambient dimension is
positive. -/
-- @node: ambientOperatorBridge_norm_firstBasis
lemma norm_firstBasis {dx : ℕ} (hdx : 0 < dx) :
    ‖(WithLp.toLp 2 (firstBasis dx) : Euc dx)‖ = 1 := by
  cases dx with
  | zero => omega
  | succ n =>
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
      simp [firstBasis]

/-- The observable target-proxy mean is the target-feature matrix applied to the latent
class-mass vector. -/
-- @node: ambientOperatorBridge_obsSummary_mX_factorization
lemma obsSummary_mX_factorization {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    (obsSummary P).mX = Matrix.mulVec (targetFeature P) (latentMass P) := by
  open MeasureTheory in
    ext j
    change (∫ o, o.X j ∂obsLaw P) = ∑ u,
      conditionalMean P (latentClass u) (fun w => w.X j) * P.real (latentClass u)
    rw [obsLaw]
    rw [integral_map (f := fun o : Obs dx dz => o.X j)
      (obsMap_measurable k dx dz).aemeasurable
      (((measurable_pi_apply j).comp measurable_obs_X).aestronglyMeasurable)]
    simp only [obsMap]
    have hXmeas : Measurable (fun w : FullData k dx dz => w.X j) :=
      (measurable_pi_apply j).comp measurable_fullData_X
    have hXint : Integrable (fun w : FullData k dx dz => w.X j) P := by
      apply Integrable.of_bound hXmeas.aestronglyMeasurable L
      filter_upwards [hM.boundedX] with w hw
      have hj := PiLp.norm_apply_le (WithLp.toLp 2 w.X : Euc dx) j
      have hcoord : |w.X j| ≤ ‖(WithLp.toLp 2 w.X : Euc dx)‖ := by
        simpa [Real.norm_eq_abs] using hj
      exact hcoord.trans (by simpa [EuclideanSpace.norm_eq] using hw)
    have hdisj : Pairwise (Function.onFun Disjoint
        (fun u : Fin k => latentClass (dx := dx) (dz := dz) u)) := by
      intro u v huv
      change Disjoint (latentClass (dx := dx) (dz := dz) u)
        (latentClass (dx := dx) (dz := dz) v)
      rw [Set.disjoint_left]
      intro w hwu hwv
      exact huv (hwu.symm.trans hwv)
    have hunion : (⋃ u : Fin k, latentClass (dx := dx) (dz := dz) u) = Set.univ := by
      ext w
      simp [latentClass]
    have hpart : (∫ w, w.X j ∂P) = ∑ u : Fin k,
        ∫ w in latentClass (dx := dx) (dz := dz) u, w.X j ∂P := by
      calc
        (∫ w, w.X j ∂P) = ∫ w in Set.univ, w.X j ∂P := by simp
        _ = ∫ w in (⋃ u : Fin k, latentClass (dx := dx) (dz := dz) u), w.X j ∂P := by
          rw [hunion]
        _ = _ := integral_iUnion_fintype (s := fun u : Fin k =>
          latentClass (dx := dx) (dz := dz) u)
          (fun _ => measurableSet_latentClass _) hdisj (fun _ => hXint.integrableOn)
    rw [hpart]
    apply Finset.sum_congr rfl
    intro u _
    have hclass : 0 < P (latentClass u) := by
      exact lt_of_lt_of_le
        (latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u false)
        (measure_mono fun _ hw => hw.1)
    unfold conditionalMean
    have hreal : P.real (latentClass u) ≠ 0 := by
      exact ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hclass, measure_ne_top P _⟩
    rw [inv_mul_eq_div, div_mul_cancel₀ _ hreal]

/-- An explicit functional-calculus formula for the target-feature factorization represents
the labelled latent-effect law.  This bridge uses only the mean and anchor identities and is
insensitive to repeated effect values. -/
-- @node: ambientOperatorBridge_represents_raw_quotientLaw
lemma represents_raw_quotientLaw {k dx : ℕ} {A : RectMatrix dx dx}
    (D : RealDiagonalization A) (B : RectMatrix dx k)
    (p tau : Fin k → ℝ) (m c : Euc dx)
    (hm : m = WithLp.toLp 2 (Matrix.mulVec B p))
    (hc : Matrix.mulVec B.transpose c = fun _ => 1)
    (hcalc : ∀ f : ℝ → ℝ, f 0 = 0 →
      D.applyFunction f =
        (moorePenroseInverse B).transpose * Matrix.diagonal (f ∘ tau) * B.transpose)
    (hleft : moorePenroseInverse B * B = 1) :
    RepresentsAtomicLaw D m c
      ({ weight := p, atom := tau } :
        CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k)) := by
  intro f _hf _hf0
  rw [hcalc f _hf0, hm]
  unfold CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.integral anchorEval
  change (∑ u, p u * f (tau u)) =
    ∑ i, (((moorePenroseInverse B).transpose * Matrix.diagonal (f ∘ tau) *
      B.transpose).mulVec c.ofLp i) * (B.mulVec p i)
  rw [← Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  have hdiag : (Matrix.diagonal (f ∘ tau)).mulVec (fun _ => 1) = f ∘ tau := by
    ext u
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [hdiag]
  change (∑ u, p u * f (tau u)) = ∑ i,
    (∑ u, moorePenroseInverse B u i * f (tau u)) * (∑ v, B i v * p v)
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  calc
    p y * f (tau y) =
        ∑ i, (p y * f (tau i)) * ∑ x, moorePenroseInverse B i x * B x y := by
      simp_rw [show ∀ i, (∑ x, moorePenroseInverse B i x * B x y) =
          if i = y then 1 else 0 by
        intro i
        have hi := congrArg (fun M : RectMatrix k k => M i y) hleft
        simpa [Matrix.mul_apply, Matrix.one_apply] using hi]
      simp
    _ = ∑ i, ∑ x, moorePenroseInverse B i x * f (tau i) * (B x y * p y) := by
      symm
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- A model-specific diagonalization whose functional calculus has the target-feature formula
automatically represents the model's raw quotient law. -/
-- @node: ambientOperatorBridge_model_represents_raw_quotientLaw
lemma model_represents_raw_quotientLaw
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (D : RealDiagonalization (ambientEffectOperator (obsSummary P)))
    (hcalc : ∀ f : ℝ → ℝ, f 0 = 0 →
      D.applyFunction f =
        (moorePenroseInverse (targetFeature P)).transpose *
          Matrix.diagonal (f ∘ latentEffect P) * (targetFeature P).transpose) :
    RepresentsAtomicLaw D
      (WithLp.toLp 2 (obsSummary P).mX) (WithLp.toLp 2 (firstBasis dx))
      (GapFreeModulusBridge.asNeutral
        (quotientLawRaw P (effectRadius dz L sigma0))) := by
  apply represents_raw_quotientLaw D (targetFeature P) (latentMass P) (latentEffect P)
  · exact congrArg (WithLp.toLp 2) (obsSummary_mX_factorization P hpi hM)
  · simpa using targetFeature_transpose_firstBasis P hk hkx hpi hM
  · exact hcalc
  · apply moorePenroseInverse_mul_eq_one_of_injective
    rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hik : i ≤ k - 1 := by
      simpa using (Nat.le_sub_one_of_lt (by simpa using hi))
    exact lt_of_lt_of_le (lt_of_lt_of_le hsigma hM.proxyRankMargin.2.2)
      ((Matrix.toEuclideanLin (targetFeature P)).singularValues_antitone hik)

/-- Once each model supplies its own bounded real diagonalization and representation
certificate, the neutral collision-safe estimate and the moving-space Moore--Penrose bound
assemble into a summary-metric modulus.  The two diagonalizers are unrelated. -/
-- @node: ambientOperatorBridge_atomicW1_le_dS_of_certificates
theorem atomicW1_le_dS_of_certificates {k dx dz r : ℕ}
    (p q : SummarySpace dx dz)
    (mu nu : CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k))
    (Dp : RealDiagonalization (ambientEffectOperator p))
    (Dq : RealDiagonalization (ambientEffectOperator q))
    {s L kappa R : ℝ}
    (hs : 0 < s) (hL : 0 ≤ L) (hkappa : 0 ≤ kappa) (hR : 0 ≤ R)
    (hdx : 0 < dx)
    (hrp0 : p.M0.rank = r) (hrq0 : q.M0.rank = r)
    (hrp1 : p.M1.rank = r) (hrq1 : q.M1.rank = r)
    (hmp0 : s ≤ singularValue p.M0 (r - 1))
    (hmq0 : s ≤ singularValue q.M0 (r - 1))
    (hmp1 : s ≤ singularValue p.M1 (r - 1))
    (hmq1 : s ≤ singularValue q.M1 (r - 1))
    (hNp0 : ‖p.N0‖ ≤ L) (hNp1 : ‖p.N1‖ ≤ L)
    (hmq : ‖(WithLp.toLp 2 q.mX : Euc dx)‖ ≤ L)
    (hmu : mu.Valid) (hnu : nu.Valid)
    (hrepP : RepresentsAtomicLaw Dp
      (WithLp.toLp 2 p.mX) (WithLp.toLp 2 (firstBasis dx)) mu)
    (hrepQ : RepresentsAtomicLaw Dq
      (WithLp.toLp 2 q.mX) (WithLp.toLp 2 (firstBasis dx)) nu)
    (hkP : Dp.conditionNumber ≤ kappa) (hkQ : Dq.conditionNumber ≤ kappa)
    (hRP : Dp.SpectrumBound R) (hRQ : Dq.SpectrumBound R) :
    CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1 mu nu ≤
      (kappa * R + L * ((dx : ℝ) ^ 2 * kappa ^ 2) *
        (3 * s⁻¹ ^ 2 * L + s⁻¹)) * dS p q := by
  have hop := norm_ambientEffectOperator_sub_le p q hs hL
    hrp0 hrq0 hrp1 hrq1 hmp0 hmq0 hmp1 hmq1 hNp0 hNp1
  have hm := norm_mX_sub_le_dS p q
  have hw := atomicW1_le_operator_anchor_perturbation Dp Dq
    (WithLp.toLp 2 p.mX) (WithLp.toLp 2 q.mX)
    (WithLp.toLp 2 (firstBasis dx)) (WithLp.toLp 2 (firstBasis dx))
    mu nu hmu hnu hrepP hrepQ hkP hkQ hR hRP hRQ
  rw [norm_firstBasis hdx] at hw
  simp only [sub_self, norm_zero, mul_one, mul_zero, add_zero] at hw
  have hm' : ‖(WithLp.toLp 2 p.mX : Euc dx) - WithLp.toLp 2 q.mX‖ ≤ dS p q := by
    simpa using hm
  calc
    CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1 mu nu ≤
        ‖(WithLp.toLp 2 p.mX : Euc dx) - WithLp.toLp 2 q.mX‖ * (kappa * R) +
          ‖(WithLp.toLp 2 q.mX : Euc dx)‖ *
            ((dx : ℝ) ^ 2 * kappa * kappa *
              ‖ambientEffectOperator p - ambientEffectOperator q‖) := hw
    _ ≤ dS p q * (kappa * R) +
          L * ((dx : ℝ) ^ 2 * kappa * kappa *
            ((3 * s⁻¹ ^ 2 * L + s⁻¹) * dS p q)) := by
      have hsInv : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
      have hdS0 : 0 ≤ dS p q := by
        unfold dS
        positivity
      gcongr
    _ = (kappa * R + L * ((dx : ℝ) ^ 2 * kappa ^ 2) *
          (3 * s⁻¹ ^ 2 * L + s⁻¹)) * dS p q := by ring

/-- Model membership discharges every analytic side condition in the ambient certificate
comparison.  What remains for the paper-specific spectral step is exactly one independently
chosen real diagonalization and representation certificate for each model law. -/
-- @node: ambientOperatorBridge_modelLaw_wass1_le_dS_of_certificates
theorem modelLaw_wass1_le_dS_of_certificates
    {k dx dz : ℕ} {L pi0 sigma0 kappa : ℝ}
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (P Q : ModelLaw k dx dz L pi0 sigma0)
    (DP : RealDiagonalization (ambientEffectOperator P.summary))
    (DQ : RealDiagonalization (ambientEffectOperator Q.summary))
    (hrepP : RepresentsAtomicLaw DP
      (WithLp.toLp 2 P.summary.mX) (WithLp.toLp 2 (firstBasis dx))
      (GapFreeModulusBridge.asNeutral (quotientLawRaw P.P
        (effectRadius dz L sigma0))))
    (hrepQ : RepresentsAtomicLaw DQ
      (WithLp.toLp 2 Q.summary.mX) (WithLp.toLp 2 (firstBasis dx))
      (GapFreeModulusBridge.asNeutral (quotientLawRaw Q.P
        (effectRadius dz L sigma0))))
    (hkappa : 0 ≤ kappa)
    (hkP : DP.conditionNumber ≤ kappa) (hkQ : DQ.conditionNumber ≤ kappa)
    (hRP : DP.SpectrumBound (effectRadius dz L sigma0))
    (hRQ : DQ.SpectrumBound (effectRadius dz L sigma0)) :
    AtomicLaw.LawModulo.wass1 (by
        letI := P.prob
        exact quotientLaw P.P P.model)
      (by
        letI := Q.prob
        exact quotientLaw Q.P Q.model) ≤
      (kappa * effectRadius dz L sigma0 +
        L * ((dx : ℝ) ^ 2 * kappa ^ 2) *
          (3 * (pi0 * sigma0 ^ 2)⁻¹ ^ 2 * L +
            (pi0 * sigma0 ^ 2)⁻¹)) * dS P.summary Q.summary := by
  letI := P.prob
  have hPb := model_summary_ambient_bounds P.P hk hkx hkz hL hpi hpiMax
    hsigma hsigmaMax P.model
  letI := Q.prob
  have hQb := model_summary_ambient_bounds Q.P hk hkx hkz hL hpi hpiMax
    hsigma hsigmaMax Q.model
  rw [quotientLaw, quotientLaw, AtomicLaw.LawModulo.wass1_ofProbabilityLaw]
  rw [GapFreeModulusBridge.wass1_eq_neutralW1
    (quotientLawRaw_valid P.P P.model) (quotientLawRaw_valid Q.P Q.model)]
  apply atomicW1_le_dS_of_certificates P.summary Q.summary
    (GapFreeModulusBridge.asNeutral (quotientLawRaw P.P (effectRadius dz L sigma0)))
    (GapFreeModulusBridge.asNeutral (quotientLawRaw Q.P (effectRadius dz L sigma0)))
    DP DQ (mul_pos hpi (sq_pos_of_pos hsigma)) (by linarith) hkappa
    (by unfold effectRadius; positivity) (by omega)
  · exact (hPb.1 false).1
  · exact (hQb.1 false).1
  · exact (hPb.1 true).1
  · exact (hQb.1 true).1
  · exact (hPb.1 false).2.1
  · exact (hQb.1 false).2.1
  · exact (hPb.1 true).2.1
  · exact (hQb.1 true).2.1
  · exact (hPb.1 false).2.2
  · exact (hPb.1 true).2.2
  · exact hQb.2
  · exact GapFreeModulusBridge.asNeutral_valid
      (quotientLawRaw_valid P.P P.model)
  · exact GapFreeModulusBridge.asNeutral_valid
      (quotientLawRaw_valid Q.P Q.model)
  · exact hrepP
  · exact hrepQ
  · exact hkP
  · exact hkQ
  · exact hRP
  · exact hRQ

end AmbientOperatorBridge
end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
