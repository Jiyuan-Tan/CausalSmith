import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.QuotientLaw
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.OutcomeFactorization
import Mathlib.Topology.Compactness.Compact

/-! Feasible-summary closure, nearest-summary repair, and ordered mass extraction. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open Causalean.Mathlib.Probability

/-- A probability law together with membership in the uniformly conditioned model. -/
structure ModelLaw (k dx dz : ℕ) (L pi0 sigma0 : ℝ) where
  P : Measure (FullData k dx dz) -- @realizes \(P\)(member law carrier)
  prob : IsProbabilityMeasure P
  model : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P

noncomputable def ModelLaw.summary {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (Q : ModelLaw k dx dz L pi0 sigma0) : SummarySpace dx dz := by
  letI := Q.prob
  exact obsSummary Q.P

/-- Admissible summary image. @realizes \(\mathscr S\)(S(M)) -/
def admissibleImage (k dx dz : ℕ) (L pi0 sigma0 : ℝ) : Set (SummarySpace dx dz) :=
  {s | ∃ Q : ModelLaw k dx dz L pi0 sigma0, Q.summary = s}

/-- Closed feasible-summary space. @realizes \(\mathcal K\)(closure of admissible image) -/
def summaryClosure (k dx dz : ℕ) (L pi0 sigma0 : ℝ) : Set (SummarySpace dx dz) :=
  closure (admissibleImage k dx dz L pi0 sigma0)

/-- The quotient-law functional on the admissible summary image.
    @realizes \(F\)(quotient functional on admissible summaries) -/
noncomputable def publishedQuotientFunctional (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (s : {q // q ∈ admissibleImage k dx dz L pi0 sigma0}) :
    AtomicLaw.LawModulo k (effectRadius dz L sigma0) := by
  let Q : ModelLaw k dx dz L pi0 sigma0 := Classical.choose s.property
  letI := Q.prob
  exact quotientLaw Q.P Q.model

/-- The `2k` spectral moments identify the quotient functional on the admissible image. -/
def PublishedMomentIdentity (k dx dz : ℕ) (L pi0 sigma0 : ℝ) : Prop :=
  ∀ (Q : ModelLaw k dx dz L pi0 sigma0)
    (j : Fin (2 * k)) -- @realizes \(j\)(moment order in Fin (2*k))
    (V : SignalBasis dx k) (hV : V.SpansSignal Q.summary),
    ∑ u, latentMass Q.P u * (latentEffect Q.P u) ^ (j : ℕ) =
      ∑ a, leftAnchor Q.summary V a *
        (∑ b, ((compressedOperator Q.summary V hV) ^ (j : ℕ)) a b * rightAnchor V b)

/-- The model anchor makes the first ambient coordinate the all-ones right anchor in latent
coordinates. -/
-- @node: publishedMomentIdentity_targetFeature_transpose_firstBasis
lemma publishedMomentIdentity_targetFeature_transpose_firstBasis
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    Matrix.mulVec (targetFeature P).transpose (firstBasis dx) = fun _ => 1 := by
  have hdx : 0 < dx := lt_of_lt_of_le (by omega : 0 < k) hkx
  funext u
  let i0 : Fin dx := ⟨0, hdx⟩
  have hclass : 0 < P (latentClass u) := by
    exact lt_of_lt_of_le
      (latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u false)
      (measure_mono fun _ hw => hw.1)
  have hanchor : ∀ᵐ w ∂P.restrict (latentClass u), w.X i0 = 1 :=
    ae_restrict_of_ae (hM.anchor.mono fun w hw => hw i0 rfl)
  let _ : IsProbabilityMeasure (normalizedRestrict P (latentClass u)) :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hclass
  have hmean : targetFeature P i0 u = 1 := by
    rw [targetFeature, conditionalMean_eq_normalizedRestrictedIntegral hclass]
    unfold normalizedRestrictedIntegral
    rw [integral_congr_ae ((ae_normalizedRestrict_iff hclass).mpr hanchor)]
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

/-- The observable target-proxy mean is the target-feature matrix applied to the latent masses. -/
-- @node: publishedMomentIdentity_obsSummary_mX_factorization
lemma publishedMomentIdentity_obsSummary_mX_factorization
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    (obsSummary P).mX = Matrix.mulVec (targetFeature P) (latentMass P) := by
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

/-- The positive compressed signal singular value implies injectivity for the moment identity. -/
-- @node: publishedMomentIdentity_injective_of_signalMinSingular_pos
lemma publishedMomentIdentity_injective_of_signalMinSingular_pos {rows cols : ℕ}
    (A : RectMatrix rows cols) (h : 0 < signalMinSingular A) :
    Function.Injective (Matrix.toEuclideanLin A) := by
  apply (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos _).2
  intro i hi
  rw [show Module.finrank ℝ (Euc cols) = cols by simp] at hi
  exact lt_of_lt_of_le h
    ((Matrix.toEuclideanLin A).singularValues_antitone (Nat.le_sub_one_of_lt hi))

/-- Injectivity makes the Gram determinant a unit for the moment-identity calculation. -/
-- @node: publishedMomentIdentity_gram_det_isUnit_of_injective
lemma publishedMomentIdentity_gram_det_isUnit_of_injective {rows cols : ℕ}
    (A : RectMatrix rows cols) (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    IsUnit (A.transpose * A).det := by
  let T := Matrix.toEuclideanLin A
  have hgram : Function.Injective (Matrix.toEuclideanLin (A.transpose * A)) := by
    have hc : Matrix.toEuclideanLin (A.transpose * A) = LinearMap.adjoint T ∘ₗ T := by
      calc
        Matrix.toEuclideanLin (A.transpose * A) =
            Matrix.toEuclideanLin A.transpose ∘ₗ T := by
          ext x i
          simp [T, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
        _ = LinearMap.adjoint T ∘ₗ T := by
          rw [← Matrix.conjTranspose_eq_transpose_of_trivial A,
            Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [hc]
    exact (LinearMap.adjoint_comp_self_injective_iff T).2 hA
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have he : Matrix.toEuclideanLin (A.transpose * A) (WithLp.toLp 2 x) =
      Matrix.toEuclideanLin (A.transpose * A) (WithLp.toLp 2 y) := by
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
  have := hgram he
  simpa using congrArg WithLp.ofLp this

/-- The Gram-form inverse is a left inverse in the injective moment-identity calculation. -/
-- @node: publishedMomentIdentity_penrose_left_inverse_of_injective
lemma publishedMomentIdentity_penrose_left_inverse_of_injective {rows cols : ℕ}
    (A : RectMatrix rows cols) (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    penroseInverse A * A = 1 := by
  letI := Matrix.invertibleOfIsUnitDet (A.transpose * A)
    (publishedMomentIdentity_gram_det_isUnit_of_injective A hA)
  simp only [penroseInverse]
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]

lemma publishedMomentIdentity_holds (k dx dz : ℕ) (L pi0 sigma0 : ℝ) :
    PublishedMomentIdentity k dx dz L pi0 sigma0 := by
  classical
  intro Q j V hV
  letI := Q.prob
  rcases Q.model.coreDomain with
    ⟨hk, hkx, _hkz, _hL, hpi, _hpiMax, hsigma, _hsigmaMax⟩
  let B := targetFeature Q.P
  let R : RectMatrix k k := B.transpose * V.V
  let C : Bool → RectMatrix dz k := fun t =>
    referenceFeature Q.P t * latentArmWeights Q.P t
  have hMfac (t : Bool) : observedProxyMoment Q.summary t * V.V = C t * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedProxyMoment_factorization Q.P hk hkx _hL hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hNfac (t : Bool) : observedOutcomeProxyMoment Q.summary t * V.V =
      C t * Matrix.diagonal (latentMean Q.P t) * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedOutcomeProxyMoment_factorization Q.P hk hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hAinj (t : Bool) : Function.Injective (Matrix.toEuclideanLin
      (observedProxyMoment Q.summary t * V.V)) := by
    have hm := observedProxyMoment_compression_margin Q.P hk hkx _hL hpi hsigma
      Q.model t V hV
    apply publishedMomentIdentity_injective_of_signalMinSingular_pos
    exact (mul_pos hpi (sq_pos_of_pos hsigma)).trans_le hm.2
  have hRinj : Function.Injective (Matrix.toEuclideanLin R) := by
    intro x y hxy
    apply hAinj false
    rw [hMfac false]
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      congrArg (Matrix.toEuclideanLin (C false)) hxy
  have hRunit : IsUnit R.det := by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    apply congrArg WithLp.ofLp
    apply hRinj
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
  letI := Matrix.invertibleOfIsUnitDet R hRunit
  have hterm (t : Bool) :
      penroseInverse (observedProxyMoment Q.summary t * V.V) *
          (observedOutcomeProxyMoment Q.summary t * V.V) =
        R⁻¹ * Matrix.diagonal (latentMean Q.P t) * R := by
    have hNrewrite : observedOutcomeProxyMoment Q.summary t * V.V =
        (observedProxyMoment Q.summary t * V.V) *
          (R⁻¹ * Matrix.diagonal (latentMean Q.P t) * R) := by
      rw [hMfac t, hNfac t]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R R⁻¹, Matrix.mul_inv_of_invertible,
        Matrix.one_mul]
    rw [hNrewrite, ← Matrix.mul_assoc,
      publishedMomentIdentity_penrose_left_inverse_of_injective _ (hAinj t), Matrix.one_mul]
  have hD : compressedOperator Q.summary V hV =
      R⁻¹ * Matrix.diagonal (latentEffect Q.P) * R := by
    unfold compressedOperator
    change genuinePenroseInverse (observedProxyMoment Q.summary true * V.V) *
        (observedOutcomeProxyMoment Q.summary true * V.V) -
      genuinePenroseInverse (observedProxyMoment Q.summary false * V.V) *
        (observedOutcomeProxyMoment Q.summary false * V.V) = _
    rw [genuinePenroseInverse_eq_penroseInverse_of_injective _ (hAinj true),
      genuinePenroseInverse_eq_penroseInverse_of_injective _ (hAinj false),
      hterm true, hterm false]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext a b
    by_cases hab : a = b <;>
      simp [Matrix.diagonal_apply, hab, latentEffect]
  have hpow (m : ℕ) : (compressedOperator Q.summary V hV) ^ m =
      R⁻¹ * Matrix.diagonal (fun u => (latentEffect Q.P u) ^ m) * R := by
    induction m with
    | zero =>
        simp [Matrix.diagonal_one]
    | succ m ih =>
        rw [pow_succ, ih, hD]
        have hdiag : Matrix.diagonal (fun u => (latentEffect Q.P u) ^ m) *
            Matrix.diagonal (latentEffect Q.P) =
              Matrix.diagonal (fun u => (latentEffect Q.P u) ^ (m + 1)) := by
          rw [Matrix.diagonal_mul_diagonal]
          congr 1
        calc
          (R⁻¹ * Matrix.diagonal (fun u => (latentEffect Q.P u) ^ m) * R) *
                (R⁻¹ * Matrix.diagonal (latentEffect Q.P) * R) =
              R⁻¹ * Matrix.diagonal (fun u => (latentEffect Q.P u) ^ m) *
                (R * R⁻¹) * Matrix.diagonal (latentEffect Q.P) * R := by
                  simp only [Matrix.mul_assoc]
          _ = R⁻¹ * (Matrix.diagonal (fun u => (latentEffect Q.P u) ^ m) *
                Matrix.diagonal (latentEffect Q.P)) * R := by
                  rw [Matrix.mul_inv_of_invertible]
                  simp [Matrix.mul_assoc]
          _ = _ := by rw [hdiag]
  have hCinj : Function.Injective (Matrix.toEuclideanLin (C false)) := by
    intro x y hxy
    have hpre : Matrix.toEuclideanLin
        (observedProxyMoment Q.summary false * V.V)
          (Matrix.toEuclideanLin R⁻¹ x) =
        Matrix.toEuclideanLin (observedProxyMoment Q.summary false * V.V)
          (Matrix.toEuclideanLin R⁻¹ y) := by
      rw [hMfac false]
      apply PiLp.ext
      intro i
      simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
        congrArg (fun z : Euc dz => z i) hxy
    have hxy' := hAinj false hpre
    have := congrArg (Matrix.toEuclideanLin R) hxy'
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible] using this
  have hMraw : observedProxyMoment Q.summary false = C false * B.transpose := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedProxyMoment_factorization Q.P hk hkx _hL hpi Q.model false]
  have hBt : penroseInverse (C false) * observedProxyMoment Q.summary false =
      B.transpose := by
    rw [hMraw, ← Matrix.mul_assoc,
      publishedMomentIdentity_penrose_left_inverse_of_injective _ hCinj,
      Matrix.one_mul]
  have hBfac : B = (observedProxyMoment Q.summary false).transpose *
      (penroseInverse (C false)).transpose := by
    have ht := congrArg Matrix.transpose hBt
    simpa [Matrix.transpose_mul] using ht.symm
  have hBmem (x : Euc k) : Matrix.toEuclideanLin B x ∈
      LinearMap.range (Matrix.toEuclideanLin V.V) := by
    rw [hV]
    apply show LinearMap.range (Matrix.toEuclideanLin
      (observedProxyMoment Q.summary false).transpose) ≤ signalRowspace Q.summary from
        le_sup_left
    refine ⟨Matrix.toEuclideanLin (penroseInverse (C false)).transpose x, ?_⟩
    rw [hBfac]
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  have hproj : V.V * V.V.transpose * B = B := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro x
    rcases hBmem x with ⟨y, hy⟩
    have hgram : V.V.transpose * V.V = (1 : RectMatrix k k) := by
      ext a b
      simpa [Matrix.mul_apply, Matrix.one_apply] using V.orthonormal a b
    apply PiLp.ext
    intro i
    change ((V.V * V.V.transpose * B).mulVec x.ofLp) i = (B.mulVec x.ofLp) i
    have hyfun : V.V.mulVec y.ofLp = B.mulVec x.ofLp := by
      simpa [Matrix.toEuclideanLin_apply] using congrArg WithLp.ofLp hy
    calc
      ((V.V * V.V.transpose * B).mulVec x.ofLp) i =
          ((V.V * V.V.transpose).mulVec (B.mulVec x.ofLp)) i := by
            exact congrFun (Matrix.mulVec_mulVec x.ofLp
              (V.V * V.V.transpose) B).symm i
      _ = (V.V.mulVec (V.V.transpose.mulVec (B.mulVec x.ofLp))) i := by
            exact congrFun (Matrix.mulVec_mulVec (B.mulVec x.ofLp)
              V.V V.V.transpose).symm i
      _ = (V.V.mulVec (V.V.transpose.mulVec (V.V.mulVec y.ofLp))) i := by rw [hyfun]
      _ = (V.V.mulVec ((V.V.transpose * V.V).mulVec y.ofLp)) i := by
            exact congrArg (fun z : Fin k → ℝ => (V.V.mulVec z) i)
              (Matrix.mulVec_mulVec y.ofLp V.V.transpose V.V)
      _ = (V.V.mulVec y.ofLp) i := by rw [hgram, Matrix.one_mulVec]
      _ = (B.mulVec x.ofLp) i := congrFun hyfun i
  have hBfactor : B = V.V * R.transpose := by
    rw [show R.transpose = V.V.transpose * B by
      simp [R, Matrix.transpose_mul]]
    simpa [Matrix.mul_assoc] using hproj.symm
  rw [hpow (j : ℕ)]
  have hmX : Q.summary.mX = Matrix.mulVec B (latentMass Q.P) := by
    exact publishedMomentIdentity_obsSummary_mX_factorization Q.P hpi Q.model
  have hanchor : Matrix.mulVec B.transpose (firstBasis dx) = fun _ => 1 := by
    exact publishedMomentIdentity_targetFeature_transpose_firstBasis Q.P hk hkx hpi Q.model
  have hRt : R.transpose = V.V.transpose * B := by
    simp [R, Matrix.transpose_mul]
  have hBt : B.transpose = R * V.V.transpose := by
    have ht := congrArg Matrix.transpose hBfactor
    simpa [Matrix.transpose_mul] using ht
  have hleftVec : Matrix.mulVec V.V.transpose Q.summary.mX =
      Matrix.mulVec R.transpose (latentMass Q.P) := by
    calc
      Matrix.mulVec V.V.transpose Q.summary.mX =
          Matrix.mulVec V.V.transpose (Matrix.mulVec B (latentMass Q.P)) := by rw [hmX]
      _ = Matrix.mulVec (V.V.transpose * B) (latentMass Q.P) :=
        Matrix.mulVec_mulVec _ _ _
      _ = Matrix.mulVec R.transpose (latentMass Q.P) := by rw [← hRt]
  have hrightVec : Matrix.mulVec R (Matrix.mulVec V.V.transpose (firstBasis dx)) =
      fun _ => 1 := by
    calc
      Matrix.mulVec R (Matrix.mulVec V.V.transpose (firstBasis dx)) =
          Matrix.mulVec (R * V.V.transpose) (firstBasis dx) :=
        Matrix.mulVec_mulVec _ _ _
      _ = Matrix.mulVec B.transpose (firstBasis dx) := by rw [← hBt]
      _ = fun _ => 1 := hanchor
  have hleftAnchor : leftAnchor Q.summary V =
      Matrix.mulVec V.V.transpose Q.summary.mX := by
    funext a
    simp [leftAnchor, Matrix.mulVec, dotProduct, mul_comm]
  have hrightAnchor : rightAnchor V =
      Matrix.mulVec V.V.transpose (firstBasis dx) := by
    funext a
    simp [rightAnchor, Matrix.mulVec, dotProduct]
  have hoperatorVec : Matrix.mulVec
        (R⁻¹ * Matrix.diagonal (fun u => (latentEffect Q.P u) ^ (j : ℕ)) * R)
        (Matrix.mulVec V.V.transpose (firstBasis dx)) =
      Matrix.mulVec R⁻¹ (Matrix.mulVec
        (Matrix.diagonal (fun u => (latentEffect Q.P u) ^ (j : ℕ))) (fun _ => 1)) := by
    calc
      _ = Matrix.mulVec (R⁻¹ * Matrix.diagonal
            (fun u => (latentEffect Q.P u) ^ (j : ℕ)))
          (Matrix.mulVec R (Matrix.mulVec V.V.transpose (firstBasis dx))) := by
            symm
            exact Matrix.mulVec_mulVec _ _ _
      _ = Matrix.mulVec (R⁻¹ * Matrix.diagonal
            (fun u => (latentEffect Q.P u) ^ (j : ℕ))) (fun _ => 1) := by
            rw [hrightVec]
      _ = _ := by
            symm
            exact Matrix.mulVec_mulVec _ _ _
  rw [hleftAnchor, hrightAnchor]
  change (latentMass Q.P) ⬝ᵥ (fun u => (latentEffect Q.P u) ^ (j : ℕ)) =
    (Matrix.mulVec V.V.transpose Q.summary.mX) ⬝ᵥ
      Matrix.mulVec
        (R⁻¹ * Matrix.diagonal (fun u => (latentEffect Q.P u) ^ (j : ℕ)) * R)
        (Matrix.mulVec V.V.transpose (firstBasis dx))
  rw [hleftVec]
  conv_rhs =>
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  rw [hoperatorVec, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec]
  apply Finset.sum_congr rfl
  intro u _
  simp [Matrix.mulVec_diagonal]

/-- Homogeneity at a common latent effect.
    @realizes \(\tau_\star\)(common value of all latent effects) -/
def HomogeneousEffects {k dx dz : ℕ} (P : Measure (FullData k dx dz))
    (tauStar : ℝ) : Prop := ∀ u, latentEffect P u = tauStar

/-- The homogeneous-effect specialization included in the closed-summary definition. -/
def HomogeneousSummarySpecialization (k dx dz : ℕ) (L pi0 sigma0 : ℝ) : Prop :=
  ∀ (Q : ModelLaw k dx dz L pi0 sigma0) (tauStar : ℝ)
    (V : SignalBasis dx k) (hV : V.SpansSignal Q.summary),
    HomogeneousEffects Q.P tauStar →
      compressedOperator Q.summary V hV = tauStar • (1 : RectMatrix k k) ∧
      AtomicLaw.LawModulo.toMeasure (by
        letI := Q.prob
        exact quotientLaw Q.P Q.model) = Measure.dirac tauStar

/-- Positivity of the last singular value makes a finite rectangular map injective. -/
-- @node: summaryClosure_injective_of_signalMinSingular_pos
lemma summaryClosure_injective_of_signalMinSingular_pos {rows cols : ℕ}
    (A : RectMatrix rows cols) (h : 0 < signalMinSingular A) :
    Function.Injective (Matrix.toEuclideanLin A) := by
  apply (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos _).2
  intro i hi
  rw [show Module.finrank ℝ (Euc cols) = cols by simp] at hi
  exact lt_of_lt_of_le h
    ((Matrix.toEuclideanLin A).singularValues_antitone (Nat.le_sub_one_of_lt hi))

/-- Injectivity of a rectangular map makes its Gram determinant a unit. -/
-- @node: summaryClosure_gram_det_isUnit_of_injective
lemma summaryClosure_gram_det_isUnit_of_injective {rows cols : ℕ}
    (A : RectMatrix rows cols) (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    IsUnit (A.transpose * A).det := by
  let T := Matrix.toEuclideanLin A
  have hgram : Function.Injective (Matrix.toEuclideanLin (A.transpose * A)) := by
    have hc : Matrix.toEuclideanLin (A.transpose * A) = LinearMap.adjoint T ∘ₗ T := by
      calc
        Matrix.toEuclideanLin (A.transpose * A) =
            Matrix.toEuclideanLin A.transpose ∘ₗ T := by
          ext x i
          simp [T, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
        _ = LinearMap.adjoint T ∘ₗ T := by
          rw [← Matrix.conjTranspose_eq_transpose_of_trivial A,
            Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [hc]
    exact (LinearMap.adjoint_comp_self_injective_iff T).2 hA
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have he : Matrix.toEuclideanLin (A.transpose * A) (WithLp.toLp 2 x) =
      Matrix.toEuclideanLin (A.transpose * A) (WithLp.toLp 2 y) := by
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
  have := hgram he
  simpa using congrArg WithLp.ofLp this

/-- The Gram-form Penrose inverse is a left inverse on every injective rectangular map. -/
-- @node: summaryClosure_penrose_left_inverse_of_injective
lemma summaryClosure_penrose_left_inverse_of_injective {rows cols : ℕ}
    (A : RectMatrix rows cols) (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    penroseInverse A * A = 1 := by
  letI := Matrix.invertibleOfIsUnitDet (A.transpose * A)
    (summaryClosure_gram_det_isUnit_of_injective A hA)
  simp only [penroseInverse]
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]

lemma homogeneousSummarySpecialization_holds (k dx dz : ℕ) (L pi0 sigma0 : ℝ) :
    HomogeneousSummarySpecialization k dx dz L pi0 sigma0 := by
  intro Q tauStar V hV hhom
  unfold HomogeneousEffects at hhom
  letI := Q.prob
  rcases Q.model.coreDomain with
    ⟨hk, hkx, hkz, hL, hpi, hpiMax, hsigma, hsigmaMax⟩
  let B := targetFeature Q.P
  let R : RectMatrix k k := B.transpose * V.V
  let C : Bool → RectMatrix dz k := fun t =>
    referenceFeature Q.P t * latentArmWeights Q.P t
  have hMfac (t : Bool) : observedProxyMoment Q.summary t * V.V = C t * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hNfac (t : Bool) : observedOutcomeProxyMoment Q.summary t * V.V =
      C t * Matrix.diagonal (latentMean Q.P t) * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedOutcomeProxyMoment_factorization Q.P hk hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hAinj (t : Bool) : Function.Injective (Matrix.toEuclideanLin
      (observedProxyMoment Q.summary t * V.V)) := by
    have hm := observedProxyMoment_compression_margin Q.P hk hkx hL hpi hsigma
      Q.model t V hV
    apply summaryClosure_injective_of_signalMinSingular_pos
    exact (mul_pos hpi (sq_pos_of_pos hsigma)).trans_le hm.2
  have hRinj : Function.Injective (Matrix.toEuclideanLin R) := by
    intro x y hxy
    apply hAinj false
    rw [hMfac false]
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      congrArg (Matrix.toEuclideanLin (C false)) hxy
  have hRunit : IsUnit R.det := by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    apply congrArg WithLp.ofLp
    apply hRinj
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
  letI := Matrix.invertibleOfIsUnitDet R hRunit
  have hterm (t : Bool) :
      penroseInverse (observedProxyMoment Q.summary t * V.V) *
          (observedOutcomeProxyMoment Q.summary t * V.V) =
        R⁻¹ * Matrix.diagonal (latentMean Q.P t) * R := by
    have hNrewrite : observedOutcomeProxyMoment Q.summary t * V.V =
        (observedProxyMoment Q.summary t * V.V) *
          (R⁻¹ * Matrix.diagonal (latentMean Q.P t) * R) := by
      rw [hMfac t, hNfac t]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R R⁻¹, Matrix.mul_inv_of_invertible,
        Matrix.one_mul]
    rw [hNrewrite, ← Matrix.mul_assoc,
      summaryClosure_penrose_left_inverse_of_injective _ (hAinj t), Matrix.one_mul]
  constructor
  · unfold compressedOperator
    change genuinePenroseInverse (observedProxyMoment Q.summary true * V.V) *
        (observedOutcomeProxyMoment Q.summary true * V.V) -
      genuinePenroseInverse (observedProxyMoment Q.summary false * V.V) *
        (observedOutcomeProxyMoment Q.summary false * V.V) = _
    rw [genuinePenroseInverse_eq_penroseInverse_of_injective _ (hAinj true),
      genuinePenroseInverse_eq_penroseInverse_of_injective _ (hAinj false),
      hterm true, hterm false]
    have hdiag : Matrix.diagonal (latentMean Q.P true) -
        Matrix.diagonal (latentMean Q.P false) =
          Matrix.diagonal (fun u => latentEffect Q.P u) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, latentEffect]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, hdiag]
    have hdiagStar : Matrix.diagonal (fun u => latentEffect Q.P u) =
        tauStar • (1 : RectMatrix k k) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simpa [Matrix.diagonal_apply] using hhom i
      · simp [Matrix.diagonal_apply, hij]
    rw [hdiagStar]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.inv_mul_of_invertible, smul_eq_mul]
  · rw [quotientLaw, AtomicLaw.LawModulo.toMeasure_eq_of_mk]
    unfold AtomicLaw.ProbabilityLaw.toMeasure AtomicLaw.toMeasure quotientLawRaw
    change (∑ i : Fin k, ENNReal.ofReal (latentMass Q.P i) •
      Measure.dirac (latentEffect Q.P i)) = Measure.dirac tauStar
    rw [show (∑ i : Fin k, ENNReal.ofReal (latentMass Q.P i) •
        Measure.dirac (latentEffect Q.P i)) =
        ∑ i : Fin k, ENNReal.ofReal (latentMass Q.P i) • Measure.dirac tauStar by
      apply Finset.sum_congr rfl
      intro i _
      rw [hhom i]]
    rw [← Finset.sum_smul]
    have hsumReal : ∑ i : Fin k, latentMass Q.P i = 1 := by
      simpa [quotientLawRaw] using (quotientLawRaw_valid Q.P Q.model).2.1
    have hsum : ∑ i : Fin k, ENNReal.ofReal (latentMass Q.P i) = 1 := by
      change ∑ i : Fin k, ENNReal.ofReal (Q.P.real (latentClass i)) = 1
      change (∑ i : Fin k, Q.P.real (latentClass i)) = 1 at hsumReal
      calc
        _ = ENNReal.ofReal (∑ i : Fin k, Q.P.real (latentClass i)) := by
          symm
          simpa using ENNReal.ofReal_sum_of_nonneg
            (s := Finset.univ) (f := fun i : Fin k => Q.P.real (latentClass i))
              (fun _ _ => measureReal_nonneg)
        _ = 1 := by rw [hsumReal]; exact ENNReal.ofReal_one
    rw [hsum, one_smul]

/-- The complete closed-summary node: its closure, identified quotient functional, spectral
moment identity, and homogeneous-effect specialization. -/
structure SummaryClosureData (k dx dz : ℕ) (L pi0 sigma0 : ℝ) where
  K : Set (SummarySpace dx dz)
  K_eq : K = closure (admissibleImage k dx dz L pi0 sigma0)
  F : {q // q ∈ admissibleImage k dx dz L pi0 sigma0} →
    AtomicLaw.LawModulo k (effectRadius dz L sigma0)
  momentIdentity : PublishedMomentIdentity k dx dz L pi0 sigma0
  homogeneous : HomogeneousSummarySpecialization k dx dz L pi0 sigma0

-- @node: def:summary-closure
noncomputable def summaryClosureData (k dx dz : ℕ) (L pi0 sigma0 : ℝ) :
    SummaryClosureData k dx dz L pi0 sigma0 where
  K := summaryClosure k dx dz L pi0 sigma0
  K_eq := rfl
  F := publishedQuotientFunctional k dx dz L pi0 sigma0
  momentIdentity := publishedMomentIdentity_holds k dx dz L pi0 sigma0
  homogeneous := homogeneousSummarySpecialization_holds k dx dz L pi0 sigma0

/-- Data supplied by the unique continuous extension and measurable nearest-point construction.
The extension is defined only on `K`, at the paper's fixed effect radius. -/
structure SummaryRepairData (k dx dz n : ℕ) (L pi0 sigma0 : ℝ) where
  k_pos : 0 < k
  radius_nonneg : 0 ≤ effectRadius dz L sigma0
  Fbar : {q // q ∈ summaryClosure k dx dz L pi0 sigma0} →
    AtomicLaw.LawModulo k (effectRadius dz L sigma0)
    -- @realizes \(\overline F\)(continuous extension on K)
  Pi : SummarySpace dx dz → SummarySpace dx dz -- @realizes \(\Pi\)(nearest selector)
  continuousFbar : Continuous Fbar
  extendsOnModel : ∀ Q : ModelLaw k dx dz L pi0 sigma0,
    Fbar ⟨Q.summary, by
      apply subset_closure
      exact ⟨Q, rfl⟩⟩ = by
      letI := Q.prob
      exact quotientLaw Q.P Q.model
  measurablePi : Measurable Pi
  nearest : ∀ s, summaryClosure k dx dz L pi0 sigma0 ≠ ∅ →
    Pi s ∈ summaryClosure k dx dz L pi0 sigma0 ∧
      ∀ q ∈ summaryClosure k dx dz L pi0 sigma0, dS (Pi s) s ≤ dS q s
  empty_fallback : summaryClosure k dx dz L pi0 sigma0 = ∅ → ∀ s, Pi s = 0
  measurableRepair : Measurable (fun sample : Fin n → Obs dx dz =>
    if hK : summaryClosure k dx dz L pi0 sigma0 = ∅ then
      AtomicLaw.LawModulo.deltaZeroLaw k_pos radius_nonneg
    else Fbar ⟨Pi (empSummary sample), (nearest _ hK).1⟩)

/-- The repaired estimator data. @realizes \(\widehat\nu_n\)(Fbar(Pi(empSummary))) -/
-- @node: def:summary-space-repair
noncomputable def summaryRepair {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (R : SummaryRepairData k dx dz n L pi0 sigma0) :
    (Fin n → Obs dx dz) → AtomicLaw.LawModulo k (effectRadius dz L sigma0) :=
  fun sample => if hK : summaryClosure k dx dz L pi0 sigma0 = ∅ then
      AtomicLaw.LawModulo.deltaZeroLaw R.k_pos R.radius_nonneg
    else R.Fbar ⟨R.Pi (empSummary sample), (R.nearest _ hK).1⟩

noncomputable def orderedMasses {k : ℕ} {radius : ℝ} (ν : AtomicLaw k radius) : Fin k → ℝ :=
  if (∀ i, 0 < ν.weight i) ∧ Function.Injective ν.atom then
    fun j => ∑ i, if (Finset.univ.filter fun l => ν.atom l < ν.atom i).card = j.val
      then ν.weight i else 0
  else fun _ => (k : ℝ)⁻¹

/-- Total effect-ordered mass estimator, with barycenter fallback.
    @realizes \(p^{\uparrow}(P)\)(ordered true masses)
    @realizes \(\widehat p_n^{\uparrow}\)(ordered estimated masses)
    @realizes \(\widetilde p_n\)(generic competitor type) -/
-- @node: def:labeled-weight-estimator
noncomputable def orderedWeightEstimator {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (R : SummaryRepairData k dx dz n L pi0 sigma0) :
    (Fin n → Obs dx dz) → (Fin k → ℝ) :=
  fun sample => orderedMasses (summaryRepair R sample).representative.1

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
