import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ConditionalMomentAdapters
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ObservedLawAdapters
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ObservedMarginAssembly
import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
import Causalean.Mathlib.Analysis.RectangularSignalSingularValues

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open ProbabilityTheory
open scoped BigOperators
open Causalean.Mathlib.Analysis
open Causalean.Mathlib.Probability

noncomputable local instance {m n : ℕ} : MeasurableSpace (Euc n →L[ℝ] Euc m) := borel _
local instance {m n : ℕ} : BorelSpace (Euc n →L[ℝ] Euc m) := ⟨rfl⟩

/-- The diagonal normalized latent-arm weight matrix retains the joint-cell positivity margin
at its least signal singular value. -/
-- @node: latentArmWeights_minSingular
lemma latentArmWeights_minSingular {k dx dz : ℕ} {pi0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hpi : 0 < pi0) (hpos : LatentArmPositivity (pi0 := pi0) P)
    (t : Bool) : pi0 ≤ signalMinSingular (latentArmWeights P t) := by
  apply le_singularValues_of_subspace
      (Matrix.toEuclideanLin (latentArmWeights P t)) ⊤ hpi.le
  · simp only [finrank_top, finrank_euclideanSpace, Fintype.card_fin]
    omega
  · intro x _hx
    have hsum : ∑ i : Fin k, (pi0 * x i) ^ 2 ≤
        ∑ i : Fin k, (latentArmWeights P t i i * x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hwi := latentArmWeight_lower P hpi hpos i t
      have hw0 : 0 ≤ latentArmWeights P t i i := hpi.le.trans hwi
      have hw2 : pi0 ^ 2 ≤ latentArmWeights P t i i ^ 2 :=
        (sq_le_sq₀ hpi.le hw0).2 hwi
      simpa only [mul_pow] using mul_le_mul_of_nonneg_right hw2 (sq_nonneg (x i))
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp only [Matrix.toEuclideanLin_apply, Real.norm_eq_abs, sq_abs]
    simp only [latentArmWeights, Matrix.mulVec_diagonal]
    have hsqrt := Real.sqrt_le_sqrt hsum
    rw [← Real.sqrt_sq hpi.le]
    rw [← Real.sqrt_mul (sq_nonneg pi0)]
    simpa only [Finset.mul_sum, mul_pow, latentArmWeights,
      Matrix.diagonal_apply_eq] using hsqrt

/-- Once the promoted conditional-moment argument supplies the proxy factorization, the three
quantitative factor margins yield the required armwise singular-value margin. -/
-- @node: observedProxyMoment_minSingular_of_factorization
lemma observedProxyMoment_minSingular_of_factorization
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (t : Bool)
    (hfac : observedProxyMoment (obsSummary P) t =
      referenceFeature P t * latentArmWeights P t * (targetFeature P).transpose) :
    pi0 * sigma0 ^ 2 ≤ singularValue (observedProxyMoment (obsSummary P) t) (k - 1) := by
  have injective_of_margin {rows : ℕ} (A : RectMatrix rows k)
      (hA : sigma0 ≤ signalMinSingular A) :
      Function.Injective (Matrix.toEuclideanLin A) := by
    rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hik : i ≤ k - 1 := by
      simpa using (Nat.le_sub_one_of_lt (by simpa using hi))
    exact lt_of_lt_of_le (lt_of_lt_of_le hsigma hA)
      ((Matrix.toEuclideanLin A).singularValues_antitone hik)
  have hAt : sigma0 ≤ signalMinSingular (referenceFeature P t) := by
    cases t with
    | false => exact hM.proxyRankMargin.1
    | true => exact hM.proxyRankMargin.2.1
  have hAinj := injective_of_margin (referenceFeature P t) hAt
  have hBinj := injective_of_margin (targetFeature P) hM.proxyRankMargin.2.2
  have hDinj := latentArmWeights_injective P hpi hM.latentArmPositivity t
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hprod := Matrix.singularValues_mul_mul_transpose_lower_bound
    (referenceFeature P t) (latentArmWeights P t) (targetFeature P)
    hAinj hDinj hBinj
  rw [hfac]
  have hA0 : 0 ≤ signalMinSingular (referenceFeature P t) :=
    (Matrix.toEuclideanLin (referenceFeature P t)).singularValues_nonneg _
  have hD0 : 0 ≤ signalMinSingular (latentArmWeights P t) :=
    (Matrix.toEuclideanLin (latentArmWeights P t)).singularValues_nonneg _
  have hB0 : 0 ≤ signalMinSingular (targetFeature P) :=
    (Matrix.toEuclideanLin (targetFeature P)).singularValues_nonneg _
  have hD := latentArmWeights_minSingular P hk hpi hM.latentArmPositivity t
  have hAD : sigma0 * pi0 ≤ signalMinSingular (referenceFeature P t) *
      signalMinSingular (latentArmWeights P t) :=
    mul_le_mul hAt hD hpi.le hA0
  calc
    pi0 * sigma0 ^ 2 = sigma0 * pi0 * sigma0 := by ring
    _ ≤ signalMinSingular (referenceFeature P t) *
          signalMinSingular (latentArmWeights P t) *
          signalMinSingular (targetFeature P) := by
      exact mul_le_mul hAD hM.proxyRankMargin.2.2 hsigma.le (mul_nonneg hA0 hD0)
    _ ≤ singularValue
        (referenceFeature P t * latentArmWeights P t * (targetFeature P).transpose)
        (k - 1) := by
      simpa only [signalMinSingular, singularValue, Fintype.card_fin] using hprod

/-- The matrix carried by a `SignalBasis` is the linear isometric embedding determined by
its orthonormal columns. -/
-- @node: signalBasisLinearIsometry
noncomputable def signalBasisLinearIsometry {dx k : ℕ} (V : SignalBasis dx k) :
    Euc k →ₗᵢ[ℝ] Euc dx := by
  refine LinearIsometry.mk (Matrix.toEuclideanLin V.V) ?_
  intro x
  have hgram : V.V.transpose * V.V = (1 : RectMatrix k k) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    exact V.orthonormal i j
  have hadj : (Matrix.toEuclideanLin V.V).adjoint =
      Matrix.toEuclideanLin V.V.transpose := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
  have hleft : (Matrix.toEuclideanLin V.V).adjoint
      (Matrix.toEuclideanLin V.V x) = x := by
    rw [hadj]
    apply PiLp.ext
    intro i
    simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
      ← Matrix.mul_apply, hgram, Matrix.one_apply, Matrix.one_mulVec]
  have hsq : ‖Matrix.toEuclideanLin V.V x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← (Matrix.toEuclideanLin V.V).adjoint_inner_left, hleft]
  nlinarith [norm_nonneg x, norm_nonneg (Matrix.toEuclideanLin V.V x)]

/-- Compression by any orthonormal basis spanning the stacked signal rowspace preserves the
last signal singular value and its quantitative lower margin. -/
-- @node: observedProxyMoment_compression_margin
lemma observedProxyMoment_compression_margin
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (t : Bool) (V : SignalBasis dx k) (hV : V.SpansSignal (obsSummary P)) :
    signalMinSingular (observedProxyMoment (obsSummary P) t * V.V) =
        singularValue (observedProxyMoment (obsSummary P) t) (k - 1) ∧
      pi0 * sigma0 ^ 2 ≤
        signalMinSingular (observedProxyMoment (obsSummary P) t * V.V) := by
  have hfac := observedProxyMoment_factorization P hk hkx hL hpi hM t
  have hmin := observedProxyMoment_minSingular_of_factorization
    P hk hpi hsigma hM t hfac
  let Vi := signalBasisLinearIsometry V
  let M := observedProxyMoment (obsSummary P) t
  have hAdj : Matrix.toEuclideanLin M.transpose =
      (Matrix.toEuclideanLin M).adjoint := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
  have hsub : (Matrix.toEuclideanLin M).adjoint.range ≤ Vi.toLinearMap.range := by
    rw [← hAdj]
    rw [show Vi.toLinearMap = Matrix.toEuclideanLin V.V from rfl, hV]
    cases t with
    | false => exact le_sup_left
    | true => exact le_sup_right
  have hpos : 0 < singularValue M (k - 1) :=
    lt_of_lt_of_le (mul_pos hpi (sq_pos_of_pos hsigma)) hmin
  have hrank : k ≤ Module.finrank ℝ (Matrix.toEuclideanLin M).adjoint.range := by
    rw [(Matrix.toEuclideanLin M).finrank_range_adjoint]
    have := (Matrix.toEuclideanLin M).singularValues_pos_iff_lt_finrank_range.mp hpos
    omega
  have hVirank : Module.finrank ℝ Vi.toLinearMap.range = k := by
    rw [Vi.toLinearMap.finrank_range_of_inj Vi.injective, finrank_euclideanSpace]
    simp
  have hrange : Vi.toLinearMap.range = (Matrix.toEuclideanLin M).adjoint.range := by
    symm
    apply Submodule.eq_of_le_of_finrank_le hsub
    rw [hVirank]
    exact hrank
  have hmul : Matrix.toEuclideanLin (M * V.V) =
      Matrix.toEuclideanLin M ∘ₗ Vi.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    simp [Vi, signalBasisLinearIsometry, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_mulVec]
  have heq := singularValues_comp_linearIsometry_last
    (Matrix.toEuclideanLin M) Vi hrange
  rw [← hmul] at heq
  refine ⟨by simpa [signalMinSingular, singularValue, M] using heq, ?_⟩
  simpa only [signalMinSingular, singularValue, Fintype.card_fin] using
    (show pi0 * sigma0 ^ 2 ≤ singularValue (M * V.V) (k - 1) by
      rw [show singularValue (M * V.V) (k - 1) = singularValue M (k - 1) by
        simpa [singularValue] using heq]
      exact hmin)

/-- Independence transfers an almost-sure product envelope to the second factor whenever the
first factor exceeds a positive threshold with positive probability. -/
-- @node: ae_abs_right_le_of_indep_product_bound
lemma ae_abs_right_le_of_indep_product_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hInd : IndepFun X Y μ) {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hEvent : 0 < μ {ω | a ≤ |X ω|})
    (hProduct : ∀ᵐ ω ∂μ, |X ω * Y ω| ≤ L) :
    ∀ᵐ ω ∂μ, |Y ω| ≤ L / a := by
  let E : Set Ω := {ω | a ≤ |X ω|}
  let B : Set Ω := {ω | L / a < |Y ω|}
  have hErange : MeasurableSet {x : ℝ | a ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hBrange : MeasurableSet {y : ℝ | L / a < |y|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hEBzero : μ (E ∩ B) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hProduct] with ω hprod hmem
    have hstrict : L < |X ω * Y ω| := by
      calc
        L = (L / a) * a := by field_simp
        _ < |Y ω| * a := mul_lt_mul_of_pos_right hmem.2 ha
        _ ≤ |Y ω| * |X ω| :=
          mul_le_mul_of_nonneg_left hmem.1 (abs_nonneg _)
        _ = |X ω * Y ω| := by rw [abs_mul]; ring
    exact (not_lt_of_ge hprod) hstrict
  have hfactor : μ (E ∩ B) = μ E * μ B := by
    simpa [E, B] using
      hInd.measure_inter_preimage_eq_mul
        {x : ℝ | a ≤ |x|} {y : ℝ | L / a < |y|} hErange hBrange
  have hBzero : μ B = 0 := by
    by_contra hB
    have hprodne : μ E * μ B ≠ 0 :=
      mul_ne_zero (ne_of_gt hEvent) hB
    exact hprodne (by rw [← hfactor, hEBzero])
  rw [measure_eq_zero_iff_ae_notMem] at hBzero
  filter_upwards [hBzero] with ω hω
  exact le_of_not_gt (by simpa [B] using hω)

/-- A bound holding on a positive-probability event transfers to an independent random variable
on the whole probability space. -/
-- @node: ae_abs_le_of_indep_positive_event
lemma ae_abs_le_of_indep_positive_event
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {A : Set Ω} (hA : MeasurableSet A)
    (hApos : 0 < μ A)
    (hInd : IndepFun X (armIndicator A) μ) {R : ℝ}
    (hBound : ∀ᵐ ω ∂μ, ω ∈ A → |X ω| ≤ R) :
    ∀ᵐ ω ∂μ, |X ω| ≤ R := by
  let B : Set Ω := {ω | R < |X ω|}
  have hBrange : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hBAzero : μ (B ∩ A) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hBound] with ω hω hmem
    exact (not_lt_of_ge (hω hmem.2)) hmem.1
  have hArmPreimage : armIndicator A ⁻¹' ({1} : Set ℝ) = A := by
    ext ω
    simp [armIndicator]
  have hfactor : μ (B ∩ A) = μ B * μ A := by
    simpa [B, hArmPreimage] using
      hInd.measure_inter_preimage_eq_mul
        {x : ℝ | R < |x|} ({1} : Set ℝ) hBrange (measurableSet_singleton 1)
  have hBzero : μ B = 0 := by
    by_contra hB
    have hprodne : μ B * μ A ≠ 0 :=
      mul_ne_zero hB (ne_of_gt hApos)
    exact hprodne (by rw [← hfactor, hBAzero])
  rw [measure_eq_zero_iff_ae_notMem] at hBzero
  filter_upwards [hBzero] with ω hω
  exact le_of_not_gt (by simpa [B] using hω)

/-- A reference-feature singular-value margin supplies a coordinate that is nontrivial with
positive probability in every normalized latent cell. -/
-- @node: exists_reference_coordinate_positive_event
lemma exists_reference_coordinate_positive_event
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) :
    ∃ j : Fin dz,
      0 < normalizedRestrict P (latentCell u t)
        {w | sigma0 / (2 * Real.sqrt dz) ≤ |w.Z j|} := by
  have hdz : 0 < dz := lt_of_lt_of_le (by omega : 0 < k) hkz
  have hsqrt : 0 < Real.sqrt dz := Real.sqrt_pos.2 (by positivity)
  have hAt : sigma0 ≤ signalMinSingular (referenceFeature P t) := by
    cases t with
    | false => exact hM.proxyRankMargin.1
    | true => exact hM.proxyRankMargin.2.1
  have hAinj : Function.Injective (Matrix.toEuclideanLin (referenceFeature P t)) := by
    rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hik : i ≤ k - 1 := by
      simpa using (Nat.le_sub_one_of_lt (by simpa using hi))
    exact lt_of_lt_of_le (lt_of_lt_of_le hsigma hAt)
      ((Matrix.toEuclideanLin (referenceFeature P t)).singularValues_antitone hik)
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let e : Euc k := WithLp.toLp 2 (Pi.single u 1)
  have he : ‖e‖ = 1 := by simp [e]
  have hcol : sigma0 ≤ ‖Matrix.toEuclideanLin (referenceFeature P t) e‖ := by
    calc
      sigma0 = sigma0 * ‖e‖ := by rw [he, mul_one]
      _ ≤ signalMinSingular (referenceFeature P t) * ‖e‖ :=
        mul_le_mul_of_nonneg_right hAt (norm_nonneg _)
      _ ≤ ‖Matrix.toEuclideanLin (referenceFeature P t) e‖ := by
        simpa [signalMinSingular, singularValue, Fintype.card_fin] using
          least_singularValue_mul_norm_le
            (Matrix.toEuclideanLin (referenceFeature P t)) hAinj e
  have hcoord : ∃ j : Fin dz,
      sigma0 / Real.sqrt dz ≤ |referenceFeature P t j u| := by
    by_contra hnone
    push_neg at hnone
    have hsquares : ∀ j : Fin dz,
        (referenceFeature P t j u) ^ 2 < sigma0 ^ 2 / dz := by
      intro j
      have hsq := (sq_lt_sq₀ (abs_nonneg (referenceFeature P t j u))
        (div_nonneg hsigma.le hsqrt.le)).2 (hnone j)
      rw [sq_abs] at hsq
      rw [div_pow] at hsq
      norm_num [Real.sq_sqrt hsqrt.le] at hsq ⊢
      exact hsq
    have hsum : (∑ j : Fin dz, (referenceFeature P t j u) ^ 2) < sigma0 ^ 2 := by
      calc
        _ < ∑ _j : Fin dz, sigma0 ^ 2 / dz :=
          Finset.sum_lt_sum (fun j _ => le_of_lt (hsquares j))
            ⟨⟨0, hdz⟩, Finset.mem_univ _, hsquares _⟩
        _ = sigma0 ^ 2 := by
          simp
          field_simp
    have hcolsq : sigma0 ^ 2 ≤
        ∑ j : Fin dz, (referenceFeature P t j u) ^ 2 := by
      have hs := (sq_le_sq₀ hsigma.le (norm_nonneg _)).2 hcol
      simp [EuclideanSpace.norm_eq, Matrix.toEuclideanLin_apply, e,
        Real.norm_eq_abs, sq_abs] at hs
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hs
    linarith
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨j, ?_⟩
  let C : Set (FullData k dx dz) := latentCell u t
  let μ := normalizedRestrict P C
  have hCpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  let _ : IsProbabilityMeasure μ :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentCell u t) hCpos
  have hb := (proxy_coordinate_bounds_of_model P hk hkx hM).2.1
  have hZint : Integrable (fun w : FullData k dx dz => w.Z j) μ := by
    exact Integrable.of_bound
      ((measurable_pi_apply j).comp measurable_fullData_Z).aestronglyMeasurable L <|
        (ae_normalizedRestrict_iff hCpos).mpr <|
          ae_restrict_of_ae (hb.mono fun w hw => by
            simpa [Real.norm_eq_abs] using hw j)
  by_contra hzero
  have hzero' : μ {w | sigma0 / (2 * Real.sqrt dz) ≤ |w.Z j|} = 0 :=
    le_antisymm (not_lt.mp hzero) bot_le
  have hae : ∀ᵐ w ∂μ, |w.Z j| < sigma0 / (2 * Real.sqrt dz) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero'] with w hw
    exact lt_of_not_ge (by simpa using hw)
  have hmean : |referenceFeature P t j u| ≤ sigma0 / (2 * Real.sqrt dz) := by
    rw [referenceFeature, conditionalMean_eq_normalizedRestrictedIntegral hCpos]
    unfold normalizedRestrictedIntegral
    calc
      |∫ w, w.Z j ∂μ| ≤ ∫ w, |w.Z j| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _w, sigma0 / (2 * Real.sqrt dz) ∂μ := by
        exact integral_mono_ae hZint.abs (integrable_const _) (hae.mono fun _ h => h.le)
      _ = sigma0 / (2 * Real.sqrt dz) := by simp
  have : sigma0 / (2 * Real.sqrt dz) < sigma0 / Real.sqrt dz := by
    calc
      sigma0 / (2 * Real.sqrt dz) = (sigma0 / Real.sqrt dz) / 2 := by field_simp
      _ < sigma0 / Real.sqrt dz := by
        have := div_pos hsigma hsqrt
        linarith
  exact (not_lt_of_ge hj) (lt_of_le_of_lt hmean this)

/-- Proxy separation, a reference-rank margin, the anchor, and the observable outcome--proxy
envelope bound the observed outcome on every latent treatment cell. -/
-- @node: ae_abs_observedOutcome_le_on_latentCell
lemma ae_abs_observedOutcome_le_on_latentCell
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) :
    ∀ᵐ w ∂P.restrict (latentCell u t),
      |w.Y| ≤ effectRadius dz L sigma0 / 2 := by
  let C : Set (FullData k dx dz) := latentCell u t
  let μ := normalizedRestrict P C
  have hCpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  let _ : IsProbabilityMeasure μ :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentCell u t) hCpos
  obtain ⟨j, hj⟩ :=
    exists_reference_coordinate_positive_event P hk hkx hkz hL hpi hsigma hM u t
  have hfac := referenceProxySeparation_to_normalizedFactorization
    hM.referenceProxySeparation u t hCpos
  have hXmeas : Measurable (fun w : FullData k dx dz => w.X) := measurable_fullData_X
  have hYmeas : Measurable (fun w : FullData k dx dz => w.Y) := measurable_fullData_Y
  have hIndVec : IndepFun (fun w : FullData k dx dz => w.Z) (fun w => (w.X, w.Y)) μ :=
    indepFun_of_boundedTestFactorization measurable_fullData_Z
      (hXmeas.prodMk hYmeas) hfac
  have hInd : IndepFun (fun w : FullData k dx dz => w.Z j) (fun w => w.Y) μ := by
    simpa only [Function.comp_def] using
      hIndVec.comp (measurable_pi_apply j) measurable_snd
  have hb := (proxy_coordinate_bounds_of_model P hk hkx hM).2.2
  have hprod : ∀ᵐ w ∂μ, |w.Z j * w.Y| ≤ L :=
    (ae_normalizedRestrict_iff hCpos).mpr <| ae_restrict_of_ae <|
      hb.mono fun w hw => by simpa [mul_comm] using hw j
  have hdzreal : (0 : ℝ) < dz := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) hkz)
  have ha : 0 < sigma0 / (2 * Real.sqrt dz) :=
    div_pos hsigma (mul_pos (by norm_num) (Real.sqrt_pos.2 hdzreal))
  have hL0 : 0 ≤ L := by linarith
  have hraw := ae_abs_right_le_of_indep_product_bound
    ((measurable_pi_apply j).comp measurable_fullData_Z) hYmeas
    hInd (a := sigma0 / (2 * Real.sqrt dz)) (L := L) ha hL0
    hj hprod
  apply (ae_normalizedRestrict_iff hCpos).mp
  filter_upwards [hraw] with w hw
  rw [effectRadius]
  have hsqrt : 0 < Real.sqrt dz := Real.sqrt_pos.2 (by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) hkz))
  calc
    |w.Y| ≤ L / (sigma0 / (2 * Real.sqrt dz)) := hw
    _ = (4 * L * Real.sqrt dz / sigma0) / 2 := by field_simp; ring

/-- Consistency and armwise latent ignorability transfer the observed cell envelope to each
potential outcome on the whole latent class. -/
-- @node: ae_abs_potential_le_on_latentClass
lemma ae_abs_potential_le_on_latentClass
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) :
    ∀ᵐ w ∂P.restrict (latentClass u),
      |potential t w| ≤ effectRadius dz L sigma0 / 2 := by
  let C : Set (FullData k dx dz) := latentClass u
  let A : Set (FullData k dx dz) := {w | w.T = t}
  let μ := normalizedRestrict P C
  have hcellpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  have hCpos : 0 < P C := lt_of_lt_of_le hcellpos <| measure_mono <| by
    intro w hw
    exact hw.1
  let _ : IsProbabilityMeasure μ :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hCpos
  have hfac := latentIgnorability_to_normalizedFactorization
    hM.latentIgnorability u t hCpos
  have hIndT : IndepFun (potential t) (fun w : FullData k dx dz => w.T) μ :=
    indepFun_of_boundedTestFactorization (measurable_potential t) measurable_fullData_T hfac
  let q : Bool → ℝ := fun b => if b = t then 1 else 0
  have hq : Measurable q := by fun_prop
  have hInd : IndepFun (potential t) (armIndicator A) μ := by
    have hc := hIndT.comp measurable_id hq
    have heq : (q ∘ fun w : FullData k dx dz => w.T) = armIndicator A := by
      funext w
      by_cases hw : w.T = t <;> simp [q, A, armIndicator, hw]
    rw [← heq]
    exact hc
  have hApos : 0 < μ A := by
    rw [normalizedRestrict_apply hCpos (measurableSet_fullDataArm t)]
    have hinter : A ∩ C = latentCell u t := by
      ext w
      simp [A, C, latentCell, latentClass, and_comm]
    rw [hinter]
    exact ENNReal.mul_pos (ENNReal.inv_pos.mpr (measure_ne_top P C)).ne' hcellpos.ne'
  have hobs := ae_abs_observedOutcome_le_on_latentCell
    P hk hkx hkz hL hpi hsigma hM u t
  have hOnArm : ∀ᵐ w ∂μ, w ∈ A →
      |potential t w| ≤ effectRadius dz L sigma0 / 2 := by
    apply (ae_normalizedRestrict_iff hCpos).mpr
    filter_upwards [ae_restrict_of_ae hM.consistency,
      ae_restrict_of_ae (ae_imp_of_ae_restrict hobs),
      self_mem_ae_restrict (measurableSet_latentClass u)] with w hcons hbound hwC hwA
    have hwcell : w ∈ latentCell u t :=
      ⟨by simpa [C, latentClass] using hwC, by simpa [A] using hwA⟩
    have ht : w.T = t := by simpa [A] using hwA
    rw [← ht, ← hcons]
    exact hbound hwcell
  exact (ae_normalizedRestrict_iff hCpos).mp <|
    ae_abs_le_of_indep_positive_event (measurable_potential t)
      (measurableSet_fullDataArm t) hApos hInd hOnArm

/-- The derived potential-outcome envelope bounds every latent conditional mean. -/
lemma latentMean_abs_le_of_model
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) :
    |latentMean P t u| ≤ effectRadius dz L sigma0 / 2 := by
  have hcell := latentCell_pos_of_latentArmPositivity
    P hpi hM.latentArmPositivity u false
  have hclass : 0 < P (latentClass u) := lt_of_lt_of_le hcell <| measure_mono <| by
    intro w hw
    exact hw.1
  let mu := normalizedRestrict P (latentClass u)
  let _ : IsProbabilityMeasure mu :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hclass
  have hpot := ae_abs_potential_le_on_latentClass
    P hk hkx hkz hL hpi hsigma hM u t
  have hpotmu : ∀ᵐ w ∂mu, |potential t w| ≤ effectRadius dz L sigma0 / 2 :=
    (ae_normalizedRestrict_iff hclass).mpr hpot
  have hint : Integrable (potential t) mu :=
    Integrable.of_bound (measurable_potential t).aestronglyMeasurable
      (effectRadius dz L sigma0 / 2) hpotmu
  rw [latentMean, conditionalMean_eq_normalizedRestrictedIntegral hclass]
  unfold normalizedRestrictedIntegral
  calc
    |∫ w, potential t w ∂mu| ≤ ∫ w, |potential t w| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _w, effectRadius dz L sigma0 / 2 ∂mu :=
      integral_mono_ae hint.abs (integrable_const _) hpotmu
    _ = effectRadius dz L sigma0 / 2 := by simp

/-- The two derived latent-mean bounds imply the gap-free support bound for every latent effect. -/
lemma latentEffect_abs_le_of_model
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) : |latentEffect P u| ≤ effectRadius dz L sigma0 := by
  rw [latentEffect]
  calc
    |latentMean P true u - latentMean P false u| ≤
        |latentMean P true u| + |latentMean P false u| := abs_sub _ _
    _ ≤ effectRadius dz L sigma0 / 2 + effectRadius dz L sigma0 / 2 :=
      add_le_add (latentMean_abs_le_of_model P hk hkx hkz hL hpi hsigma hM u true)
        (latentMean_abs_le_of_model P hk hkx hkz hL hpi hsigma hM u false)
    _ = effectRadius dz L sigma0 := by ring

/-- The operator norm of a conditional matrix mean is bounded by an almost-sure operator
envelope for the matrix-valued random element. -/
-- @node: conditionalMatrix_norm_le_of_ae_bound
lemma conditionalMatrix_norm_le_of_ae_bound
    {k dx dz : ℕ} (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (t : Bool) (A : FullData k dx dz → RectMatrix dz dx)
    (hcoordMeas : ∀ i j, Measurable (fun w => A w i j))
    (hmapMeas : Measurable (fun w => matrixCLM (A w)))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ w ∂P, ‖matrixCLM (A w)‖ ≤ L)
    (hArm : 0 < P {w | w.T = t}) :
    ‖matrixCLM (fun i j => conditionalMean P {w | w.T = t} (fun w => A w i j))‖ ≤ L := by
  let C : Set (FullData k dx dz) := {w | w.T = t}
  let μ := normalizedRestrict P C
  let _ : IsProbabilityMeasure μ :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_fullDataArm t) hArm
  have hboundμ : ∀ᵐ w ∂μ, ‖matrixCLM (A w)‖ ≤ L :=
    (ae_normalizedRestrict_iff hArm).mpr (ae_restrict_of_ae hbound)
  have hmap : Integrable (fun w => matrixCLM (A w)) μ :=
    Integrable.of_bound hmapMeas.aestronglyMeasurable L hboundμ
  have hcoord : ∀ i j, Integrable (fun w => A w i j) μ := by
    intro i j
    exact Integrable.of_bound
      (hcoordMeas i j).aestronglyMeasurable
      L <| hboundμ.mono fun w hw => by
        simpa [Real.norm_eq_abs] using
          (abs_matrix_entry_le_matrixCLM_norm (A w) i j).trans hw
  rw [matrixCLM_conditionalMatrix_eq_integral P C hArm A hcoord hmap]
  calc
    ‖∫ w, matrixCLM (A w) ∂μ‖ ≤ ∫ w, ‖matrixCLM (A w)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _w, L ∂μ :=
      integral_mono_ae hmap.norm (integrable_const _) hboundμ
    _ = L := by simp

/-- All five observable summary blocks inherit the common model envelope. -/
-- @node: observedSummary_envelopes_of_model
lemma observedSummary_envelopes_of_model
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    (∀ t : Bool, ‖matrixCLM (observedProxyMoment (obsSummary P) t)‖ ≤ L ∧
      ‖matrixCLM (observedOutcomeProxyMoment (obsSummary P) t)‖ ≤ L) ∧
      ‖(WithLp.toLp 2 (obsSummary P).mX : Euc dx)‖ ≤ L := by
  have hL0 : 0 ≤ L := by linarith
  have harm (t : Bool) : 0 < P {w : FullData k dx dz | w.T = t} :=
    fullDataArm_pos_of_latentArmPositivity P (by omega) hpi hM.latentArmPositivity t
  have hOuterCoordMeas (i : Fin dz) (j : Fin dx) :
      Measurable (fun w : FullData k dx dz => outerProduct w.Z w.X i j) :=
    ((measurable_pi_apply i).comp measurable_fullData_Z).mul
      ((measurable_pi_apply j).comp measurable_fullData_X)
  have hZlp : Measurable (fun w : FullData k dx dz => (WithLp.toLp 2 w.Z : Euc dz)) :=
    (WithLp.measurable_toLp 2 (Fin dz → ℝ)).comp measurable_fullData_Z
  have hXlp : Measurable (fun w : FullData k dx dz => (WithLp.toLp 2 w.X : Euc dx)) :=
    (WithLp.measurable_toLp 2 (Fin dx → ℝ)).comp measurable_fullData_X
  have hOuterCont : Continuous (fun p : Euc dz × Euc dx =>
      matrixCLM (fun i j => p.1 i * p.2 j)) := by
    apply matrixCLM_continuous.comp
    fun_prop
  have hOuterMapMeas : Measurable
      (fun w : FullData k dx dz => matrixCLM (outerProduct w.Z w.X)) := by
    convert hOuterCont.measurable.comp (hZlp.prodMk hXlp) using 1
    funext w
    rfl
  have hYOuterCoordMeas (i : Fin dz) (j : Fin dx) : Measurable
      (fun w : FullData k dx dz => (w.Y • outerProduct w.Z w.X) i j) :=
    by
      change Measurable (fun w : FullData k dx dz => w.Y * (w.Z i * w.X j))
      exact measurable_fullData_Y.mul
        (((measurable_pi_apply i).comp measurable_fullData_Z).mul
          ((measurable_pi_apply j).comp measurable_fullData_X))
  have hYOuterMapMeas : Measurable
      (fun w : FullData k dx dz => matrixCLM (w.Y • outerProduct w.Z w.X)) := by
    have heq : (fun w : FullData k dx dz => matrixCLM (w.Y • outerProduct w.Z w.X)) =
        fun w => w.Y • matrixCLM (outerProduct w.Z w.X) := by
      funext w
      ext x i
      simp [matrixCLM, Matrix.toEuclideanLin_apply, outerProduct, Finset.mul_sum]
    rw [heq]
    exact measurable_fullData_Y.smul hOuterMapMeas
  have hMfull (t : Bool) :
      ‖matrixCLM (fun i j => conditionalMean P {w | w.T = t}
        (fun w => outerProduct w.Z w.X i j))‖ ≤ L :=
    conditionalMatrix_norm_le_of_ae_bound P t _ hOuterCoordMeas hOuterMapMeas hL0
      hM.boundedProxyProduct (harm t)
  have hNfull (t : Bool) :
      ‖matrixCLM (fun i j => conditionalMean P {w | w.T = t}
        (fun w => (w.Y • outerProduct w.Z w.X) i j))‖ ≤ L :=
    conditionalMatrix_norm_le_of_ae_bound P t _ hYOuterCoordMeas hYOuterMapMeas hL0
      hM.boundedOutcomeProxyProduct (harm t)
  have hMobs (t : Bool) : observedProxyMoment (obsSummary P) t =
      fun i j => conditionalMean P {w | w.T = t} (fun w => outerProduct w.Z w.X i j) := by
    ext i j
    have ht := conditionalMean_obsArm_eq_fullDataArm P t
      (fun o : Obs dx dz => o.Z i * o.X j)
      (((measurable_pi_apply i).comp measurable_obs_Z).mul
        ((measurable_pi_apply j).comp measurable_obs_X))
    cases t <;>
      simpa [observedProxyMoment, obsSummary, obsMap, outerProduct, Function.comp_def] using ht
  have hNobs (t : Bool) : observedOutcomeProxyMoment (obsSummary P) t =
      fun i j => conditionalMean P {w | w.T = t}
        (fun w => (w.Y • outerProduct w.Z w.X) i j) := by
    ext i j
    have ht := conditionalMean_obsArm_eq_fullDataArm P t
      (fun o : Obs dx dz => o.Y * o.Z i * o.X j)
      ((measurable_obs_Y.mul ((measurable_pi_apply i).comp measurable_obs_Z)).mul
        ((measurable_pi_apply j).comp measurable_obs_X))
    cases t <;>
      simpa [observedOutcomeProxyMoment, obsSummary, obsMap, outerProduct,
        Function.comp_def, mul_assoc] using ht
  have hXMeas : Measurable (fun w : FullData k dx dz =>
      (WithLp.toLp 2 w.X : Euc dx)) := by
    exact hXlp
  have hXint : Integrable (fun w : FullData k dx dz =>
      (WithLp.toLp 2 w.X : Euc dx)) P := by
    apply Integrable.of_bound hXMeas.aestronglyMeasurable L
    simpa only [BoundedTargetProxy, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
      using hM.boundedX
  have hmEq : (WithLp.toLp 2 (obsSummary P).mX : Euc dx) =
      ∫ w, (WithLp.toLp 2 w.X : Euc dx) ∂P := by
    apply PiLp.ext
    intro j
    rw [eval_integral_piLp (fun i => hXint.eval_piLp i) j]
    change (∫ o, o.X j ∂obsLaw P) = ∫ w, w.X j ∂P
    rw [obsLaw]
    exact integral_map (obsMap_measurable k dx dz).aemeasurable
      (((measurable_pi_apply j).comp measurable_obs_X).aestronglyMeasurable)
  refine ⟨fun t => ⟨?_, ?_⟩, ?_⟩
  · rw [hMobs t]
    exact hMfull t
  · rw [hNobs t]
    exact hNfull t
  · rw [hmEq]
    calc
      ‖∫ w, (WithLp.toLp 2 w.X : Euc dx) ∂P‖ ≤
          ∫ w, ‖(WithLp.toLp 2 w.X : Euc dx)‖ ∂P :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _w, L ∂P := by
        apply integral_mono_ae hXint.norm (integrable_const _)
        filter_upwards [hM.boundedX] with w hw
        simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hw
      _ = L := by simp

/-- The Euclidean norm of either arm block is at most the norm of the vertically stacked
proxy-moment operator. -/
-- @node: observedProxyMoment_norm_le_stackedProxyMoment
lemma observedProxyMoment_norm_le_stackedProxyMoment
    {dx dz : ℕ} (s : SummarySpace dx dz) (x : Euc dx) (t : Bool) :
    ‖Matrix.toEuclideanLin (observedProxyMoment s t) x‖ ≤
      ‖Matrix.toEuclideanLin (stackedProxyMoment s) x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have hsplit : (∑ i : Fin (2 * dz),
      ((Matrix.toEuclideanLin (stackedProxyMoment s) x) i) ^ 2) =
      (∑ i : Fin dz, ((Matrix.toEuclideanLin (observedProxyMoment s false) x) i) ^ 2) +
      ∑ i : Fin dz, ((Matrix.toEuclideanLin (observedProxyMoment s true) x) i) ^ 2 := by
    let e : (Fin dz ⊕ Fin dz) ≃ Fin (2 * dz) :=
      finSumFinEquiv.trans (finCongr (two_mul dz).symm)
    rw [← Equiv.sum_comp e]
    rw [Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      have hi : e (Sum.inl i) = ⟨i.val, by omega⟩ := by
        apply Fin.ext
        simp [e]
      rw [hi]
      change (∑ j, (if h : i.val < dz then s.M0 ⟨i.val, h⟩ j
        else s.M1 ⟨i.val - dz, by omega⟩ j) * x j) = ∑ j, s.M0 i j * x j
      simp [i.isLt]
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      have hi : e (Sum.inr i) = ⟨i.val + dz, by omega⟩ := by
        apply Fin.ext
        simp [e]
      rw [hi]
      change (∑ j, (if h : i.val + dz < dz then s.M0 ⟨i.val + dz, h⟩ j
        else s.M1 ⟨i.val + dz - dz, by omega⟩ j) * x j) = ∑ j, s.M1 i j * x j
      simp
  simp only [Real.norm_eq_abs, sq_abs]
  rw [hsplit]
  cases t
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The vertically stacked proxy moment retains the common quantitative signal margin. -/
-- @node: stackedProxyMoment_minSingular
lemma stackedProxyMoment_minSingular
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    pi0 * sigma0 ^ 2 ≤ singularValue (stackedProxyMoment (obsSummary P)) (k - 1) := by
  let A := Matrix.toEuclideanLin (referenceFeature P false)
  let D := Matrix.toEuclideanLin (latentArmWeights P false)
  let B := Matrix.toEuclideanLin (targetFeature P)
  let S := B.range
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have injective_of_margin {rows : ℕ} (G : RectMatrix rows k)
      (hG : sigma0 ≤ signalMinSingular G) :
      Function.Injective (Matrix.toEuclideanLin G) := by
    rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hik : i ≤ k - 1 := by
      simpa using (Nat.le_sub_one_of_lt (by simpa using hi))
    exact lt_of_lt_of_le (lt_of_lt_of_le hsigma hG)
      ((Matrix.toEuclideanLin G).singularValues_antitone hik)
  have hAinj := injective_of_margin (referenceFeature P false) hM.proxyRankMargin.1
  have hBinj := injective_of_margin (targetFeature P) hM.proxyRankMargin.2.2
  have hDinj := latentArmWeights_injective P hpi hM.latentArmPositivity false
  apply le_singularValues_of_subspace
    (Matrix.toEuclideanLin (stackedProxyMoment (obsSummary P))) S
      (mul_nonneg hpi.le (sq_nonneg sigma0))
  · dsimp [S]
    rw [B.finrank_range_of_inj hBinj, finrank_euclideanSpace]
    simp
    omega
  · intro x hx
    have hBexp : sigma0 * ‖x‖ ≤ ‖B.adjoint x‖ := by
      calc
        sigma0 * ‖x‖ ≤ B.singularValues (k - 1) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hM.proxyRankMargin.2.2 (norm_nonneg _)
        _ ≤ ‖B.adjoint x‖ := by
          simpa [B, S, Fintype.card_fin] using
            least_singularValue_mul_norm_le_adjoint_on_range B hBinj x hx
    have hDmargin := latentArmWeights_minSingular P hk hpi hM.latentArmPositivity false
    have hDexp : pi0 * ‖B.adjoint x‖ ≤ ‖D (B.adjoint x)‖ := by
      calc
        pi0 * ‖B.adjoint x‖ ≤ D.singularValues (k - 1) * ‖B.adjoint x‖ :=
          mul_le_mul_of_nonneg_right hDmargin (norm_nonneg _)
        _ ≤ ‖D (B.adjoint x)‖ := by
          simpa [D, Fintype.card_fin] using
            least_singularValue_mul_norm_le D hDinj (B.adjoint x)
    have hAexp : sigma0 * ‖D (B.adjoint x)‖ ≤ ‖A (D (B.adjoint x))‖ := by
      calc
        sigma0 * ‖D (B.adjoint x)‖ ≤ A.singularValues (k - 1) * ‖D (B.adjoint x)‖ :=
          mul_le_mul_of_nonneg_right hM.proxyRankMargin.1 (norm_nonneg _)
        _ ≤ ‖A (D (B.adjoint x))‖ := by
          simpa [A, Fintype.card_fin] using
            least_singularValue_mul_norm_le A hAinj (D (B.adjoint x))
    have hchain : pi0 * sigma0 ^ 2 * ‖x‖ ≤ ‖A (D (B.adjoint x))‖ := by
      calc
        pi0 * sigma0 ^ 2 * ‖x‖ = sigma0 * pi0 * (sigma0 * ‖x‖) := by ring
        _ ≤ sigma0 * pi0 * ‖B.adjoint x‖ :=
          mul_le_mul_of_nonneg_left hBexp (mul_nonneg hsigma.le hpi.le)
        _ = sigma0 * (pi0 * ‖B.adjoint x‖) := by ring
        _ ≤ sigma0 * ‖D (B.adjoint x)‖ :=
          mul_le_mul_of_nonneg_left hDexp hsigma.le
        _ ≤ ‖A (D (B.adjoint x))‖ := hAexp
    have hAdj : B.adjoint = Matrix.toEuclideanLin (targetFeature P).transpose := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      rfl
    have hfac := observedProxyMoment_factorization P hk hkx hL hpi hM false
    calc
      pi0 * sigma0 ^ 2 * ‖x‖ ≤ ‖A (D (B.adjoint x))‖ := hchain
      _ = ‖Matrix.toEuclideanLin (observedProxyMoment (obsSummary P) false) x‖ := by
        rw [hfac, hAdj]
        simp [A, D, B, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
      _ ≤ ‖Matrix.toEuclideanLin (stackedProxyMoment (obsSummary P)) x‖ :=
        observedProxyMoment_norm_le_stackedProxyMoment (obsSummary P) x false

/-- Uniform observed-moment and latent-outcome consequences of model membership, together with
the conditional cited-scope transfer to the published VMW model. -/
-- @node: prop:observed-vmw-margin-inclusion
theorem observed_vmw_margin_inclusion {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (publishedScope : PublishedVMWScopeHandle)
    (publishedMargins : PublishedVMWMarginRecord)
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hVMWModelScope_of_gate : VMWModelScope publishedScope publishedMargins) :
    (∀ t : Bool, k * pi0 ≤ P.real {w | w.T = t} ∧
      observedProxyMoment (obsSummary P) t =
        referenceFeature P t * latentArmWeights P t * (targetFeature P).transpose ∧
      ∀ V : SignalBasis dx k, V.SpansSignal (obsSummary P) →
        signalMinSingular (observedProxyMoment (obsSummary P) t * V.V) =
          singularValue (observedProxyMoment (obsSummary P) t) (k - 1) ∧
        pi0 * sigma0 ^ 2 ≤
          signalMinSingular (observedProxyMoment (obsSummary P) t * V.V)) ∧
    pi0 * sigma0 ^ 2 ≤ singularValue (stackedProxyMoment (obsSummary P)) (k - 1) ∧
    (∀ t : Bool, ‖matrixCLM (if t then (obsSummary P).M1 else (obsSummary P).M0)‖ ≤ L ∧
      ‖matrixCLM (if t then (obsSummary P).N1 else (obsSummary P).N0)‖ ≤ L) ∧
    ‖(WithLp.toLp 2 (obsSummary P).mX : Euc dx)‖ ≤ L ∧
    (∀ u : Fin k, ∀ t : Bool,
      (∀ᵐ w ∂P.restrict (latentClass u), |potential t w| ≤ effectRadius dz L sigma0 / 2) ∧
      |latentMean P t u| ≤ effectRadius dz L sigma0 / 2 ∧
      |latentEffect P u| ≤ effectRadius dz L sigma0) ∧
    PublishedVMWModel publishedScope P := by
  have hEnv := observedSummary_envelopes_of_model P hk hkx hL hpi hM
  have hMean (u : Fin k) (t : Bool) :
      |latentMean P t u| ≤ effectRadius dz L sigma0 / 2 := by
    exact latentMean_abs_le_of_model P hk hkx hkz hL hpi hsigma hM u t
  refine ⟨?_, stackedProxyMoment_minSingular P hk hkx hL hpi hsigma hM,
    ?_, hEnv.2, ?_, ?_⟩
  · intro t
    refine ⟨arm_mass_lower_of_latentArmPositivity P hM.latentArmPositivity t,
      observedProxyMoment_factorization P hk hkx hL hpi hM t, ?_⟩
    intro V hV
    exact observedProxyMoment_compression_margin P hk hkx hL hpi hsigma hM t V hV
  · intro t
    cases t with
    | false =>
        simpa [observedProxyMoment, observedOutcomeProxyMoment] using hEnv.1 false
    | true =>
        simpa [observedProxyMoment, observedOutcomeProxyMoment] using hEnv.1 true
  · intro u t
    refine ⟨ae_abs_potential_le_on_latentClass
      P hk hkx hkz hL hpi hsigma hM u t, hMean u t, ?_⟩
    exact latentEffect_abs_le_of_model P hk hkx hkz hL hpi hsigma hM u
  · exact (hVMWModelScope_of_gate.2 k dx dz P inferInstance).2
      (ucvmwModel_publishedQualitativeConditions k dx dz L pi0 sigma0 P
        ⟨hk, hkx, hkz, hL, hpi, hpiMax, hsigma, hsigmaMax⟩ hM)

/-- The five observable blocks of a model-generated summary obey the common envelope. -/
-- @node: observed_summary_block_bounds
lemma observed_summary_block_bounds {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ‖matrixCLM (obsSummary P).M0‖ ≤ L ∧
      ‖matrixCLM (obsSummary P).M1‖ ≤ L ∧
      ‖matrixCLM (obsSummary P).N0‖ ≤ L ∧
      ‖matrixCLM (obsSummary P).N1‖ ≤ L ∧
      ‖(obsSummary P).mX‖ ≤ L := by
  have h := observedSummary_envelopes_of_model P hk hkx hL hpi hM
  have hmX : ‖(obsSummary P).mX‖ ≤ L := by
    rw [pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ L)]
    intro i
    have hi := PiLp.norm_apply_le (WithLp.toLp 2 (obsSummary P).mX : Euc dx) i
    simpa only [Real.norm_eq_abs] using hi.trans h.2
  exact ⟨by simpa [observedProxyMoment] using (h.1 false).1,
    by simpa [observedProxyMoment] using (h.1 true).1,
    by simpa [observedOutcomeProxyMoment] using (h.1 false).2,
    by simpa [observedOutcomeProxyMoment] using (h.1 true).2, hmX⟩

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
