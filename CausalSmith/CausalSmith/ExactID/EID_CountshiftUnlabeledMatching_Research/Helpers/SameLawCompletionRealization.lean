module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.MomentBridge
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.CompatibleModelRealization

/-! Gaussian and covariance infrastructure for same-law structural completions. -/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
noncomputable section
variable {p : ℕ}
namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: multivariateGaussian_matrix_image_hasLaw
lemma multivariateGaussian_matrix_image_hasLaw (C S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef) :
    HasLaw (fun x : EuclideanSpace ℝ (Fin p) =>
      WithLp.toLp 2 (C *ᵥ WithLp.ofLp x))
      (multivariateGaussian 0 (C * S * C.transpose))
      (multivariateGaussian 0 S) := by
  let L := (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun C
  have hL : (fun x : EuclideanSpace ℝ (Fin p) =>
      WithLp.toLp 2 (C *ᵥ WithLp.ofLp x)) = L := rfl
  rw [hL]
  refine ⟨(by fun_prop), ?_⟩
  haveI : _root_.ProbabilityTheory.IsGaussian ((multivariateGaussian 0 S).map L) := inferInstance
  apply ProbabilityTheory.IsGaussian.ext
  · rw [integral_map (by fun_prop) IsGaussian.integrable_id.aestronglyMeasurable]
    calc
      (∫ x, L x ∂multivariateGaussian 0 S) =
          L (∫ x, x ∂multivariateGaussian 0 S) :=
        L.integral_comp_comm IsGaussian.integrable_id
      _ = 0 := by simp
      _ = ∫ x, id x ∂multivariateGaussian 0 (C * S * C.transpose) := by simp
  · have hop : L.adjoint =
        (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun C.transpose := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      change star ((Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun C) = _
      calc
        star ((Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun C) =
            (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun (star C) :=
          (map_star (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)) C).symm
        _ = _ := by congr 2
    have hadj (u : EuclideanSpace ℝ (Fin p)) :
        L.adjoint u = WithLp.toLp 2 (C.transpose *ᵥ WithLp.ofLp u) := by
      rw [hop]
      rfl
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian]
    · rw [hadj, hadj]
      simp only [WithLp.ofLp_toLp]
      rw [Matrix.mulVec_transpose]
      nth_rewrite 1 [dotProduct_mulVec]
      rw [Matrix.vecMul_vecMul]
      rw [dotProduct_mulVec, Matrix.vecMul_vecMul]
      exact (Matrix.dotProduct_mulVec (WithLp.ofLp u) (C * S * C.transpose) (WithLp.ofLp v)).symm
    · exact hS.mul_mul_conjTranspose_same (B := C)


-- @node: obsCov_eq_structural_covariance
lemma obsCov_eq_structural_covariance {M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝔐 : AtomicCountModel p M Ω μ) (m : Fin (M + 1)) :
    Matrix.of (obsCov μ 𝔐 m) =
      totalEffect 𝔐.A * 𝔐.Ωc m * (totalEffect 𝔐.A).transpose := by
  letI : IsProbabilityMeasure μ := (𝔐.gaussian m).2.isProbabilityMeasure
  let B := totalEffect 𝔐.A
  have hbridge := (observable_moment_bridge μ 𝔐).2.1 m
  have hmean := (observable_moment_bridge μ 𝔐).1 m
  have hstruct := obsMean_eq_structural_mean μ 𝔐 m
  have hξlaw := (𝔐.gaussian m).2
  have hYlaw0 := multivariateGaussian_matrix_image_hasLaw B (𝔐.Ωc m) (𝔐.gaussian m).1.posSemidef
  have hYlaw : HasLaw (fun ω => WithLp.toLp 2 (B *ᵥ 𝔐.ξ m ω))
      (multivariateGaussian 0 (B * 𝔐.Ωc m * B.transpose)) μ := by
    exact hYlaw0.comp hξlaw
  ext j k
  simp only [Matrix.of_apply]
  rw [hbridge]
  have hcenter (ω : Ω) (i : Fin p) :
      latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i -
          (∫ ω', latentState 𝔐.A 𝔐.η 𝔐.ξ m ω' i ∂μ) =
        (B *ᵥ 𝔐.ξ m ω) i := by
    rw [← hmean i, hstruct]
    simp only [latentState, B]
    rw [show (fun a => 𝔐.η m a + 𝔐.ξ m ω a) = 𝔐.η m + 𝔐.ξ m ω from rfl,
      Matrix.mulVec_add]
    simp
  simp_rw [hcenter]
  have hYmean (i : Fin p) : ∫ ω, (B *ᵥ 𝔐.ξ m ω) i ∂μ = 0 := by
    have hm := hYlaw.integral_comp
      (f := fun y : EuclideanSpace ℝ (Fin p) => WithLp.ofLp y i)
      (by fun_prop)
    rw [show (fun y : EuclideanSpace ℝ (Fin p) => WithLp.ofLp y i) =
      EuclideanSpace.proj (𝕜 := ℝ) i by rfl] at hm
    change (∫ ω, (B *ᵥ 𝔐.ξ m ω) i ∂μ) =
      ∫ y, WithLp.ofLp y i ∂multivariateGaussian 0
        (B * 𝔐.Ωc m * B.transpose) at hm
    calc
      (∫ ω, (B *ᵥ 𝔐.ξ m ω) i ∂μ) =
          ∫ y, WithLp.ofLp y i
            ∂multivariateGaussian 0 (B * 𝔐.Ωc m * B.transpose) := hm
      _ = (EuclideanSpace.proj (𝕜 := ℝ) i)
          (∫ y, y ∂multivariateGaussian 0 (B * 𝔐.Ωc m * B.transpose)) := by
        change (∫ y, (EuclideanSpace.proj (𝕜 := ℝ) i) y
            ∂multivariateGaussian 0 (B * 𝔐.Ωc m * B.transpose)) = _
        exact (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
          IsGaussian.integrable_id
      _ = 0 := by simp
  have hcov := hYlaw.covariance_fun_comp
    (f := fun y : EuclideanSpace ℝ (Fin p) => WithLp.ofLp y j)
    (g := fun y : EuclideanSpace ℝ (Fin p) => WithLp.ofLp y k)
    (by fun_prop) (by fun_prop)
  simp only [Function.comp_apply, WithLp.ofLp_toLp] at hcov
  calc
    (∫ ω, (B *ᵥ 𝔐.ξ m ω) j * (B *ᵥ 𝔐.ξ m ω) k ∂μ) =
        covariance (fun ω => (B *ᵥ 𝔐.ξ m ω) j)
          (fun ω => (B *ᵥ 𝔐.ξ m ω) k) μ := by
      simp [covariance, hYmean]
    _ = covariance (fun y : EuclideanSpace ℝ (Fin p) => WithLp.ofLp y j)
          (fun y : EuclideanSpace ℝ (Fin p) => WithLp.ofLp y k)
          (multivariateGaussian 0 (B * 𝔐.Ωc m * B.transpose)) := hcov
    _ = (B * 𝔐.Ωc m * B.transpose) j k := by
      rw [covariance_eval_multivariateGaussian]
      exact (𝔐.gaussian m).1.posSemidef.mul_mul_conjTranspose_same (B := B)
    _ = _ := rfl


-- @node: sameLawCompletion_gaussian
lemma sameLawCompletion_gaussian {p M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝔐 : AtomicCountModel p M Ω μ)
    (B' : Matrix (Fin p) (Fin p) ℝ) (hunit' : IsUnit B'.det) :
    GaussianDisturbance μ
      (fun m => B'⁻¹ * Matrix.of (obsCov μ 𝔐 m) * (B'⁻¹).transpose)
      (fun m ω => B'⁻¹ *ᵥ (fun i =>
        latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i - obsMean μ 𝔐 m i)) := by
  intro m
  let B := totalEffect 𝔐.A
  let C := B'⁻¹ * B
  have hunitB : IsUnit B.det := acyclic_unit_matrix_invertible B
    (acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic)
    (acyclic_mechanism_totalEffect_acyclic 𝔐.A 𝔐.acyclic)
  have hunitBmat : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr hunitB
  have hunitB'mat : IsUnit B' := (Matrix.isUnit_iff_isUnit_det B').mpr hunit'
  have hunitCmat : IsUnit C := by
    exact (isUnit_nonsing_inv_iff.mpr hunitB'mat).mul hunitBmat
  have hunitC : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hunitCmat
  have hcov := obsCov_eq_structural_covariance μ 𝔐 m
  have hΩ : B'⁻¹ * Matrix.of (obsCov μ 𝔐 m) * (B'⁻¹).transpose =
      C * 𝔐.Ωc m * C.transpose := by
    rw [hcov]
    simp only [C, B, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  change (B'⁻¹ * Matrix.of (obsCov μ 𝔐 m) * (B'⁻¹).transpose).PosDef ∧
    HasLaw (fun ω => WithLp.toLp 2 (B'⁻¹ *ᵥ (fun i =>
      latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i - obsMean μ 𝔐 m i)))
      (multivariateGaussian 0
        (B'⁻¹ * Matrix.of (obsCov μ 𝔐 m) * (B'⁻¹).transpose)) μ
  rw [hΩ]
  constructor
  · exact (𝔐.gaussian m).1.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr hunitCmat)
  · have hlaw0 := multivariateGaussian_matrix_image_hasLaw C (𝔐.Ωc m)
      (𝔐.gaussian m).1.posSemidef
    have hlaw : HasLaw (fun ω => WithLp.toLp 2 (C *ᵥ 𝔐.ξ m ω))
        (multivariateGaussian 0 (C * 𝔐.Ωc m * C.transpose)) μ :=
      hlaw0.comp (𝔐.gaussian m).2
    apply hlaw.congr
    filter_upwards [] with ω
    apply WithLp.ofLp_injective
    ext i
    simp only [WithLp.ofLp_toLp]
    have hmean := obsMean_eq_structural_mean μ 𝔐 m
    simp only [latentState]
    rw [hmean]
    rw [show (fun a => 𝔐.η m a + 𝔐.ξ m ω a) = 𝔐.η m + 𝔐.ξ m ω from rfl,
      Matrix.mulVec_add]
    change (B'⁻¹ *ᵥ (B *ᵥ 𝔐.η m + B *ᵥ 𝔐.ξ m ω - B *ᵥ 𝔐.η m)) i = _
    rw [add_sub_cancel_left, Matrix.mulVec_mulVec]


-- @node: sameLawCompletion_model_of_atomic
lemma sameLawCompletion_model_of_atomic {p M q : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (v : Fin q → Fin p → ℝ)
    (𝔐 : AtomicCountModel p M Ω μ)
    (B' : Matrix (Fin p) (Fin p) ℝ) (hB' : B' ∈ completionFiber v)
    (hdiag : ∀ i, B' i i = 1)
    (hacyc : ∀ i, ¬ Relation.TransGen (fun j k => j ≠ k ∧ B' k j ≠ 0) i i)
    (α' : Fin M → ℝ) (t' : Fin M → Fin p)
    (hatomic : AtomicMeanShift
      (fun m => B'⁻¹ *ᵥ obsMean μ 𝔐 m) α' t')
    (hnonzero : NonvanishingStrength α') :
    ∃ 𝔐' : AtomicCountModel p M Ω μ,
      𝔐'.A = 1 - B'⁻¹ ∧
      (∀ m, 𝔐'.η m = (sameLawCompletion μ v 𝔐 B' hB').2.1 m ∧
        𝔐'.Ωc m = (sameLawCompletion μ v 𝔐 B' hB').2.2.1 m ∧
        𝔐'.ξ m = (sameLawCompletion μ v 𝔐 B' hB').2.2.2.1 m) ∧
      (sameLawCompletion μ v 𝔐 B' hB').2.2.2.2 = poissonCountLaw ∧
      𝔐'.S = 𝔐.S ∧ 𝔐'.X = 𝔐.X := by
  have hunit := acyclic_unit_matrix_invertible B' hdiag hacyc
  have hmech := acyclic_completion_to_mechanism B' hdiag hacyc
  let η' := fun m => B'⁻¹ *ᵥ obsMean μ 𝔐 m
  let Ωc' := fun m => B'⁻¹ * Matrix.of (obsCov μ 𝔐 m) * (B'⁻¹).transpose
  let ξ' := fun m ω => B'⁻¹ *ᵥ (fun i =>
    latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i - obsMean μ 𝔐 m i)
  have hlatent (m : Fin (M + 1)) (ω : Ω) :
      latentState (1 - B'⁻¹) η' ξ' m ω =
        latentState 𝔐.A 𝔐.η 𝔐.ξ m ω := by
    change totalEffect (1 - B'⁻¹) *ᵥ (fun i =>
      (B'⁻¹ *ᵥ obsMean μ 𝔐 m) i +
      (B'⁻¹ *ᵥ (fun i => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i -
        obsMean μ 𝔐 m i)) i) = _
    rw [hmech.2]
    have hadd : (fun i => (B'⁻¹ *ᵥ obsMean μ 𝔐 m) i +
        (B'⁻¹ *ᵥ (fun i => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i -
          obsMean μ 𝔐 m i)) i) =
        B'⁻¹ *ᵥ latentState 𝔐.A 𝔐.η 𝔐.ξ m ω := by
      change (B'⁻¹ *ᵥ obsMean μ 𝔐 m) +
          B'⁻¹ *ᵥ (fun i => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i -
            obsMean μ 𝔐 m i) = _
      rw [← Matrix.mulVec_add]
      congr 1
      ext i
      simp
    rw [hadd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B' hunit,
      Matrix.one_mulVec]
  let 𝔐' : AtomicCountModel p M Ω μ := {
    p_pos := 𝔐.p_pos
    M_pos := 𝔐.M_pos
    A := 1 - B'⁻¹
    η := η'
    Ωc := Ωc'
    α := α'
    t := t'
    ξ := ξ'
    S := 𝔐.S
    X := 𝔐.X
    acyclic := hmech.1
    atomic := hatomic
    nonvanishing := hnonzero
    gaussian := sameLawCompletion_gaussian μ 𝔐 B' hunit
    poisson := by
      intro m u
      have hold := 𝔐.poisson m u
      refine ⟨hold.1, ?_, ?_, ?_⟩
      · simpa only [hlatent] using hold.2.1
      · simpa only [hlatent] using hold.2.2.1
      · simpa only [hlatent] using hold.2.2.2 }
  refine ⟨𝔐', rfl, ?_, rfl, rfl, rfl⟩
  intro m
  exact ⟨rfl, rfl, rfl⟩


-- @node: sameLawCompletion_atomic_data
lemma sameLawCompletion_atomic_data {p q M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (v : Fin q → Fin p → ℝ)
    (𝔐 : AtomicCountModel p M Ω μ) (hgen : GeneratesDirections μ 𝔐 v)
    (B' : Matrix (Fin p) (Fin p) ℝ) (hB' : B' ∈ completionFiber v) :
    ∃ (α' : Fin M → ℝ) (t' : Fin M → Fin p),
      AtomicMeanShift (fun m => B'⁻¹ *ᵥ obsMean μ 𝔐 m) α' t' ∧
      NonvanishingStrength α' := by
  classical
  simp only [completionFiber, Set.mem_iUnion] at hB'
  obtain ⟨f, hf, hslice⟩ := hB'
  obtain ⟨r, hrq, e, he⟩ := hgen
  let g : Fin M → Fin q := fun m => e (r.κ m)
  let t' : Fin M → Fin p := fun m => f (g m)
  let α' : Fin M → ℝ := fun m => r.c m * v (g m) (f (g m))
  have hvfg (m : Fin M) : v (g m) (f (g m)) ≠ 0 := by
    simpa [support] using hf.1 (g m)
  have hinv (m : Fin M) : B'⁻¹ *ᵥ v (g m) =
      v (g m) (f (g m)) • Pi.single (f (g m)) 1 := by
    have hunit := acyclic_unit_matrix_invertible B' hslice.2.1 hslice.2.2
    have hvcol : v (g m) = v (g m) (f (g m)) • B'.col (f (g m)) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      change v (g m) i = v (g m) (f (g m)) * B' i (f (g m))
      rw [hslice.1 (g m) i]
      field_simp [hvfg m]
    have hcol : B'.col (f (g m)) = B' *ᵥ Pi.single (f (g m)) 1 := by
      ext i
      simp [Matrix.mulVec_single]
    calc
      B'⁻¹ *ᵥ v (g m) = B'⁻¹ *ᵥ
          (v (g m) (f (g m)) • B'.col (f (g m))) := congrArg _ hvcol
      _ = v (g m) (f (g m)) • (B'⁻¹ *ᵥ B'.col (f (g m))) :=
        Matrix.mulVec_smul _ _ _
      _ = _ := by
        rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B' hunit,
          Matrix.one_mulVec]
  refine ⟨α', t', ?_, ?_⟩
  · intro m
    have hshift : (fun i => obsMean μ 𝔐 m.succ i - obsMean μ 𝔐 0 i) =
        obsShift μ 𝔐 m := rfl
    have hdecomp := r.decomp m
    rw [he (r.κ m)] at hdecomp
    change (B'⁻¹ *ᵥ obsMean μ 𝔐 m.succ) -
      (B'⁻¹ *ᵥ obsMean μ 𝔐 0) = _
    rw [← Matrix.mulVec_sub]
    change B'⁻¹ *ᵥ (fun i => obsMean μ 𝔐 m.succ i - obsMean μ 𝔐 0 i) = _
    rw [hshift, hdecomp, Matrix.mulVec_smul, hinv]
    simp [α', t', g, smul_smul, mul_comm]
  · intro m
    exact mul_ne_zero (r.c_ne m) (hvfg m)


-- @node: sameLawCompletion_model
lemma sameLawCompletion_model {p q M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (v : Fin q → Fin p → ℝ)
    (𝔐 : AtomicCountModel p M Ω μ) (hgen : GeneratesDirections μ 𝔐 v)
    (B' : Matrix (Fin p) (Fin p) ℝ) (hB' : B' ∈ completionFiber v) :
    ∃ 𝔐' : AtomicCountModel p M Ω μ,
      GeneratesDirections μ 𝔐' v ∧
      𝔐'.A = 1 - B'⁻¹ ∧
      (∀ m, 𝔐'.η m = (sameLawCompletion μ v 𝔐 B' hB').2.1 m ∧
        𝔐'.Ωc m = (sameLawCompletion μ v 𝔐 B' hB').2.2.1 m ∧
        𝔐'.ξ m = (sameLawCompletion μ v 𝔐 B' hB').2.2.2.1 m) ∧
      (sameLawCompletion μ v 𝔐 B' hB').2.2.2.2 = poissonCountLaw ∧
      𝔐'.S = 𝔐.S ∧ 𝔐'.X = 𝔐.X := by
  classical
  simp only [completionFiber, Set.mem_iUnion] at hB'
  obtain ⟨f, hf, hslice⟩ := hB'
  have hBmem : B' ∈ completionFiber v := by
    simp only [completionFiber, Set.mem_iUnion]
    exact ⟨f, hf, hslice⟩
  obtain ⟨α', t', hatomic, hnonzero⟩ :=
    sameLawCompletion_atomic_data μ v 𝔐 hgen B' hBmem
  obtain ⟨𝔐', hA, hparams, hk, hS, hX⟩ :=
    sameLawCompletion_model_of_atomic μ v 𝔐 B' hBmem hslice.2.1
      hslice.2.2 α' t' hatomic hnonzero
  have hmean (m : Fin (M + 1)) : obsMean μ 𝔐' m = obsMean μ 𝔐 m := by
    funext i
    unfold obsMean
    rw [hS, hX]
  have hobs : obsShift μ 𝔐' = obsShift μ 𝔐 := by
    funext m i
    simp only [obsShift, congrFun (hmean m.succ) i, congrFun (hmean 0) i]
  have hgen' : GeneratesDirections μ 𝔐' v := by
    unfold GeneratesDirections
    exact hobs.symm ▸ hgen
  exact ⟨𝔐', hgen', hA, hparams, hk, hS, hX⟩

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
