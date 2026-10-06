module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Basic
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.PoissonMixtureMoments
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.OffsetExampleWitnesses
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! Observable factorial moments identify Gaussian latent means and covariances. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- The Gaussian moment-generating formula supplies both the exponential
integrability needed by the Poisson transfer and its exact moment. -/
-- @node: hasGaussianLaw_exp_integrable_and_integral
lemma hasGaussianLaw_exp_integrable_and_integral {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : HasGaussianLaw X μ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) μ ∧
      (∫ ω, Real.exp (t * X ω) ∂μ) =
        Real.exp ((∫ ω, X ω ∂μ) * t +
          (variance X μ).toNNReal * t ^ 2 / 2) := by
  have hmgf := mgf_gaussianReal hX.map_eq_gaussianReal t
  constructor
  · exact mgf_pos_iff.mp (hmgf.symm ▸ Real.exp_pos _)
  · exact hmgf

/-- The structural state is an affine image of the Gaussian disturbance. -/
-- @node: atomicCountModel_latentState_hasGaussianLaw
lemma atomicCountModel_latentState_hasGaussianLaw {p M : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p M Ω μ) (m : Fin (M + 1)) :
    HasGaussianLaw
      (fun ω => WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω)) μ := by
  let L := (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun (totalEffect 𝔐.A)
  let F : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
    fun x => WithLp.toLp 2 (Matrix.mulVec (totalEffect 𝔐.A) (𝔐.η m)) + L x
  have hF : Measurable F := by fun_prop
  have hξ := HasLaw.hasGaussianLaw (𝔐.gaussian m).2
  have hstate (ω : Ω) :
      WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω) =
        F (WithLp.toLp 2 (𝔐.ξ m ω)) := by
    change WithLp.toLp 2 (Matrix.mulVec (totalEffect 𝔐.A)
        (fun i => 𝔐.η m i + 𝔐.ξ m ω i)) = _
    rw [show (fun i => 𝔐.η m i + 𝔐.ξ m ω i) = 𝔐.η m + 𝔐.ξ m ω from rfl,
      Matrix.mulVec_add]
    simp only [F]
    congr 1
  have hmap : μ.map (fun ω => WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω)) =
      (μ.map (fun ω => WithLp.toLp 2 (𝔐.ξ m ω))).map F := by
    rw [show (fun ω => WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω)) =
      F ∘ (fun ω => WithLp.toLp 2 (𝔐.ξ m ω)) from funext hstate]
    exact (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hξ.aemeasurable).symm
  constructor
  rw [hmap]
  haveI : IsGaussian (μ.map (fun ω => WithLp.toLp 2 (𝔐.ξ m ω))) :=
    hξ.isGaussian_map
  have hF' : F = (fun x => WithLp.toLp 2 (Matrix.mulVec (totalEffect 𝔐.A) (𝔐.η m)) + x) ∘ L := rfl
  rw [hF', ← Measure.map_map (by fun_prop) (by fun_prop)]
  infer_instance

-- @node: atomicCountModel_latentCoord_hasGaussianLaw
lemma atomicCountModel_latentCoord_hasGaussianLaw {p M : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (𝔐 : AtomicCountModel p M Ω μ) (m : Fin (M + 1)) (j : Fin p) :
    HasGaussianLaw (fun ω => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j) μ := by
  have h := (atomicCountModel_latentState_hasGaussianLaw μ 𝔐 m).map_of_measurable
    (EuclideanSpace.proj (𝕜 := ℝ) j) (by fun_prop)
  simpa [Function.comp_def] using h

-- @node: obsCov_diagonal_formula
lemma obsCov_diagonal_formula {p M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝔐 : AtomicCountModel p M Ω μ)
    (m : Fin (M + 1)) (j : Fin p) :
    obsCov μ 𝔐 m j j =
      Real.log (∫ ω, secondFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) -
        2 * Real.log
          (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) := by
  simp only [obsCov, crossFactorial, ite_true]
  ring

-- @node: secondFactorial_unit_offset
lemma secondFactorial_unit_offset {p : ℕ} (x : Fin p → ℕ)
    (s : Fin p → ℝ) (j : Fin p) (hs : s j = 1) :
    secondFactorial x s j = (x j : ℝ) * ((x j : ℝ) - 1) := by
  simp [secondFactorial, hs]

/-- The two ways of applying a second falling factorial to an offset count
differ by a first-order offset term. -/
-- @node: offset_factorial_difference
lemma offset_factorial_difference {p : ℕ} (x : Fin p → ℕ)
    (s : Fin p → ℝ) (j : Fin p) (hs : s j ≠ 0) :
    firstFactorial x s j * (firstFactorial x s j - 1) -
        secondFactorial x s j =
      (x j : ℝ) * (1 - s j) / (s j) ^ 2 := by
  simp only [firstFactorial, secondFactorial]
  field_simp
  ring

/-- A nonzero count at a positive nonunit offset witnesses that the two
statistics are different as functions of the observed pair. -/
-- @node: offset_factorial_ne_of_nonunit
lemma offset_factorial_ne_of_nonunit {p : ℕ} (x : Fin p → ℕ)
    (s : Fin p → ℝ) (j : Fin p) (hx : x j ≠ 0)
    (hs : 0 < s j) (hs1 : s j ≠ 1) :
    firstFactorial x s j * (firstFactorial x s j - 1) ≠
      secondFactorial x s j := by
  intro heq
  have hdiff := offset_factorial_difference x s j (ne_of_gt hs)
  rw [heq, sub_self] at hdiff
  have hx' : (x j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hx
  have hs' : 1 - s j ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  exact (div_ne_zero (mul_ne_zero hx' hs') (pow_ne_zero 2 (ne_of_gt hs))) hdiff.symm

/-- The model's joint conditional Poisson law transfers adjusted factorial
moments to exponential moments of its latent state. -/
-- @node: atomicCountModel_factorial_moment_transfer
lemma atomicCountModel_factorial_moment_transfer {p M : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝔐 : AtomicCountModel p M Ω μ) (m : Fin (M + 1)) (j k : Fin p)
    (hj : Integrable (fun ω => Real.exp (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j)) μ)
    (hjk : Integrable (fun ω => Real.exp
      (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j +
        latentState 𝔐.A 𝔐.η 𝔐.ξ m ω k)) μ) :
    (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) =
      ∫ ω, Real.exp (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j) ∂μ ∧
    (∫ ω, crossFactorial (𝔐.X m ω) (𝔐.S m ω) j k ∂μ) =
      ∫ ω, Real.exp (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j +
        latentState 𝔐.A 𝔐.η 𝔐.ξ m ω k) ∂μ := by
  exact poisson_mixture_factorial_moment_transfer μ
    (𝔐.S m) (latentState 𝔐.A 𝔐.η 𝔐.ξ m) (𝔐.X m)
    (fun _ _ => 𝔐.poisson m ()) j k hj hjk

/-- Observable factorial moments recover the latent Gaussian mean and covariance. -/
-- @node: lem:observable-moment-bridge
lemma observable_moment_bridge {p M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝔐 : AtomicCountModel p M Ω μ) :
    (∀ m j, obsMean μ 𝔐 m j =
      ∫ ω, latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j ∂μ) ∧
    (∀ m j k, obsCov μ 𝔐 m j k =
      ∫ ω, (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j -
        ∫ ω', latentState 𝔐.A 𝔐.η 𝔐.ξ m ω' j ∂μ) *
        (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω k -
        ∫ ω', latentState 𝔐.A 𝔐.η 𝔐.ξ m ω' k ∂μ) ∂μ) ∧
    (∀ m j, obsCov μ 𝔐 m j j =
      Real.log (∫ ω, secondFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) -
        2 * Real.log
          (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ)) ∧
    (∀ m j, (∀ ω, 𝔐.S m ω j = 1) →
      ∀ ω, secondFactorial (𝔐.X m ω) (𝔐.S m ω) j =
        (𝔐.X m ω j : ℝ) * ((𝔐.X m ω j : ℝ) - 1)) ∧
    (∃ (Ω' : Type) (ms' : MeasurableSpace Ω')
      (μ' : Measure Ω'),
      letI : MeasurableSpace Ω' := ms'
      ∃ 𝔐' : AtomicCountModel 1 1 Ω' μ',
        μ' Set.univ = 1 ∧
        (∀ᵐ ω ∂μ', 𝔐'.S 0 ω 0 ≠ 1) ∧
        (∫ ω,
          firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 *
            (firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 - 1) ∂μ') ≠
          ∫ ω, secondFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 ∂μ') ∧
    (∃ (Ω' : Type) (ms' : MeasurableSpace Ω')
      (μ' : Measure Ω'),
      letI : MeasurableSpace Ω' := ms'
      ∃ 𝔐' : AtomicCountModel 1 1 Ω' μ',
        μ' Set.univ = 1 ∧
        (∀ᵐ ω ∂μ', 𝔐'.S 0 ω 0 ≠ 1) ∧
        (∫ ω,
          firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 *
            (firstFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 - 1) ∂μ') =
          ∫ ω, secondFactorial (𝔐'.X 0 ω) (𝔐'.S 0 ω) 0 ∂μ') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m j
    let Z : Ω → ℝ := fun ω => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j
    have hZ : HasGaussianLaw Z μ :=
      atomicCountModel_latentCoord_hasGaussianLaw μ 𝔐 m j
    have h1 := hasGaussianLaw_exp_integrable_and_integral μ Z hZ 1
    have h2 := hasGaussianLaw_exp_integrable_and_integral μ Z hZ 2
    have h2int : Integrable (fun ω => Real.exp (Z ω + Z ω)) μ := by
      convert h2.1 using 1
      funext ω
      congr 1
      ring
    have htransfer := atomicCountModel_factorial_moment_transfer μ 𝔐 m j j
      (by simpa [Z] using h1.1) (by simpa [Z] using h2int)
    have hfirst : (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) =
        Real.exp ((∫ ω, Z ω ∂μ) + (variance Z μ).toNNReal / 2) := by
      rw [htransfer.1]
      simpa [Z] using h1.2
    have hsecond : (∫ ω, secondFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) =
        Real.exp (2 * (∫ ω, Z ω ∂μ) + 2 * (variance Z μ).toNNReal) := by
      have hx := htransfer.2
      simp only [crossFactorial, ite_true] at hx
      calc
        _ = ∫ ω, Real.exp (2 * Z ω) ∂μ := by
          rw [hx]
          congr 1
          funext ω
          congr 1
          ring
        _ = Real.exp ((∫ ω, Z ω ∂μ) * 2 +
              (variance Z μ).toNNReal * 2 ^ 2 / 2) := h2.2
        _ = _ := by congr 1; ring
    unfold obsMean
    rw [hfirst, hsecond, Real.log_exp, Real.log_exp]
    change 2 * ((∫ ω, Z ω ∂μ) + (variance Z μ).toNNReal / 2) -
      (1 / 2 : ℝ) * (2 * (∫ ω, Z ω ∂μ) + 2 * (variance Z μ).toNNReal) = _
    ring
  · intro m j k
    let X : Ω → ℝ := fun ω => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j
    let Y : Ω → ℝ := fun ω => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω k
    have hstate := atomicCountModel_latentState_hasGaussianLaw μ 𝔐 m
    have hX : HasGaussianLaw X μ :=
      atomicCountModel_latentCoord_hasGaussianLaw μ 𝔐 m j
    have hY : HasGaussianLaw Y μ :=
      atomicCountModel_latentCoord_hasGaussianLaw μ 𝔐 m k
    have hsum : HasGaussianLaw (fun ω => X ω + Y ω) μ := by
      have h := hstate.map_of_measurable
        (EuclideanSpace.proj (𝕜 := ℝ) j + EuclideanSpace.proj (𝕜 := ℝ) k)
        (by fun_prop)
      simpa [X, Y, Function.comp_def] using h
    have hXm := hasGaussianLaw_exp_integrable_and_integral μ X hX 1
    have hYm := hasGaussianLaw_exp_integrable_and_integral μ Y hY 1
    have hSm := hasGaussianLaw_exp_integrable_and_integral μ
      (fun ω => X ω + Y ω) hsum 1
    have htransfer := atomicCountModel_factorial_moment_transfer μ 𝔐 m j k
      (by simpa [X] using hXm.1) (by simpa [X, Y] using hSm.1)
    have htransferY := (atomicCountModel_factorial_moment_transfer μ 𝔐 m k k
      (by simpa [Y] using hYm.1)
      (by
        have h2 := hasGaussianLaw_exp_integrable_and_integral μ Y hY 2
        convert h2.1 using 1
        funext ω
        congr 1
        ring)).1
    have hvar : variance (fun ω => X ω + Y ω) μ =
        variance X μ + 2 * covariance X Y μ + variance Y μ :=
      variance_fun_add hX.memLp_two hY.memLp_two
    simp only [one_mul] at hSm hXm hYm
    unfold obsCov
    rw [htransfer.2, htransfer.1, htransferY, hSm.2, hXm.2, hYm.2,
      Real.log_exp, Real.log_exp, Real.log_exp]
    change _ = covariance X Y μ
    simp only [mul_one, one_pow] at *
    rw [integral_add hX.integrable hY.integrable, hvar]
    have hXnn := variance_nonneg X μ
    have hYnn := variance_nonneg Y μ
    have hSnn := variance_nonneg (fun ω => X ω + Y ω) μ
    rw [Real.coe_toNNReal _ hXnn, Real.coe_toNNReal _ hYnn]
    have hsumNN : 0 ≤ variance X μ + 2 * covariance X Y μ + variance Y μ := by
      rw [← hvar]
      exact hSnn
    rw [Real.coe_toNNReal _ hsumNN]
    ring
  · exact fun m j => obsCov_diagonal_formula μ 𝔐 m j
  · intro m j hs ω
    exact secondFactorial_unit_offset (𝔐.X m ω) (𝔐.S m ω) j (hs ω)
  · exact fixed_offset_atomic_model_witness
  · exact random_offset_atomic_model_witness

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
