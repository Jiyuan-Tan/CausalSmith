module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Basic
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.PoissonMixtureMoments
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial

/-! Random-offset factorial variance identities. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Transfer a raw second-moment correction into a variance correction. -/
-- @node: variance_of_raw_moment_transfer
lemma variance_of_raw_moment_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U E : Ω → ℝ) (c : ℝ) (hU : MemLp U 2 μ) (hE : MemLp E 2 μ)
    (hmean : (∫ ω, U ω ∂μ) = ∫ ω, E ω ∂μ)
    (hsq : (∫ ω, U ω ^ 2 ∂μ) = (∫ ω, E ω ^ 2 ∂μ) + c) :
    variance U μ = variance E μ + c := by
  rw [variance_eq_sub hU, variance_eq_sub hE, hmean]
  simp only [Pi.pow_apply]
  rw [hsq]
  ring

/-- Applying the adjusted factorial map to each observed offset-count pair preserves
independence and identical distribution within an environment. -/
-- @node: factorialPair_iid
lemma factorialPair_iid {p n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ)
    (X : Fin (p + 1) → Fin n → Ω → Fin p → ℕ)
    (hI : IIDWithinEnvironment μ S X) :
    (∀ m j,
      iIndepFun (fun r ω =>
        (firstFactorial (X m r ω) (S m r ω) j,
         secondFactorial (X m r ω) (S m r ω) j)) μ) ∧
    (∀ m j r s,
      IdentDistrib
        (fun ω => (firstFactorial (X m r ω) (S m r ω) j,
          secondFactorial (X m r ω) (S m r ω) j))
        (fun ω => (firstFactorial (X m s ω) (S m s ω) j,
          secondFactorial (X m s ω) (S m s ω) j)) μ μ) := by
  let F (j : Fin p) : (Fin p → ℝ) × (Fin p → ℕ) → ℝ × ℝ :=
    fun sx => (firstFactorial sx.2 sx.1 j, secondFactorial sx.2 sx.1 j)
  have hF (j : Fin p) : Measurable (F j) := by
    dsimp [F, firstFactorial, secondFactorial]
    fun_prop
  constructor
  · intro m j
    have h := (hI m).1.comp (fun _ => F j) (fun _ => hF j)
    simpa only [Function.comp_def, F] using h
  · intro m j r s
    have h := ((hI m).2 r s).comp (hF j)
    simpa only [Function.comp_def, F] using h

/-- Exogeneity and the stated moment envelope make the conditional raw second
moments of the adjusted factorial statistics integrable. -/
-- @node: offset_exogeneity_raw_moments_integrable
lemma offset_exogeneity_raw_moments_integrable {p n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ)
    (hE : OffsetExogeneity μ S Z)
    (v : ℝ) (hV : FactorialVarianceBound μ Z S v)
    (m : Fin (p + 1)) (r : Fin n) (j : Fin p) :
    Integrable (fun ω => Real.exp (2 * Z m r ω j) +
      Real.exp (Z m r ω j) / S m r ω j) μ ∧
    Integrable (fun ω => Real.exp (4 * Z m r ω j) +
      4 * Real.exp (3 * Z m r ω j) / S m r ω j +
      2 * Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) μ := by
  have h := (hV.1 m r j)
  rcases h with ⟨h1, hMem1, h2, hMem2, h3, hs1, hs2⟩
  have hE1 : IndepFun
      (fun ω => Real.exp (Z m r ω j))
      (fun ω => (S m r ω j)⁻¹) μ := by
    simpa only [Function.comp_def] using
      (hE m r).symm.comp
        (by fun_prop : Measurable (fun z : Fin p → ℝ => Real.exp (z j)))
        (by fun_prop : Measurable (fun s : Fin p → ℝ => (s j)⁻¹))
  have hE3 : IndepFun
      (fun ω => Real.exp (3 * Z m r ω j))
      (fun ω => (S m r ω j)⁻¹) μ := by
    simpa only [Function.comp_def] using
      (hE m r).symm.comp
        (by fun_prop : Measurable (fun z : Fin p → ℝ => Real.exp (3 * z j)))
        (by fun_prop : Measurable (fun s : Fin p → ℝ => (s j)⁻¹))
  have hE2 : IndepFun
      (fun ω => Real.exp (2 * Z m r ω j))
      (fun ω => (S m r ω j)⁻¹ ^ 2) μ := by
    simpa only [Function.comp_def] using
      (hE m r).symm.comp
        (by fun_prop : Measurable (fun z : Fin p → ℝ => Real.exp (2 * z j)))
        (by fun_prop : Measurable (fun s : Fin p → ℝ => (s j)⁻¹ ^ 2))
  have hUprod : Integrable (fun ω => Real.exp (Z m r ω j) / S m r ω j) μ := by
    have heq : (fun ω => Real.exp (Z m r ω j) / S m r ω j) =
        (fun ω => Real.exp (Z m r ω j)) * (fun ω => (S m r ω j)⁻¹) := by
      funext ω
      simp [div_eq_mul_inv]
    rw [heq]
    exact hE1.integrable_mul h1 hs1
  have hWprod1 : Integrable
      (fun ω => Real.exp (3 * Z m r ω j) / S m r ω j) μ := by
    have heq : (fun ω => Real.exp (3 * Z m r ω j) / S m r ω j) =
        (fun ω => Real.exp (3 * Z m r ω j)) * (fun ω => (S m r ω j)⁻¹) := by
      funext ω
      simp [div_eq_mul_inv]
    rw [heq]
    exact hE3.integrable_mul h3 hs1
  have hWprod2 : Integrable
      (fun ω => Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) μ := by
    have heq : (fun ω => Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) =
        (fun ω => Real.exp (2 * Z m r ω j)) *
          (fun ω => (S m r ω j)⁻¹ ^ 2) := by
      funext ω
      simp [div_eq_mul_inv, inv_pow]
    rw [heq]
    exact hE2.integrable_mul h2 hs2
  have h4 : Integrable (fun ω => Real.exp (4 * Z m r ω j)) μ := by
    convert hMem2.integrable_sq using 1
    funext ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  refine ⟨h2.add hUprod, ?_⟩
  have heq : (fun ω => Real.exp (4 * Z m r ω j) +
        4 * Real.exp (3 * Z m r ω j) / S m r ω j +
        2 * Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) =
      ((fun ω => Real.exp (4 * Z m r ω j)) +
        (4 : ℝ) • (fun ω => Real.exp (3 * Z m r ω j) / S m r ω j)) +
        (2 : ℝ) • (fun ω => Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) := by
    funext ω
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  rw [heq]
  exact (h4.add (hWprod1.const_mul 4)).add (hWprod2.const_mul 2)

/-- Offset exogeneity factors each integrable mixed exponential and inverse-offset moment. -/
-- @node: offset_exogeneity_exp_inverse_factor
lemma offset_exogeneity_exp_inverse_factor {p n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (Z S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ)
    (hE : OffsetExogeneity μ S Z)
    (m : Fin (p + 1)) (r : Fin n) (j : Fin p) (k : ℝ) (a : ℕ)
    (hexp : Integrable (fun ω => Real.exp (k * Z m r ω j)) μ)
    (hinv : Integrable (fun ω => (S m r ω j)⁻¹ ^ a) μ) :
    Integrable (fun ω => Real.exp (k * Z m r ω j) * (S m r ω j)⁻¹ ^ a) μ ∧
      (∫ ω, Real.exp (k * Z m r ω j) * (S m r ω j)⁻¹ ^ a ∂μ) =
        (∫ ω, Real.exp (k * Z m r ω j) ∂μ) *
          ∫ ω, (S m r ω j)⁻¹ ^ a ∂μ := by
  have hindep : IndepFun (fun ω => Real.exp (k * Z m r ω j))
      (fun ω => (S m r ω j)⁻¹ ^ a) μ := by
    simpa only [Function.comp_def] using
      (hE m r).symm.comp
        (by fun_prop : Measurable (fun z : Fin p → ℝ => Real.exp (k * z j)))
        (by fun_prop : Measurable (fun s : Fin p → ℝ => (s j)⁻¹ ^ a))
  refine ⟨?_, ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral
    hindep hexp.1 hinv.1⟩
  have heq : (fun ω => Real.exp (k * Z m r ω j) * (S m r ω j)⁻¹ ^ a) =
      (fun ω => Real.exp (k * Z m r ω j)) *
        (fun ω => (S m r ω j)⁻¹ ^ a) := by
    funext ω
    rfl
  rw [heq]
  exact hindep.integrable_mul hexp hinv

-- @node: lem:random-offset-variance
lemma random_offset_variance {p n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z S : Fin (p + 1) → Fin n → Ω → Fin p → ℝ)
    (X : Fin (p + 1) → Fin n → Ω → Fin p → ℕ)
    (v : ℝ) (hP : PoissonMeasurement μ Z S X)
    (hI : IIDWithinEnvironment μ S X)
    (hE : OffsetExogeneity μ S Z)
    (hV : FactorialVarianceBound μ Z S v) :
    (∀ m j,
      iIndepFun (fun r ω =>
        (firstFactorial (X m r ω) (S m r ω) j,
         secondFactorial (X m r ω) (S m r ω) j)) μ) ∧
    (∀ m j r s,
      IdentDistrib
        (fun ω => (firstFactorial (X m r ω) (S m r ω) j,
          secondFactorial (X m r ω) (S m r ω) j))
        (fun ω => (firstFactorial (X m s ω) (S m s ω) j,
          secondFactorial (X m s ω) (S m s ω) j)) μ μ) ∧
    (∀ m r j,
      variance (fun ω => firstFactorial (X m r ω) (S m r ω) j) μ =
        variance (fun ω => Real.exp (Z m r ω j)) μ +
          (∫ ω, Real.exp (Z m r ω j) ∂μ) *
            ∫ ω, (S m r ω j)⁻¹ ∂μ) ∧
    (∀ m r j,
      variance (fun ω => secondFactorial (X m r ω) (S m r ω) j) μ =
        variance (fun ω => Real.exp (2 * Z m r ω j)) μ +
          4 * (∫ ω, Real.exp (3 * Z m r ω j) ∂μ) *
            (∫ ω, (S m r ω j)⁻¹ ∂μ) +
          2 * (∫ ω, Real.exp (2 * Z m r ω j) ∂μ) *
            ∫ ω, (S m r ω j)⁻¹ ^ 2 ∂μ) ∧
    (∀ m r j,
      variance (fun ω => firstFactorial (X m r ω) (S m r ω) j) μ ≤ v ∧
      variance (fun ω => secondFactorial (X m r ω) (S m r ω) j) μ ≤ v) := by
  have hIID := factorialPair_iid μ S X hI
  have hvariance :
      (∀ m r j,
        variance (fun ω => firstFactorial (X m r ω) (S m r ω) j) μ =
          variance (fun ω => Real.exp (Z m r ω j)) μ +
            (∫ ω, Real.exp (Z m r ω j) ∂μ) *
              ∫ ω, (S m r ω j)⁻¹ ∂μ) ∧
      (∀ m r j,
        variance (fun ω => secondFactorial (X m r ω) (S m r ω) j) μ =
          variance (fun ω => Real.exp (2 * Z m r ω j)) μ +
            4 * (∫ ω, Real.exp (3 * Z m r ω j) ∂μ) *
              (∫ ω, (S m r ω j)⁻¹ ∂μ) +
            2 * (∫ ω, Real.exp (2 * Z m r ω j) ∂μ) *
              ∫ ω, (S m r ω j)⁻¹ ^ 2 ∂μ) := by
    constructor <;> intro m r j
    · have hp : PoissonMeasurement μ
          (fun _ : Unit => fun _ : Unit => Z m r)
          (fun _ _ => S m r) (fun _ _ => X m r) := by
        intro _ _
        exact hP m r
      obtain ⟨h1, hMem1, h2, _, _, hs1, _⟩ := hV.1 m r j
      have hcond := offset_exogeneity_raw_moments_integrable μ Z S hE v hV m r j
      have hraw := poisson_mixture_adjusted_factorial_raw_moments μ
        (S m r) (Z m r) (X m r) hp j h1 h2 hcond.1 hcond.2
      have hUprod : Integrable
          (fun ω => Real.exp (Z m r ω j) / S m r ω j) μ := by
        have heq : (fun ω => Real.exp (Z m r ω j) / S m r ω j) =
            (fun ω => Real.exp (2 * Z m r ω j) +
              Real.exp (Z m r ω j) / S m r ω j) -
              (fun ω => Real.exp (2 * Z m r ω j)) := by
          funext ω
          simp [Pi.sub_apply]
        rw [heq]
        exact hcond.1.sub h2
      have hfactor : (∫ ω, Real.exp (Z m r ω j) / S m r ω j ∂μ) =
          (∫ ω, Real.exp (Z m r ω j) ∂μ) *
            ∫ ω, (S m r ω j)⁻¹ ∂μ := by
        simpa only [one_mul, pow_one, div_eq_mul_inv] using
          (offset_exogeneity_exp_inverse_factor μ Z S hE m r j 1 1
            (by simpa using h1) (by simpa using hs1)).2
      have hexpsq : (∫ ω, (Real.exp (Z m r ω j)) ^ 2 ∂μ) =
          ∫ ω, Real.exp (2 * Z m r ω j) ∂μ := by
        congr 1
        funext ω
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have hsq : (∫ ω, (firstFactorial (X m r ω) (S m r ω) j) ^ 2 ∂μ) =
          (∫ ω, (Real.exp (Z m r ω j)) ^ 2 ∂μ) +
            (∫ ω, Real.exp (Z m r ω j) ∂μ) *
              ∫ ω, (S m r ω j)⁻¹ ∂μ := by
        rw [hraw.2.1, integral_add h2 hUprod, hfactor, hexpsq]
      exact variance_of_raw_moment_transfer μ
        (fun ω => firstFactorial (X m r ω) (S m r ω) j)
        (fun ω => Real.exp (Z m r ω j))
        ((∫ ω, Real.exp (Z m r ω j) ∂μ) *
          ∫ ω, (S m r ω j)⁻¹ ∂μ)
        hraw.2.2.2.2.1 hMem1 hraw.1 hsq
    · have hp : PoissonMeasurement μ
          (fun _ : Unit => fun _ : Unit => Z m r)
          (fun _ _ => S m r) (fun _ _ => X m r) := by
        intro _ _
        exact hP m r
      obtain ⟨h1, _, h2, hMem2, h3, hs1, hs2⟩ := hV.1 m r j
      have hcond := offset_exogeneity_raw_moments_integrable μ Z S hE v hV m r j
      have hraw := poisson_mixture_adjusted_factorial_raw_moments μ
        (S m r) (Z m r) (X m r) hp j h1 h2 hcond.1 hcond.2
      have h4 : Integrable (fun ω => Real.exp (4 * Z m r ω j)) μ := by
        convert hMem2.integrable_sq using 1
        funext ω
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have hfactor3 := offset_exogeneity_exp_inverse_factor μ Z S hE m r j 3 1
        (by simpa using h3) (by simpa using hs1)
      have hfactor2 := offset_exogeneity_exp_inverse_factor μ Z S hE m r j 2 2
        h2 hs2
      have hterm4 : Integrable
          (fun ω => 4 * Real.exp (3 * Z m r ω j) / S m r ω j) μ := by
        have heq : (fun ω => 4 * Real.exp (3 * Z m r ω j) / S m r ω j) =
            (4 : ℝ) • (fun ω => Real.exp (3 * Z m r ω j) *
              (S m r ω j)⁻¹ ^ 1) := by
          funext ω
          simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
          ring
        rw [heq]
        exact hfactor3.1.const_mul 4
      have hterm2 : Integrable
          (fun ω => 2 * Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) μ := by
        have heq : (fun ω => 2 * Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) =
            (2 : ℝ) • (fun ω => Real.exp (2 * Z m r ω j) *
              (S m r ω j)⁻¹ ^ 2) := by
          funext ω
          simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, inv_pow]
          ring
        rw [heq]
        exact hfactor2.1.const_mul 2
      have hexpsq : (∫ ω, (Real.exp (2 * Z m r ω j)) ^ 2 ∂μ) =
          ∫ ω, Real.exp (4 * Z m r ω j) ∂μ := by
        congr 1
        funext ω
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have hsq : (∫ ω, (secondFactorial (X m r ω) (S m r ω) j) ^ 2 ∂μ) =
          (∫ ω, (Real.exp (2 * Z m r ω j)) ^ 2 ∂μ) +
            4 * (∫ ω, Real.exp (3 * Z m r ω j) ∂μ) *
              (∫ ω, (S m r ω j)⁻¹ ∂μ) +
            2 * (∫ ω, Real.exp (2 * Z m r ω j) ∂μ) *
              ∫ ω, (S m r ω j)⁻¹ ^ 2 ∂μ := by
        rw [hraw.2.2.2.1]
        have heq : (fun ω => Real.exp (4 * Z m r ω j) +
            4 * Real.exp (3 * Z m r ω j) / S m r ω j +
            2 * Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) =
            ((fun ω => Real.exp (4 * Z m r ω j)) +
              (fun ω => 4 * Real.exp (3 * Z m r ω j) / S m r ω j)) +
              (fun ω => 2 * Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) := by
          funext ω
          simp [Pi.add_apply]
        rw [heq]
        rw [integral_add' (h4.add hterm4) hterm2, integral_add' h4 hterm4]
        have ht4 : (∫ ω, 4 * Real.exp (3 * Z m r ω j) / S m r ω j ∂μ) =
            4 * ((∫ ω, Real.exp (3 * Z m r ω j) ∂μ) *
              ∫ ω, (S m r ω j)⁻¹ ∂μ) := by
          calc
            _ = ∫ ω, 4 * (Real.exp (3 * Z m r ω j) / S m r ω j) ∂μ := by
              congr 1
              funext ω
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
            _ = 4 * ∫ ω, Real.exp (3 * Z m r ω j) / S m r ω j ∂μ :=
              integral_const_mul 4 _
            _ = _ := by
              simpa only [pow_one, div_eq_mul_inv] using
                congrArg (fun x : ℝ => 4 * x) hfactor3.2
        have ht2 : (∫ ω, 2 * Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2 ∂μ) =
            2 * ((∫ ω, Real.exp (2 * Z m r ω j) ∂μ) *
              ∫ ω, (S m r ω j)⁻¹ ^ 2 ∂μ) := by
          calc
            _ = ∫ ω, 2 * (Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2) ∂μ := by
              congr 1
              funext ω
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
            _ = 2 * ∫ ω, Real.exp (2 * Z m r ω j) / (S m r ω j) ^ 2 ∂μ :=
              integral_const_mul 2 _
            _ = _ := by
              simpa only [div_eq_mul_inv, inv_pow] using
                congrArg (fun x : ℝ => 2 * x) hfactor2.2
        rw [ht4, ht2, hexpsq]
        ring
      have hsq' : (∫ ω, (secondFactorial (X m r ω) (S m r ω) j) ^ 2 ∂μ) =
          (∫ ω, (Real.exp (2 * Z m r ω j)) ^ 2 ∂μ) +
            (4 * (∫ ω, Real.exp (3 * Z m r ω j) ∂μ) *
              (∫ ω, (S m r ω j)⁻¹ ∂μ) +
              2 * (∫ ω, Real.exp (2 * Z m r ω j) ∂μ) *
                ∫ ω, (S m r ω j)⁻¹ ^ 2 ∂μ) := by
        rw [hsq]
        ring
      have hvar := variance_of_raw_moment_transfer μ
        (fun ω => secondFactorial (X m r ω) (S m r ω) j)
        (fun ω => Real.exp (2 * Z m r ω j))
        (4 * (∫ ω, Real.exp (3 * Z m r ω j) ∂μ) *
            (∫ ω, (S m r ω j)⁻¹ ∂μ) +
          2 * (∫ ω, Real.exp (2 * Z m r ω j) ∂μ) *
            ∫ ω, (S m r ω j)⁻¹ ^ 2 ∂μ)
        hraw.2.2.2.2.2 hMem2 hraw.2.2.1 hsq'
      simpa only [add_assoc] using hvar
  refine ⟨hIID.1, hIID.2, hvariance.1, hvariance.2, ?_⟩
  intro m r j
  obtain ⟨hfirst, hsecond⟩ := hvariance
  have hbound := hV.2 m r j
  rw [hfirst m r j, hsecond m r j]
  exact ⟨(le_max_left _ _).trans hbound, (le_max_right _ _).trans hbound⟩

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
