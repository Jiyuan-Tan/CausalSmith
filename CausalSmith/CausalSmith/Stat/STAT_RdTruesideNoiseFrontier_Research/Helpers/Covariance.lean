module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.HeatHermite
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Kernel
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Rate

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The removable quotient has degree at most one less than its Chebyshev index. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_natDegree_le (L : ℕ) : (endpointF L).natDegree ≤ L - 1 := by
  have ha : (1 - Polynomial.C (2 : ℝ) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_one]
    exact max_le (by omega) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  have hc : ((chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X)).natDegree ≤ L := by
    apply Polynomial.natDegree_comp_le.trans
    simpa [chebyshev, Polynomial.Chebyshev.natDegree_T] using Nat.mul_le_mul_left L ha
  have hn : (1 - (chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X)).natDegree ≤ L :=
    (Polynomial.natDegree_sub_le _ _).trans (by simpa using hc)
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    exact Nat.sub_le_sub_right hn 1)

/-- Cubing the endpoint quotient gives the declared kernel degree bound. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_natDegree_le (L : ℕ) :
    (endpointKernel L).natDegree ≤ kernelDegree L := by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [Polynomial.natDegree_pow]
  exact Nat.mul_le_mul_left 3 (endpointF_natDegree_le L)

/-- Squaring the factorial derivative norm estimate gives the covariance summands. Given [the displayed inputs and assumptions](hyp:hleg,p,m,j,hm,hj), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_derivative_square_factorial_bound (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (m j : ℕ) (hm : p.natDegree ≤ m) (hj : j ≤ m) :
    (∫ x in (0 : ℝ)..1, ((polyDeriv j p).eval x)^2) ≤
      16^j * ((m : ℝ)+1)^(4*j) * (∫ x in (0 : ℝ)..1, (p.eval x)^2) /
        (Nat.factorial j : ℝ)^2 := by
  by_cases hz : j = 0
  · subst j
    simp [polyDeriv]
  have hE : 0 ≤ ∫ x in (0 : ℝ)..1, (p.eval x)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (by intro x hx; positivity)
  have hD : 0 ≤ ∫ x in (0 : ℝ)..1, ((polyDeriv j p).eval x)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (by intro x hx; positivity)
  have hn := factorial_derivatives p m j hm (by omega) hj
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
  rw [Real.sq_sqrt hD] at hs
  have hfour : ((4 : ℝ)^j)^2 = 16^j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  have hexp : (2*j)*2 = 4*j := by omega
  simpa only [div_pow, mul_pow, Real.sq_sqrt hE, hfour, ← pow_mul, hexp] using hs

/-- The finite cubic-factorial variance series follows from endpoint mass and derivative bounds. Given [the displayed inputs and assumptions](hyp:hleg), [the stated mathematical conclusion holds](goal). -/
lemma kernelVariance_factorial_envelope (hleg : ClassicalLegendreFacts) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L → ∀ σ ∈ Icc (0 : ℝ) 1,
      kernelVariance L σ ≤ C * (L : ℝ)^2 *
        ∑ j ∈ Finset.range (kernelDegree L + 1),
          (C * σ^2 * (L : ℝ)^4)^j / (Nat.factorial j : ℝ)^3 := by
  obtain ⟨A, hA, hkernel⟩ := positive_endpoint 1 (by norm_num)
  let C : ℝ := max A 1296
  have hAC : A ≤ C := le_max_left _ _
  have hbig : 1296 ≤ C := le_max_right _ _
  have hC : 0 < C := lt_of_lt_of_le hA hAC
  refine ⟨C, hC, ?_⟩
  intro L hL σ hσ
  have hσ0 : 0 ≤ σ := hσ.1
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hdegree : (kernelDegree L : ℝ)+1 ≤ 3*(L : ℝ) := by
    unfold kernelDegree
    have hsub : L - 1 + 1 = L := Nat.sub_add_cancel hL
    have hh : (L - 1 : ℕ) + 1 = L := hsub
    have hr : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by exact_mod_cast hh
    push_cast
    linarith
  have hmass := (hkernel L hL).2.2.2
  have hmassC : (∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2) ≤ C*(L : ℝ)^2 :=
    hmass.trans (mul_le_mul_of_nonneg_right hAC (sq_nonneg _))
  have hterm (j : ℕ) (hj : j ∈ Finset.range (kernelDegree L+1)) :
      σ^(2*j) / (Nat.factorial j : ℝ) *
        (∫ x in (0 : ℝ)..1, ((polyDeriv j (endpointKernel L)).eval x)^2) ≤
      C*(L : ℝ)^2 * ((C*σ^2*(L : ℝ)^4)^j / (Nat.factorial j : ℝ)^3) := by
    have hd := polynomial_derivative_square_factorial_bound hleg (endpointKernel L)
      (kernelDegree L) j (endpointKernel_natDegree_le L)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hpow : 16^j * ((kernelDegree L : ℝ)+1)^(4*j) ≤ (C*(L : ℝ)^4)^j := by
      calc
        _ = (16 * (((kernelDegree L : ℝ)+1)^4))^j := by rw [mul_pow, ← pow_mul]
        _ ≤ (C*(L : ℝ)^4)^j := by
          apply pow_le_pow_left₀ (by positivity)
          have hp := pow_le_pow_left₀ (by positivity) hdegree 4
          have hc := mul_le_mul_of_nonneg_right hbig (pow_nonneg hL0 4)
          nlinarith [hp]
    calc
      _ ≤ σ^(2*j) / (Nat.factorial j : ℝ) *
          (16^j * ((kernelDegree L : ℝ)+1)^(4*j) * (C*(L : ℝ)^2) /
            (Nat.factorial j : ℝ)^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hd.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmassC (by positivity)) (by positivity))
      _ ≤ σ^(2*j) / (Nat.factorial j : ℝ) *
          ((C*(L : ℝ)^4)^j * (C*(L : ℝ)^2) / (Nat.factorial j : ℝ)^2) := by
        gcongr
      _ = _ := by
        rw [mul_pow, mul_pow, ← pow_mul]
        ring
  have hs := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hs
  unfold kernelVariance
  have hsum : 0 ≤ ∑ j ∈ Finset.range (kernelDegree L+1),
      σ^(2*j) / (Nat.factorial j : ℝ) *
        (∫ x in (0 : ℝ)..1, ((polyDeriv j (endpointKernel L)).eval x)^2) := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by norm_num) (by intro x hx; positivity)
  exact (show (3/4 : ℝ) * _ ≤ _ from by nlinarith [hsum]).trans hs

/-- With zero noise the finite inverse-heat operator is the identity polynomial. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeat_zero (L : ℕ) : inverseHeat L 0 = endpointKernel L := by
  unfold inverseHeat
  rw [Finset.sum_eq_single 0]
  · simp [polyDeriv]
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

/-- Zero noise leaves the kernel mean and square unchanged under the Gaussian expectation. Given [the displayed inputs and assumptions](hyp:L,x), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeat_zero_covariance (L : ℕ) (x : ℝ) :
    (∫ z, (inverseHeat L 0).eval (x + 0*z) ∂gaussianReal 0 1) =
        (endpointKernel L).eval x ∧
    (∫ z, ((inverseHeat L 0).eval (x + 0*z))^2 ∂gaussianReal 0 1) =
      ∑ j ∈ Finset.range (kernelDegree L + 1),
        (0 : ℝ)^(2*j) * ((polyDeriv j (endpointKernel L)).eval x)^2 /
          (Nat.factorial j : ℝ) := by
  rw [inverseHeat_zero]
  constructor
  · simp
  · rw [Finset.sum_eq_single 0]
    · simp [polyDeriv]
    · intro j hj hj0
      have hpow : 2*j ≠ 0 := by omega
      simp [zero_pow hpow]
    · simp

/-- Nonnegative diagonal cubes are bounded by the cube of their finite sum. Given [the displayed inputs and assumptions](hyp:f,hf,N), [the stated mathematical conclusion holds](goal). -/
lemma sum_cubes_le_cube_sum (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (N : ℕ) :
    (∑ j ∈ Finset.range N, (f j)^3) ≤ (∑ j ∈ Finset.range N, f j)^3 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (add_le_add ih (le_refl ((f N)^3))).trans
      (pow_add_pow_le (n := 3) (x := ∑ j ∈ Finset.range N, f j) (y := f N)
        (Finset.sum_nonneg (fun j _ => hf j)) (hf N) (by norm_num))

/-- The cubic-factorial series is bounded by the cube of the exponential series. Given [the displayed inputs and assumptions](hyp:z,hz,N), [the stated mathematical conclusion holds](goal). -/
lemma cubic_factorial_series_le_exp (z : ℝ) (hz : 0 ≤ z) (N : ℕ) :
    (∑ j ∈ Finset.range N, (z^3)^j / (Nat.factorial j : ℝ)^3) ≤
      Real.exp (3*z) := by
  have hseries : HasSum (fun j : ℕ => z^j / (Nat.factorial j : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have hsum : (∑ j ∈ Finset.range N, z^j / (Nat.factorial j : ℝ)) ≤ Real.exp z := by
    rw [← hseries.tsum_eq]
    exact hseries.summable.sum_le_tsum (Finset.range N) (fun j _ => by positivity)
  calc
    _ = ∑ j ∈ Finset.range N, (z^j / (Nat.factorial j : ℝ))^3 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 3 j]
    _ ≤ (∑ j ∈ Finset.range N, z^j / (Nat.factorial j : ℝ))^3 :=
      sum_cubes_le_cube_sum _ (fun j => by positivity) N
    _ ≤ (Real.exp z)^3 := pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => by positivity)) hsum 3
    _ = Real.exp (3*z) := by simpa using (Real.exp_nat_mul z 3).symm

/-- Below the endpoint resolution, the factorial series has an absolute exponential bound. Given [the displayed inputs and assumptions](hyp:hleg), [the stated mathematical conclusion holds](goal). -/
lemma kernelVariance_low_noise_envelope (hleg : ClassicalLegendreFacts) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, 1 ≤ L → ∀ σ ∈ Icc (0 : ℝ) 1,
      σ ≤ (L : ℝ)^(-2 : ℝ) →
      kernelVariance L σ ≤ D * (L : ℝ)^2 * Real.exp D := by
  obtain ⟨C, hC, hvariance⟩ := kernelVariance_factorial_envelope hleg
  let D : ℝ := max C (3*(C+1))
  have hCD : C ≤ D := le_max_left _ _
  have hexpD : 3*(C+1) ≤ D := le_max_right _ _
  refine ⟨D, lt_of_lt_of_le hC hCD, ?_⟩
  intro L hL σ hσ hsmall
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hres : (L : ℝ)^(-2 : ℝ) = ((L : ℝ)^2)⁻¹ := by
    rw [Real.rpow_neg hLp.le, Real.rpow_two]
  rw [hres] at hsmall
  have hscale : σ * (L : ℝ)^2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (L : ℝ))
    simpa [ne_of_gt hLp] using hh
  have hscale0 : 0 ≤ σ * (L : ℝ)^2 := mul_nonneg hσ.1 (sq_nonneg _)
  have hsquare : σ^2 * (L : ℝ)^4 ≤ 1 := by
    have hs := pow_le_pow_left₀ hscale0 hscale 2
    nlinarith [hs]
  have hbase : C*σ^2*(L : ℝ)^4 ≤ (C+1)^3 := by
    have hc := mul_le_mul_of_nonneg_left hsquare hC.le
    nlinarith [sq_nonneg C]
  have hseries : (∑ j ∈ Finset.range (kernelDegree L+1),
      (C*σ^2*(L : ℝ)^4)^j / (Nat.factorial j : ℝ)^3) ≤ Real.exp D := by
    calc
      _ ≤ ∑ j ∈ Finset.range (kernelDegree L+1),
          ((C+1)^3)^j / (Nat.factorial j : ℝ)^3 := by
        apply Finset.sum_le_sum
        intro j hj
        gcongr
      _ ≤ Real.exp (3*(C+1)) := cubic_factorial_series_le_exp (C+1) (by positivity) _
      _ ≤ Real.exp D := Real.exp_le_exp.mpr hexpD
  calc
    _ ≤ C*(L : ℝ)^2 * _ := hvariance L hL σ hσ
    _ ≤ C*(L : ℝ)^2 * Real.exp D := mul_le_mul_of_nonneg_left hseries (by positivity)
    _ ≤ D*(L : ℝ)^2 * Real.exp D := by gcongr

/-- The diagonal-series argument controls variance by the two-thirds noise scale. Given [the displayed inputs and assumptions](hyp:hleg), [the stated mathematical conclusion holds](goal). -/
lemma kernelVariance_power_noise_envelope (hleg : ClassicalLegendreFacts) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, 1 ≤ L → ∀ σ ∈ Icc (0 : ℝ) 1,
      kernelVariance L σ ≤ D * (L : ℝ)^2 *
        Real.exp (D * (σ * (L : ℝ)^2)^(2/3 : ℝ)) := by
  obtain ⟨C, hC, hvariance⟩ := kernelVariance_factorial_envelope hleg
  let D : ℝ := max C (3*(C+1))
  have hCD : C ≤ D := le_max_left _ _
  have hexpD : 3*(C+1) ≤ D := le_max_right _ _
  refine ⟨D, lt_of_lt_of_le hC hCD, ?_⟩
  intro L hL σ hσ
  let a : ℝ := σ * (L : ℝ)^2
  let z : ℝ := (C+1) * a^(2/3 : ℝ)
  have ha : 0 ≤ a := mul_nonneg hσ.1 (sq_nonneg _)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hcub : (a^(2/3 : ℝ))^3 = a^2 := by
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul ha]
    norm_num
  have hbase : C*σ^2*(L : ℝ)^4 ≤ z^3 := by
    dsimp [z]
    rw [mul_pow, hcub]
    have hc : C ≤ (C+1)^3 := by nlinarith [sq_nonneg C]
    have hb := mul_le_mul_of_nonneg_right hc (sq_nonneg a)
    dsimp [a] at hb
    nlinarith [hb]
  have hseries : (∑ j ∈ Finset.range (kernelDegree L+1),
      (C*σ^2*(L : ℝ)^4)^j / (Nat.factorial j : ℝ)^3) ≤
        Real.exp (D * a^(2/3 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (kernelDegree L+1),
          (z^3)^j / (Nat.factorial j : ℝ)^3 := by
        apply Finset.sum_le_sum
        intro j hj
        gcongr
      _ ≤ Real.exp (3*z) := cubic_factorial_series_le_exp z hz _
      _ ≤ Real.exp (D * a^(2/3 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        dsimp [z]
        nlinarith [mul_le_mul_of_nonneg_right hexpD (Real.rpow_nonneg ha (2/3 : ℝ))]
  calc
    _ ≤ C*(L : ℝ)^2 * _ := hvariance L hL σ hσ
    _ ≤ C*(L : ℝ)^2 * Real.exp (D * a^(2/3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hseries (by positivity)
    _ ≤ D*(L : ℝ)^2 * Real.exp (D * a^(2/3 : ℝ)) := by gcongr

/-- The intermediate cost exactly equals the two-thirds endpoint noise scale. Given [the displayed inputs and assumptions](hyp:L,hL,σ,hσ,hsmall,hpower), [the stated mathematical conclusion holds](goal). -/
lemma endpoint_intermediate_noiseCost (L : ℕ) (hL : 1 ≤ L) (σ : ℝ)
    (hσ : 0 ≤ σ) (hsmall : ¬ σ ≤ (L : ℝ)^(-2 : ℝ))
    (hpower : σ^4 ≤ (L : ℝ)^(-2 : ℝ)) :
    1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ = (σ * (L : ℝ)^2)^(2/3 : ℝ) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hres : (L : ℝ)^(-2 : ℝ) = ((L : ℝ)^2)⁻¹ := by
    rw [Real.rpow_neg hLp.le, Real.rpow_two]
  simp only [noiseCost, if_neg hsmall, if_pos hpower]
  rw [hres, div_inv_eq_mul]
  ring

/-- Below the compact-support interface, the public variance has the exact cost envelope. Given [the displayed inputs and assumptions](hyp:hleg), [the stated mathematical conclusion holds](goal). -/
lemma kernelVariance_noncompact_noise_envelope (hleg : ClassicalLegendreFacts) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, 1 ≤ L → ∀ σ ∈ Icc (0 : ℝ) 1,
      (σ ≤ (L : ℝ)^(-2 : ℝ) ∨ σ^4 ≤ (L : ℝ)^(-2 : ℝ)) →
      kernelVariance L σ ≤ D * (L : ℝ)^2 *
        Real.exp (D * (1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ)) := by
  obtain ⟨D, hD, hbound⟩ := kernelVariance_power_noise_envelope hleg
  refine ⟨D, hD, ?_⟩
  intro L hL σ hσ hbranch
  apply (hbound L hL σ hσ).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hD.le
  by_cases hsmall : σ ≤ (L : ℝ)^(-2 : ℝ)
  · have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hres : (L : ℝ)^(-2 : ℝ) = ((L : ℝ)^2)⁻¹ := by
      rw [Real.rpow_neg hLp.le, Real.rpow_two]
    have hscale : σ * (L : ℝ)^2 ≤ 1 := by
      rw [hres] at hsmall
      have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (L : ℝ))
      simpa [ne_of_gt hLp] using hh
    simp only [noiseCost, if_pos hsmall, add_zero]
    exact Real.rpow_le_one (mul_nonneg hσ.1 (sq_nonneg _)) hscale (by norm_num)
  · rw [endpoint_intermediate_noiseCost L hL σ hσ.1 hsmall (hbranch.resolve_left hsmall)]

/-- A finite cubic-factorial series admits a logarithmic bound at a fixed degree scale.
The exponential coefficient estimate is the uniform version of the factorial/logarithm
estimate: each normalized coefficient at scale L is bounded by exp L. Given [the displayed inputs and assumptions](hyp:L,hL,a,ha,N,hN), [the stated mathematical conclusion holds](goal). -/
lemma finite_cubic_factorial_log_bound (L : ℕ) (hL : 1 ≤ L)
    (a : ℝ) (ha : 1 ≤ a) (N : ℕ) (hN : N ≤ 3*L+1) :
    (∑ j ∈ Finset.range N, (a*(L : ℝ)^3)^j / (Nat.factorial j : ℝ)^3) ≤
      Real.exp ((L : ℝ)*(7 + 3*Real.log a)) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      (a*(L : ℝ)^3)^j / (Nat.factorial j : ℝ)^3 ≤
        a^(3*L) * Real.exp (3*(L : ℝ)) := by
    have hjL : j ≤ 3*L := by have := Finset.mem_range.mp hj; omega
    calc
      _ = a^j * ((L : ℝ)^j / (Nat.factorial j : ℝ))^3 := by
        rw [mul_pow, div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 3 j]
        ring
      _ ≤ a^(3*L) * (Real.exp (L : ℝ))^3 := by
        apply mul_le_mul
        · exact pow_le_pow_right₀ ha hjL
        · exact pow_le_pow_left₀ (by positivity)
            (Real.pow_div_factorial_le_exp (L : ℝ) hLp.le j) 3
        · positivity
        · positivity
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hcard : (N : ℝ) ≤ Real.exp (4*(L : ℝ)) := by
    have hN' : (N : ℝ) ≤ 3*(L : ℝ)+1 := by exact_mod_cast hN
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    exact (hN'.trans (by linarith : 3*(L : ℝ)+1 ≤ 4*(L : ℝ)+1)).trans
      (Real.add_one_le_exp _)
  calc
    _ ≤ ∑ j ∈ Finset.range N, a^(3*L) * Real.exp (3*(L : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (N : ℝ) * (a^(3*L) * Real.exp (3*(L : ℝ))) := by simp
    _ ≤ Real.exp (4*(L : ℝ)) * (a^(3*L) * Real.exp (3*(L : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = Real.exp ((L : ℝ)*(7 + 3*Real.log a)) := by
      rw [← Real.exp_log (lt_of_lt_of_le (by norm_num) ha), ← Real.exp_nat_mul]
      simp only [Real.log_exp, Nat.cast_mul, Nat.cast_ofNat]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- On the compact-support branch, the endpoint cost is the degree times a logarithm. Given [the displayed inputs and assumptions](hyp:L,hL,σ,hsmall,hpower), [the stated mathematical conclusion holds](goal). -/
lemma endpoint_compact_noiseCost (L : ℕ) (hL : 1 ≤ L) (σ : ℝ)
    (hsmall : ¬ σ ≤ (L : ℝ)^(-2 : ℝ))
    (hpower : ¬ σ^4 ≤ (L : ℝ)^(-2 : ℝ)) :
    1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ =
      (L : ℝ)*(1 + Real.log (σ^2*(L : ℝ))) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hres : (L : ℝ)^(-2 : ℝ) = ((L : ℝ)^2)⁻¹ := by
    rw [Real.rpow_neg hLp.le, Real.rpow_two]
  have hsqrt : Real.sqrt ((L : ℝ)^(-2 : ℝ)) = (L : ℝ)⁻¹ := by
    rw [hres, Real.sqrt_inv, Real.sqrt_sq hLp.le]
  have hroot : ((L : ℝ)^(-2 : ℝ))^(-1/2 : ℝ) = (L : ℝ) := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num,
      Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, hsqrt, inv_inv]
  simp only [noiseCost, if_neg hsmall, if_neg hpower, hroot, hsqrt, div_inv_eq_mul]
  ring

/-- Above the compact-support interface the logarithmic noise scale is at least one. Given [the displayed inputs and assumptions](hyp:L,hL,σ,hpower), [the stated mathematical conclusion holds](goal). -/
lemma endpoint_compact_noise_scale (L : ℕ) (hL : 1 ≤ L) (σ : ℝ)
    (hpower : ¬ σ^4 ≤ (L : ℝ)^(-2 : ℝ)) : 1 ≤ σ^2*(L : ℝ) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hres : (L : ℝ)^(-2 : ℝ) = ((L : ℝ)^2)⁻¹ := by
    rw [Real.rpow_neg hLp.le, Real.rpow_two]
  have hp : ((L : ℝ)^2)⁻¹ < σ^4 := by simpa [hres] using lt_of_not_ge hpower
  have hp' : 1 < σ^4*(L : ℝ)^2 := by
    have hh := mul_lt_mul_of_pos_right hp (sq_pos_of_pos hLp)
    simpa [ne_of_gt hLp] using hh
  have hn : 0 ≤ σ^2*(L : ℝ) := by positivity
  nlinarith [sq_nonneg (σ^2*(L : ℝ)-1)]

/-- The exponential cost factor is nonnegative in every endpoint noise branch. Given [the displayed inputs and assumptions](hyp:L,hL,σ,hσ), [the stated mathematical conclusion holds](goal). -/
lemma endpoint_noiseCost_factor_nonneg (L : ℕ) (hL : 1 ≤ L) (σ : ℝ)
    (hσ : 0 ≤ σ) : 0 ≤ 1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ := by
  by_cases hsmall : σ ≤ (L : ℝ)^(-2 : ℝ)
  · simp only [noiseCost, if_pos hsmall, add_zero]
    norm_num
  · by_cases hpower : σ^4 ≤ (L : ℝ)^(-2 : ℝ)
    · rw [endpoint_intermediate_noiseCost L hL σ hσ hsmall hpower]
      positivity
    · rw [endpoint_compact_noiseCost L hL σ hsmall hpower]
      have hlog := Real.log_nonneg (endpoint_compact_noise_scale L hL σ hpower)
      positivity

/-- The finite degree and cubic factorial yield the compact-support variance envelope. Given [the displayed inputs and assumptions](hyp:hleg), [the stated mathematical conclusion holds](goal). -/
lemma kernelVariance_compact_noise_envelope (hleg : ClassicalLegendreFacts) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, 1 ≤ L → ∀ σ ∈ Icc (0 : ℝ) 1,
      (¬ σ ≤ (L : ℝ)^(-2 : ℝ)) → (¬ σ^4 ≤ (L : ℝ)^(-2 : ℝ)) →
      kernelVariance L σ ≤ D*(L : ℝ)^2 *
        Real.exp (D*(1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ)) := by
  obtain ⟨C, hC, hvariance⟩ := kernelVariance_factorial_envelope hleg
  let D : ℝ := max C (7 + 3*Real.log (C+1))
  have hCD : C ≤ D := le_max_left _ _
  have hlogD : 7 + 3*Real.log (C+1) ≤ D := le_max_right _ _
  have hlogC : 0 ≤ Real.log (C+1) := Real.log_nonneg (by linarith)
  have hD : 0 < D := lt_of_lt_of_le hC hCD
  refine ⟨D, hD, ?_⟩
  intro L hL σ hσ hsmall hpower
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hscale : 1 ≤ σ^2*(L : ℝ) := endpoint_compact_noise_scale L hL σ hpower
  have hscale0 : 0 < σ^2*(L : ℝ) := lt_of_lt_of_le (by norm_num) hscale
  have ha : 1 ≤ (C+1)*(σ^2*(L : ℝ)) := by nlinarith
  have hN : kernelDegree L+1 ≤ 3*L+1 := by unfold kernelDegree; omega
  have hseries : (∑ j ∈ Finset.range (kernelDegree L+1),
      (C*σ^2*(L : ℝ)^4)^j / (Nat.factorial j : ℝ)^3) ≤
      Real.exp (D*(1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (kernelDegree L+1),
          (((C+1)*(σ^2*(L : ℝ)))*(L : ℝ)^3)^j / (Nat.factorial j : ℝ)^3 := by
        apply Finset.sum_le_sum
        intro j hj
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [mul_nonneg (sq_nonneg σ) (pow_nonneg hLp.le 4)]
      _ ≤ Real.exp ((L : ℝ)*(7 + 3*Real.log ((C+1)*(σ^2*(L : ℝ))))) :=
        finite_cubic_factorial_log_bound L hL _ ha _ hN
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [endpoint_compact_noiseCost L hL σ hsmall hpower,
          Real.log_mul (by positivity) (ne_of_gt hscale0)]
        have hlogscale : 0 ≤ Real.log (σ^2*(L : ℝ)) := Real.log_nonneg hscale
        have hD3 : 3 ≤ D := by linarith
        have hprod := mul_le_mul_of_nonneg_right hD3 hlogscale
        nlinarith [mul_nonneg hLp.le
          (show 0 ≤ D*(1+Real.log (σ^2*(L : ℝ))) -
            (7+3*(Real.log (C+1)+Real.log (σ^2*(L : ℝ)))) by nlinarith)]
  calc
    _ ≤ C*(L : ℝ)^2 * _ := hvariance L hL σ hσ
    _ ≤ C*(L : ℝ)^2 * Real.exp (D*(1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ)) :=
      mul_le_mul_of_nonneg_left hseries (by positivity)
    _ ≤ D*(L : ℝ)^2 * Real.exp (D*(1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ)) := by gcongr

/-- The nonzero diagonal orthogonality integral supplies square integrability. Given [the displayed inputs and assumptions](hyp:hherm,j), [the stated mathematical conclusion holds](goal). -/
lemma hermite_memLp_two (hherm : ClassicalHermiteFacts) (j : ℕ) :
    MemLp (fun z : ℝ => (Polynomial.aeval z (Polynomial.hermite j) : ℝ)) 2
      (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  by_contra hn
  have hz := integral_undef hn
  have hd := hherm.2.1 j j
  simp only [pow_two] at hz
  rw [hz, if_pos rfl] at hd
  have hp : (0 : ℝ) < (Nat.factorial j : ℝ) := by positivity
  linarith

/-- The constant Hermite mode extracts the Gaussian mean of every mode. Given [the displayed inputs and assumptions](hyp:hherm,j), [the stated mathematical conclusion holds](goal). -/
lemma hermite_gaussian_mean (hherm : ClassicalHermiteFacts) (j : ℕ) :
    (∫ z, (Polynomial.aeval z (Polynomial.hermite j) : ℝ) ∂gaussianReal 0 1) =
      if j = 0 then 1 else 0 := by
  have h := hherm.2.1 j 0
  rw [hherm.2.2] at h
  simp only [map_one, mul_one] at h
  split_ifs with hj
  · subst j
    simpa using h
  · simpa [hj] using h

/-- A finite Hermite series has mean equal to its constant coefficient. Given [the displayed inputs and assumptions](hyp:hherm,c,N,hN), [the stated mathematical conclusion holds](goal). -/
lemma hermite_finite_sum_mean (hherm : ClassicalHermiteFacts) (c : ℕ → ℝ)
    (N : ℕ) (hN : 0 < N) :
    (∫ z, ∑ j ∈ Finset.range N,
      c j * (Polynomial.aeval z (Polynomial.hermite j) : ℝ) ∂gaussianReal 0 1) = c 0 := by
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, hermite_gaussian_mean hherm]
    simp [mul_ite, hN]
  · intro j hj
    exact ((hermite_memLp_two hherm j).integrable (by norm_num)).const_mul _

/-- Orthogonality removes all cross terms in the square of a finite Hermite series. Given [the displayed inputs and assumptions](hyp:hherm,c,N), [the stated mathematical conclusion holds](goal). -/
lemma hermite_finite_sum_square (hherm : ClassicalHermiteFacts) (c : ℕ → ℝ) (N : ℕ) :
    (∫ z, (∑ j ∈ Finset.range N,
      c j * (Polynomial.aeval z (Polynomial.hermite j) : ℝ))^2 ∂gaussianReal 0 1) =
      ∑ j ∈ Finset.range N, (c j)^2 * (Nat.factorial j : ℝ) := by
  have hint (j k : ℕ) : Integrable (fun z : ℝ =>
      c j * (Polynomial.aeval z (Polynomial.hermite j) : ℝ) *
        (c k * (Polynomial.aeval z (Polynomial.hermite k) : ℝ))) (gaussianReal 0 1) := by
    exact
      ((hermite_memLp_two hherm j).const_mul (c j)).integrable_mul
        ((hermite_memLp_two hherm k).const_mul (c k))
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum _ (fun j hj => integrable_finset_sum _ (fun k hk => hint j k))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finset_sum _ (fun k hk => hint j k)]
  have he (k : ℕ) :
      (∫ z, c j * (Polynomial.aeval z (Polynomial.hermite j) : ℝ) *
        (c k * (Polynomial.aeval z (Polynomial.hermite k) : ℝ)) ∂gaussianReal 0 1) =
      c j * c k * (if j = k then (Nat.factorial j : ℝ) else 0) := by
    calc
      _ = ∫ z, (c j * c k) * ((Polynomial.aeval z (Polynomial.hermite j) : ℝ) *
          Polynomial.aeval z (Polynomial.hermite k)) ∂gaussianReal 0 1 := by
        congr 1
        funext z
        ring
      _ = _ := by rw [integral_const_mul, hherm.2.1]
  simp_rw [he]
  simp [mul_ite, Finset.mem_range.mp hj, pow_two]

/-- Exact inverse-heat mean, exact second moment, and absolute factorial covariance envelope. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
-- @node: lem:exact-covariance
lemma exact_covariance :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L → ∀ σ ∈ Icc (0 : ℝ) 1,
      (∀ x : ℝ,
        (∫ z, (inverseHeat L σ).eval (x + σ*z) ∂gaussianReal 0 1) = (endpointKernel L).eval x ∧
        (∫ z, ((inverseHeat L σ).eval (x + σ*z))^2 ∂gaussianReal 0 1) =
          ∑ j ∈ Finset.range (kernelDegree L + 1),
            σ^(2*j) * ((polyDeriv j (endpointKernel L)).eval x)^2 / (Nat.factorial j : ℝ)) ∧
      kernelVariance L σ ≤ C * (L : ℝ)^2 *
        ∑ j ∈ Finset.range (kernelDegree L + 1),
          (C * σ^2 * (L : ℝ)^4)^j / (Nat.factorial j : ℝ)^3 := by
  let hermite_of_gate : ClassicalHermiteFacts := classicalHermiteFacts
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  obtain ⟨C, hC, hvariance⟩ := kernelVariance_factorial_envelope legendre_of_gate
  refine ⟨C, hC, ?_⟩
  intro L hL σ hσ
  refine ⟨?_, hvariance L hL σ hσ⟩
  by_cases hzero : σ = 0
  · subst σ
    exact inverseHeat_zero_covariance L
  · intro x
    have hexp : ∀ z : ℝ, (inverseHeat L σ).eval (x + σ*z) =
        ∑ j ∈ Finset.range (kernelDegree L + 1),
          (σ^j * (polyDeriv j (endpointKernel L)).eval x / (Nat.factorial j : ℝ)) *
            (Polynomial.aeval z (Polynomial.hermite j) : ℝ) := by
      intro z
      rw [inverseHeat_eq_finiteInverseHeat]
      exact finiteInverseHeat_hermite_expansion (endpointKernel L) (kernelDegree L)
        (endpointKernel_natDegree_le L) x σ z
    constructor
    · simp_rw [hexp]
      simpa [polyDeriv] using hermite_finite_sum_mean hermite_of_gate
        (fun j => σ^j * (polyDeriv j (endpointKernel L)).eval x /
          (Nat.factorial j : ℝ)) (kernelDegree L + 1) (by omega)
    · simp_rw [hexp]
      rw [hermite_finite_sum_square hermite_of_gate]
      apply Finset.sum_congr rfl
      intro j hj
      have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
      rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm j 2]
      field_simp
/-- An absolute exponential cost envelope for the exact public variance. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
-- @node: lem:variance-cost-envelope
lemma variance_cost_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L → ∀ σ ∈ Icc (0 : ℝ) 1,
      kernelVariance L σ ≤ C * (L : ℝ)^2 *
        Real.exp (C * (1 + noiseCost ((L : ℝ) ^ (-2 : ℝ)) σ)) := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  obtain ⟨D, hD, hnoncompact⟩ := kernelVariance_noncompact_noise_envelope legendre_of_gate
  obtain ⟨E, hE, hcompact⟩ := kernelVariance_compact_noise_envelope legendre_of_gate
  let C : ℝ := max D E
  have hDC : D ≤ C := le_max_left _ _
  have hEC : E ≤ C := le_max_right _ _
  refine ⟨C, lt_of_lt_of_le hD hDC, ?_⟩
  intro L hL σ hσ
  have hcost := endpoint_noiseCost_factor_nonneg L hL σ hσ.1
  have henlarge (A : ℝ) (hA : 0 < A) (hAC : A ≤ C) :
      A*(L : ℝ)^2 * Real.exp (A*(1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ)) ≤
        C*(L : ℝ)^2 * Real.exp (C*(1 + noiseCost ((L : ℝ)^(-2 : ℝ)) σ)) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hAC (sq_nonneg _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAC hcost)
    · positivity
    · positivity
  by_cases hsmall : σ ≤ (L : ℝ)^(-2 : ℝ)
  · exact (hnoncompact L hL σ hσ (Or.inl hsmall)).trans (henlarge D hD hDC)
  · by_cases hpower : σ^4 ≤ (L : ℝ)^(-2 : ℝ)
    · exact (hnoncompact L hL σ hσ (Or.inr hpower)).trans (henlarge D hD hDC)
    · exact (hcompact L hL σ hσ hsmall hpower).trans (henlarge E hE hEC)

end CausalSmith.Stat.RdTruesideNoiseFrontier
