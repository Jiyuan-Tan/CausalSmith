module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.FourierBridge
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.TorusGeometry

/-!
# Pointwise and integral localization of Jackson packets

Discrete second variation controls decay away from the center, and the
resulting envelope yields the normalized integral bound.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

open MeasureTheory

private theorem finiteFourier_norm_le (a : ℤ → ℝ)
    (ha : Function.HasFiniteSupport a) (u : ℝ) :
    ‖finiteFourier (fun j => (a j : ℂ)) u‖ ≤ ∑' j : ℤ, |a j| := by
  have hs : Summable (fun j : ℤ =>
      ‖(a j : ℂ) * Complex.exp (Complex.I * (j : ℂ) * (u : ℂ))‖) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset ha
    intro j hj
    simpa only [Function.mem_support, ne_eq, norm_eq_zero, mul_eq_zero,
      Complex.exp_ne_zero, or_false, Complex.ofReal_eq_zero] using hj
  have hphase (j : ℤ) :
      ‖Complex.exp (Complex.I * (j : ℂ) * (u : ℂ))‖ = 1 := by
    rw [show Complex.I * (j : ℂ) * (u : ℂ) =
      (((j : ℝ) * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  simpa only [finiteFourier, norm_mul, Complex.norm_real, hphase, mul_one,
    Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs

private theorem weightedCoeff_finite (N : ℕ) (σ : ℝ) :
    Function.HasFiniteSupport (weightedCoeff N σ) := by
  apply (Finset.finite_toSet (Finset.Icc
    (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ))).subset
  intro j hj
  by_contra hn
  have hout : ((2 * N - 2 : ℕ) : ℤ) < |j| := by
    simp only [SetLike.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · have := neg_le_abs j; omega
    · have := le_abs_self j; omega
  exact hj (weightedCoeff_support N σ j hout)

private theorem weightedCoeff_delta2_finite (N : ℕ) (σ : ℝ) :
    Function.HasFiniteSupport (delta2 (weightedCoeff N σ)) := by
  have ha := weightedCoeff_finite N σ
  have h1 : Function.HasFiniteSupport (fun j : ℤ => weightedCoeff N σ (j + 1)) :=
    ha.fun_comp_of_injective (Equiv.addRight (1 : ℤ)).injective
  have h2 : Function.HasFiniteSupport (fun j : ℤ => weightedCoeff N σ (j + 2)) :=
    ha.fun_comp_of_injective (Equiv.addRight (2 : ℤ)).injective
  have hh := (h2.sub h1).sub (h1.sub ha)
  have heq : delta2 (weightedCoeff N σ) =
      ((fun j : ℤ => weightedCoeff N σ (j + 2)) -
       (fun j : ℤ => weightedCoeff N σ (j + 1))) -
      ((fun j : ℤ => weightedCoeff N σ (j + 1)) - weightedCoeff N σ) := by
    funext j
    simp only [delta2, delta, Pi.sub_apply]
    rw [show j + 1 + 1 = j + 2 by omega]
  rw [heq]
  exact hh

private theorem normalizedCoeff_finite (N : ℕ) :
    Function.HasFiniteSupport (normalizedCoeff N) := by
  apply (Finset.finite_toSet (Finset.Icc
    (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ))).subset
  intro j hj
  by_contra hn
  have hout : ((2 * N - 2 : ℕ) : ℤ) < |j| := by
    simp only [SetLike.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · have := neg_le_abs j; omega
    · have := le_abs_self j; omega
  exact hj (normalizedCoeff_support N j hout)

private theorem weightedCoeff_l1 (N : ℕ) (hN : 2 ≤ N) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    (∑' j : ℤ, |weightedCoeff N σ j|) ≤ 2 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpoint (j : ℤ) :
      |weightedCoeff N σ j| ≤ (1 / (N : ℝ) ^ 2) * |normalizedCoeff N j| := by
    by_cases hj : |j| ≤ (2 * N : ℕ)
    · rw [weightedCoeff, abs_mul]
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left (reciprocalSquare_bound N hN σ hσ j hj)
          (abs_nonneg (normalizedCoeff N j)))
    · have hout : ((2 * N - 2 : ℕ) : ℤ) < |j| := by omega
      simp [weightedCoeff_support N σ j hout,
        normalizedCoeff_support N j hout]
  have hs : Summable (weightedCoeff N σ) :=
    summable_of_hasFiniteSupport (weightedCoeff_finite N σ)
  have hnS : Summable (normalizedCoeff N) :=
    summable_of_hasFiniteSupport (normalizedCoeff_finite N)
  have hmain := (hs.abs).tsum_le_tsum hpoint ((hnS.abs).mul_left _)
  rw [tsum_mul_left] at hmain
  have hmass := normalizedCoeff_l1 N (by omega : 0 < N)
  calc
    _ ≤ (1 / (N : ℝ) ^ 2) * (∑' j : ℤ, |normalizedCoeff N j|) := hmain
    _ ≤ (1 / (N : ℝ) ^ 2) * (2 * (N : ℝ)) := by gcongr
    _ = 2 / (N : ℝ) := by field_simp

private theorem packet_abs_le_fourier (N : ℕ) (u : ℝ) :
    |packetAntideriv N u| ≤
      (‖finiteFourier (fun j => (packetCoeffPlus N j : ℂ)) u‖ +
       ‖finiteFourier (fun j => (packetCoeffMinus N j : ℂ)) (-u)‖) / 2 := by
  let z : ℂ := Complex.exp (Complex.I * (4 * (N : ℝ) * u : ℂ))
  let p : ℂ := finiteFourier (fun j => (packetCoeffPlus N j : ℂ)) u
  let m : ℂ := finiteFourier (fun j => (packetCoeffMinus N j : ℂ)) (-u)
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    simp [Complex.norm_exp, Complex.mul_re]
  rw [packetAntideriv_eq_finiteFourier]
  change |-(1 / 2 : ℝ) * ((z * p).re + (z * m).re)| ≤ (‖p‖ + ‖m‖) / 2
  have hp : |(z * p).re| ≤ ‖p‖ := by
    calc
      _ ≤ ‖z * p‖ := Complex.abs_re_le_norm _
      _ = ‖p‖ := by rw [norm_mul, hz, one_mul]
  have hm : |(z * m).re| ≤ ‖m‖ := by
    calc
      _ ≤ ‖z * m‖ := Complex.abs_re_le_norm _
      _ = ‖m‖ := by rw [norm_mul, hz, one_mul]
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hsum := abs_add_le (z * p).re (z * m).re
  nlinarith

private theorem weightedCoeff_fourier_far (N : ℕ) (hN : 2 ≤ N)
    (σ v : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hd : 0 < torusDistance v) :
    ‖finiteFourier (fun j => (weightedCoeff N σ j : ℂ)) v‖ ≤
      2048 / ((N : ℝ) ^ 3 * torusDistance v ^ 2) := by
  let a : ℤ → ℂ := fun j => (weightedCoeff N σ j : ℂ)
  let g : ℂ := Complex.exp (-Complex.I * (v : ℂ)) - 1
  have ha : Function.HasFiniteSupport a := by
    apply Set.Finite.subset (weightedCoeff_finite N σ)
    intro j hj
    simpa [a] using hj
  have hdelta : complexDelta2 a =
      (fun j => (delta2 (weightedCoeff N σ) j : ℂ)) := by
    funext j
    simp only [complexDelta2, delta2, delta, a]
    push_cast
    ring_nf
  have hdFinite := weightedCoeff_delta2_finite N σ
  have hsum := finiteFourier_norm_le (delta2 (weightedCoeff N σ)) hdFinite v
  have hFourier := finiteFourier_twice_summation_by_parts a ha v
  rw [← hdelta] at hsum
  rw [hFourier, norm_mul, norm_pow] at hsum
  have hvariation := weightedCoeff_delta2_l1 N hN σ hσ
  have hbound : ‖g‖ ^ 2 * ‖finiteFourier a v‖ ≤ 512 / (N : ℝ) ^ 3 :=
    hsum.trans hvariation
  have hgap0 := character_gap_ge_torusDistance v
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hgap : torusDistance v / 2 ≤ ‖g‖ := by
    change _ ≤ ‖Complex.exp (-Complex.I * (v : ℂ)) - 1‖
    have hratio : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      apply (le_div_iff₀ hpi).mpr
      nlinarith [Real.pi_le_four]
    nlinarith [mul_le_mul_of_nonneg_right hratio (le_of_lt hd)]
  have hsq : (torusDistance v / 2) ^ 2 ≤ ‖g‖ ^ 2 := by gcongr
  have hpos : 0 < (torusDistance v / 2) ^ 2 := by positivity
  have hF : ‖finiteFourier a v‖ ≤
      (512 / (N : ℝ) ^ 3) / (torusDistance v / 2) ^ 2 := by
    apply (le_div_iff₀ hpos).mpr
    calc
      ‖finiteFourier a v‖ * (torusDistance v / 2) ^ 2 ≤
          ‖finiteFourier a v‖ * ‖g‖ ^ 2 := by gcongr
      _ = ‖g‖ ^ 2 * ‖finiteFourier a v‖ := by ring
      _ ≤ _ := hbound
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  change ‖finiteFourier a v‖ ≤ _
  calc
    _ ≤ _ := hF
    _ = 2048 / ((N : ℝ) ^ 3 * torusDistance v ^ 2) := by
      field_simp
      ring

private theorem torusDistance_neg (u : ℝ) :
    torusDistance (-u) = torusDistance u := by
  unfold torusDistance
  congr 1
  ext r
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨-j, ?_⟩
    push_cast
    rw [show -u - 2 * Real.pi * (j : ℝ) =
      -(u - 2 * Real.pi * (-(j : ℝ))) by ring, abs_neg]
  · rintro ⟨j, rfl⟩
    refine ⟨-j, ?_⟩
    push_cast
    rw [show -u - 2 * Real.pi * (-(j : ℝ)) =
      -(u - 2 * Real.pi * (j : ℝ)) by ring, abs_neg]

private theorem integral_rational_envelope (N : ℕ) (hN : 0 < N) :
    (∫ u in Set.Icc (-Real.pi) Real.pi,
      1 / (1 + ((N : ℝ) * u) ^ 2)) ≤ Real.pi / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hpi]
  have hcalc : (∫ u in -Real.pi..Real.pi,
      1 / (1 + ((N : ℝ) * u) ^ 2)) =
      (N : ℝ)⁻¹ * (Real.arctan ((N : ℝ) * Real.pi) -
        Real.arctan ((N : ℝ) * -Real.pi)) := by
    convert intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => 1 / (1 + x ^ 2)) (ne_of_gt hn)
      (a := -Real.pi) (b := Real.pi) using 1
    · simp only [smul_eq_mul]
      rw [integral_one_div_one_add_sq]
  rw [hcalc]
  have hdiff : Real.arctan ((N : ℝ) * Real.pi) -
      Real.arctan ((N : ℝ) * -Real.pi) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two ((N : ℝ) * Real.pi),
      Real.neg_pi_div_two_lt_arctan ((N : ℝ) * -Real.pi)]
  have := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hn.le)
  simpa [div_eq_mul_inv, mul_comm] using this

/-- [There is a positive constant C such that, for every order N at least two and every real angle
u, the packet antiderivative at u is at most C divided by N times the square of (1 + N times the
torus distance of u), in absolute value](goal). -/
theorem packet_pointwise_localization :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ u : ℝ,
        |packetAntideriv N u| ≤
          C / ((N : ℝ) * (1 + (N : ℝ) * torusDistance u) ^ 2) := by
  refine ⟨8192, by norm_num, ?_⟩
  intro N hN u
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let d := torusDistance u
  have hd : 0 ≤ d := (torusDistance_bounds u).1
  have hden : 0 < (N : ℝ) * (1 + (N : ℝ) * d) ^ 2 := by positivity
  have hp := finiteFourier_norm_le (weightedCoeff N 1)
    (weightedCoeff_finite N 1) u
  have hm := finiteFourier_norm_le (weightedCoeff N (-1))
    (weightedCoeff_finite N (-1)) (-u)
  have hnear : |packetAntideriv N u| ≤ 2 / (N : ℝ) := by
    calc
      _ ≤ (‖finiteFourier (fun j => (packetCoeffPlus N j : ℂ)) u‖ +
           ‖finiteFourier (fun j => (packetCoeffMinus N j : ℂ)) (-u)‖) / 2 :=
        packet_abs_le_fourier N u
      _ ≤ ((∑' j : ℤ, |weightedCoeff N 1 j|) +
           (∑' j : ℤ, |weightedCoeff N (-1) j|)) / 2 := by
        dsimp [packetCoeffPlus, packetCoeffMinus]
        gcongr
      _ ≤ 2 / (N : ℝ) := by
        have hp' := weightedCoeff_l1 N hN 1 (Or.inl rfl)
        have hm' := weightedCoeff_l1 N hN (-1) (Or.inr rfl)
        linarith
  by_cases hsmall : (N : ℝ) * d ≤ 1
  · calc
      |packetAntideriv N u| ≤ 2 / (N : ℝ) := hnear
      _ ≤ 8192 / ((N : ℝ) * (1 + (N : ℝ) * d) ^ 2) := by
        have hsq : (1 + (N : ℝ) * d) ^ 2 ≤ 4 := by
          have hnd : 0 ≤ (N : ℝ) * d := mul_nonneg hn.le hd
          nlinarith [mul_le_mul_of_nonneg_left hsmall hnd]
        apply (div_le_div_iff₀ hn hden).mpr
        nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hn)]
  · have hlarge : 1 ≤ (N : ℝ) * d := by linarith
    have hdpos : 0 < d := by nlinarith
    have hfplus := weightedCoeff_fourier_far N hN 1 u (Or.inl rfl) hdpos
    have hfminus := weightedCoeff_fourier_far N hN (-1) (-u) (Or.inr rfl)
      (by simpa only [torusDistance_neg] using hdpos)
    have hfar : |packetAntideriv N u| ≤
        2048 / ((N : ℝ) ^ 3 * d ^ 2) := by
      calc
        _ ≤ (‖finiteFourier (fun j => (packetCoeffPlus N j : ℂ)) u‖ +
             ‖finiteFourier (fun j => (packetCoeffMinus N j : ℂ)) (-u)‖) / 2 :=
          packet_abs_le_fourier N u
        _ ≤ (2048 / ((N : ℝ) ^ 3 * d ^ 2) +
             2048 / ((N : ℝ) ^ 3 * d ^ 2)) / 2 := by
          dsimp [packetCoeffPlus, packetCoeffMinus]
          rw [torusDistance_neg] at hfminus
          exact div_le_div_of_nonneg_right (add_le_add hfplus hfminus) (by norm_num)
        _ = _ := by ring
    calc
      |packetAntideriv N u| ≤ 2048 / ((N : ℝ) ^ 3 * d ^ 2) := hfar
      _ ≤ 8192 / ((N : ℝ) * (1 + (N : ℝ) * d) ^ 2) := by
        have hsq : (1 + (N : ℝ) * d) ^ 2 ≤ 4 * ((N : ℝ) * d) ^ 2 := by
          nlinarith [sq_nonneg ((N : ℝ) * d - 1)]
        apply (div_le_div_iff₀ (by positivity) hden).mpr
        nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hn)]

/-- [There is a positive constant C such that, for every order N at least two, the integral over
the period from −π to π of the absolute value of the packet antiderivative divided by 2π is at most
C / N²](goal). -/
theorem packet_l1_localization :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N →
        (∫ u in Set.Icc (-Real.pi) Real.pi,
          |packetAntideriv N u| / (2 * Real.pi)) ≤ C / (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, hlocal⟩ := packet_pointwise_localization
  refine ⟨C / 2, by positivity, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  let f : ℝ → ℝ := fun u => |packetAntideriv N u| / (2 * Real.pi)
  let g : ℝ → ℝ := fun u =>
    (C / ((N : ℝ) * (2 * Real.pi))) *
      (1 / (1 + ((N : ℝ) * u) ^ 2))
  have hcf : Continuous f := by
    dsimp [f, packetAntideriv]
    fun_prop
  have hcg : Continuous g := by
    dsimp [g]
    have hb : Continuous (fun u : ℝ => 1 + ((N : ℝ) * u) ^ 2) := by fun_prop
    have hr := hb.inv₀ (by intro u; positivity)
    have hc : Continuous (fun _ : ℝ => C / ((N : ℝ) * (2 * Real.pi))) :=
      continuous_const
    convert (hc.mul hr) using 1
    funext u
    simp [Pi.mul_apply, one_div]
  have hf : IntegrableOn f (Set.Icc (-Real.pi) Real.pi) :=
    hcf.continuousOn.integrableOn_compact isCompact_Icc
  have hg : IntegrableOn g (Set.Icc (-Real.pi) Real.pi) :=
    hcg.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint (u : ℝ) (hu : u ∈ Set.Icc (-Real.pi) Real.pi) : f u ≤ g u := by
    have huabs : |u| ≤ Real.pi := abs_le.mpr ⟨hu.1, hu.2⟩
    have hloc := hlocal N hN u
    rw [torusDistance_eq_abs u huabs] at hloc
    have hx : 0 ≤ (N : ℝ) * |u| := mul_nonneg hn.le (abs_nonneg _)
    have hden : 0 < (N : ℝ) * (1 + (N : ℝ) * |u|) ^ 2 := by positivity
    have hrat : 1 / (1 + (N : ℝ) * |u|) ^ 2 ≤
        1 / (1 + ((N : ℝ) * u) ^ 2) := by
      have hsq : 1 + ((N : ℝ) * u) ^ 2 ≤
          (1 + (N : ℝ) * |u|) ^ 2 := by
        have heq : ((N : ℝ) * u) ^ 2 = ((N : ℝ) * |u|) ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]
        rw [heq]
        nlinarith [hx]
      exact one_div_le_one_div_of_le (by positivity) hsq
    dsimp [f, g]
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have hconst : 0 ≤ C / ((N : ℝ) * (2 * Real.pi)) := by positivity
    calc
      |packetAntideriv N u| / (2 * Real.pi) ≤
          (C / ((N : ℝ) * (1 + (N : ℝ) * |u|) ^ 2)) /
            (2 * Real.pi) := by exact div_le_div_of_nonneg_right hloc hp.le
      _ = (C / ((N : ℝ) * (2 * Real.pi))) *
            (1 / (1 + (N : ℝ) * |u|) ^ 2) := by
              field_simp [ne_of_gt hn, ne_of_gt hpi,
                show 1 + (N : ℝ) * |u| ≠ 0 by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrat hconst
  have hmono := MeasureTheory.setIntegral_mono_on hf hg measurableSet_Icc hpoint
  change (∫ u in Set.Icc (-Real.pi) Real.pi,
    |packetAntideriv N u| / (2 * Real.pi)) ≤ _ at hmono
  have hr := integral_rational_envelope N (by omega : 0 < N)
  dsimp [g] at hmono
  rw [MeasureTheory.integral_const_mul] at hmono
  have hbound : (C / ((N : ℝ) * (2 * Real.pi))) *
      (∫ u in Set.Icc (-Real.pi) Real.pi,
        1 / (1 + ((N : ℝ) * u) ^ 2)) ≤
      (C / ((N : ℝ) * (2 * Real.pi))) *
      (Real.pi / (N : ℝ)) := by gcongr
  calc
    _ ≤ _ := hmono
    _ ≤ _ := hbound
    _ = (C / 2) / (N : ℝ) ^ 2 := by field_simp

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

