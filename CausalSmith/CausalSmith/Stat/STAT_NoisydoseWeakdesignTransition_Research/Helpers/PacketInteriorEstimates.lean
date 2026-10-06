module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketDerivativeAssembly

/-! Interior angular geometry and taper estimates for the P15 localization step. -/
public section
set_option linter.style.longLine false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The cosine Lipschitz bound turns interior angular decay into dose decay (P15). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packet_interior_angular_lower
lemma packet_interior_angular_lower (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    |u| ≤ jacobiAngularDistance 0 u := by
  have h := Real.abs_cos_sub_cos_le (Real.arccos 0) (Real.arccos u)
  simpa only [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1),
    Real.cos_arccos hu.1 hu.2, zero_sub, abs_neg, jacobiAngularDistance] using h

/-- The symmetric regularized weight dominates the sixth power of the taper (P15). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packet_interior_taper_weight_lower
lemma packet_interior_taper_weight_lower (m : ℕ) (u : ℝ)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (1-u^2)^6 ≤ jacobiRegularizedWeight 4 4 m u := by
  have he : 0 ≤ (m : ℝ)^(-2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hD : 0 ≤ 1-u^2 := by nlinarith [hu.1, hu.2]
  have hD1 : 1-u^2 ≤ 1 := by nlinarith [sq_nonneg u]
  rw [jacobiRegularizedWeight, ← Real.mul_rpow (by linarith [hu.2] : 0 ≤ 1-u+(m : ℝ)^(-2 : ℝ))
    (by linarith [hu.1] : 0 ≤ 1+u+(m : ℝ)^(-2 : ℝ))]
  calc
    _ = (1-u^2)^(6 : ℝ) := by norm_num [Real.rpow_ofNat]
    _ ≤ (1-u^2)^(4+1/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' hD hD1 (by norm_num) (by norm_num)
    _ ≤ _ := Real.rpow_le_rpow hD (by nlinarith [sq_nonneg ((m : ℝ)^(-2 : ℝ))]) (by norm_num)

/-- At the interior center the regularized weight is at least one (P15). [This is the stated conclusion](goal). -/
-- @node: packet_interior_center_weight_lower
lemma packet_interior_center_weight_lower (m : ℕ) :
    1 ≤ jacobiRegularizedWeight 4 4 m 0 := by
  have he : 0 ≤ (m : ℝ)^(-2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have h : 1 ≤ (1+(m : ℝ)^(-2 : ℝ))^(4+1/2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  simpa only [jacobiRegularizedWeight, sub_zero, add_zero, one_mul] using
    mul_le_mul h h (by norm_num : (0 : ℝ) ≤ 1) (by positivity)

/-- The cubed taper absorbs the square-root weight loss of the interior kernel (P15). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packet_interior_taper_sqrt_weight
lemma packet_interior_taper_sqrt_weight (m : ℕ) (u : ℝ)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (1-u^2)^3 ≤ Real.sqrt (jacobiRegularizedWeight 4 4 m 0 *
      jacobiRegularizedWeight 4 4 m u) := by
  apply Real.le_sqrt_of_sq_le
  have h := mul_le_mul (packet_interior_center_weight_lower m)
    (packet_interior_taper_weight_lower m u hu) (by positivity : 0 ≤ (1-u^2)^6)
    (le_trans (by norm_num) (packet_interior_center_weight_lower m))
  convert h using 1 <;> first | rfl | ring

/-- Localization and the fourth-order taper give arbitrary dose decay before normalization.
The remaining P13 task is to divide this estimate by a denominator of order m. [Under the stated conditions](hyp:hLoc,hS). [This is the stated conclusion](goal). -/
-- @node: packetKernel_interior_taper_decay
lemma packetKernel_interior_taper_decay (hLoc : FilteredJacobiLocalization)
    (S : ℝ) (hS : 0 < S) :
    ∃ L : ℝ, 0 < L ∧ ∀ m : ℕ, 4 ≤ m → ∀ u ∈ Icc (-1 : ℝ) 1,
      |(1-u^2)^4 * packetKernel 0 m u| ≤
        L*m*(1+(m : ℝ)*|u|)^(-S) := by
  obtain ⟨L, hL, hlocal⟩ := hLoc 4 4 (by norm_num) (by norm_num)
    packetFilter packetFilter_smoothJacobiFilter S hS
  refine ⟨L, hL, ?_⟩
  intro m hm u hu
  let B := Real.sqrt (jacobiRegularizedWeight 4 4 m 0 * jacobiRegularizedWeight 4 4 m u)
  let Q := 1+(m : ℝ)*jacobiAngularDistance 0 u
  let R := 1+(m : ℝ)*|u|
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hB : 0 < B := Real.sqrt_pos.mpr (mul_pos
    (jacobiRegularizedWeight_pos 4 4 m (by omega) 0 (by norm_num))
    (jacobiRegularizedWeight_pos 4 4 m (by omega) u hu))
  have hD : 0 ≤ 1-u^2 := by nlinarith [hu.1, hu.2]
  have hD1 : 1-u^2 ≤ 1 := by nlinarith [sq_nonneg u]
  have ht : (1-u^2)^4 ≤ B := by
    calc
      _ ≤ (1-u^2)^3 := by nlinarith [pow_nonneg hD 3]
      _ ≤ B := packet_interior_taper_sqrt_weight m u hu
  have hR : 0 < R := by dsimp [R]; positivity
  have hRQ : R ≤ Q := by
    dsimp [R, Q]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (packet_interior_angular_lower u hu) hmp.le) 1
  have hQ : 0 < Q := lt_of_lt_of_le hR hRQ
  have hK : |packetKernel 0 m u| ≤ L*m/(B*Q^S) := by
    simpa only [packetKernel, lt_self_iff_false, if_false] using hlocal m (by omega) 0 (by norm_num) u hu
  have hpow : R^S ≤ Q^S := Real.rpow_le_rpow hR.le hRQ hS.le
  calc
    _ = (1-u^2)^4 * |packetKernel 0 m u| := by rw [abs_mul, abs_pow, abs_of_nonneg hD]
    _ ≤ (1-u^2)^4 * (L*m/(B*Q^S)) := mul_le_mul_of_nonneg_left hK (by positivity)
    _ ≤ B*(L*m/(B*Q^S)) := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = L*m/Q^S := by field_simp
    _ ≤ L*m/R^S := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hR _) hpow
    _ = _ := by rw [Real.rpow_neg hR.le]; ring

/-- The interior first derivative follows from the cited nearby-argument estimate (P15). [Under the stated conditions](hyp:hLip). [This is the stated conclusion](goal). -/
-- @node: packetKernel_interior_derivative_bound
lemma packetKernel_interior_derivative_bound (hLip : FilteredJacobiLipschitz) :
    ∃ J : ℝ, 0 < J ∧ ∀ m : ℕ, 4 ≤ m → ∀ u ∈ Ioo (-1 : ℝ) 1,
      |deriv (packetKernel 0 m) u| ≤
        (J*(m : ℝ)^2 / Real.sqrt (jacobiRegularizedWeight 4 4 m 0 *
          jacobiRegularizedWeight 4 4 m u)) * (1/Real.sqrt (1-u^2)) := by
  obtain ⟨J, hJ, hd⟩ := filteredJacobiKernel_derivative_bound hLip 4 4
    (by norm_num) (by norm_num) packetFilter packetFilter_smoothJacobiFilter 1 (by norm_num)
  refine ⟨J, hJ, ?_⟩
  intro m hm u hu
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let B := Real.sqrt (jacobiRegularizedWeight 4 4 m 0 * jacobiRegularizedWeight 4 4 m u)
  have hB : 0 < B := Real.sqrt_pos.mpr (mul_pos
    (jacobiRegularizedWeight_pos 4 4 m (by omega) 0 (by norm_num))
    (jacobiRegularizedWeight_pos 4 4 m (by omega) u ⟨hu.1.le, hu.2.le⟩))
  have hQ : 1 ≤ 1+(m : ℝ)*jacobiAngularDistance 0 u := by
    have h := mul_nonneg hmp.le (abs_nonneg (Real.arccos 0-Real.arccos u))
    unfold jacobiAngularDistance
    linarith
  have he : packetKernel 0 m = fun t => filteredJacobiKernel 4 4 packetFilter m t 0 := by
    funext t
    simp only [packetKernel, lt_self_iff_false, if_false]
    exact filteredJacobiKernel_symm _ _ _ _ _ _
  rw [he]
  have h := hd m (by omega) u hu 0 (by norm_num)
  simp only [Real.rpow_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by positivity) hB (by nlinarith)) (by positivity))

/-- The product rule for the interior packet on its open support (P15). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packetPsi_interior_derivative_formula
lemma packetPsi_interior_derivative_formula (m : ℕ) (u : ℝ)
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    deriv (packetPsi 0 m) u =
      ((-8*u*(1-u^2)^3)*packetKernel 0 m u +
        (1-u^2)^4*deriv (packetKernel 0 m) u) / packetKernel 0 m 0 := by
  have ht : HasDerivAt (fun v : ℝ => (1-v^2)^4) (-8*u*(1-u^2)^3) u := by
    have hd := ((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).pow 4
    simp only [Nat.cast_ofNat, show (4-1 : ℕ) = 3 from rfl,
      show (2-1 : ℕ) = 1 from rfl, pow_one, mul_one, zero_sub,
      Pi.pow_apply, Pi.sub_apply, id_eq] at hd
    convert hd using 1 <;> first | rfl | ring
  have hk : DifferentiableAt ℝ (packetKernel 0 m) u := ((packetKernel_contDiff 0 m).differentiable (by norm_num)).differentiableAt
  have he : packetPsi 0 m =ᶠ[𝓝 u] (fun v =>
      (1-v^2)^4*packetKernel 0 m v/packetKernel 0 m 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    rw [packetPsi, if_pos ⟨hv.1.le, hv.2.le⟩, if_neg (lt_irrefl 0)]
    ring
  rw [he.deriv_eq]
  exact ((ht.mul hk.hasDerivAt).div_const _).deriv

/-- P15 assembled after the P13 normalization estimate. The normalization premise is
an intermediate proof obligation, not a new assumption of the paper theorem. [Under the stated conditions](hyp:hLoc,hLip,hc,hnorm). [This is the stated conclusion](goal). -/
-- @node: packetinterior_bounds_of_normalization
lemma packetinterior_bounds_of_normalization (hLoc : FilteredJacobiLocalization)
    (hLip : FilteredJacobiLipschitz) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ m : ℕ, 4 ≤ m → c*m ≤ packetKernel 0 m 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 4 ≤ m →
      0 < packetKernel 0 m 0 ∧
      (∀ u, |packetPsi 0 m u| ≤ A*(1+(m : ℝ)*|u|)^(-(0+2 : ℝ))) ∧
      (∀ u, |deriv (packetPsi 0 m) u| ≤ A*m) := by
  obtain ⟨L, hL, hdecay⟩ := packetKernel_interior_taper_decay hLoc 2 (by norm_num)
  obtain ⟨K, hK, hlocal⟩ := hLoc 4 4 (by norm_num) (by norm_num)
    packetFilter packetFilter_smoothJacobiFilter 1 (by norm_num)
  obtain ⟨J, hJ, hderiv⟩ := packetKernel_interior_derivative_bound hLip
  let A := (L+8*K+J)/c
  have hA : 0 < A := by dsimp [A]; positivity
  have hLA : L/c ≤ A := by dsimp [A]; apply div_le_div_of_nonneg_right _ hc.le; linarith
  have hJA : (8*K+J)/c ≤ A := by dsimp [A]; apply div_le_div_of_nonneg_right _ hc.le; linarith
  refine ⟨A, hA, ?_⟩
  intro m hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  let N := packetKernel 0 m 0
  have hN : 0 < N := lt_of_lt_of_le (mul_pos hc hmp) (hnorm m hm)
  refine ⟨hN, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · have h := hdecay m hm u hu
      have hp : 0 ≤ (1+(m : ℝ)*|u|)^(-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
      calc
        |packetPsi 0 m u| = |(1-u^2)^4*packetKernel 0 m u|/N := by
          rw [packetPsi, if_pos hu, if_neg (lt_irrefl 0)]
          rw [← mul_div_assoc, abs_div, abs_of_pos hN]
        _ ≤ (L*m*(1+(m : ℝ)*|u|)^(-(2 : ℝ)))/N := div_le_div_of_nonneg_right h hN.le
        _ ≤ (L/c)*(1+(m : ℝ)*|u|)^(-(2 : ℝ)) := by
          apply (div_le_iff₀ hN).mpr
          calc
            _ = ((L/c)*(1+(m : ℝ)*|u|)^(-(2 : ℝ)))*(c*m) := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left (hnorm m hm) (by positivity)
        _ ≤ _ := by norm_num only; exact mul_le_mul_of_nonneg_right hLA hp
    · rw [packetPsi_support 0 m u hu, abs_zero]
      positivity
  · have hinterior : ∀ u ∈ Ioo (-1 : ℝ) 1,
        |deriv (packetPsi 0 m) u| ≤ A*m := by
      intro u hu
      let D := 1-u^2
      let B := Real.sqrt (jacobiRegularizedWeight 4 4 m 0 * jacobiRegularizedWeight 4 4 m u)
      have hD : 0 < D := by dsimp [D]; nlinarith [hu.1, hu.2]
      have hD1 : D ≤ 1 := by dsimp [D]; nlinarith [sq_nonneg u]
      have huabs : |u| ≤ 1 := abs_le.mpr ⟨hu.1.le, hu.2.le⟩
      have hB : 0 < B := Real.sqrt_pos.mpr (mul_pos
        (jacobiRegularizedWeight_pos 4 4 m (by omega) 0 (by norm_num))
        (jacobiRegularizedWeight_pos 4 4 m (by omega) u ⟨hu.1.le, hu.2.le⟩))
      have htB : D^3/B ≤ 1 := (div_le_iff₀ hB).mpr (by
        simpa using packet_interior_taper_sqrt_weight m u ⟨hu.1.le, hu.2.le⟩)
      have hQ : 1 ≤ 1+(m : ℝ)*jacobiAngularDistance 0 u := by
        have h := mul_nonneg hmp.le (abs_nonneg (Real.arccos 0-Real.arccos u))
        unfold jacobiAngularDistance
        linarith
      have hkernel : |packetKernel 0 m u| ≤ K*m/B := by
        have h := hlocal m (by omega) 0 (by norm_num) u ⟨hu.1.le, hu.2.le⟩
        simp only [Real.rpow_one] at h
        have h' : |packetKernel 0 m u| ≤ K*m/(B*(1+m*jacobiAngularDistance 0 u)) := by
          simpa only [packetKernel, lt_self_iff_false, if_false] using h
        exact h'.trans (div_le_div_of_nonneg_left (by positivity) hB (by nlinarith))
      have hd := hderiv m hm u hu
      have htaper : D^4/Real.sqrt D ≤ D^3 := by
        have hs : D ≤ Real.sqrt D := by apply Real.le_sqrt_of_sq_le; nlinarith
        apply (div_le_iff₀ (Real.sqrt_pos.mpr hD)).mpr
        calc
          D^4 = D^3*D := by ring
          _ ≤ D^3*Real.sqrt D := mul_le_mul_of_nonneg_left hs (by positivity)
      calc
        |deriv (packetPsi 0 m) u| ≤
            (8*D^3*|packetKernel 0 m u| + D^4*|deriv (packetKernel 0 m) u|)/N := by
          rw [packetPsi_interior_derivative_formula m u hu, abs_div, abs_of_pos hN]
          apply div_le_div_of_nonneg_right _ hN.le
          calc
            _ ≤ |(-8*u*(1-u^2)^3)*packetKernel 0 m u| +
                |(1-u^2)^4*deriv (packetKernel 0 m) u| := abs_add_le _ _
            _ = 8*|u| *D^3*|packetKernel 0 m u| + D^4*|deriv (packetKernel 0 m) u| := by
              have hab : |1-u^2| = D := abs_of_pos hD
              simp only [abs_mul, abs_pow, hab]
              norm_num
            _ ≤ _ := by gcongr; linarith
        _ ≤ (8*D^3*(K*m/B) + D^4*((J*(m : ℝ)^2/B)*(1/Real.sqrt D)))/N := by gcongr
        _ = (8*K*m*(D^3/B) + J*(m : ℝ)^2/B*(D^4/Real.sqrt D))/N := by ring
        _ ≤ (8*K*m+J*(m : ℝ)^2)/N := by
          apply div_le_div_of_nonneg_right _ hN.le
          apply add_le_add
          · simpa using mul_le_mul_of_nonneg_left htB (show 0 ≤ 8*K*m by positivity)
          · calc
              _ ≤ J*(m : ℝ)^2/B*D^3 := mul_le_mul_of_nonneg_left htaper (by positivity)
              _ = J*(m : ℝ)^2*(D^3/B) := by ring
              _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left htB (show 0 ≤ J*(m : ℝ)^2 by positivity)
        _ ≤ ((8*K+J)/c)*m := by
          apply (div_le_iff₀ hN).mpr
          calc
            _ ≤ (8*K+J)*(m : ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 8*K*m by positivity)]
            _ = (((8*K+J)/c)*m)*(c*m) := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left (hnorm m hm) (by positivity)
        _ ≤ A*m := mul_le_mul_of_nonneg_right hJA hmp.le
    have hdense : Dense ({(-1 : ℝ), 1} : Set ℝ)ᶜ :=
      (Set.toFinite _).countable.dense_compl ℝ
    have hbound : ∀ u ∈ ({(-1 : ℝ), 1} : Set ℝ)ᶜ,
        |deriv (packetPsi 0 m) u| ≤ A*m := by
      intro u hu
      have hex : u ≠ -1 ∧ u ≠ 1 := by simpa using hu
      by_cases hi : u ∈ Icc (-1 : ℝ) 1
      · exact hinterior u ⟨lt_of_le_of_ne hi.1 hex.1.symm, lt_of_le_of_ne hi.2 hex.2⟩
      · rw [packetPsi_derivative_outside 0 m u hi, abs_zero]
        positivity
    intro u
    exact le_on_closure hbound (packetPsi_contDiff 0 m).continuous_deriv_one.abs.continuousOn
      continuous_const.continuousOn (hdense u)

end CausalSmith.Stat.NoisydoseWeakdesignTransition
