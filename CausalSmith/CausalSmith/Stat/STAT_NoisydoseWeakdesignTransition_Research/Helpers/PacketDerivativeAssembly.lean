module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketDerivative
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketEndpointFacts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Algebra.Module.Cardinality

/-! Taper and normalization assembly for the global packet derivative bound (P10). -/
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- On the open support, differentiating the taper and the polynomial kernel gives
both terms of the product rule in (P10). [Under the stated conditions](hyp:hkappa,hu). [This is the stated conclusion](goal). -/
-- @node: packetPsi_endpoint_derivative_formula
lemma packetPsi_endpoint_derivative_formula (kappa : ℝ) (hkappa : 0 < kappa)
    (m : ℕ) (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    deriv (packetPsi kappa m) u =
      ((-8*u*(1-u^2)^3)*packetKernel kappa m (2*u^2-1) +
        (1-u^2)^4*deriv (fun v => packetKernel kappa m (2*v^2-1)) u) /
      packetKernel kappa m (-1) := by
  have ht : HasDerivAt (fun v : ℝ => (1-v^2)^4) (-8*u*(1-u^2)^3) u := by
    have hd := ((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).pow 4
    simp only [Nat.cast_ofNat, show (4-1 : ℕ) = 3 from rfl,
      show (2-1 : ℕ) = 1 from rfl, pow_one, mul_one, zero_sub, Pi.pow_apply, Pi.sub_apply, id_eq] at hd
    convert hd using 1 <;> first | rfl | ring
  have hk : DifferentiableAt ℝ (fun v => packetKernel kappa m (2*v^2-1)) u := by
    have hc : ContDiff ℝ 1 (fun v => packetKernel kappa m (2*v^2-1)) := by fun_prop
    exact (hc.differentiable (by norm_num)).differentiableAt
  have he : packetPsi kappa m =ᶠ[𝓝 u] (fun v =>
      (1-v^2)^4*packetKernel kappa m (2*v^2-1)/packetKernel kappa m (-1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    rw [packetPsi, if_pos ⟨hv.1.le, hv.2.le⟩, if_pos hkappa]
    ring
  rw [he.deriv_eq]
  exact ((ht.mul hk.hasDerivAt).div_const _).deriv

/-- Outside the closed support the packet is locally zero, hence its derivative vanishes. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hu). -/
-- @node: packetPsi_derivative_outside
lemma packetPsi_derivative_outside (kappa : ℝ) (m : ℕ) (u : ℝ)
    (hu : u ∉ Icc (-1 : ℝ) 1) : deriv (packetPsi kappa m) u = 0 := by
  have he : packetPsi kappa m =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hu] with v hv
    exact packetPsi_support kappa m v hv
  rw [he.deriv_eq, deriv_const]

/-- Normalization and the cubed taper absorb both losses in the nearby-argument derivative
bound. Continuity extends the bound to zero and the support endpoints, giving (P10) globally. [Under the stated conditions](hyp:hLoc,hLip,hNorm,hGamma,hkappa). [This is the stated conclusion](goal). -/
-- @node: packetPsi_endpoint_derivative_bound
lemma packetPsi_endpoint_derivative_bound (hLoc : FilteredJacobiLocalization)
    (hLip : FilteredJacobiLipschitz) (hNorm : JacobiNormOrthogonality)
    (hGamma : GammaRatioAsymptotic) (kappa : ℝ) (hkappa : 0 < kappa) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 4 ≤ m → ∀ u : ℝ,
      |deriv (packetPsi kappa m) u| ≤ A*m := by
  obtain ⟨c0, C0, hc0, hC0, hnorm⟩ :=
    packetKernel_endpoint_power_bounds hNorm hGamma kappa hkappa
  obtain ⟨L, hL, hlocal⟩ := hLoc 4 ((kappa-1)/2) (by norm_num) (by linarith)
    packetFilter packetFilter_smoothJacobiFilter 1 (by norm_num)
  obtain ⟨J, hJ, hderiv⟩ := packetKernel_endpoint_composed_derivative_bound hLip
    kappa hkappa 1 (by norm_num)
  let A := (8*L+2*J)/c0
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro m hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hinterior : ∀ u ∈ Ioo (-1 : ℝ) 1, u ≠ 0 →
      |deriv (packetPsi kappa m) u| ≤ A*m := by
    intro u hu hu0
    let D := 1-u^2
    let B := Real.sqrt (jacobiRegularizedWeight 4 ((kappa-1)/2) m (-1) *
      jacobiRegularizedWeight 4 ((kappa-1)/2) m (2*u^2-1))
    let Q := 1+(m : ℝ)*jacobiAngularDistance (-1) (2*u^2-1)
    let N := packetKernel kappa m (-1)
    have hD : 0 < D := by dsimp [D]; nlinarith [hu.1, hu.2]
    have hD1 : D ≤ 1 := by dsimp [D]; nlinarith [sq_nonneg u]
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨hu.1.le, hu.2.le⟩
    have hB : 0 < B := Real.sqrt_pos.mpr (mul_pos
      (jacobiRegularizedWeight_pos 4 ((kappa-1)/2) m (by omega) (-1) (by norm_num))
      (jacobiRegularizedWeight_pos 4 ((kappa-1)/2) m (by omega) _
        (packet_endpoint_coordinate_mem u ⟨hu.1.le, hu.2.le⟩)))
    have hQ : 1 ≤ Q := by
      have := abs_nonneg (Real.arccos (-1)-Real.arccos (2*u^2-1))
      dsimp [Q, jacobiAngularDistance]
      nlinarith
    have hN : 0 < N := packetKernel_endpoint_pos hNorm kappa hkappa m hm
    have hnormN : c0*((m : ℝ)^kappa*m) ≤ N := by
      simpa only [Real.rpow_add hmp, Real.rpow_one] using (hnorm m hm).1
    have htB : D^3/B ≤ (m : ℝ)^kappa := by
      apply (div_le_iff₀ hB).mpr
      have ht := mul_le_mul_of_nonneg_right
        (packet_endpoint_derivative_taper_sqrt_weight kappa hkappa.le m (by omega) u
          ⟨hu.1.le, hu.2.le⟩) (Real.rpow_nonneg hmp.le kappa)
      have he : (m : ℝ)^(-kappa)*(m : ℝ)^kappa = 1 := by
        rw [← Real.rpow_add hmp]; simp
      change (D^3*(m : ℝ)^(-kappa))*(m : ℝ)^kappa ≤ B*(m : ℝ)^kappa at ht
      rw [mul_assoc, he, mul_one] at ht
      simpa only [mul_comm] using ht
    have hK : |packetKernel kappa m (2*u^2-1)| ≤ L*m/B := by
      have hl := hlocal m (by omega) (-1) (by norm_num) _
        (packet_endpoint_coordinate_mem u ⟨hu.1.le, hu.2.le⟩)
      have hl' : |packetKernel kappa m (2*u^2-1)| ≤ L*m/(B*Q) := by
        simpa only [packetKernel, if_pos hkappa, Real.rpow_one] using hl
      exact hl'.trans (div_le_div_of_nonneg_left (by positivity) hB
        (by nlinarith))
    have hKd : |deriv (fun v => packetKernel kappa m (2*v^2-1)) u| ≤
        (J*(m : ℝ)^2/B)*(2/Real.sqrt D) := by
      have hd := hderiv m hm u hu hu0
      simp only [Real.rpow_one] at hd
      exact hd.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hB (by nlinarith)) (by positivity))
    have hsD : D ≤ Real.sqrt D := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have htaper : D^4/Real.sqrt D ≤ D^3 := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hD)).mpr
      calc
        D^4 = D^3*D := by ring
        _ ≤ D^3*Real.sqrt D := mul_le_mul_of_nonneg_left hsD (by positivity)
    calc
      |deriv (packetPsi kappa m) u| ≤
          (8*D^3*|packetKernel kappa m (2*u^2-1)| +
            D^4*|deriv (fun v => packetKernel kappa m (2*v^2-1)) u|)/N := by
        rw [packetPsi_endpoint_derivative_formula kappa hkappa m u hu,
          abs_div, abs_of_pos hN]
        apply div_le_div_of_nonneg_right _ hN.le
        calc
          _ ≤ |(-8*u*(1-u^2)^3)*packetKernel kappa m (2*u^2-1)| +
              |(1-u^2)^4*deriv (fun v => packetKernel kappa m (2*v^2-1)) u| := abs_add_le _ _
          _ = 8*|u| * D^3*|packetKernel kappa m (2*u^2-1)| +
              D^4*|deriv (fun v => packetKernel kappa m (2*v^2-1)) u| := by
            have hab : |1-u^2| = D := abs_of_pos hD
            simp only [abs_mul, abs_pow, hab]
            norm_num
          _ ≤ _ := by
            gcongr
            linarith
      _ ≤ (8*D^3*(L*m/B) + D^4*((J*(m : ℝ)^2/B)*(2/Real.sqrt D)))/N := by
        gcongr
      _ = (8*L*m*(D^3/B) + 2*J*(m : ℝ)^2/B*(D^4/Real.sqrt D))/N := by ring
      _ ≤ (8*L*m*(m : ℝ)^kappa + 2*J*(m : ℝ)^2*(m : ℝ)^kappa)/N := by
        apply div_le_div_of_nonneg_right _ hN.le
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left htB (by positivity)
        · calc
            _ ≤ 2*J*(m : ℝ)^2/B*D^3 := mul_le_mul_of_nonneg_left htaper (by positivity)
            _ = 2*J*(m : ℝ)^2*(D^3/B) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left htB (by positivity)
      _ ≤ (8*L+2*J*m)/c0 := by
        apply (div_le_iff₀ hN).mpr
        calc
          _ = ((8*L+2*J*m)/c0)*(c0*((m : ℝ)^kappa*m)) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hnormN (by positivity)
      _ ≤ A*m := by
        dsimp [A]
        apply (div_le_iff₀ hc0).mpr
        have h := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 8*L by positivity)
        have he : (8*L+2*J)/c0*m*c0 = (8*L+2*J)*m := by field_simp
        rw [he]
        nlinarith
  have hdense : Dense ({(-1 : ℝ), 0, 1} : Set ℝ)ᶜ :=
    (Set.toFinite _).countable.dense_compl ℝ
  have hbound : ∀ u ∈ ({(-1 : ℝ), 0, 1} : Set ℝ)ᶜ,
      |deriv (packetPsi kappa m) u| ≤ A*m := by
    intro u hu
    have hex : u ≠ -1 ∧ u ≠ 0 ∧ u ≠ 1 := by simpa using hu
    by_cases hi : u ∈ Icc (-1 : ℝ) 1
    · exact hinterior u ⟨lt_of_le_of_ne hi.1 hex.1.symm, lt_of_le_of_ne hi.2 hex.2.2⟩ hex.2.1
    · rw [packetPsi_derivative_outside kappa m u hi, abs_zero]
      positivity
  intro u
  exact le_on_closure hbound (packetPsi_contDiff kappa m).continuous_deriv_one.abs.continuousOn
    continuous_const.continuousOn (hdense u)

end CausalSmith.Stat.NoisydoseWeakdesignTransition
