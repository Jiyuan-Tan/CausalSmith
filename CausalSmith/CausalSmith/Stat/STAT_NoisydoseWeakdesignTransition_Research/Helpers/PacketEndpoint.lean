module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketDerivativeAssembly

/-! Assembly of the endpoint packet bounds from normalization, localization and derivatives. -/
public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The endpoint packet has all weighted localization, derivative and cancellation bounds. [Under the stated conditions](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate,hkappa). [This is the stated conclusion](goal). -/
-- @node: packetendpoint_bounds
lemma packetendpoint_bounds (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic) (kappa : ℝ) (hkappa : 0 < kappa ∧ kappa ≤ 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ m : ℕ, 4 ≤ m → PacketBounds kappa C c m := by
  -- P2--P3 are proved in PacketNormalization and PacketKernelNormalization.
  -- P5--P6 are proved in PacketGeometry; P9--P10 in PacketDerivativeAssembly.
  -- P7 follows below from P6 at S = kappa + 2; P4 and P8 are also proved.
  obtain ⟨A, hA, hlocalized⟩ : ∃ A : ℝ, 0 < A ∧
      ∀ m : ℕ, 4 ≤ m →
        (∀ u, |packetPsi kappa m u| ≤ A*(1+(m : ℝ)*|u|)^(-(kappa+2))) ∧
        (∀ u, |deriv (packetPsi kappa m) u| ≤ A*m) := by
    obtain ⟨A0, hA0, hdecay⟩ := packetPsi_endpoint_localization
      hLocalization_of_gate hNorm_of_gate hGamma_of_gate kappa hkappa.1 (kappa+2)
      (by linarith [hkappa.1])
    obtain ⟨D, hD, hderiv⟩ : ∃ D : ℝ, 0 < D ∧
        ∀ m : ℕ, 4 ≤ m → ∀ u : ℝ, |deriv (packetPsi kappa m) u| ≤ D*m := by
      exact packetPsi_endpoint_derivative_bound hLocalization_of_gate hLipschitz_of_gate
        hNorm_of_gate hGamma_of_gate kappa hkappa.1
    refine ⟨max A0 D, lt_of_lt_of_le hA0 (le_max_left _ _), ?_⟩
    intro m hm
    constructor
    · intro u
      exact (hdecay m hm u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by positivity) _))
    · intro u
      exact (hderiv m hm u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

  let C := 2*A
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hanalytic : ∀ m : ℕ, 4 ≤ m →
        (∀ u, |packetPsi kappa m u| ≤ C) ∧
        (∀ u, |deriv (packetPsi kappa m) u| ≤ C*m) ∧
        (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * |packetPsi kappa m u|) ≤
          C*(m : ℝ)^(-kappa-1) := by
    intro m hm
    obtain ⟨hdecay, hd⟩ := hlocalized m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    refine ⟨?_, (fun u => (hd u).trans (mul_le_mul_of_nonneg_right hAC hmp.le)), ?_⟩
    · intro u
      have hbase : 1 ≤ 1+(m : ℝ)*|u| := by
        linarith [mul_nonneg hmp.le (abs_nonneg u)]
      have hpow : (1+(m : ℝ)*|u|)^(-(kappa+2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith [hkappa.1])
      exact (hdecay u).trans ((mul_le_mul_of_nonneg_left hpow hA.le).trans
        (by simpa using hAC))
    · exact packet_decay_absolute_mass_le kappa m A (packetPsi kappa m) hkappa.1.le hmp hA.le
        (packetPsi_contDiff kappa m).continuous (packetPsi_endpoint_even kappa hkappa.1 m) hdecay
  let C' := max C (C*C)
  have hCC' : C ≤ C' := le_max_left _ _
  have hsqC' : C*C ≤ C' := le_max_right _ _
  refine ⟨C', 1, lt_of_lt_of_le hC hCC', by norm_num, ?_⟩
  intro m hm
  obtain ⟨hsup, hderiv, hmass⟩ := hanalytic m hm
  have hsquare : (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * (packetPsi kappa m u)^2) ≤
      C'*(m : ℝ)^(-kappa-1) := by
    calc
      _ ≤ C * (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * |packetPsi kappa m u|) :=
        packetPsi_square_mass_le kappa hkappa.1.le m C hsup
      _ ≤ C * (C*(m : ℝ)^(-kappa-1)) := mul_le_mul_of_nonneg_left hmass hC.le
      _ = (C*C)*(m : ℝ)^(-kappa-1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsqC' (Real.rpow_nonneg (by positivity) _)
  have heven := packetPsi_endpoint_even kappa hkappa.1 m
  refine ⟨?_, heven, packetPsi_contDiff kappa m, packetPsi_support kappa m,
    packetPsi_endpoint_zero hNorm_of_gate kappa hkappa.1 m hm,
    (fun u => (hsup u).trans hCC'),
    (fun u => (hderiv u).trans (mul_le_mul_of_nonneg_right hCC' (by positivity))),
    hmass.trans (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (by positivity) _)),
    hsquare, ?_⟩
  · simpa only [if_pos hkappa.1] using
      packetKernel_endpoint_pos hNorm_of_gate kappa hkappa.1 m hm
  · intro j hj
    rcases Nat.even_or_odd j with he | ho
    · obtain ⟨s, rfl⟩ := he
      have hs : s ≤ m := by
        have h : (s+s : ℝ) < m := by simpa using hj
        have hn : s+s < m := by exact_mod_cast h
        omega
      simpa only [two_mul] using
        packetPsi_endpoint_even_moment_zero hNorm_of_gate kappa hkappa.1 m s (by omega) hs
    · exact even_packet_odd_moment kappa (packetPsi kappa m) heven j ho

end CausalSmith.Stat.NoisydoseWeakdesignTransition
