module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketInteriorNormalization

/-! Helpers — PacketInterior -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]


/-- Reflection of the binomial sum gives parity of the symmetric Jacobi system (P12). [Under the stated conditions](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: stdJacobi_symmetric_parity
lemma stdJacobi_symmetric_parity (a : ℝ) (ha : -1/2 < a) (j : ℕ) (u : ℝ) :
    stdJacobi a a j (-u) = (-1 : ℝ)^j * stdJacobi a a j u := by
  rw [stdJacobi_binomial_repr a a ha ha j (-u),
    stdJacobi_binomial_repr a a ha ha j u]
  have hreflect := Finset.sum_range_reflect
    (fun i => genBinom (j+a) i * genBinom (j+a) (j-i) *
      (-u-1)^(j-i) * (-u+1)^i) (j+1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [← hreflect]
  rw [show (-1 : ℝ)^j * ((2 : ℝ)^(-(j : ℤ)) *
      ∑ i ∈ Finset.range (j+1), genBinom (j+a) i * genBinom (j+a) (j-i) *
        (u-1)^(j-i) * (u+1)^i) =
      (2 : ℝ)^(-(j : ℤ)) *
      ∑ i ∈ Finset.range (j+1), (-1 : ℝ)^j *
        (genBinom (j+a) i * genBinom (j+a) (j-i) * (u-1)^(j-i) * (u+1)^i) by
    rw [← Finset.mul_sum]; ring]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ j := by have := Finset.mem_range.mp hi; omega
  rw [Nat.sub_sub_self hi', show -u-1 = -(u+1) by ring,
    show -u+1 = -(u-1) by ring]
  rw [neg_pow (u+1) i, neg_pow (u-1) (j-i)]
  have hp : (-1 : ℝ)^i * (-1)^(j-i) = (-1)^j := by
    rw [← pow_add, Nat.add_sub_of_le hi']
  calc
    _ = ((-1 : ℝ)^i * (-1)^(j-i)) *
      (genBinom (j+a) i * genBinom (j+a) (j-i) * (u-1)^(j-i) * (u+1)^i) := by ring
    _ = _ := by rw [hp]

/-- Odd symmetric Jacobi polynomials vanish at the interior center (P12). [Under the stated conditions](hyp:ha,hj). [This is the stated conclusion](goal). -/
-- @node: stdJacobi_symmetric_odd_zero
lemma stdJacobi_symmetric_odd_zero (a : ℝ) (ha : -1/2 < a) (j : ℕ) (hj : Odd j) :
    stdJacobi a a j 0 = 0 := by
  have h := stdJacobi_symmetric_parity a ha j 0
  rw [neg_zero, hj.neg_one_pow, neg_one_mul] at h
  linarith

/-- Centering the symmetric filtered kernel kills the odd degrees, leaving an even kernel. [This is the stated conclusion](goal). -/
-- @node: packetKernel_interior_even
lemma packetKernel_interior_even (m : ℕ) : Function.Even (packetKernel 0 m) := by
  intro u
  simp only [packetKernel, lt_self_iff_false, if_false, filteredJacobiKernel]
  apply Finset.sum_congr rfl
  intro j hj
  rcases Nat.even_or_odd j with he | ho
  · rw [stdJacobi_symmetric_parity 4 (by norm_num), he.neg_one_pow, one_mul]
  · rw [stdJacobi_symmetric_odd_zero 4 (by norm_num) j ho]
    simp

/-- The taper preserves the symmetric interior kernel's evenness (P11). [This is the stated conclusion](goal). -/
-- @node: packetPsi_interior_even
lemma packetPsi_interior_even (m : ℕ) : Function.Even (packetPsi 0 m) := by
  intro u
  have hs : -u ∈ Icc (-1 : ℝ) 1 ↔ u ∈ Icc (-1 : ℝ) 1 := by
    simp only [mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [packetPsi, hs, lt_self_iff_false, if_false, neg_sq,
    packetKernel_interior_even m u]

/-- On its support the fourth-order taper is exactly the symmetric Jacobi weight. [This is the stated conclusion](goal). -/
-- @node: jacobiWeight_four_four
lemma jacobiWeight_four_four (u : ℝ) : jacobiWeight 4 4 u = (1-u^2)^4 := by
  simp only [jacobiWeight, Real.rpow_ofNat]
  ring

/-- Interior raw moments cancel by the same finite-sum orthogonality as the endpoint system (P14). [Under the stated conditions](hyp:hNorm,hm,hj). [This is the stated conclusion](goal). -/
-- @node: packetPsi_interior_moment_zero
lemma packetPsi_interior_moment_zero (hNorm : JacobiNormOrthogonality)
    (m j : ℕ) (hm : 0 < m) (hj : j ≤ m) :
    (∫ u in Icc (-1 : ℝ) 1, |u|^(0 : ℝ) * u^j * packetPsi 0 m u) = 0 := by
  have hdeg : (Polynomial.X^j : Polynomial ℝ).degree ≤ (m : WithBot ℕ) := by
    simpa using (show (j : WithBot ℕ) ≤ m by exact_mod_cast hj)
  have horth := packet_filtered_kernel_orthogonal hNorm 4 4 (by norm_num) (by norm_num)
    m hm 0 (Polynomial.X^j) hdeg
  have heq : (∫ u in Icc (-1 : ℝ) 1, |u|^(0 : ℝ) * u^j * packetPsi 0 m u) =
      (∫ u in Icc (-1 : ℝ) 1, jacobiWeight 4 4 u *
        filteredJacobiKernel 4 4 packetFilter m 0 u * (Polynomial.X^j).eval u) /
          packetKernel 0 m 0 := by
    rw [← integral_div]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only [packetPsi, if_pos hu, lt_self_iff_false, if_false, Real.rpow_zero,
      one_mul, packetKernel, Polynomial.eval_pow, Polynomial.eval_X, jacobiWeight_four_four]
    ring
  rw [heq, horth, zero_div]

/-- Interior analytic bounds: the P12 center formula, elementary integral comparison,
and norm/Gamma leaves give P13; P15 follows from the proved estimate chain. [Under the stated conditions](hyp:hLocalization,hLipschitz,hNorm,hGamma). [This is the stated conclusion](goal). -/
-- @node: packetinterior_analytic_bounds
lemma packetinterior_analytic_bounds (hLocalization : FilteredJacobiLocalization)
    (hLipschitz : FilteredJacobiLipschitz) (hNorm : JacobiNormOrthogonality)
    (hGamma : GammaRatioAsymptotic) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 4 ≤ m →
      0 < packetKernel 0 m 0 ∧
      (∀ u, |packetPsi 0 m u| ≤ A*(1+(m : ℝ)*|u|)^(-(0+2 : ℝ))) ∧
      (∀ u, |deriv (packetPsi 0 m) u| ≤ A*m) := by
  have hnormalization : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 4 ≤ m →
      c*m ≤ packetKernel 0 m 0 := by
    have hspectral := jacobi_four_even_spectral_lower hNorm hGamma
    obtain ⟨c₀, hc₀, hcoef⟩ := hspectral
    exact packetKernel_interior_lower_of_spectral_lower hNorm c₀ hc₀ hcoef
  obtain ⟨c, hc, hnorm⟩ := hnormalization
  exact packetinterior_bounds_of_normalization hLocalization hLipschitz c hc hnorm

/-- The symmetric interior packet has all weighted localization, derivative and cancellation bounds. [Under the stated conditions](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate,hkappa). [This is the stated conclusion](goal). -/
-- @node: packetinterior_bounds
lemma packetinterior_bounds (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic) (kappa : ℝ) (hkappa : kappa = 0) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ m : ℕ, 4 ≤ m → PacketBounds kappa C c m := by
  subst kappa
  obtain ⟨A, hA, hlocalized⟩ := packetinterior_analytic_bounds
    hLocalization_of_gate hLipschitz_of_gate hNorm_of_gate hGamma_of_gate
  let C := 2*A
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  let C' := max C (C*C)
  have hCC' : C ≤ C' := le_max_left _ _
  refine ⟨C', 1, lt_of_lt_of_le hC hCC', by norm_num, ?_⟩
  intro m hm
  obtain ⟨hnorm, hdecay, hd⟩ := hlocalized m hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsup : ∀ u, |packetPsi 0 m u| ≤ C := by
    intro u
    have hbase : 1 ≤ 1+(m : ℝ)*|u| := by
      linarith [mul_nonneg hmp.le (abs_nonneg u)]
    have hpow : (1+(m : ℝ)*|u|)^(-(0+2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)
    exact (hdecay u).trans ((mul_le_mul_of_nonneg_left hpow hA.le).trans
      (by simpa using hAC))
  have hmass : (∫ u in Icc (-1 : ℝ) 1, |u|^(0 : ℝ) * |packetPsi 0 m u|) ≤
      C*(m : ℝ)^(-(0 : ℝ)-1) := by
    exact packet_decay_absolute_mass_le 0 m A (packetPsi 0 m) (by norm_num) hmp hA.le
      (packetPsi_contDiff 0 m).continuous (packetPsi_interior_even m) hdecay
  have hsquare : (∫ u in Icc (-1 : ℝ) 1, |u|^(0 : ℝ) * (packetPsi 0 m u)^2) ≤
      C'*(m : ℝ)^(-(0 : ℝ)-1) := by
    calc
      _ ≤ C * (∫ u in Icc (-1 : ℝ) 1, |u|^(0 : ℝ) * |packetPsi 0 m u|) :=
        packetPsi_square_mass_le 0 (by norm_num) m C hsup
      _ ≤ C * (C*(m : ℝ)^(-(0 : ℝ)-1)) := mul_le_mul_of_nonneg_left hmass hC.le
      _ = (C*C)*(m : ℝ)^(-(0 : ℝ)-1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
  refine ⟨by simpa using hnorm, packetPsi_interior_even m, packetPsi_contDiff 0 m,
    packetPsi_support 0 m, ?_, (fun u => (hsup u).trans hCC'),
    (fun u => (hd u).trans (mul_le_mul_of_nonneg_right (hAC.trans hCC') hmp.le)),
    hmass.trans (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (by positivity) _)),
    hsquare, ?_⟩
  · simp [packetPsi, hnorm.ne']
  · intro j hj
    have hjm : j ≤ m := by
      have h : (j : ℝ) < m := by simpa using hj
      have hn : j < m := by exact_mod_cast h
      omega
    exact packetPsi_interior_moment_zero hNorm_of_gate m j (by omega) hjm

end CausalSmith.Stat.NoisydoseWeakdesignTransition
