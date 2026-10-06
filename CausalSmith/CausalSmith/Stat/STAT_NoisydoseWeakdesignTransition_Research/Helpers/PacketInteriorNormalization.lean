module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.PacketInteriorEstimates
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Analysis.Real.Pi.Wallis
/-! Interior Jacobi center evaluations (P12), active even-degree counts, and normalization assembly (P13). -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
open Polynomial Set
open scoped BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
/-- Generalized binomial coefficients at natural arguments are ordinary binomial coefficients. [This is the stated conclusion](goal). -/
-- @node: genBinom_natCast
lemma genBinom_natCast (n k : ℕ) : genBinom (n : ℝ) k = (n.choose k : ℝ) := by
  exact (Nat.cast_choose_eq_descPochhammer_div ℝ n k).symm
/-- Coefficients of the negative binomial polynomial carry the expected alternating sign. [This is the stated conclusion](goal). -/
-- @node: packet_coeff_one_sub_X_pow
lemma packet_coeff_one_sub_X_pow (n k : ℕ) : ((1-X : Polynomial ℝ)^n).coeff k =
    (-1 : ℝ)^k * (n.choose k : ℝ) := by
  by_cases hk : k ≤ n
  · have he : (1-X : Polynomial ℝ)^n = C ((-1 : ℝ)^n) * (X+C (-1))^n := by
      rw [C_pow, ← mul_pow]
      congr 1
      simp [sub_eq_add_neg]
    rw [he, coeff_C_mul, coeff_X_add_C_pow]
    have hs : (-1 : ℝ)^n * (-1)^(n-k) = (-1)^k := by
      have hn : n = k+(n-k) := by omega
      conv_lhs => lhs; rw [hn, pow_add]
      rw [mul_assoc, ← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [← mul_assoc, hs]
  · have hn : n < k := by omega
    have he : (1-X : Polynomial ℝ)^n = C ((-1 : ℝ)^n) * (X+C (-1))^n := by
      rw [C_pow, ← mul_pow]
      congr 1
      simp [sub_eq_add_neg]
    rw [he, coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt hn]
    simp
/-- The coefficient of degree twice s in the product (1+X)^n (1-X)^n is the coefficient of degree s in (1-X)^n. [This is the stated conclusion](goal). -/
-- @node: packet_alternating_choose_convolution
lemma packet_alternating_choose_convolution (n s : ℕ) :
    (∑ i ∈ Finset.range (2*s+1), (n.choose i : ℝ) *
      (n.choose (2*s-i) : ℝ) * (-1 : ℝ)^(2*s-i)) =
      (-1 : ℝ)^s * (n.choose s : ℝ) := by
  have hp : (1+X : Polynomial ℝ)^n * (1-X)^n = (1-X^2)^n := by
    rw [← mul_pow]
    congr 1
    ring
  have h := congrArg (fun p : Polynomial ℝ => p.coeff (2*s)) hp
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [coeff_one_add_X_pow, packet_coeff_one_sub_X_pow] at h
  have he : (1-X^2 : Polynomial ℝ)^n = expand ℝ 2 ((1-X)^n) := by simp
  rw [he, coeff_expand_mul' (by norm_num : 0 < 2), packet_coeff_one_sub_X_pow] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  ring
/-- The even symmetric Jacobi center evaluation in P12 follows by coefficient extraction. [This is the stated conclusion](goal). -/
-- @node: stdJacobi_four_even_zero
lemma stdJacobi_four_even_zero (s : ℕ) : stdJacobi 4 4 (2*s) 0 =
    (-1 : ℝ)^s * (2 : ℝ)^(-(2*s : ℤ)) * ((2*s+4).choose s : ℝ) := by
  rw [stdJacobi_binomial_repr 4 4 (by norm_num) (by norm_num)]
  simp only [zero_sub, zero_add, one_pow, mul_one]
  have he : ((2*s : ℕ) : ℝ)+4 = ((2*s+4 : ℕ) : ℝ) := by push_cast; ring
  rw [he]
  simp only [genBinom_natCast]
  rw [packet_alternating_choose_convolution]
  push_cast
  ring
/-- Every even-degree symmetric Jacobi polynomial is nonzero at its center. [This is the stated conclusion](goal). -/
-- @node: stdJacobi_four_even_zero_ne_zero
lemma stdJacobi_four_even_zero_ne_zero (s : ℕ) : stdJacobi 4 4 (2*s) 0 ≠ 0 := by
  rw [stdJacobi_four_even_zero]
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  · exact_mod_cast (Nat.choose_pos (by omega : s ≤ 2*s+4)).ne'

/-- The norm and Gamma leaves bound the symmetric squared norm by a constant divided by degree (P13). [Under the stated conditions](hyp:hNorm,hGamma). [This is the stated conclusion](goal). -/
-- @node: jacobi_four_sqNorm_upper
lemma jacobi_four_sqNorm_upper (hNorm : JacobiNormOrthogonality)
    (hGamma : GammaRatioAsymptotic) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j → jacobiSqNorm 4 4 j ≤ C/(j : ℝ) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h₁⟩ :=
    gamma_ratio_integer_power_bounds hGamma 5 1 (by norm_num) (by norm_num)
  obtain ⟨c₂, C₂, hc₂, hC₂, h₂⟩ :=
    gamma_ratio_integer_power_bounds hGamma 5 9 (by norm_num) (by norm_num)
  refine ⟨512*C₁*C₂, by positivity, ?_⟩
  intro j hj
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj
  have h₁u := (h₁ j hj).2
  have h₂u := (h₂ j hj).2
  norm_num only at h₁u h₂u
  have hratio₁ : 0 ≤ Real.Gamma (j+5)/Real.Gamma (j+1) := by positivity
  have hratio₂ : 0 ≤ Real.Gamma (j+5)/Real.Gamma (j+9) := by positivity
  have hprod := mul_le_mul h₁u h₂u hratio₂ (by positivity : 0 ≤ C₁*(j : ℝ)^(4 : ℝ))
  have hcancel : (j : ℝ)^(4 : ℝ) * (j : ℝ)^(-4 : ℝ) = 1 := by
    rw [← Real.rpow_add hjp]; norm_num
  have hbound : Real.Gamma (j+5)*Real.Gamma (j+5) /
      (Real.Gamma (j+1)*Real.Gamma (j+9)) ≤ C₁*C₂ := by
    calc
      _ = (Real.Gamma (j+5)/Real.Gamma (j+1)) *
          (Real.Gamma (j+5)/Real.Gamma (j+9)) := by ring
      _ ≤ C₁*(j : ℝ)^(4 : ℝ)*(C₂*(j : ℝ)^(-4 : ℝ)) := hprod
      _ = C₁*C₂ := by rw [mul_mul_mul_comm, hcancel, mul_one]
  rw [(hNorm 4 4 (by norm_num) (by norm_num) j).2.2]
  norm_num only
  rw [show (j : ℝ)+4+1 = j+5 by ring, show (j : ℝ)+4+4+1 = j+9 by ring]
  have hden : (j : ℝ) ≤ 2*j+4+4+1 := by linarith
  calc
    _ ≤ (512/(2*(j : ℝ)+4+4+1))*(C₁*C₂) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (512/(j : ℝ))*(C₁*C₂) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) hjp hden) (by positivity)
    _ = _ := by ring

/-- Wallis' elementary integral comparison bounds the squared normalized central binomial coefficient below (P12--P13). [Under the stated conditions](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: packet_central_binomial_square_lower
lemma packet_central_binomial_square_lower (s : ℕ) (hs : 1 ≤ s) :
    2/(3*Real.pi*(s : ℝ)) ≤
      ((2 : ℝ)^(-(2*s : ℤ)) * ((2*s).choose s : ℝ))^2 := by
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  have hf : ((2*s).choose s : ℝ) * (s.factorial : ℝ)^2 = ((2*s).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : s ≤ 2*s)
    rw [show 2*s-s = s by omega] at h
    simpa only [pow_two, mul_assoc] using (show ((2*s).choose s : ℝ) * (s.factorial : ℝ) * (s.factorial : ℝ) = ((2*s).factorial : ℝ) by exact_mod_cast h)
  have hW := Real.Wallis.W_le s
  have hidentity : Real.Wallis.W s *
      ((2 : ℝ)^(-(2*s : ℤ)) * ((2*s).choose s : ℝ))^2 * (2*(s : ℝ)+1) = 1 := by
    rw [Real.Wallis.W_eq_factorial_ratio]
    have hp : (2 : ℝ)^(-(2*s : ℤ)) = ((2 : ℝ)^(2*s : ℕ))⁻¹ := by
      rw [zpow_neg, show (2*(s : ℤ)) = ((2*s : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [hp]
    have hf0 : (s.factorial : ℝ) ≠ 0 := by positivity
    have hf2 : ((2*s).factorial : ℝ) ≠ 0 := by positivity
    have hp0 : (2 : ℝ)^(2*s) ≠ 0 := by positivity
    have hp4 : (2 : ℝ)^(4*s) = ((2 : ℝ)^(2*s))^2 := by
      rw [← pow_mul]; congr 1; omega
    rw [hp4]
    field_simp
    nlinarith [sq_nonneg (((2*s).choose s : ℝ)*(s.factorial : ℝ)^2)]
  let B := ((2 : ℝ)^(-(2*s : ℤ)) * ((2*s).choose s : ℝ))^2
  have hB : 0 ≤ B := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hW (mul_nonneg hB (by positivity : 0 ≤ 2*(s : ℝ)+1))
  have hlow : 1 ≤ (Real.pi/2)*B*(2*(s : ℝ)+1) := by
    calc
      1 = Real.Wallis.W s * (B*(2*(s : ℝ)+1)) := by dsimp [B]; nlinarith [hidentity]
      _ ≤ (Real.pi/2)*(B*(2*(s : ℝ)+1)) := hmul
      _ = _ := by ring
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hfinal : 2 ≤ (3*Real.pi*(s : ℝ))*B := by
    have hpi := Real.pi_pos
    nlinarith [mul_nonneg (mul_nonneg hpi.le hB) (by linarith : 0 ≤ (s : ℝ)-1)]
  apply (div_le_iff₀ (by positivity : 0 < 3*Real.pi*(s : ℝ))).mpr
  simpa only [B, mul_comm] using hfinal

/-- Increasing the binomial top index transfers the central-binomial lower bound to the even Jacobi center value (P12). [Under the stated conditions](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: stdJacobi_four_even_square_lower
lemma stdJacobi_four_even_square_lower (s : ℕ) (hs : 1 ≤ s) :
    2/(3*Real.pi*(s : ℝ)) ≤ (stdJacobi 4 4 (2*s) 0)^2 := by
  have hchoose : ((2*s).choose s : ℝ) ≤ ((2*s+4).choose s : ℝ) := by
    exact_mod_cast Nat.choose_le_choose s (by omega : 2*s ≤ 2*s+4)
  have hmul := mul_le_mul_of_nonneg_left hchoose
    (by positivity : 0 ≤ (2 : ℝ)^(-(2*s : ℤ)))
  have hnonneg : 0 ≤ (2 : ℝ)^(-(2*s : ℤ)) * ((2*s).choose s : ℝ) := by positivity
  have hsquare : ((2 : ℝ)^(-(2*s : ℤ)) * ((2*s).choose s : ℝ))^2 ≤
      ((2 : ℝ)^(-(2*s : ℤ)) * ((2*s+4).choose s : ℝ))^2 := by nlinarith
  have hsign : ((-1 : ℝ)^s)^2 = 1 := by
    rw [← pow_mul, mul_comm s 2, pow_mul]; simp
  simp only [stdJacobi_four_even_zero, mul_pow, hsign, one_mul]
  simpa only [mul_pow] using (packet_central_binomial_square_lower s hs).trans hsquare

/-- The P12 center lower bound divided by the norm/Gamma upper bound gives uniform positive even spectral coefficients (P13). [Under the stated conditions](hyp:hNorm,hGamma). [This is the stated conclusion](goal). -/
-- @node: jacobi_four_even_spectral_lower
lemma jacobi_four_even_spectral_lower (hNorm : JacobiNormOrthogonality)
    (hGamma : GammaRatioAsymptotic) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ (stdJacobi 4 4 (2*s) 0)^2 / jacobiSqNorm 4 4 (2*s) := by
  obtain ⟨C, hC, hnorm⟩ := jacobi_four_sqNorm_upper hNorm hGamma
  refine ⟨2/(3*Real.pi*C), by positivity, ?_⟩
  intro s hs
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  have hnpos := (hNorm 4 4 (by norm_num) (by norm_num) (2*s)).2.1
  have hn : jacobiSqNorm 4 4 (2*s) ≤ C/(s : ℝ) := by
    calc
      _ ≤ C/((2*s : ℕ) : ℝ) := hnorm (2*s) (by omega)
      _ ≤ C/(s : ℝ) := div_le_div_of_nonneg_left hC.le hsp (by push_cast; linarith)
  apply (le_div_iff₀ hnpos).mpr
  calc
    (2/(3*Real.pi*C))*jacobiSqNorm 4 4 (2*s) ≤ (2/(3*Real.pi*C))*(C/(s : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2/(3*Real.pi*(s : ℝ)) := by field_simp
    _ ≤ _ := stdJacobi_four_even_square_lower s hs

/-- An explicit injective sequence of even degrees lies in the positive filter counting interval for every legal packet degree. [Under the stated conditions](hyp:hm,hi). [This is the stated conclusion](goal). -/
-- @node: packetFilter_interior_even_indices
lemma packetFilter_interior_even_indices (m i : ℕ) (hm : 4 ≤ m)
    (hi : i < max 1 (m/8)) :
    2*((5*m+7)/8+i) ∈ Finset.range (2*m+1) ∧
    ((2*((5*m+7)/8+i) : ℕ) : ℝ)/(m : ℝ) ∈ Icc (5/4 : ℝ) (7/4) := by
  have hlo : 5*m ≤ 8*((5*m+7)/8+i) := by omega
  have hhi : 8*((5*m+7)/8+i) ≤ 7*m := by
    by_cases h : 8 ≤ m
    · omega
    · omega
  have hp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
  · rw [le_div_iff₀ hp]
    have h : (5 : ℝ)*m ≤ 8*((5*m+7)/8+i : ℕ) := by exact_mod_cast hlo
    push_cast at h ⊢
    linarith
  · rw [div_le_iff₀ hp]
    have h : (8 : ℝ)*((5*m+7)/8+i : ℕ) ≤ 7*m := by exact_mod_cast hhi
    push_cast at h ⊢
    linarith
/-- The explicit even-degree sequence contains at least a fixed positive multiple of the packet degree. [Under the stated conditions](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: packetFilter_interior_even_count
lemma packetFilter_interior_even_count (m : ℕ) (hm : 4 ≤ m) :
    (m : ℝ)/15 ≤ (max 1 (m/8) : ℕ) := by
  have h : m ≤ 15*(max 1 (m/8)) := by omega
  have hr : (m : ℝ) ≤ 15*(max 1 (m/8) : ℕ) := by exact_mod_cast h
  linarith
/-- The interior normalization denominator is positive, using an active even spectral degree and the P12 center evaluation. [Under the stated conditions](hyp:hNorm,hm). [This is the stated conclusion](goal). -/
-- @node: packetKernel_interior_pos
lemma packetKernel_interior_pos (hNorm : JacobiNormOrthogonality) (m : ℕ) (hm : 4 ≤ m) :
    0 < packetKernel 0 m 0 := by
  simp only [packetKernel, lt_self_iff_false, if_false, filteredJacobiKernel]
  apply Finset.sum_pos'
  · intro j hj
    have hn := (hNorm 4 4 (by norm_num) (by norm_num) j).2.1
    have hnum : 0 ≤ packetFilter ((j : ℝ)/m) * stdJacobi 4 4 j 0 * stdJacobi 4 4 j 0 := by
      nlinarith [packetFilter_nonneg ((j : ℝ)/m), sq_nonneg (stdJacobi 4 4 j 0)]
    exact div_nonneg hnum hn.le
  · obtain ⟨hj, hs⟩ := packetFilter_interior_even_indices m 0 hm (by omega)
    simp only [Nat.add_zero] at hj hs
    refine ⟨2*((5*m+7)/8), hj, ?_⟩
    have hn := (hNorm 4 4 (by norm_num) (by norm_num) (2*((5*m+7)/8))).2.1
    have hf : 0 < packetFilter (((2*((5*m+7)/8) : ℕ) : ℝ)/m) :=
      lt_of_lt_of_le (Real.exp_pos (-64)) (packetFilter_counting_interval_lower _ hs)
    have hsq := sq_pos_of_ne_zero (stdJacobi_four_even_zero_ne_zero ((5*m+7)/8))
    apply div_pos _ hn
    nlinarith [mul_pos hf hsq]
/-- Counting active even degrees assembles the P13 normalization lower bound from a uniform positive lower bound on even spectral coefficients. [Under the stated conditions](hyp:hNorm,hc,hcoef). [This is the stated conclusion](goal). -/
-- @node: packetKernel_interior_lower_of_spectral_lower
lemma packetKernel_interior_lower_of_spectral_lower (hNorm : JacobiNormOrthogonality) (c : ℝ) (hc : 0 < c)
    (hcoef : ∀ s : ℕ, 1 ≤ s →
      c ≤ (stdJacobi 4 4 (2*s) 0)^2 / jacobiSqNorm 4 4 (2*s)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ m : ℕ, 4 ≤ m → c'*m ≤ packetKernel 0 m 0 := by
  let E := Real.exp (-64)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨E*c/15, by positivity, ?_⟩
  intro m hm
  let f : ℕ → ℝ := fun j => packetFilter ((j : ℝ)/m) *
    (stdJacobi 4 4 j 0)^2 / jacobiSqNorm 4 4 j
  let g : ℕ → ℕ := fun i => 2*((5*m+7)/8+i)
  have hfnonneg (j : ℕ) : 0 ≤ f j :=
    div_nonneg (mul_nonneg (packetFilter_nonneg _) (sq_nonneg _))
      (hNorm 4 4 (by norm_num) (by norm_num) j).2.1.le
  have hkernel : packetKernel 0 m 0 = ∑ j ∈ Finset.range (2*m+1), f j := by
    simp only [packetKernel, lt_self_iff_false, if_false, filteredJacobiKernel]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [f]
    ring
  have hginj : Function.Injective g := by intro i j hij; dsimp [g] at hij; omega
  have hsub : (Finset.range (max 1 (m/8))).image g ⊆ Finset.range (2*m+1) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (packetFilter_interior_even_indices m i hm (Finset.mem_range.mp hi)).1
  have hlower (i : ℕ) (hi : i ∈ Finset.range (max 1 (m/8))) : E*c ≤ f (g i) := by
    have hs := (packetFilter_interior_even_indices m i hm (Finset.mem_range.mp hi)).2
    have hcp := hcoef ((5*m+7)/8+i) (by omega)
    have hfilter := packetFilter_counting_interval_lower _ hs
    have hmul := mul_le_mul hfilter hcp hc.le (packetFilter_nonneg _)
    dsimp [E, f, g]
    simpa only [mul_div_assoc] using hmul
  rw [hkernel]
  calc
    E*c/15*(m : ℝ) = ((m : ℝ)/15)*(E*c) := by ring
    _ ≤ (max 1 (m/8) : ℕ)*(E*c) :=
      mul_le_mul_of_nonneg_right (packetFilter_interior_even_count m hm) (by positivity)
    _ = ∑ i ∈ Finset.range (max 1 (m/8)), E*c := by simp
    _ ≤ ∑ i ∈ Finset.range (max 1 (m/8)), f (g i) := Finset.sum_le_sum hlower
    _ = ∑ j ∈ (Finset.range (max 1 (m/8))).image g, f j :=
      (Finset.sum_image (fun i hi j hj hij => hginj hij)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj hn => hfnonneg j)
end CausalSmith.Stat.NoisydoseWeakdesignTransition
