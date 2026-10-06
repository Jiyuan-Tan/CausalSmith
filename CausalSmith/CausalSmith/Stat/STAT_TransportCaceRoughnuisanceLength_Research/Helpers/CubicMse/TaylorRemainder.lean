module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.FourthDerivative

/-! # Exact cubic Taylor remainder for the marked transport integrand -/

public section

open scoped BigOperators
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The remainder after the degree-three Taylor polynomial of a marked ratio
has an exact factored rational expression.  Under [the displayed assumptions and inputs](hyp:a,b,c,v,h,hc,hc'), [the stated conclusion holds](goal). -/
-- @node: cubicRatio_cubic_taylor_remainder_eq
lemma cubicRatio_cubic_taylor_remainder_eq (a b c : Fin 7)
    (v h : DensityVector) (hc : v c ≠ 0) (hc' : v c + h c ≠ 0) :
    cubicRatioTerm a b c (v + h) -
      (cubicRatioTerm a b c v + cubicRatioD1Apply a b c h v +
        cubicRatioD2Apply a b c h h v / 2 +
        cubicRatioD3Apply a b c h h h v / 6) =
      (h c) ^ 2 * (v c * h a - v a * h c) *
        (v c * h b - v b * h c) * (v c)⁻¹ ^ 4 * (v c + h c)⁻¹ := by
  simp only [cubicRatioTerm, cubicRatioD1Apply, cubicRatioD2Apply,
    cubicRatioD3Apply, Pi.add_apply]
  field_simp
  ring

/-- Bounding the factored remainder uses only endpoint denominator bounds
and the sum of the absolute coordinate increments.  Under [the displayed assumptions and inputs](hyp:a,b,c,v,h,C,R,S,hC,_hR,hS,hc,hc',ha,hb,hq,hRa,hRb,hSc,hSa,hSb), [the stated conclusion holds](goal). -/
-- @node: cubicRatio_cubic_taylor_remainder_abs_le
lemma cubicRatio_cubic_taylor_remainder_abs_le (a b c : Fin 7)
    (v h : DensityVector) (C R S : ℝ)
    (hC : 0 ≤ C) (_hR : 0 ≤ R) (hS : 0 ≤ S)
    (hc : v c ≠ 0) (hc' : v c + h c ≠ 0)
    (ha : |v a| ≤ C) (hb : |v b| ≤ C) (hq : |v c| ≤ C)
    (hRa : |(v c)⁻¹| ≤ R) (hRb : |(v c + h c)⁻¹| ≤ R)
    (hSc : |h c| ≤ S) (hSa : |h a| + |h c| ≤ S)
    (hSb : |h b| + |h c| ≤ S) :
    |cubicRatioTerm a b c (v + h) -
      (cubicRatioTerm a b c v + cubicRatioD1Apply a b c h v +
        cubicRatioD2Apply a b c h h v / 2 +
        cubicRatioD3Apply a b c h h h v / 6)| ≤ C ^ 2 * R ^ 5 * S ^ 4 := by
  rw [cubicRatio_cubic_taylor_remainder_eq a b c v h hc hc']
  have hfactor (j : Fin 7) (hj : |v j| ≤ C) (hs : |h j| + |h c| ≤ S) :
      |v c * h j - v j * h c| ≤ C * S := by
    calc
      _ ≤ |v c * h j| + |v j * h c| := abs_sub _ _
      _ = |v c| * |h j| + |v j| * |h c| := by rw [abs_mul, abs_mul]
      _ ≤ C * |h j| + C * |h c| := by gcongr
      _ = C * (|h j| + |h c|) := by ring
      _ ≤ C * S := mul_le_mul_of_nonneg_left hs hC
  simp only [abs_mul, abs_pow]
  calc
    _ ≤ S ^ 2 * (C * S) * (C * S) * R ^ 4 * R := by
      gcongr
      · exact hfactor a ha hSa
      · exact hfactor b hb hSb
    _ = _ := by ring


/-- Two distinct coordinate increments are bounded by the full coordinate
sum used in the Taylor remainder.  Under [the displayed assumptions and inputs](hyp:h,i,j,hij), [the stated conclusion holds](goal). -/
-- @node: abs_pair_le_density_increment_sum
lemma abs_pair_le_density_increment_sum (h : DensityVector) (i j : Fin 7)
    (hij : i ≠ j) : |h i| + |h j| ≤ ∑ r : Fin 7, |h r| := by
  classical
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({i, j} : Finset (Fin 7)) ⊆ Finset.univ from Finset.subset_univ _)
    (fun r _ _ => abs_nonneg (h r))
  simpa [Finset.sum_pair hij] using hs

/-- Roadmap (8), with the paper's constant: the exact third-order Taylor
polynomial of either transport channel leaves a fourth-order remainder.
Both endpoints lie in the clipping rectangle, so all denominators are positive.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,hf,hF,A,v,h,hv,hw), [the stated conclusion holds](goal). -/
-- @node: Phi_cubic_taylor_remainder_abs_le
lemma Phi_cubic_taylor_remainder_abs_le (c_f C_f : ℝ)
    (hf : 0 < c_f) (hF : 1 < C_f) (A : Bool) (v h : DensityVector)
    (hv : clippingRectangle c_f C_f v)
    (hw : clippingRectangle c_f C_f (v + h)) :
    |Phi A (v + h) - (Phi A v +
      iteratedFDeriv ℝ 1 (Phi A) v ![h] +
      iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
      iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6)| ≤
      (fourthDerivativeEnvelope c_f C_f / 24) *
        (∑ r : Fin 7, |h r|) ^ 4 := by
  classical
  let S := ∑ r : Fin 7, |h r|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC : 0 ≤ C_f := by linarith
  have hR : 0 ≤ 4 / c_f := by positivity
  have hvalue (i : Fin 7) : |v i| ≤ C_f := by
    by_cases hi0 : i = 0
    · subst i
      rw [abs_of_nonneg (hf.le.trans hv.1.1)]
      exact hv.1.2
    by_cases hi1 : i = 1
    · subst i
      rw [abs_of_nonneg (le_trans (by positivity) hv.2.1.1)]
      linarith [hv.2.1.2]
    by_cases hi2 : i = 2
    · subst i
      rw [abs_of_nonneg (le_trans (by positivity) hv.2.2.1.1)]
      linarith [hv.2.2.1.2]
    have hi3 : 3 ≤ i.val := by
      have hn0 : i.val ≠ 0 := fun he => hi0 (Fin.ext he)
      have hn1 : i.val ≠ 1 := fun he => hi1 (Fin.ext he)
      have hn2 : i.val ≠ 2 := fun he => hi2 (Fin.ext he)
      omega
    have hb := hv.2.2.2 i hi3
    rw [abs_of_nonneg hb.1]
    linarith [hb.2]
  have hden (q : ℝ) (hq : c_f / 4 ≤ q) : q ≠ 0 ∧ |q⁻¹| ≤ 4 / c_f := by
    have hqp : 0 < q := by linarith
    refine ⟨ne_of_gt hqp, ?_⟩
    rw [abs_of_nonneg (inv_pos.mpr hqp).le]
    calc
      q⁻¹ ≤ (c_f / 4)⁻¹ := (inv_le_inv₀ hqp (by positivity)).2 hq
      _ = 4 / c_f := by field_simp
  have h1 := hden (v 1) hv.2.1.1
  have h2 := hden (v 2) hv.2.2.1.1
  have hw1 := hden (v 1 + h 1) hw.2.1.1
  have hw2 := hden (v 2 + h 2) hw.2.2.1.1
  let T (b c : Fin 7) := cubicRatioTerm 0 b c (v + h) -
    (cubicRatioTerm 0 b c v + cubicRatioD1Apply 0 b c h v +
      cubicRatioD2Apply 0 b c h h v / 2 + cubicRatioD3Apply 0 b c h h h v / 6)
  have hbound (b c : Fin 7) (hb : 3 ≤ b.val) (hc : c = 1 ∨ c = 2) :
      |T b c| ≤ C_f ^ 2 * (4 / c_f) ^ 5 * S ^ 4 := by
    have hc0 : (0 : Fin 7) ≠ c := by rcases hc with rfl | rfl <;> decide
    have hbc : b ≠ c := by
      intro heq
      subst b
      rcases hc with rfl | rfl <;> norm_num at hb
    have hq := Or.elim hc (fun heq => heq ▸ h1) (fun heq => heq ▸ h2)
    have hwq := Or.elim hc (fun heq => heq ▸ hw1) (fun heq => heq ▸ hw2)
    exact cubicRatio_cubic_taylor_remainder_abs_le 0 b c v h C_f (4 / c_f) S
      hC hR hS hq.1 hwq.1 (hvalue 0) (hvalue b) (hvalue c) hq.2 hwq.2
      (Finset.single_le_sum (fun r _ => abs_nonneg (h r)) (Finset.mem_univ c))
      (abs_pair_le_density_increment_sum h 0 c hc0)
      (abs_pair_le_density_increment_sum h b c hbc)
  have hplus := hbound (if A then 4 else 6) 2 (by cases A <;> decide) (Or.inr rfl)
  have hminus := hbound (if A then 3 else 5) 1 (by cases A <;> decide) (Or.inl rfl)
  have heq : Phi A (v + h) - (Phi A v +
      iteratedFDeriv ℝ 1 (Phi A) v ![h] +
      iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
      iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6) =
      T (if A then 4 else 6) 2 - T (if A then 3 else 5) 1 := by
    rw [iteratedFDeriv_one_Phi_apply A v h h1.1 h2.1,
      iteratedFDeriv_two_Phi A v h h h1.1 h2.1,
      iteratedFDeriv_three_Phi A v h h h h1.1 h2.1]
    simp only [T, Phi, cubicRatioTerm, cubicRatioD1Apply, div_eq_mul_inv, Pi.add_apply]
    ring
  rw [heq]
  calc
    _ ≤ |T (if A then 4 else 6) 2| + |T (if A then 3 else 5) 1| := abs_sub _ _
    _ ≤ 2 * C_f ^ 2 * (4 / c_f) ^ 5 * S ^ 4 := by linarith
    _ ≤ 2 * (1 + C_f) ^ 2 * (4 / c_f) ^ 5 * S ^ 4 := by
      gcongr
      linarith
    _ = _ := by dsimp [fourthDerivativeEnvelope, S]; ring


/-- The exact clipped pilot and true marked-density vector satisfy the
fourth-order Taylor bound used by the MSE proof, pointwise on the covariate support.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A,x,hx), [the stated conclusion holds](goal). -/
-- @node: pilot_Phi_cubic_taylor_remainder_abs_le
lemma pilot_Phi_cubic_taylor_remainder_abs_le (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool)
    (ω : TwoSample n n) (x : ℝ) (hx : x ∈ covariateSpace) :
    let v := pilot c_f C_f ω x
    let h := markedDensityVector c_f C_f L P n hP x - v
    |Phi A (markedDensityVector c_f C_f L P n hP x) - (Phi A v +
      iteratedFDeriv ℝ 1 (Phi A) v ![h] +
      iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
      iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6)| ≤
      (fourthDerivativeEnvelope c_f C_f / 24) *
        (∑ r : Fin 7, |h r|) ^ 4 := by
  dsimp only
  have heq : pilot c_f C_f ω x +
      (markedDensityVector c_f C_f L P n hP x - pilot c_f C_f ω x) =
      markedDensityVector c_f C_f L P n hP x := add_sub_cancel _ _
  have hw : clippingRectangle c_f C_f
      (pilot c_f C_f ω x +
        (markedDensityVector c_f C_f L P n hP x - pilot c_f C_f ω x)) := by
    rw [heq]
    exact markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx
  have hr := Phi_cubic_taylor_remainder_abs_le c_f C_f hP.sourceBounds.1.1
    hP.sourceBounds.2.1 A (pilot c_f C_f ω x)
    (markedDensityVector c_f C_f L P n hP x - pilot c_f C_f ω x)
    (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x) hw
  simpa only [heq] using hr

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
