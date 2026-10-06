module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.CubicDerivative

/-! # Fourth coordinate derivative of the observable transport integrand

Explicit differentiation of the two marked ratios completes the roadmap's
fourth-order envelope on the deterministic clipping rectangle.
-/

@[expose] public section

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: cubicRatioD4Apply
/-- [The cubic ratio d4 apply object](goal) is defined from [the supplied inputs](hyp:a,b,c,h,k,l,m,v). -/
noncomputable def cubicRatioD4Apply (a b c : Fin 7)
    (h k l m v : DensityVector) : ℝ :=
  2 * (h a * k b + k a * h b) * l c * m c * (v c)⁻¹ ^ 3 +
  2 * (h a * l b + l a * h b) * k c * m c * (v c)⁻¹ ^ 3 +
  2 * (h a * m b + m a * h b) * k c * l c * (v c)⁻¹ ^ 3 +
  2 * (k a * l b + l a * k b) * h c * m c * (v c)⁻¹ ^ 3 +
  2 * (k a * m b + m a * k b) * h c * l c * (v c)⁻¹ ^ 3 +
  2 * (l a * m b + m a * l b) * h c * k c * (v c)⁻¹ ^ 3 -
  6 * (h a * v b + v a * h b) * k c * l c * m c * (v c)⁻¹ ^ 4 -
  6 * (k a * v b + v a * k b) * h c * l c * m c * (v c)⁻¹ ^ 4 -
  6 * (l a * v b + v a * l b) * h c * k c * m c * (v c)⁻¹ ^ 4 -
  6 * (m a * v b + v a * m b) * h c * k c * l c * (v c)⁻¹ ^ 4 +
  24 * v a * v b * h c * k c * l c * m c * (v c)⁻¹ ^ 5

-- @node: fderiv_cubicRatioD3Apply
/-- Given [the supplied inputs](hyp:a,b,c,v,h,k,l,m,hc), [the stated result about fderiv cubic ratio d3 apply holds](goal). -/
lemma fderiv_cubicRatioD3Apply (a b c : Fin 7)
    (v h k l m : DensityVector) (hc : v c ≠ 0) :
    fderiv ℝ (fun y => cubicRatioD3Apply a b c k l m y) v h =
      cubicRatioD4Apply a b c h k l m v := by
  have ha := (densityCoord a).hasFDerivAt (x := v)
  have hb := (densityCoord b).hasFDerivAt (x := v)
  have hc' := (densityCoord c).hasFDerivAt (x := v)
  have hi := (hasFDerivAt_inv hc).comp v hc'
  have hi2 := hi.mul hi
  have hi3 := hi2.mul hi
  have hi4 := hi3.mul hi
  have hp := ha.mul hb
  have hs (s : DensityVector) := (hb.const_mul (s a)).add (ha.mul_const (s b))
  have ht1 := hi2.const_mul (-(k a * l b + l a * k b) * m c)
  have ht2 := hi2.const_mul (-((k a * m b + m a * k b) * l c +
    (l a * m b + m a * l b) * k c))
  have ht3 := ((hs k).mul hi3).const_mul (2 * l c * m c)
  have ht4 := ((hs l).mul hi3).const_mul (2 * k c * m c)
  have ht5 := ((hs m).mul hi3).const_mul (2 * k c * l c)
  have ht6 := (hp.mul hi4).const_mul (6 * k c * l c * m c)
  have ht := ((((ht1.add ht2).add ht3).add ht4).add ht5).sub ht6
  have ht' := ht.congr_of_eventuallyEq (f₁ := fun y => cubicRatioD3Apply a b c k l m y)
    (Filter.Eventually.of_forall (fun y => by
      simp [cubicRatioD3Apply, densityCoord, Function.comp_apply]
      ring))
  rw [ht'.fderiv]
  simp [cubicRatioD4Apply, densityCoord, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp [hc]
  <;> ring

-- @node: iteratedFDeriv_four_cubicRatioTerm
/-- Given [the supplied inputs](hyp:a,b,c,v,h,k,l,m,hc), [the stated result about iterated fderiv four cubic ratio term holds](goal). -/
lemma iteratedFDeriv_four_cubicRatioTerm (a b c : Fin 7)
    (v h k l m : DensityVector) (hc : v c ≠ 0) :
    iteratedFDeriv ℝ 4 (cubicRatioTerm a b c) v ![h, k, l, m] =
      cubicRatioD4Apply a b c h k l m v := by
  have hs : ContDiffAt ℝ 4 (cubicRatioTerm a b c) v := by
    unfold cubicRatioTerm
    fun_prop
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 3 (cubicRatioTerm a b c)) v :=
    hs.differentiableAt_iteratedFDeriv (by norm_num)
  rw [hd.iteratedFDeriv_succ_apply_left']
  have hne : ∀ᶠ y in nhds v, y c ≠ 0 :=
    (densityCoord c).continuous.continuousAt.eventually_ne hc
  have heq :
      (fun y => iteratedFDeriv ℝ 3 (cubicRatioTerm a b c) y
        (Fin.tail ![h, k, l, m])) =ᶠ[nhds v]
      (fun y => cubicRatioD3Apply a b c k l m y) := by
    filter_upwards [hne] with y hy
    simpa using iteratedFDeriv_three_cubicRatioTerm a b c y k l m hy
  rw [heq.fderiv_eq]
  simpa using fderiv_cubicRatioD3Apply a b c v h k l m hc

-- @node: iteratedFDeriv_four_Phi
/-- Given [the supplied inputs](hyp:A,v,h,k,l,m,h1,h2), [the stated result about iterated fderiv four phi holds](goal). -/
lemma iteratedFDeriv_four_Phi (A : Bool) (v : DensityVector)
    (h k l m : DensityVector) (h1 : v 1 ≠ 0) (h2 : v 2 ≠ 0) :
    iteratedFDeriv ℝ 4 (Phi A) v ![h, k, l, m] =
      cubicRatioD4Apply 0 (if A then 4 else 6) 2 h k l m v -
        cubicRatioD4Apply 0 (if A then 3 else 5) 1 h k l m v := by
  cases A with
  | false =>
      have hs2 : ContDiffAt ℝ 4 (cubicRatioTerm 0 6 2) v := by
        unfold cubicRatioTerm
        fun_prop
      have hs1 : ContDiffAt ℝ 4 (cubicRatioTerm 0 5 1) v := by
        unfold cubicRatioTerm
        fun_prop
      have heq : Phi false = cubicRatioTerm 0 6 2 - cubicRatioTerm 0 5 1 := by
        funext y
        simp [Phi, cubicRatioTerm, div_eq_mul_inv]
        ring
      rw [heq, iteratedFDeriv_sub_apply hs2 hs1]
      change iteratedFDeriv ℝ 4 (cubicRatioTerm 0 6 2) v ![h, k, l, m] -
          iteratedFDeriv ℝ 4 (cubicRatioTerm 0 5 1) v ![h, k, l, m] = _
      rw [
        iteratedFDeriv_four_cubicRatioTerm 0 6 2 v h k l m h2,
        iteratedFDeriv_four_cubicRatioTerm 0 5 1 v h k l m h1]
      simp
  | true =>
      have hs2 : ContDiffAt ℝ 4 (cubicRatioTerm 0 4 2) v := by
        unfold cubicRatioTerm
        fun_prop
      have hs1 : ContDiffAt ℝ 4 (cubicRatioTerm 0 3 1) v := by
        unfold cubicRatioTerm
        fun_prop
      have heq : Phi true = cubicRatioTerm 0 4 2 - cubicRatioTerm 0 3 1 := by
        funext y
        simp [Phi, cubicRatioTerm, div_eq_mul_inv]
        ring
      rw [heq, iteratedFDeriv_sub_apply hs2 hs1]
      change iteratedFDeriv ℝ 4 (cubicRatioTerm 0 4 2) v ![h, k, l, m] -
          iteratedFDeriv ℝ 4 (cubicRatioTerm 0 3 1) v ![h, k, l, m] = _
      rw [
        iteratedFDeriv_four_cubicRatioTerm 0 4 2 v h k l m h2,
        iteratedFDeriv_four_cubicRatioTerm 0 3 1 v h k l m h1]
      simp

-- @node: cubicRatioD4_basis_abs_le
/-- Given [the supplied inputs](hyp:a,b,c,i,j,k,l,v,C,R,hC,hR,ha,hb,hc), [the stated result about cubic ratio d4 basis abs le holds](goal). -/
lemma cubicRatioD4_basis_abs_le (a b c i j k l : Fin 7)
    (v : DensityVector) (C R : ℝ) (hC : 1 < C) (hR : 1 < R)
    (ha : |v a| ≤ C) (hb : |v b| ≤ C) (hc : |(v c)⁻¹| ≤ R) :
    |cubicRatioD4Apply a b c (basis i) (basis j) (basis k) (basis l) v| ≤
      24 * (1 + C) ^ 2 * R ^ 5 := by
  have hC0 : 0 ≤ C := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hd (s r : Fin 7) : |basis s r| ≤ 1 := by
    by_cases hrs : r = s <;> simp [basis, hrs]
  have hpair (s t : Fin 7) :
      |basis s a * basis t b + basis t a * basis s b| ≤ 2 := by
    calc
      _ ≤ |basis s a| * |basis t b| + |basis t a| * |basis s b| := by
        simpa only [abs_mul] using abs_add_le (basis s a * basis t b) (basis t a * basis s b)
      _ ≤ 1 * 1 + 1 * 1 := by gcongr <;> apply hd
      _ = 2 := by norm_num
  have hlinear (s : Fin 7) : |basis s a * v b + v a * basis s b| ≤ 2 * C := by
    calc
      _ ≤ |basis s a| * |v b| + |v a| * |basis s b| := by
        simpa only [abs_mul] using abs_add_le (basis s a * v b) (v a * basis s b)
      _ ≤ 1 * C + C * 1 := by gcongr <;> first | apply hd | exact ha | exact hb
      _ = 2 * C := by ring
  have hp (s t u w : Fin 7) :
      |2 * (basis s a * basis t b + basis t a * basis s b) *
        basis u c * basis w c * (v c)⁻¹ ^ 3| ≤ 4 * R ^ 3 := by
    simp only [abs_mul, abs_pow]
    calc
      _ ≤ |(2 : ℝ)| * 2 * 1 * 1 * R ^ 3 := by
        gcongr <;> first | apply hpair | apply hd | exact hc
      _ = _ := by norm_num
  have hs (s t u w : Fin 7) :
      |6 * (basis s a * v b + v a * basis s b) *
        basis t c * basis u c * basis w c * (v c)⁻¹ ^ 4| ≤ 12 * C * R ^ 4 := by
    simp only [abs_mul, abs_pow]
    calc
      _ ≤ |(6 : ℝ)| * (2 * C) * 1 * 1 * 1 * R ^ 4 := by
        gcongr <;> first | apply hlinear | apply hd | exact hc
      _ = _ := by norm_num <;> ring <;> simp
  have ht : |24 * v a * v b * basis i c * basis j c * basis k c * basis l c *
      (v c)⁻¹ ^ 5| ≤ 24 * C ^ 2 * R ^ 5 := by
    simp only [abs_mul, abs_pow]
    calc
      _ ≤ |(24 : ℝ)| * C * C * 1 * 1 * 1 * 1 * R ^ 5 := by
        gcongr <;> first | exact ha | exact hb | apply hd | exact hc
      _ = _ := by norm_num <;> ring <;> simp
  have hraw : |cubicRatioD4Apply a b c (basis i) (basis j) (basis k) (basis l) v| ≤
      24 * R ^ 3 + 48 * C * R ^ 4 + 24 * C ^ 2 * R ^ 5 := by
    unfold cubicRatioD4Apply
    have hab1 := abs_add_le (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3) (2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3)
    have hab2 := abs_add_le (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3) (2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3)
    have hab3 := abs_add_le (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3) (2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3)
    have hab4 := abs_add_le (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3) (2 * (basis j a * basis l b + basis l a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3)
    have hab5 := abs_add_le (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis l b + basis l a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3) (2 * (basis k a * basis l b + basis l a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3)
    have hab6 := abs_sub (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis l b + basis l a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis k a * basis l b + basis l a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3) (6 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * basis l c * (v c)⁻¹ ^ 4)
    have hab7 := abs_sub (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis l b + basis l a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis k a * basis l b + basis l a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3 -
      6 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * basis l c * (v c)⁻¹ ^ 4) (6 * (basis j a * v b + v a * basis j b) * basis i c * basis k c * basis l c * (v c)⁻¹ ^ 4)
    have hab8 := abs_sub (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis l b + basis l a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis k a * basis l b + basis l a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3 -
      6 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * basis l c * (v c)⁻¹ ^ 4 -
      6 * (basis j a * v b + v a * basis j b) * basis i c * basis k c * basis l c * (v c)⁻¹ ^ 4) (6 * (basis k a * v b + v a * basis k b) * basis i c * basis j c * basis l c * (v c)⁻¹ ^ 4)
    have hab9 := abs_sub (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis l b + basis l a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis k a * basis l b + basis l a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3 -
      6 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * basis l c * (v c)⁻¹ ^ 4 -
      6 * (basis j a * v b + v a * basis j b) * basis i c * basis k c * basis l c * (v c)⁻¹ ^ 4 -
      6 * (basis k a * v b + v a * basis k b) * basis i c * basis j c * basis l c * (v c)⁻¹ ^ 4) (6 * (basis l a * v b + v a * basis l b) * basis i c * basis j c * basis k c * (v c)⁻¹ ^ 4)
    have hab10 := abs_add_le (2 * (basis i a * basis j b + basis j a * basis i b) * basis k c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis k b + basis k a * basis i b) * basis j c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis i a * basis l b + basis l a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis k b + basis k a * basis j b) * basis i c * basis l c * (v c)⁻¹ ^ 3 +
      2 * (basis j a * basis l b + basis l a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3 +
      2 * (basis k a * basis l b + basis l a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3 -
      6 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * basis l c * (v c)⁻¹ ^ 4 -
      6 * (basis j a * v b + v a * basis j b) * basis i c * basis k c * basis l c * (v c)⁻¹ ^ 4 -
      6 * (basis k a * v b + v a * basis k b) * basis i c * basis j c * basis l c * (v c)⁻¹ ^ 4 -
      6 * (basis l a * v b + v a * basis l b) * basis i c * basis j c * basis k c * (v c)⁻¹ ^ 4) (24 * v a * v b * basis i c * basis j c * basis k c * basis l c * (v c)⁻¹ ^ 5)
    linarith [hp i j k l, hp i k j l, hp i l j k, hp j k i l, hp j l i k, hp k l i j, hs i j k l, hs j i k l, hs k i j l, hs l i j k, ht]
  have h3 : R ^ 3 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by omega)
  have h4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by omega)
  calc
    _ ≤ 24 * R ^ 3 + 48 * C * R ^ 4 + 24 * C ^ 2 * R ^ 5 := hraw
    _ ≤ 24 * R ^ 5 + 48 * C * R ^ 5 + 24 * C ^ 2 * R ^ 5 := by
      gcongr
    _ = _ := by ring

-- @node: dPhi4_abs_le
/-- Given [the supplied inputs](hyp:c_f,C_f,hf,hC,A,v,hv,i,j,k,l), [the stated result about d phi4 abs le holds](goal). -/
lemma dPhi4_abs_le (c_f C_f : ℝ)
    (hf : 0 < c_f ∧ c_f < 1) (hC : 1 < C_f)
    (A : Bool) (v : Fin 7 → ℝ) (hv : clippingRectangle c_f C_f v)
    (i j k l : Fin 7) :
    |iteratedFDeriv ℝ 4 (Phi A) v ![basis i, basis j, basis k, basis l]| ≤
      fourthDerivativeEnvelope c_f C_f := by
  have ht : |v 0| ≤ C_f := by
    rw [abs_of_nonneg (le_trans hf.1.le hv.1.1)]
    exact hv.1.2
  have hm (b : Fin 7) (hb : 3 ≤ b.val) : |v b| ≤ C_f := by
    have hbnd := hv.2.2.2 b hb
    rw [abs_of_nonneg hbnd.1]
    linarith [hbnd.2]
  have hq (c : Fin 7) (hc : c_f / 4 ≤ v c) : v c ≠ 0 ∧ |(v c)⁻¹| ≤ 4 / c_f := by
    have hpos : 0 < v c := by linarith
    refine ⟨ne_of_gt hpos, ?_⟩
    rw [abs_of_nonneg (inv_pos.mpr hpos).le]
    calc
      (v c)⁻¹ ≤ (c_f / 4)⁻¹ := (inv_le_inv₀ hpos (div_pos hf.1 (by norm_num))).2 hc
      _ = 4 / c_f := by ring
  have h1 := hq 1 hv.2.1.1
  have h2 := hq 2 hv.2.2.1.1
  have hR : 1 < 4 / c_f := (lt_div_iff₀ hf.1).2 (by linarith [hf.2])
  rw [iteratedFDeriv_four_Phi A v (basis i) (basis j) (basis k) (basis l) h1.1 h2.1]
  have hp := cubicRatioD4_basis_abs_le 0 (if A then 4 else 6) 2 i j k l v C_f (4 / c_f)
    hC hR ht (hm _ (by cases A <;> decide)) h2.2
  have hn := cubicRatioD4_basis_abs_le 0 (if A then 3 else 5) 1 i j k l v C_f (4 / c_f)
    hC hR ht (hm _ (by cases A <;> decide)) h1.2
  exact (abs_sub _ _).trans (by unfold fourthDerivativeEnvelope; linarith)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
