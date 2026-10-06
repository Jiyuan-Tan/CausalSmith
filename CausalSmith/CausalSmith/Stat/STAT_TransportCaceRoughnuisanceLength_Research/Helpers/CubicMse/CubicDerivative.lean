module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Reduction
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.Estimator
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Second and third coordinate derivative envelopes at the clipped pilot -/

@[expose] public section

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: DensityVector
/-- [The density vector object](goal) is defined without additional inputs. -/
abbrev DensityVector := Fin 7 → ℝ

-- @node: densityCoord
/-- [The density coord object](goal) is defined from [the supplied inputs](hyp:r). -/
noncomputable def densityCoord (r : Fin 7) : DensityVector →L[ℝ] ℝ :=
  ContinuousLinearMap.proj r

-- @node: cubicRatioTerm
/-- [The cubic ratio term object](goal) is defined from [the supplied inputs](hyp:a,b,c,v). -/
noncomputable def cubicRatioTerm (a b c : Fin 7) (v : DensityVector) : ℝ :=
  v a * v b * (v c)⁻¹

-- @node: cubicRatioD1
/-- [The cubic ratio d1 object](goal) is defined from [the supplied inputs](hyp:a,b,c,v). -/
noncomputable def cubicRatioD1 (a b c : Fin 7) (v : DensityVector) :
    DensityVector →L[ℝ] ℝ :=
  (v a * v b) • (-(v c)⁻¹ ^ 2 • densityCoord c) +
    (v c)⁻¹ • (v a • densityCoord b + v b • densityCoord a)

-- @node: cubicRatioD1Apply
/-- [The cubic ratio d1 apply object](goal) is defined from [the supplied inputs](hyp:a,b,c,h,v). -/
noncomputable def cubicRatioD1Apply (a b c : Fin 7)
    (h v : DensityVector) : ℝ :=
  (v a * v b) * (-(v c)⁻¹ ^ 2 * h c) +
    (v c)⁻¹ * (h a * v b + v a * h b)

-- @node: cubicRatioD2Apply
/-- [The cubic ratio d2 apply object](goal) is defined from [the supplied inputs](hyp:a,b,c,h,k,v). -/
noncomputable def cubicRatioD2Apply (a b c : Fin 7)
    (h k v : DensityVector) : ℝ :=
  (h a * k b + k a * h b) * (v c)⁻¹ -
    (h a * v b + v a * h b) * k c * (v c)⁻¹ ^ 2 -
    (k a * v b + v a * k b) * h c * (v c)⁻¹ ^ 2 +
    2 * v a * v b * h c * k c * (v c)⁻¹ ^ 3

-- @node: cubicRatioD3Apply
/-- [The cubic ratio d3 apply object](goal) is defined from [the supplied inputs](hyp:a,b,c,h,k,l,v). -/
noncomputable def cubicRatioD3Apply (a b c : Fin 7)
    (h k l v : DensityVector) : ℝ :=
  -(h a * k b + k a * h b) * l c * (v c)⁻¹ ^ 2 -
    ((h a * l b + l a * h b) * k c +
      (k a * l b + l a * k b) * h c) * (v c)⁻¹ ^ 2 +
    2 * (h a * v b + v a * h b) * k c * l c * (v c)⁻¹ ^ 3 +
    2 * (k a * v b + v a * k b) * h c * l c * (v c)⁻¹ ^ 3 +
    2 * (l a * v b + v a * l b) * h c * k c * (v c)⁻¹ ^ 3 -
    6 * v a * v b * h c * k c * l c * (v c)⁻¹ ^ 4

-- @node: hasFDerivAt_cubicRatioTerm
/-- Given [the supplied inputs](hyp:a,b,c,v,hc), [the stated result about has fderiv at cubic ratio term holds](goal). -/
lemma hasFDerivAt_cubicRatioTerm (a b c : Fin 7) (v : DensityVector)
    (hc : v c ≠ 0) :
    HasFDerivAt (cubicRatioTerm a b c) (cubicRatioD1 a b c v) v := by
  have ha := (densityCoord a).hasFDerivAt (x := v)
  have hb := (densityCoord b).hasFDerivAt (x := v)
  have hc' := (densityCoord c).hasFDerivAt (x := v)
  have hi := (hasFDerivAt_inv hc).comp v hc'
  refine ((ha.mul hb).mul hi).congr_fderiv ?_
  ext h
  simp [cubicRatioD1, densityCoord, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp [hc]
  <;> simp

-- @node: cubicRatioD1_apply
/-- Given [the supplied inputs](hyp:a,b,c,v,h), [the stated result about cubic ratio d1 apply holds](goal). -/
lemma cubicRatioD1_apply (a b c : Fin 7) (v h : DensityVector) :
    cubicRatioD1 a b c v h = cubicRatioD1Apply a b c h v := by
  simp only [cubicRatioD1, cubicRatioD1Apply, densityCoord,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

-- @node: fderiv_cubicRatioD1Apply
/-- Given [the supplied inputs](hyp:a,b,c,v,h,k,hc), [the stated result about fderiv cubic ratio d1 apply holds](goal). -/
lemma fderiv_cubicRatioD1Apply (a b c : Fin 7) (v h k : DensityVector)
    (hc : v c ≠ 0) :
    fderiv ℝ (fun y => cubicRatioD1Apply a b c k y) v h =
      cubicRatioD2Apply a b c h k v := by
  have ha := (densityCoord a).hasFDerivAt (x := v)
  have hb := (densityCoord b).hasFDerivAt (x := v)
  have hc' := (densityCoord c).hasFDerivAt (x := v)
  have hi := (hasFDerivAt_inv hc).comp v hc'
  have hp := ha.mul hb
  have hi2 := hi.mul hi
  have hs := (ha.mul_const (k b)).add (hb.mul_const (k a))
  have ht := (hp.mul (hi2.mul_const (-k c))).add (hi.mul hs)
  have ht' := ht.congr_of_eventuallyEq (f₁ := fun y => cubicRatioD1Apply a b c k y)
      (Filter.Eventually.of_forall (fun y => by
    simp [cubicRatioD1Apply, densityCoord, Function.comp_apply]
    ring))
  rw [ht'.fderiv]
  simp [cubicRatioD2Apply, densityCoord, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp [hc]
  <;> ring

-- @node: fderiv_cubicRatioD2Apply
/-- Given [the supplied inputs](hyp:a,b,c,v,h,k,l,hc), [the stated result about fderiv cubic ratio d2 apply holds](goal). -/
lemma fderiv_cubicRatioD2Apply (a b c : Fin 7)
    (v h k l : DensityVector) (hc : v c ≠ 0) :
    fderiv ℝ (fun y => cubicRatioD2Apply a b c k l y) v h =
      cubicRatioD3Apply a b c h k l v := by
  have ha := (densityCoord a).hasFDerivAt (x := v)
  have hb := (densityCoord b).hasFDerivAt (x := v)
  have hc' := (densityCoord c).hasFDerivAt (x := v)
  have hi := (hasFDerivAt_inv hc).comp v hc'
  have hi2 := hi.mul hi
  have hi3 := hi2.mul hi
  have hp := ha.mul hb
  have ht1 := hi.const_mul (k a * l b + l a * k b)
  have hsk := (hb.const_mul (k a)).add (ha.mul_const (k b))
  have hsl := (hb.const_mul (l a)).add (ha.mul_const (l b))
  have ht2 := ((hsk.mul_const (l c)).mul hi2)
  have ht3 := ((hsl.mul_const (k c)).mul hi2)
  have ht4 := (hp.mul hi3).const_mul (2 * k c * l c)
  have ht := ((ht1.sub ht2).sub ht3).add ht4
  have ht' := ht.congr_of_eventuallyEq (f₁ := fun y => cubicRatioD2Apply a b c k l y)
      (Filter.Eventually.of_forall (fun y => by
    simp [cubicRatioD2Apply, densityCoord, Function.comp_apply]
    ring))
  rw [ht'.fderiv]
  simp [cubicRatioD3Apply, densityCoord, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp [hc]
  <;> ring

-- @node: iteratedFDeriv_one_cubicRatioTerm
/-- Given [the supplied inputs](hyp:a,b,c,v,h,hc), [the stated result about iterated fderiv one cubic ratio term holds](goal). -/
lemma iteratedFDeriv_one_cubicRatioTerm (a b c : Fin 7)
    (v h : DensityVector) (hc : v c ≠ 0) :
    iteratedFDeriv ℝ 1 (cubicRatioTerm a b c) v ![h] =
      cubicRatioD1Apply a b c h v := by
  rw [iteratedFDeriv_one_apply, (hasFDerivAt_cubicRatioTerm a b c v hc).fderiv]
  exact cubicRatioD1_apply a b c v h

-- @node: iteratedFDeriv_two_cubicRatioTerm
/-- Given [the supplied inputs](hyp:a,b,c,v,h,k,hc), [the stated result about iterated fderiv two cubic ratio term holds](goal). -/
lemma iteratedFDeriv_two_cubicRatioTerm (a b c : Fin 7)
    (v h k : DensityVector) (hc : v c ≠ 0) :
    iteratedFDeriv ℝ 2 (cubicRatioTerm a b c) v ![h, k] =
      cubicRatioD2Apply a b c h k v := by
  have hs : ContDiffAt ℝ 2 (cubicRatioTerm a b c) v := by
    unfold cubicRatioTerm
    fun_prop
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (cubicRatioTerm a b c)) v :=
    hs.differentiableAt_iteratedFDeriv (by norm_num)
  rw [hd.iteratedFDeriv_succ_apply_left']
  have hne : ∀ᶠ y in nhds v, y c ≠ 0 :=
    (densityCoord c).continuous.continuousAt.eventually_ne hc
  have heq :
      (fun y => iteratedFDeriv ℝ 1 (cubicRatioTerm a b c) y
        (Fin.tail ![h, k])) =ᶠ[nhds v]
      (fun y => cubicRatioD1Apply a b c k y) := by
    filter_upwards [hne] with y hy
    simpa using iteratedFDeriv_one_cubicRatioTerm a b c y k hy
  rw [heq.fderiv_eq]
  simpa using fderiv_cubicRatioD1Apply a b c v h k hc

-- @node: iteratedFDeriv_three_cubicRatioTerm
/-- Given [the supplied inputs](hyp:a,b,c,v,h,k,l,hc), [the stated result about iterated fderiv three cubic ratio term holds](goal). -/
lemma iteratedFDeriv_three_cubicRatioTerm (a b c : Fin 7)
    (v h k l : DensityVector) (hc : v c ≠ 0) :
    iteratedFDeriv ℝ 3 (cubicRatioTerm a b c) v ![h, k, l] =
      cubicRatioD3Apply a b c h k l v := by
  have hs : ContDiffAt ℝ 3 (cubicRatioTerm a b c) v := by
    unfold cubicRatioTerm
    fun_prop
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 (cubicRatioTerm a b c)) v :=
    hs.differentiableAt_iteratedFDeriv (by norm_num)
  rw [hd.iteratedFDeriv_succ_apply_left']
  have hne : ∀ᶠ y in nhds v, y c ≠ 0 :=
    (densityCoord c).continuous.continuousAt.eventually_ne hc
  have heq :
      (fun y => iteratedFDeriv ℝ 2 (cubicRatioTerm a b c) y
        (Fin.tail ![h, k, l])) =ᶠ[nhds v]
      (fun y => cubicRatioD2Apply a b c k l y) := by
    filter_upwards [hne] with y hy
    simpa using iteratedFDeriv_two_cubicRatioTerm a b c y k l hy
  rw [heq.fderiv_eq]
  simpa using fderiv_cubicRatioD2Apply a b c v h k l hc

-- @node: iteratedFDeriv_three_Phi
/-- Given [the supplied inputs](hyp:A,v,h,k,l,h1,h2), [the stated result about iterated fderiv three phi holds](goal). -/
lemma iteratedFDeriv_three_Phi (A : Bool) (v : DensityVector)
    (h k l : DensityVector) (h1 : v 1 ≠ 0) (h2 : v 2 ≠ 0) :
    iteratedFDeriv ℝ 3 (Phi A) v ![h, k, l] =
      cubicRatioD3Apply 0 (if A then 4 else 6) 2 h k l v -
        cubicRatioD3Apply 0 (if A then 3 else 5) 1 h k l v := by
  cases A with
  | false =>
      have hs2 : ContDiffAt ℝ 3 (cubicRatioTerm 0 6 2) v := by
        unfold cubicRatioTerm
        fun_prop
      have hs1 : ContDiffAt ℝ 3 (cubicRatioTerm 0 5 1) v := by
        unfold cubicRatioTerm
        fun_prop
      have heq : Phi false = cubicRatioTerm 0 6 2 - cubicRatioTerm 0 5 1 := by
        funext y
        simp [Phi, cubicRatioTerm, div_eq_mul_inv]
        ring
      rw [heq, iteratedFDeriv_sub_apply hs2 hs1]
      change iteratedFDeriv ℝ 3 (cubicRatioTerm 0 6 2) v ![h, k, l] -
          iteratedFDeriv ℝ 3 (cubicRatioTerm 0 5 1) v ![h, k, l] = _
      rw [
        iteratedFDeriv_three_cubicRatioTerm 0 6 2 v h k l h2,
        iteratedFDeriv_three_cubicRatioTerm 0 5 1 v h k l h1]
      simp
  | true =>
      have hs2 : ContDiffAt ℝ 3 (cubicRatioTerm 0 4 2) v := by
        unfold cubicRatioTerm
        fun_prop
      have hs1 : ContDiffAt ℝ 3 (cubicRatioTerm 0 3 1) v := by
        unfold cubicRatioTerm
        fun_prop
      have heq : Phi true = cubicRatioTerm 0 4 2 - cubicRatioTerm 0 3 1 := by
        funext y
        simp [Phi, cubicRatioTerm, div_eq_mul_inv]
        ring
      rw [heq, iteratedFDeriv_sub_apply hs2 hs1]
      change iteratedFDeriv ℝ 3 (cubicRatioTerm 0 4 2) v ![h, k, l] -
          iteratedFDeriv ℝ 3 (cubicRatioTerm 0 3 1) v ![h, k, l] = _
      rw [
        iteratedFDeriv_three_cubicRatioTerm 0 4 2 v h k l h2,
        iteratedFDeriv_three_cubicRatioTerm 0 3 1 v h k l h1]
      simp

-- @node: iteratedFDeriv_two_Phi
/-- Given [the supplied inputs](hyp:A,v,h,k,h1,h2), [the stated result about iterated fderiv two phi holds](goal). -/
lemma iteratedFDeriv_two_Phi (A : Bool) (v : DensityVector)
    (h k : DensityVector) (h1 : v 1 ≠ 0) (h2 : v 2 ≠ 0) :
    iteratedFDeriv ℝ 2 (Phi A) v ![h, k] =
      cubicRatioD2Apply 0 (if A then 4 else 6) 2 h k v -
        cubicRatioD2Apply 0 (if A then 3 else 5) 1 h k v := by
  cases A with
  | false =>
      have hs2 : ContDiffAt ℝ 2 (cubicRatioTerm 0 6 2) v := by
        unfold cubicRatioTerm
        fun_prop
      have hs1 : ContDiffAt ℝ 2 (cubicRatioTerm 0 5 1) v := by
        unfold cubicRatioTerm
        fun_prop
      have heq : Phi false = cubicRatioTerm 0 6 2 - cubicRatioTerm 0 5 1 := by
        funext y
        simp [Phi, cubicRatioTerm, div_eq_mul_inv]
        ring
      rw [heq, iteratedFDeriv_sub_apply hs2 hs1]
      change iteratedFDeriv ℝ 2 (cubicRatioTerm 0 6 2) v ![h, k] -
          iteratedFDeriv ℝ 2 (cubicRatioTerm 0 5 1) v ![h, k] = _
      rw [
        iteratedFDeriv_two_cubicRatioTerm 0 6 2 v h k h2,
        iteratedFDeriv_two_cubicRatioTerm 0 5 1 v h k h1]
      simp
  | true =>
      have hs2 : ContDiffAt ℝ 2 (cubicRatioTerm 0 4 2) v := by
        unfold cubicRatioTerm
        fun_prop
      have hs1 : ContDiffAt ℝ 2 (cubicRatioTerm 0 3 1) v := by
        unfold cubicRatioTerm
        fun_prop
      have heq : Phi true = cubicRatioTerm 0 4 2 - cubicRatioTerm 0 3 1 := by
        funext y
        simp [Phi, cubicRatioTerm, div_eq_mul_inv]
        ring
      rw [heq, iteratedFDeriv_sub_apply hs2 hs1]
      change iteratedFDeriv ℝ 2 (cubicRatioTerm 0 4 2) v ![h, k] -
          iteratedFDeriv ℝ 2 (cubicRatioTerm 0 3 1) v ![h, k] = _
      rw [
        iteratedFDeriv_two_cubicRatioTerm 0 4 2 v h k h2,
        iteratedFDeriv_two_cubicRatioTerm 0 3 1 v h k h1]
      simp

/-- The explicit second derivative of one marked ratio has a uniform coordinate bound.  Under [the displayed assumptions and inputs](hyp:a,b,c,i,j,v,C,R,hC,hR,ha,hb,hc), [the stated conclusion holds](goal). -/
-- @node: cubicRatioD2_basis_abs_le
lemma cubicRatioD2_basis_abs_le (a b c i j : Fin 7)
    (v : DensityVector) (C R : ℝ) (hC : 1 < C) (hR : 1 < R)
    (ha : |v a| ≤ C) (hb : |v b| ≤ C) (hc : |(v c)⁻¹| ≤ R) :
    |cubicRatioD2Apply a b c (basis i) (basis j) v| ≤
      24 * (1 + C) ^ 2 * R ^ 5 := by
  have hC0 : 0 ≤ C := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hd (s r : Fin 7) : |basis s r| ≤ 1 := by
    by_cases hrs : r = s <;> simp [basis, hrs]
  have hpair : |basis i a * basis j b + basis j a * basis i b| ≤ 2 := by
    calc
      _ ≤ |basis i a| * |basis j b| + |basis j a| * |basis i b| := by
        simpa only [abs_mul] using abs_add_le (basis i a * basis j b) (basis j a * basis i b)
      _ ≤ 1 * 1 + 1 * 1 := by gcongr <;> apply hd
      _ = 2 := by norm_num
  have hlinear (s : Fin 7) : |basis s a * v b + v a * basis s b| ≤ 2 * C := by
    calc
      _ ≤ |basis s a| * |v b| + |v a| * |basis s b| := by
        simpa only [abs_mul] using abs_add_le (basis s a * v b) (v a * basis s b)
      _ ≤ 1 * C + C * 1 := by gcongr <;> first | apply hd | exact ha | exact hb
      _ = 2 * C := by ring
  have ht1 : |(basis i a * basis j b + basis j a * basis i b) * (v c)⁻¹| ≤ 2 * R := by
    rw [abs_mul]
    exact mul_le_mul hpair hc (abs_nonneg _) (by norm_num)
  have ht2 (s t : Fin 7) :
      |(basis s a * v b + v a * basis s b) * basis t c * (v c)⁻¹ ^ 2| ≤ 2 * C * R ^ 2 := by
    simp only [abs_mul, abs_pow]
    calc
      _ ≤ (2 * C) * 1 * R ^ 2 := by gcongr <;> first | apply hlinear | apply hd | exact hc
      _ = _ := by ring
  have ht4 : |2 * v a * v b * basis i c * basis j c * (v c)⁻¹ ^ 3| ≤ 2 * C ^ 2 * R ^ 3 := by
    simp only [abs_mul, abs_pow]
    norm_num
    have hp : (|v c| ^ 3)⁻¹ ≤ R ^ 3 := by
      simpa only [abs_inv, inv_pow] using pow_le_pow_left₀ (abs_nonneg _) hc 3
    calc
      _ ≤ 2 * C * C * 1 * 1 * R ^ 3 := by gcongr <;> first | exact ha | exact hb | apply hd | exact hp
      _ = _ := by ring
  have hraw : |cubicRatioD2Apply a b c (basis i) (basis j) v| ≤
      2 * R + 4 * C * R ^ 2 + 2 * C ^ 2 * R ^ 3 := by
    unfold cubicRatioD2Apply
    calc
      _ ≤ |(basis i a * basis j b + basis j a * basis i b) * (v c)⁻¹ -
          (basis i a * v b + v a * basis i b) * basis j c * (v c)⁻¹ ^ 2 -
          (basis j a * v b + v a * basis j b) * basis i c * (v c)⁻¹ ^ 2| +
          |2 * v a * v b * basis i c * basis j c * (v c)⁻¹ ^ 3| := abs_add_le _ _
      _ ≤ _ := by
        have hsub := abs_sub
          ((basis i a * basis j b + basis j a * basis i b) * (v c)⁻¹ -
            (basis i a * v b + v a * basis i b) * basis j c * (v c)⁻¹ ^ 2)
          ((basis j a * v b + v a * basis j b) * basis i c * (v c)⁻¹ ^ 2)
        have hsub' := abs_sub
          ((basis i a * basis j b + basis j a * basis i b) * (v c)⁻¹)
          ((basis i a * v b + v a * basis i b) * basis j c * (v c)⁻¹ ^ 2)
        linarith [ht2 i j, ht2 j i]
  have hp1 : R ≤ R ^ 5 := by simpa using pow_le_pow_right₀ hR.le (show 1 ≤ 5 by omega)
  have hp2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by omega)
  have hp3 : R ^ 3 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by omega)
  have hC1 : 1 ≤ (1 + C) ^ 2 := by nlinarith
  have hC2 : C ≤ (1 + C) ^ 2 := by nlinarith [sq_nonneg C]
  have hC3 : C ^ 2 ≤ (1 + C) ^ 2 := by nlinarith
  have h1 := mul_le_mul hC1 hp1 hR0 (by positivity : 0 ≤ (1 + C) ^ 2)
  have h2 := mul_le_mul hC2 hp2 (by positivity) (by positivity : 0 ≤ (1 + C) ^ 2)
  have h3 := mul_le_mul hC3 hp3 (by positivity) (by positivity : 0 ≤ (1 + C) ^ 2)
  exact hraw.trans (by nlinarith [mul_nonneg (sq_nonneg (1 + C)) (by positivity : 0 ≤ R ^ 5)])

/-- The second coordinate derivative has the same deterministic envelope as orders zero and one.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,hf,hC,A,v,hv,i,j), [the stated conclusion holds](goal). -/
-- @node: dPhi2_abs_le
lemma dPhi2_abs_le (c_f C_f : ℝ)
    (hf : 0 < c_f ∧ c_f < 1) (hC : 1 < C_f)
    (A : Bool) (v : Fin 7 → ℝ) (hv : clippingRectangle c_f C_f v)
    (i j : Fin 7) :
    |iteratedFDeriv ℝ 2 (Phi A) v ![basis i, basis j]| ≤
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
  rw [iteratedFDeriv_two_Phi A v (basis i) (basis j) h1.1 h2.1]
  have hp := cubicRatioD2_basis_abs_le 0 (if A then 4 else 6) 2 i j v C_f (4 / c_f)
    hC hR ht (hm _ (by cases A <;> decide)) h2.2
  have hn := cubicRatioD2_basis_abs_le 0 (if A then 3 else 5) 1 i j v C_f (4 / c_f)
    hC hR ht (hm _ (by cases A <;> decide)) h1.2
  exact (abs_sub _ _).trans (by unfold fourthDerivativeEnvelope; linarith)

-- @node: cubicRatioD3_basis_abs_le
/-- Given [the supplied inputs](hyp:a,b,c,i,j,k,v,C,R,hC,hR,ha0,haC,hb0,hbC,hc0,hcR), [the stated result about cubic ratio d3 basis abs le holds](goal). -/
lemma cubicRatioD3_basis_abs_le (a b c i j k : Fin 7)
    (v : DensityVector) (C R : ℝ)
    (hC : 1 < C) (hR : 1 < R)
    (ha0 : 0 ≤ v a) (haC : v a ≤ C)
    (hb0 : 0 ≤ v b) (hbC : v b ≤ C)
    (hc0 : 0 < v c) (hcR : (v c)⁻¹ ≤ R) :
    |cubicRatioD3Apply a b c (basis i) (basis j) (basis k) v| ≤
      24 * (1 + C) ^ 2 * R ^ 5 := by
  have hdir (s r : Fin 7) : |basis s r| ≤ 1 := by
    by_cases hrs : r = s <;> simp [basis, hrs]
  have hi0 : 0 ≤ (v c)⁻¹ := (inv_pos.mpr hc0).le
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR.le
  have haAbs : |v a| ≤ C := by simpa [abs_of_nonneg ha0] using haC
  have hbAbs : |v b| ≤ C := by simpa [abs_of_nonneg hb0] using hbC
  have hInvAbs : |(v c)⁻¹| ≤ R := by simpa [abs_of_nonneg hi0] using hcR
  have hs1 :
      |basis i a * basis j b + basis j a * basis i b| ≤ 2 := by
    calc
      _ ≤ |basis i a * basis j b| + |basis j a * basis i b| := abs_add_le _ _
      _ ≤ 2 := by
        rw [abs_mul, abs_mul]
        have hia := hdir i a
        have hjb := hdir j b
        have hja := hdir j a
        have hib := hdir i b
        nlinarith [abs_nonneg (basis i a), abs_nonneg (basis j b),
          abs_nonneg (basis j a), abs_nonneg (basis i b),
          mul_nonneg (sub_nonneg.mpr hia) (abs_nonneg (basis j b)),
          mul_nonneg (sub_nonneg.mpr hjb) (abs_nonneg (basis i a)),
          mul_nonneg (sub_nonneg.mpr hja) (abs_nonneg (basis i b)),
          mul_nonneg (sub_nonneg.mpr hib) (abs_nonneg (basis j a))]
  have hs2 :
      |(basis i a * basis k b + basis k a * basis i b) * basis j c +
        (basis j a * basis k b + basis k a * basis j b) * basis i c| ≤ 4 := by
    calc
      _ ≤ |basis i a * basis k b + basis k a * basis i b| * |basis j c| +
          |basis j a * basis k b + basis k a * basis j b| * |basis i c| := by
            simpa only [abs_mul] using abs_add_le
              ((basis i a * basis k b + basis k a * basis i b) * basis j c)
              ((basis j a * basis k b + basis k a * basis j b) * basis i c)
      _ ≤ 4 := by
        have h1 : |basis i a * basis k b + basis k a * basis i b| ≤ 2 := by
          calc
            _ ≤ |basis i a * basis k b| + |basis k a * basis i b| := abs_add_le _ _
            _ ≤ 2 := by
              rw [abs_mul, abs_mul]
              nlinarith [hdir i a, hdir k b, hdir k a, hdir i b,
                abs_nonneg (basis i a), abs_nonneg (basis k b),
                abs_nonneg (basis k a), abs_nonneg (basis i b)]
        have h2 : |basis j a * basis k b + basis k a * basis j b| ≤ 2 := by
          calc
            _ ≤ |basis j a * basis k b| + |basis k a * basis j b| := abs_add_le _ _
            _ ≤ 2 := by
              rw [abs_mul, abs_mul]
              nlinarith [hdir j a, hdir k b, hdir k a, hdir j b,
                abs_nonneg (basis j a), abs_nonneg (basis k b),
                abs_nonneg (basis k a), abs_nonneg (basis j b)]
        nlinarith [hdir j c, hdir i c, abs_nonneg (basis j c),
          abs_nonneg (basis i c), mul_nonneg (sub_nonneg.mpr h1) (abs_nonneg (basis j c)),
          mul_nonneg (sub_nonneg.mpr h2) (abs_nonneg (basis i c))]
  have hpair (s : Fin 7) : |basis s a * v b + v a * basis s b| ≤ 2 * C := by
    calc
      _ ≤ |basis s a| * |v b| + |v a| * |basis s b| := by
        simpa only [abs_mul] using
          abs_add_le (basis s a * v b) (v a * basis s b)
      _ ≤ 2 * C := by
        have hC0 : 0 ≤ C := le_trans (by norm_num) hC.le
        nlinarith [hdir s a, hdir s b, abs_nonneg (basis s a),
          abs_nonneg (basis s b), haAbs, hbAbs,
          mul_nonneg (sub_nonneg.mpr (hdir s a)) (abs_nonneg (v b)),
          mul_nonneg (sub_nonneg.mpr hbAbs) (abs_nonneg (basis s a)),
          mul_nonneg (sub_nonneg.mpr haAbs) (abs_nonneg (basis s b)),
          mul_nonneg (sub_nonneg.mpr (hdir s b)) (abs_nonneg (v a))]
  have hraw :
      |cubicRatioD3Apply a b c (basis i) (basis j) (basis k) v| ≤
        6 * R ^ 2 + 12 * C * R ^ 3 + 6 * C ^ 2 * R ^ 4 := by
    unfold cubicRatioD3Apply
    have habs6 (x1 x2 x3 x4 x5 x6 : ℝ) :
        |x1 + x2 + x3 + x4 + x5 + x6| ≤
          |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by
      calc
        _ ≤ |x1 + x2 + x3 + x4 + x5| + |x6| := abs_add_le _ _
        _ ≤ (|x1 + x2 + x3 + x4| + |x5|) + |x6| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|x1 + x2 + x3| + |x4|) + |x5|) + |x6| := by gcongr; exact abs_add_le _ _
        _ ≤ (((|x1 + x2| + |x3|) + |x4|) + |x5|) + |x6| := by gcongr; exact abs_add_le _ _
        _ ≤ ((((|x1| + |x2|) + |x3|) + |x4|) + |x5|) + |x6| := by
          gcongr; exact abs_add_le _ _
        _ = _ := by ring
    calc
      _ ≤ |-(basis i a * basis j b + basis j a * basis i b) * basis k c * (v c)⁻¹ ^ 2| +
          |((basis i a * basis k b + basis k a * basis i b) * basis j c +
            (basis j a * basis k b + basis k a * basis j b) * basis i c) * (v c)⁻¹ ^ 2| +
          |2 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3| +
          |2 * (basis j a * v b + v a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3| +
          |2 * (basis k a * v b + v a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3| +
          |6 * v a * v b * basis i c * basis j c * basis k c * (v c)⁻¹ ^ 4| := by
            calc
              _ = |(-(basis i a * basis j b + basis j a * basis i b) * basis k c * (v c)⁻¹ ^ 2) +
                    (-((basis i a * basis k b + basis k a * basis i b) * basis j c +
                      (basis j a * basis k b + basis k a * basis j b) * basis i c) * (v c)⁻¹ ^ 2) +
                    (2 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3) +
                    (2 * (basis j a * v b + v a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3) +
                    (2 * (basis k a * v b + v a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3) +
                    (-6 * v a * v b * basis i c * basis j c * basis k c * (v c)⁻¹ ^ 4)| := by
                      congr 1
                      ring
              _ ≤ |-(basis i a * basis j b + basis j a * basis i b) * basis k c * (v c)⁻¹ ^ 2| +
                    |-((basis i a * basis k b + basis k a * basis i b) * basis j c +
                      (basis j a * basis k b + basis k a * basis j b) * basis i c) * (v c)⁻¹ ^ 2| +
                    |2 * (basis i a * v b + v a * basis i b) * basis j c * basis k c * (v c)⁻¹ ^ 3| +
                    |2 * (basis j a * v b + v a * basis j b) * basis i c * basis k c * (v c)⁻¹ ^ 3| +
                    |2 * (basis k a * v b + v a * basis k b) * basis i c * basis j c * (v c)⁻¹ ^ 3| +
                    |-6 * v a * v b * basis i c * basis j c * basis k c * (v c)⁻¹ ^ 4| :=
                      habs6 _ _ _ _ _ _
              _ = _ := by
                rw [show -((basis i a * basis k b + basis k a * basis i b) * basis j c +
                    (basis j a * basis k b + basis k a * basis j b) * basis i c) * (v c)⁻¹ ^ 2 =
                    -(((basis i a * basis k b + basis k a * basis i b) * basis j c +
                      (basis j a * basis k b + basis k a * basis j b) * basis i c) *
                        (v c)⁻¹ ^ 2) by ring, abs_neg]
                rw [show -6 * v a * v b * basis i c * basis j c * basis k c * (v c)⁻¹ ^ 4 =
                    -(6 * v a * v b * basis i c * basis j c * basis k c * (v c)⁻¹ ^ 4) by ring,
                  abs_neg]
      _ ≤ 6 * R ^ 2 + 12 * C * R ^ 3 + 6 * C ^ 2 * R ^ 4 := by
        simp only [abs_mul, abs_neg, abs_pow]
        norm_num
        have hC0 : 0 ≤ C := le_trans (by norm_num) hC.le
        have hT1 :
            |basis i a * basis j b + basis j a * basis i b| * |basis k c| * |(v c)⁻¹| ^ 2 ≤
              2 * R ^ 2 := by
          have hp : |basis i a * basis j b + basis j a * basis i b| * |basis k c| ≤ 2 := by
            nlinarith [hs1, hdir k c, abs_nonneg (basis k c),
              mul_nonneg (sub_nonneg.mpr hs1) (abs_nonneg (basis k c)),
              mul_nonneg (sub_nonneg.mpr (hdir k c))
                (abs_nonneg (basis i a * basis j b + basis j a * basis i b))]
          exact mul_le_mul hp (pow_le_pow_left₀ (abs_nonneg _) hInvAbs 2)
            (by positivity) (by positivity)
        have hT2 :
            |(basis i a * basis k b + basis k a * basis i b) * basis j c +
              (basis j a * basis k b + basis k a * basis j b) * basis i c| * |(v c)⁻¹| ^ 2 ≤
              4 * R ^ 2 := by
          exact mul_le_mul hs2 (pow_le_pow_left₀ (abs_nonneg _) hInvAbs 2)
            (by positivity) (by positivity)
        have hT3 (s t u : Fin 7) :
            2 * |basis s a * v b + v a * basis s b| * |basis t c| * |basis u c| * |(v c)⁻¹| ^ 3 ≤
              4 * C * R ^ 3 := by
          have hp : 2 * |basis s a * v b + v a * basis s b| * |basis t c| * |basis u c| ≤
              4 * C := by
            have hp1 := mul_le_mul (hpair s) (hdir t c) (abs_nonneg (basis t c))
              (by positivity : 0 ≤ 2 * C)
            have hp2 := mul_le_mul hp1 (hdir u c) (abs_nonneg (basis u c))
              (by positivity : 0 ≤ 2 * C * 1)
            nlinarith
          exact mul_le_mul hp (pow_le_pow_left₀ (abs_nonneg _) hInvAbs 3)
            (by positivity) (by positivity)
        have hT4 :
            6 * |v a| * |v b| * |basis i c| * |basis j c| * |basis k c| * |(v c)⁻¹| ^ 4 ≤
              6 * C ^ 2 * R ^ 4 := by
          have hp : 6 * |v a| * |v b| * |basis i c| * |basis j c| * |basis k c| ≤
              6 * C ^ 2 := by
            have hab := mul_le_mul haAbs hbAbs (abs_nonneg (v b)) (by positivity : 0 ≤ C)
            have habi := mul_le_mul hab (hdir i c) (abs_nonneg (basis i c)) (by positivity : 0 ≤ C * C)
            have habij := mul_le_mul habi (hdir j c) (abs_nonneg (basis j c))
              (by positivity : 0 ≤ C * C * 1)
            have habijk := mul_le_mul habij (hdir k c) (abs_nonneg (basis k c))
              (by positivity : 0 ≤ C * C * 1 * 1)
            nlinarith
          exact mul_le_mul hp (pow_le_pow_left₀ (abs_nonneg _) hInvAbs 4)
            (by positivity) (by positivity)
        have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hT1 hT2)
          (hT3 i j k)) (hT3 j i k)) (hT3 k i j)) hT4
        have hsum' := hsum
        simp only [abs_inv, abs_of_pos hc0, inv_pow] at hsum'
        rw [abs_of_pos hc0]
        nlinarith
  calc
    _ ≤ 6 * R ^ 2 + 12 * C * R ^ 3 + 6 * C ^ 2 * R ^ 4 := hraw
    _ ≤ 24 * (1 + C) ^ 2 * R ^ 5 := by
      have hR2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by omega)
      have hR3 : R ^ 3 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by omega)
      have hR4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR.le (by omega)
      have hC0 : 0 ≤ C := le_trans (by norm_num) hC.le
      have hC_sq : C ^ 2 ≤ (1 + C) ^ 2 := by nlinarith
      have hC_lin : C ≤ (1 + C) ^ 2 := by nlinarith [sq_nonneg C]
      nlinarith [mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ 6 * (1 + C) ^ 2),
        mul_le_mul_of_nonneg_left hR3 (by positivity : 0 ≤ 12 * (1 + C) ^ 2),
        mul_le_mul hC_sq hR4 (by positivity) (by positivity)]

-- @node: dPhi3_abs_le
/-- Given [the supplied inputs](hyp:c_f,C_f,hf,hC,A,v,hv,i,j,k), [the stated result about d phi3 abs le holds](goal). -/
lemma dPhi3_abs_le (c_f C_f : ℝ)
    (hf : 0 < c_f ∧ c_f < 1) (hC : 1 < C_f)
    (A : Bool) (v : Fin 7 → ℝ) (hv : clippingRectangle c_f C_f v)
    (i j k : Fin 7) :
    |iteratedFDeriv ℝ 3 (Phi A) v ![basis i, basis j, basis k]| ≤
      fourthDerivativeEnvelope c_f C_f := by
  rcases hv with ⟨hv0, hv1, hv2, hvmark⟩
  have hC0 : 0 < C_f := lt_trans (by norm_num) hC
  have hv0nonneg : 0 ≤ v 0 := le_trans hf.1.le hv0.1
  have hv1pos : 0 < v 1 := lt_of_lt_of_le (by nlinarith [hf.1]) hv1.1
  have hv2pos : 0 < v 2 := lt_of_lt_of_le (by nlinarith [hf.1]) hv2.1
  have hR : 1 < 4 / c_f := (lt_div_iff₀ hf.1).2 (by nlinarith [hf.2])
  have hinv (q : ℝ) (hq : c_f / 4 ≤ q) : q⁻¹ ≤ 4 / c_f := by
    have hqpos : 0 < q := lt_of_lt_of_le (by nlinarith [hf.1]) hq
    calc
      q⁻¹ ≤ (c_f / 4)⁻¹ :=
        (inv_le_inv₀ hqpos (by nlinarith [hf.1] : 0 < c_f / 4)).2 hq
      _ = 4 / c_f := by field_simp
  have hmarkC (r : Fin 7) (hr : 3 ≤ r.val) : 0 ≤ v r ∧ v r ≤ C_f := by
    have hrange := hvmark r hr
    exact ⟨hrange.1, le_trans hrange.2 (by nlinarith [hC0])⟩
  have hterm (b c : Fin 7) (hb : 3 ≤ b.val)
      (hcpos : 0 < v c) (hclower : c_f / 4 ≤ v c) :
      |cubicRatioD3Apply 0 b c (basis i) (basis j) (basis k) v| ≤
        24 * (1 + C_f) ^ 2 * (4 / c_f) ^ 5 := by
    have hbnd := hmarkC b hb
    exact cubicRatioD3_basis_abs_le 0 b c i j k v C_f (4 / c_f)
      hC hR hv0nonneg hv0.2 hbnd.1 hbnd.2 hcpos (hinv (v c) hclower)
  have h1ne : v 1 ≠ 0 := ne_of_gt hv1pos
  have h2ne : v 2 ≠ 0 := ne_of_gt hv2pos
  rw [iteratedFDeriv_three_Phi A v (basis i) (basis j) (basis k) h1ne h2ne]
  cases A with
  | false =>
      calc
        |cubicRatioD3Apply 0 6 2 (basis i) (basis j) (basis k) v -
            cubicRatioD3Apply 0 5 1 (basis i) (basis j) (basis k) v| ≤
            |cubicRatioD3Apply 0 6 2 (basis i) (basis j) (basis k) v| +
              |cubicRatioD3Apply 0 5 1 (basis i) (basis j) (basis k) v| := abs_sub _ _
        _ ≤ 48 * (1 + C_f) ^ 2 * (4 / c_f) ^ 5 := by
          nlinarith [hterm 6 2 (by norm_num) hv2pos hv2.1,
            hterm 5 1 (by norm_num) hv1pos hv1.1]
        _ = fourthDerivativeEnvelope c_f C_f := by rfl
  | true =>
      calc
        |cubicRatioD3Apply 0 4 2 (basis i) (basis j) (basis k) v -
            cubicRatioD3Apply 0 3 1 (basis i) (basis j) (basis k) v| ≤
            |cubicRatioD3Apply 0 4 2 (basis i) (basis j) (basis k) v| +
              |cubicRatioD3Apply 0 3 1 (basis i) (basis j) (basis k) v| := abs_sub _ _
        _ ≤ 48 * (1 + C_f) ^ 2 * (4 / c_f) ^ 5 := by
          nlinarith [hterm 4 2 (by norm_num) hv2pos hv2.1,
            hterm 3 1 (by norm_num) hv1pos hv1.1]
        _ = fourthDerivativeEnvelope c_f C_f := by rfl

-- @node: pilot_mem_clippingRectangle
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hn,hP,w,x), [the stated result about pilot mem clipping rectangle holds](goal). -/
lemma pilot_mem_clippingRectangle (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n)
    (w : TwoSample n n) (x : ℝ) :
    clippingRectangle c_f C_f (pilot c_f C_f w x) := by
  have hc : 0 < c_f := hP.sourceBounds.1.1
  have hC : 1 < C_f := hP.sourceBounds.2.1
  have hcfC : c_f < C_f := lt_trans hP.sourceBounds.1.2 hC
  simp only [pilot, if_neg (Nat.not_lt_of_ge hn)]
  rw [clippingRectangle]
  constructor
  · simp [clipChannel, clip]
    linarith
  constructor
  · simp [clipChannel, clip]
    linarith
  constructor
  · simp [clipChannel, clip]
    linarith
  intro i hi
  fin_cases i <;> simp_all [clipChannel, clip] <;> linarith

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
