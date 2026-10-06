module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentAmplitude
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-! Finite tensor product differentiation and second-order integration for the component
amplitude path, retaining the sharp finite-array absolute-mass bound. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The first product-rule array for a finite collection of scalar paths. -/
-- @node: finiteProductSlope
def finiteProductSlope {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, (∏ j ∈ (Finset.univ : Finset ι).erase i, p j) * q i

/-- The second product-rule array, including every ordered pair of distinct factors. -/
-- @node: finiteProductCurvature
def finiteProductCurvature {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ι → ℝ) : ℝ :=
  ∑ i, ((∑ j ∈ (Finset.univ : Finset ι).erase i,
    (∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j, p k) * q j) * q i +
      (∏ j ∈ (Finset.univ : Finset ι).erase i, p j) * r i)

/-- The first product-rule array differentiates to the second product-rule array.  [the theorem's stated inputs and assumptions](hyp:p,q,r,u,hp,hq), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι). -/
-- @node: finiteProductSlope_hasDerivAt
lemma finiteProductSlope_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ → ℝ) (r : ι → ℝ) (u : ℝ)
    (hp : ∀ i, HasDerivAt (p i) (q i u) u)
    (hq : ∀ i, HasDerivAt (q i) (r i) u) :
    HasDerivAt (fun v => finiteProductSlope (fun i => p i v) (fun i => q i v))
      (finiteProductCurvature (fun i => p i u) (fun i => q i u) r) u := by
  exact HasDerivAt.fun_sum (fun i _ =>
    (HasDerivAt.fun_finsetProd (fun j _ => hp j)).mul (hq i))

/-- The absolute mass of a tensor array factors as the product of its absolute masses.  [the theorem's stated inputs and assumptions](hyp:p), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α). -/
-- @node: finiteTensor_abs_sum
lemma finiteTensor_abs_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → α → ℝ) :
    (∑ z : ι → α, |∏ i, p i (z i)|) = ∏ i, ∑ a, |p i a| := by
  simp_rw [Finset.abs_prod]
  exact (Fintype.prod_sum (fun i a => |p i a|)).symm

/-- Replacing one tensor factor gives its absolute mass times those of the remaining factors.  [the theorem's stated inputs and assumptions](hyp:p,q,i), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α). -/
-- @node: finiteTensor_replace_abs_sum
lemma finiteTensor_replace_abs_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → α → ℝ) (q : α → ℝ) (i : ι) :
    (∑ z : ι → α, |(∏ j ∈ (Finset.univ : Finset ι).erase i, p j (z j)) * q (z i)|) =
      (∏ j ∈ (Finset.univ : Finset ι).erase i, ∑ a, |p j a|) * (∑ a, |q a|) := by
  classical
  let f : ι → α → ℝ := Function.update p i q
  have hprod (z : ι → α) : (∏ j, f j (z j)) =
      (∏ j ∈ (Finset.univ : Finset ι).erase i, p j (z j)) * q (z i) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · simp [f]
  simp_rw [← hprod]
  rw [finiteTensor_abs_sum]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · simp [f]

/-- Unit-mass factors make a one-factor replacement's absolute mass exactly that factor's mass.  [the theorem's stated inputs and assumptions](hyp:p,hp,q,i), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α). -/
-- @node: finiteTensor_replace_abs_sum_unit
lemma finiteTensor_replace_abs_sum_unit {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → α → ℝ) (hp : ∀ i, (∑ a, |p i a|) = 1) (q : α → ℝ) (i : ι) :
    (∑ z : ι → α, |(∏ j ∈ (Finset.univ : Finset ι).erase i, p j (z j)) * q (z i)|) =
      ∑ a, |q a| := by
  rw [finiteTensor_replace_abs_sum]
  simp_rw [hp]
  simp

/-- Unit-mass factors make two distinct replacements' absolute mass the product of their masses.  [the theorem's stated inputs and assumptions](hyp:p,hp,q,r,i,j,hji), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α). -/
-- @node: finiteTensor_double_replace_abs_sum_unit
lemma finiteTensor_double_replace_abs_sum_unit {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (p : ι → α → ℝ) (hp : ∀ i, (∑ a, |p i a|) = 1)
    (q r : α → ℝ) (i j : ι) (hji : j ≠ i) :
    (∑ z : ι → α,
      |((∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j, p k (z k)) *
        r (z j)) * q (z i)|) = (∑ a, |r a|) * (∑ a, |q a|) := by
  classical
  let f : ι → α → ℝ := Function.update p j r
  have hprod (z : ι → α) :
      (∏ k ∈ (Finset.univ : Finset ι).erase i, f k (z k)) =
        (∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j, p k (z k)) * r (z j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
    congr 1
    · apply Finset.prod_congr rfl
      intro k hk
      simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    · simp [f]
  simp_rw [← hprod]
  rw [finiteTensor_replace_abs_sum]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
  have hone : (∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j, ∑ a, |f k a|) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hk), hp]
  simp [hone, f]

/-- The second product derivative has quadratic absolute mass when individual derivatives
have absolute masses at most four and the base factors have unit absolute mass.  [the theorem's stated inputs and assumptions](hyp:p,q,r,hp,hq,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι,α). -/
-- @node: finiteProductCurvature_abs_sum_le
lemma finiteProductCurvature_abs_sum_le {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (p q r : ι → α → ℝ) (hp : ∀ i, (∑ a, |p i a|) = 1)
    (hq : ∀ i, (∑ a, |q i a|) ≤ 4) (hr : ∀ i, (∑ a, |r i a|) ≤ 4) :
    (∑ z : ι → α,
      |finiteProductCurvature (fun i => p i (z i))
        (fun i => q i (z i)) (fun i => r i (z i))|) ≤
      16 * (Fintype.card ι : ℝ)^2 := by
  classical
  have hpoint (z : ι → α) :
      |finiteProductCurvature (fun i => p i (z i))
        (fun i => q i (z i)) (fun i => r i (z i))| ≤
      ∑ i, ((∑ j ∈ (Finset.univ : Finset ι).erase i,
        |((∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j, p k (z k)) *
          q j (z j)) * q i (z i)|) +
          |(∏ j ∈ (Finset.univ : Finset ι).erase i, p j (z j)) * r i (z i)|) := by
    dsimp [finiteProductCurvature]
    simp_rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl)
  have hi (i : ι) :
      (∑ z : ι → α, ((∑ j ∈ (Finset.univ : Finset ι).erase i,
        |((∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j, p k (z k)) *
          q j (z j)) * q i (z i)|) +
          |(∏ j ∈ (Finset.univ : Finset ι).erase i, p j (z j)) * r i (z i)|)) ≤
      16 * ((Fintype.card ι : ℝ)-1) + 4 := by
    rw [Finset.sum_add_distrib, Finset.sum_comm,
      finiteTensor_replace_abs_sum_unit p hp]
    apply add_le_add _ (hr i)
    calc
      _ ≤ ∑ j ∈ (Finset.univ : Finset ι).erase i, (16 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [finiteTensor_double_replace_abs_sum_unit p hp _ _ i j
          (Finset.ne_of_mem_erase hj)]
        exact (mul_le_mul (hq j) (hq i) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by norm_num)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Nat.cast_sub (Nat.succ_le_iff.mpr
            (Fintype.card_pos_iff.mpr ⟨i⟩)), Nat.cast_one]
        ring
  calc
    _ ≤ ∑ z : ι → α, ∑ i, ((∑ j ∈ (Finset.univ : Finset ι).erase i,
        |((∏ k ∈ ((Finset.univ : Finset ι).erase i).erase j, p k (z k)) *
          q j (z j)) * q i (z i)|) +
          |(∏ j ∈ (Finset.univ : Finset ι).erase i, p j (z j)) * r i (z i)|) :=
      Finset.sum_le_sum (fun z _ => hpoint z)
    _ ≤ ∑ i : ι, (16 * ((Fintype.card ι : ℝ)-1) + 4) := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun i _ => hi i)
    _ ≤ 16 * (Fintype.card ι : ℝ)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]

/-- Free-amplitude component masses sum to one at every real amplitude.  [the theorem's stated inputs and assumptions](hyp:C,u), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: componentAmplitudeMass_sum
lemma componentAmplitudeMass_sum (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (u : ℝ) :
    (∑ z : Marks C, componentAmplitudeMass hL n x C z u) = 1 := by
  classical
  simp only [componentAmplitudeMass, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Fintype.prod_sum, amplitudeMarkMass_sum]
  simp only [Finset.prod_const_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  exact sign_weight_real_normalization hL

/-- On the legal path every component mark mass is nonnegative.  [the theorem's stated inputs and assumptions](hyp:n,x,C,z,u,hu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentAmplitudeMass_nonneg
lemma componentAmplitudeMass_nonneg (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C)
    (u : ℝ) (hu : u ∈ Icc 0 (1 / 10)) :
    0 ≤ componentAmplitudeMass hL n x C z u := by
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro lam _
  apply Finset.prod_nonneg
  intro i _
  obtain ⟨hS, hq, _⟩ := amplitudeMark_coefficients_valid hL hhL lam (x i)
  exact (amplitudeMarkMass_pos _ _ u hS hq hu (z i)).le

/-- The component probability array has unit absolute mass on the legal path.  [the theorem's stated inputs and assumptions](hyp:n,x,C,u,hu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentAmplitudeMass_abs_sum
lemma componentAmplitudeMass_abs_sum (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n))
    (u : ℝ) (hu : u ∈ Icc 0 (1 / 10)) :
    (∑ z : Marks C, |componentAmplitudeMass hL n x C z u|) = 1 := by
  simp_rw [abs_of_nonneg (componentAmplitudeMass_nonneg hL hhL n x C _ u hu)]
  exact componentAmplitudeMass_sum hL n x C u

/-- The averaged first product-rule array along the component path. -/
-- @node: componentAmplitudeSlope
def componentAmplitudeSlope (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) (u : ℝ) : ℝ :=
  (2 : ℝ)^(-((activeSigns hL).card : ℤ)) * ∑ lam : SignVector hL,
    finiteProductSlope
      (fun i : C => amplitudeMarkMass (perturbation hL lam (x i)) (bump hL (x i)) u (z i))
      (fun i : C => amplitudeMarkSlope (perturbation hL lam (x i)) (bump hL (x i)) u (z i))

/-- The averaged second product-rule array along the component path. -/
-- @node: componentAmplitudeCurvature
def componentAmplitudeCurvature (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) (u : ℝ) : ℝ :=
  (2 : ℝ)^(-((activeSigns hL).card : ℤ)) * ∑ lam : SignVector hL,
    finiteProductCurvature
      (fun i : C => amplitudeMarkMass (perturbation hL lam (x i)) (bump hL (x i)) u (z i))
      (fun i : C => amplitudeMarkSlope (perturbation hL lam (x i)) (bump hL (x i)) u (z i))
      (fun i : C => amplitudeMarkCurvature (perturbation hL lam (x i)) (bump hL (x i)) u (z i))

/-- The named slope is the derivative of the component mass path.  [the theorem's stated inputs and assumptions](hyp:x,C,z,u), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n). -/
-- @node: componentAmplitudeMass_hasDerivAt_slope
lemma componentAmplitudeMass_hasDerivAt_slope (hL : ℝ) (n : ℕ)
    (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C) (u : ℝ) :
    HasDerivAt (componentAmplitudeMass hL n x C z)
      (componentAmplitudeSlope hL n x C z u) u :=
  componentAmplitudeMass_hasDerivAt hL n x C z u

/-- The named curvature is the derivative of the component slope path. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: componentAmplitudeSlope_hasDerivAt
lemma componentAmplitudeSlope_hasDerivAt (hL : ℝ) (n : ℕ)
    (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C) (u : ℝ) :
    HasDerivAt (componentAmplitudeSlope hL n x C z)
      (componentAmplitudeCurvature hL n x C z u) u := by
  classical
  exact (HasDerivAt.fun_sum (fun lam _ => finiteProductSlope_hasDerivAt _ _ _ u
    (fun i => amplitudeMarkMass_hasDerivAt _ _ u (z i))
    (fun i => amplitudeMarkSlope_hasDerivAt _ _ u (z i)))).const_mul _

/-- The named component slope vanishes at zero amplitude by fair-sign cancellation.  [the theorem's stated inputs and assumptions](hyp:x,C,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n). -/
-- @node: componentAmplitudeSlope_zero
lemma componentAmplitudeSlope_zero (hL : ℝ) (n : ℕ)
    (x : Fin n → Covariate) (C : Finset (Fin n)) (z : Marks C) :
    componentAmplitudeSlope hL n x C z 0 = 0 := by
  exact (componentAmplitudeMass_hasDerivAt_slope hL n x C z 0).unique
    (componentAmplitudeMass_hasDerivAt_zero hL n x C z)

/-- Averaging over signs preserves the quadratic bound on the component second derivative.  [the theorem's stated inputs and assumptions](hyp:n,x,C,u,hu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentAmplitudeCurvature_abs_sum_le
lemma componentAmplitudeCurvature_abs_sum_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n))
    (u : ℝ) (hu : u ∈ Icc 0 (1 / 10)) :
    (∑ z : Marks C, |componentAmplitudeCurvature hL n x C z u|) ≤
      16 * (C.card : ℝ)^2 := by
  classical
  have hw : 0 ≤ (2 : ℝ)^(-((activeSigns hL).card : ℤ)) := by
    positivity
  have hbound (lam : SignVector hL) :
      (∑ z : Marks C, |finiteProductCurvature
        (fun i : C => amplitudeMarkMass (perturbation hL lam (x i)) (bump hL (x i)) u (z i))
        (fun i : C => amplitudeMarkSlope (perturbation hL lam (x i)) (bump hL (x i)) u (z i))
        (fun i : C => amplitudeMarkCurvature
          (perturbation hL lam (x i)) (bump hL (x i)) u (z i))|) ≤
        16 * (C.card : ℝ)^2 := by
    simpa only [Fintype.card_coe] using finiteProductCurvature_abs_sum_le
      (fun i : C => fun a => amplitudeMarkMass (perturbation hL lam (x i)) (bump hL (x i)) u a)
      (fun i : C => fun a => amplitudeMarkSlope (perturbation hL lam (x i)) (bump hL (x i)) u a)
      (fun i : C => fun a => amplitudeMarkCurvature (perturbation hL lam (x i)) (bump hL (x i)) u a)
      (by
        intro i
        obtain ⟨hS, hq, hr⟩ := amplitudeMark_coefficients_valid hL hhL lam (x i)
        exact amplitudeMarkMass_abs_sum _ _ u hS hq hu)
      (by
        intro i
        obtain ⟨hS, hq, hr⟩ := amplitudeMark_coefficients_valid hL hhL lam (x i)
        exact amplitudeMarkSlope_abs_sum_le_four _ _ u hS hq hr hu)
      (by
        intro i
        obtain ⟨hS, hq, hr⟩ := amplitudeMark_coefficients_valid hL hhL lam (x i)
        exact amplitudeMarkCurvature_abs_sum_le_four _ _ u hS hq hr hu)
  unfold componentAmplitudeCurvature
  simp_rw [abs_mul, abs_of_nonneg hw]
  apply (Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left
    (Finset.abs_sum_le_sum_abs _ _) hw)).trans
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun lam _ => hbound lam)) hw).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, sign_weight_real_normalization, one_mul]

/-- A vanishing initial slope and a bounded second derivative give the quadratic remainder
by the mean-value inequality followed by integration of the first derivative.  [the theorem's stated inputs and assumptions](hyp:hu,hf,hg,hzero,hbound), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:f,g,r,K,u). -/
-- @node: scalar_second_derivative_remainder_le
lemma scalar_second_derivative_remainder_le (f g r : ℝ → ℝ) (K u : ℝ)
    (hu : 0 ≤ u) (hf : ∀ v, HasDerivAt f (g v) v)
    (hg : ∀ v, HasDerivAt g (r v) v) (hzero : g 0 = 0)
    (hbound : ∀ v ∈ Icc 0 u, |r v| ≤ K) :
    |f u-f 0| ≤ K*u^2/2 := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr
    (fun v => (hg v).continuousAt)
  have hgi : IntervalIntegrable g volume 0 u := hgc.intervalIntegrable _ _
  have hslope (v : ℝ) (hv : v ∈ Icc 0 u) : |g v| ≤ K*v := by
    have hm := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := u) (f := g) (f' := r)
      (fun v _ => (hg v).hasDerivWithinAt)
      (fun v hv => by
        simpa only [Real.norm_eq_abs] using (hbound v ⟨hv.1, hv.2.le⟩)) v hv
    simpa only [hzero, sub_zero, Real.norm_eq_abs] using hm
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hf v) hgi]
  calc
    _ ≤ ∫ v in (0 : ℝ)..u, |g v| := intervalIntegral.abs_integral_le_integral_abs hu
    _ ≤ ∫ v in (0 : ℝ)..u, K*v :=
      intervalIntegral.integral_mono_on hu hgi.abs
        ((continuous_const.mul continuous_id).intervalIntegrable _ _) hslope
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; simp; ring

/-- Applying the scalar second-order bound to a signed projection controls the whole
finite array without multiplying the bound by the number of its coordinates.  [the theorem's stated inputs and assumptions](hyp:f,g,r,K,u,hu,hf,hg,hzero,hbound), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:ι). -/
-- @node: finite_array_second_derivative_remainder_le
lemma finite_array_second_derivative_remainder_le {ι : Type*} [Fintype ι]
    (f g r : ι → ℝ → ℝ) (K u : ℝ) (hu : 0 ≤ u)
    (hf : ∀ i v, HasDerivAt (f i) (g i v) v)
    (hg : ∀ i v, HasDerivAt (g i) (r i v) v)
    (hzero : ∀ i, g i 0 = 0)
    (hbound : ∀ v ∈ Icc 0 u, (∑ i, |r i v|) ≤ K) :
    (∑ i, |f i u-f i 0|) ≤ K*u^2/2 := by
  classical
  let a (i : ι) : ℝ := if 0 ≤ f i u-f i 0 then 1 else -1
  have ha (i : ι) : |a i| = 1 := by dsimp [a]; split_ifs <;> norm_num
  have hd (i : ι) : a i*(f i u-f i 0) = |f i u-f i 0| := by
    dsimp [a]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hs := scalar_second_derivative_remainder_le
    (fun v => ∑ i, a i*f i v) (fun v => ∑ i, a i*g i v)
    (fun v => ∑ i, a i*r i v) K u hu
    (fun v => HasDerivAt.fun_sum (fun i _ => (hf i v).const_mul (a i)))
    (fun v => HasDerivAt.fun_sum (fun i _ => (hg i v).const_mul (a i)))
    (by simp only [hzero, mul_zero, Finset.sum_const_zero]) (by
      intro v hv
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      simpa only [abs_mul, ha, one_mul] using hbound v hv)
  have he : (∑ i, a i*f i u)-(∑ i, a i*f i 0) = ∑ i, |f i u-f i 0| := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, hd]
  rw [he, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at hs
  exact hs

/-- Integrating the component curvature twice gives the sharp second-order array bound.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: alternativeMass_abs_sub_nullMass_sum_le
lemma alternativeMass_abs_sub_nullMass_sum_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∑ z : Marks C, |alternativeMass hL n x C z-nullMass n C z|) ≤
      8*separation hL*(C.card : ℝ)^2 := by
  have hu := sqrt_separation_amplitude_range hL hhL
  have h := finite_array_second_derivative_remainder_le
    (componentAmplitudeMass hL n x C) (componentAmplitudeSlope hL n x C)
    (componentAmplitudeCurvature hL n x C) (16*(C.card : ℝ)^2)
    (Real.sqrt (separation hL)) hu.1
    (componentAmplitudeMass_hasDerivAt_slope hL n x C)
    (componentAmplitudeSlope_hasDerivAt hL n x C)
    (componentAmplitudeSlope_zero hL n x C) (by
      intro v hv
      exact componentAmplitudeCurvature_abs_sum_le hL hhL n x C v ⟨hv.1, hv.2.trans hu.2⟩)
  simp_rw [componentAmplitudeMass_actual hL hhL, componentAmplitudeMass_zero] at h
  rw [Real.sq_sqrt (separation_unit_range hL hhL).1] at h
  convert h using 1
  ring

/-- The absolute-array bound gives the component coupling's failure-probability bound.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: overlapMass_deficit_le
lemma overlapMass_deficit_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    1-overlapMass hL n x C ≤ 4*separation hL*(C.card : ℝ)^2 := by
  have h := alternativeMass_abs_sub_nullMass_sum_le hL hhL n x C
  rw [componentMass_abs_sum] at h
  linarith

/-- A nonsingleton component's expected number of changed marks is at most four times
separation times the cube of its size, as required by the component-counting argument.  [the theorem's stated inputs and assumptions](hyp:n,x,C), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: componentCoupling_hamming_cost_le_cubic
lemma componentCoupling_hamming_cost_le_cubic (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (x : Fin n → Covariate) (C : Finset (Fin n)) :
    (∫⁻ zw, (hammingDist zw.1 zw.2 : ℝ≥0∞) ∂componentCoupling hL n x C) ≤
      ENNReal.ofReal (4*separation hL*(C.card : ℝ)^3) := by
  apply (componentCoupling_hamming_cost_le hL hhL n x C).trans
  rw [← ENNReal.ofReal_natCast C.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg C.card)]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (overlapMass_deficit_le hL hhL n x C)
    (Nat.cast_nonneg (α := ℝ) C.card)
  calc
    _ ≤ (C.card : ℝ)*(4*separation hL*(C.card : ℝ)^2) := h
    _ = _ := by ring

end CausalSmith.Stat.PrivateCateRoughdesign
