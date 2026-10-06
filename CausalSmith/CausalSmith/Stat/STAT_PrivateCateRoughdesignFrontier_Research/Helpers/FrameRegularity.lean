module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.FrameGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.MetricSpace.Lipschitz
/-! Global moduli of the localized cosine envelope and effect bump, including support boundaries. -/
public section
noncomputable section
open Set
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Clamping the displacement to the support interval realizes a zero-extended cosine exactly.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:r,c,x,hr). -/
-- @node: localized_cosine_eq_clamped
lemma localized_cosine_eq_clamped (r c x : ℝ) (hr : 0 < r) :
    (if |x - c| ≤ r then Real.cos (Real.pi * (x - c) / (2*r)) else 0) =
      Real.cos (Real.pi * (projIcc (-r) r (by linarith) (x-c) : ℝ) / (2*r)) := by
  classical
  by_cases hx : |x-c| ≤ r
  · rw [if_pos hx, projIcc_of_mem _ (abs_le.mp hx)]
  · rw [if_neg hx]
    have hout : x-c < -r ∨ r < x-c := by
      simpa only [not_and_or, not_le] using (show ¬ (-r ≤ x-c ∧ x-c ≤ r) by
        simpa only [← abs_le] using hx)
    rcases hout with hlo | hhi
    · rw [projIcc_of_le_left _ hlo.le]
      have he : Real.pi * (-r) / (2*r) = -(Real.pi/2) := by field_simp
      rw [he, Real.cos_neg, Real.cos_pi_div_two]
    · rw [projIcc_of_right_le _ hhi.le]
      have he : Real.pi * r / (2*r) = Real.pi/2 := by field_simp
      rw [he, Real.cos_pi_div_two]

/-- A zero-extended cosine has its global cosine Lipschitz bound across both support endpoints.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:r,c,x,y,hr). -/
-- @node: localized_cosine_difference
lemma localized_cosine_difference (r c x y : ℝ) (hr : 0 < r) :
    |(if |x-c| ≤ r then Real.cos (Real.pi*(x-c)/(2*r)) else 0) -
      (if |y-c| ≤ r then Real.cos (Real.pi*(y-c)/(2*r)) else 0)| ≤
      Real.pi/(2*r) * |x-y| := by
  rw [localized_cosine_eq_clamped r c x hr, localized_cosine_eq_clamped r c y hr]
  have hc := (LipschitzWith.projIcc (show -r ≤ r by linarith)).dist_le_mul (x-c) (y-c)
  simp only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hc
  have ha : |Real.pi * (projIcc (-r) r (by linarith) (x-c) : ℝ) / (2*r) -
      Real.pi * (projIcc (-r) r (by linarith) (y-c) : ℝ) / (2*r)| =
      Real.pi/(2*r) * |(projIcc (-r) r (by linarith) (x-c) : ℝ) -
        (projIcc (-r) r (by linarith) (y-c) : ℝ)| := by
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by positivity : 0 < 2*r)]
    ring
  calc
    _ ≤ _ := Real.abs_cos_sub_cos_le _ _
    _ = _ := ha
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sub_sub_sub_cancel_right] using hc

/-- Squaring values in the unit interval at most doubles their absolute difference.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:u,v,hu,hv). -/
-- @node: square_difference_le_twice
lemma square_difference_le_twice (u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |u^2-v^2| ≤ 2*|u-v| := by
  have he : u^2-v^2 = (u-v)*(u+v) := by ring
  rw [he, abs_mul]
  have hs : |u+v| ≤ 2 := (abs_add_le u v).trans (by linarith)
  nlinarith [abs_nonneg (u-v)]

/-- The macro envelope has a global Lipschitz modulus, with no exception at support boundaries.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh,y). -/
-- @node: envelope_difference_bound
lemma envelope_difference_bound (hL : ℝ) (hh : 0 < hL) (x y : Covariate) :
    |envelope hL x - envelope hL y| ≤ (Real.pi/hL)*|(x : ℝ)-y| := by
  classical
  let f (z : Covariate) : ℝ :=
    if |(z : ℝ)-x0| ≤ hL then Real.cos (Real.pi*((z : ℝ)-x0)/(2*hL)) else 0
  have hf (z : Covariate) : |f z| ≤ 1 := by
    dsimp [f]
    split_ifs <;> first | exact Real.abs_cos_le_one _ | norm_num
  have he (z : Covariate) : envelope hL z = (f z)^2 := by
    dsimp [envelope, f]
    split_ifs <;> ring
  rw [he x, he y]
  calc
    _ ≤ 2*|f x-f y| := square_difference_le_twice _ _ (hf x) (hf y)
    _ ≤ 2*(Real.pi/(2*hL)*|(x : ℝ)-y|) :=
      mul_le_mul_of_nonneg_left (localized_cosine_difference hL x0 x y hh) (by norm_num)
    _ = _ := by field_simp

/-- The squared envelope has a global Lipschitz modulus inherited from the envelope.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh,y). -/
-- @node: bump_difference_bound
lemma bump_difference_bound (hL : ℝ) (hh : 0 < hL) (x y : Covariate) :
    |bump hL x - bump hL y| ≤ (2*Real.pi/hL)*|(x : ℝ)-y| := by
  have hx := envelope_range hL x
  have hy := envelope_range hL y
  calc
    _ ≤ 2*|envelope hL x-envelope hL y| := square_difference_le_twice _ _
      (by simpa only [abs_of_nonneg hx.1] using hx.2)
      (by simpa only [abs_of_nonneg hy.1] using hy.2)
    _ ≤ 2*((Real.pi/hL)*|(x : ℝ)-y|) :=
      mul_le_mul_of_nonneg_left (envelope_difference_bound hL hh x y) (by norm_num)
    _ = _ := by ring
/-- Each micro-frame has the global modulus of its zero-extended cosine.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh,j,y). -/
-- @node: frame_difference_bound
lemma frame_difference_bound (hL : ℝ) (hh : 0 < hL) (j : ℤ) (x y : Covariate) :
    |frame hL j x-frame hL j y| ≤ (Real.pi/(2*deltaL hL))*|(x : ℝ)-y| := by
  exact localized_cosine_difference (deltaL hL) (j*deltaL hL) x y (pow_pos hh 5)

/-- A bounded oscillation and a Lipschitz modulus give the one-tenth Holder modulus
by splitting distances at the public radius.  [the theorem's stated inputs and assumptions](hyp:hC,hbound,hlip), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:r,z,v,C,hr,hz). -/
-- @node: holder_modulus_of_two_bounds
lemma holder_modulus_of_two_bounds (r z v C : ℝ) (hr : 0 < r) (hz : 0 ≤ z)
    (hC : 0 ≤ C) (hbound : v ≤ C) (hlip : v ≤ C*(z/r)) :
    v ≤ C*z^(1/10 : ℝ)/r^(1/10 : ℝ) := by
  by_cases hzero : z = 0
  · subst z
    simpa using hlip
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzero)
  have hu : 0 ≤ z/r := div_nonneg hz hr.le
  have hid : (z/r)^(1/10 : ℝ) = z^(1/10 : ℝ)/r^(1/10 : ℝ) :=
    Real.div_rpow hz hr.le _
  rw [div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv, ← hid]
  by_cases hs : z/r ≤ 1
  · have he : z/r ≤ (z/r)^(1/10 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (div_pos hzpos hr) hs (by norm_num : (1/10 : ℝ) ≤ 1)
      simpa using h
    exact hlip.trans (mul_le_mul_of_nonneg_left he hC)
  · have he : 1 ≤ (z/r)^(1/10 : ℝ) := Real.one_le_rpow (le_of_not_ge hs) (by norm_num)
    exact hbound.trans (by nlinarith)
end CausalSmith.Stat.PrivateCateRoughdesign
