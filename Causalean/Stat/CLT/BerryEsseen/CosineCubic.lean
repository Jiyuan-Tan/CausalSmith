module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Global cubic and quartic cosine remainder bounds

This deterministic leaf isolates the sharp analytic ingredient of the wide
characteristic-function estimate and a reusable quartic Taylor enclosure.
The cubic coefficient is conservatively rounded
up from Tyurin's extremal cosine-remainder constant, approximately 0.099162;
see `tmp/mnar_round4_sources/arxiv.tex`, definition of a before Theorem 5.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- The cosine of [any real argument](hyp:u) is [bounded above by its
quartic Taylor polynomial](goal). -/
theorem cos_le_quadratic_add_quartic (u : ℝ) :
    Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 := by
  have hd (x : ℝ) :
      deriv (fun x : ℝ => (1 - x ^ 2 / 2 + x ^ 4 / 24) - Real.cos x) x =
        Real.sin x - (x - x ^ 3 / 6) := by
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn
      (fun x : ℝ => (1 - x ^ 2 / 2 + x ^ 4 / 24) - Real.cos x) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (by fun_prop) (by fun_prop)
    intro x hx
    rw [hd]
    exact sub_nonneg.mpr (Real.sin_ge_sub_cube
      (le_of_lt (by simpa using hx)))
  have h := hm (by simp) (abs_nonneg u) (abs_nonneg u)
  norm_num [Real.cos_abs, pow_abs,
    abs_of_nonneg (show 0 ≤ u ^ 2 by positivity),
    abs_of_nonneg (show 0 ≤ u ^ 4 by positivity)] at h
  linarith only [h]

/-- The cosine of [any real argument](hyp:u) is [bounded above by its quadratic
Taylor polynomial 1 − u²/2 plus one tenth of the absolute cube |u|³](goal). -/
theorem cos_le_quadratic_add_cubic (u : ℝ) :
    Real.cos u ≤ 1 - u ^ 2 / 2 + |u| ^ 3 / 10 := by
  /- Reduce to u≥0 using cosine evenness. For u≥5, cos u≤1 suffices.
  On the remaining compact interval, certify the polynomial Taylor bounds
  with alternating remainder signs, subdividing with rational endpoints as
  needed. A sixth/eighth-order truncation alone need not reach coefficient
  1/10 near u=4. Bounds must be proved in Lean, not sampled numerically.
  This task is only deterministic cosine analysis; it contains no moment,
  product-measure, smoothing, or CLT obligation. -/
  have integrate (f : ℝ → ℝ) (hf : Differentiable ℝ f) (h0 : f 0 = 0)
      (hd : ∀ x, 0 ≤ x → 0 ≤ deriv f x) (x : ℝ) (hx : 0 ≤ x) :
      0 ≤ f x := by
    have hm : MonotoneOn f (Set.Ici 0) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn
        hf.differentiableOn (fun y hy => hd y (le_of_lt (by simpa using hy)))
    simpa [h0] using hm (by simp) hx hx
  -- Integrating nonnegative derivative differences proves each remainder sign.
  have h3 (x : ℝ) (hx : 0 ≤ x) := Real.sin_ge_sub_cube hx
  have h4 (x : ℝ) (_hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 :=
    cos_le_quadratic_add_quartic x
  have h5 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (x - x ^ 3 / 6 + x ^ 5 / 120) - (Real.sin x)) x =
        (1 - x ^ 2 / 2 + x ^ 4 / 24) - (Real.cos x) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (x - x ^ 3 / 6 + x ^ 5 / 120) - (Real.sin x)) (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h4 y hy)) x hx
    linarith only [h]
  have h6 (x : ℝ) (hx : 0 ≤ x) : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (Real.cos x) - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 /
        720)) x =
        (x - x ^ 3 / 6 + x ^ 5 / 120) - (Real.sin x) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (Real.cos x) - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720))
        (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h5 y hy)) x hx
    linarith only [h]
  have h7 (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (Real.sin x) - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 /
        5040)) x =
        (Real.cos x) - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (Real.sin x) - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
        (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h6 y hy)) x hx
    linarith only [h]
  have h8 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 /
      40320 := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 /
        40320) - (Real.cos x)) x =
        (Real.sin x) - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) -
        (Real.cos x)) (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h7 y hy)) x hx
    linarith only [h]
  have h9 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 /
      362880 := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 /
        362880) - (Real.sin x)) x =
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) - (Real.cos x) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 /
        362880) - (Real.sin x)) (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h8 y hy)) x hx
    linarith only [h]
  have h10 (x : ℝ) (hx : 0 ≤ x) : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^
      10 / 3628800 ≤ Real.cos x := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (Real.cos x) - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
        + x ^ 8 / 40320 - x ^ 10 / 3628800)) x =
        (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880) - (Real.sin x) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (Real.cos x) - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x
        ^ 8 / 40320 - x ^ 10 / 3628800)) (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h9 y hy)) x hx
    linarith only [h]
  have h11 (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x
      ^ 11 / 39916800 ≤ Real.sin x := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (Real.sin x) - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 /
        5040 + x ^ 9 / 362880 - x ^ 11 / 39916800)) x =
        (Real.cos x) - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 /
            3628800) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (Real.sin x) - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 +
        x ^ 9 / 362880 - x ^ 11 / 39916800)) (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h10 y hy)) x hx
    linarith only [h]
  have h12 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 /
      40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600 := by
    have hd (x : ℝ) : deriv (fun x : ℝ => (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 /
        40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600) - (Real.cos x)) x =
        (Real.sin x) - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 /
            39916800) := by
      simp (disch := fun_prop)
      ring
    have h := integrate (fun x : ℝ => (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
        x ^ 10 / 3628800 + x ^ 12 / 479001600) - (Real.cos x)) (by fun_prop)
      (by norm_num) (by
        intro y hy
        rw [hd]
        exact sub_nonneg.mpr (h11 y hy)) x hx
    linarith only [h]
  -- Exact Bernstein certificates on three rational intervals.
  have hpoly (x : ℝ) (hx : 0 ≤ x) (hx5 : x ≤ 5) :
      0 ≤ (1 / 10 - x / 24 + x ^ 3 / 720 - x ^ 5 / 40320 + x ^ 7 / 3628800 - x ^ 9 / 479001600 :
          ℝ) := by
    by_cases hx3 : x ≤ 3
    · have hr : 0 ≤ 3 - x := by linarith
      rw [show (1 / 10 - x / 24 + x ^ 3 / 720 - x ^ 5 / 40320 + x ^ 7 / 3628800 - x ^ 9 /
          479001600 : ℝ) =
          (1 / 196830 : ℝ) * (3 - x) ^ 9
          + (31 / 787320 : ℝ) * x * (3 - x) ^ 8
          + (13 / 98415 : ℝ) * x ^ 2 * (3 - x) ^ 7
          + (79 / 314928 : ℝ) * x ^ 3 * (3 - x) ^ 6
          + (233 / 787320 : ℝ) * x ^ 4 * (3 - x) ^ 5
          + (19741 / 88179840 : ℝ) * x ^ 5 * (3 - x) ^ 4
          + (2381 / 22044960 : ℝ) * x ^ 6 * (3 - x) ^ 3
          + (28087 / 881798400 : ℝ) * x ^ 7 * (3 - x) ^ 2
          + (2287 / 440899200 : ℝ) * x ^ 8 * (3 - x)
          + (1981 / 5542732800 : ℝ) * x ^ 9 from by ring]
      positivity
    · have hx3 : 0 ≤ x - 3 := by linarith
      by_cases hx4 : x ≤ 4
      · have hr : 0 ≤ 4 - x := by linarith
        rw [show (1 / 10 - x / 24 + x ^ 3 / 720 - x ^ 5 / 40320 + x ^ 7 / 3628800 - x ^ 9 /
            479001600 : ℝ) =
            (1981 / 281600 : ℝ) * (4 - x) ^ 9
            + (74489 / 1478400 : ℝ) * (x - 3) * (4 - x) ^ 8
            + (231919 / 1478400 : ℝ) * (x - 3) ^ 2 * (4 - x) ^ 7
            + (308311 / 1108800 : ℝ) * (x - 3) ^ 3 * (4 - x) ^ 6
            + (76147 / 246400 : ℝ) * (x - 3) ^ 4 * (4 - x) ^ 5
            + (124337 / 554400 : ℝ) * (x - 3) ^ 5 * (4 - x) ^ 4
            + (89813 / 831600 : ℝ) * (x - 3) ^ 6 * (4 - x) ^ 3
            + (21611 / 623700 : ℝ) * (x - 3) ^ 7 * (4 - x) ^ 2
            + (8999 / 1247400 : ℝ) * (x - 3) ^ 8 * (4 - x)
            + (53 / 66825 : ℝ) * (x - 3) ^ 9 from by ring]
        positivity
      · have hx4 : 0 ≤ x - 4 := by linarith
        have hr : 0 ≤ 5 - x := by linarith
        rw [show (1 / 10 - x / 24 + x ^ 3 / 720 - x ^ 5 / 40320 + x ^ 7 / 3628800 - x ^ 9 /
            479001600 : ℝ) =
            (53 / 66825 : ℝ) * (5 - x) ^ 9
            + (8809 / 1247400 : ℝ) * (x - 4) * (5 - x) ^ 8
            + (20851 / 623700 : ℝ) * (x - 4) ^ 2 * (5 - x) ^ 7
            + (50933 / 498960 : ℝ) * (x - 4) ^ 3 * (5 - x) ^ 6
            + (29339 / 142560 : ℝ) * (x - 4) ^ 4 * (5 - x) ^ 5
            + (1091809 / 3991680 : ℝ) * (x - 4) ^ 5 * (5 - x) ^ 4
            + (471799 / 1995840 : ℝ) * (x - 4) ^ 6 * (5 - x) ^ 3
            + (1019911 / 7983360 : ℝ) * (x - 4) ^ 7 * (5 - x) ^ 2
            + (313139 / 7983360 : ℝ) * (x - 4) ^ 8 * (5 - x)
            + (71501 / 13685760 : ℝ) * (x - 4) ^ 9 from by ring]
        positivity
  have hnonneg (x : ℝ) (hx : 0 ≤ x) :
      Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 3 / 10 := by
    by_cases hx5 : x ≤ 5
    · have hp := mul_nonneg (pow_nonneg hx 3) (hpoly x hx hx5)
      have hc := h12 x hx
      nlinarith only [hp, hc]
    · have hp := mul_nonneg (sq_nonneg x) (show 0 ≤ x - 5 by linarith)
      have hc := Real.cos_le_one x
      nlinarith only [hp, hc]
  simpa only [Real.cos_abs, sq_abs] using hnonneg |u| (abs_nonneg u)

end Causalean.Stat.CLT.BerryEsseen
