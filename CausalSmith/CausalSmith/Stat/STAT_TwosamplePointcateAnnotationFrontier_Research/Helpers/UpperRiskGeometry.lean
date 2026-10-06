module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.UpperAssembly

/-! # Geometry of the guarded rectangular estimator
Rayleigh coercivity, inverse stability, and pointwise clipped-error bounds used
in the fixed-tuning risk assembly.
-/

public section

noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The unit-vector Rayleigh lower bound extends homogeneously to every vector.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the specified input a](hyp:a), [the specified input ha](hyp:ha), [the specified input v](hyp:v), [the rayleigh coercivity conclusion](goal) holds. -/
lemma rayleigh_coercivity {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (a : ℝ) (ha : a ≤ lambdaMin Q) (v : PolyIdx d → ℝ) :
    a * (∑ u, v u^2) ≤ ∑ u, v u * (Q.mulVec v) u := by
  classical
  have hs0 : 0 ≤ ∑ u, v u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hs : (∑ u, v u^2) = 0
  · have hv : v = 0 := by
      ext u
      have hu := Finset.single_le_sum (fun w _ => sq_nonneg (v w)) (Finset.mem_univ u)
      rw [hs] at hu
      simpa using (sq_eq_zero_iff.mp (le_antisymm hu (sq_nonneg _)))
    simp [hv]
  · have hspos : 0 < ∑ u, v u^2 := lt_of_le_of_ne hs0 (Ne.symm hs)
    let s := Real.sqrt (∑ u, v u^2)
    have hsp : 0 < s := Real.sqrt_pos.mpr hspos
    have hss : s^2 = ∑ u, v u^2 := Real.sq_sqrt hs0
    let w : PolyIdx d → ℝ := s⁻¹ • v
    have hw : (∑ u, w u^2) = 1 := by
      simp only [w, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow]
      rw [hss]
      exact inv_mul_cancel₀ hs
    have hl := ha.trans (lambdaMin_le_unit_quadratic Q w hw)
    have he : (∑ u, w u*(Q.mulVec w) u) = s⁻¹^2 * (∑ u, v u*(Q.mulVec v) u) := by
      simp only [w, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [he] at hl
    have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg s)
    have hc : s^2 * (s⁻¹^2 * (∑ u, v u*(Q.mulVec v) u)) = ∑ u, v u*(Q.mulVec v) u := by
      field_simp
    rw [hc, hss] at hm
    simpa only [mul_comm] using hm

/-- The guard bounds the squared Euclidean norm of the inverse image by the reciprocal squared threshold.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [a guard threshold g](hyp:g), [its positivity](hyp:hg), [the specified input hmin](hyp:hmin), [the specified input R](hyp:R), [the good branch inverse sq bound conclusion](goal) holds. -/
lemma good_branch_inverse_sq_bound {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (g : ℝ) (hg : 0 < g) (hmin : g ≤ lambdaMin Q) (R : PolyIdx d → ℝ) :
    (∑ u, (Q⁻¹.mulVec R u)^2) ≤ (g⁻¹)^2 * (∑ u, R u^2) := by
  classical
  let v := Q⁻¹.mulVec R
  have hunit : IsUnit Q := isUnit_of_lambdaMin_pos Q (by linarith)
  have hQR : Q.mulVec v = R := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q
      ((Matrix.isUnit_iff_isUnit_det Q).mp hunit), Matrix.one_mulVec]
  have hl := rayleigh_coercivity Q g hmin v
  rw [hQR] at hl
  have hs : 0 ≤ ∑ u, v u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr : 0 ≤ ∑ u, R u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (PolyIdx d)) v R
  have hdot : 0 ≤ ∑ u, v u*R u := le_trans (by positivity) hl
  have hh : (g*(∑ u, v u^2))^2 ≤ (∑ u, v u*R u)^2 :=
    pow_le_pow_left₀ (by positivity) hl 2
  by_cases hz : (∑ u, v u^2) = 0
  · change (∑ u, v u^2) ≤ _
    rw [hz]
    positivity
  · have hp : 0 < ∑ u, v u^2 := lt_of_le_of_ne hs (Ne.symm hz)
    have hcancel : g^2*(∑ u, v u^2) ≤ ∑ u, R u^2 := by
      apply (mul_le_mul_iff_right₀ hp).mp
      nlinarith
    change (∑ u, v u^2) ≤ _
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith

/-- Finite Cauchy–Schwarz in Euclidean square-root notation.  Given [the specified input v](hyp:v), [the specified input w](hyp:w), [the finite dot abs le conclusion](goal) holds. -/
lemma finite_dot_abs_le {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    |∑ u, v u*w u| ≤ Real.sqrt (∑ u, v u^2) * Real.sqrt (∑ u, w u^2) := by
  classical
  have hv : 0 ≤ ∑ u, v u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw : 0 ≤ ∑ u, w u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) v w
  have hvs := Real.sq_sqrt hv
  have hws := Real.sq_sqrt hw
  have ha := sq_abs (∑ u, v u*w u)
  nlinarith [Real.sqrt_nonneg (∑ u, v u^2), Real.sqrt_nonneg (∑ u, w u^2),
    mul_nonneg (Real.sqrt_nonneg (∑ u, v u^2)) (Real.sqrt_nonneg (∑ u, w u^2))]

/-- On the good branch the projected inverse amplifies a residual by at most the reciprocal guard threshold.  Given [the specified input d](hyp:d), [the specified input Q](hyp:Q), [the specified input hQ](hyp:hQ), [the specified input hmin](hyp:hmin), [the specified input R](hyp:R), [the specified input theta](hyp:theta), [the specified input r](hyp:r), [the good branch projected error conclusion](goal) holds. -/
lemma good_branch_projected_error {d : ℕ} (Q : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (hQ : Q.transpose = Q) (g : ℝ) (hg : 0 < g) (hmin : g ≤ lambdaMin Q)
    (R theta r : PolyIdx d → ℝ) :
    |∑ u, r u * (Q⁻¹.mulVec R u-theta u)| ≤
      g⁻¹ * Real.sqrt (∑ u, r u^2) *
        Real.sqrt (∑ u, (R u-Q.mulVec theta u)^2) := by
  have he := good_branch_resolvent Q hQ g hg hmin R theta
  have hi := good_branch_inverse_sq_bound Q g hg hmin (R-Q.mulVec theta)
  have hs : Real.sqrt (∑ u, (Q⁻¹.mulVec (R-Q.mulVec theta) u)^2) ≤
      g⁻¹*Real.sqrt (∑ u, (R u-Q.mulVec theta u)^2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact hi
  calc
    _ = |∑ u, r u * (Q⁻¹.mulVec (R-Q.mulVec theta)) u| := by
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      rw [← he]
      rfl
    _ ≤ Real.sqrt (∑ u, r u^2) * Real.sqrt (∑ u, (Q⁻¹.mulVec (R-Q.mulVec theta) u)^2) :=
      finite_dot_abs_le r _
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (∑ u, r u^2))
      have hgi : 0 ≤ g⁻¹ := inv_nonneg.mpr hg.le
      nlinarith

/-- The Euclidean square-root norm satisfies the triangle inequality.  Given [the specified input v](hyp:v), [the specified input w](hyp:w), [the finite sqrt triangle conclusion](goal) holds. -/
lemma finite_sqrt_triangle {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    Real.sqrt (∑ u, (v u+w u)^2) ≤
      Real.sqrt (∑ u, v u^2) + Real.sqrt (∑ u, w u^2) := by
  classical
  have hv : 0 ≤ ∑ u, v u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw : 0 ≤ ∑ u, w u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc := (le_abs_self (∑ u, v u*w u)).trans (finite_dot_abs_le v w)
  have he : (∑ u, (v u+w u)^2) =
      (∑ u, v u^2) + 2*(∑ u, v u*w u) + (∑ u, w u^2) := by
    simp only [add_sq, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [he]
  nlinarith [Real.sq_sqrt hv, Real.sq_sqrt hw]

/-- The Frobenius norm bounds matrix action in the Euclidean norm.  Given [the specified input E](hyp:E), [the specified input v](hyp:v), [the finite matrix mul vec sqrt le conclusion](goal) holds. -/
lemma finite_matrix_mulVec_sqrt_le {ι : Type*} [Fintype ι]
    (E : Matrix ι ι ℝ) (v : ι → ℝ) :
    Real.sqrt (∑ u, (E.mulVec v u)^2) ≤
      Real.sqrt (∑ u, ∑ w, (E u w)^2) * Real.sqrt (∑ u, v u^2) := by
  classical
  have he : 0 ≤ ∑ u, ∑ w, (E u w)^2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv : 0 ≤ ∑ u, v u^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc : (∑ u, (E.mulVec v u)^2) ≤ (∑ u, ∑ w, (E u w)^2)*(∑ u, v u^2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro u _
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (E u) v
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt he, Real.sq_sqrt hv]
  exact hc

/-- A sample residual decomposes into vector noise, population bias, and Gram noise.  Given [the specified input R](hyp:R), [the specified input Rbar](hyp:Rbar), [the specified input theta](hyp:theta), [the specified input Q](hyp:Q), [the specified input Qbar](hyp:Qbar), [the rectangular residual sqrt le conclusion](goal) holds. -/
lemma rectangular_residual_sqrt_le {ι : Type*} [Fintype ι]
    (R Rbar theta : ι → ℝ) (Q Qbar : Matrix ι ι ℝ) :
    Real.sqrt (∑ u, (R u-Q.mulVec theta u)^2) ≤
      Real.sqrt (∑ u, (R u-Rbar u)^2) +
      Real.sqrt (∑ u, (Rbar u-Qbar.mulVec theta u)^2) +
      Real.sqrt (∑ u, ∑ v, (Q u v-Qbar u v)^2) * Real.sqrt (∑ u, theta u^2) := by
  have he : R-Q.mulVec theta =
      ((R-Rbar)+(Rbar-Qbar.mulVec theta)) + (Qbar-Q).mulVec theta := by
    ext u
    simp only [Matrix.sub_mulVec, Pi.add_apply, Pi.sub_apply]
    ring
  have h1 := finite_sqrt_triangle ((R-Rbar)+(Rbar-Qbar.mulVec theta)) ((Qbar-Q).mulVec theta)
  have h2 := finite_sqrt_triangle (R-Rbar) (Rbar-Qbar.mulVec theta)
  have h3 := finite_matrix_mulVec_sqrt_le (Qbar-Q) theta
  have hs : (∑ u, ∑ v, ((Qbar-Q) u v)^2) = (∑ u, ∑ v, (Q u v-Qbar u v)^2) := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    simp only [Matrix.sub_apply]
    ring
  rw [hs] at h3
  change Real.sqrt (∑ u, ((R-Q.mulVec theta) u)^2) ≤ _
  rw [he]
  exact h1.trans (add_le_add h2 h3)

/-- The good-branch clipped error is controlled by sampling deviations and population bias.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input D](hyp:D), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input theta](hyp:theta), [the specified input Rbar](hyp:Rbar), [the specified input Qbar](hyp:Qbar), [the specified input y](hyp:y), [the specified input hy](hyp:hy), [the specified input hcenter](hyp:hcenter), [the specified input hgood](hyp:hgood), [the overlap level eps](hyp:eps), [the t hat good branch error conclusion](goal) holds. -/
lemma tHat_good_branch_error {d n m : ℕ} {eps : ℝ} (heps : 0 < gramGuard eps)
    (D : Dataset d n m) (h : ℝ) (J : ℕ)
    (theta Rbar : PolyIdx d → ℝ) (Qbar : Matrix (PolyIdx d) (PolyIdx d) ℝ)
    (y : ℝ) (hy : y ∈ Icc (-1) 1) (hcenter : pv h theta (x0 d) = y)
    (hgood : gramGuard eps ≤ lambdaMin (qHat D h J)) :
    |tHat eps h J D-y| ≤ (gramGuard eps)⁻¹*Real.sqrt (∑ u, (r0 d h u)^2) *
      (Real.sqrt (∑ u, (rHat D h J u-Rbar u)^2) +
       Real.sqrt (∑ u, (Rbar u-Qbar.mulVec theta u)^2) +
       Real.sqrt (∑ u, ∑ v, (qHat D h J u v-Qbar u v)^2) * Real.sqrt (∑ u, theta u^2)) := by
  have hsym : (qHat D h J).transpose = qHat D h J := by
    ext u v
    simp only [Matrix.transpose_apply, qHat]
    ring
  have hp := good_branch_projected_error (qHat D h J) hsym _ heps hgood (rHat D h J) theta (r0 d h)
  have hres := rectangular_residual_sqrt_le (rHat D h J) Rbar theta (qHat D h J) Qbar
  have he : (∑ u, r0 d h u * (qHat D h J)⁻¹.mulVec (rHat D h J) u)-y =
      ∑ u, r0 d h u * ((qHat D h J)⁻¹.mulVec (rHat D h J) u-theta u) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    change _-y = _-pv h theta (x0 d)
    rw [hcenter]
  rw [tHat, if_pos hgood]
  calc
    _ ≤ |(∑ u, r0 d h u * (qHat D h J)⁻¹.mulVec (rHat D h J) u)-y| :=
      clipping_contraction _ y hy
    _ ≤ (gramGuard eps)⁻¹*Real.sqrt (∑ u, (r0 d h u)^2) *
        Real.sqrt (∑ u, (rHat D h J u-(qHat D h J).mulVec theta u)^2) := by
      rw [he]
      exact hp
    _ ≤ _ := mul_le_mul_of_nonneg_left hres (by positivity)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
