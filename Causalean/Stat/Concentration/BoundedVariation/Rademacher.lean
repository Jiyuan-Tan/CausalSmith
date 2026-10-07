module
public import Causalean.Stat.Concentration.BoundedVariation.SignedChaining

/-!
# Rademacher maximal bound for controlled paths

The finite sign average controls the supremum over the whole unit interval.
The proof uses the common variation control to partition time by mass, then
applies sub-Gaussian increment estimates and dyadic chaining.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- Suppose each control path v_j is [nondecreasing](hyp:hmono) and [zero
at time zero](hyp:hzero), and [bounds the increments of the path w_j: for
s ≤ t, |w_j(t) − w_j(s)| ≤ v_j(t) − v_j(s)](hyp:hinc). Then for [times
s ≤ t](hyp:hst), [the summed squared increments of the paths w_j from s to
t are at most the sum of v_j(1)·(v_j(t) − v_j(s))](goal).
-/
theorem increment_energy_le_control {n : ℕ} (w v : Fin n → Path)
    (hmono : ∀ j, Monotone (v j : Time → ℝ))
    (hzero : ∀ j, v j timeZero = 0)
    (hinc : ∀ j (s t : Time), s ≤ t →
      |w j t - w j s| ≤ v j t - v j s)
    (s t : Time) (hst : s ≤ t) :
    (∑ j, (w j t - w j s) ^ 2) ≤
      ∑ j, v j timeOne * (v j t - v j s) := by
  apply Finset.sum_le_sum
  intro j _
  have hs0 : 0 ≤ v j s := by
    have h0s : timeZero ≤ s := s.property.1
    simpa only [hzero j] using hmono j h0s
  have hst0 : 0 ≤ v j t - v j s := sub_nonneg.mpr (hmono j hst)
  have ht1 : v j t ≤ v j timeOne := hmono j t.property.2
  have hsq : (w j t - w j s) ^ 2 ≤ (v j t - v j s) ^ 2 := by
    calc
      (w j t - w j s) ^ 2 = |w j t - w j s| ^ 2 := (sq_abs _).symm
      _ ≤ (v j t - v j s) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hst0).mpr (hinc j s t hst)
  nlinarith

/-- Suppose each control path v_j is [nondecreasing](hyp:hmono) and [zero
at time zero](hyp:hzero), and [bounds the increments of the path w_j: for
s ≤ t, |w_j(t) − w_j(s)| ≤ v_j(t) − v_j(s)](hyp:hinc). Then [the Rademacher
energy of the paths w_j is at most 4096 times the sum of
(‖w_j‖ + v_j(1))^2](goal), a dimension-free bound.

The numerical constant is deliberately generous so that elementary
sub-Gaussian and chaining bounds can be used without optimizing constants.
-/
theorem rademacherEnergy_le_control {n : ℕ} (w v : Fin n → Path)
    (hmono : ∀ j, Monotone (v j : Time → ℝ))
    (hzero : ∀ j, v j timeZero = 0)
    (hinc : ∀ j (s t : Time), s ≤ t →
      |w j t - w j s| ≤ v j t - v j s) :
    rademacherEnergy w ≤
      4096 * ∑ j, (‖w j‖ + v j timeOne) ^ 2 := by
  /- Set ν(t) = ∑ j (v_j(1)) v_j(t). By
  `increment_energy_le_control`, ν controls squared coefficient increments.
  Apply `rademacherEnergy_le_scalar_control`. Its initial-energy and total
  control-mass terms are each bounded by the displayed envelope sum. -/
  classical
  let u : Path := ∑ j, (v j timeOne) • v j
  have hvnonneg (j : Fin n) : 0 ≤ v j timeOne := by
    have h01 : timeZero ≤ timeOne := by
      change (0 : ℝ) ≤ 1
      norm_num
    simpa only [hzero j] using hmono j h01
  have humono : Monotone (u : Time → ℝ) := by
    intro s t hst
    simp only [u, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hmono j hst) (hvnonneg j)
  have huzero : u timeZero = 0 := by
    simp [u, hzero]
  have huenergy (s t : Time) (hst : s ≤ t) :
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s := by
    calc
      (∑ j, (w j t - w j s) ^ 2) ≤
          ∑ j, v j timeOne * (v j t - v j s) :=
        increment_energy_le_control w v hmono hzero hinc s t hst
      _ = u t - u s := by
        simp only [u, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
          smul_eq_mul, ← Finset.sum_sub_distrib]
        congr 1
        ext j
        ring
  have hbound :
      (∑ j, (w j timeZero) ^ 2) + u timeOne ≤
        ∑ j, (‖w j‖ + v j timeOne) ^ 2 := by
    simp only [u, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have heval : |w j timeZero| ≤ ‖w j‖ := by
      simpa only [Real.norm_eq_abs] using
        (ContinuousMap.norm_coe_le_norm (w j) timeZero)
    have hsq : (w j timeZero) ^ 2 ≤ ‖w j‖ ^ 2 := by
      calc
        (w j timeZero) ^ 2 = |w j timeZero| ^ 2 := (sq_abs _).symm
        _ ≤ ‖w j‖ ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr heval
    nlinarith [norm_nonneg (w j), hvnonneg j]
  exact (rademacherEnergy_le_scalar_control w u humono huzero huenergy).trans
    (mul_le_mul_of_nonneg_left hbound (by norm_num))

/-- If [each of finitely many continuous paths has bounded
variation](hyp:hBV), then [their Rademacher energy is at most 4096 times the
sum of their squared supremum-plus-total-variation sizes](goal).

The supremum ranges over the entire unit interval.
-/
theorem rademacherEnergy_le_pathSize_sq {n : ℕ} (w : Fin n → Path)
    (hBV : ∀ j, eVariationOn (w j) Set.univ < ⊤) :
    rademacherEnergy w ≤ 4096 * ∑ j, (pathSize (w j)) ^ 2 := by
  classical
  have hv (j : Fin n) := exists_variation_control (w j) (hBV j)
  choose v hmono hzero hone hinc using hv
  simpa only [hone, pathSize] using
    (rademacherEnergy_le_control w v hmono hzero hinc)

end Causalean.Stat.Concentration.BoundedVariation
