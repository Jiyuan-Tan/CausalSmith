module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.PriorHandle

/-!
Affine-prior public schedule and the shared raw total mass.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,m,d), [The affine schedule has uniform total-intensity, degree, and rare-cell mass bounds](goal).
-/
-- @node: affine_tuning_bounds
lemma affine_tuning_bounds (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    let tun := affineTuning n m d eps
    128 * ((n : Real) + m) ≤ tun.M ∧ tun.M ≤ 256 * ((n : Real) + m) ∧
    8 * logScale n eps ≤ (tun.L : Real) ∧ (tun.L : Real) ≤ 9 * logScale n eps ∧
    0 < tun.B ∧ 0 < tun.alpha ∧ 0 < tun.b0 ∧ (tun.Kstar : Real) * tun.b0 ≤ 1 / 100 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ m := Nat.cast_nonneg m
  have hell : 1 ≤ logScale n eps := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + labelScale n eps by
        exact le_add_of_nonneg_right (by dsimp [labelScale]; positivity))
    simpa only [Real.log_exp, logScale] using h
  have hLlo := Nat.le_ceil (8 * logScale n eps)
  have hLhi := Nat.ceil_lt_add_one
    (show 0 ≤ 8 * logScale n eps by linarith)
  have hLpos : 0 < (Nat.ceil (8 * logScale n eps) : Real) := by linarith
  have hMpos : 0 < 128 * (n : Real) + 128 * ((n : Real) + m) := by linarith
  have hBpos : 0 < (affineTuning n m d eps).B := by
    dsimp [affineTuning]; exact div_pos hLpos (mul_pos (by norm_num) hMpos)
  have hapos : 0 < (affineTuning n m d eps).alpha := by
    dsimp only [affineTuning] at hBpos ⊢
    exact div_pos hBpos (mul_pos (by norm_num) (pow_pos hLpos 2))
  have hbpos : 0 < (affineTuning n m d eps).b0 := div_pos hapos heps
  refine ⟨?_, ?_, hLlo, ?_, hBpos, hapos, hbpos, ?_⟩
  · dsimp [affineTuning]; linarith
  · dsimp [affineTuning]; linarith
  · dsimp [affineTuning]; linarith
  · have hfloor := Nat.floor_le
      (show 0 ≤ 1 / (100 * (affineTuning n m d eps).b0) by positivity)
    have hmin : (affineTuning n m d eps).Kstar ≤
        Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) := Nat.min_le_right _ _
    have hcast : ((affineTuning n m d eps).Kstar : Real) ≤
        (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) : Real) := by
      exact_mod_cast hmin
    have hbound := mul_le_mul_of_nonneg_right (hcast.trans hfloor) hbpos.le
    have hid : (1 / (100 * (affineTuning n m d eps).b0)) *
        (affineTuning n m d eps).b0 = 1 / 100 := by field_simp
    exact hid ▸ hbound
/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,m,d), The baseline mass has the explicit reciprocal form used in the numerical bounds.  This gives [the stated result](goal).-/
-- @node: affine_tuning_b0_identity
lemma affine_tuning_b0_identity (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    (affineTuning n m d eps).b0 =
      1 / (100000 * (affineTuning n m d eps).M * eps * (affineTuning n m d eps).L) := by
  obtain ⟨hM, _, hL, _, _, _, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hell : 1 ≤ logScale n eps := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + labelScale n eps by
        apply le_add_of_nonneg_right; dsimp [labelScale]; positivity)
    simpa only [logScale, Real.log_exp] using h
  have hLp : 0 < ((affineTuning n m d eps).L : Real) := by linarith
  have hMp : 0 < (affineTuning n m d eps).M := by
    have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
    have hmR : (0 : Real) ≤ m := Nat.cast_nonneg m
    linarith
  change ((affineTuning n m d eps).L : Real) /
    (1000 * (affineTuning n m d eps).M) /
    (100 * ((affineTuning n m d eps).L : Real) ^ 2) / eps = _
  field_simp
  <;> ring

/-- [Under the stated inputs and conditions](hyp:eps,heps,n,m,d), The bandwidth contribution to concentration equals the stated dimensionless scale.  This gives [the stated result](goal).-/
-- @node: affine_tuning_B_alpha_identity
lemma affine_tuning_B_alpha_identity (n m d : Nat) (eps : Real) (heps : 0 < eps) :
    (affineTuning n m d eps).B * (affineTuning n m d eps).alpha =
      100 * eps ^ 2 * ((affineTuning n m d eps).L : Real) ^ 2 *
        (affineTuning n m d eps).b0 ^ 2 := by
  have hb : eps * (affineTuning n m d eps).b0 = (affineTuning n m d eps).alpha := by
    change eps * ((affineTuning n m d eps).alpha / eps) = (affineTuning n m d eps).alpha
    rw [mul_comm]
    exact div_mul_cancel₀ _ heps.ne'
  have ha : (affineTuning n m d eps).alpha *
      (100 * ((affineTuning n m d eps).L : Real) ^ 2) = (affineTuning n m d eps).B := by
    change ((affineTuning n m d eps).B / (100 * ((affineTuning n m d eps).L : Real) ^ 2)) *
      (100 * ((affineTuning n m d eps).L : Real) ^ 2) = (affineTuning n m d eps).B
    by_cases hL : (affineTuning n m d eps).L = 0
    · have hB : (affineTuning n m d eps).B = 0 := by
        change ((affineTuning n m d eps).L : Real) / (1000 * (affineTuning n m d eps).M) = 0
        rw [hL]; simp
      simp [hL, hB]
    · exact div_mul_cancel₀ _ (by positivity)
  rw [← ha, ← hb]
  ring

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,m,d), At label scale at least one, the affine schedule includes a rare cell.  This gives [the stated result](goal).-/
-- @node: affine_tuning_Kstar_pos
lemma affine_tuning_Kstar_pos (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps) : 0 < (affineTuning n m d eps).Kstar := by
  obtain ⟨hM, _, hL, _, _, _, hb, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hell : 1 ≤ logScale n eps := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1 + labelScale n eps by
        apply le_add_of_nonneg_right; dsimp [labelScale]; positivity)
    simpa only [logScale, Real.log_exp] using h
  have hMe : 128 ≤ (affineTuning n m d eps).M * eps := by
    have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
    have h := mul_le_mul_of_nonneg_right hM heps.le
    nlinarith
  have hden : 100 ≤ 100000 * (affineTuning n m d eps).M * eps *
      ((affineTuning n m d eps).L : Real) := by
    have h := mul_le_mul hMe hL (by linarith : 0 ≤ 8 * logScale n eps) (by linarith)
    nlinarith
  have hbsmall : (affineTuning n m d eps).b0 ≤ 1 / 100 := by
    rw [affine_tuning_b0_identity n m d eps hn hd heps heps']
    apply (div_le_iff₀ (by linarith : 0 < 100000 * (affineTuning n m d eps).M * eps *
      ((affineTuning n m d eps).L : Real))).mpr
    linarith
  have hinv : (1 : Real) ≤ 1 / (100 * (affineTuning n m d eps).b0) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hfloor : 1 ≤ Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) :=
    (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hinv)
  change 0 < min (d - 1) (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)))
  exact lt_min (by omega) (by omega)

/--
[For the complete-sample size](hyp:n), [the auxiliary-sample size](hyp:m), [the covariate dimension](hyp:d), [the overlap floor](hyp:eps), [a cone-dual certificate](hyp:sigma), and [the latent assignments of rare cells](hyp:lat),
[the raw normalizer](goal) is the remaining reservoir mass after the affine rare-cell masses are assigned.
-/
noncomputable def rawNormalizer (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) : Real :=
  1 - ((affineTuning n m d eps).Kstar : Real) * latentMeanMass sigma +
    ∑ j, ((affineTuning n m d eps).b0 + latentNode sigma (lat j))

end CausalSmith.Stat.AnnotationRarearmFrontier
