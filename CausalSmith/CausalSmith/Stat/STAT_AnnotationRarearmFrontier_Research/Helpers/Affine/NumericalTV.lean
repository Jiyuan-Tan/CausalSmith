module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalSeparation
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.SignedCountTail

/-!
Uniform numerical bound on the joint raw-mixture Taylor envelope in equation (8).
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:eps,hn,n,m,d), The scheduled Taylor argument is exactly the degree divided by 500.  This gives [the stated result](goal).-/
-- @node: affine_tuning_taylor_argument
lemma affine_tuning_taylor_argument (n m d : Nat) (eps : Real) (hn : 1 ≤ n) :
    2 * (affineTuning n m d eps).M * (affineTuning n m d eps).B =
      ((affineTuning n m d eps).L : Real) / 500 := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hmR : (0 : Real) ≤ m := Nat.cast_nonneg m
  have hM : (affineTuning n m d eps).M ≠ 0 := by
    dsimp [affineTuning]
    linarith
  change 2 * (affineTuning n m d eps).M *
    (((affineTuning n m d eps).L : Real) / (1000 * (affineTuning n m d eps).M)) = _
  field_simp
  <;> ring

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,m,d), The summed marked intensity is controlled by the capped rare-cell mass budget.  This gives [the stated result](goal).-/
-- @node: affine_tuning_marked_intensity_bound
lemma affine_tuning_marked_intensity_bound (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).u *
      (affineTuning n m d eps).alpha ≤ (32 / 25 : Real) * ((n : Real) * eps) := by
  have hbudget := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.2.2.2.2.2
  have hab : (affineTuning n m d eps).alpha = eps * (affineTuning n m d eps).b0 := by
    change _ = eps * ((affineTuning n m d eps).alpha / eps)
    field_simp
  rw [hab]
  have hu : (affineTuning n m d eps).u = 128 * (n : Real) := rfl
  rw [hu]
  have h := mul_le_mul_of_nonneg_right hbudget
    (show 0 ≤ 128 * (n : Real) * eps by positivity)
  nlinarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,m,d), Degree calibration makes the label-scale weighted exponential tail uniformly tiny.  This gives [the stated result](goal).-/
-- @node: affine_tuning_weighted_exp_tail
lemma affine_tuning_weighted_exp_tail (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    ((n : Real) * eps) * Real.exp (-5 * ((affineTuning n m d eps).L : Real)) ≤
      (1 : Real) / 256 := by
  have hL := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.1
  have hell := affine_logScale_one_le n eps heps.le
  have hS : (n : Real) * eps ≤ Real.exp (logScale n eps) := by
    rw [logScale, Real.exp_log (by unfold labelScale; positivity)]
    unfold labelScale
    linarith [Real.exp_pos 1]
  have he8 : (256 : Real) ≤ Real.exp 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2)
      (Real.exp_one_gt_two.le) 8
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hneg : Real.exp (-8 : Real) ≤ (1 : Real) / 256 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) he8
  calc
    _ ≤ Real.exp (logScale n eps) *
        Real.exp (-5 * ((affineTuning n m d eps).L : Real)) :=
      mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le
    _ = Real.exp (logScale n eps - 5 * ((affineTuning n m d eps).L : Real)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-39 * logScale n eps) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := hneg

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,m,d), The full K-cell Taylor envelope is below the testing distance budget of 1/64.  This gives [the stated result](goal).-/
-- @node: affine_poisson_joint_tail_small
lemma affine_poisson_joint_tail_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).u *
      (affineTuning n m d eps).alpha *
      (∑' h : Nat, if (affineTuning n m d eps).L < h then
        (2 * (affineTuning n m d eps).M * (affineTuning n m d eps).B) ^ h /
          (h.factorial : Real) else 0) < 1 / 64 := by
  obtain ⟨_, _, hL, _, _, ha, _, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hell := affine_logScale_one_le n eps heps.le
  have hLn : 2 ≤ (affineTuning n m d eps).L := by
    have : (2 : Real) ≤ (affineTuning n m d eps).L := by linarith
    exact_mod_cast this
  rw [affine_tuning_taylor_argument n m d eps hn]
  have htail := affine_poisson_taylor_tail (affineTuning n m d eps).L hLn
  have hintensity := affine_tuning_marked_intensity_bound n m d eps hn hd heps heps'
  have hexp := affine_tuning_weighted_exp_tail n m d eps hn hd heps heps'
  have hI : 0 ≤ ((affineTuning n m d eps).Kstar : Real) *
      (affineTuning n m d eps).u * (affineTuning n m d eps).alpha := by
    have hu : (affineTuning n m d eps).u = 128 * (n : Real) := rfl
    rw [hu]; positivity
  calc
    _ ≤ ((affineTuning n m d eps).Kstar : Real) * (affineTuning n m d eps).u *
        (affineTuning n m d eps).alpha *
        (2 * Real.exp (-5 * ((affineTuning n m d eps).L : Real))) :=
      mul_le_mul_of_nonneg_left htail hI
    _ ≤ ((32 / 25 : Real) * ((n : Real) * eps)) *
        (2 * Real.exp (-5 * ((affineTuning n m d eps).L : Real))) :=
      mul_le_mul_of_nonneg_right hintensity (by positivity)
    _ ≤ (1 : Real) / 100 := by nlinarith
    _ < _ := by norm_num

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,m,d), The full three-count coefficient envelope, weighted by the K-cell marked
intensity, meets the raw testing budget directly.  This gives [the stated result](goal).-/
-- @node: affine_three_count_joint_envelope_small
lemma affine_three_count_joint_envelope_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    let t := affineTuning n m d eps
    (t.Kstar : Real) * t.u * t.alpha *
      (∑' j : Nat, (Real.exp (-t.M * t.b0) *
        (∑' c : Nat, t.M ^ c / (c.factorial : Real) *
          (∑' r : Nat, ∑' g : Nat, t.u ^ r / ((r + 1).factorial : Real) *
            (t.w ^ g / (g.factorial : Real)) *
            (((Polynomial.C (eps * t.b0) +
                Polynomial.C (1 - eps) * Polynomial.X) ^ (r + g)) *
              ((Polynomial.C ((1 - eps) * t.b0) +
                Polynomial.C eps * Polynomial.X) ^ c)).coeff j))) *
        t.B ^ j * ∑' k : Nat, if t.L < k + j then
          (t.M * t.B) ^ k / (k.factorial : Real) else 0) < 1 / 64 := by
  intro t
  obtain ⟨_, _, _, _, hB, ha, hb, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hu : 0 ≤ t.u := by change 0 ≤ 128 * (n : Real); positivity
  have hw : 0 ≤ t.w := by change 0 ≤ 128 * ((n : Real) + m); positivity
  have hM : t.M = t.u + t.w := rfl
  have hI : 0 ≤ (t.Kstar : Real) * t.u * t.alpha := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) ha.le
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left
      (affine_three_count_total_degree_tail_le t.b0 eps t.u t.w t.M t.B t.L
        hb.le heps.le (by linarith) hu hw hM hB.le) hI)
    (affine_poisson_joint_tail_small n m d eps hn hd heps heps')

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The K-cell sum of the absolute equation (6) signed masses meets the testing
budget in equation (8), with no bound on the common control baseline.  This gives [the stated result](goal).-/
-- @node: affine_signed_raw_joint_count_small
lemma affine_signed_raw_joint_count_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let t := affineTuning n m d eps
    (t.Kstar : Real) * (∑' v : Nat × (Nat × Nat),
      |∑ i, sigma.weights i * (Real.exp (-t.M * (t.b0 + sigma.nodes i)) *
        (t.u * (eps * t.b0 + (1 - eps) * sigma.nodes i)) ^ (v.2.1 + 1) *
        (t.w * (eps * t.b0 + (1 - eps) * sigma.nodes i)) ^ v.2.2 *
        (t.M * ((1 - eps) * t.b0 + eps * sigma.nodes i)) ^ v.1 /
        (((v.2.1 + 1).factorial : Real) * (v.2.2.factorial : Real) *
          (v.1.factorial : Real)) *
        (eps * t.b0 / (eps * t.b0 + (1 - eps) * sigma.nodes i)))|) < 1 / 64 := by
  intro t
  obtain ⟨_, _, _, _, _, _, hb, _⟩ := affine_tuning_bounds n m d eps hn hd heps heps'
  have hu : 0 ≤ t.u := by change 0 ≤ 128 * (n : Real); positivity
  have hw : 0 ≤ t.w := by change 0 ≤ 128 * ((n : Real) + m); positivity
  have h := (affine_signed_raw_count_tail_bound sigma t.b0 t.u t.w t.M
    hb heps (by linarith) hu hw rfl).2
  have ha : t.alpha = eps * t.b0 := by
    change t.alpha = eps * (t.alpha / eps)
    field_simp
  calc
    _ ≤ (t.Kstar : Real) * (t.u * (eps * t.b0) *
        ∑' h : Nat, if t.L < h then (2 * t.M * t.B) ^ h / (h.factorial : Real) else 0) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = (t.Kstar : Real) * t.u * t.alpha *
        (∑' h : Nat, if t.L < h then (2 * t.M * t.B) ^ h / (h.factorial : Real) else 0) := by
      rw [ha]; ring
    _ < _ := affine_poisson_joint_tail_small n m d eps hn hd heps heps'

end CausalSmith.Stat.AnnotationRarearmFrontier
