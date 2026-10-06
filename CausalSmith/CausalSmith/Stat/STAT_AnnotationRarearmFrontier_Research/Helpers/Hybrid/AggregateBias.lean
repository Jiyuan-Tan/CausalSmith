module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.FalseLightRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.MixtureVariance

/-!
Aggregate pilot bias and heavy-cell separation bounds for equations (10)--(13)
of the hybrid arm risk proof.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- [Under the stated inputs and conditions](hyp:hS,htp,ht,hratio,alpha,J,hcell,hmass,S,tp,t,s,v,mu), The incorrectly selected inverse branch has total bias at most S to the
negative twentieth power, using only the total cell mass bound.  This gives [the stated result](goal).-/
-- @node: hybrid_false_heavy_bias_sum
lemma hybrid_false_heavy_bias_sum (S tp t : Real)
    (hS : Real.exp 4096 ≤ S) (htp : 0 < tp) (ht : 0 < t)
    (hratio : 1 / 3 ≤ t / tp) {alpha : Type} (J : Finset alpha)
    (s v mu : alpha → Real)
    (hcell : ∀ j ∈ J, 0 ≤ s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1)
    (hmass : (J.sum (fun j => s j + v j)) ≤ 1) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let k0 := Nat.floor (tp * B / 4)
    (∑ j ∈ J, v j * mu j *
      ((1 - (poissonMeasure (Real.toNNReal (tp * s j))).real (Set.Iic k0)) *
        Real.exp (-t * s j))) ≤ (S ^ 20)⁻¹ := by
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let k0 := Nat.floor (tp * B / 4)
  calc
    _ ≤ ∑ j ∈ J, (s j + v j) * (S ^ 20)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hs, hv, hmu⟩ := hcell j hj
      have hw : 0 ≤ v j * mu j := mul_nonneg hv hmu.1
      have hwp : v j * mu j ≤ s j + v j :=
        (mul_le_of_le_one_right hv hmu.2).trans (by linarith)
      have hb := hybrid_false_heavy_bias_bound S tp t (s j) hS htp ht hs hratio
      exact (mul_le_mul_of_nonneg_left hb hw).trans
        (mul_le_mul_of_nonneg_right hwp (by positivity))
    _ = (J.sum (fun j => s j + v j)) * (S ^ 20)⁻¹ := by rw [Finset.sum_mul]
    _ ≤ (S ^ 20)⁻¹ := by
      simpa using mul_le_mul_of_nonneg_right hmass (show 0 ≤ (S ^ 20)⁻¹ by positivity)

/-- [Under the stated inputs and conditions](hyp:hS,hu,htp,ht,hs,hv,hmu,heps,hov,hratio,S,u,tp,t,s,v,mu,eps), A light cell's actual pilot mixture retains the polynomial approximation bias
and an inverse twentieth power remainder weighted by cell mass.  This gives [the stated result](goal).-/
-- @node: hybrid_light_selected_bias
lemma hybrid_light_selected_bias (S u tp t s v mu eps : Real)
    (hS : Real.exp 4096 ≤ S) (hu : 0 < u) (htp : 0 < tp) (ht : 0 < t)
    (hs : 0 < s) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1)
    (heps : 0 < eps) (hov : eps * (s + v) ≤ s) (hratio : 1 / 3 ≤ t / tp) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let k0 := Nat.floor (tp * B / 4)
    s ≤ B →
    |(∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s))).prod
        (cellPoissonLaw u t (s * mu) s v)) - (s + v) * mu| ≤
      B / (eps * (L : Real) ^ 2) + (s + v) * (S ^ 20)⁻¹ := by
  dsimp only
  intro hsB
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let k0 := Nat.floor (tp * B / 4)
  let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic k0)
  have hL : 2 ≤ L := by have := (hybrid_degree_calibration S hS).1; omega
  have hB : 0 < B := by
    dsimp [B]
    have hLp : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
    positivity
  have hpi : pi ∈ Set.Icc 0 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hE := (chebyshev_factorial_certificate L hL).1
    (s / B) (div_pos hs hB) ((div_le_one hB).2 hsB)
  have hb := hybrid_light_polynomial_bias L B u t s v mu eps
    hL hB hu ht hs hsB hv hmu heps hov
  rw [(hybrid_branch_means L B u t s v mu hL hB hu ht hs hv hmu).1] at hb
  rw [sub_sub_cancel_left, abs_neg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hv hmu.1) hE.1)] at hb
  have htail := hybrid_false_heavy_bias_bound S tp t s hS htp ht hs.le hratio
  have hw : 0 ≤ v * mu := mul_nonneg hv hmu.1
  have hwp : v * mu ≤ s + v :=
    (mul_le_of_le_one_right hv hmu.2).trans (by linarith)
  rw [hybrid_pilot_cell_mean L k0 B u tp t s v mu hL hB hu ht hs hv hmu]
  have hnon : 0 ≤ v * mu * (pi * (chebE L).eval (s / B) +
      (1 - pi) * Real.exp (-t * s)) :=
    mul_nonneg hw (add_nonneg (mul_nonneg hpi.1 hE.1)
      (mul_nonneg (sub_nonneg.mpr hpi.2) (Real.exp_nonneg _)))
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hnon]
  change v * mu * (pi * (chebE L).eval (s / B) +
    (1 - pi) * Real.exp (-t * s)) ≤ _
  calc
    _ = pi * (v * mu * (chebE L).eval (s / B)) +
        v * mu * ((1 - pi) * Real.exp (-t * s)) := by ring
    _ ≤ B / (eps * (L : Real) ^ 2) + (s + v) * (S ^ 20)⁻¹ := by
      apply add_le_add
      · exact (mul_le_of_le_one_left (mul_nonneg hw hE.1) hpi.2).trans hb
      · exact (mul_le_mul_of_nonneg_left htail hw).trans
          (mul_le_mul_of_nonneg_right hwp (by positivity))

/-- [Under the stated inputs and conditions](hyp:hS,hu,htp,ht,heps,hratio,alpha,J,S,u,tp,t,eps,s,v,mu), Equation (12) on the light cells: summing the actual cell biases gives one
bandwidth term per cell and a single public-scale pilot remainder.  This gives [the stated result](goal).-/
-- @node: hybrid_light_selected_bias_sum
lemma hybrid_light_selected_bias_sum (S u tp t eps : Real)
    (hS : Real.exp 4096 ≤ S) (hu : 0 < u) (htp : 0 < tp) (ht : 0 < t)
    (heps : 0 < eps) (hratio : 1 / 3 ≤ t / tp)
    {alpha : Type} (J : Finset alpha) (s v mu : alpha → Real) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let k0 := Nat.floor (tp * B / 4)
    (∀ j ∈ J, 0 < s j ∧ s j ≤ B ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
      eps * (s j + v j) ≤ s j) →
    (J.sum (fun j => s j + v j)) ≤ 1 →
    |∑ j ∈ J, ((∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s j))).prod
        (cellPoissonLaw u t (s j * mu j) (s j) (v j))) - (s j + v j) * mu j)| ≤
      J.card * (B / (eps * (L : Real) ^ 2)) + (S ^ 20)⁻¹ := by
  dsimp only
  intro hcell hmass
  calc
    _ ≤ ∑ j ∈ J, |(∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue _ _ _ u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s j))).prod
        (cellPoissonLaw u t (s j * mu j) (s j) (v j))) - (s j + v j) * mu j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ J, ((2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) / min tp t /
        (eps * (Nat.floor (Real.log S / 1024) : Real) ^ 2) +
        (s j + v j) * (S ^ 20)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hs, hsB, hv, hmu, hov⟩ := hcell j hj
      exact hybrid_light_selected_bias S u tp t (s j) (v j) (mu j) eps
        hS hu htp ht hs hv hmu heps hov hratio hsB
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, nsmul_eq_mul]
      exact add_le_add_right
        (by
          simpa using mul_le_mul_of_nonneg_right hmass
            (show 0 ≤ (S ^ 20)⁻¹ by positivity)) _

/-- [Under the stated inputs and conditions](hyp:L,hL,z,hz), The coefficient certificate controls the continuation polynomial on the entire
nonnegative half-line, including cells outside the approximation interval.  This gives [the stated result](goal).-/
-- @node: hybrid_chebG_eval_growth
lemma hybrid_chebG_eval_growth (L : Nat) (hL : 2 ≤ L) (z : Real) (hz : 0 ≤ z) :
    |(chebG L).eval z| ≤ (14 : Real) ^ L * (1 + z) ^ L := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (chebG_natDegree_le L)
    (by omega : L - 2 < L - 1))]
  calc
    _ ≤ ∑ h ∈ Finset.range (L - 1), |(chebG L).coeff h * z ^ h| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ Finset.range (L - 1), |(chebG L).coeff h| * (1 + z) ^ L := by
      apply Finset.sum_le_sum
      intro h hh
      rw [abs_mul, abs_of_nonneg (pow_nonneg hz _)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ hz (by linarith) h).trans
        (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + z) (by
          have := Finset.mem_range.mp hh
          omega))
    _ = (∑ h ∈ Finset.range (L - 1), |(chebG L).coeff h|) * (1 + z) ^ L := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (chebG_coeff_sum_le L hL) (by positivity)

/-- [Under the stated inputs and conditions](hyp:L,hL,z,hz), The polynomial bias outside the bandwidth grows more slowly than the full
factorial second-moment envelope used by the pilot-tail absorption.  This gives [the stated result](goal).-/
-- @node: hybrid_chebE_growth
lemma hybrid_chebE_growth (L : Nat) (hL : 2 ≤ L) (z : Real) (hz : 0 < z) :
    |(chebE L).eval z| ≤
      2 * (((2 : Real) ^ 24) ^ L * (1 + z) ^ (2 * L + 2)) := by
  have hG := hybrid_chebG_eval_growth L hL z hz.le
  have hid : (chebE L).eval z = 1 - z * (chebG L).eval z := by
    rw [(cheb_continuation_eval L (by omega) z hz.ne').2]
    field_simp
    ring
  have hgrowth : z * ((14 : Real) ^ L * (1 + z) ^ L) ≤
      ((2 : Real) ^ 24) ^ L * (1 + z) ^ (2 * L + 2) := by
    calc
      _ ≤ (1 + z) * (((2 : Real) ^ 24) ^ L * (1 + z) ^ L) := by
        apply mul_le_mul (by linarith)
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 14) (by norm_num) L)
            (by positivity)) (by positivity) (by positivity)
      _ = ((2 : Real) ^ 24) ^ L * (1 + z) ^ (L + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + z) (by omega)) (by positivity)
  have hone : 1 ≤ ((2 : Real) ^ 24) ^ L * (1 + z) ^ (2 * L + 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by linarith))
  calc
    _ = |1 - z * (chebG L).eval z| := by rw [hid]
    _ ≤ 1 + z * |(chebG L).eval z| := by
      simpa [abs_mul, abs_of_pos hz] using abs_sub (1 : Real) (z * (chebG L).eval z)
    _ ≤ 1 + z * ((14 : Real) ^ L * (1 + z) ^ L) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hG hz.le) 1
    _ ≤ _ := by linarith

/-- [Under the stated inputs and conditions](hyp:hS,htp,hB,hsB,hv,hmu,hscale,S,tp,B,s,v,mu), A falsely light cell's polynomial bias is absorbed by its pilot probability,
with no inverse-overlap factor in the remainder.  This gives [the stated result](goal).-/
-- @node: hybrid_false_light_bias_bound
lemma hybrid_false_light_bias_bound (S tp B s v mu : Real)
    (hS : Real.exp 4096 ≤ S) (htp : 0 < tp) (hB : 0 < B)
    (hsB : B < s) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1)
    (hscale : (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B) :
    let L := Nat.floor (Real.log S / 1024)
    let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4)))
    pi * |v * mu * (chebE L).eval (s / B)| ≤ 2 * (s + v) * (S ^ 20)⁻¹ := by
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4)))
  let F := ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2)
  have hs : 0 < s := hB.trans hsB
  have hcal := hybrid_degree_calibration S hS
  have hg := hybrid_chebE_growth L (by have := hcal.1; omega) (s / B) (div_pos hs hB)
  have hp : 0 ≤ pi := measureReal_nonneg
  have hvm : 0 ≤ v * mu := mul_nonneg hv hmu.1
  have hvmp : v * mu ≤ s + v :=
    (mul_le_of_le_one_right hv hmu.2).trans (by linarith)
  have htail : pi * F ≤ (S ^ 20)⁻¹ := by
    calc
      _ ≤ Real.exp (-tp * s / 4) * F :=
        mul_le_mul_of_nonneg_right (pilot_false_light_tail tp B s htp hB hsB) (by positivity)
      _ ≤ Real.exp (-200000 * (L : Real)) := by
        simpa only [F, mul_assoc] using
          false_light_absorption L tp B s hcal.1 htp hB hsB hscale
      _ ≤ _ := hcal.2.2.2
  rw [abs_mul, abs_of_nonneg hvm]
  calc
    _ ≤ pi * ((s + v) * (2 * F)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hvmp hg (abs_nonneg _) (by positivity)) hp
    _ = 2 * (s + v) * (pi * F) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)

/-- [Under the stated inputs and conditions](hyp:hS,hu,htp,ht,hv,hmu,hratio,S,u,tp,t,s,v,mu), The actual heavy-cell mixture bias includes both pilot errors and is bounded
by three times cell mass times the public inverse twentieth power.  This gives [the stated result](goal).-/
-- @node: hybrid_heavy_selected_bias
lemma hybrid_heavy_selected_bias (S u tp t s v mu : Real)
    (hS : Real.exp 4096 ≤ S) (hu : 0 < u) (htp : 0 < tp) (ht : 0 < t)
    (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1) (hratio : 1 / 3 ≤ t / tp) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let k0 := Nat.floor (tp * B / 4)
    B < s →
    |(∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s))).prod
        (cellPoissonLaw u t (s * mu) s v)) - (s + v) * mu| ≤
      3 * (s + v) * (S ^ 20)⁻¹ := by
  dsimp only
  intro hsB
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let k0 := Nat.floor (tp * B / 4)
  let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic k0)
  have hL : 2 ≤ L := by have := (hybrid_degree_calibration S hS).1; omega
  have hB : 0 < B := by
    have hLp : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
    dsimp [B]; positivity
  have hs : 0 < s := hB.trans hsB
  have hpi : 0 ≤ pi := measureReal_nonneg
  have hvm : 0 ≤ v * mu := mul_nonneg hv hmu.1
  have hvmp : v * mu ≤ s + v :=
    (mul_le_of_le_one_right hv hmu.2).trans (by linarith)
  have hpol := hybrid_false_light_bias_bound S tp B s v mu hS htp hB hsB hv hmu
    (hybrid_bandwidth_pilot_scale L tp t htp ht)
  have hinv := hybrid_false_heavy_bias_bound S tp t s hS htp ht hs.le hratio
  rw [hybrid_pilot_cell_mean L k0 B u tp t s v mu hL hB hu ht hs hv hmu,
    sub_sub_cancel_left, abs_neg]
  change |v * mu * (pi * (chebE L).eval (s / B) + (1 - pi) * Real.exp (-t * s))| ≤ _
  calc
    _ = |pi * (v * mu * (chebE L).eval (s / B)) +
        v * mu * ((1 - pi) * Real.exp (-t * s))| := by congr 1; ring
    _ ≤ pi * |v * mu * (chebE L).eval (s / B)| +
        v * mu * ((1 - pi) * Real.exp (-t * s)) := by
      have hnon : 0 ≤ v * mu * ((1 - pi) * Real.exp (-t * s)) :=
        mul_nonneg hvm (mul_nonneg
          (sub_nonneg.mpr (show pi ≤ 1 from measureReal_le_one)) (Real.exp_nonneg _))
      simpa only [abs_mul, abs_of_nonneg hpi, abs_of_nonneg hnon] using
        abs_add_le (pi * (v * mu * (chebE L).eval (s / B)))
          (v * mu * ((1 - pi) * Real.exp (-t * s)))
    _ ≤ 2 * (s + v) * (S ^ 20)⁻¹ + (s + v) * (S ^ 20)⁻¹ :=
      add_le_add hpol ((mul_le_mul_of_nonneg_left hinv hvm).trans
        (mul_le_mul_of_nonneg_right hvmp (by positivity)))
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:L,hu,ht,hv,B,u,t,s,v), A zero-success Poisson outcome count makes both branch expectations zero,
including at a null own-arm cell.  This gives [the stated result](goal).-/
-- @node: hybrid_zero_outcome_branch_means
lemma hybrid_zero_outcome_branch_means (L : Nat) (B u t s v : Real)
    (hu : 0 < u) (ht : 0 < t) (hv : 0 ≤ v) :
    (∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t 0 s v) = 0 ∧
    (∫ z, inverseCellBranch u z ∂cellPoissonLaw u t 0 s v) = 0 := by
  constructor
  · let G : Nat → Real := fun K => ∑ h ∈ Finset.range (L - 1),
      (chebG L).coeff h * (K.descFactorial h : Real) / (t * B) ^ h
    have hG : Integrable G (poissonMeasure (Real.toNNReal (t * s))) := by
      apply integrable_finsetSum
      intro h _
      exact ((Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable
        _ h).const_mul _).div_const _
    have heq : polynomialCellBranch L B u t =
        (fun z : Nat × Nat × Nat => (z.1 : Real) / u *
          (1 + (z.2.2 : Real) * (G z.2.1 / (t * B)))) := by
      funext z; dsimp [polynomialCellBranch, G]; ring
    rw [heq, poisson_cell_multiplier_mean u t 0 s v hu (by norm_num) hv ht
      (fun K => G K / (t * B)) (hG.div_const _), zero_mul]
  · let F : Nat → Real := fun K => ((K : Real) + 1)⁻¹
    have hF : Integrable F (poissonMeasure (Real.toNNReal (t * s))) := by
      simpa only [F, Nat.cast_add, Nat.cast_one] using
        (Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two
          (Real.toNNReal (t * s))).integrable (by norm_num)
    have heq : inverseCellBranch u =
        (fun z : Nat × Nat × Nat => (z.1 : Real) / u *
          (1 + (z.2.2 : Real) * F z.2.1)) := by
      funext z; simp [inverseCellBranch, F, div_eq_mul_inv]
    rw [heq, poisson_cell_multiplier_mean u t 0 s v hu (by norm_num) hv ht F hF,
      zero_mul]

/-- [Under the stated inputs and conditions](hyp:hu,ht,hv,L,k0,B,u,tp,t,s,v), Null outcome counts contribute zero also after the independent pilot selection.  This gives [the stated result](goal).-/
-- @node: hybrid_zero_outcome_selected_mean
lemma hybrid_zero_outcome_selected_mean (L k0 : Nat) (B u tp t s v : Real)
    (hu : 0 < u) (ht : 0 < t) (hv : 0 ≤ v) :
    (∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s))).prod (cellPoissonLaw u t 0 s v)) = 0 := by
  let : IsProbabilityMeasure (cellPoissonLaw u t 0 s v) := by
    unfold cellPoissonLaw
    infer_instance
  rw [hybrid_cell_event_mixture]
  have hLp := hybrid_cell_branches_memLp L B u t 0 s v
  rw [Causalean.Mathlib.Probability.integral_eventSelectedMixture _ _ _
    measurableSet_Iic _ _ (hLp.1.integrable (by norm_num)) (hLp.2.integrable (by norm_num))]
  obtain ⟨hp, hh⟩ := hybrid_zero_outcome_branch_means L B u t s v hu ht hv
  rw [hp, hh]
  ring

/-- [Under the stated inputs and conditions](hyp:hS,hu,htp,ht,heps,hratio,alpha,J,S,u,tp,t,eps,s,v,mu), Equation (12): the sum of canonical hybrid cell biases is bounded by one
approximation term per cell and a universal pilot remainder. Null cells are included.  This gives [the stated result](goal).-/
-- @node: hybrid_selected_bias_sum
lemma hybrid_selected_bias_sum (S u tp t eps : Real)
    (hS : Real.exp 4096 ≤ S) (hu : 0 < u) (htp : 0 < tp) (ht : 0 < t)
    (heps : 0 < eps) (hratio : 1 / 3 ≤ t / tp)
    {alpha : Type} (J : Finset alpha) (s v mu : alpha → Real) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let k0 := Nat.floor (tp * B / 4)
    (∀ j ∈ J, 0 ≤ s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
      eps * (s j + v j) ≤ s j) →
    (J.sum (fun j => s j + v j)) ≤ 1 →
    |∑ j ∈ J, ((∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s j))).prod
        (cellPoissonLaw u t (s j * mu j) (s j) (v j))) - (s j + v j) * mu j)| ≤
      J.card * (B / (eps * (L : Real) ^ 2)) + 3 * (S ^ 20)⁻¹ := by
  dsimp only
  intro hcell hmass
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let k0 := Nat.floor (tp * B / 4)
  have hL : 2 ≤ L := by have := (hybrid_degree_calibration S hS).1; omega
  have hB : 0 < B := by
    have hLp : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
    dsimp [B]; positivity
  have happrox : 0 ≤ B / (eps * (L : Real) ^ 2) := by positivity
  calc
    _ ≤ ∑ j ∈ J, |(∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s j))).prod
        (cellPoissonLaw u t (s j * mu j) (s j) (v j))) - (s j + v j) * mu j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ J, (B / (eps * (L : Real) ^ 2) + 3 * (s j + v j) * (S ^ 20)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hs, hv, hmu, hov⟩ := hcell j hj
      by_cases hs0 : s j = 0
      · have hv0 : v j = 0 := by rw [hs0] at hov; nlinarith
        have hz := hybrid_zero_outcome_selected_mean L k0 B u tp t 0 0 hu ht (by norm_num)
        simpa only [hs0, hv0, zero_mul, mul_zero, add_zero, sub_zero, abs_zero] using
          (show |(∫ z : Nat × (Nat × Nat × Nat),
            hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
            (poissonMeasure (Real.toNNReal (tp * 0))).prod (cellPoissonLaw u t 0 0 0))| ≤
              B / (eps * (L : Real) ^ 2) from by rw [hz, abs_zero]; exact happrox)
      · have hsp : 0 < s j := lt_of_le_of_ne hs (Ne.symm hs0)
        by_cases hsB : s j ≤ B
        · have hb := hybrid_light_selected_bias S u tp t (s j) (v j) (mu j) eps
            hS hu htp ht hsp hv hmu heps hov hratio hsB
          exact hb.trans (by
            have hn : 0 ≤ (s j + v j) * (S ^ 20)⁻¹ := by positivity
            change B / (eps * (L : Real) ^ 2) + (s j + v j) * (S ^ 20)⁻¹ ≤ _
            nlinarith)
        · have hb := hybrid_heavy_selected_bias S u tp t (s j) (v j) (mu j)
            hS hu htp ht hv hmu hratio (lt_of_not_ge hsB)
          exact hb.trans (le_add_of_nonneg_left happrox)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have heq : (∑ j ∈ J, 3 * (s j + v j) * (S ^ 20)⁻¹) =
          3 * (∑ j ∈ J, (s j + v j)) * (S ^ 20)⁻¹ := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum]
      rw [heq]
      apply add_le_add_right
      have hh := mul_le_mul_of_nonneg_right hmass
        (show 0 ≤ 3 * (S ^ 20)⁻¹ by positivity)
      nlinarith only [hh]


end CausalSmith.Stat.AnnotationRarearmFrontier
