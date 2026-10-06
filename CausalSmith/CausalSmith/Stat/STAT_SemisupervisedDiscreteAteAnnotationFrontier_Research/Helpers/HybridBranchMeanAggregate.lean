module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyMean

/-! Aggregate branch-mean comparison for light cells. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- C31, with explicit overlap-dependent constants.  [the stated conditions](hyp:hP,hu,ht,heps,hB,hL) [the stated conclusion](goal). -/
lemma sum_light_branchMean_sq_le {d : Nat} {eps B : Real} {L : Nat}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    {u t : Real} (hu : 0 < u) (ht : 0 < t)
    (heps : 0 < eps) (hB : 0 < B) (hL : 2 ≤ L) :
    let muE := fun x : Fin d ↦
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))
    (∑ x ∈ Finset.univ.filter (fun x : Fin d ↦ cellMass P x ≤ B),
      ((∫ W, hybridLightPools L B u t W ∂muE x) -
        ∫ W, hybridHeavyPools u W ∂muE x) ^ 2) ≤
      8 * d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + 4 / (eps * t) := by
  dsimp only
  classical
  let S : Finset (Fin d) := Finset.univ.filter fun x ↦ cellMass P x ≤ B
  let muE := fun x : Fin d ↦
    ((Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
     (Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (t * armMass P x a))))
  let theta := fun x : Fin d ↦ cellMass P x *
    (outcomeMean P true x - outcomeMean P false x)
  let EL := fun x : Fin d ↦ ∫ W, hybridLightPools L B u t W ∂muE x
  let EH := fun x : Fin d ↦ ∫ W, hybridHeavyPools u W ∂muE x
  have hp0 (x : Fin d) : 0 ≤ cellMass P x := (cellMass_mem_unitInterval P x).1
  have hsum : ∑ x : Fin d, cellMass P x = 1 := cellMass_sum_eq_one_annotation P
  have hpoint (x : Fin d) (hx : x ∈ S) :
      (EL x - EH x) ^ 2 ≤
        8 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) +
        8 * cellMass P x ^ 2 *
          Real.exp (-2 * eps * t * cellMass P x) := by
    have hcell : cellMass P x ≤ B := by
      simpa [S] using (Finset.mem_filter.mp hx).2
    have hlight : |EL x - theta x| ≤ 2 * B / (eps * (L : Real) ^ 2) := by
      dsimp [EL, theta, muE]
      rw [integral_hybridLightPools P hu ht hB L x]
      exact light_exact_mean_bias_le P hP x heps hB hL hcell
    have hheavy : |EH x - theta x| ≤
        2 * cellMass P x * Real.exp (-eps * t * cellMass P x) := by
      exact integral_hybridHeavyPools_bias_le P hP x hu ht heps
    have hA0 : 0 ≤ 2 * B / (eps * (L : Real) ^ 2) := by positivity
    have hD0 : 0 ≤ 2 * cellMass P x *
        Real.exp (-eps * t * cellMass P x) :=
      mul_nonneg (mul_nonneg (by norm_num) (hp0 x)) (Real.exp_pos _).le
    rcases (abs_le.mp hlight) with ⟨hlow, hupp⟩
    rcases (abs_le.mp hheavy) with ⟨hhlow, hhup⟩
    have hid : EL x - EH x = (EL x - theta x) - (EH x - theta x) := by ring
    rw [hid]
    have hsquare : ((EL x - theta x) - (EH x - theta x)) ^ 2 ≤
        2 * (2 * B / (eps * (L : Real) ^ 2)) ^ 2 +
        2 * (2 * cellMass P x * Real.exp (-eps * t * cellMass P x)) ^ 2 := by
      nlinarith [sq_nonneg ((EL x - theta x) + (EH x - theta x))]
    calc
      _ ≤ _ := hsquare
      _ = _ := by
        have hexpsq : Real.exp (-eps * t * cellMass P x) ^ 2 =
            Real.exp (-2 * eps * t * cellMass P x) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        simp only [mul_pow]
        rw [hexpsq]
        field_simp [heps.ne', ht.ne']
        ring
  have htail (x : Fin d) : cellMass P x ^ 2 *
      Real.exp (-2 * eps * t * cellMass P x) ≤
        cellMass P x / (2 * eps * Real.exp 1 * t) := by
    have henv := poisson_bias_envelope (eps := 2 * eps) (t := t)
      (z := cellMass P x) (by positivity) ht (hp0 x)
    have hp0' := hp0 x
    have hexp0 : 0 ≤ Real.exp (-2 * eps * t * cellMass P x) := Real.exp_pos _ |>.le
    calc
      _ = cellMass P x *
          (cellMass P x * Real.exp (-(2 * eps) * t * cellMass P x)) := by ring
      _ ≤ cellMass P x * (1 / (2 * eps * Real.exp 1 * t)) :=
        mul_le_mul_of_nonneg_left henv hp0'
      _ = _ := by ring
  change (∑ x ∈ S, (EL x - EH x) ^ 2) ≤ _
  calc
    _ ≤ ∑ x ∈ S, (8 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) +
        8 * cellMass P x ^ 2 * Real.exp (-2 * eps * t * cellMass P x)) :=
      Finset.sum_le_sum fun x hx ↦ hpoint x hx
    _ ≤ ∑ x ∈ S, (8 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) +
        8 * (cellMass P x / (2 * eps * Real.exp 1 * t))) := by
      apply Finset.sum_le_sum
      intro x _
      nlinarith [mul_le_mul_of_nonneg_left (htail x) (by norm_num : (0 : Real) ≤ 8)]
    _ ≤ 8 * d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + 4 / (eps * t) := by
      have hcard : (S.card : Real) ≤ d := by
        exact_mod_cast (by simpa using S.card_le_univ : S.card ≤ d)
      have hsumS : ∑ x ∈ S, cellMass P x ≤ 1 := by
        rw [← hsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [S])
          (fun _ _ _ ↦ hp0 _)
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcoef0 : 0 ≤ 8 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) := by positivity
      have hden : 0 < eps * Real.exp 1 * t := by positivity
      rw [← Finset.mul_sum]
      have hsumdiv : (∑ x ∈ S,
          cellMass P x / (2 * eps * Real.exp 1 * t)) =
          (∑ x ∈ S, cellMass P x) / (2 * eps * Real.exp 1 * t) := by
        rw [Finset.sum_div]
      have hrewrite : 8 * (∑ x ∈ S,
          cellMass P x / (2 * eps * Real.exp 1 * t)) =
          (8 / (2 * eps * Real.exp 1 * t)) *
            (∑ x ∈ S, cellMass P x) := by
        rw [hsumdiv]
        ring
      rw [hrewrite]
      have hfirst := mul_le_mul_of_nonneg_right hcard hcoef0
      have hsecond := mul_le_mul_of_nonneg_left hsumS
        (show 0 ≤ 8 / (2 * eps * Real.exp 1 * t) by positivity)
      have heone : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      have hlast : 8 / (2 * eps * Real.exp 1 * t) ≤ 4 / (eps * t) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      have hfirst' : (S.card : Real) *
          (8 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4)) ≤
          8 * d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) := by
        calc
          _ ≤ (d : Real) * (8 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4)) := hfirst
          _ = _ := by ring
      have hsecond' : (8 / (2 * eps * Real.exp 1 * t)) *
          (∑ x ∈ S, cellMass P x) ≤ 4 / (eps * t) :=
        hsecond.trans (by simpa using hlast)
      linarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
