module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridCellAnalysis

/-! Aggregate-ready second-moment bound for a light cell. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

private lemma integral_hybridLightPools_sq_le_of_moment {d : Nat}
    (P : DiscreteLaw d) (x : Fin d) {u t B R : Real} {L : Nat}
    (hu : 0 < u) (hR : 0 ≤ R)
    (hmoment : ∀ a : Bool, factorialLiftSecondMoment a L B t
      (armMass P x false) (armMass P x true) ≤ R) :
    (∫ W, hybridLightPools L B u t W ^ 2 ∂
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))) ≤
      4 * (cellMass P x / u + cellMass P x ^ 2) * R := by
  let muS : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (u * markedMass P x a))
  let muK : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (t * armMass P x a))
  let armStat (a : Bool) (W : (Bool → Nat) × (Bool → Nat)) :=
    (W.1 a : Real) / u * factorialLift a L B t (W.2 false) (W.2 true)
  have hp0 : 0 ≤ cellMass P x := (cellMass_mem_unitInterval P x).1
  have hs0 : 0 ≤ armMass P x false := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x false y).1
  have hs1 : 0 ≤ armMass P x true := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x true y).1
  have hsum : armMass P x false + armMass P x true = cellMass P x := by
    simp [armMass, cellMass]
    ring
  have hm (a : Bool) : 0 ≤ markedMass P x a :=
    (jointMass_mem_unitInterval P x a true).1
  have hmp (a : Bool) : MeasurePreserving
      (fun W : (Bool → Nat) × (Bool → Nat) ↦
        (W.1 a, (W.2 false, W.2 true)))
      ((Measure.pi muS).prod (Measure.pi muK))
      ((muS a).prod ((muK false).prod (muK true))) :=
    (measurePreserving_eval muS a).prod (boolPair_measurePreserving muK)
  have hArmSq (a : Bool) :
      (∫ W, armStat a W ^ 2 ∂(Measure.pi muS).prod (Measure.pi muK)) ≤
        (markedMass P x a / u + markedMass P x a ^ 2) * R := by
    calc
      _ = ∫ Z, lightArmCell a L B u t Z ^ 2 ∂
          (muS a).prod ((muK false).prod (muK true)) := by
        rw [← (hmp a).map_eq]
        exact (integral_map (hmp a).aemeasurable
          (measurable_of_countable
            (fun Z ↦ lightArmCell a L B u t Z ^ 2)).aestronglyMeasurable).symm
      _ = (markedMass P x a / u + markedMass P x a ^ 2) *
          factorialLiftSecondMoment a L B t
            (armMass P x false) (armMass P x true) := by
        exact integral_lightArmCell_sq a L hu (hm a)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmoment a)
        (add_nonneg (div_nonneg (hm a) hu.le) (sq_nonneg _))
  have hmarked_le (a : Bool) : markedMass P x a ≤ cellMass P x := by
    calc
      markedMass P x a ≤ armMass P x a := by
        simp [markedMass, armMass]
        exact (jointMass_mem_unitInterval P x a false).1
      _ ≤ cellMass P x := by
        cases a <;> rw [← hsum] <;> linarith
  have hcommon (a : Bool) :
      markedMass P x a / u + markedMass P x a ^ 2 ≤
        cellMass P x / u + cellMass P x ^ 2 := by
    have hma := hm a
    have hle := hmarked_le a
    have hdiv := div_le_div_of_nonneg_right hle hu.le
    nlinarith [sq_nonneg (cellMass P x - markedMass P x a)]
  have hArmInt (a : Bool) : Integrable (fun W ↦ armStat a W ^ 2)
      ((Measure.pi muS).prod (Measure.pi muK)) := by
    have hS := ((memLp_descFactorial_poisson
      (Real.toNNReal (u * markedMass P x a)) 1).const_mul u⁻¹).comp_measurePreserving
        (measurePreserving_eval muS a)
    have hK := (factorialLift_memLp a L B t (armMass P x false)
      (armMass P x true)).comp_measurePreserving (boolPair_measurePreserving muK)
    have hprod := Causalean.Mathlib.Probability.memLp_mul_prod_two hS hK
    apply hprod.integrable_sq.congr
    filter_upwards [] with W
    dsimp [armStat]
    simp only [boolPair, Nat.descFactorial_one, Function.comp_apply]
    ring
  have hlightInt := (hybridLightPools_memLp P u t B L x).integrable_sq
  calc
    _ ≤ ∫ W, (2 * armStat true W ^ 2 + 2 * armStat false W ^ 2) ∂
        (Measure.pi muS).prod (Measure.pi muK) := by
      apply integral_mono hlightInt ((hArmInt true).const_mul 2 |>.add
        ((hArmInt false).const_mul 2))
      intro W
      dsimp [hybridLightPools, armStat]
      exact sq_sub_le_two_sq_add_two_sq _ _
    _ = 2 * (∫ W, armStat true W ^ 2 ∂(Measure.pi muS).prod (Measure.pi muK)) +
        2 * (∫ W, armStat false W ^ 2 ∂(Measure.pi muS).prod (Measure.pi muK)) := by
      rw [integral_add ((hArmInt true).const_mul 2) ((hArmInt false).const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * ((cellMass P x / u + cellMass P x ^ 2) * R) +
        2 * ((cellMass P x / u + cellMass P x ^ 2) * R) := by
      gcongr
      · exact (hArmSq true).trans (mul_le_mul_of_nonneg_right (hcommon true) hR)
      · exact (hArmSq false).trans (mul_le_mul_of_nonneg_right (hcommon false) hR)
    _ = _ := by ring

/-- C28 specialized to a cell below the bandwidth.  [the stated conditions](hyp:hu,ht,hB,hL,htB,hcell) [the stated conclusion](goal). -/
lemma integral_hybridLightPools_sq_le_of_cellMass_le {d : Nat}
    (P : DiscreteLaw d) (x : Fin d) {u t B : Real} {L : Nat}
    (hu : 0 < u) (ht : 0 < t) (hB : 0 < B) (hL : 2 ≤ L)
    (htB : (L : Real) ≤ t * B) (hcell : cellMass P x ≤ B) :
    (∫ W, hybridLightPools L B u t W ^ 2 ∂
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))) ≤
      4 * (cellMass P x / u + cellMass P x ^ 2) * starA ^ L := by
  have hs0 : 0 ≤ armMass P x false := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x false y).1
  have hs1 : 0 ≤ armMass P x true := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x true y).1
  have hsum : armMass P x false + armMass P x true = cellMass P x := by
    simp [armMass, cellMass]
    ring
  apply integral_hybridLightPools_sq_le_of_moment P x hu (by positivity)
  intro a
  have h := (explicit_chebyshev_calibration L hL).2.2.1 a t B
    (armMass P x false) (armMass P x true) ht hB hs0 hs1 htB
  have hpB : armMass P x false + armMass P x true ≤ B := by
    rw [hsum]
    exact hcell
  simpa [starA] using h.2 hpB

/-- C21 in the exact separated-pool notation.  [the stated conditions](hyp:hu,ht,hB,hL,htB) [the stated conclusion](goal). -/
lemma integral_hybridLightPools_sq_le {d : Nat}
    (P : DiscreteLaw d) (x : Fin d) {u t B : Real} {L : Nat}
    (hu : 0 < u) (ht : 0 < t) (hB : 0 < B) (hL : 2 ≤ L)
    (htB : (L : Real) ≤ t * B) :
    (∫ W, hybridLightPools L B u t W ^ 2 ∂
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))) ≤
      4 * (cellMass P x / u + cellMass P x ^ 2) *
        (starA ^ L * (1 + cellMass P x / B) ^ (2 * L)) := by
  have hs0 : 0 ≤ armMass P x false := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x false y).1
  have hs1 : 0 ≤ armMass P x true := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x true y).1
  have hsum : armMass P x false + armMass P x true = cellMass P x := by
    simp [armMass, cellMass]
    ring
  apply integral_hybridLightPools_sq_le_of_moment P x hu
    (mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg (add_nonneg zero_le_one (div_nonneg
        (cellMass_mem_unitInterval P x).1 hB.le)) _))
  intro a
  have h := (explicit_chebyshev_calibration L hL).2.2.1 a t B
    (armMass P x false) (armMass P x true) ht hB hs0 hs1 htB
  simpa [starA, hsum] using h.1

/-- Summed C29 envelope over all cells whose mass is at most the bandwidth.  [the stated conditions](hyp:hu,ht,hB,hL,htB) [the stated conclusion](goal). -/
lemma sum_light_secondMoment_le {d : Nat} (P : DiscreteLaw d)
    {u t B : Real} {L : Nat}
    (hu : 0 < u) (ht : 0 < t) (hB : 0 < B) (hL : 2 ≤ L)
    (htB : (L : Real) ≤ t * B) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin d ↦ cellMass P x ≤ B),
      ∫ W, hybridLightPools L B u t W ^ 2 ∂
        ((Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
         (Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (t * armMass P x a))))) ≤
      4 * starA ^ L *
        (min 1 ((d : Real) * B) / u + (d : Real) * B ^ 2) := by
  classical
  let S : Finset (Fin d) := Finset.univ.filter fun x ↦ cellMass P x ≤ B
  have hp0 (x : Fin d) : 0 ≤ cellMass P x := (cellMass_mem_unitInterval P x).1
  have hsumAll : ∑ x : Fin d, cellMass P x = 1 :=
    cellMass_sum_eq_one_annotation P
  have hsum0 : 0 ≤ ∑ x ∈ S, cellMass P x :=
    Finset.sum_nonneg fun x _ ↦ hp0 x
  have hsum1 : ∑ x ∈ S, cellMass P x ≤ 1 := by
    rw [← hsumAll]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [S])
      (fun _ _ _ ↦ hp0 _)
  have hsumB : ∑ x ∈ S, cellMass P x ≤ (d : Real) * B := by
    calc
      _ ≤ ∑ _x ∈ S, B := Finset.sum_le_sum fun x hx ↦ by
        simpa [S] using (Finset.mem_filter.mp hx).2
      _ = (S.card : Real) * B := by simp
      _ ≤ (d : Real) * B := by
        exact mul_le_mul_of_nonneg_right (by
          exact_mod_cast (by simpa using S.card_le_univ : S.card ≤ d)) hB.le
  have hsumMin : ∑ x ∈ S, cellMass P x ≤ min 1 ((d : Real) * B) :=
    le_min hsum1 hsumB
  have hsq : ∑ x ∈ S, cellMass P x ^ 2 ≤ (d : Real) * B ^ 2 := by
    calc
      _ ≤ ∑ _x ∈ S, B ^ 2 := Finset.sum_le_sum fun x hx ↦ by
        have hle : cellMass P x ≤ B := by simpa [S] using (Finset.mem_filter.mp hx).2
        nlinarith [mul_nonneg (sub_nonneg.mpr hle)
          (add_nonneg hB.le (hp0 x))]
      _ = (S.card : Real) * B ^ 2 := by simp
      _ ≤ (d : Real) * B ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by
          exact_mod_cast (by simpa using S.card_le_univ : S.card ≤ d)) (sq_nonneg B)
  have hpoint (x : Fin d) (hx : x ∈ S) :
      (∫ W, hybridLightPools L B u t W ^ 2 ∂
        ((Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
         (Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (t * armMass P x a))))) ≤
        4 * (cellMass P x / u + cellMass P x ^ 2) * starA ^ L := by
    apply integral_hybridLightPools_sq_le_of_cellMass_le P x hu ht hB hL htB
    simpa [S] using (Finset.mem_filter.mp hx).2
  change (∑ x ∈ S, _) ≤ _
  calc
    _ ≤ ∑ x ∈ S, 4 * (cellMass P x / u + cellMass P x ^ 2) * starA ^ L :=
      Finset.sum_le_sum fun x hx ↦ hpoint x hx
    _ = 4 * starA ^ L *
        ((∑ x ∈ S, cellMass P x) / u + ∑ x ∈ S, cellMass P x ^ 2) := by
      have hdivsum : (∑ x ∈ S, cellMass P x / u) =
          (∑ x ∈ S, cellMass P x) / u := by rw [Finset.sum_div]
      rw [← hdivsum, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ 4 * starA ^ L *
        (min 1 ((d : Real) * B) / u + (d : Real) * B ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (div_le_div_of_nonneg_right hsumMin hu.le) hsq

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
