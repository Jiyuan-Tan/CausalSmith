module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridMeanAssembly
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyAggregate

/-! Algebraic assembly of the calibrated hybrid variance. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- The branch-mean part of C27 on heavy cells is negligible.  [the stated conditions](hyp:hP,heps,hn,hcal) [the stated conclusion](goal). -/
lemma sum_heavy_branchMean_sq_le {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P)
    {n m : Nat} (heps : 0 < eps) (hn : 1 ≤ n)
    (hcal : calibrationPredicate n m eps) :
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    let muE := fun x : Fin d ↦
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))
    (∑ x ∈ Finset.univ.filter
        (fun x : Fin d ↦ Bscale n m eps < cellMass P x),
      hybridPilotLightProbability P tp (k0 n m eps) x *
        hybridPilotHeavyProbability P tp (k0 n m eps) x *
          ((∫ W, hybridLightPools (Ldeg n) (Bscale n m eps) u t W ∂muE x) -
            ∫ W, hybridHeavyPools u W ∂muE x) ^ 2) ≤
      282 * ((n : Real) ^ 12)⁻¹ := by
  dsimp only
  classical
  let S : Finset (Fin d) := Finset.univ.filter
    (fun x ↦ Bscale n m eps < cellMass P x)
  let u : Real := (blockSizes n m).M0 / 8
  let tp : Real := ((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  let EL := fun x : Fin d ↦ ∫ W,
    hybridLightPools (Ldeg n) (Bscale n m eps) u t W ∂
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))
  let EH := fun x : Fin d ↦ ∫ W, hybridHeavyPools u W ∂
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))
  let pi := fun x : Fin d ↦ hybridPilotLightProbability P tp (k0 n m eps) x
  let eta := fun x : Fin d ↦ hybridPilotHeavyProbability P tp (k0 n m eps) x
  obtain ⟨hu, _htp, ht, _hB⟩ := calibrationPredicate_positive_parameters hcal
  have hp0 (x : Fin d) := (cellMass_mem_unitInterval P x).1
  have hsum : ∑ x : Fin d, cellMass P x = 1 := cellMass_sum_eq_one_annotation P
  have hsumS : ∑ x ∈ S, cellMass P x ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [S])
      (fun _ _ _ ↦ hp0 _)
  have hpi0 (x : Fin d) : 0 ≤ pi x := measureReal_nonneg
  have heta0 (x : Fin d) : 0 ≤ eta x := measureReal_nonneg
  have hetale (x : Fin d) : eta x ≤ 1 := measureReal_le_one
  have hpoint (x : Fin d) (hx : x ∈ S) :
      pi x * eta x * (EL x - EH x) ^ 2 ≤
        2 * pi x * (EL x) ^ 2 +
          18 * cellMass P x * ((n : Real) ^ 12)⁻¹ := by
    have hp : Bscale n m eps < cellMass P x := by
      simpa [S] using (Finset.mem_filter.mp hx).2
    have hpile := calibrated_heavy_cell_pilot_le P hn hcal x hp
    have hEH := abs_integral_hybridHeavyPools_le_three_cellMass
      P hP x hu ht heps
    have hEH' : |EH x| ≤ 3 * cellMass P x := by
      simpa [EH, u, t] using hEH
    have hp1 := (cellMass_mem_unitInterval P x).2
    have hsq : (EL x - EH x) ^ 2 ≤ 2 * (EL x) ^ 2 + 2 * (EH x) ^ 2 :=
      sq_sub_le_two_sq_add_two_sq _ _
    have hEHsq : (EH x) ^ 2 ≤ 9 * cellMass P x ^ 2 := by
      rw [← sq_abs]
      nlinarith [sq_nonneg (3 * cellMass P x - |EH x|), abs_nonneg (EH x)]
    have hpi : pi x ≤ ((n : Real) ^ 12)⁻¹ := by
      simpa [pi, tp] using hpile
    have hinv0 : 0 ≤ ((n : Real) ^ 12)⁻¹ := by positivity
    calc
      _ = eta x * (pi x * (EL x - EH x) ^ 2) := by ring
      _ ≤ pi x * (EL x - EH x) ^ 2 :=
        mul_le_of_le_one_left (mul_nonneg (hpi0 x) (sq_nonneg _)) (hetale x)
      _ ≤ pi x * (2 * (EL x) ^ 2 + 2 * (EH x) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (hpi0 x)
      _ = 2 * pi x * (EL x) ^ 2 + 2 * pi x * (EH x) ^ 2 := by ring
      _ ≤ 2 * pi x * (EL x) ^ 2 +
          18 * cellMass P x * ((n : Real) ^ 12)⁻¹ := by
        have htail1 : 2 * pi x * (EH x) ^ 2 ≤
            18 * pi x * cellMass P x ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hEHsq
            (mul_nonneg (by norm_num : (0 : Real) ≤ 2) (hpi0 x))]
        have htail2 : 18 * pi x * cellMass P x ^ 2 ≤
            18 * ((n : Real) ^ 12)⁻¹ * cellMass P x ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpi (by norm_num)) (sq_nonneg _)
        have hpSq : cellMass P x ^ 2 ≤ cellMass P x := by
          nlinarith [mul_nonneg (hp0 x) (sub_nonneg.mpr hp1)]
        have htail3 := mul_le_mul_of_nonneg_right hpSq
          (mul_nonneg (by norm_num : (0 : Real) ≤ 18) hinv0)
        nlinarith
  change (∑ x ∈ S, pi x * eta x * (EL x - EH x) ^ 2) ≤ _
  calc
    _ ≤ ∑ x ∈ S, (2 * pi x * (EL x) ^ 2 +
        18 * cellMass P x * ((n : Real) ^ 12)⁻¹) :=
      Finset.sum_le_sum fun x hx ↦ hpoint x hx
    _ = 2 * (∑ x ∈ S, pi x * (EL x) ^ 2) +
        18 * (∑ x ∈ S, cellMass P x) * ((n : Real) ^ 12)⁻¹ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      · rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ 2 * (132 * ((n : Real) ^ 12)⁻¹) +
        18 * 1 * ((n : Real) ^ 12)⁻¹ := by
      have hlight := sum_heavy_light_secondMoment_le P heps hn hcal
      have hlight' : (∑ x ∈ S, pi x * (EL x) ^ 2) ≤
          132 * ((n : Real) ^ 12)⁻¹ := by
        have hmeanSq (x : Fin d) : (EL x) ^ 2 ≤
            ∫ W, hybridLightPools (Ldeg n) (Bscale n m eps) u t W ^ 2 ∂
              ((Measure.pi fun a : Bool ↦
                poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
               (Measure.pi fun a : Bool ↦
                poissonMeasure (Real.toNNReal (t * armMass P x a)))) := by
          have hv := variance_nonneg (hybridLightPools (Ldeg n)
            (Bscale n m eps) u t)
            ((Measure.pi fun a : Bool ↦
              poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
             (Measure.pi fun a : Bool ↦
              poissonMeasure (Real.toNNReal (t * armMass P x a))))
          rw [variance_eq_sub (hybridLightPools_memLp P u t
            (Bscale n m eps) (Ldeg n) x)] at hv
          exact sub_nonneg.mp hv
        calc
          _ ≤ ∑ x ∈ S, pi x *
              (∫ W, hybridLightPools (Ldeg n) (Bscale n m eps) u t W ^ 2 ∂
                ((Measure.pi fun a : Bool ↦
                  poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
                 (Measure.pi fun a : Bool ↦
                  poissonMeasure (Real.toNNReal (t * armMass P x a))))) :=
            Finset.sum_le_sum fun x _ ↦
              mul_le_mul_of_nonneg_left (hmeanSq x) (hpi0 x)
          _ ≤ _ := by simpa [S, pi, u, tp, t] using hlight
      exact add_le_add (mul_le_mul_of_nonneg_left hlight' (by norm_num))
        (by
          have h := mul_le_mul_of_nonneg_left hsumS (by norm_num : (0 : Real) ≤ 18)
          exact mul_le_mul_of_nonneg_right h (by positivity))
    _ = _ := by ring

/-- C27--C32, retaining the deterministic quantities used in the final absorption.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma calibrated_hybrid_variance_le {eps : Real} (heps : 0 < eps)
    (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat) (P : DiscreteLaw d), 1 ≤ n →
      ModelClass d eps P → calibrationPredicate n m eps →
      let bs := blockSizes n m
      let u : Real := bs.M0 / 8
      let tp : Real := (bs.np + bs.mp : Nat) / 8
      let t : Real := (bs.nf + bs.mf : Nat) / 8
      Var[(fun K : HybridPoissonCounts d ↦ ∑ x : Fin d,
          hybridSelectedCell (k0 n m eps) (Ldeg n) (Bscale n m eps) u t (K x));
        hybridPoissonCountLaw P u tp t] ≤
        4 * starA ^ Ldeg n *
          (min 1 ((d : Real) * Bscale n m eps) / u +
            (d : Real) * Bscale n m eps ^ 2) +
        C * (u⁻¹ + t⁻¹) +
        8 * d * Bscale n m eps ^ 2 /
          (eps ^ 2 * (Ldeg n : Real) ^ 4) + 4 / (eps * t) +
        414 * ((n : Real) ^ 12)⁻¹ := by
  obtain ⟨C, hC, hheavy⟩ := pilotHeavy_variance_bound_exists heps heps2
  refine ⟨C, hC, ?_⟩
  intro n m d P hn hP hcal
  dsimp only
  classical
  let u : Real := (blockSizes n m).M0 / 8
  let tp : Real := ((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  let B := Bscale n m eps
  let L := Ldeg n
  let muE := fun x : Fin d ↦
    ((Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
     (Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (t * armMass P x a))))
  let pi := fun x : Fin d ↦ hybridPilotLightProbability P tp (k0 n m eps) x
  let eta := fun x : Fin d ↦ hybridPilotHeavyProbability P tp (k0 n m eps) x
  let EL := fun x : Fin d ↦ ∫ W, hybridLightPools L B u t W ∂muE x
  let EH := fun x : Fin d ↦ ∫ W, hybridHeavyPools u W ∂muE x
  let VL := fun x : Fin d ↦ Var[hybridLightPools L B u t; muE x]
  let VH := fun x : Fin d ↦ Var[hybridHeavyPools u; muE x]
  let S : Finset (Fin d) := Finset.univ.filter fun x ↦ cellMass P x ≤ B
  obtain ⟨hu, _htp, ht, hB⟩ := calibrationPredicate_positive_parameters hcal
  have hL : 2 ≤ L := Ldeg_ge_two n
  have hcal' := hcal
  simp only [calibrationPredicate] at hcal'
  have htB : (L : Real) ≤ t * B := by
    simpa [L, t, B] using hcal'.2.2.2.2.2.2.2.2.2.2.2.1
  have hpi0 (x : Fin d) : 0 ≤ pi x := measureReal_nonneg
  have hpile (x : Fin d) : pi x ≤ 1 := measureReal_le_one
  have heta0 (x : Fin d) : 0 ≤ eta x := measureReal_nonneg
  have heta (x : Fin d) : eta x = 1 - pi x := by
    exact hybridPilotHeavyProbability_eq_one_sub_light P tp (k0 n m eps) x
  have hVL (x : Fin d) : VL x ≤ ∫ W, hybridLightPools L B u t W ^ 2 ∂muE x := by
    exact variance_le_expectation_sq
      (hybridLightPools_memLp P u t B L x).aestronglyMeasurable
  have hcell (x : Fin d) :
      Var[hybridSelectedCell (k0 n m eps) L B u t;
        Measure.pi fun arm : Bool ↦
          (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
            ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
              (poissonMeasure (Real.toNNReal (t * armMass P x arm))))] =
        pi x * VL x + eta x * VH x + pi x * eta x * (EL x - EH x) ^ 2 := by
    rw [variance_hybridSelectedCell_exact]
    change pi x * VL x + (1 - pi x) * VH x +
      pi x * (1 - pi x) * (EL x - EH x) ^ 2 = _
    rw [← heta x]
  have hlightVar : (∑ x : Fin d, pi x * VL x) ≤
      4 * starA ^ L * (min 1 ((d : Real) * B) / u + (d : Real) * B ^ 2) +
        132 * ((n : Real) ^ 12)⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Fin d ↦ cellMass P x ≤ B) (fun x ↦ pi x * VL x)]
    have hSc : Finset.univ.filter (fun x : Fin d ↦ ¬ cellMass P x ≤ B) =
        Finset.univ.filter (fun x : Fin d ↦ B < cellMass P x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_le
    rw [hSc]
    apply add_le_add
    · calc
        _ ≤ ∑ x ∈ S, ∫ W, hybridLightPools L B u t W ^ 2 ∂muE x := by
          apply Finset.sum_le_sum
          intro x hx
          exact (mul_le_of_le_one_left (variance_nonneg _ _) (hpile x)).trans
            (hVL x)
        _ ≤ _ := by
          simpa [S, L, B, u, t, muE] using
            sum_light_secondMoment_le P hu ht hB hL htB
    · calc
        _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin d ↦ B < cellMass P x),
            pi x * (∫ W, hybridLightPools L B u t W ^ 2 ∂muE x) := by
          apply Finset.sum_le_sum
          intro x hx
          have hx' : x ∈ Finset.univ.filter (fun x : Fin d ↦ B < cellMass P x) := by
            simpa [S] using hx
          exact mul_le_mul_of_nonneg_left (hVL x) (hpi0 x)
        _ ≤ _ := by
          simpa [pi, L, B, u, tp, t, muE] using
            sum_heavy_light_secondMoment_le P heps hn hcal
  have hheavyVar : (∑ x : Fin d, eta x * VH x) ≤ C * (u⁻¹ + t⁻¹) := by
    simpa [eta, VH, u, tp, t, muE] using hheavy d P hP hu ht (k0 n m eps)
  have hbranch : (∑ x : Fin d, pi x * eta x * (EL x - EH x) ^ 2) ≤
      8 * d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + 4 / (eps * t) +
        282 * ((n : Real) ^ 12)⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Fin d ↦ cellMass P x ≤ B)
      (fun x ↦ pi x * eta x * (EL x - EH x) ^ 2)]
    have hSc : Finset.univ.filter (fun x : Fin d ↦ ¬ cellMass P x ≤ B) =
        Finset.univ.filter (fun x : Fin d ↦ B < cellMass P x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_le
    rw [hSc]
    calc
      _ ≤ (8 * d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + 4 / (eps * t)) +
          282 * ((n : Real) ^ 12)⁻¹ := add_le_add (by
        calc
          _ ≤ ∑ x ∈ S, (EL x - EH x) ^ 2 := by
            apply Finset.sum_le_sum
            intro x _
            have hprod : pi x * eta x ≤ 1 := by
              calc
                _ ≤ pi x * 1 := mul_le_mul_of_nonneg_left measureReal_le_one (hpi0 x)
                _ ≤ 1 := by simpa using hpile x
            exact mul_le_of_le_one_left (sq_nonneg _) hprod
          _ ≤ _ := by
            simpa [S, EL, EH, L, B, u, t, muE] using
              sum_light_branchMean_sq_le P hP hu ht heps hB hL) (by
        simpa [pi, eta, EL, EH, L, B, u, tp, t, muE] using
          sum_heavy_branchMean_sq_le P hP heps hn hcal)
      _ = _ := by ring
  change Var[(fun K : HybridPoissonCounts d ↦ ∑ x : Fin d,
      hybridSelectedCell (k0 n m eps) L B u t (K x));
      hybridPoissonCountLaw P u tp t] ≤
    4 * starA ^ L * (min 1 ((d : Real) * B) / u + (d : Real) * B ^ 2) +
      C * (u⁻¹ + t⁻¹) +
      8 * d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + 4 / (eps * t) +
      414 * ((n : Real) ^ 12)⁻¹
  calc
    _ = ∑ x : Fin d, (pi x * VL x + eta x * VH x +
        pi x * eta x * (EL x - EH x) ^ 2) := by
      rw [variance_sum_hybridSelectedCell]
      exact Finset.sum_congr rfl (fun x _ ↦ hcell x)
    _ = (∑ x : Fin d, pi x * VL x) + (∑ x : Fin d, eta x * VH x) +
        ∑ x : Fin d, pi x * eta x * (EL x - EH x) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
