module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridBranchMeanAggregate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyLightTail

/-! Algebraic assembly of the calibrated hybrid mean. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
/-- [the stated conditions](hyp:P,u,tp,t,B,threshold,L,x) defines [the specified object](goal). -/

noncomputable def hybridSelectedCellMean {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) (x : Fin d) : Real :=
  ∫ Z, hybridSelectedCell threshold L B u t Z ∂
    (Measure.pi fun arm : Bool ↦
      (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
        ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
          (poissonMeasure (Real.toNNReal (t * armMass P x arm)))))
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma hybridSelectedCellMean_eq_mixture {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) (x : Fin d) :
    let muE :=
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))
    hybridSelectedCellMean P u tp t B threshold L x =
      hybridPilotLightProbability P tp threshold x *
          (∫ W, hybridLightPools L B u t W ∂muE) +
        hybridPilotHeavyProbability P tp threshold x *
          (∫ W, hybridHeavyPools u W ∂muE) := by
  dsimp only
  rw [hybridSelectedCellMean, integral_hybridSelectedCell_exact]
  rw [hybridPilotHeavyProbability_eq_one_sub_light]
  rfl

/-- C26 with explicit constants.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma calibrated_hybrid_mean_bias_le {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∀ (n m d : Nat) (P : DiscreteLaw d), 1 ≤ n →
      ModelClass d eps P → calibrationPredicate n m eps →
      let bs := blockSizes n m
      let u : Real := bs.M0 / 8
      let tp : Real := (bs.np + bs.mp : Nat) / 8
      let t : Real := (bs.nf + bs.mf : Nat) / 8
      |(∑ x : Fin d, hybridSelectedCellMean P u tp t (Bscale n m eps)
          (k0 n m eps) (Ldeg n) x) - ateFunctional P| ≤
        2 * d * Bscale n m eps / (eps * (Ldeg n : Real) ^ 2) +
          6 * ((n : Real) ^ 12)⁻¹ := by
  intro n m d P hn hP hcal
  dsimp only
  classical
  let u : Real := (blockSizes n m).M0 / 8
  let tp : Real := ((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  let B := Bscale n m eps
  let L := Ldeg n
  let invn := ((n : Real) ^ 12)⁻¹
  let theta := fun x : Fin d ↦ cellMass P x *
    (outcomeMean P true x - outcomeMean P false x)
  let EL := fun x : Fin d ↦ ∫ W, hybridLightPools L B u t W ∂
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
  obtain ⟨hu, _htp, ht, hB⟩ := calibrationPredicate_positive_parameters hcal
  have hL : 2 ≤ L := Ldeg_ge_two n
  have hp0 (x : Fin d) := (cellMass_mem_unitInterval P x).1
  have hsum : ∑ x : Fin d, cellMass P x = 1 := cellMass_sum_eq_one_annotation P
  have hmix (x : Fin d) : hybridSelectedCellMean P u tp t B (k0 n m eps) L x =
      pi x * EL x + eta x * EH x :=
    hybridSelectedCellMean_eq_mixture P u tp t B (k0 n m eps) L x
  have heta (x : Fin d) : eta x = 1 - pi x :=
    hybridPilotHeavyProbability_eq_one_sub_light P tp (k0 n m eps) x
  have hpi0 (x : Fin d) : 0 ≤ pi x := measureReal_nonneg
  have hpile (x : Fin d) : pi x ≤ 1 := measureReal_le_one
  have heta0 (x : Fin d) : 0 ≤ eta x := measureReal_nonneg
  have hetale (x : Fin d) : eta x ≤ 1 := measureReal_le_one
  have htheta (x : Fin d) : |theta x| ≤ cellMass P x := by
    dsimp [theta]
    rw [abs_mul, abs_of_nonneg (hp0 x)]
    apply mul_le_of_le_one_right (hp0 x)
    rw [abs_le]
    rcases outcomeMean_mem_unitInterval P true x with ⟨h10, h11⟩
    rcases outcomeMean_mem_unitInterval P false x with ⟨h00, h01⟩
    constructor <;> nlinarith
  have hpoint (x : Fin d) :
      |hybridSelectedCellMean P u tp t B (k0 n m eps) L x - theta x| ≤
        if cellMass P x ≤ B then
          2 * B / (eps * (L : Real) ^ 2) + 2 * cellMass P x * invn
        else 4 * cellMass P x * invn := by
    rw [hmix]
    by_cases hx : cellMass P x ≤ B
    · rw [if_pos hx]
      have hlight : |EL x - theta x| ≤ 2 * B / (eps * (L : Real) ^ 2) := by
        dsimp [EL, theta, B, L, u, t]
        rw [integral_hybridLightPools P hu ht hB (Ldeg n) x]
        exact light_exact_mean_bias_le P hP x heps hB hL hx
      have hheavy := integral_hybridHeavyPools_bias_le P hP x hu ht heps
      have hwrong := calibrated_light_cell_heavy_probability_mul_exp_le
        P heps heps2 hcal x
      have hid : pi x * EL x + eta x * EH x - theta x =
          pi x * (EL x - theta x) + eta x * (EH x - theta x) := by
        rw [heta]
        ring
      rw [hid]
      calc
        |_ + _| ≤ |pi x * (EL x - theta x)| +
            |eta x * (EH x - theta x)| := abs_add_le _ _
        _ ≤ pi x * |EL x - theta x| + eta x * |EH x - theta x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hpi0 x), abs_of_nonneg (heta0 x)]
        _ ≤ 2 * B / (eps * (L : Real) ^ 2) +
            2 * cellMass P x * invn := by
          have hfirst := mul_le_mul (hpile x) hlight (abs_nonneg _) (by positivity)
          have hsecond := mul_le_mul_of_nonneg_left hheavy (heta0 x)
          dsimp [eta, invn, t] at hwrong
          dsimp [eta, t] at hsecond
          nlinarith [mul_le_mul_of_nonneg_left hwrong
            (show 0 ≤ 2 * cellMass P x by exact mul_nonneg (by norm_num) (hp0 x))]
    · rw [if_neg hx]
      have hp : B < cellMass P x := lt_of_not_ge hx
      have hmean := calibrated_heavy_cell_light_mean_le P heps hn hcal x hp
      have hpip := calibrated_heavy_cell_pilot_le P hn hcal x hp
      have hheavy := integral_hybridHeavyPools_bias_le P hP x hu ht heps
      have hexp := calibrated_heavy_cell_bias_exp_le P heps heps2 hn hcal x hp
      have hid : pi x * EL x + eta x * EH x - theta x =
          pi x * EL x - pi x * theta x + eta x * (EH x - theta x) := by
        rw [heta]
        ring
      rw [hid]
      calc
        |_ + _| ≤ |pi x * EL x - pi x * theta x| +
            |eta x * (EH x - theta x)| := abs_add_le _ _
        _ ≤ pi x * |EL x| + pi x * |theta x| +
            eta x * |EH x - theta x| := by
          calc
            _ ≤ (|pi x * EL x| + |pi x * theta x|) +
                |eta x * (EH x - theta x)| :=
              add_le_add (abs_sub _ _) le_rfl
            _ = _ := by
              rw [abs_mul (pi x) (EL x), abs_mul (pi x) (theta x),
                abs_mul (eta x) (EH x - theta x),
                abs_of_nonneg (hpi0 x), abs_of_nonneg (heta0 x)]
        _ ≤ 4 * cellMass P x * invn := by
          have hinv : 0 ≤ invn := by dsimp [invn]; positivity
          have hthetaTerm : pi x * |theta x| ≤ cellMass P x * invn := by
            calc
              _ = |theta x| * pi x := by ring
              _ ≤ |theta x| * invn :=
                mul_le_mul_of_nonneg_left (by simpa [pi, tp, invn] using hpip)
                  (abs_nonneg _)
              _ ≤ cellMass P x * invn :=
                mul_le_mul_of_nonneg_right (htheta x) hinv
          have hheavyTerm : eta x * |EH x - theta x| ≤
              2 * cellMass P x * invn := by
            calc
              _ ≤ eta x * (2 * cellMass P x *
                  Real.exp (-eps * t * cellMass P x)) := by
                exact mul_le_mul_of_nonneg_left
                  (by simpa [EH, theta, u, t] using hheavy) (heta0 x)
              _ ≤ 1 * (2 * cellMass P x *
                  Real.exp (-eps * t * cellMass P x)) :=
                mul_le_mul_of_nonneg_right (hetale x)
                  (mul_nonneg (mul_nonneg (by norm_num) (hp0 x))
                    (Real.exp_nonneg _))
              _ ≤ 2 * cellMass P x * invn := by
                have := mul_le_mul_of_nonneg_left
                  (by simpa [t, invn] using hexp)
                  (show 0 ≤ 2 * cellMass P x by
                    exact mul_nonneg (by norm_num) (hp0 x))
                nlinarith
          have hmean' : pi x * |EL x| ≤ cellMass P x * invn := by
            simpa [pi, EL, u, tp, t, invn] using hmean
          linarith
  rw [ateFunctional, ← Finset.sum_sub_distrib]
  calc
    |∑ x, (hybridSelectedCellMean P u tp t B (k0 n m eps) L x - theta x)| ≤
        ∑ x, |hybridSelectedCellMean P u tp t B (k0 n m eps) L x - theta x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, (if cellMass P x ≤ B then
          2 * B / (eps * (L : Real) ^ 2) + 2 * cellMass P x * invn
        else 4 * cellMass P x * invn) := Finset.sum_le_sum fun x _ ↦ hpoint x
    _ ≤ 2 * d * B / (eps * (L : Real) ^ 2) + 6 * invn := by
      have hbase0 : 0 ≤ 2 * B / (eps * (L : Real) ^ 2) := by positivity
      calc
        _ ≤ ∑ x, (2 * B / (eps * (L : Real) ^ 2) +
            4 * cellMass P x * invn) := Finset.sum_le_sum fun x _ ↦ by
          split_ifs
          · have hi : 0 ≤ invn := by dsimp [invn]; positivity
            nlinarith [mul_nonneg (hp0 x) hi]
          · exact le_add_of_nonneg_left hbase0
        _ = d * (2 * B / (eps * (L : Real) ^ 2)) +
            4 * (∑ x, cellMass P x) * invn := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            Finset.mul_sum, Finset.sum_mul]
          simp only [Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := by
          rw [hsum]
          have hi : 0 ≤ invn := by dsimp [invn]; positivity
          have heq : (d : Real) * (2 * B / (eps * (L : Real) ^ 2)) =
              2 * d * B / (eps * (L : Real) ^ 2) := by ring
          rw [heq]
          linarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
