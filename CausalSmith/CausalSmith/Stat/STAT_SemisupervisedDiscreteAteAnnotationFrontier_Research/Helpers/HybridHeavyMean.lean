module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyAggregate

/-! Exact one-cell expectation and bias bounds for the heavy branch. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

private def mergePairedPools
    (W : (Bool → Nat) × (Bool → Nat)) : Bool → Nat × Nat :=
  (MeasurableEquiv.arrowProdEquivProdArrow Nat Nat Bool).symm W

private lemma mergePairedPools_measurePreserving
    (muS muK : Bool → Measure Nat)
    [∀ a, IsProbabilityMeasure (muS a)]
    [∀ a, IsProbabilityMeasure (muK a)] :
    MeasurePreserving mergePairedPools
      ((Measure.pi muS).prod (Measure.pi muK))
      (Measure.pi fun a : Bool ↦ (muS a).prod (muK a)) := by
  exact (measurePreserving_arrowProdEquivProdArrow Nat Nat Bool muS muK).symm

/-- One arm of the inverse-count statistic has finite second moment.  [the stated conclusion](goal). -/
lemma hybridHeavyArmPools_memLp {d : Nat} (P : DiscreteLaw d)
    (u t : Real) (x : Fin d) (a : Bool) :
    MemLp (fun W : (Bool → Nat) × (Bool → Nat) ↦
      (W.1 a : Real) / u * ((W.2 false + W.2 true + 1 : Nat) : Real) /
        ((W.2 a + 1 : Nat) : Real)) 2
      ((Measure.pi fun b : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x b))).prod
       (Measure.pi fun b : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x b)))) := by
  let muS : Bool → Measure Nat := fun b ↦
    poissonMeasure (Real.toNNReal (u * markedMass P x b))
  let muK : Bool → Measure Nat := fun b ↦
    poissonMeasure (Real.toNNReal (t * armMass P x b))
  have hS : MemLp (fun S : Bool → Nat ↦ (S a : Real) / u) 2
      (Measure.pi muS) := by
    have hbase := (memLp_descFactorial_poisson
      (Real.toNNReal (u * markedMass P x a)) 1).const_mul u⁻¹
    have hpull := hbase.comp_measurePreserving (measurePreserving_eval muS a)
    convert hpull using 1
    funext S
    simp only [Nat.descFactorial_one, Function.comp_apply]
    ring
  have hKcoord (b : Bool) : MemLp (fun K : Bool → Nat ↦ (K b : Real)) 2
      (Measure.pi muK) := by
    have hpull := (memLp_descFactorial_poisson
      (Real.toNNReal (t * armMass P x b)) 1).comp_measurePreserving
        (measurePreserving_eval muK b)
    convert hpull using 1
    funext K
    simp only [Nat.descFactorial_one, Function.comp_apply]
  have hKtotal : MemLp
      (fun K : Bool → Nat ↦ ((K false + K true + 1 : Nat) : Real)) 2
      (Measure.pi muK) := by
    convert ((hKcoord false).add (hKcoord true)).add (memLp_const (1 : Real)) using 1
    funext K
    push_cast
    rfl
  have hdom := Causalean.Mathlib.Probability.memLp_mul_prod_two hS hKtotal
  apply hdom.mono (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with W
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
  have hden : (1 : Real) ≤ ((W.2 a + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_add_left 1 (W.2 a)
  rw [abs_of_nonneg (by positivity : 0 ≤ ((W.2 a + 1 : Nat) : Real))]
  exact div_le_self (abs_nonneg _) hden

/-- Exact one-cell identification extracted from the arm calculation in the
all-heavy expectation proof.  [the stated conditions](hyp:hu) [the stated conclusion](goal). -/
lemma integral_hybridHeavyPools_eq_armMeans {d : Nat}
    (P : DiscreteLaw d) (x : Fin d) {u t : Real} (hu : 0 < u) :
    (∫ W, hybridHeavyPools u W ∂
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))) =
      poissonInverseArmMean P u t x true -
        poissonInverseArmMean P u t x false := by
  let muS : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (u * markedMass P x a))
  let muK : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (t * armMass P x a))
  let muE := (Measure.pi muS).prod (Measure.pi muK)
  let muPair := Measure.pi fun a : Bool ↦ (muS a).prod (muK a)
  let armStat (a : Bool) (W : (Bool → Nat) × (Bool → Nat)) : Real :=
    (W.1 a : Real) / u * ((W.2 false + W.2 true + 1 : Nat) : Real) /
      ((W.2 a + 1 : Nat) : Real)
  let pairedArm (a : Bool) (K : Bool → Nat × Nat) : Real :=
    ((K a).1 : Real) / u *
      (((K false).2 + (K true).2 + 1 : Nat) : Real) /
        (((K a).2 + 1 : Nat) : Real)
  have hmp : MeasurePreserving mergePairedPools muE muPair :=
    mergePairedPools_measurePreserving muS muK
  have hArm (a : Bool) : (∫ W, armStat a W ∂muE) =
      poissonInverseArmMean P u t x a := by
    have htransport : (∫ W, armStat a W ∂muE) =
        ∫ K, pairedArm a K ∂muPair := by
      rw [← hmp.map_eq]
      rw [integral_map hmp.aemeasurable
        (measurable_of_countable (pairedArm a)).aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with W
      rfl
    rw [htransport]
    let lambdaS : Bool → NNReal := fun b ↦
      Real.toNNReal (u * markedMass P x b)
    let lambdaK : Bool → NNReal := fun b ↦
      Real.toNNReal (t * armMass P x b)
    have hbase : Integrable (fun K : Bool → Nat × Nat ↦
        ((K a).1 : Real) / u) muPair := by
      have h := (memLp_descFactorial_poisson (lambdaS a) 1).const_mul u⁻¹
      have heval := measurePreserving_eval (fun b : Bool ↦
        (poissonMeasure (lambdaS b)).prod (poissonMeasure (lambdaK b))) a
      have hp := h.comp_measurePreserving
        ((measurePreserving_fst (μ := poissonMeasure (lambdaS a))
          (ν := poissonMeasure (lambdaK a))).comp heval)
      apply (hp.integrable one_le_two).congr
      filter_upwards [] with K
      simp only [Function.comp_apply, Nat.descFactorial_one, div_eq_mul_inv]
      ring
    have hfull : Integrable (pairedArm a) muPair := by
      have hs := hybridHeavyArmPools_memLp P u t x a
      have hsplit := measurePreserving_arrowProdEquivProdArrow Nat Nat Bool muS muK
      exact ((hs.comp_measurePreserving hsplit).integrable one_le_two).congr (by
        filter_upwards [] with K
        rfl)
    have hcross : Integrable (fun K : Bool → Nat × Nat ↦
        ((K a).1 : Real) / u * ((K (!a)).2 : Real) *
          (((K a).2 + 1 : Nat) : Real)⁻¹) muPair := by
      apply (hfull.sub hbase).congr
      filter_upwards [] with K
      dsimp [pairedArm]
      cases a <;> simp only [Bool.not_false, Bool.not_true]
      all_goals push_cast; field_simp [hu.ne']; ring
    have hout := poisson_inverse_outcome_mean lambdaS lambdaK u a
    have hcrossMean := poisson_inverse_cross_moment lambdaS lambdaK u a
    rw [poissonInverseArmMean]
    change (∫ K, pairedArm a K ∂muPair) = _
    calc
      _ = (∫ K, ((K a).1 : Real) / u ∂muPair) +
          ∫ K, ((K a).1 : Real) / u * ((K (!a)).2 : Real) *
            (((K a).2 + 1 : Nat) : Real)⁻¹ ∂muPair := by
        rw [← integral_add hbase hcross]
        apply integral_congr_ae
        filter_upwards [] with K
        dsimp [pairedArm]
        cases a <;> simp only [Bool.not_false, Bool.not_true]
        all_goals push_cast; field_simp [hu.ne']; ring
      _ = _ := by
        change _ = ((lambdaS a : Real) / u) *
          (∫ z : Nat × Nat, 1 + (z.2 : Real) * (((z.1 + 1 : Nat) : Real))⁻¹
            ∂(poissonMeasure (lambdaK a)).prod (poissonMeasure (lambdaK (!a))))
        rw [hout, hcrossMean, poisson_inverse_weight_mean]
        ring
  change (∫ W, armStat true W - armStat false W ∂muE) = _
  rw [integral_sub
    ((hybridHeavyArmPools_memLp P u t x true).integrable one_le_two)
    ((hybridHeavyArmPools_memLp P u t x false).integrable one_le_two),
    hArm true, hArm false]

/-- C18 in the separated-pool notation.  [the stated conditions](hyp:hP,hu,ht,heps) [the stated conclusion](goal). -/
lemma integral_hybridHeavyPools_bias_le {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P) (x : Fin d)
    {u t : Real} (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps) :
    |(∫ W, hybridHeavyPools u W ∂
        ((Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
         (Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (t * armMass P x a))))) -
      cellMass P x * (outcomeMean P true x - outcomeMean P false x)| ≤
        2 * cellMass P x * Real.exp (-eps * t * cellMass P x) := by
  rw [integral_hybridHeavyPools_eq_armMeans P x hu]
  have h1 : |poissonInverseArmMean P u t x true -
      cellMass P x * outcomeMean P true x| ≤
      cellMass P x * Real.exp (-eps * t * cellMass P x) := by
    simpa [poissonInverseArmMean] using
      poisson_inverse_arm_mean_envelope P hP x true hu ht heps
  have h0 : |poissonInverseArmMean P u t x false -
      cellMass P x * outcomeMean P false x| ≤
      cellMass P x * Real.exp (-eps * t * cellMass P x) := by
    simpa [poissonInverseArmMean] using
      poisson_inverse_arm_mean_envelope P hP x false hu ht heps
  calc
    |poissonInverseArmMean P u t x true - poissonInverseArmMean P u t x false -
        cellMass P x * (outcomeMean P true x - outcomeMean P false x)| =
      |(poissonInverseArmMean P u t x true -
          cellMass P x * outcomeMean P true x) -
        (poissonInverseArmMean P u t x false -
          cellMass P x * outcomeMean P false x)| := by congr 1 <;> ring
    _ ≤ |poissonInverseArmMean P u t x true -
          cellMass P x * outcomeMean P true x| +
        |poissonInverseArmMean P u t x false -
          cellMass P x * outcomeMean P false x| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- The heavy-cell mean is at most three times the cell mass in absolute value.  [the stated conditions](hyp:hP,hu,ht,heps) [the stated conclusion](goal). -/
lemma abs_integral_hybridHeavyPools_le_three_cellMass {d : Nat} {eps : Real}
    (P : DiscreteLaw d) (hP : ModelClass d eps P) (x : Fin d)
    {u t : Real} (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps) :
    let muE := ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))
    abs (∫ W, hybridHeavyPools u W ∂muE) ≤ 3 * cellMass P x := by
  dsimp only
  let muE := ((Measure.pi fun a : Bool ↦
    poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
    (Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (t * armMass P x a))))
  change abs (∫ W, hybridHeavyPools u W ∂muE) ≤ 3 * cellMass P x
  let theta := cellMass P x *
    (outcomeMean P true x - outcomeMean P false x)
  have hb := integral_hybridHeavyPools_bias_le P hP x hu ht heps
  have hp0 := (cellMass_mem_unitInterval P x).1
  have htheta : |theta| ≤ cellMass P x := by
    dsimp [theta]
    rw [abs_mul, abs_of_nonneg hp0]
    apply mul_le_of_le_one_right hp0
    rw [abs_le]
    rcases outcomeMean_mem_unitInterval P true x with ⟨h10, h11⟩
    rcases outcomeMean_mem_unitInterval P false x with ⟨h00, h01⟩
    constructor <;> linarith
  have hexp : Real.exp (-eps * t * cellMass P x) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have := mul_nonneg (mul_nonneg heps.le ht.le) hp0
    linarith
  have htri : abs (∫ W, hybridHeavyPools u W ∂muE) ≤
      abs ((∫ W, hybridHeavyPools u W ∂muE) - theta) + |theta| := by
    calc
      abs _ = abs (((_ - theta) + theta)) := by congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
  change abs ((∫ W, hybridHeavyPools u W ∂muE) - theta) ≤
    2 * cellMass P x * Real.exp (-eps * t * cellMass P x) at hb
  have hprod : 2 * cellMass P x * Real.exp (-eps * t * cellMass P x) ≤
      2 * cellMass P x := by
    nlinarith [mul_le_mul_of_nonneg_left hexp
      (show 0 ≤ 2 * cellMass P x by positivity)]
  linarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
