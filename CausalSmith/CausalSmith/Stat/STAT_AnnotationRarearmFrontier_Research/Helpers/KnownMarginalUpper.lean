module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountArmRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.LabelFloorPair
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Variance

/-!
A total supplied-marginal inverse-propensity rule and its finite-sample risk bound.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- The binary inverse-propensity score reads both cell masses from the supplied table.
Division is total even for illegal tables and null cells. -/
-- @node: knownMarginalScore
noncomputable def knownMarginalScore {d : Nat} (v : AuxTable d) (z : Obs d) : Real :=
  if z.2.2 then
    (if z.2.1 then 1 else -1) * (v (z.1, false) + v (z.1, true)) / v (z.1, z.2.1)
  else 0

/-- The score is Borel jointly in its real table and finite record. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: knownMarginalScore_measurable
lemma knownMarginalScore_measurable (d : Nat) :
    Measurable (fun z : AuxTable d × Obs d => knownMarginalScore z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro z
  dsimp only [knownMarginalScore]
  split_ifs <;> fun_prop

/-- Clipping makes the supplied-table mean a total bounded rule on every table. -/
-- @node: knownMarginalEstimator
noncomputable def knownMarginalEstimator (n d : Nat) (eps : Real)
    (z : (Fin n → Obs d) × AuxTable d × Real) : Real :=
  if (n : Real) * eps < 1 then 0 else
    max (-1) (min 1 ((∑ i : Fin n, knownMarginalScore z.2.1 (z.1 i)) / n))

/-- The supplied-table rule is jointly Borel. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: knownMarginalEstimator_measurable
lemma knownMarginalEstimator_measurable (n d : Nat) (eps : Real) :
    Measurable (knownMarginalEstimator n d eps) := by
  unfold knownMarginalEstimator
  split_ifs
  · fun_prop
  · have hscore (i : Fin n) : Measurable (fun z : (Fin n → Obs d) × AuxTable d × Real =>
        knownMarginalScore z.2.1 (z.1 i)) :=
      (knownMarginalScore_measurable d).comp
        (show Measurable (fun z : (Fin n → Obs d) × AuxTable d × Real =>
          (z.2.1, z.1 i)) by fun_prop)
    fun_prop

/-- [Under the stated inputs and conditions](hyp:eps,z,n,d), The total supplied-table rule is clipped to the prescribed action interval.  This gives [the stated result](goal).-/
-- @node: knownMarginalEstimator_mem_Icc
lemma knownMarginalEstimator_mem_Icc (n d : Nat) (eps : Real)
    (z : (Fin n → Obs d) × AuxTable d × Real) :
    knownMarginalEstimator n d eps z ∈ Set.Icc (-1) 1 := by
  unfold knownMarginalEstimator
  split
  · norm_num
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- [Under the stated inputs and conditions](hyp:d,P), At the actual marginal table the score has exactly the observable ATE mean.  This gives [the stated result](goal).-/
-- @node: knownMarginalScore_mean
lemma knownMarginalScore_mean {d : Nat} (P : DiscreteLaw d) :
    (∫ z, knownMarginalScore (auxTable P) z ∂obsLaw P) = ateFunctional P := by
  let : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  rw [obsLaw, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  change (∑ z : Obs d, jointMass P z.1 z.2.1 z.2.2 *
    knownMarginalScore (auxTable P) z) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, knownMarginalScore,
    auxTable, auxMarginal_toReal_armMass, Bool.false_eq_true, if_false, if_true]
  unfold ateFunctional outcomeMean markedMass
  apply Finset.sum_congr rfl
  intro j _
  have hp : armMass P j false + armMass P j true = cellMass P j := by
    simp [cellMass, armMass, add_comm]
  rw [hp]
  ring

/-- [Under the stated inputs and conditions](hyp:d,P,eps,heps,hP,j,a), Overlap bounds each arm's marked contribution to the score's second moment.  This gives [the stated result](goal).-/
-- @node: knownMarginalScore_arm_second_moment
lemma knownMarginalScore_arm_second_moment {d : Nat} (P : DiscreteLaw d)
    (eps : Real) (heps : 0 < eps) (hP : ModelClass d eps P) (j : Fin d) (a : Bool) :
    markedMass P j a * (cellMass P j / armMass P j a) ^ 2 ≤ cellMass P j / eps := by
  have hp := cellMass_nonneg P j
  have hs := armMass_nonneg P j a
  have hqs : markedMass P j a ≤ armMass P j a := by
    simp only [armMass, markedMass, Fintype.sum_bool]
    linarith [jointMass_nonneg P j a false]
  have hover := armMass_ge_overlap_cellMass P eps hP j a
  by_cases hz : armMass P j a = 0
  · simp only [hz, div_zero, zero_pow (by decide : (2 : Nat) ≠ 0), mul_zero]
    positivity
  · have hspos : 0 < armMass P j a := lt_of_le_of_ne hs (Ne.symm hz)
    calc
      _ ≤ armMass P j a * (cellMass P j / armMass P j a) ^ 2 :=
        mul_le_mul_of_nonneg_right hqs (sq_nonneg _)
      _ = cellMass P j * (cellMass P j / armMass P j a) := by field_simp
      _ ≤ cellMass P j * (1 / eps) := by
        apply mul_le_mul_of_nonneg_left _ hp
        apply (div_le_iff₀ hspos).2
        have hh := (le_div_iff₀ heps).2 (by simpa only [mul_comm] using hover)
        convert hh using 1 <;> ring
      _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:d,P,eps,heps,hP), The score's second moment is at most twice the inverse overlap floor.  This gives [the stated result](goal).-/
-- @node: knownMarginalScore_second_moment
lemma knownMarginalScore_second_moment {d : Nat} (P : DiscreteLaw d)
    (eps : Real) (heps : 0 < eps) (hP : ModelClass d eps P) :
    (∫ z, knownMarginalScore (auxTable P) z ^ 2 ∂obsLaw P) ≤ 2 / eps := by
  let : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  rw [obsLaw, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  change (∑ z : Obs d, jointMass P z.1 z.2.1 z.2.2 *
    knownMarginalScore (auxTable P) z ^ 2) ≤ _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, knownMarginalScore,
    auxTable, auxMarginal_toReal_armMass, Bool.false_eq_true, if_false, if_true]
  have hcell (j : Fin d) : armMass P j false + armMass P j true = cellMass P j := by
    simp [cellMass, armMass, add_comm]
  simp_rw [hcell]
  calc
    _ = ∑ j : Fin d, (markedMass P j false * (cellMass P j / armMass P j false) ^ 2 +
        markedMass P j true * (cellMass P j / armMass P j true) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [markedMass, neg_div, neg_sq, add_comm]
    _ ≤ ∑ j : Fin d, (cellMass P j / eps + cellMass P j / eps) :=
      Finset.sum_le_sum (fun j _ => add_le_add
        (knownMarginalScore_arm_second_moment P eps heps hP j false)
        (knownMarginalScore_arm_second_moment P eps heps hP j true))
    _ = 2 / eps := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, sum_cellMass]
      ring

/-- [Under the stated inputs and conditions](hyp:d,P,n,eps,hn,heps,hP), Independence of complete records divides the score variance by the labeled budget.  This gives [the stated result](goal).-/
-- @node: knownMarginalMean_risk
lemma knownMarginalMean_risk {d : Nat} (P : DiscreteLaw d) (n : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps) (hP : ModelClass d eps P) :
    (∫ x, ((∑ i : Fin n, knownMarginalScore (auxTable P) (x i)) / n -
      ateFunctional P) ^ 2 ∂labeledProductLaw P n) ≤ 2 / ((n : Real) * eps) := by
  let : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  let : IsProbabilityMeasure (labeledProductLaw P n) := by unfold labeledProductLaw; infer_instance
  let F := knownMarginalScore (auxTable P)
  let M : (Fin n → Obs d) → Real := fun x => (∑ i : Fin n, F (x i)) / n
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hF : MemLp F 2 (obsLaw P) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 Integrable.of_finite
  have hM : Measurable M := by fun_prop
  have hmean : (∫ x, M x ∂labeledProductLaw P n) = ateFunctional P := by
    dsimp [M, labeledProductLaw]
    rw [integral_div, integral_finsetSum]
    · have heval (i : Fin n) : (∫ x : Fin n → Obs d, F (x i)
          ∂Measure.pi (fun _ : Fin n => obsLaw P)) = ∫ z, F z ∂obsLaw P :=
        integral_comp_eval (μ := fun _ : Fin n => obsLaw P) (i := i) hF.aestronglyMeasurable
      simp_rw [heval]
      simp [F, knownMarginalScore_mean, hn0]
    · intro i _
      exact Integrable.of_finite
  have hvar : Var[M; labeledProductLaw P n] = Var[F; obsLaw P] / n := by
    dsimp [M, labeledProductLaw]
    simp only [div_eq_mul_inv]
    rw [variance_mul_const]
    have hsum : (fun x : Fin n → Obs d => ∑ i : Fin n, F (x i)) =
        ∑ i : Fin n, (fun x : Fin n → Obs d => F (x i)) := by
      funext x
      simp
    rw [hsum, variance_sum_pi (fun _ : Fin n => hF)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hv := (variance_le_expectation_sq hF.aestronglyMeasurable).trans
    (knownMarginalScore_second_moment P eps heps hP)
  calc
    _ = Var[M; labeledProductLaw P n] := by
      rw [variance_eq_integral hM.aemeasurable, hmean]
    _ = Var[F; obsLaw P] / n := hvar
    _ ≤ (2 / eps) / n := div_le_div_of_nonneg_right hv (Nat.cast_nonneg n)
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:htau,x,tau), Projection onto the action interval cannot increase squared distance to a legal target.  This gives [the stated result](goal).-/
-- @node: knownMarginal_clip_loss
lemma knownMarginal_clip_loss (x tau : Real) (htau : tau ∈ Set.Icc (-1) 1) :
    (max (-1) (min 1 x) - tau) ^ 2 ≤ (x - tau) ^ 2 := by
  by_cases hlo : x < -1
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    nlinarith [htau.1]
  · by_cases hhi : 1 < x
    · rw [min_eq_left hhi.le, max_eq_right (by norm_num)]
      nlinarith [htau.2]
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- [Under the stated inputs and conditions](hyp:d,P,n,eps,hn,heps,hP), The zero branch and the clipped iid mean attain the capped oracle label rate.  This gives [the stated result](goal).-/
-- @node: knownMarginalEstimator_risk
lemma knownMarginalEstimator_risk {d : Nat} (P : DiscreteLaw d) (n : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps) (hP : ModelClass d eps P) :
    knownRuleRisk (knownMarginalEstimator n d eps) P ≤ 2 * labelBenchmark n eps := by
  let : IsProbabilityMeasure (obsLaw P) := by unfold obsLaw; infer_instance
  let : IsProbabilityMeasure (labeledProductLaw P n) := by unfold labeledProductLaw; infer_instance
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hS := mul_pos hnpos heps
  have htau := ateFunctional_mem_Icc P
  by_cases hsmall : (n : Real) * eps < 1
  · have hbench : labelBenchmark n eps = 1 := by
      exact min_eq_left ((one_le_inv₀ hS).2 hsmall.le)
    have hrisk : knownRuleRisk (knownMarginalEstimator n d eps) P = ateFunctional P ^ 2 := by
      simp [knownRuleRisk, knownMarginalEstimator, hsmall]
    rw [hrisk, hbench, mul_one]
    nlinarith [htau.1, htau.2]
  · have hbench : labelBenchmark n eps = 1 / ((n : Real) * eps) := by
      simpa only [labelBenchmark, labelScale, one_div] using
        min_eq_right (inv_le_one_of_one_le₀ (le_of_not_gt hsmall))
    rw [hbench]
    have hint : Integrable (fun x : Fin n → Obs d =>
        ((∑ i : Fin n, knownMarginalScore (auxTable P) (x i)) / n -
          ateFunctional P) ^ 2) (labeledProductLaw P n) := Integrable.of_finite
    have hprod := hint.comp_fst seedLaw
    unfold knownRuleRisk
    calc
      _ ≤ ∫ z : (Fin n → Obs d) × Real,
          ((∑ i : Fin n, knownMarginalScore (auxTable P) (z.1 i)) / n -
            ateFunctional P) ^ 2 ∂((labeledProductLaw P n).prod seedLaw) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
          hprod (Filter.Eventually.of_forall (fun z => ?_))
        simp only [knownMarginalEstimator, if_neg hsmall]
        exact knownMarginal_clip_loss _ _ htau
      _ = ∫ x, ((∑ i : Fin n, knownMarginalScore (auxTable P) (x i)) / n -
            ateFunctional P) ^ 2 ∂labeledProductLaw P n := by
        rw [integral_prod]
        · simp
        · exact hprod
      _ ≤ 2 / ((n : Real) * eps) := knownMarginalMean_risk P n eps hn heps hP
      _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',n,d), Taking the infimum over Borel supplied-table rules preserves the oracle upper bound.  This gives [the stated result](goal).-/
-- @node: knownMarginalRisk_le_labelBenchmark
lemma knownMarginalRisk_le_labelBenchmark (n d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    knownMarginalRisk n d eps ≤ 2 * labelBenchmark n eps := by
  let P0 : ClassLaw d eps :=
    ⟨labelFloorLaw d eps (1 / 8) false hd labelFloorAmplitude_eighth,
      labelFloor_model d eps (1 / 8) false hd labelFloorAmplitude_eighth heps heps'⟩
  letI : Nonempty (ClassLaw d eps) := ⟨P0⟩
  let T : KnownRule n d := ⟨knownMarginalEstimator n d eps,
    knownMarginalEstimator_measurable n d eps, knownMarginalEstimator_mem_Icc n d eps⟩
  apply (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (T : KnownRule n d) (P : ClassLaw d eps) => knownRuleRisk T.1 P.1)
    (fun T P => integral_nonneg (fun z => sq_nonneg _)) T).trans
  exact ciSup_le (fun P => knownMarginalEstimator_risk P.1 n eps hn heps P.2)

end CausalSmith.Stat.AnnotationRarearmFrontier
