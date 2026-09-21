module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessFaithfulnessAssembly

/-!
# Cancellation-witness faithfulness

This file proves dependence of the cancellation witness's unique edge from a
strictly positive covariance, and then invokes the three-node graph reduction.
-/

public section

open Causalean.Graph


open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: continuous_reflectedCancellationPrimitive
/-- A [fixed signed reflection followed by the cancellation primitive is continuous](goal). -/
@[fun_prop] lemma continuous_reflectedCancellationPrimitive
    (s : SignVector 3) (i : Fin 3) :
    Continuous (fun z : ℝ => cancellationPrimitive (reflectedCoordinate s i z)) := by
  rcases s.signed i with hi | hi <;>
    simp [cancellationPrimitive, reflectedCoordinate, reflect, hi,
      show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop

-- @node: cancellationWitness_integral_eq_iterated
/-- A continuous test function under the cancellation observational law is its explicit
three-coordinate iterated density integral.  Given [the stated inputs and conditions](hyp:hf), [the stated conclusion](goal) follows. -/
lemma cancellationWitness_integral_eq_iterated (s : SignVector 3)
    (f : LatentState 3 → ℝ) (hf : ContinuousOn f (latentCube 3)) :
    (∫ v, f v ∂observationalLaw (cancellationWitness s)) =
      ∫ x in Set.Icc (0 : ℝ) 1,
        ∫ y in Set.Icc (0 : ℝ) 1,
          ∫ z in Set.Icc (0 : ℝ) 1,
            observationalDensity (cancellationWitness s) ![x, y, z] * f ![x, y, z] := by
  let μ : Measure (LatentState 3) := volume.restrict (latentCube 3)
  have hpos := cancellationWitness_positive_normalized_smooth s
  have hcubeCompact : IsCompact (latentCube 3) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hdensityCont : ContinuousOn (observationalDensity (cancellationWitness s))
      (latentCube 3) := by
    unfold observationalDensity
    exact continuousOn_finset_prod _ fun i _ => (hpos.2.2.1 i).continuousOn
  have hprodInt : Integrable
      (fun v => observationalDensity (cancellationWitness s) v * f v) μ := by
    dsimp only [μ]
    exact (hdensityCont.mul hf).integrableOn_compact hcubeCompact
  have hμ : μ = Measure.pi (fun _ : Fin 3 =>
      volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    dsimp only [μ]
    change volume.restrict (Set.univ.pi fun _ : Fin 3 => Set.Icc (0 : ℝ) 1) = _
    rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  calc
    (∫ v, f v ∂observationalLaw (cancellationWitness s)) =
        ∫ v, observationalDensity (cancellationWitness s) v * f v ∂μ := by
      unfold observationalLaw
      rw [integral_withDensity_eq_integral_toReal_smul]
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_latentCube 3)] with v hv
        rw [ENNReal.toReal_ofReal (le_of_lt (by
          unfold observationalDensity
          exact Finset.prod_pos fun i _ => hpos.1 i v hv))]
        rfl
      · exact (measurable_cancellationWitness_observationalDensity s).ennreal_ofReal
      · filter_upwards with v
        exact ENNReal.ofReal_lt_top
    _ = _ := by
      rw [hμ, integral_fin_three_pi_eq_iterated _ _ (by simpa [hμ] using hprodInt)]

-- @node: cancellationWitness_parent_inner_integral
/-- Integrating over the child leaves the cancellation coefficient unchanged.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_parent_inner_integral (s : SignVector 3) (x : ℝ) :
    (∫ y in Set.Icc (0 : ℝ) 1,
      (1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y)) *
        cancellationPrimitive (reflectedCoordinate s 0 x)) =
      cancellationPrimitive (reflectedCoordinate s 0 x) := by
  let A := cancellationPrimitive (reflectedCoordinate s 0 x)
  let B : ℝ → ℝ := fun y => centeredCoordinate (reflectedCoordinate s 1 y)
  have hB : Continuous B := continuous_reflectedCenteredCoordinate s 1
  have h2 : IntegrableOn (fun y => (1 / 10 : ℝ) * A ^ 2 * B y)
      (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.mul hB).continuousOn.integrableOn_Icc
  have hconst : IntegrableOn (fun _ : ℝ => A) (Set.Icc (0 : ℝ) 1) :=
    continuous_const.continuousOn.integrableOn_Icc
  rw [show (fun y => (1 + (1 / 10 : ℝ) * A * B y) * A) =
      fun y => A + (1 / 10 : ℝ) * A ^ 2 * B y by funext y; ring,
    integral_add hconst h2, MeasureTheory.integral_const,
    MeasureTheory.integral_const_mul, centeredCoordinate_reflected_integral,
    mul_zero, add_zero]
  simp [A, Real.volume_Icc]

-- @node: cancellationWitness_child_inner_integral
/-- Integrating the centered child coordinate gives one thirtieth of the parent coefficient.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_child_inner_integral (s : SignVector 3) (x : ℝ) :
    (∫ y in Set.Icc (0 : ℝ) 1,
      (1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y)) *
        centeredCoordinate (reflectedCoordinate s 1 y)) =
      (1 / 30 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 x) := by
  let A := cancellationPrimitive (reflectedCoordinate s 0 x)
  let B : ℝ → ℝ := fun y => centeredCoordinate (reflectedCoordinate s 1 y)
  have hB : Continuous B := continuous_reflectedCenteredCoordinate s 1
  have h1 : IntegrableOn B (Set.Icc (0 : ℝ) 1) :=
    hB.continuousOn.integrableOn_Icc
  have h2 : IntegrableOn (fun y => (1 / 10 : ℝ) * A * B y ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.mul (hB.pow 2)).continuousOn.integrableOn_Icc
  rw [show (fun y => (1 + (1 / 10 : ℝ) * A * B y) * B y) =
      fun y => B y + (1 / 10 : ℝ) * A * B y ^ 2 by funext y; ring,
    integral_add h1 h2, MeasureTheory.integral_const_mul,
    centeredCoordinate_reflected_integral,
    centeredCoordinate_reflected_sq_integral]
  dsimp only [A]
  ring

-- @node: cancellationWitness_joint_inner_integral
/-- The child-parent test-product integral is one thirtieth of the squared coefficient.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_joint_inner_integral (s : SignVector 3) (x : ℝ) :
    (∫ y in Set.Icc (0 : ℝ) 1,
      (1 + (1 / 10 : ℝ) *
          cancellationPrimitive (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y)) *
        (cancellationPrimitive (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y))) =
      (1 / 30 : ℝ) * cancellationPrimitive (reflectedCoordinate s 0 x) ^ 2 := by
  let A := cancellationPrimitive (reflectedCoordinate s 0 x)
  let B : ℝ → ℝ := fun y => centeredCoordinate (reflectedCoordinate s 1 y)
  have hB : Continuous B := continuous_reflectedCenteredCoordinate s 1
  have h1 : IntegrableOn (fun y => A * B y) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.mul hB).continuousOn.integrableOn_Icc
  have h2 : IntegrableOn (fun y => (1 / 10 : ℝ) * A ^ 2 * B y ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.mul (hB.pow 2)).continuousOn.integrableOn_Icc
  rw [show (fun y => (1 + (1 / 10 : ℝ) * A * B y) * (A * B y)) =
      fun y => A * B y + (1 / 10 : ℝ) * A ^ 2 * B y ^ 2 by funext y; ring,
    integral_add h1 h2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, centeredCoordinate_reflected_integral,
    centeredCoordinate_reflected_sq_integral]
  dsimp only [A]
  ring

-- @node: reflectedCancellationPrimitive_variance_pos
/-- The reflected cancellation coefficient has strictly positive variance under unit Lebesgue law.  [the stated conclusion](goal) follows. -/
lemma reflectedCancellationPrimitive_variance_pos (s : SignVector 3) :
    0 < (∫ x in Set.Icc (0 : ℝ) 1,
        cancellationPrimitive (reflectedCoordinate s 0 x) ^ 2) -
      (∫ x in Set.Icc (0 : ℝ) 1,
        cancellationPrimitive (reflectedCoordinate s 0 x)) ^ 2 := by
  let K : ℝ → ℝ := fun x => cancellationPrimitive (reflectedCoordinate s 0 x)
  let m : ℝ := ∫ x in Set.Icc (0 : ℝ) 1, K x
  have hK : Continuous K := continuous_reflectedCancellationPrimitive s 0
  have hx : ∃ x ∈ Set.Icc (0 : ℝ) 1, K x ≠ m := by
    have hmid : K (1 / 2) = cancellationPrimitive (1 / 2) := by
      rcases s.signed 0 with hi | hi <;>
        norm_num [K, reflectedCoordinate, reflect, hi,
          show (-1 : ℝ) ≠ 1 by norm_num]
    by_cases hm : K (1 / 2) = m
    · rcases s.signed 0 with hi | hi
      · refine ⟨1, by norm_num, ?_⟩
        have hend : K 1 = 0 := by
          simp only [K, reflectedCoordinate, hi, reflect,
            if_neg (show (-1 : ℝ) ≠ 1 by norm_num)]
          norm_num
          exact cancellationPrimitive_zero.1
        rw [← hm, hmid]
        rw [hend]
        exact ne_of_gt cancellationPrimitive_half_neg
      · refine ⟨0, by norm_num, ?_⟩
        have hend : K 0 = 0 := by
          simp [K, reflectedCoordinate, reflect, hi, cancellationPrimitive_zero.1]
        rw [← hm, hmid]
        rw [hend]
        exact ne_of_gt cancellationPrimitive_half_neg
    · exact ⟨1 / 2, by norm_num, hm⟩
  have hposInt : 0 < ∫ x in Set.Icc (0 : ℝ) 1, (K x - m) ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => 0) (g := fun x => (K x - m) ^ 2)
      (by norm_num : (0 : ℝ) < 1) continuousOn_const
      ((hK.sub continuous_const).pow 2).continuousOn
      (fun x hx' => sq_nonneg _)
      (by
        rcases hx with ⟨x, hxI, hxm⟩
        exact ⟨x, hxI, sq_pos_of_ne_zero (sub_ne_zero.mpr hxm)⟩)
    simpa using hlt
  have hexpand : (∫ x in Set.Icc (0 : ℝ) 1, (K x - m) ^ 2) =
      (∫ x in Set.Icc (0 : ℝ) 1, K x ^ 2) - m ^ 2 := by
    have hKint : IntegrableOn K (Set.Icc (0 : ℝ) 1) :=
      hK.continuousOn.integrableOn_Icc
    have hKsq : IntegrableOn (fun x => K x ^ 2) (Set.Icc (0 : ℝ) 1) :=
      (hK.pow 2).continuousOn.integrableOn_Icc
    have hcross : IntegrableOn (fun x => 2 * m * K x) (Set.Icc (0 : ℝ) 1) :=
      hKint.const_mul (2 * m)
    have hconst : IntegrableOn (fun _ : ℝ => m ^ 2) (Set.Icc (0 : ℝ) 1) :=
      continuous_const.continuousOn.integrableOn_Icc
    calc
      _ = ∫ x in Set.Icc (0 : ℝ) 1,
          (K x ^ 2 - 2 * m * K x) + m ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = (∫ x in Set.Icc (0 : ℝ) 1, K x ^ 2 - 2 * m * K x) +
          ∫ _x in Set.Icc (0 : ℝ) 1, m ^ 2 := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_add (hKsq.sub hcross) hconst
      _ = ((∫ x in Set.Icc (0 : ℝ) 1, K x ^ 2) -
          ∫ x in Set.Icc (0 : ℝ) 1, 2 * m * K x) +
          ∫ _x in Set.Icc (0 : ℝ) 1, m ^ 2 := by
        rw [integral_sub hKsq hcross]
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
        have hvol : (volume.restrict (Set.Icc (0 : ℝ) 1)).real Set.univ = 1 := by
          simp [Measure.real, Real.volume_Icc]
        rw [hvol]
        dsimp only [m]
        ring
  rw [hexpand] at hposInt
  simpa only [K, m] using hposInt

-- @node: cancellationWitness_not_condIndep_edge
/-- Positive coefficient-child covariance rules out independence of the cancellation edge.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_not_condIndep_edge (s : SignVector 3) :
    ¬ CondIndepCoordinates (cancellationWitness s) {0} {1} ∅ := by
  intro hCI
  let K : ℝ → ℝ := fun x => cancellationPrimitive (reflectedCoordinate s 0 x)
  let H : ℝ → ℝ := fun y => centeredCoordinate (reflectedCoordinate s 1 y)
  let m : ℝ := ∫ x in Set.Icc (0 : ℝ) 1, K x
  let v2 : ℝ := ∫ x in Set.Icc (0 : ℝ) 1, K x ^ 2
  have hparent : (∫ v, K (v 0) ∂observationalLaw (cancellationWitness s)) = m := by
    rw [cancellationWitness_integral_eq_iterated]
    · simp [observationalDensity, cancellationWitness, cancellationP]
      apply integral_congr_ae
      filter_upwards with x
      simpa [K, one_div] using cancellationWitness_parent_inner_integral s x
    · exact (continuous_reflectedCancellationPrimitive s 0).comp
        (continuous_apply 0) |>.continuousOn
  have hchild : (∫ v, H (v 1) ∂observationalLaw (cancellationWitness s)) =
      (1 / 30 : ℝ) * m := by
    rw [cancellationWitness_integral_eq_iterated]
    · simp [observationalDensity, cancellationWitness, cancellationP]
      calc
        _ = ∫ x in Set.Icc (0 : ℝ) 1, (1 / 30 : ℝ) * K x := by
          apply integral_congr_ae
          filter_upwards with x
          simpa [K, H, one_div] using cancellationWitness_child_inner_integral s x
        _ = _ := by
          rw [MeasureTheory.integral_const_mul]
          norm_num
          change (∫ x in Set.Icc (0 : ℝ) 1, K x) =
            ∫ x in Set.Icc (0 : ℝ) 1, K x
          rfl
    · exact (continuous_reflectedCenteredCoordinate s 1).comp
        (continuous_apply 1) |>.continuousOn
  have hjoint : (∫ v, K (v 0) * H (v 1)
      ∂observationalLaw (cancellationWitness s)) = (1 / 30 : ℝ) * v2 := by
    rw [cancellationWitness_integral_eq_iterated]
    · simp [observationalDensity, cancellationWitness, cancellationP]
      calc
        _ = ∫ x in Set.Icc (0 : ℝ) 1, (1 / 30 : ℝ) * K x ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          simpa [K, H, one_div] using cancellationWitness_joint_inner_integral s x
        _ = _ := by
          rw [MeasureTheory.integral_const_mul]
          norm_num
          change (∫ x in Set.Icc (0 : ℝ) 1, K x ^ 2) =
            ∫ x in Set.Icc (0 : ℝ) 1, K x ^ 2
          rfl
    · exact ((continuous_reflectedCancellationPrimitive s 0).comp
        (continuous_apply 0)).mul
          ((continuous_reflectedCenteredCoordinate s 1).comp
            (continuous_apply 1)) |>.continuousOn
  letI : IsProbabilityMeasure (observationalLaw (cancellationWitness s)) :=
    observationalLaw_isProbabilityMeasure (cancellationWitness_positive_normalized_smooth s)
  have hblocks := indepFun_of_condIndepCoordinates_empty
    ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3)) hCI
  let z0 : {j // j ∈ ({0} : Finset (Fin 3))} := ⟨0, by simp⟩
  let z1 : {j // j ∈ ({1} : Finset (Fin 3))} := ⟨1, by simp⟩
  have hind : IndepFun (fun v : LatentState 3 => K (v 0))
      (fun v : LatentState 3 => H (v 1))
      (observationalLaw (cancellationWitness s)) := by
    let left := fun z : ((j : {j // j ∈ ({0} : Finset (Fin 3))}) → ℝ) => K (z z0)
    let right := fun z : ((j : {j // j ∈ ({1} : Finset (Fin 3))}) → ℝ) => H (z z1)
    have hraw := hblocks.comp
      (show Measurable left by unfold left; fun_prop)
      (show Measurable right by unfold right; fun_prop)
    convert hraw using 1 <;> funext v <;> rfl
  have hmul := hind.integral_fun_mul_eq_mul_integral
    ((continuous_reflectedCancellationPrimitive s 0).measurable.comp
      (measurable_pi_apply 0)).aestronglyMeasurable
    ((continuous_reflectedCenteredCoordinate s 1).measurable.comp
      (measurable_pi_apply 1)).aestronglyMeasurable
  rw [hjoint, hparent, hchild] at hmul
  have hvar := reflectedCancellationPrimitive_variance_pos s
  nlinarith

-- @node: cancellationWitness_causalMinimality
/-- The cancellation witness is causally minimal for the one-edge three-node DAG.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_causalMinimality (s : SignVector 3) :
    CausalMinimality threeNodeDAG (cancellationWitness s) := by
  intro j i hji
  rcases hji with ⟨rfl, rfl⟩
  intro hCI
  apply cancellationWitness_not_condIndep_edge s
  have hparents : (threeNodeDAG.parents 1).erase 0 = ∅ := by
    ext k
    fin_cases k <;> simp [threeNodeDAG, threeNodeEdge, DAG.parents]
  rw [hparents] at hCI
  exact condIndepCoordinates_symm hCI

-- @node: cancellationWitness_faithfulness
/-- The cancellation witness is faithful to `0 → 1` with isolated node `2`.  [the stated conclusion](goal) follows. -/
lemma cancellationWitness_faithfulness (s : SignVector 3) :
    Faithfulness threeNodeDAG (cancellationWitness s) :=
  threeNodeDAG_faithful_of_causalMinimality
    (cancellationWitness_positive_normalized_smooth s)
    (cancellationWitness_causalMinimality s)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
