import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessAssembly
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessFaithfulness
import Mathlib.Probability.Independence.Integration

/-!
# Explicit-witness faithfulness assembly

This file turns the explicit sparse density calculation into dependence of the
unique adjacent coordinate pair, and hence into faithfulness of the sparse
three-node witness.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: centeredCoordinate_sq_integral
/-- The squared centered coordinate has unit-interval integral `1/3`.  [the stated conclusion](goal) follows. -/
lemma centeredCoordinate_sq_integral :
    (∫ z in Set.Icc (0 : ℝ) 1, centeredCoordinate z ^ 2) = 1 / 3 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hfun : (fun z : ℝ => centeredCoordinate z ^ 2) =
      fun z => 4 * z ^ 2 - 4 * z + 1 := by
    funext z
    simp only [centeredCoordinate]
    ring
  have hpow : IntervalIntegrable (fun z : ℝ => 4 * z ^ 2) volume 0 1 := by
    exact (intervalIntegral.intervalIntegrable_pow 2).const_mul 4
  have hid : IntervalIntegrable (fun z : ℝ => 4 * z) volume 0 1 := by
    exact intervalIntegral.intervalIntegrable_id.const_mul 4
  rw [hfun, intervalIntegral.integral_add (hpow.sub hid) intervalIntegrable_const,
    intervalIntegral.integral_sub hpow hid,
    intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const]
  norm_num

-- @node: centeredCoordinate_reflected_sq_integral
/-- Coordinate reflection preserves the squared centered-coordinate integral.  [the stated conclusion](goal) follows. -/
lemma centeredCoordinate_reflected_sq_integral (s : SignVector 3) (i : Fin 3) :
    (∫ z in Set.Icc (0 : ℝ) 1,
      centeredCoordinate (reflectedCoordinate s i z) ^ 2) = 1 / 3 := by
  calc
    _ = ∫ z in Set.Icc (0 : ℝ) 1, centeredCoordinate z ^ 2 :=
      integral_reflectedCoordinate s i (fun z => centeredCoordinate z ^ 2)
    _ = 1 / 3 := centeredCoordinate_sq_integral

-- @node: measurable_sparseP
/-- [Every sparse-witness observational mechanism slot is globally measurable](goal). -/
@[fun_prop] lemma measurable_sparseP (s : SignVector 3) (i : Fin 3) :
    Measurable (sparseP s i) := by
  fin_cases i
  · change Measurable (fun _ : LatentState 3 => (1 : ℝ))
    fun_prop
  · rcases s.signed 0 with h0 | h0 <;>
      rcases s.signed 1 with h1 | h1 <;>
      change Measurable (fun v : LatentState 3 => 1 + (1 / 10 : ℝ) *
        centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
          centeredCoordinate (reflectedCoordinate s 1 (v 1))) <;>
      simp [centeredCoordinate, reflectedCoordinate, reflect, h0, h1,
        show (-1 : ℝ) ≠ 1 by norm_num] <;> fun_prop
  · change Measurable (fun _ : LatentState 3 => (1 : ℝ))
    fun_prop

-- @node: measurable_sparseWitness_observationalDensity
/-- The [sparse witness's observational joint density is globally measurable](goal). -/
@[fun_prop] lemma measurable_sparseWitness_observationalDensity (s : SignVector 3) :
    Measurable (observationalDensity (sparseWitness s)) := by
  unfold observationalDensity
  apply Finset.measurable_prod
  intro i _
  exact measurable_sparseP s i

-- @node: continuous_reflectedCenteredCoordinate
/-- A [fixed signed reflection followed by centering is continuous](goal). -/
@[fun_prop] lemma continuous_reflectedCenteredCoordinate
    (s : SignVector 3) (i : Fin 3) :
    Continuous (fun z : ℝ => centeredCoordinate (reflectedCoordinate s i z)) := by
  rcases s.signed i with hi | hi
  · simp [centeredCoordinate, reflectedCoordinate, reflect, hi,
      show (-1 : ℝ) ≠ 1 by norm_num]
    fun_prop
  · simp [centeredCoordinate, reflectedCoordinate, reflect, hi]
    fun_prop

-- @node: sparseWitness_integral_eq_iterated
/-- A continuous test function under the sparse observational law can be evaluated
as the explicit three-coordinate iterated density integral.  Given [the stated inputs and conditions](hyp:hf), [the stated conclusion](goal) follows. -/
lemma sparseWitness_integral_eq_iterated (s : SignVector 3)
    (f : LatentState 3 → ℝ) (hf : ContinuousOn f (latentCube 3)) :
    (∫ v, f v ∂observationalLaw (sparseWitness s)) =
      ∫ x in Set.Icc (0 : ℝ) 1,
        ∫ y in Set.Icc (0 : ℝ) 1,
          ∫ z in Set.Icc (0 : ℝ) 1,
            observationalDensity (sparseWitness s) ![x, y, z] * f ![x, y, z] := by
  let μ : Measure (LatentState 3) := volume.restrict (latentCube 3)
  have hpos := sparseWitness_positive_normalized_smooth s
  have hcubeCompact : IsCompact (latentCube 3) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hdensityCont : ContinuousOn (observationalDensity (sparseWitness s))
      (latentCube 3) := by
    unfold observationalDensity
    exact continuousOn_finset_prod _ fun i _ => (hpos.2.2.1 i).continuousOn
  have hprodInt : Integrable
      (fun v => observationalDensity (sparseWitness s) v * f v) μ := by
    dsimp only [μ]
    exact (hdensityCont.mul hf).integrableOn_compact hcubeCompact
  have hμ : μ = Measure.pi (fun _ : Fin 3 =>
      volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    dsimp only [μ]
    change volume.restrict (Set.univ.pi fun _ : Fin 3 => Set.Icc (0 : ℝ) 1) = _
    rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]
  calc
    (∫ v, f v ∂observationalLaw (sparseWitness s)) =
        ∫ v, observationalDensity (sparseWitness s) v * f v ∂μ := by
      unfold observationalLaw
      rw [integral_withDensity_eq_integral_toReal_smul]
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_latentCube 3)] with v hv
        rw [ENNReal.toReal_ofReal (le_of_lt (by
          unfold observationalDensity
          exact Finset.prod_pos fun i _ => hpos.1 i v hv))]
        rfl
      · exact (measurable_sparseWitness_observationalDensity s).ennreal_ofReal
      · filter_upwards with v
        exact ENNReal.ofReal_lt_top
    _ = _ := by
      rw [hμ, integral_fin_three_pi_eq_iterated _ _ (by simpa [hμ] using hprodInt)]

-- @node: sparseWitness_parent_inner_integral
/-- Integrating the sparse density times its centered parent coordinate over the
child coordinate leaves the centered parent coordinate unchanged.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_parent_inner_integral (s : SignVector 3) (x : ℝ) :
    (∫ y in Set.Icc (0 : ℝ) 1,
      (1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y)) *
        centeredCoordinate (reflectedCoordinate s 0 x)) =
      centeredCoordinate (reflectedCoordinate s 0 x) := by
  let A := centeredCoordinate (reflectedCoordinate s 0 x)
  let B : ℝ → ℝ := fun y => centeredCoordinate (reflectedCoordinate s 1 y)
  have hB : Continuous B := continuous_reflectedCenteredCoordinate s 1
  have h1 : IntegrableOn (fun y => A * B y) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.mul hB).continuousOn.integrableOn_Icc
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

-- @node: sparseWitness_child_inner_integral
/-- Integrating the sparse density times the centered child coordinate produces
one thirtieth of the centered parent coordinate.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_child_inner_integral (s : SignVector 3) (x : ℝ) :
    (∫ y in Set.Icc (0 : ℝ) 1,
      (1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y)) *
        centeredCoordinate (reflectedCoordinate s 1 y)) =
      (1 / 30 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) := by
  let A := centeredCoordinate (reflectedCoordinate s 0 x)
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

-- @node: sparseWitness_joint_inner_integral
/-- Integrating the sparse density times both centered edge coordinates over the
child coordinate produces one thirtieth of the squared parent coordinate.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_joint_inner_integral (s : SignVector 3) (x : ℝ) :
    (∫ y in Set.Icc (0 : ℝ) 1,
      (1 + (1 / 10 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y)) *
        (centeredCoordinate (reflectedCoordinate s 0 x) *
          centeredCoordinate (reflectedCoordinate s 1 y))) =
      (1 / 30 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) ^ 2 := by
  let A := centeredCoordinate (reflectedCoordinate s 0 x)
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
    MeasureTheory.integral_const_mul,
    centeredCoordinate_reflected_integral,
    centeredCoordinate_reflected_sq_integral]
  dsimp only [A]
  ring

-- @node: sparseWitness_centered_marginal_zero
/-- Each reflected centered endpoint has zero mean under the sparse observational law.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_centered_marginal_zero (s : SignVector 3) (i : Fin 2) :
    (∫ v, centeredCoordinate (reflectedCoordinate s i.castSucc (v i.castSucc))
      ∂observationalLaw (sparseWitness s)) = 0 := by
  rw [sparseWitness_integral_eq_iterated]
  · fin_cases i
    · simp [observationalDensity, sparseWitness, sparseP]
      calc
        _ = ∫ x in Set.Icc (0 : ℝ) 1,
            centeredCoordinate (reflectedCoordinate s 0 x) := by
          apply integral_congr_ae
          filter_upwards with x
          simpa [one_div] using sparseWitness_parent_inner_integral s x
        _ = 0 := centeredCoordinate_reflected_integral s 0
    · simp [observationalDensity, sparseWitness, sparseP]
      calc
        _ = ∫ x in Set.Icc (0 : ℝ) 1,
            (1 / 30 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) := by
          apply integral_congr_ae
          filter_upwards with x
          simpa [one_div] using sparseWitness_child_inner_integral s x
        _ = 0 := by
          rw [MeasureTheory.integral_const_mul,
            centeredCoordinate_reflected_integral, mul_zero]
  · apply Continuous.continuousOn
    exact (continuous_reflectedCenteredCoordinate s i.castSucc).comp
      (continuous_apply i.castSucc)

-- @node: sparseWitness_centered_jointMoment
/-- The two reflected centered edge coordinates have the exact positive sparse-law
joint moment `1/90`.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_centered_jointMoment (s : SignVector 3) :
    (∫ v,
      centeredCoordinate (reflectedCoordinate s 0 (v 0)) *
        centeredCoordinate (reflectedCoordinate s 1 (v 1))
      ∂observationalLaw (sparseWitness s)) = 1 / 90 := by
  rw [sparseWitness_integral_eq_iterated]
  · simp [observationalDensity, sparseWitness, sparseP]
    calc
      _ = ∫ x in Set.Icc (0 : ℝ) 1,
          (1 / 30 : ℝ) * centeredCoordinate (reflectedCoordinate s 0 x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        simpa [one_div] using sparseWitness_joint_inner_integral s x
      _ = 1 / 90 := by
        rw [MeasureTheory.integral_const_mul,
          centeredCoordinate_reflected_sq_integral]
        norm_num
    norm_num
  · apply Continuous.continuousOn
    exact ((continuous_reflectedCenteredCoordinate s 0).comp (continuous_apply 0)).mul
      ((continuous_reflectedCenteredCoordinate s 1).comp (continuous_apply 1))

-- @node: sparseWitness_not_condIndep_edge
/-- The exact nonzero centered cross-moment rules out independence of the sparse
witness's unique adjacent coordinate pair.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_not_condIndep_edge (s : SignVector 3) :
    ¬ CondIndepCoordinates (sparseWitness s) {0} {1} ∅ := by
  intro hCI
  letI : IsProbabilityMeasure (observationalLaw (sparseWitness s)) :=
    observationalLaw_isProbabilityMeasure (sparseWitness_positive_normalized_smooth s)
  have hblocks := indepFun_of_condIndepCoordinates_empty
    ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3)) hCI
  let z0 : {j // j ∈ ({0} : Finset (Fin 3))} := ⟨0, by simp⟩
  let z1 : {j // j ∈ ({1} : Finset (Fin 3))} := ⟨1, by simp⟩
  let left : ((j : {j // j ∈ ({0} : Finset (Fin 3))}) → ℝ) → ℝ :=
    fun z => centeredCoordinate (reflectedCoordinate s 0 (z z0))
  let right : ((j : {j // j ∈ ({1} : Finset (Fin 3))}) → ℝ) → ℝ :=
    fun z => centeredCoordinate (reflectedCoordinate s 1 (z z1))
  have hleft : Measurable left := by
    unfold left
    exact (continuous_reflectedCenteredCoordinate s 0).measurable.comp
      (measurable_pi_apply z0)
  have hright : Measurable right := by
    unfold right
    exact (continuous_reflectedCenteredCoordinate s 1).measurable.comp
      (measurable_pi_apply z1)
  have hindRaw := hblocks.comp hleft hright
  have hind : IndepFun
      (fun v : LatentState 3 => centeredCoordinate (reflectedCoordinate s 0 (v 0)))
      (fun v : LatentState 3 => centeredCoordinate (reflectedCoordinate s 1 (v 1)))
      (observationalLaw (sparseWitness s)) := by
    convert hindRaw using 1 <;> funext v <;> rfl
  have hmul := hind.integral_fun_mul_eq_mul_integral
    ((continuous_reflectedCenteredCoordinate s 0).measurable.comp
      (measurable_pi_apply 0)).aestronglyMeasurable
    ((continuous_reflectedCenteredCoordinate s 1).measurable.comp
      (measurable_pi_apply 1)).aestronglyMeasurable
  have hm0 : (∫ v, centeredCoordinate (reflectedCoordinate s 0 (v 0))
      ∂observationalLaw (sparseWitness s)) = 0 := by
    simpa using sparseWitness_centered_marginal_zero s (0 : Fin 2)
  have hm1 : (∫ v, centeredCoordinate (reflectedCoordinate s 1 (v 1))
      ∂observationalLaw (sparseWitness s)) = 0 := by
    simpa using sparseWitness_centered_marginal_zero s (1 : Fin 2)
  rw [sparseWitness_centered_jointMoment, hm0, hm1] at hmul
  norm_num at hmul

-- @node: sparseWitness_causalMinimality
/-- The sparse witness is causally minimal for the one-edge three-node DAG.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_causalMinimality (s : SignVector 3) :
    CausalMinimality threeNodeDAG (sparseWitness s) := by
  intro j i hji
  rcases hji with ⟨rfl, rfl⟩
  intro hCI
  apply sparseWitness_not_condIndep_edge s
  have hparents : (threeNodeDAG.parents 1).erase 0 = ∅ := by
    ext k
    fin_cases k <;> simp [threeNodeDAG, threeNodeEdge, Causalean.DAG.parents]
  rw [hparents] at hCI
  have hsymm := condIndepCoordinates_symm hCI
  exact hsymm

-- @node: sparseWitness_faithfulness
/-- The sparse witness is faithful to `0 → 1` with isolated node `2`.  [the stated conclusion](goal) follows. -/
lemma sparseWitness_faithfulness (s : SignVector 3) :
    Faithfulness threeNodeDAG (sparseWitness s) := by
  exact threeNodeDAG_faithful_of_causalMinimality
    (sparseWitness_positive_normalized_smooth s)
    (sparseWitness_causalMinimality s)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
