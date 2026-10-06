module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveInputs
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotGrowth
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiniteOracle
public import Causalean.Mathlib.Optimization.QuadraticSaddle.Continuity

/-! # Continuity of the private-pilot oracle value and adaptive variance -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter
open scoped Topology BigOperators
open Causalean.Mathlib.Optimization.QuadraticSaddle

private def adaptiveToWeight (α : EuclideanSpace ℝ (Fin 14)) : StaircaseWeight :=
  EuclideanSpace.equiv (Fin 14) ℝ α

private def adaptiveOfWeight (α : StaircaseWeight) : EuclideanSpace ℝ (Fin 14) :=
  (EuclideanSpace.equiv (Fin 14) ℝ).symm α

@[simp] private lemma adaptiveToWeight_adaptiveOfWeight (α : StaircaseWeight) :
    adaptiveToWeight (adaptiveOfWeight α) = α :=
  (EuclideanSpace.equiv (Fin 14) ℝ).apply_symm_apply α

@[simp] private lemma adaptiveOfWeight_adaptiveToWeight
    (α : EuclideanSpace ℝ (Fin 14)) :
    adaptiveOfWeight (adaptiveToWeight α) = α :=
  (EuclideanSpace.equiv (Fin 14) ℝ).symm_apply_apply α

@[simp] private lemma adaptiveToWeight_apply
    (α : EuclideanSpace ℝ (Fin 14)) (s : Fin 14) :
    adaptiveToWeight α s = α s := rfl

/-- For the supplied quantities and conditions, the adaptive pilot polytope is the mathematical object specified below. [The adaptive Pilot Polytope](goal) is determined by [the displayed parameters](hyp:ε,hε). -/
def adaptivePilotPolytope (ε : ℝ) (hε : 0 ≤ ε) :
    Polytope (Fin 14) (Fin 4) where
  A j s := patternRay ε s j
  b _ := 1
  compact := by
    have hc := (staircaseFeasible_compact ε hε).image
      (EuclideanSpace.equiv (Fin 14) ℝ).symm.continuous
    convert hc using 1
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_image, feasibleSet]
    constructor
    · rintro ⟨hn, heq⟩
      refine ⟨adaptiveToWeight α, ⟨hn, ?_⟩,
        adaptiveOfWeight_adaptiveToWeight α⟩
      intro j
      simpa [adaptiveToWeight, staircaseMatrix, mul_comm] using heq j
    · rintro ⟨β, ⟨hn, heq⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [adaptiveOfWeight, adaptiveToWeight] using hn
      · intro j
        simpa [adaptiveOfWeight, adaptiveToWeight, staircaseMatrix, mul_comm]
          using heq j
  nonempty := by
    obtain ⟨α, hα⟩ := staircaseFeasible_nonempty ε
    refine ⟨adaptiveOfWeight α, ?_, ?_⟩
    · simpa [adaptiveOfWeight, adaptiveToWeight] using hα.1
    · intro j
      simpa [adaptiveOfWeight, adaptiveToWeight, staircaseMatrix, mul_comm]
        using hα.2 j

private lemma measurable_adaptivePatternMass_subtype (p ε : ℝ) (s : Fin 14) :
    Measurable (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
      patternMass θ.1 p ε s) := by
  unfold patternMass
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul
  · fin_cases j
    · change Measurable (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        (1 - p) * (1 - θ.1 0))
      exact measurable_const.mul (measurable_const.sub
        ((measurable_pi_apply 0).comp measurable_subtype_coe))
    · change Measurable (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        (1 - p) * θ.1 0)
      exact measurable_const.mul
        ((measurable_pi_apply 0).comp measurable_subtype_coe)
    · change Measurable (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        p * (1 - θ.1 1))
      exact measurable_const.mul (measurable_const.sub
        ((measurable_pi_apply 1).comp measurable_subtype_coe))
    · change Measurable (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        p * θ.1 1)
      exact measurable_const.mul
        ((measurable_pi_apply 1).comp measurable_subtype_coe)
  · exact measurable_const

/-- For the supplied quantities and conditions, the adaptive pilot quadratics is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Quadratics](goal) is determined by [the displayed parameters](hyp:p,ε,hp,hε). -/
def adaptivePilotQuadratics (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 ≤ ε) :
    Quadratics {θ : TrialParameter // InteriorMeans θ} (Fin 14) where
  a s θ := (patternGradient p ε s 0 + patternGradient p ε s 1) ^ 2 /
    patternMass θ.1 p ε s
  b s θ := 2 * (patternGradient p ε s 0 + patternGradient p ε s 1) *
    patternGradient p ε s 1 / patternMass θ.1 p ε s
  c s θ := (patternGradient p ε s 1) ^ 2 / patternMass θ.1 p ε s
  measurable_a := by
    intro s
    exact measurable_const.div (measurable_adaptivePatternMass_subtype p ε s)
  measurable_b := by
    intro s
    exact measurable_const.div (measurable_adaptivePatternMass_subtype p ε s)
  measurable_c := by
    intro s
    exact measurable_const.div (measurable_adaptivePatternMass_subtype p ε s)
  nonneg_a := by
    intro θ s
    exact div_nonneg (sq_nonneg _)
      (patternMass_pos_interior θ.1 p ε hp θ.2 hε s).le

private lemma adaptivePilotQuadratics_objective (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 ≤ ε)
    (θ : {θ : TrialParameter // InteriorMeans θ})
    (α : EuclideanSpace ℝ (Fin 14)) (t : ℝ) :
    (adaptivePilotQuadratics p ε hp hε).objective θ α t =
      informationObjective θ.1 p ε (adaptiveToWeight α) t := by
  unfold Quadratics.objective informationObjective patternInformation
  apply Finset.sum_congr rfl
  intro s _
  unfold adaptivePilotQuadratics projectedGradient direction
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, if_false, adaptiveToWeight_apply]
  ring

private lemma adaptivePilotPolytope_weights (ε : ℝ) (hε : 0 ≤ ε)
    (α : EuclideanSpace ℝ (Fin 14)) :
    α ∈ (adaptivePilotPolytope ε hε).weights ↔
      staircaseFeasible ε (adaptiveToWeight α) := by
  constructor
  · rintro ⟨hn, heq⟩
    refine ⟨?_, ?_⟩
    · simpa [adaptiveToWeight] using hn
    · intro j
      simpa [adaptivePilotPolytope, staircaseMatrix, adaptiveToWeight, mul_comm]
        using heq j
  · rintro ⟨hn, heq⟩
    refine ⟨?_, ?_⟩
    · simpa [adaptiveToWeight] using hn
    · intro j
      simpa [adaptivePilotPolytope, staircaseMatrix, adaptiveToWeight, mul_comm]
        using heq j

private lemma adaptivePilot_selected_isSaddle (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : {θ : TrialParameter // InteriorMeans θ}) :
    IsSaddle (adaptivePilotPolytope ε hε.le)
      (adaptivePilotQuadratics p ε hp hε.le) θ
      (adaptiveOfWeight (select θ.1).1)
      (select θ.1).2.1 := by
  let select := select
  have hs := (hselect.1).2 θ.1 θ.2
  refine ⟨(adaptivePilotPolytope_weights ε hε.le _).2 (by simpa [select] using hs.1),
    ?_, ?_⟩
  · intro u
    rw [adaptivePilotQuadratics_objective,
      adaptivePilotQuadratics_objective]
    simpa [select] using hs.2.1 u
  · intro β hβ
    rw [adaptivePilotQuadratics_objective,
      adaptivePilotQuadratics_objective]
    simpa [select] using (hselect).2 θ.1 θ.2
      (adaptiveToWeight β) ((adaptivePilotPolytope_weights ε hε.le β).1 hβ)

/-- Under the supplied quantities and conditions, the jstar eq adaptive quadratic value assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε), [the Jstar eq adaptive Quadratic Value](goal).

Under the stated assumptions, the Jstar eq adaptive Quadratic Value. -/
lemma Jstar_eq_adaptiveQuadraticValue (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : {θ : TrialParameter // InteriorMeans θ}) :
    Jstar θ.1 p ε = value (adaptivePilotPolytope ε hε.le)
      (adaptivePilotQuadratics p ε hp hε.le) θ := by
  let select := select
  have hsaddle := adaptivePilot_selected_isSaddle select p ε hselect hp hε θ
  rw [value_eq_of_isSaddle _ _ _ _ _ hsaddle,
    adaptivePilotQuadratics_objective]
  simp only [adaptiveToWeight_adaptiveOfWeight]
  have hs := (hselect.1).2 θ.1 θ.2
  exact hs.2.2.1.trans hs.2.2.2

private lemma continuous_adaptivePatternMass_subtype (p ε : ℝ) (s : Fin 14) :
    Continuous (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
      patternMass θ.1 p ε s) := by
  unfold patternMass
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul
  · fin_cases j
    · change Continuous (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        (1 - p) * (1 - θ.1 0))
      exact continuous_const.mul (continuous_const.sub
        ((continuous_apply 0).comp continuous_subtype_val))
    · change Continuous (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        (1 - p) * θ.1 0)
      exact continuous_const.mul
        ((continuous_apply 0).comp continuous_subtype_val)
    · change Continuous (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        p * (1 - θ.1 1))
      exact continuous_const.mul (continuous_const.sub
        ((continuous_apply 1).comp continuous_subtype_val))
    · change Continuous (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        p * θ.1 1)
      exact continuous_const.mul
        ((continuous_apply 1).comp continuous_subtype_val)
  · exact continuous_const

private lemma continuous_adaptivePilotQuadratics_objective (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    Continuous (fun x :
      (({θ : TrialParameter // InteriorMeans θ} × ℝ) ×
        EuclideanSpace ℝ (Fin 14)) =>
      (adaptivePilotQuadratics p ε hp hε.le).objective x.1.1 x.2 x.1.2) := by
  let Q := adaptivePilotQuadratics p ε hp hε.le
  have ha (s : Fin 14) : Continuous (Q.a s) := by
    exact continuous_const.div (continuous_adaptivePatternMass_subtype p ε s)
      (fun θ => ne_of_gt
        (patternMass_pos_interior θ.1 p ε hp θ.2 hε.le s))
  have hb (s : Fin 14) : Continuous (Q.b s) := by
    exact continuous_const.div (continuous_adaptivePatternMass_subtype p ε s)
      (fun θ => ne_of_gt
        (patternMass_pos_interior θ.1 p ε hp θ.2 hε.le s))
  have hc (s : Fin 14) : Continuous (Q.c s) := by
    exact continuous_const.div (continuous_adaptivePatternMass_subtype p ε s)
      (fun θ => ne_of_gt
        (patternMass_pos_interior θ.1 p ε hp θ.2 hε.le s))
  unfold Quadratics.objective
  apply continuous_finset_sum
  intro s _
  exact (((EuclideanSpace.proj (𝕜 := ℝ) s).continuous.comp continuous_snd).mul
    (((((ha s).comp (continuous_fst.comp continuous_fst)).mul
      ((continuous_snd.comp continuous_fst).pow 2)).add
      (((hb s).comp (continuous_fst.comp continuous_fst)).mul
        (continuous_snd.comp continuous_fst))).add
      ((hc s).comp (continuous_fst.comp continuous_fst))))

private lemma isOpen_interiorMeans : IsOpen {θ : TrialParameter | InteriorMeans θ} := by
  change IsOpen {θ : TrialParameter |
    0 < θ 0 ∧ θ 0 < 1 ∧ 0 < θ 1 ∧ θ 1 < 1}
  have h0l : IsOpen {θ : TrialParameter | (0 : ℝ) < θ 0} :=
    isOpen_lt continuous_const (continuous_apply 0)
  have h0r : IsOpen {θ : TrialParameter | θ 0 < (1 : ℝ)} :=
    isOpen_lt (continuous_apply 0) continuous_const
  have h1l : IsOpen {θ : TrialParameter | (0 : ℝ) < θ 1} :=
    isOpen_lt continuous_const (continuous_apply 1)
  have h1r : IsOpen {θ : TrialParameter | θ 1 < (1 : ℝ)} :=
    isOpen_lt (continuous_apply 1) continuous_const
  convert ((h0l.inter h0r).inter h1l).inter h1r using 1 <;>
    ext θ <;> simp [and_assoc]

/-- Under the supplied quantities and conditions, the continuous at jstar assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε), [the continuous At Jstar](goal).

Under the stated assumptions, the continuous At Jstar. -/
lemma continuousAt_Jstar (θ : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ContinuousAt (fun η => Jstar η p ε) θ := by
  let Θ := {η : TrialParameter // InteriorMeans η}
  let θ0 : Θ := ⟨θ, hθ⟩
  let B := pilotTUpper p ε
  let K : Set ℝ := Set.Icc (-B) B
  have hB : 0 ≤ B := by
    unfold B pilotTUpper
    exact Real.sqrt_nonneg _
  have hatt : {η : Θ | ∃ α : EuclideanSpace ℝ (Fin 14),
      ∃ t ∈ K, IsSaddle (adaptivePilotPolytope ε hε.le)
        (adaptivePilotQuadratics p ε hp hε.le) η α t} ∈ nhds θ0 := by
    filter_upwards [] with η
    let select := select
    refine ⟨adaptiveOfWeight (select η.1).1, (select η.1).2.1, ?_, ?_⟩
    · have ht := strongSelector_t_bound select
        (hselect) hp hε η.1 η.2
      exact (abs_le.mp ht)
    · exact adaptivePilot_selected_isSaddle select p ε hselect hp hε η
  have hvalue : ContinuousAt
      (value (adaptivePilotPolytope ε hε.le)
        (adaptivePilotQuadratics p ε hp hε.le)) θ0 := by
    apply continuousAt_quadratic_value
      (adaptivePilotPolytope ε hε.le)
      (adaptivePilotQuadratics p ε hp hε.le) K
      (isCompact_Icc) ⟨0, by simpa [K] using hB⟩ θ0 Set.univ
      isOpen_univ (Set.mem_univ θ0)
    · exact (continuous_adaptivePilotQuadratics_objective p ε hp hε).continuousOn
    · exact hatt
  have hsub : ContinuousAt (fun η : Θ => Jstar η.1 p ε) θ0 := by
    apply hvalue.congr_of_eventuallyEq
    filter_upwards [] with η
    exact Jstar_eq_adaptiveQuadraticValue select p ε hselect hp hε η
  have hwithin : ContinuousWithinAt (fun η => Jstar η p ε)
      {η | InteriorMeans η} θ := by
    apply (continuousWithinAt_iff_continuousAt_domRestrict
      (f := fun η => Jstar η p ε)
      (s := {η | InteriorMeans η}) hθ).2
    change ContinuousAt
      (fun η : {η : TrialParameter // InteriorMeans η} => Jstar η.1 p ε)
      ⟨θ, hθ⟩
    simpa only [Θ, θ0] using hsub
  exact hwithin.continuousAt (isOpen_interiorMeans.mem_nhds hθ)

/-- Under the supplied quantities and conditions, the continuous at vstar assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε), [the continuous At Vstar](goal).

Under the stated assumptions, the continuous At Vstar. -/
lemma continuousAt_Vstar (θ : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ContinuousAt (fun η => Vstar η p ε) θ := by
  change ContinuousAt ((fun η => Jstar η p ε)⁻¹) θ
  exact (continuousAt_Jstar select θ p ε hselect hp hθ hε).inv₀
    (ne_of_gt (Jstar_pos_interior θ p ε hp hθ hε))

private lemma continuous_adaptivePatternMass (p ε : ℝ) (s : Fin 14) :
    Continuous (fun θ : TrialParameter => patternMass θ p ε s) := by
  unfold patternMass
  apply continuous_finset_sum
  intro j _
  apply Continuous.mul
  · fin_cases j
    · change Continuous (fun θ : TrialParameter => (1 - p) * (1 - θ 0))
      fun_prop
    · change Continuous (fun θ : TrialParameter => (1 - p) * θ 0)
      fun_prop
    · change Continuous (fun θ : TrialParameter => p * (1 - θ 1))
      fun_prop
    · change Continuous (fun θ : TrialParameter => p * θ 1)
      fun_prop
  · exact continuous_const

private lemma adaptiveScoreVariance_diag_error_le
    (θ' η : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ' : InteriorMeans θ')
    (hη : InteriorMeans η) (hε : 0 < ε) :
    |adaptiveScoreVariance select θ' η p ε - Vstar η p ε| ≤
      (pilotPhiUpper p ε) ^ 2 *
        ∑ s : Fin 14, |patternMass θ' p ε s - patternMass η p ε s| +
      (contrast θ' - contrast η) ^ 2 := by
  let select := select
  let α := (select η).1
  let φ := adaptiveSelectedScore select η p ε
  let B := pilotPhiUpper p ε
  have hsel := (hselect.1).2 η hη
  have hB : 0 ≤ B := pilotPhiUpper_nonneg p ε hp hε
  have hαnonneg (s : Fin 14) : 0 ≤ α s := hsel.1.1 s
  have hαone (s : Fin 14) : α s ≤ 1 :=
    staircaseWeight_le_one ε hε.le α hsel.1 s
  have hφsq (s : Fin 14) : (φ s) ^ 2 ≤ B ^ 2 := by
    have hab := adaptiveSelectedScore_abs_le select η p ε hselect hp hη hε s
    rw [← sq_abs (φ s)]
    exact (sq_le_sq₀ (abs_nonneg _) hB).2 hab
  have hcoef (s : Fin 14) : 0 ≤ α s * (φ s) ^ 2 ∧
      α s * (φ s) ^ 2 ≤ B ^ 2 := by
    constructor
    · exact mul_nonneg (hαnonneg s) (sq_nonneg _)
    · nlinarith [hαone s, hφsq s, sq_nonneg (φ s), sq_nonneg B]
  have heq : adaptiveScoreVariance select θ' η p ε - Vstar η p ε =
      (∑ s : Fin 14, α s *
        (patternMass θ' p ε s - patternMass η p ε s) * (φ s) ^ 2) -
        (contrast θ' - contrast η) ^ 2 := by
    rw [← adaptiveScoreVariance_diag select η p ε hselect hp hη hε]
    unfold adaptiveScoreVariance adaptiveMainMass
    simp only [sub_self, α, φ, select]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero]
    have hsum :
        (∑ s : Fin 14, (select η).1 s *
            patternMass θ' p ε s * (adaptiveSelectedScore select η p ε s) ^ 2) -
          ∑ s : Fin 14, (select η).1 s *
            patternMass η p ε s * (adaptiveSelectedScore select η p ε s) ^ 2 =
        ∑ s : Fin 14, (select η).1 s *
          (patternMass θ' p ε s - patternMass η p ε s) *
            (adaptiveSelectedScore select η p ε s) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [← hsum]
    ring
  rw [heq]
  calc
    |(∑ s : Fin 14, α s *
        (patternMass θ' p ε s - patternMass η p ε s) * (φ s) ^ 2) -
        (contrast θ' - contrast η) ^ 2| ≤
        |∑ s : Fin 14, α s *
          (patternMass θ' p ε s - patternMass η p ε s) * (φ s) ^ 2| +
          |(contrast θ' - contrast η) ^ 2| := abs_sub _ _
    _ ≤ ∑ s : Fin 14, |α s *
          (patternMass θ' p ε s - patternMass η p ε s) * (φ s) ^ 2| +
          (contrast θ' - contrast η) ^ 2 := by
      rw [abs_sq]
      exact add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ ∑ s : Fin 14, B ^ 2 *
          |patternMass θ' p ε s - patternMass η p ε s| +
          (contrast θ' - contrast η) ^ 2 := by
      apply add_le_add _ le_rfl
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_mul, abs_of_nonneg (hαnonneg s), abs_sq]
      calc
        α s * |patternMass θ' p ε s - patternMass η p ε s| *
            φ s ^ 2 = (α s * φ s ^ 2) *
              |patternMass θ' p ε s - patternMass η p ε s| := by ring
        _ ≤ B ^ 2 * |patternMass θ' p ε s - patternMass η p ε s| :=
          mul_le_mul_of_nonneg_right (hcoef s).2 (abs_nonneg _)
    _ = B ^ 2 * ∑ s : Fin 14,
          |patternMass θ' p ε s - patternMass η p ε s| +
          (contrast θ' - contrast η) ^ 2 := by
      rw [Finset.mul_sum]

/-- Under the supplied quantities and conditions, the continuous at adaptive score variance diag assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε), [the continuous At adaptive Score Variance diag](goal).

Under the stated assumptions, the continuous At adaptive Score Variance diag. -/
lemma continuousAt_adaptiveScoreVariance_diag
    (θ : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ContinuousAt (fun pair : TrialParameter × TrialParameter =>
      adaptiveScoreVariance select pair.1 pair.2 p ε) (θ, θ) := by
  let B := pilotPhiUpper p ε
  let g : TrialParameter × TrialParameter → ℝ := fun q =>
    B ^ 2 * ∑ s : Fin 14,
      |patternMass q.1 p ε s - patternMass q.2 p ε s| +
      (contrast q.1 - contrast q.2) ^ 2
  have hgcont : Continuous g := by
    unfold g
    apply Continuous.add
    · apply Continuous.mul continuous_const
      apply continuous_finset_sum
      intro s _
      exact (((continuous_adaptivePatternMass p ε s).comp continuous_fst).sub
        ((continuous_adaptivePatternMass p ε s).comp continuous_snd)).abs
    · unfold contrast
      fun_prop
  have hgzero : g (θ, θ) = 0 := by simp [g]
  have hinterior : {q : TrialParameter × TrialParameter |
      InteriorMeans q.1 ∧ InteriorMeans q.2} ∈ nhds (θ, θ) := by
    have hopen := isOpen_interiorMeans.prod isOpen_interiorMeans
    exact hopen.mem_nhds ⟨hθ, hθ⟩
  let f : TrialParameter × TrialParameter → ℝ := fun q =>
    adaptiveScoreVariance select q.1 q.2 p ε - Vstar q.2 p ε
  have hbound : {q : TrialParameter × TrialParameter | ‖f q‖ ≤ g q} ∈
      nhds (θ, θ) := by
    filter_upwards [hinterior] with q hq
    rw [Real.norm_eq_abs]
    exact adaptiveScoreVariance_diag_error_le select q.1 q.2 p ε hselect hp hq.1 hq.2 hε
  have hgtend : Tendsto g (nhds (θ, θ)) (nhds 0) := by
    rw [← hgzero]
    exact hgcont.continuousAt
  have hftend : Tendsto f (nhds (θ, θ)) (nhds 0) :=
    squeeze_zero_norm' hbound hgtend
  have hv : ContinuousAt (fun q : TrialParameter × TrialParameter =>
      Vstar q.2 p ε) (θ, θ) :=
    by
      have hsnd : ContinuousAt
          (fun q : TrialParameter × TrialParameter => q.2) (θ, θ) :=
        continuousAt_snd
      change ContinuousAt ((fun η => Vstar η p ε) ∘
        (fun q : TrialParameter × TrialParameter => q.2)) (θ, θ)
      exact (continuousAt_Vstar select θ p ε hselect hp hθ hε).comp hsnd
  have hsum := hftend.add hv
  change Tendsto (fun pair : TrialParameter × TrialParameter =>
    adaptiveScoreVariance select pair.1 pair.2 p ε) (nhds (θ, θ))
      (nhds (adaptiveScoreVariance select θ θ p ε))
  rw [adaptiveScoreVariance_diag select θ p ε hselect hp hθ hε]
  simpa only [f, zero_add, sub_add_cancel] using hsum

end CausalSmith.Stat.LdpAteEfficiencySurface
