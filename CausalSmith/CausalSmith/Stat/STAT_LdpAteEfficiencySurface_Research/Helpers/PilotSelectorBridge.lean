module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotBridge
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiniteOracle
public import Causalean.Mathlib.Optimization.QuadraticSaddle.Selection

/-! # Measurable finite-quadratic selector adapter -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Mathlib.Optimization.QuadraticSaddle

private def toWeight (α : EuclideanSpace ℝ (Fin 14)) : StaircaseWeight :=
  EuclideanSpace.equiv (Fin 14) ℝ α

private def ofWeight (α : StaircaseWeight) : EuclideanSpace ℝ (Fin 14) :=
  (EuclideanSpace.equiv (Fin 14) ℝ).symm α

@[simp] private lemma toWeight_ofWeight (α : StaircaseWeight) :
    toWeight (ofWeight α) = α := (EuclideanSpace.equiv (Fin 14) ℝ).apply_symm_apply α

@[simp] private lemma ofWeight_toWeight (α : EuclideanSpace ℝ (Fin 14)) :
    ofWeight (toWeight α) = α := (EuclideanSpace.equiv (Fin 14) ℝ).symm_apply_apply α

@[simp] private lemma toWeight_apply (α : EuclideanSpace ℝ (Fin 14)) (s : Fin 14) :
    toWeight α s = α s := rfl

private def pilotPolytope (ε : ℝ) (hε : 0 ≤ ε) : Polytope (Fin 14) (Fin 4) where
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
      refine ⟨toWeight α, ⟨hn, ?_⟩, ofWeight_toWeight α⟩
      intro j
      simpa [toWeight, staircaseMatrix, mul_comm] using heq j
    · rintro ⟨β, ⟨hn, heq⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [ofWeight, toWeight] using hn
      · intro j
        simpa [ofWeight, toWeight, staircaseMatrix, mul_comm] using heq j
  nonempty := by
    obtain ⟨α, hα⟩ := staircaseFeasible_nonempty ε
    refine ⟨ofWeight α, ?_, ?_⟩
    · simpa [ofWeight, toWeight] using hα.1
    · intro j
      simpa [ofWeight, toWeight, staircaseMatrix, mul_comm] using hα.2 j

private def pilotLinearCoeff (p ε : ℝ) (s : Fin 14) : ℝ :=
  patternGradient p ε s 0 + patternGradient p ε s 1

private def pilotConstantCoeff (p ε : ℝ) (s : Fin 14) : ℝ :=
  patternGradient p ε s 1

private lemma measurable_patternMass_subtype (p ε : ℝ) (s : Fin 14) :
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
      exact measurable_const.mul ((measurable_pi_apply 0).comp measurable_subtype_coe)
    · change Measurable (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        p * (1 - θ.1 1))
      exact measurable_const.mul (measurable_const.sub
        ((measurable_pi_apply 1).comp measurable_subtype_coe))
    · change Measurable (fun θ : {θ : TrialParameter // InteriorMeans θ} =>
        p * θ.1 1)
      exact measurable_const.mul ((measurable_pi_apply 1).comp measurable_subtype_coe)
  · exact measurable_const

private def pilotQuadratics (p ε : ℝ) (hp : InteriorAssignment p) (hε : 0 ≤ ε) :
    Quadratics {θ : TrialParameter // InteriorMeans θ} (Fin 14) where
  a s θ := pilotLinearCoeff p ε s ^ 2 / patternMass θ.1 p ε s
  b s θ := 2 * pilotLinearCoeff p ε s * pilotConstantCoeff p ε s /
    patternMass θ.1 p ε s
  c s θ := pilotConstantCoeff p ε s ^ 2 / patternMass θ.1 p ε s
  measurable_a s := measurable_const.div (measurable_patternMass_subtype p ε s)
  measurable_b s := measurable_const.div (measurable_patternMass_subtype p ε s)
  measurable_c s := measurable_const.div (measurable_patternMass_subtype p ε s)
  nonneg_a θ s := div_nonneg (sq_nonneg _)
    (patternMass_pos_interior θ.1 p ε hp θ.2 hε s).le

private lemma pilotPolytope_weights (ε : ℝ) (hε : 0 ≤ ε)
    (α : EuclideanSpace ℝ (Fin 14)) :
    α ∈ (pilotPolytope ε hε).weights ↔ staircaseFeasible ε (toWeight α) := by
  constructor
  · rintro ⟨hn, heq⟩
    refine ⟨?_, ?_⟩
    · simpa [toWeight] using hn
    · intro j
      simpa [pilotPolytope, staircaseMatrix, toWeight, mul_comm] using heq j
  · rintro ⟨hn, heq⟩
    refine ⟨?_, ?_⟩
    · simpa [toWeight] using hn
    · intro j
      simpa [pilotPolytope, staircaseMatrix, toWeight, mul_comm] using heq j

private lemma pilotQuadratics_objective (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 ≤ ε)
    (θ : {θ : TrialParameter // InteriorMeans θ})
    (α : EuclideanSpace ℝ (Fin 14)) (t : ℝ) :
    (pilotQuadratics p ε hp hε).objective θ α t =
      informationObjective θ.1 p ε (toWeight α) t := by
  unfold Quadratics.objective informationObjective patternInformation
  apply Finset.sum_congr rfl
  intro s _
  unfold pilotQuadratics pilotLinearCoeff pilotConstantCoeff projectedGradient direction
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, if_false]
  simp only [toWeight_apply]
  ring

private lemma exists_quadratic_saddle (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (θ : {θ : TrialParameter // InteriorMeans θ}) :
    ∃ α t, IsSaddle (pilotPolytope ε hε.le)
      (pilotQuadratics p ε hp hε.le) θ α t := by
  obtain ⟨α, hα, hopt⟩ := Jstar_exists_optimal_weight θ.1 p ε hp θ.2 hε.le
  obtain ⟨t, ht⟩ := upperEnvelope_exists_minimizer θ.1 p ε hp θ.2 hε
  have hleast : sInf {u : ℝ | ∃ v : ℝ, u = upperEnvelope θ.1 p ε v} =
      upperEnvelope θ.1 p ε t := by
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact ht u⟩
  have hJ : upperEnvelope θ.1 p ε t = Jstar θ.1 p ε := by
    rw [← hleast, ← finiteOracle_minimax θ.1 p ε hp θ.2 hε]
  have hbdd : BddBelow {u : ℝ | ∃ v : ℝ,
      u = informationObjective θ.1 p ε α v} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact informationObjective_nonneg_interior θ.1 p ε hp θ.2 hε.le α hα u
  have hlower (u : ℝ) : Jstar θ.1 p ε ≤ informationObjective θ.1 p ε α u := by
    rw [hopt]
    exact csInf_le hbdd ⟨u, rfl⟩
  obtain ⟨z, hz, hzmax⟩ := informationObjective_exists_maximizer θ.1 p ε t hε.le
  have henv : upperEnvelope θ.1 p ε t = informationObjective θ.1 p ε z t := by
    unfold upperEnvelope
    apply IsGreatest.csSup_eq
    exact ⟨⟨z, hz, rfl⟩, by rintro _ ⟨β, hβ, rfl⟩; exact hzmax β hβ⟩
  have hat : informationObjective θ.1 p ε α t = Jstar θ.1 p ε :=
    le_antisymm ((hzmax α hα).trans (by rw [← henv, hJ])) (hlower t)
  refine ⟨ofWeight α, t, (pilotPolytope_weights ε hε.le _).2 ?_, ?_, ?_⟩
  · simpa using hα
  · intro u
    rw [pilotQuadratics_objective, pilotQuadratics_objective]
    simp only [toWeight_ofWeight, hat]
    exact hlower u
  · intro β hβ
    rw [pilotQuadratics_objective, pilotQuadratics_objective]
    simp only [toWeight_ofWeight, hat, ← hJ, henv]
    exact hzmax (toWeight β) ((pilotPolytope_weights ε hε.le β).1 hβ)

private lemma measurableSet_interiorMeans :
    MeasurableSet {θ : TrialParameter | InteriorMeans θ} := by
  rw [show {θ : TrialParameter | InteriorMeans θ} =
      ({θ : TrialParameter | 0 < θ 0} ∩
        ({θ : TrialParameter | θ 0 < 1} ∩
          ({θ : TrialParameter | 0 < θ 1} ∩
            {θ : TrialParameter | θ 1 < 1}))) by ext θ; simp [InteriorMeans]]
  exact (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
    ((measurableSet_lt (measurable_pi_apply 0) measurable_const).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
        (measurableSet_lt (measurable_pi_apply 1) measurable_const)))

/-- Under the supplied quantities and conditions, the exists measurable saddle selector bridge strong assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε), [the exists measurable saddle selector bridge strong](goal).

Under the stated assumptions, the exists measurable saddle selector bridge strong. -/
lemma exists_measurable_saddle_selector_bridge_strong (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    ∃ select : TrialParameter → StaircaseWeight × ℝ × ℝ,
      Measurable select ∧
      ∀ θ, InteriorMeans θ →
        staircaseFeasible ε (select θ).1 ∧
        (∀ u, informationObjective θ p ε (select θ).1 (select θ).2.1 ≤
          informationObjective θ p ε (select θ).1 u) ∧
        Jstar θ p ε = (select θ).2.2 ∧
        (select θ).2.2 =
          informationObjective θ p ε (select θ).1 (select θ).2.1 ∧
        (∀ β, staircaseFeasible ε β →
          informationObjective θ p ε β (select θ).2.1 ≤
            informationObjective θ p ε (select θ).1 (select θ).2.1) := by
  classical
  let Θ := {θ : TrialParameter // InteriorMeans θ}
  letI : StandardBorelSpace Θ := measurableSet_interiorMeans.standardBorel
  have hatt : ∀ θ : Θ, θ ∈ Set.univ → ∃ α t,
      IsSaddle (pilotPolytope ε hε.le) (pilotQuadratics p ε hp hε.le) θ α t :=
    fun θ _ => exists_quadratic_saddle p ε hp hε θ
  obtain ⟨α, t, hαm, htm, hs⟩ := exists_measurable_saddle_on
    (pilotPolytope ε hε.le) (pilotQuadratics p ε hp hε.le)
    Set.univ MeasurableSet.univ hatt
  let lift : Θ → (Set.univ : Set Θ) := fun x => ⟨x, Set.mem_univ x⟩
  have hlift : Measurable lift := by
    dsimp [lift]
    fun_prop
  let αD : Θ → EuclideanSpace ℝ (Fin 14) := α ∘ lift
  let tD : Θ → ℝ := t ∘ lift
  have hαD : Measurable αD := hαm.comp hlift
  have htD : Measurable tD := htm.comp hlift
  let policyD : Θ → StaircaseWeight × ℝ × ℝ := fun x =>
    (toWeight (αD x), tD x,
      (pilotQuadratics p ε hp hε.le).objective x (αD x) (tD x))
  have hpolicyD : Measurable policyD := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro s
      exact ((EuclideanSpace.proj (𝕜 := ℝ) s).continuous.measurable.comp hαD)
    · exact htD.prodMk ((pilotQuadratics p ε hp hε.le).measurable_objective.comp
        (measurable_id.prodMk (hαD.prodMk htD)))
  let select : TrialParameter → StaircaseWeight × ℝ × ℝ := fun θ =>
    if hθ : InteriorMeans θ then
      policyD ⟨θ, hθ⟩
    else (0, 0, 0)
  have hselect : Measurable select := by
    exact Measurable.dite hpolicyD measurable_const measurableSet_interiorMeans
  refine ⟨select, hselect, ?_⟩
  intro θ hθ
  let x : Θ := ⟨θ, hθ⟩
  let xu : (Set.univ : Set Θ) := ⟨x, Set.mem_univ x⟩
  have hsx := hs xu
  have hfeasSel : staircaseFeasible ε (toWeight (α xu)) :=
    (pilotPolytope_weights ε hε.le _).1 hsx.1
  have hupper : ∀ z ∈ {z : ℝ | ∃ β : StaircaseWeight,
      staircaseFeasible ε β ∧
      z = sInf {y : ℝ | ∃ u : ℝ, y = informationObjective θ p ε β u}},
      z ≤ informationObjective θ p ε (toWeight (α xu)) (t xu) := by
    rintro _ ⟨β, hβ, rfl⟩
    have hb : BddBelow {u : ℝ | ∃ v : ℝ,
        u = informationObjective θ p ε β v} := by
      refine ⟨0, ?_⟩
      rintro _ ⟨u, rfl⟩
      exact informationObjective_nonneg_interior θ p ε hp hθ hε.le β hβ u
    calc
      sInf {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε β v} ≤
          informationObjective θ p ε β (t xu) := csInf_le hb ⟨t xu, rfl⟩
      _ ≤ informationObjective θ p ε (toWeight (α xu)) (t xu) := by
        have hh := hsx.2.2 (ofWeight β)
          ((pilotPolytope_weights ε hε.le _).2 (by simpa))
        rw [pilotQuadratics_objective, pilotQuadratics_objective] at hh
        simpa [x, xu] using hh
  have hne : {z : ℝ | ∃ β : StaircaseWeight, staircaseFeasible ε β ∧
      z = sInf {y : ℝ | ∃ u : ℝ, y = informationObjective θ p ε β u}}.Nonempty :=
    ⟨sInf {y : ℝ | ∃ u : ℝ,
      y = informationObjective θ p ε (toWeight (α xu)) u},
      toWeight (α xu), hfeasSel, rfl⟩
  have hj : Jstar θ p ε = (pilotQuadratics p ε hp hε.le).objective x
      (α xu) (t xu) := by
    rw [pilotQuadratics_objective]
    apply le_antisymm
    · rw [Jstar]
      apply csSup_le
      · exact hne
      · exact hupper
    · rw [Jstar]
      apply le_csSup
      · exact ⟨_, hupper⟩
      · refine ⟨toWeight (α xu), (pilotPolytope_weights ε hε.le _).1 hsx.1, ?_⟩
        symm
        apply IsLeast.csInf_eq
        refine ⟨⟨t xu, rfl⟩, ?_⟩
        rintro _ ⟨u, rfl⟩
        have hh := hsx.2.1 u
        rw [pilotQuadratics_objective, pilotQuadratics_objective] at hh
        simpa [x, xu] using hh
  simp only [select, hθ, dite_true, policyD, αD, tD, lift, Function.comp_apply]
  refine ⟨(pilotPolytope_weights ε hε.le _).1 hsx.1, ?_, hj, ?_, ?_⟩
  · intro u
    have hh := hsx.2.1 u
    rw [pilotQuadratics_objective, pilotQuadratics_objective] at hh
    simpa [x, xu] using hh
  · exact pilotQuadratics_objective p ε hp hε.le x (α xu) (t xu)
  · intro β hβ
    have hh := hsx.2.2 (ofWeight β)
      ((pilotPolytope_weights ε hε.le _).2 (by simpa))
    rw [pilotQuadratics_objective, pilotQuadratics_objective] at hh
    simpa [x, xu] using hh

/-- Under the supplied quantities and conditions, the exists measurable saddle selector bridge assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε), [the exists measurable saddle selector bridge](goal).

Under the stated assumptions, the exists measurable saddle selector bridge. -/
lemma exists_measurable_saddle_selector_bridge (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    ∃ select : TrialParameter → StaircaseWeight × ℝ × ℝ,
      Measurable select ∧
      ∀ θ, InteriorMeans θ →
        staircaseFeasible ε (select θ).1 ∧
        (∀ u, informationObjective θ p ε (select θ).1 (select θ).2.1 ≤
          informationObjective θ p ε (select θ).1 u) ∧
        Jstar θ p ε = (select θ).2.2 ∧
        (select θ).2.2 =
          informationObjective θ p ε (select θ).1 (select θ).2.1 := by
  obtain ⟨select, hm, hs⟩ :=
    exists_measurable_saddle_selector_bridge_strong p ε hp hε
  refine ⟨select, hm, ?_⟩
  intro θ hθ
  have h := hs θ hθ
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
