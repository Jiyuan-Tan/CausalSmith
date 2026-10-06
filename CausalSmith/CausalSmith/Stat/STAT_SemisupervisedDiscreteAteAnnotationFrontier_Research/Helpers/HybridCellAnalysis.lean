module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.FactorialCertificate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLightMoments
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLightBounds
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridPilotTails
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridQuantitativeArithmetic
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridVarianceAlgebra
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridPoolReindex
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.Splitting
public import Causalean.Stat.UStatistic.OrderM.Basic

/-! Per-cell analysis for the unequal-information Poisson hybrid. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
/-- Independent outcome, pilot, and factorial counts for every arm and cell.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev HybridPoissonCounts (d : Nat) := Fin d → Bool → Nat × (Nat × Nat)
/-- The three-pool marked Poisson law used in the hybrid analysis.  [the stated conditions](hyp:P,u,tp,t) [the stated conclusion](goal). -/
noncomputable def hybridPoissonCountLaw {d : Nat} (P : DiscreteLaw d)
    (u tp t : Real) : MeasureTheory.Measure (HybridPoissonCounts d) :=
  MeasureTheory.Measure.pi fun x => MeasureTheory.Measure.pi fun arm =>
    (ProbabilityTheory.poissonMeasure
      (Real.toNNReal (u * markedMass P x arm))).prod
      ((ProbabilityTheory.poissonMeasure
        (Real.toNNReal (tp * armMass P x arm))).prod
        (ProbabilityTheory.poissonMeasure
          (Real.toNNReal (t * armMass P x arm))))
/-- Polynomial statistic in one cell, excluding the pilot decision.  [the stated conditions](hyp:L,B,u,t,Z) [the stated conclusion](goal). -/
noncomputable def hybridLightCell (L : Nat) (B u t : Real)
    (Z : Bool → Nat × (Nat × Nat)) : Real :=
  (Z true).1 / u * factorialLift true L B t (Z false).2.2 (Z true).2.2 -
    (Z false).1 / u * factorialLift false L B t (Z false).2.2 (Z true).2.2

/-- Inverse-count statistic in one cell, excluding the pilot decision.  [the stated conditions](hyp:u,Z) [the stated conclusion](goal). -/
noncomputable def hybridHeavyCell (u : Real)
    (Z : Bool → Nat × (Nat × Nat)) : Real :=
  (Z true).1 / u * ((Z false).2.2 + (Z true).2.2 + 1 : Nat) /
      ((Z true).2.2 + 1 : Nat) -
    (Z false).1 / u * ((Z false).2.2 + (Z true).2.2 + 1 : Nat) /
      ((Z false).2.2 + 1 : Nat)

/-- Pilot-selected contribution of one covariate cell.  [the stated conditions](hyp:threshold,L,B,u,t,Z) [the stated conclusion](goal). -/
noncomputable def hybridSelectedCell (threshold L : Nat) (B u t : Real)
    (Z : Bool → Nat × (Nat × Nat)) : Real :=
  if (Z false).2.1 + (Z true).2.1 ≤ threshold then
    hybridLightCell L B u t Z
  else hybridHeavyCell u Z

/-- Pilot-count configurations selecting the polynomial branch.  [the stated conditions](hyp:threshold) [the stated conclusion](goal). -/
def hybridPilotEvent (threshold : Nat) : Set (Bool → Nat) :=
  {J | J false + J true ≤ threshold}
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma hybridPilotEvent_measurable (threshold : Nat) :
    MeasurableSet (hybridPilotEvent threshold) := by
  exact measurableSet_Iic.preimage
    (measurable_of_countable (fun J : Bool → Nat ↦ J false + J true))

/-- Polynomial cell statistic after separating outcome and factorial pools.  [the stated conditions](hyp:L,B,u,t,W) [the stated conclusion](goal). -/
noncomputable def hybridLightPools (L : Nat) (B u t : Real)
    (W : (Bool → Nat) × (Bool → Nat)) : Real :=
  W.1 true / u * factorialLift true L B t (W.2 false) (W.2 true) -
    W.1 false / u * factorialLift false L B t (W.2 false) (W.2 true)

/-- Inverse-count cell statistic after separating outcome and factorial pools.  [the stated conditions](hyp:u,W) [the stated conclusion](goal). -/
noncomputable def hybridHeavyPools (u : Real)
    (W : (Bool → Nat) × (Bool → Nat)) : Real :=
  W.1 true / u * (W.2 false + W.2 true + 1 : Nat) /
      (W.2 true + 1 : Nat) -
    W.1 false / u * (W.2 false + W.2 true + 1 : Nat) /
      (W.2 false + 1 : Nat)

/-- The polynomial branch is square-integrable under its independent outcome
and factorial Poisson pools.  [the stated conclusion](goal). -/
lemma hybridLightPools_memLp {d : Nat} (P : DiscreteLaw d)
    (u t B : Real) (L : Nat) (x : Fin d) :
    MemLp (hybridLightPools L B u t) 2
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
       (Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x arm)))) := by
  let muS : Bool → Measure Nat := fun arm ↦
    poissonMeasure (Real.toNNReal (u * markedMass P x arm))
  let muK : Bool → Measure Nat := fun arm ↦
    poissonMeasure (Real.toNNReal (t * armMass P x arm))
  have hS (a : Bool) : MemLp (fun S : Bool → Nat ↦ (S a : Real) / u) 2
      (Measure.pi muS) := by
    have hbase := (memLp_descFactorial_poisson
      (Real.toNNReal (u * markedMass P x a)) 1).const_mul u⁻¹
    have hpull := hbase.comp_measurePreserving (measurePreserving_eval muS a)
    convert hpull using 1
    funext S
    simp only [Nat.descFactorial_one, Function.comp_apply]
    ring
  have hK (a : Bool) : MemLp
      (fun K : Bool → Nat ↦ factorialLift a L B t (K false) (K true)) 2
      (Measure.pi muK) := by
    have hpair := factorialLift_memLp a L B t
      (armMass P x false) (armMass P x true)
    have hpull := hpair.comp_measurePreserving (boolPair_measurePreserving muK)
    unfold boolPair at hpull
    change MemLp
      (fun K : Bool → Nat ↦ factorialLift a L B t (K false) (K true)) 2
      (Measure.pi muK) at hpull
    exact hpull
  have htrue := Causalean.Mathlib.Probability.memLp_mul_prod_two (hS true) (hK true)
  have hfalse := Causalean.Mathlib.Probability.memLp_mul_prod_two (hS false) (hK false)
  convert htrue.sub hfalse using 1
  funext W
  rfl

/-- The inverse-count branch is square-integrable under its independent
outcome and factorial Poisson pools.  [the stated conclusion](goal). -/
lemma hybridHeavyPools_memLp {d : Nat} (P : DiscreteLaw d)
    (u t : Real) (x : Fin d) :
    MemLp (hybridHeavyPools u) 2
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
       (Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x arm)))) := by
  let muS : Bool → Measure Nat := fun arm ↦
    poissonMeasure (Real.toNNReal (u * markedMass P x arm))
  let muK : Bool → Measure Nat := fun arm ↦
    poissonMeasure (Real.toNNReal (t * armMass P x arm))
  have hS (a : Bool) : MemLp (fun S : Bool → Nat ↦ (S a : Real) / u) 2
      (Measure.pi muS) := by
    have hbase := (memLp_descFactorial_poisson
      (Real.toNNReal (u * markedMass P x a)) 1).const_mul u⁻¹
    have hpull := hbase.comp_measurePreserving (measurePreserving_eval muS a)
    convert hpull using 1
    funext S
    simp only [Nat.descFactorial_one, Function.comp_apply]
    ring
  have hKcoord (a : Bool) : MemLp (fun K : Bool → Nat ↦ (K a : Real)) 2
      (Measure.pi muK) := by
    have hbase := memLp_descFactorial_poisson
      (Real.toNNReal (t * armMass P x a)) 1
    have hpull := hbase.comp_measurePreserving (measurePreserving_eval muK a)
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
  have hArm (a : Bool) : MemLp
      (fun W : (Bool → Nat) × (Bool → Nat) ↦
        (W.1 a : Real) / u * ((W.2 false + W.2 true + 1 : Nat) : Real) /
          ((W.2 a + 1 : Nat) : Real)) 2
      ((Measure.pi muS).prod (Measure.pi muK)) := by
    have hdom := Causalean.Mathlib.Probability.memLp_mul_prod_two (hS a) hKtotal
    apply hdom.mono (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [] with W
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
    have hn : 1 ≤ W.2 a + 1 := by omega
    have hden : (1 : Real) ≤ ((W.2 a + 1 : Nat) : Real) := by exact_mod_cast hn
    have habs : |((W.2 a + 1 : Nat) : Real)| =
        ((W.2 a + 1 : Nat) : Real) := abs_of_nonneg (by linarith [hden])
    rw [habs]
    exact div_le_self (abs_nonneg _) hden
  convert (hArm true).sub (hArm false) using 1
  funext W
  rfl
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma hybridSelectedCell_eq_eventSelectedMixture (threshold L : Nat) (B u t : Real)
    (Z : Bool → Nat × (Nat × Nat)) :
    hybridSelectedCell threshold L B u t Z =
      Causalean.Mathlib.Probability.eventSelectedMixture (hybridPilotEvent threshold)
        (hybridLightPools L B u t)
        (hybridHeavyPools u) (pilotFirstSplitHybridPools Z) := by
  by_cases h : (Z false).2.1 + (Z true).2.1 ≤ threshold <;>
    simp [hybridSelectedCell, Causalean.Mathlib.Probability.eventSelectedMixture, hybridPilotEvent,
      pilotFirstSplitHybridPools, pilotFirstPools, splitHybridPools,
      hybridLightCell, hybridHeavyCell, hybridLightPools, hybridHeavyPools, h]

/-- Exact product-law transport which makes the pilot independent of the two
estimator pools in a fixed cell.  [the stated conclusion](goal). -/
lemma hybridCellLaw_pilotFirst_measurePreserving {d : Nat} (P : DiscreteLaw d)
    (u tp t : Real) (x : Fin d) :
    MeasurePreserving pilotFirstSplitHybridPools
      (Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm)))))
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
      (Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x arm))))) := by
  exact pilotFirstSplitHybridPools_measurePreserving _ _ _

/-- Exact per-cell mean decomposition after separating the pilot pool.  [the stated conditions](hyp:hLight,hHeavy) [the stated conclusion](goal). -/
lemma integral_hybridSelectedCell {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) (x : Fin d)
    (hLight : Integrable (hybridLightPools L B u t)
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
       (Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x arm)))))
    (hHeavy : Integrable (hybridHeavyPools u)
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
       (Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x arm))))) :
    (∫ Z, hybridSelectedCell threshold L B u t Z ∂
      (Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm)))))) =
      let muJ := Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (tp * armMass P x arm))
      let muE :=
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (t * armMass P x arm)))
      muJ.real (hybridPilotEvent threshold) *
          (∫ W, hybridLightPools L B u t W ∂muE) +
        (1 - muJ.real (hybridPilotEvent threshold)) *
          (∫ W, hybridHeavyPools u W ∂muE) := by
  let muJ := Measure.pi fun arm : Bool =>
    poissonMeasure (Real.toNNReal (tp * armMass P x arm))
  let muE :=
    (Measure.pi fun arm : Bool =>
      poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
    (Measure.pi fun arm : Bool =>
      poissonMeasure (Real.toNNReal (t * armMass P x arm)))
  let muZ := Measure.pi fun arm : Bool =>
    (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
      ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
        (poissonMeasure (Real.toNNReal (t * armMass P x arm))))
  let F := Causalean.Mathlib.Probability.eventSelectedMixture (hybridPilotEvent threshold)
    (hybridLightPools L B u t)
    (hybridHeavyPools u)
  have hmp : MeasurePreserving pilotFirstSplitHybridPools muZ (muJ.prod muE) :=
    hybridCellLaw_pilotFirst_measurePreserving P u tp t x
  have htransport : (∫ Z, F (pilotFirstSplitHybridPools Z) ∂muZ) =
      ∫ W, F W ∂muJ.prod muE := by
    rw [← hmp.map_eq]
    exact (integral_map hmp.aemeasurable
      (measurable_of_countable F).aestronglyMeasurable).symm
  rw [show (∫ Z, hybridSelectedCell threshold L B u t Z ∂muZ) =
      ∫ Z, F (pilotFirstSplitHybridPools Z) ∂muZ by
        apply integral_congr_ae
        filter_upwards [] with Z
        exact hybridSelectedCell_eq_eventSelectedMixture threshold L B u t Z,
    htransport]
  exact Causalean.Mathlib.Probability.integral_eventSelectedMixture muJ muE _
    (hybridPilotEvent_measurable threshold)
    _ _ hLight hHeavy

/-- Exact per-cell conditional-mixture variance decomposition.  [the stated conditions](hyp:hLight,hHeavy) [the stated conclusion](goal). -/
lemma variance_hybridSelectedCell {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) (x : Fin d)
    (hLight : MemLp (hybridLightPools L B u t) 2
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
       (Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x arm)))))
    (hHeavy : MemLp (hybridHeavyPools u) 2
      ((Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
       (Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x arm))))) :
    Var[hybridSelectedCell threshold L B u t;
      Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm))))] =
      let muJ := Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (tp * armMass P x arm))
      let muE :=
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (t * armMass P x arm)))
      let pi := muJ.real (hybridPilotEvent threshold)
      pi * Var[hybridLightPools L B u t; muE] +
        (1 - pi) * Var[hybridHeavyPools u; muE] +
        pi * (1 - pi) *
          ((∫ W, hybridLightPools L B u t W ∂muE) -
            ∫ W, hybridHeavyPools u W ∂muE) ^ 2 := by
  let muJ := Measure.pi fun arm : Bool =>
    poissonMeasure (Real.toNNReal (tp * armMass P x arm))
  let muE :=
    (Measure.pi fun arm : Bool =>
      poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
    (Measure.pi fun arm : Bool =>
      poissonMeasure (Real.toNNReal (t * armMass P x arm)))
  let muZ := Measure.pi fun arm : Bool =>
    (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
      ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
        (poissonMeasure (Real.toNNReal (t * armMass P x arm))))
  let F := Causalean.Mathlib.Probability.eventSelectedMixture (hybridPilotEvent threshold)
    (hybridLightPools L B u t)
    (hybridHeavyPools u)
  have hmp : MeasurePreserving pilotFirstSplitHybridPools muZ (muJ.prod muE) :=
    hybridCellLaw_pilotFirst_measurePreserving P u tp t x
  rw [show Var[hybridSelectedCell threshold L B u t; muZ] =
      Var[fun Z => F (pilotFirstSplitHybridPools Z); muZ] by
        apply variance_congr
        filter_upwards [] with Z
        exact hybridSelectedCell_eq_eventSelectedMixture threshold L B u t Z,
    hmp.variance_fun_comp (measurable_of_countable F).aemeasurable]
  exact Causalean.Mathlib.Probability.variance_eventSelectedMixture muJ muE _
    (hybridPilotEvent_measurable threshold)
    _ _ hLight hHeavy

/-- Each pilot-selected cell contribution has a finite second moment.  [the stated conclusion](goal). -/
lemma hybridSelectedCell_memLp {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) (x : Fin d) :
    MemLp (hybridSelectedCell threshold L B u t) 2
      (Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm))))) := by
  let muJ := Measure.pi fun arm : Bool =>
    poissonMeasure (Real.toNNReal (tp * armMass P x arm))
  let muE :=
    (Measure.pi fun arm : Bool =>
      poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
    (Measure.pi fun arm : Bool =>
      poissonMeasure (Real.toNNReal (t * armMass P x arm)))
  let muZ := Measure.pi fun arm : Bool =>
    (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
      ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
        (poissonMeasure (Real.toNNReal (t * armMass P x arm))))
  let F := Causalean.Mathlib.Probability.eventSelectedMixture (hybridPilotEvent threshold)
    (hybridLightPools L B u t)
    (hybridHeavyPools u)
  have hF : MemLp F 2 (muJ.prod muE) :=
    Causalean.Mathlib.Probability.memLp_eventSelectedMixture muJ muE _
    (hybridPilotEvent_measurable threshold) _ _
    (hybridLightPools_memLp P u t B L x) (hybridHeavyPools_memLp P u t x)
  have hmp : MeasurePreserving pilotFirstSplitHybridPools muZ (muJ.prod muE) :=
    hybridCellLaw_pilotFirst_measurePreserving P u tp t x
  have hpull := hF.comp_measurePreserving hmp
  convert hpull using 1
  funext Z
  simpa [F, Function.comp_apply] using
    hybridSelectedCell_eq_eventSelectedMixture threshold L B u t Z

/-- Independence across covariate cells turns the variance of the un-clipped
hybrid sum into the sum of its cell variances.  [the stated conclusion](goal). -/
lemma variance_sum_hybridSelectedCell {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) :
    Var[(fun K : HybridPoissonCounts d ↦
      ∑ x : Fin d, hybridSelectedCell threshold L B u t (K x));
      hybridPoissonCountLaw P u tp t] =
    ∑ x : Fin d, Var[hybridSelectedCell threshold L B u t;
      Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm))))] := by
  have h := variance_sum_pi (μ := fun x : Fin d ↦ Measure.pi fun arm : Bool =>
      (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
        ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
          (poissonMeasure (Real.toNNReal (t * armMass P x arm)))))
      (X := fun x Z ↦ hybridSelectedCell threshold L B u t Z)
      (fun x ↦ hybridSelectedCell_memLp P u tp t B threshold L x)
  change Var[(fun K : HybridPoissonCounts d ↦
      ∑ x : Fin d, hybridSelectedCell threshold L B u t (K x));
      Measure.pi fun x : Fin d ↦ Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm))))] = _
  calc
    _ = Var[∑ x : Fin d, fun K : HybridPoissonCounts d ↦
        hybridSelectedCell threshold L B u t (K x);
        Measure.pi fun x : Fin d ↦ Measure.pi fun arm : Bool =>
          (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
            ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
              (poissonMeasure (Real.toNNReal (t * armMass P x arm))))] := by
      apply variance_congr
      filter_upwards [] with K
      simp only [Finset.sum_apply]
    _ = _ := h

/-- Unconditional exact per-cell mean formula, with integrability supplied by
the explicit Poisson-polynomial bounds above.  [the stated conclusion](goal). -/
lemma integral_hybridSelectedCell_exact {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) (x : Fin d) :
    (∫ Z, hybridSelectedCell threshold L B u t Z ∂
      (Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm)))))) =
      let muJ := Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (tp * armMass P x arm))
      let muE :=
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (t * armMass P x arm)))
      muJ.real (hybridPilotEvent threshold) *
          (∫ W, hybridLightPools L B u t W ∂muE) +
        (1 - muJ.real (hybridPilotEvent threshold)) *
          (∫ W, hybridHeavyPools u W ∂muE) := by
  apply integral_hybridSelectedCell P u tp t B threshold L x
  · exact (hybridLightPools_memLp P u t B L x).integrable one_le_two
  · exact (hybridHeavyPools_memLp P u t x).integrable one_le_two

/-- Unconditional exact C27 variance formula for one hybrid cell.  [the stated conclusion](goal). -/
lemma variance_hybridSelectedCell_exact {d : Nat} (P : DiscreteLaw d)
    (u tp t B : Real) (threshold L : Nat) (x : Fin d) :
    Var[hybridSelectedCell threshold L B u t;
      Measure.pi fun arm : Bool =>
        (poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
          ((poissonMeasure (Real.toNNReal (tp * armMass P x arm))).prod
            (poissonMeasure (Real.toNNReal (t * armMass P x arm))))] =
      let muJ := Measure.pi fun arm : Bool =>
        poissonMeasure (Real.toNNReal (tp * armMass P x arm))
      let muE :=
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (u * markedMass P x arm))).prod
        (Measure.pi fun arm : Bool =>
          poissonMeasure (Real.toNNReal (t * armMass P x arm)))
      let pi := muJ.real (hybridPilotEvent threshold)
      pi * Var[hybridLightPools L B u t; muE] +
        (1 - pi) * Var[hybridHeavyPools u; muE] +
        pi * (1 - pi) *
          ((∫ W, hybridLightPools L B u t W ∂muE) -
            ∫ W, hybridHeavyPools u W ∂muE) ^ 2 := by
  exact variance_hybridSelectedCell P u tp t B threshold L x
    (hybridLightPools_memLp P u t B L x) (hybridHeavyPools_memLp P u t x)

/-- Exact light-branch mean in a cell.  [the stated conditions](hyp:hu,ht,hB) [the stated conclusion](goal). -/
lemma integral_hybridLightPools {d : Nat} (P : DiscreteLaw d)
    {u t B : Real} (hu : 0 < u) (ht : 0 < t) (hB : 0 < B)
    (L : Nat) (x : Fin d) :
    (∫ W, hybridLightPools L B u t W ∂
      ((Measure.pi fun a : Bool =>
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool =>
        poissonMeasure (Real.toNNReal (t * armMass P x a))))) =
      markedMass P x true * (cellMass P x / B) *
          (chebG L).eval (armMass P x true / B) -
        markedMass P x false * (cellMass P x / B) *
          (chebG L).eval (armMass P x false / B) := by
  let muS : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (u * markedMass P x a))
  let muK : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (t * armMass P x a))
  let armStat (a : Bool) (W : (Bool → Nat) × (Bool → Nat)) :=
    (W.1 a : Real) / u * factorialLift a L B t (W.2 false) (W.2 true)
  have hs (a : Bool) : 0 ≤ armMass P x a :=
    Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P x a y).1
  have hArm (a : Bool) : (∫ W, armStat a W ∂(Measure.pi muS).prod (Measure.pi muK)) =
      markedMass P x a * (cellMass P x / B) *
        (chebG L).eval (armMass P x a / B) := by
    let e (W : (Bool → Nat) × (Bool → Nat)) := (W.1 a, boolPair W.2)
    have hmp : MeasurePreserving e ((Measure.pi muS).prod (Measure.pi muK))
        ((muS a).prod ((muK false).prod (muK true))) :=
      (measurePreserving_eval muS a).prod (boolPair_measurePreserving muK)
    calc
      _ = ∫ Z, lightArmCell a L B u t Z ∂
          (muS a).prod ((muK false).prod (muK true)) := by
        rw [← hmp.map_eq]
        exact (integral_map hmp.aemeasurable
          (measurable_of_countable
            (lightArmCell a L B u t)).aestronglyMeasurable).symm
      _ = _ := by
        simp only [muS, muK]
        rw [integral_lightArmCell a L (marked := markedMass P x a)
          (s0 := armMass P x false) (s1 := armMass P x true) hu ht hB
          (jointMass_mem_unitInterval P x a true).1
          (hs false) (hs true)]
        rw [show armMass P x false + armMass P x true = cellMass P x by
          simp [armMass, cellMass]; ring]
        cases a <;> simp
  have hLp := hybridLightPools_memLp P u t B L x
  have htrue : Integrable (armStat true) ((Measure.pi muS).prod (Measure.pi muK)) := by
    have hs := ((memLp_descFactorial_poisson
      (Real.toNNReal (u * markedMass P x true)) 1).const_mul u⁻¹).comp_measurePreserving
        (measurePreserving_eval muS true)
    have hk := (factorialLift_memLp true L B t (armMass P x false)
      (armMass P x true)).comp_measurePreserving (boolPair_measurePreserving muK)
    apply ((Causalean.Mathlib.Probability.memLp_mul_prod_two hs hk).integrable one_le_two).congr
    filter_upwards [] with W
    simp only [Function.comp_apply, Nat.descFactorial_one]
    unfold boolPair
    dsimp [armStat]
    ring
  rw [show hybridLightPools L B u t = armStat true - armStat false by rfl]
  change (∫ W, armStat true W - armStat false W ∂
    (Measure.pi muS).prod (Measure.pi muK)) = _
  rw [integral_sub]
  · exact congrArg₂ (· - ·) (hArm true) (hArm false)
  · exact htrue
  · have hfull := hLp.integrable one_le_two
    apply (htrue.sub hfull).congr
    filter_upwards [] with W
    simp only [Pi.sub_apply]
    dsimp [armStat, hybridLightPools]
    ring

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
