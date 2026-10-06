module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalKLWitness

/-! # Transporting armwise mean identities to lower-bound separation -/

public section

open MeasureTheory Set
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Once the stopped-mean theorem identifies each causal target with its
survival-weighted intensity contrast, preserving both hazards and the control
intensity reduces the target difference exactly to the treatment-arm
direction integral. -/
lemma causalTarget_sub_eq_direction_integral
    (P₁ Pbase : SubjectLaw) (direction : ℝ → ℝ)
    (hmean₁ : causalTarget P₁ =
      ∫ t in (0 : ℝ)..1,
        (survival P₁ true t * P₁.lam true t -
          survival P₁ false t * P₁.lam false t))
    (hmeanBase : causalTarget Pbase =
      ∫ t in (0 : ℝ)..1,
        (survival Pbase true t * Pbase.lam true t -
          survival Pbase false t * Pbase.lam false t))
    (hint₁ : IntervalIntegrable (fun t : ℝ =>
      survival P₁ true t * P₁.lam true t -
        survival P₁ false t * P₁.lam false t) volume 0 1)
    (hintBase : IntervalIntegrable (fun t : ℝ =>
      survival Pbase true t * Pbase.lam true t -
        survival Pbase false t * Pbase.lam false t) volume 0 1)
    (hhazard : P₁.hazard = Pbase.hazard)
    (hfalse : P₁.lam false = Pbase.lam false)
    (htrue : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      P₁.lam true t = Pbase.lam true t + direction t) :
    causalTarget P₁ - causalTarget Pbase =
      ∫ t in (0 : ℝ)..1, survival Pbase true t * direction t := by
  have hsurvival : ∀ a : Arm, survival P₁ a = survival Pbase a := by
    intro a
    unfold survival
    rw [hhazard]
  rw [hmean₁, hmeanBase, ← intervalIntegral.integral_sub hint₁ hintBase]
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  change
    (survival P₁ true t * P₁.lam true t -
        survival P₁ false t * P₁.lam false t) -
      (survival Pbase true t * Pbase.lam true t -
        survival Pbase false t * Pbase.lam false t) =
      survival Pbase true t * direction t
  rw [congrFun (hsurvival true) t, congrFun (hsurvival false) t,
    congrFun hfalse t, htrue t htIcc]
  ring

/-- The exact treatment intensity formula supplied by the endpoint witness
turns its causal target difference into the endpoint direction integral. -/
lemma endpoint_causalTarget_sub_eq_integral
    (c : ClassConstants) (P₁ Pbase : SubjectLaw) (cut : CutoffData c)
    (u h : ℝ)
    (hmean₁ : causalTarget P₁ =
      ∫ t in (0 : ℝ)..1,
        (survival P₁ true t * P₁.lam true t -
          survival P₁ false t * P₁.lam false t))
    (hmeanBase : causalTarget Pbase =
      ∫ t in (0 : ℝ)..1,
        (survival Pbase true t * Pbase.lam true t -
          survival Pbase false t * Pbase.lam false t))
    (hint₁ : IntervalIntegrable (fun t : ℝ =>
      survival P₁ true t * P₁.lam true t -
        survival P₁ false t * P₁.lam false t) volume 0 1)
    (hintBase : IntervalIntegrable (fun t : ℝ =>
      survival Pbase true t * Pbase.lam true t -
        survival Pbase false t * Pbase.lam false t) volume 0 1)
    (hhazard : P₁.hazard = Pbase.hazard)
    (hfalse : P₁.lam false = Pbase.lam false)
    (htrue : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      P₁.lam true t = Pbase.lam true t + endpointDirection c cut u h t) :
    causalTarget P₁ - causalTarget Pbase =
      ∫ t in (0 : ℝ)..1,
        survival Pbase true t * endpointDirection c cut u h t :=
  causalTarget_sub_eq_direction_integral P₁ Pbase
    (endpointDirection c cut u h) hmean₁ hmeanBase hint₁ hintBase
      hhazard hfalse htrue

/-- The exact treatment intensity formula supplied by the critical witness
turns its causal target difference into the critical direction integral. -/
lemma critical_causalTarget_sub_eq_integral
    (c : ClassConstants) (P₁ Pbase : SubjectLaw) (cut : CutoffData c)
    (u : ℝ) (n : ℕ)
    (hmean₁ : causalTarget P₁ =
      ∫ t in (0 : ℝ)..1,
        (survival P₁ true t * P₁.lam true t -
          survival P₁ false t * P₁.lam false t))
    (hmeanBase : causalTarget Pbase =
      ∫ t in (0 : ℝ)..1,
        (survival Pbase true t * Pbase.lam true t -
          survival Pbase false t * Pbase.lam false t))
    (hint₁ : IntervalIntegrable (fun t : ℝ =>
      survival P₁ true t * P₁.lam true t -
        survival P₁ false t * P₁.lam false t) volume 0 1)
    (hintBase : IntervalIntegrable (fun t : ℝ =>
      survival Pbase true t * Pbase.lam true t -
        survival Pbase false t * Pbase.lam false t) volume 0 1)
    (hhazard : P₁.hazard = Pbase.hazard)
    (hfalse : P₁.lam false = Pbase.lam false)
    (htrue : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      P₁.lam true t = Pbase.lam true t + criticalDirection c cut u n t) :
    causalTarget P₁ - causalTarget Pbase =
      ∫ t in (0 : ℝ)..1,
        survival Pbase true t * criticalDirection c cut u n t :=
  causalTarget_sub_eq_direction_integral P₁ Pbase
    (criticalDirection c cut u n) hmean₁ hmeanBase hint₁ hintBase
      hhazard hfalse htrue

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
