module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ObservedKL

/-!
# Explicit midpoint baseline

This module constructs the constant recurrence and death baseline at the
midpoints of the model bands and proves that it remains in the model class.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The midpoint of the admissible recurrence-intensity band. -/
@[no_expose]
noncomputable def midpointLambda (c : ClassConstants) : ℝ :=
  (c.lambdaMin + c.lambdaMax) / 2

/-- The midpoint of the admissible death-hazard band. -/
@[no_expose]
noncomputable def midpointDeath (c : ClassConstants) : ℝ :=
  (c.dMin + c.dMax) / 2

/-- Both chosen midpoints lie strictly inside their respective bands. -/
lemma midpoint_strict_bounds (c : ClassConstants) :
    c.lambdaMin < midpointLambda c ∧ midpointLambda c < c.lambdaMax ∧
      c.dMin < midpointDeath c ∧ midpointDeath c < c.dMax := by
  unfold midpointLambda midpointDeath
  constructor
  · linarith [c.lambdaMin_lt]
  · constructor
    · linarith [c.lambdaMin_lt]
    · constructor <;> linarith [c.dMin_lt]

/-- The midpoint death rate is positive. -/
lemma midpointDeath_pos (c : ClassConstants) : 0 < midpointDeath c :=
  lt_trans c.dMin_pos (midpoint_strict_bounds c).2.2.1

/-- The explicit baseline at the two band midpoints. -/
@[no_expose]
noncomputable def midpointBaseline (c : ClassConstants) (reference : SubjectLaw) :
    SubjectLaw :=
  SubjectLaw.baseline reference (midpointLambda c) (midpointDeath c)
    (midpointDeath_pos c)

lemma midpointBaseline_eq_baseline (c : ClassConstants) (reference : SubjectLaw) :
    midpointBaseline c reference =
      SubjectLaw.baseline reference (midpointLambda c) (midpointDeath c)
        (midpointDeath_pos c) := by
  rfl

@[simp] lemma midpointBaseline_lam (c : ClassConstants) (reference : SubjectLaw)
    (a : Arm) (t : ℝ) :
    (midpointBaseline c reference).lam a t = midpointLambda c := by
  rfl

@[simp] lemma midpointBaseline_hazard (c : ClassConstants) (reference : SubjectLaw)
    (a : Arm) (t : ℝ) :
    (midpointBaseline c reference).hazard a t = midpointDeath c := by
  rfl

/-- The explicit product baseline preserves every censoring retention value
of its reference law. -/
lemma SubjectLaw.baseline_retention_eq
    (reference : SubjectLaw) (lambda0 d0 : ℝ) (hd0 : 0 < d0)
    (a : Arm) (t : ℝ) :
    retention (SubjectLaw.baseline reference lambda0 d0 hd0) a t =
      retention reference a t := by
  have hmarg := (SubjectLaw.baseline_preserves_marginals
    reference lambda0 d0 hd0).2
  have hs : MeasurableSet {q : Arm → ENNReal | ENNReal.ofReal t ≤ q a} :=
    measurableSet_le measurable_const (measurable_pi_apply a)
  have hbase := Measure.map_apply measurable_latentSubject_censorFamily hs
    (μ := (SubjectLaw.baseline reference lambda0 d0 hd0).latent)
  have href := Measure.map_apply measurable_latentSubject_censorFamily hs
    (μ := reference.latent)
  unfold retention
  simp only [measureReal_def]
  calc
    _ = (((SubjectLaw.baseline reference lambda0 d0 hd0).latent.map
          LatentSubject.censor) {q | ENNReal.ofReal t ≤ q a}).toReal :=
      congrArg ENNReal.toReal hbase.symm
    _ = ((reference.latent.map LatentSubject.censor)
          {q | ENNReal.ofReal t ≤ q a}).toReal := by rw [hmarg]
    _ = _ := congrArg ENNReal.toReal href

/-- Constant real-valued functions have zero Hölder seminorm and hence fit
every positive-radius Hölder ball used by the model. -/
lemma holderSeminormLe_const (k : ℕ) (gamma L x : ℝ) (hL : 0 ≤ L) :
    HolderSeminormLe k gamma L (fun _ : ℝ => x) := by
  constructor
  · exact contDiffOn_const
  · intro u hu v hv
    simp only [iteratedDerivWithin_const, sub_self, abs_zero]
    positivity

/-- Replacing recurrence and death mechanisms by their constant band
midpoints preserves membership in the full model class. -/
lemma midpointBaseline_modelClass (c : ClassConstants)
    (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀) :
    ModelClass c (midpointBaseline c P₀) := by
  let lambda0 := midpointLambda c
  let d0 := midpointDeath c
  have hlower : c.lambdaMin < lambda0 := by
    exact (midpoint_strict_bounds c).1
  have hupper : lambda0 < c.lambdaMax := by
    exact (midpoint_strict_bounds c).2.1
  have hlambda0 : 0 < lambda0 := lt_trans c.lambdaMin_pos hlower
  have hdlower : c.dMin < d0 := by
    exact (midpoint_strict_bounds c).2.2.1
  have hdupper : d0 < c.dMax := by
    exact (midpoint_strict_bounds c).2.2.2
  have hd0 : 0 < d0 := lt_trans c.dMin_pos hdlower
  let Pbase := SubjectLaw.baseline P₀ lambda0 d0 hd0
  have hprod := SubjectLaw.baseline_productIndependence P₀ lambda0 d0 hd0
  have hret : ∀ a t, retention Pbase a t = retention P₀ a t := by
    intro a t
    exact SubjectLaw.baseline_retention_eq P₀ lambda0 d0 hd0 a t
  have hp : Pbase.p = P₀.p := by rfl
  have hg : Pbase.g = P₀.g := by rfl
  have hlam : ∀ a t, Pbase.lam a t = lambda0 := by
    intro a t
    rfl
  have hhazard : ∀ a t, Pbase.hazard a t = d0 := by
    intro a t
    rfl
  change ModelClass c Pbase
  refine
    { iid := ?_
      randomAssignment := hprod.1
      assignmentLaw := SubjectLaw.baseline_assignmentLaw P₀ lambda0 d0 hd0
        hP₀.assignmentLaw
      treatmentOverlap := ?_
      poissonRecurrence := SubjectLaw.baseline_poissonRecurrence P₀ lambda0 d0
        hlambda0.le hd0
      deathHazard := SubjectLaw.baseline_deathHazard P₀ lambda0 d0 hd0
      recurrenceDeathIndependence := hprod.2.1
      independentCensoring := hprod.2.2
      recurrenceBounds := ?_
      deathBounds := ?_
      recurrenceHolder := ?_
      deathHolder := ?_
      endpointRetention := ?_
      tailEnvelopeSmall := hP₀.tailEnvelopeSmall
      endpointCoefficientBounds := ?_
      interiorRetention := ?_ }
  · intro n
    rfl
  · intro a
    rw [hp]
    exact hP₀.treatmentOverlap a
  · intro a t ht
    rw [hlam]
    exact ⟨hlower.le, hupper.le⟩
  · intro a t ht
    rw [hhazard]
    exact ⟨hdlower.le, hdupper.le⟩
  · intro a
    rw [show Pbase.lam a = fun _ => lambda0 by funext t; exact hlam a t]
    exact holderSeminormLe_const _ _ _ _ c.Llambda_pos.le
  · intro a
    rw [show Pbase.hazard a = fun _ => d0 by funext t; exact hhazard a t]
    exact holderSeminormLe_const _ _ _ _ c.Ld_pos.le
  · intro a x hx hx0
    rw [hret, show Pbase.g a = P₀.g a by rw [hg]]
    exact hP₀.endpointRetention a x hx hx0
  · intro a
    rw [hg]
    exact hP₀.endpointCoefficientBounds a
  · intro a t ht
    rw [hret]
    exact hP₀.interiorRetention a t ht

/-- The named midpoint baseline exposes the strict band bounds, inherited
assignment and censoring marginals, and its constant mechanisms. -/
lemma midpointBaseline_spec (c : ClassConstants)
    (P₀ : SubjectLaw) (hP₀ : ModelClass c P₀) :
    ModelClass c (midpointBaseline c P₀) ∧
      (midpointBaseline c P₀).p = P₀.p ∧
      (midpointBaseline c P₀).latent.map LatentSubject.censor =
        P₀.latent.map LatentSubject.censor ∧
      c.lambdaMin < midpointLambda c ∧
      midpointLambda c < c.lambdaMax ∧
      c.dMin < midpointDeath c ∧
      midpointDeath c < c.dMax ∧
      (∀ a : Arm, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (midpointBaseline c P₀).lam a t = midpointLambda c ∧
        (midpointBaseline c P₀).hazard a t = midpointDeath c) := by
  refine ⟨midpointBaseline_modelClass c P₀ hP₀, rfl, ?_,
    (midpoint_strict_bounds c).1, (midpoint_strict_bounds c).2.1,
    (midpoint_strict_bounds c).2.2.1, (midpoint_strict_bounds c).2.2.2, ?_⟩
  · exact (SubjectLaw.baseline_preserves_marginals P₀
      (midpointLambda c) (midpointDeath c) (midpointDeath_pos c)).2
  · intro a t ht
    exact ⟨rfl, rfl⟩

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
