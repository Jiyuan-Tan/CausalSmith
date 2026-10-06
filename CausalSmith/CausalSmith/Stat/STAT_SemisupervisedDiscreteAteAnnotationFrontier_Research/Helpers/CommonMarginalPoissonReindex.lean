module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalPoissonTransport

/-! Finite reindexing identities for the common-marginal Poisson experiment. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
/-- The formal statement establishes [the stated conclusion](goal). -/

theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  ext s hs
  rw [poissonMeasure, Measure.sum_apply _ hs]
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro n hn
    rw [Measure.smul_apply, smul_eq_mul]
    simp [zero_pow hn]
  · simp
/-- The formal statement establishes [the stated conclusion](goal). -/

theorem rawCellZeroLaw :
    (Measure.pi fun _ : Bool =>
      ((poissonMeasure 0).prod (poissonMeasure 0)).prod (poissonMeasure 0)) =
      Measure.dirac (fun _ : Bool => ((0, 0), 0)) := by
  simp only [poissonMeasure_zero]
  simp only [Measure.dirac_prod_dirac]
  refine Measure.pi_eq fun s hs => ?_
  by_cases h0 : ((0, 0), 0) ∈ s false <;>
    by_cases h1 : ((0, 0), 0) ∈ s true <;>
      simp [Measure.dirac_apply', hs, h0, h1]

/-- Regroup the five rare-cell counts into the Boolean arm table used by the raw experiment.  [the stated conclusion](goal). -/
def rareObservationToCell :
    ((Nat × Nat) × (Nat × (Nat × Nat))) → Bool → (Nat × Nat) × Nat :=
  fun z arm => if arm then (z.1, z.2.1) else ((0, z.2.2.1), z.2.2.2)

/-- Inserting a deterministic zero coordinate commutes with a binary product law.  [the stated conclusion](goal). -/
theorem prod_map_insertZero (mu nu : Measure Nat)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (mu.prod nu).map (fun z => ((0, z.1), z.2)) =
      ((Measure.dirac 0).prod mu).prod nu := by
  change (mu.prod nu).map (Prod.map (Prod.mk 0) id) = _
  rw [← Measure.map_prod_map mu nu (by fun_prop : Measurable (Prod.mk 0)) measurable_id]
  rw [← Measure.dirac_prod]
  simp

/-- The nested five-factor product, after regrouping, is exactly the two-arm product law.  [the stated conclusion](goal). -/
theorem fiveProduct_map_rareObservationToCell
    (mu11 mu10 mu1a mu00 mu0a : Measure Nat)
    [IsProbabilityMeasure mu11] [IsProbabilityMeasure mu10]
    [IsProbabilityMeasure mu1a] [IsProbabilityMeasure mu00]
    [IsProbabilityMeasure mu0a] :
    (((mu11.prod mu10).prod (mu1a.prod (mu00.prod mu0a))).map
        rareObservationToCell) =
      Measure.pi fun arm : Bool => if arm then
        (mu11.prod mu10).prod mu1a
      else ((Measure.dirac 0).prod mu00).prod mu0a := by
  let treated : Measure ((Nat × Nat) × Nat) :=
    (mu11.prod mu10).prod mu1a
  let control : Measure ((Nat × Nat) × Nat) :=
    ((Measure.dirac 0).prod mu00).prod mu0a
  have hregroup :
      (((mu11.prod mu10).prod (mu1a.prod (mu00.prod mu0a))).map
          (fun z => (((0, z.2.2.1), z.2.2.2), (z.1, z.2.1)))) =
        control.prod treated := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
    change Measure.map
      (Prod.swap ∘ Prod.map id (fun z : Nat × Nat => ((0, z.1), z.2)))
        (treated.prod (mu00.prod mu0a)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    rw [← Measure.map_prod_map treated (mu00.prod mu0a)
      measurable_id (by fun_prop : Measurable fun z : Nat × Nat => ((0, z.1), z.2))]
    rw [prod_map_insertZero]
    simpa [treated, control, Function.comp_def] using
      (Measure.prod_swap (μ := treated) (ν := control))
  rw [← prod_map_boolArrow control treated]
  rw [← hregroup, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
