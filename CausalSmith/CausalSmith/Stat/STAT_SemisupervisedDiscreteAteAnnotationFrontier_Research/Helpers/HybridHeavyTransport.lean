module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridPoolReindex
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonInverseCountMarginalEnergy

/-! Transport of the all-heavy statistic to separated arm-count pools. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- The outcome and marginal counts separated within every covariate cell.  [the stated conditions](hyp:d) [the stated conclusion](goal). -/
abbrev SeparatedPoissonCounts (d : Nat) :=
  Fin d → (Bool → Nat) × (Bool → Nat)

/-- Product law of the separated outcome and marginal pools.  [the stated conditions](hyp:P,u,t) [the stated conclusion](goal). -/
noncomputable def separatedPoissonCountLaw {d : Nat} (P : DiscreteLaw d)
    (u t : Real) : Measure (SeparatedPoissonCounts d) :=
  Measure.pi fun x : Fin d ↦
    (Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
    (Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (t * armMass P x a)))

/-- All-heavy inverse-count statistic written on separated pools.  [the stated conditions](hyp:u,W) [the stated conclusion](goal). -/
noncomputable def separatedInverseCountStatistic {d : Nat} (u : Real)
    (W : SeparatedPoissonCounts d) : Real :=
  ∑ x : Fin d,
    ((W x).1 true / u * ((W x).2 false + (W x).2 true + 1 : Nat) /
        ((W x).2 true + 1 : Nat) -
      (W x).1 false / u * ((W x).2 false + (W x).2 true + 1 : Nat) /
        ((W x).2 false + 1 : Nat))
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma separatedInverseCountStatistic_split_apply {d : Nat} (u : Real)
    (K : PoissonCounts d) :
    separatedInverseCountStatistic u (splitPairedCellPools K) =
      inverseCountStatistic u K := by
  rfl

/-- Splitting paired counts identifies the heavy product experiment.  [the stated conclusion](goal). -/
lemma poissonCountLaw_split_measurePreserving {d : Nat} (P : DiscreteLaw d)
    (u t : Real) :
    MeasurePreserving
      (splitPairedCellPools : PoissonCounts d → SeparatedPoissonCounts d)
      (poissonCountLaw P u t) (separatedPoissonCountLaw P u t) := by
  exact splitPairedCellPools_measurePreserving _ _
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma integral_separatedInverseCountStatistic {d : Nat} (P : DiscreteLaw d)
    (u t : Real) :
    (∫ W, separatedInverseCountStatistic u W
        ∂separatedPoissonCountLaw P u t) =
      expectationUnder (poissonCountLaw P u t) (inverseCountStatistic u) := by
  let hmp := poissonCountLaw_split_measurePreserving P u t
  rw [← hmp.map_eq]
  rw [integral_map hmp.aemeasurable
    (measurable_of_countable (separatedInverseCountStatistic u)).aestronglyMeasurable]
  simp_rw [separatedInverseCountStatistic_split_apply]
  rfl
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma variance_separatedInverseCountStatistic {d : Nat} (P : DiscreteLaw d)
    (u t : Real) :
    Var[separatedInverseCountStatistic u; separatedPoissonCountLaw P u t] =
      varianceUnder (poissonCountLaw P u t) (inverseCountStatistic u) := by
  let hmp := poissonCountLaw_split_measurePreserving P u t
  rw [← hmp.variance_fun_comp
    (measurable_of_countable (separatedInverseCountStatistic u)).aemeasurable]
  rw [show (fun ω ↦ separatedInverseCountStatistic u
      (splitPairedCellPools ω)) = inverseCountStatistic u by
    funext K
    exact separatedInverseCountStatistic_split_apply u K]
  exact (varianceUnder_eq_variance _ _ (measurable_of_countable _).aemeasurable).symm

/-- Existing all-heavy risk control, transported to separated pools.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma separated_inverse_count_risk {eps : Real} (heps : 0 < eps)
    (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧ ∀ (d : Nat) (u t : Real), 0 < u → 0 < t →
      ∀ P : DiscreteLaw d, ModelClass d eps P →
        |(∫ W, separatedInverseCountStatistic u W
            ∂separatedPoissonCountLaw P u t) - ateFunctional P| ≤
            C * min 1 (d / t) ∧
        Var[separatedInverseCountStatistic u; separatedPoissonCountLaw P u t] ≤
            C * (u⁻¹ + t⁻¹) := by
  obtain ⟨C, hC, h⟩ := poisson_inverse_count_risk heps heps2
  refine ⟨C, hC, ?_⟩
  intro d u t hu ht P hP
  simpa [integral_separatedInverseCountStatistic,
    variance_separatedInverseCountStatistic] using h d u t hu ht P hP

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
