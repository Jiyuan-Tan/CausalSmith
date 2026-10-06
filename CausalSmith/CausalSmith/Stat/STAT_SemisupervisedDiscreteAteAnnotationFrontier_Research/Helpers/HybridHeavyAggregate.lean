module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridHeavyTransport
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridPilotAggregate

/-! Aggregate identities and the C30 variance domination for the heavy branch. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- The all-heavy variance is the sum of the independent cell variances.  [the stated conclusion](goal). -/
lemma variance_separatedInverseCountStatistic_eq_sum {d : Nat}
    (P : DiscreteLaw d) (u t : Real) :
    Var[separatedInverseCountStatistic u; separatedPoissonCountLaw P u t] =
      ∑ x : Fin d, Var[hybridHeavyPools u;
        ((Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
         (Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (t * armMass P x a))))] := by
  let mu : Fin d → Measure ((Bool → Nat) × (Bool → Nat)) := fun x ↦
    (Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
    (Measure.pi fun a : Bool ↦
      poissonMeasure (Real.toNNReal (t * armMass P x a)))
  have h := variance_sum_pi (μ := mu)
    (X := fun x W ↦ hybridHeavyPools u W)
    (fun x ↦ hybridHeavyPools_memLp P u t x)
  change Var[(fun W ↦ ∑ x : Fin d, hybridHeavyPools u (W x));
    Measure.pi mu] = _
  calc
    _ = Var[∑ x : Fin d, fun W : SeparatedPoissonCounts d ↦
        hybridHeavyPools u (W x); Measure.pi mu] := by
      apply variance_congr
      filter_upwards [] with W
      simp only [Finset.sum_apply]
    _ = ∑ x : Fin d, Var[hybridHeavyPools u; mu x] := h
    _ = _ := by rfl

/-- C30: pilot downweighting can only reduce the all-heavy variance sum.  [the stated conditions](hyp:hvar) [the stated conclusion](goal). -/
lemma sum_pilotHeavy_mul_variance_heavy_le {d : Nat}
    (P : DiscreteLaw d) {u tp t C : Real} {threshold : Nat}
    (hvar : Var[separatedInverseCountStatistic u;
        separatedPoissonCountLaw P u t] ≤ C) :
    (∑ x : Fin d,
      hybridPilotHeavyProbability P tp threshold x *
        Var[hybridHeavyPools u;
          ((Measure.pi fun a : Bool ↦
            poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
           (Measure.pi fun a : Bool ↦
            poissonMeasure (Real.toNNReal (t * armMass P x a))))]) ≤ C := by
  calc
    _ ≤ ∑ x : Fin d, Var[hybridHeavyPools u;
        ((Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
         (Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (t * armMass P x a))))] := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_of_le_one_left (variance_nonneg _ _)
        (measureReal_le_one (μ := Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (tp * armMass P x a)))
          (s := (hybridPilotEvent threshold)ᶜ))
    _ = Var[separatedInverseCountStatistic u;
        separatedPoissonCountLaw P u t] :=
      (variance_separatedInverseCountStatistic_eq_sum P u t).symm
    _ ≤ C := hvar

/-- C30 with the overlap-dependent constant supplied by the all-heavy risk theorem.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma pilotHeavy_variance_bound_exists {eps : Real} (heps : 0 < eps)
    (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧ ∀ (d : Nat) (P : DiscreteLaw d)
      (hP : ModelClass d eps P) {u tp t : Real} (hu : 0 < u) (ht : 0 < t)
      (threshold : Nat),
      (∑ x : Fin d,
        hybridPilotHeavyProbability P tp threshold x *
          Var[hybridHeavyPools u;
            ((Measure.pi fun a : Bool ↦
              poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
             (Measure.pi fun a : Bool ↦
              poissonMeasure (Real.toNNReal (t * armMass P x a))))]) ≤
        C * (u⁻¹ + t⁻¹) := by
  obtain ⟨C, hC, hheavy⟩ := separated_inverse_count_risk heps heps2
  refine ⟨C, hC, ?_⟩
  intro d P hP u tp t hu ht threshold
  exact sum_pilotHeavy_mul_variance_heavy_le P
    (hheavy d u t hu ht P hP).2

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
