module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.FixedLawEndpointFullRow

/-! Convex closure of compatible fixed released laws. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section
/-- For [the specified mathematical inputs](hyp:ε,J,c,d,P,Q), [this definition](goal) introduces the corresponding object. -/
def compatibleMixture {ε : ℝ} {J : ℕ} (c d : ENNReal)
    (P Q : Measure (FullRow ε J)) : Measure (FullRow ε J) :=
  c • P + d • Q

private lemma mixtureScore_integrable {ε : ℝ} {J : ℕ}
    (c : ENNReal) (hc : c ≠ ∞) (P : Measure (FullRow ε J))
    [IsProbabilityMeasure P] :
    Integrable (fun ω => (score ω : ℝ)) (c • P) := by
  letI : IsFiniteMeasure (c • P) := ⟨by
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (measure_lt_top P univ)⟩
  apply Integrable.of_bound (by unfold score; fun_prop) (|ε| + |1 - ε| + 1)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  rcases (score ω).property with ⟨he0, he1⟩
  have h₁ := neg_le_abs ε
  have h₂ := le_abs_self (1 - ε)
  have h₃ := neg_le_abs (1 - ε)
  have h₄ := le_abs_self ε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma mixture_real_apply {α : Type*} [MeasurableSpace α]
    (c d : ENNReal) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] (S : Set α) :
    (c • P + d • Q).real S =
      c.toReal * P.real S + d.toReal * Q.real S := by
  unfold Measure.real
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    ENNReal.toReal_add]
  · simp only [smul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  · exact ENNReal.mul_ne_top hc (measure_ne_top P S)
  · exact ENNReal.mul_ne_top hd (measure_ne_top Q S)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,H,g,Prel,P,Q,hP,hQ,c,d,hc,hd,hsum), this result [establishes the stated mathematical conclusion](goal). -/
lemma compatibleCausalLaw_mixture {ε : ℝ} {J : ℕ}
    (H : Measure (ScoreSpace ε)) (g : ScoreSpace ε → LabelSpace J)
    (Prel : Measure (Observation J)) (P Q : Measure (FullRow ε J))
    (hP : CompatibleCausalLaw H g Prel P)
    (hQ : CompatibleCausalLaw H g Prel Q)
    (c d : ENNReal) (hc : c ≠ ∞) (hd : d ≠ ∞) (hsum : c + d = 1) :
    CompatibleCausalLaw H g Prel (compatibleMixture c d P Q) := by
  letI : IsProbabilityMeasure P := hP.probability
  letI : IsProbabilityMeasure Q := hQ.probability
  have hprob : IsProbabilityMeasure (compatibleMixture c d P Q) := by
    rw [isProbabilityMeasure_iff]
    unfold compatibleMixture
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact hsum
  refine
    { probability := hprob
      measurableRelease := hP.measurableRelease
      scoreMarginal := ?_
      randomizedAssignment := ?_
      consistency := ?_
      deterministicRelease := ?_
      releasedLaw := ?_ }
  · unfold ScoreMarginal compatibleMixture
    rw [Measure.map_add _ _ (by unfold score; fun_prop),
      Measure.map_smul, Measure.map_smul, hP.scoreMarginal, hQ.scoreMarginal,
      ← add_smul, hsum, one_smul]
  · intro B hB
    let S : Set (FullRow ε J) :=
      {ω | arm ω = true ∧ (score ω, outcome0 ω, outcome1 ω) ∈ B}
    let T : Set (FullRow ε J) :=
      {ω | (score ω, outcome0 ω, outcome1 ω) ∈ B}
    have hSintP := mixtureScore_integrable c hc P
    have hSintQ := mixtureScore_integrable d hd Q
    change (compatibleMixture c d P Q).real S =
      ∫ ω in T, (score ω : ℝ) ∂compatibleMixture c d P Q
    unfold compatibleMixture
    rw [mixture_real_apply c d hc hd P Q S]
    rw [Measure.restrict_add,
      integral_add_measure hSintP.integrableOn hSintQ.integrableOn,
      Measure.restrict_smul, Measure.restrict_smul,
      integral_smul_measure, integral_smul_measure]
    rw [hP.randomizedAssignment B hB, hQ.randomizedAssignment B hB]
    simp only [smul_eq_mul]
    rfl
  · unfold Consistency compatibleMixture
    rw [ae_add_measure_iff]
    exact ⟨Measure.smul_absolutelyContinuous.ae_le hP.consistency,
      Measure.smul_absolutelyContinuous.ae_le hQ.consistency⟩
  · unfold DeterministicRelease compatibleMixture
    rw [ae_add_measure_iff]
    exact ⟨Measure.smul_absolutelyContinuous.ae_le hP.deterministicRelease,
      Measure.smul_absolutelyContinuous.ae_le hQ.deterministicRelease⟩
  · unfold ReleasedLaw releasedLaw compatibleMixture
    rw [Measure.map_add _ _ (by
      unfold releasedRecord label arm observed
      fun_prop), Measure.map_smul, Measure.map_smul,
      show P.map releasedRecord = Prel from hP.releasedLaw,
      show Q.map releasedRecord = Prel from hQ.releasedLaw,
      ← add_smul, hsum, one_smul]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,P,Q,c,d,hc,hd,f,hf,K,hK), this result [establishes the stated mathematical conclusion](goal). -/
lemma integral_compatibleMixture {ε : ℝ} {J : ℕ}
    (P Q : Measure (FullRow ε J)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (c d : ENNReal) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (f : FullRow ε J → ℝ) (hf : Measurable f) (K : ℝ)
    (hK : ∀ ω, ‖f ω‖ ≤ K) :
    (∫ ω, f ω ∂compatibleMixture c d P Q) =
      c.toReal * ∫ ω, f ω ∂P + d.toReal * ∫ ω, f ω ∂Q := by
  have hPc : Integrable f (c • P) := by
    letI : IsFiniteMeasure (c • P) := ⟨by
      rw [Measure.smul_apply]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (measure_lt_top P univ)⟩
    exact Integrable.of_bound hf.aestronglyMeasurable K
      (Filter.Eventually.of_forall hK)
  have hQd : Integrable f (d • Q) := by
    letI : IsFiniteMeasure (d • Q) := ⟨by
      rw [Measure.smul_apply]
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hd) (measure_lt_top Q univ)⟩
    exact Integrable.of_bound hf.aestronglyMeasurable K
      (Filter.Eventually.of_forall hK)
  unfold compatibleMixture
  rw [integral_add_measure hPc hQd, integral_smul_measure,
    integral_smul_measure]
  simp only [smul_eq_mul]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
