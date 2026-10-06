module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerCertificate

/-! An explicit moment-matched three-score pair for the score-log lower bound. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,x,y,z), [this definition](goal) introduces the corresponding object. -/
def scoreLogTripleBaseline {ε : ℝ}
    (x y z : ScoreSpace ε) : Measure (ScoreSpace ε) :=
  (ENNReal.ofReal (1 / 3 : ℝ)) • Measure.dirac x +
    (ENNReal.ofReal (1 / 3 : ℝ)) • Measure.dirac y +
    (ENNReal.ofReal (1 / 3 : ℝ)) • Measure.dirac z

/-- For [the specified mathematical inputs](hyp:ε,x,y,z,u), [this definition](goal) introduces the corresponding object. -/
def scoreLogTriplePerturbed {ε : ℝ}
    (x y z : ScoreSpace ε) (u : ℝ) : Measure (ScoreSpace ε) :=
  ENNReal.ofReal (1 / 3 + u * ((z : ℝ) - y)) • Measure.dirac x +
    ENNReal.ofReal (1 / 3 - u * ((z : ℝ) - x)) • Measure.dirac y +
    ENNReal.ofReal (1 / 3 + u * ((y : ℝ) - x)) • Measure.dirac z

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,hxy,hyz,u,hu0,hu), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriple_weights_nonneg {ε : ℝ}
    (x y z : ScoreSpace ε) (hxy : x < y) (hyz : y < z)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3) :
    0 ≤ 1 / 3 + u * ((z : ℝ) - y) ∧
    0 ≤ 1 / 3 - u * ((z : ℝ) - x) ∧
    0 ≤ 1 / 3 + u * ((y : ℝ) - x) := by
  have hzy : 0 ≤ (z : ℝ) - y := sub_nonneg.mpr (le_of_lt hyz)
  have hyx : 0 ≤ (y : ℝ) - x := sub_nonneg.mpr (le_of_lt hxy)
  constructor
  · positivity
  constructor
  · linarith
  · positivity

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,hxy,hyz,u), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriple_weight_identities {ε : ℝ}
    (x y z : ScoreSpace ε) (hxy : x < y) (hyz : y < z) (u : ℝ) :
    (1 / 3 + u * ((z : ℝ) - y)) +
        (1 / 3 - u * ((z : ℝ) - x)) +
        (1 / 3 + u * ((y : ℝ) - x)) = 1 ∧
    (x : ℝ) * (1 / 3 + u * ((z : ℝ) - y)) +
        (y : ℝ) * (1 / 3 - u * ((z : ℝ) - x)) +
        (z : ℝ) * (1 / 3 + u * ((y : ℝ) - x)) =
      (x : ℝ) / 3 + (y : ℝ) / 3 + (z : ℝ) / 3 := by
  have h := fiberTriple_perturbation_identities (x : ℝ) y z hxy hyz
  constructor <;> nlinarith [h.1, h.2.1]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTripleBaseline_isProbabilityMeasure {ε : ℝ}
    (x y z : ScoreSpace ε) :
    IsProbabilityMeasure (scoreLogTripleBaseline x y z) := by
  rw [isProbabilityMeasure_iff]
  unfold scoreLogTripleBaseline
  rw [Measure.add_apply, Measure.add_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 3 + 1 / 3) (by norm_num)]
  norm_num

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,hxy,hyz,u,hu0,hu), this result [establishes the stated mathematical conclusion](goal). -/
lemma scoreLogTriplePerturbed_isProbabilityMeasure {ε : ℝ}
    (x y z : ScoreSpace ε) (hxy : x < y) (hyz : y < z)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u * ((z : ℝ) - x) ≤ 1 / 3) :
    IsProbabilityMeasure (scoreLogTriplePerturbed x y z u) := by
  have hw := scoreLogTriple_weights_nonneg x y z hxy hyz u hu0 hu
  have hsum := (scoreLogTriple_weight_identities x y z hxy hyz u).1
  rw [isProbabilityMeasure_iff]
  unfold scoreLogTriplePerturbed
  rw [Measure.add_apply, Measure.add_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.mem_univ,
    Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hw.1 hw.2.1, ← ENNReal.ofReal_add (add_nonneg hw.1 hw.2.1) hw.2.2]
  rw [hsum]
  norm_num

end
end CausalSmith.PartialID.UnlinkedPropensityAte
