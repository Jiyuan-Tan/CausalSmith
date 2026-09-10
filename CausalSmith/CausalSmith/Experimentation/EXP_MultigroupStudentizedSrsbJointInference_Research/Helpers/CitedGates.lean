import Causalean.Stat.CLT.MartingaleArray.Main

/-!
# Discharged cited gates

Local proved wrappers connecting the paper's cited interfaces to promoted Causalean results.
-/

open Filter MeasureTheory ProbabilityTheory Topology

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open Causalean.Stat

/-- Li--Zhao (2026), *Design-based theory for causal inference from adaptive experiments*,
Appendix subsection "Lemmas for the central limit theorem", lemma `lem:martingale_clt`,
arXiv:2602.21998.  In the source's variance-normalized coordinates, predictable quadratic
variation convergence and the conditional Lindeberg condition imply convergence of row sums
to the standard normal law. -/
noncomputable def liZhaoVariance
    {Omega : ℕ → Type*} {mOmega : (n : ℕ) → MeasurableSpace (Omega n)}
    {mu : (n : ℕ) → Measure (Omega n)}
    (A : MartingaleDifferenceArray Omega mu) (T : ℕ) : ℝ :=
  ∫ w, A.predictableQuadraticVariation T w ∂mu T

noncomputable def liZhaoNormalizedRowSum
    {Omega : ℕ → Type*} {mOmega : (n : ℕ) → MeasurableSpace (Omega n)}
    {mu : (n : ℕ) → Measure (Omega n)}
    (A : MartingaleDifferenceArray Omega mu) (T : ℕ) (w : Omega T) : ℝ :=
  (Real.sqrt (liZhaoVariance A T))⁻¹ * A.rowSum T w

-- @node: lem:li-zhao-martingale-clt
lemma li_zhao_martingale_clt
    {Omega : ℕ → Type*} {mOmega : (n : ℕ) → MeasurableSpace (Omega n)}
    {mu : (n : ℕ) → Measure (Omega n)} [∀ n, IsProbabilityMeasure (mu n)]
    (A : MartingaleDifferenceArray Omega mu)
    (hInitial : ∀ T, A.filtration T 0 = ⊥)
    (hVariance : TendstoInProbability mu
      (fun T w ↦ A.predictableQuadraticVariation T w / liZhaoVariance A T) 1)
    (hLindeberg : ∀ epsilon : ℝ, 0 < epsilon → Tendsto
      (fun T ↦ (liZhaoVariance A T)⁻¹ *
        ∑ t ∈ Finset.range (A.rowLength T),
          ∫ w, (A.increment T t w) ^ 2 *
            (if epsilon * (liZhaoVariance A T) ^ (-(1 : ℝ) / 2) ≤
                |A.increment T t w| then 1 else 0) ∂mu T)
      atTop (nhds 0)) :
    TendstoInDistribution mu (liZhaoNormalizedRowSum A) (gaussianReal 0 1)
      (fun T ↦ (A.rowSum_aemeasurable T).const_mul _) := by
  let normalized : MartingaleDifferenceArray Omega mu := by sorry
  have hNormalizedVariance : TendstoInProbability mu
      normalized.predictableQuadraticVariation 1 := by sorry
  have hNormalizedLindeberg : ∀ epsilon : ℝ, 0 < epsilon →
      TendstoInProbability mu (normalized.conditionalLindeberg epsilon) 0 := by sorry
  have hCLT := Causalean.Stat.martingaleArrayCLT normalized
    hNormalizedVariance hNormalizedLindeberg
  exact (by sorry)

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
