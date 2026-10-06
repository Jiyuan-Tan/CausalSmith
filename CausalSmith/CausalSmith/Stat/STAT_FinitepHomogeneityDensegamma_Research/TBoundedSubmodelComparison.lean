module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryRandomization

/-! Finite-moment homogeneity testing: TBoundedSubmodelComparison. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- [Bounded submodel comparison](goal). For every \(v=(p,\alpha,\beta,\gamma)\in\mathcal V\), with \(w=(\alpha,\beta,\gamma)\), \[\mathcal M^{\mathrm{bin}}_w\subseteq\mathcal M^{\mathrm b}_w\subseteq\mathcal M_v,\qquad D_w^{\mathrm{bin}}=D_w^{\mathrm b}=D_v\ge d_0.\] For every \(n\ge2\) and \(0<r<D_v\), \[B_n^{\mathrm{bin}}(w,r)=B_n^{\mathrm b}(w,r)\le B_n(v,r),\qquad 0<r_n^{*,\mathrm{bin}}(w)=r_n^{*,\mathrm b}(w)\le r_n^*(v).\] A bounded record can be converted to a signed-binary record by keeping \((X,A)\) and drawing a sign with conditional mean \(Y\); this preserves both arm means, the propensity and \(d(P)\). Every permissible primitive mean triple has a signed-binary realization. Independent conversion randomization is integrated into a Borel rejection probability based on the original records and public randomization. This statement assumes [the hv condition](hyp:hv). -/
-- @node: prop:bounded-submodel-comparison
theorem bounded_submodel_comparison (v : Params) (hv : v.Valid) :
    (∀ law, InBinaryModel v.toSmooth3 law → InBoundedModel v.toSmooth3 law) ∧
    (∀ law, InBoundedModel v.toSmooth3 law → InModel v law) ∧
    maxDistBinary v.toSmooth3=maxDistBounded v.toSmooth3 ∧ maxDistBounded v.toSmooth3=maxDist v ∧ d0 ≤ maxDist v ∧
    (∀ n : ℕ, 2 ≤ n → ∀ r : ℝ, 0 < r → r < maxDist v →
      binaryTestingRisk n v.toSmooth3 r=boundedTestingRisk n v.toSmooth3 r ∧ boundedTestingRisk n v.toSmooth3 r ≤ testingRisk n v r) ∧
    (∀ n : ℕ, 2 ≤ n → 0 < binaryCriticalRadius n v.toSmooth3 ∧
      binaryCriticalRadius n v.toSmooth3=boundedCriticalRadius n v.toSmooth3 ∧ boundedCriticalRadius n v.toSmooth3 ≤ criticalRadius n v) ∧
    (∀ law, InModel (Params.ofBounded v.toSmooth3) law →
      InBinaryModel v.toSmooth3 (binaryConversion law) ∧ (binaryConversion law).e=law.e ∧
      (binaryConversion law).m0=law.m0 ∧ (binaryConversion law).tau=law.tau ∧
      hetDist (binaryConversion law)=hetDist law ∧ (NullConstancy (binaryConversion law) ↔ NullConstancy law)) ∧
    (∀ n : ℕ, ∀ ψ : Test n, ∀ law, InBoundedModel v.toSmooth3 law →
      rejectProb n law.P (binaryRandomizationTest n ψ)=rejectProb n (binaryConversion law).P ψ) := by
  -- Integrate independent sign conversion before comparing the decision problems.
  have hconversion : ∀ n : ℕ, ∀ ψ : Test n, ∀ law, InBoundedModel v.toSmooth3 law →
      rejectProb n law.P (binaryRandomizationTest n ψ) =
        rejectProb n (binaryConversion law).P ψ := by
    intro n ψ law hm
    exact binaryRandomization_rejectProb v.toSmooth3 n ψ law hm
  have hrisk (n : ℕ) (r : ℝ) :
      binaryTestingRisk n v.toSmooth3 r = boundedTestingRisk n v.toSmooth3 r :=
    (boundedTestingRisk_eq_binary_of_conversion v.toSmooth3 n r (hconversion n)).symm
  refine ⟨binaryModel_inBoundedModel v.toSmooth3, ?_,
    maxDistBinary_eq_maxDistBounded v.toSmooth3, maxDistBounded_eq_maxDist v,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact boundedModel_inModel v hv
  · exact model_distance_lower v hv
  · intro n hn r hr hrD
    refine ⟨?_, boundedTestingRisk_le_testingRisk v hv n r⟩
    exact hrisk n r
  · intro n hn
    refine ⟨?_, ?_, boundedCriticalRadius_le_criticalRadius v hv n⟩
    · exact binaryCriticalRadius_pos n hn v.toSmooth3 hv.2
    · unfold binaryCriticalRadius boundedCriticalRadius
      rw [maxDistBinary_eq_maxDistBounded]
      exact cappedRadius_eq_of_risk_eq _ _ _ (fun r _ _ => hrisk n r)
  · intro law hm
    have hc := binaryConversion_primitives law hm.baselineCap hm.effectCap
    have hd := binaryConversion_preserves_effect law hm.baselineCap hm.effectCap
    exact ⟨binaryConversion_inModel v.toSmooth3 law hm, hc.1, hc.2.1, hc.2.2.1,
      hd.1, hd.2⟩
  · exact hconversion

end CausalSmith.Stat.FinitepHomogeneityDensegamma
