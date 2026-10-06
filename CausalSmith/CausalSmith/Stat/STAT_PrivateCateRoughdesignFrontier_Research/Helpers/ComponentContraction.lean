module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.DatasetMarginals
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TreeOrdering
/-! Assembly of the Borel measurable shared-sign coupling and its private contraction bound. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
variable (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n : ℕ)

/-- Finite graph factorization yields measurable component couplings and, in the sparse regime,
a Hamming bound and its private-output consequence. Both cited gates remain explicit inputs.  [the theorem's stated inputs and assumptions](hyp:cayley_of_gate,boundedDifferences_of_gate,epsilon,he,B,M,hM), and [the asserted conclusion follows](goal). -/
-- @node: lem:measurable-component-contraction
lemma measurable_component_contraction
    (cayley_of_gate : CayleyLabeledTreeCount)
    (boundedDifferences_of_gate : BoundedDifferencesMGF)
    (epsilon : ℝ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    {B : Type*} [MeasurableSpace B] [StandardBorelSpace B]
    (M : Kernel (Dataset n) B) [IsMarkovKernel M] (hM : PrivateKernel n epsilon M) :
    (∀ x z,
      fullAlternativeMass hL n x z =
        ((orderedComponents hL n x).map (fun C =>
          alternativeMass hL n x C (fun i => z i))).prod ∧
      (4 : ℝ)^(-(n : ℤ)) =
        ((orderedComponents hL n x).map (fun C => nullMass n C (fun i => z i))).prod) ∧
    (∀ x i,
      let C := componentVertices hL n x i
      (C.card = 1 → alternativeComponentLaw hL n x C = nullComponentLaw n C) ∧
      TV (alternativeComponentLaw hL n x C) (nullComponentLaw n C) ≤
        4*separation hL*(componentSize n C : ℝ)^2 ∧
      Causalean.Stat.IsCoupling (componentCoupling hL n x C)
        (alternativeComponentLaw hL n x C) (nullComponentLaw n C)) ∧
    Measurable (conditionalDatasetCoupling hL n) ∧
    Causalean.Stat.IsCoupling (commonMassCoupling hL n)
      (signMixture hL hhL n) (dataLaw n fairNull) ∧
    ((n : ℝ)*deltaL hL ≤ 1/128 →
      WH n (signMixture hL hhL n) (dataLaw n fairNull) ≤
        ENNReal.ofReal (1024*separation hL*(n : ℝ)^2*hL*deltaL hL) ∧
      TV (M ∘ₘ signMixture hL hhL n) (M ∘ₘ dataLaw n fairNull) ≤
        2048*epsilon*separation hL*(n : ℝ)^2*hL*deltaL hL) := by
  refine ⟨?_, ?_, measurable_conditionalDatasetCoupling hL n,
    commonMassCoupling_isCoupling hL hhL n, ?_⟩
  · intro x z
    exact ⟨fullAlternativeMass_component_factorization hL n x z,
      nullMass_component_factorization hL n x z⟩
  · intro x i
    exact ⟨alternativeComponentLaw_eq_null_of_card_one hL hhL n x _,
      component_TV_le_quadratic hL hhL n x _, componentCoupling_isCoupling hL hhL n x _⟩
  · intro hcap
    have heps : 0 ≤ epsilon := he.1.le
    have hradius : 0 ≤ hL := hhL.1.le
    have hγ := commonMassCoupling_isCoupling hL hhL n
    let := hγ.isProbabilityMeasure
    have hcost : (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂commonMassCoupling hL n) ≤
        ENNReal.ofReal (1024*separation hL*(n : ℝ)^2*hL*deltaL hL) := by
      by_cases hn : 1 ≤ n
      · exact commonMassCoupling_hamming_cost_le_sparse cayley_of_gate hL hhL n hn hcap
      · have hn0 : n = 0 := by omega
        subst n
        simp [dHam, hammingDist]
    have hWH : WH n (signMixture hL hhL n) (dataLaw n fairNull) ≤
        ENNReal.ofReal (1024*separation hL*(n : ℝ)^2*hL*deltaL hL) := by
      exact (iInf_le_of_le (commonMassCoupling hL n) (iInf_le_of_le hγ le_rfl)).trans hcost
    refine ⟨hWH, ?_⟩
    let : IsProbabilityMeasure (signMixture hL hhL n) := by
      rw [← hγ.map_fst]
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let : IsProbabilityMeasure (dataLaw n fairNull) := by
      rw [← hγ.map_snd]
      exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    have hout := private_TV_le_coupling_cost n epsilon he M hM
      (signMixture hL hhL n) (dataLaw n fairNull) (commonMassCoupling hL n) hγ
    have hbound : ENNReal.ofReal (TV (M ∘ₘ signMixture hL hhL n)
        (M ∘ₘ dataLaw n fairNull)) ≤
        ENNReal.ofReal (2048*epsilon*separation hL*(n : ℝ)^2*hL*deltaL hL) := by
      calc
        _ ≤ ENNReal.ofReal (2*epsilon) *
            ENNReal.ofReal (1024*separation hL*(n : ℝ)^2*hL*deltaL hL) :=
          hout.trans (mul_le_mul' le_rfl hcost)
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*epsilon)]
          congr 1
          ring
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have hs := (separation_unit_range hL hhL).1
      have hd : 0 ≤ deltaL hL := by unfold deltaL; positivity
      positivity)).mp hbound

end CausalSmith.Stat.PrivateCateRoughdesign
