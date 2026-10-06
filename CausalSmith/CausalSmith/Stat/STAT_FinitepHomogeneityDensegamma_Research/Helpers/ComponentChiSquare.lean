module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentCoefficientFactorization
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentDerivative
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentSignOverlap

/-! Finite-moment homogeneity testing: Helpers/ComponentChiSquare. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Squared discrepancy quotients are nonnegative because their actual denominators are positive. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_activities_nonneg
lemma component_activities_nonneg (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) :
    0 ≤ componentEvenActivity n K M a u aug C ∧
    0 ≤ componentOddActivity n K M a u aug C := by
  have hp (labels : Labels n) := component_denominator_bounds n K M a u hK ha hu aug C labels
  constructor
  · unfold componentEvenActivity
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro labels _
    exact div_nonneg (sq_nonneg _) (le_trans (by positivity) (hp labels).1)
  · unfold componentOddActivity
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro labels _
    exact div_nonneg (sq_nonneg _) (le_trans (by positivity) (hp labels).2)

/-- Both conditional activities are nonnegative, with distinct-component products retaining their sign. [This is the stated conclusion](goal). -/
-- @node: conditional_activities_nonneg
lemma conditional_activities_nonneg (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (aug : Augmentation n K) :
    0 ≤ activityA n K M a u aug ∧ 0 ≤ activityB n K M a u aug := by
  rcases h with ⟨hn, hk, hm, hKM, hM, ha, hu, hε, hL⟩
  have hK : 0 < K := by omega
  have hc := component_activities_nonneg n K M a u hK ha hu aug
  constructor
  · unfold activityA
    exact Finset.sum_nonneg (fun C _ => (hc C).1)
  · unfold activityB
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro C _
    apply Finset.sum_nonneg
    intro C' _
    split
    · exact mul_nonneg (hc C).2 (hc C').2
    · exact le_refl _

/-- The derivative estimates and positive actual denominators give both occupancy envelopes, including exact singleton and mark-count cutoffs. [This is the stated conclusion](goal). -/
-- @node: component_activity_envelopes
lemma component_activity_envelopes (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) :
    ∀ᵐ aug ∂commonAugmentation n K M ε, ∀ C ∈ components n K M aug,
      componentEvenActivity n K M a u aug C ≤
        (if 2 ≤ C.card ∧ 2 ≤ (C.filter (fun i => aug.2.1 i)).card then
          2^14*a^4*u^4*(C.card:ℝ)^8*8^C.card else 0) ∧
      componentOddActivity n K M a u aug C ≤
        (if 2 ≤ C.card ∧ 1 ≤ (C.filter (fun i => aug.2.1 i)).card then
          2^8*a^2*u^2*(C.card:ℝ)^4*8^C.card else 0) := by
  have hd := component_discrepancy_bounds n K M a u ε L h
  rcases h with ⟨hn, hk, hm, hKM, hM, ha, hu, hε, hL⟩
  have hK : 0 < K := by omega
  filter_upwards [hd] with aug hd
  intro C hC
  constructor
  · split
    · exact componentEvenActivity_bound n K M a u hK ha hu aug C
        (fun labels => (hd C hC labels).1)
    · rename_i hcut
      have hz (labels : Labels n) : evenDiscrepancy n K M a u aug C labels = 0 := by
        by_cases hs : C.card ≤ 1
        · exact ((hd C hC labels).2.2.1 hs).1
        · exact (hd C hC labels).2.2.2.1 (by omega)
      simp [componentEvenActivity, hz]
  · split
    · exact componentOddActivity_bound n K M a u hK ha hu aug C
        (fun labels => (hd C hC labels).2.1)
    · rename_i hcut
      have hz (labels : Labels n) : oddDiscrepancy n K M a u aug C labels = 0 := by
        by_cases hs : C.card ≤ 1
        · exact ((hd C hC labels).2.2.1 hs).2
        · exact (hd C hC labels).2.2.2.2 (by omega)
      simp [componentOddActivity, hz]

/-- Conditional component comparisons: the displayed mathematical construction or bound. [This is the stated conclusion](goal). -/
lemma conditional_component_comparisons (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) :
    ∀ᵐ aug ∂commonAugmentation n K M ε,
      IsProbabilityMeasure (intermediateConditionalLaw n K M a u aug) ∧
      IsProbabilityMeasure (nullConditionalLaw n K M a u aug) ∧
      IsProbabilityMeasure (alternativeConditionalLaw n K M a u aug) ∧
      0 ≤ activityA n K M a u aug ∧ 0 ≤ activityB n K M a u aug ∧
      1+Causalean.Stat.chiSqDiv (intermediateConditionalLaw n K M a u aug) (nullConditionalLaw n K M a u aug) ≤ Real.exp (activityA n K M a u aug) ∧
      1+Causalean.Stat.chiSqDiv (alternativeConditionalLaw n K M a u aug) (intermediateConditionalLaw n K M a u aug) ≤ Real.exp (activityB n K M a u aug)  := by
  have hfactor : ∀ᵐ aug ∂commonAugmentation n K M ε,
      1+Causalean.Stat.chiSqDiv (intermediateConditionalLaw n K M a u aug)
        (nullConditionalLaw n K M a u aug) =
          ∏ C ∈ components n K M aug, (1 + componentEvenActivity n K M a u aug C) ∧
      1+Causalean.Stat.chiSqDiv (alternativeConditionalLaw n K M a u aug)
        (intermediateConditionalLaw n K M a u aug) =
          ∏ j ∈ (components n K M aug).image (pairIndex M aug),
            ((∏ C ∈ (components n K M aug).filter (fun C => pairIndex M aug C = j),
                (1 + componentOddActivity n K M a u aug C)) +
              ∏ C ∈ (components n K M aug).filter (fun C => pairIndex M aug C = j),
                (1 - componentOddActivity n K M a u aug C))/2 := by
    have hK : 0 < K := by
      have := h.2.2.2.1
      have := h.2.2.2.2.1
      omega
    have hodd : ∀ᵐ aug ∂commonAugmentation n K M ε,
        1+Causalean.Stat.chiSqDiv (alternativeConditionalLaw n K M a u aug)
          (intermediateConditionalLaw n K M a u aug) =
            ∏ j ∈ (components n K M aug).image (pairIndex M aug),
              ((∏ C ∈ (components n K M aug).filter (fun C => pairIndex M aug C = j),
                  (1 + componentOddActivity n K M a u aug C)) +
                ∏ C ∈ (components n K M aug).filter (fun C => pairIndex M aug C = j),
                  (1 - componentOddActivity n K M a u aug C))/2 := by
      have hstructure : ∀ᵐ aug ∂commonAugmentation n K M ε,
          ∃ g : Finset (Fin n) → {j // j ∈ (components n K M aug).image (pairIndex M aug)},
            (∀ C ∈ components n K M aug, (g C).val = pairIndex M aug C) ∧
            (∀ l : Labels n, alternativeConditionalDensity n K M a u aug l =
              (Fintype.card ({j // j ∈ (components n K M aug).image (pairIndex M aug)} → Bool) : ℝ)⁻¹ *
                ∑ s : {j // j ∈ (components n K M aug).image (pairIndex M aug)} → Bool,
                  ∏ C ∈ components n K M aug,
                    componentDensity true (s (g C)) n K M a u aug C l) := by
        classical
        have hn : 2 ≤ n := h.1
        have hM2 : 2 ≤ M := h.2.2.2.2.1
        have hM : 0 < M := by omega
        have hK : 0 < K := by
          have := h.2.2.2.1
          omega
        obtain ⟨k, hk⟩ := h.2.1
        obtain ⟨m, hm⟩ := h.2.2.1
        have hMK : M ≤ K := by
          have := h.2.2.2.1
          omega
        have hmk : m ≤ k := by
          apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
          rw [← hm, ← hk]
          exact hMK
        have hdiv : M ∣ K := by
          rw [hm, hk]
          exact Nat.pow_dvd_pow 2 hmk
        have heven : 2 ∣ M := by
          have hmpos : 0 < m := by
            by_contra hm0
            have : m = 0 := by omega
            simp [hm, this] at hM2
          obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
          rw [hm, pow_succ]
          simpa only [mul_comm] using dvd_mul_right 2 (2 ^ r)
        filter_upwards [commonAugmentation_ae_actual_disclosure n K M ε] with aug hactual
        let i0 : Fin n := ⟨0, by omega⟩
        let C0 : Finset (Fin n) := componentOf n K M aug i0
        have hC0 : C0 ∈ components n K M aug := by
          exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩
        let J := {j // j ∈ (components n K M aug).image (pairIndex M aug)}
        let j0 : J := ⟨pairIndex M aug C0,
          Finset.mem_image.mpr ⟨C0, hC0, rfl⟩⟩
        let g : Finset (Fin n) → J := fun C =>
          if hC : C ∈ components n K M aug then
            ⟨pairIndex M aug C, Finset.mem_image.mpr ⟨C, hC, rfl⟩⟩
          else j0
        have hg : ∀ C ∈ components n K M aug, (g C).val = pairIndex M aug C := by
          intro C hC
          simp [g, hC]
        have hjbound (j : J) : j.val < M / 2 := by
          obtain ⟨C, hC, hCj⟩ := Finset.mem_image.mp j.property
          rw [← hCj]
          exact pairIndex_lt_half n K M hM heven aug hC
        let e : J ↪ Fin (M / 2) :=
          ⟨fun j => ⟨j.val, hjbound j⟩, fun x y hxy => by
            apply Subtype.ext
            exact Fin.ext_iff.mp hxy⟩
        have heval (C : Finset (Fin n)) : (e (g C)).val = (g C).val := rfl
        refine ⟨g, hg, ?_⟩
        intro l
        unfold alternativeConditionalDensity
        have hhalf : (M : ℤ) / 2 = ((M / 2 : ℕ) : ℤ) := by
          omega
        have hnorm : (2 : ℝ) ^ (-(M / 2 : ℤ)) =
            (Fintype.card (Fin (M / 2) → Bool) : ℝ)⁻¹ := by
          rw [hhalf, zpow_neg, zpow_natCast]
          simp
        rw [hnorm]
        calc
          _ = (Fintype.card (Fin (M / 2) → Bool) : ℝ)⁻¹ *
              ∑ σ : Fin (M / 2) → Bool,
                ∏ C ∈ components n K M aug,
                  componentDensity true (σ (e (g C))) n K M a u aug C l := by
            congr 1
            apply Finset.sum_congr rfl
            intro σ _
            apply conditional_record_component_factorization true n K M a u
              hK hM hdiv heven σ aug l hactual (fun C => e (g C))
            intro C hC
            rw [heval, hg C hC]
          _ = (Fintype.card (J → Bool) : ℝ)⁻¹ *
              ∑ s : J → Bool,
                ∏ C ∈ components n K M aug,
                  componentDensity true (s (g C)) n K M a u aug C l := by
            exact uniform_bool_cube_embedding e (fun s =>
              ∏ C ∈ components n K M aug,
                componentDensity true (s (g C)) n K M a u aug C l)
      filter_upwards [hstructure] with aug hs
      obtain ⟨g, hg, hdensity⟩ := hs
      rw [alternative_chiSq_of_component_factorization n K M a u hK
        h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug g hdensity]
      have hfilter (j : {j // j ∈ (components n K M aug).image (pairIndex M aug)}) :
          (components n K M aug).filter (fun C => g C = j) =
            (components n K M aug).filter (fun C => pairIndex M aug C = j.val) := by
        ext C
        simp only [Finset.mem_filter]
        by_cases hC : C ∈ components n K M aug
        · simp only [hC, true_and, Subtype.ext_iff, hg C hC]
        · simp only [hC, false_and]
      simp_rw [hfilter]
      exact Finset.prod_coe_sort ((components n K M aug).image (pairIndex M aug))
        (fun j => ((∏ C ∈ (components n K M aug).filter (fun C => pairIndex M aug C = j),
          (1 + componentOddActivity n K M a u aug C)) +
          ∏ C ∈ (components n K M aug).filter (fun C => pairIndex M aug C = j),
            (1 - componentOddActivity n K M a u aug C))/2)
    filter_upwards [hodd] with aug ho
    exact ⟨intermediate_null_chiSq_factorization n K M a u hK
      h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug, ho⟩
  have hrest : ∀ᵐ aug ∂commonAugmentation n K M ε,
      1+Causalean.Stat.chiSqDiv (intermediateConditionalLaw n K M a u aug) (nullConditionalLaw n K M a u aug) ≤ Real.exp (activityA n K M a u aug) ∧
      1+Causalean.Stat.chiSqDiv (alternativeConditionalLaw n K M a u aug) (intermediateConditionalLaw n K M a u aug) ≤ Real.exp (activityB n K M a u aug) := by
    filter_upwards [hfactor] with aug hf
    have hK : 0 < K := by
      have := h.2.2.2.1
      have := h.2.2.2.2.1
      omega
    have hc := component_activities_nonneg n K M a u hK
      h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
    constructor
    · rw [hf.1]
      exact component_product_le_exp_sum _ _ (fun C _ => (hc C).1)
    · rw [hf.2]
      exact grouped_shared_sign_product_le_exp _ _ _ (fun C _ => (hc C).2)
  filter_upwards [hrest] with aug hr
  have hn := conditional_activities_nonneg n K M a u ε L h aug
  have hK : 0 < K := by
    have := h.2.2.2.1
    have := h.2.2.2.2.1
    omega
  have hprob := alternativeConditionalLaw_isProbabilityMeasure n K M a u hK
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
  have hnull := nullConditionalLaw_isProbabilityMeasure n K M a u hK
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
  have hmid := intermediateConditionalLaw_isProbabilityMeasure n K M a u hK
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
  exact ⟨hmid, hnull, hprob, hn.1, hn.2, hr.1, hr.2⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
