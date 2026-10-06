module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActiveCapacityBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenAllocationSummation

/-!
# Disjoint active rows of the actual conditional likelihood

Compatible response supports are reindexed by their hidden-only active rows.
The masked allocation coefficient then satisfies the existing good-event energy
bound with the exact number of hidden-only rows.
-/

public section
open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- A response support containing the revealed-active rows is uniquely their
union with a subset of the complementary labeled rows.  [For the stated data and conditions](hyp:B,A,F,hzero), [the stated conclusion holds](goal). -/
-- @node: active_support_sum_reindex
lemma active_support_sum_reindex (B : ℕ) (A : Finset (Fin B))
    (F : Finset (Fin B) → ℝ) (hzero : ∀ T, ¬ A ⊆ T → F T = 0) :
    (∑ T : Finset (Fin B), F T) =
      ∑ E ∈ (Finset.univ \ A).powerset, F (A ∪ E) := by
  classical
  rw [← Finset.sum_subset (Finset.filter_subset (fun T => A ⊆ T) Finset.univ)
    (fun T _ hT => hzero T (by simpa using hT))]
  apply Finset.sum_bij (fun T _ => T \ A)
  · intro T hT
    simp only [Finset.mem_powerset]
    intro ℓ hℓ
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hℓ).2⟩
  · intro T hT U hU he
    have hAT := (Finset.mem_filter.mp hT).2
    have hAU := (Finset.mem_filter.mp hU).2
    ext ℓ
    by_cases hℓ : ℓ ∈ A
    · simp [hAT hℓ, hAU hℓ]
    · have := congrArg (fun S => ℓ ∈ S) he
      simpa [hℓ] using this
  · intro E hE
    refine ⟨A ∪ E, by simp, ?_⟩
    ext ℓ
    have hEA : ℓ ∈ E → ℓ ∉ A := fun hℓ =>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hE hℓ)).2
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  · intro T hT
    congr 1
    have hAT := (Finset.mem_filter.mp hT).2
    ext ℓ
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hℓ
      by_cases hA : ℓ ∈ A
      · exact Or.inl hA
      · exact Or.inr ⟨hℓ, hA⟩
    · rintro (hA | ⟨hℓ, _⟩)
      · exact hAT hA
      · exact hℓ

/-- The actual coefficient's squared norm splits over disjoint hidden-only
active rows, with incompatible supports contributing zero.  [For the stated data and conditions](hyp:B,d,h,u,j,k), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_disjoint_energy_sum
lemma allocationSupportCoeff_disjoint_energy_sum (B d : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (k : ℕ) :
    (∑ T : Finset (Fin B), ∫ y : Fin B → ℝ,
      allocationSupportCoeff B d h u j k T y ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) =
    ∑ E ∈ (Finset.univ \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).powerset,
      ∫ y : Fin B → ℝ,
        allocationSupportCoeff B d h u j k
          ((Finset.univ.filter (fun ℓ => j ℓ ≠ 0)) ∪ E) y ^ 2
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w))) := by
  apply active_support_sum_reindex
  intro T hT
  have hn : ¬ ∀ ℓ, j ℓ ≠ 0 → ℓ ∈ T := by
    simpa only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and] using hT
  simp_rw [allocationSupportCoeff_eq_rowwise_or_zero, if_neg hn]
  simp

/-- A masked support uses no more than all hidden slots and no more than degree
times the number of its active rows.  [For the stated data and conditions](hyp:B,d,u,T,hu), [the stated conclusion holds](goal). -/
-- @node: activeCapacity_sum_bounds
lemma activeCapacity_sum_bounds (B d : ℕ) (u : Fin B → ℕ)
    (T : Finset (Fin B)) (hu : ∀ ℓ, u ℓ ≤ d) :
    (∑ ℓ, activeCapacity B u T ℓ) ≤ ∑ ℓ, u ℓ ∧
      (∑ ℓ, activeCapacity B u T ℓ) ≤ d * T.card := by
  constructor
  · apply Finset.sum_le_sum
    intro ℓ _
    simp only [activeCapacity]
    split_ifs <;> omega
  · rw [show (∑ ℓ, activeCapacity B u T ℓ) = ∑ ℓ ∈ T, u ℓ by
      simp [activeCapacity]]
    calc
      _ ≤ ∑ ℓ ∈ T, d := Finset.sum_le_sum (fun ℓ _ => hu ℓ)
      _ = _ := by simp [Nat.mul_comm]

/-- Requiring positive degree on every hidden-only active row gives the exact
minimum total hidden degree needed by the binomial-ratio contraction.  [For the stated data and conditions](hyp:B,u,j,T,t,ht), [the stated conclusion holds](goal). -/
-- @node: active_support_min_hidden_degree
lemma active_support_min_hidden_degree (B : ℕ) (u j : Fin B → ℕ)
    (T : Finset (Fin B)) (t : ∀ ℓ, Fin (u ℓ + 1))
    (ht : ∀ ℓ, if j ℓ ≠ 0 then True else
      if ℓ ∈ T then 0 < (t ℓ).val else (t ℓ).val = 0) :
    (T \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card ≤ ∑ ℓ, (t ℓ).val := by
  classical
  calc
    _ = ∑ ℓ ∈ T \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0), 1 := by simp
    _ ≤ ∑ ℓ ∈ T \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0), (t ℓ).val := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      obtain ⟨hT, hA⟩ := Finset.mem_sdiff.mp hℓ
      have hj : j ℓ = 0 := by simpa using hA
      have hp := ht ℓ
      simp only [hj, ne_eq, not_true_eq_false, if_false, hT, if_true] at hp
      omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)

/-- Each compatible actual support satisfies the all-hidden-degrees energy
bound after masking inactive capacities, with no independence of hidden rows.  [For the stated data and conditions](hyp:B,d,M,h,u,j,T,hB,hd,hu,hM,hgood,hT), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_summed_energy_le
lemma allocationSupportCoeff_summed_energy_le (B d M : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (T : Finset (Fin B))
    (hB : 0 < B) (hd : 0 < d) (hu : ∀ ℓ, u ℓ ≤ d)
    (hM : (∑ ℓ, u ℓ) ≤ M)
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M)
    (hT : ∀ ℓ, j ℓ ≠ 0 → ℓ ∈ T) :
    (∑ k ∈ Finset.range (M + 1),
      (∫ y : Fin B → ℝ, allocationSupportCoeff B d h u j k T y ^ 2
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w)))) / (M.choose k : ℝ)) ≤
      (min 1 (4 * ((Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card +
        (T \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card : ℕ) / (B : ℝ))) ^
          (T \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card *
        ∏ ℓ, ∑ t : Fin (activeCapacity B u T ℓ + 1),
          if (if j ℓ ≠ 0 then True else
            if ℓ ∈ T then 0 < t.val else t.val = 0) then
            ((activeCapacity B u T ℓ).choose t.val : ℝ) *
              gamma d h (j ℓ + t.val) else 0 := by
  classical
  have hAT : Finset.univ.filter (fun ℓ => j ℓ ≠ 0) ⊆ T := by
    intro ℓ hℓ
    exact hT ℓ (Finset.mem_filter.mp hℓ).2
  have hcard : (Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card +
      (T \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card = T.card := by
    rw [Finset.card_sdiff_of_subset hAT]
    have := Finset.card_le_card hAT
    omega
  have hb := activeCapacity_sum_bounds B d u T hu
  have hmask (k : ℕ) (y : Fin B → ℝ) :=
    allocationSupportCoeff_activeCapacity B d h u j k T y
  have hrow (k : ℕ) (y : Fin B → ℝ) :=
    allocationSupportCoeff_eq_rowwise B d h (activeCapacity B u T) j k T hT y
  simp_rw [hmask, hrow]
  have hbound := hidden_allocation_rowwise_summed_energy_le B d M
    (Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card
    (T \ Finset.univ.filter (fun ℓ => j ℓ ≠ 0)).card h
    (activeCapacity B u T) j
    (fun ℓ t => if j ℓ ≠ 0 then True else
      if ℓ ∈ T then 0 < t.val else t.val = 0) hB hd (hb.1.trans hM)
    (by simpa only [hcard] using hb.2) hgood
    (fun t ht => active_support_min_hidden_degree B (activeCapacity B u T) j T t ht)
  convert hbound using 1 <;> congr 2
  · funext k
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    congr 1
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> rfl
  · funext ℓ
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> rfl

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
