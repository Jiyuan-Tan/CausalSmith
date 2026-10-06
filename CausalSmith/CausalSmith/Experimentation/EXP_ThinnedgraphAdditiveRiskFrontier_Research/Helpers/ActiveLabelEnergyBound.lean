module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActiveSupportBridge

/-!
# Active-support bound for the original labeled coefficient energy

Sum the masked allocation bound over disjoint hidden-only response supports,
then retain the actual revealed-label indexing and remove its constant term.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The rowwise energy envelope for one exact revealed-label degree vector. -/
-- @node: activeSupportEnergyBound
def activeSupportEnergyBound (B d : ℕ) (h : ℝ) (u j : Fin B → ℕ) : ℝ :=
  let A := Finset.univ.filter (fun ℓ => j ℓ ≠ 0)
  ∑ E ∈ (Finset.univ \ A).powerset,
    (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
      ∏ ℓ, ∑ t : Fin (activeCapacity B u (A ∪ E) ℓ + 1),
        if (if j ℓ ≠ 0 then True else
          if ℓ ∈ A ∪ E then 0 < t.val else t.val = 0) then
          ((activeCapacity B u (A ∪ E) ℓ).choose t.val : ℝ) *
            gamma d h (j ℓ + t.val) else 0

/-- The full hidden-degree energy for a fixed revealed subset is bounded by
its disjoint active-support envelope, using the original total hidden capacity.  [For the stated data and conditions](hyp:B,d,M,h,u,j,hB,hd,hu,hM,hgood), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_total_energy_le
lemma allocationSupportCoeff_total_energy_le (B d M : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (hB : 0 < B) (hd : 0 < d)
    (hu : ∀ ℓ, u ℓ ≤ d) (hM : (∑ ℓ, u ℓ) ≤ M)
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ M) :
    (∑ k ∈ Finset.range (M + 1),
      (∑ T : Finset (Fin B), ∫ y : Fin B → ℝ,
        allocationSupportCoeff B d h u j k T y ^ 2
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w)))) / (M.choose k : ℝ)) ≤
      activeSupportEnergyBound B d h u j := by
  classical
  simp_rw [allocationSupportCoeff_disjoint_energy_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  unfold activeSupportEnergyBound
  apply Finset.sum_le_sum
  intro E hE
  let A := Finset.univ.filter (fun ℓ => j ℓ ≠ 0)
  have hEA : Disjoint A E := by
    apply Finset.disjoint_left.mpr
    intro ℓ hA hℓ
    exact (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hE hℓ)).2 hA
  have hs : (A ∪ E) \ A = E := Finset.union_sdiff_cancel_left hEA
  have hb := allocationSupportCoeff_summed_energy_le B d M h u j
    (A ∪ E) hB hd hu hM hgood
    (fun ℓ hj => Finset.mem_union_left E (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
  dsimp only [A] at hs hb
  rw [hs] at hb
  exact hb

/-- The single removed coefficient has unit reference energy. This identifies
its contribution before the full labeled sum is bounded.  [For the stated data and conditions](hyp:n,B,d,h,H), [the stated conclusion holds](goal). -/
-- @node: actualLabelWalshCoeff_constant_integral
lemma actualLabelWalshCoeff_constant_integral (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) :
    (∫ y : Fin B → ℝ, actualLabelWalshCoeff n B d h H (∅, 0) y ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) = 1 := by
  let := referenceRowLaw_probability d h
  calc
    _ = ∫ _ : Fin B → ℝ, (1 : ℝ)
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w))) := by
      apply integral_congr_ae
      filter_upwards [referenceRows_positive_ae B d h] with y hy
      simp [actualLabelWalshCoeff, groupedHiddenWalshCoeff_empty_zero_pos n B d h H y hy]
    _ = 1 := by simp

/-- Restoring exactly the constant coefficient gives the complete original-label
energy sum, with all hidden-degree denominators unchanged.  [For the stated data and conditions](hyp:n,B,d,h,H), [the stated conclusion holds](goal). -/
-- @node: actualLabelEnergy_add_one
lemma actualLabelEnergy_add_one (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) :
    actualLabelEnergy n B d h H + 1 =
      ∑ i : Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
          Fin (undiscovered n B d H + 1),
        (∫ y : Fin B → ℝ, actualLabelWalshCoeff n B d h H i y ^ 2
          ∂Measure.pi (fun _ : Fin B => volume.withDensity
            (fun w => ENNReal.ofReal (refDensity d h w)))) /
          (Nat.choose (undiscovered n B d H) i.2.val : ℝ) := by
  unfold actualLabelEnergy
  have hc : (∫ y : Fin B → ℝ, actualLabelWalshCoeff n B d h H (∅, 0) y ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) /
          (Nat.choose (undiscovered n B d H) 0 : ℝ) = 1 := by
    simp [actualLabelWalshCoeff_constant_integral]
  rw [← hc]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ _)

/-- Sum the active-support envelope over the actual labeled revealed subsets. -/
-- @node: actualLabelActiveEnvelope
def actualLabelActiveEnvelope (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) : ℝ :=
  ∑ J : Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card),
    activeSupportEnergyBound B d h (capacity n B d H)
      (fun ℓ => ((J.map (revealedLabelEmbedding n B d H)) ∩
        revealedSources n B d H ℓ).card)

/-- On the good event the exact nonconstant labeled energy is bounded by the
summed disjoint-support envelope after subtracting its one constant coefficient.  [For the stated data and conditions](hyp:n,B,d,h,hB,hd,H,hgood), [the stated conclusion holds](goal). -/
-- @node: actualLabelEnergy_le_activeEnvelope
lemma actualLabelEnergy_le_activeEnvelope (n B d : ℕ) (h : ℝ)
    (hB : 0 < B) (hd : 0 < d) (H : OffDiag (Fin n) → Bool)
    (hgood : (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H) :
    actualLabelEnergy n B d h H ≤ actualLabelActiveEnvelope n B d h H - 1 := by
  have hs : actualLabelEnergy n B d h H + 1 ≤ actualLabelActiveEnvelope n B d h H := by
    rw [actualLabelEnergy_add_one, Fintype.sum_prod_type]
    unfold actualLabelActiveEnvelope
    apply Finset.sum_le_sum
    intro J _
    simp_rw [actualLabelWalshCoeff_support_energy n B d h hd H]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (∑ T : Finset (Fin B), ∫ y : Fin B → ℝ,
        allocationSupportCoeff B d h (capacity n B d H)
          (fun ℓ => ((J.map (revealedLabelEmbedding n B d H)) ∩
            revealedSources n B d H ℓ).card) k T y ^ 2
          ∂Measure.pi (fun _ : Fin B => volume.withDensity
            (fun w => ENNReal.ofReal (refDensity d h w)))) /
        ((undiscovered n B d H).choose k : ℝ))]
    apply allocationSupportCoeff_total_energy_le B d (undiscovered n B d H) h
      (capacity n B d H) _ hB hd
    · intro ℓ
      exact Nat.sub_le _ _
    · rfl
    · exact hgood
  linarith

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
