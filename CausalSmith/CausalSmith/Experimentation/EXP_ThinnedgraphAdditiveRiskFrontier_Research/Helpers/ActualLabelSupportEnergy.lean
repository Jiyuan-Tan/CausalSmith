module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActualLabelWalshBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenAllocationOrthogonality

/-!
# Active response supports of the actual labeled coefficients

The capacity-constrained coefficient is partitioned by its actual positive-degree
response rows. Orthogonality gives an exact decomposition of its energy without
assuming orthogonality between different positive degrees within a row.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The positive response rows of a revealed and hidden degree vector. -/
-- @node: allocationResponseSupport
def allocationResponseSupport (B : ℕ) (j t : Fin B → ℕ) : Finset (Fin B) :=
  Finset.univ.filter (fun ℓ => j ℓ + t ℓ ≠ 0)

/-- Restrict the exact bounded allocation coefficient to one response support. -/
-- @node: allocationSupportCoeff
def allocationSupportCoeff (B d : ℕ) (h : ℝ) (u j : Fin B → ℕ)
    (k : ℕ) (T : Finset (Fin B)) (y : Fin B → ℝ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) =>
    k = ∑ ℓ, (t ℓ).val ∧
      allocationResponseSupport B j (fun ℓ => (t ℓ).val) = T),
    (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
      ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ)

/-- Every bounded allocation belongs to precisely one actual response support.  [For the stated data and conditions](hyp:B,d,h,u,j,k,y), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_sum
lemma allocationSupportCoeff_sum (B d : ℕ) (h : ℝ) (u j : Fin B → ℕ)
    (k : ℕ) (y : Fin B → ℝ) :
    (∑ T : Finset (Fin B), allocationSupportCoeff B d h u j k T y) =
      ∑ t ∈ Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) =>
        k = ∑ ℓ, (t ℓ).val),
        (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
          ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ) := by
  unfold allocationSupportCoeff
  simpa only [Finset.filter_filter] using
    (Finset.sum_fiberwise
      (Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) => k = ∑ ℓ, (t ℓ).val))
      (fun t => allocationResponseSupport B j (fun ℓ => (t ℓ).val))
      (fun t => (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
        ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ)))

/-- Distinct actual response supports contribute additive squared norms.  [For the stated data and conditions](hyp:B,d,h,hd,u,j,k), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_energy
lemma allocationSupportCoeff_energy (B d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (u j : Fin B → ℕ) (k : ℕ) :
    (∫ y : Fin B → ℝ,
      (∑ t ∈ Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) =>
        k = ∑ ℓ, (t ℓ).val),
        (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
          ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ)) ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) =
      ∑ T : Finset (Fin B), ∫ y : Fin B → ℝ,
        allocationSupportCoeff B d h u j k T y ^ 2
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w))) := by
  simp_rw [← allocationSupportCoeff_sum B d h u j k]
  unfold allocationSupportCoeff
  apply hidden_active_support_group_energy B d h hd
    Finset.univ
    (fun T => Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) =>
      k = ∑ ℓ, (t ℓ).val ∧
        allocationResponseSupport B j (fun ℓ => (t ℓ).val) = T))
    (fun _ t => ∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ))
    (fun _ t ℓ => j ℓ + (t ℓ).val) id
  · intro T _ t ht ℓ
    have he := (Finset.mem_filter.mp ht).2.2
    rw [← he]
    simp [allocationResponseSupport]
  · intro T _ U _ hTU
    exact hTU

/-- The actual enumerated-label coefficient has the same support decomposition,
with every original row capacity and labeled revealed count retained.  [For the stated data and conditions](hyp:n,B,d,h,hd,H,i), [the stated conclusion holds](goal). -/
-- @node: actualLabelWalshCoeff_support_energy
lemma actualLabelWalshCoeff_support_energy (n B d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (H : OffDiag (Fin n) → Bool)
    (i : Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
      Fin (undiscovered n B d H + 1)) :
    (∫ y : Fin B → ℝ, actualLabelWalshCoeff n B d h H i y ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) =
      ∑ T : Finset (Fin B), ∫ y : Fin B → ℝ,
        allocationSupportCoeff B d h (capacity n B d H)
          (fun ℓ => ((i.1.map (revealedLabelEmbedding n B d H)) ∩
            revealedSources n B d H ℓ).card) i.2.val T y ^ 2
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w))) := by
  simp_rw [actualLabelWalshCoeff, groupedHiddenWalshCoeff_eq_bounded]
  exact allocationSupportCoeff_energy B d h hd _ _ _

/-- A coefficient fiber's support condition is exactly a rowwise restriction:
revealed-active rows allow every hidden degree, hidden-only active rows require a
positive degree, and all remaining rows require degree zero.  [For the stated data and conditions](hyp:B,j,t,T,hT), [the stated conclusion holds](goal). -/
-- @node: allocationResponseSupport_eq_iff_rowwise
lemma allocationResponseSupport_eq_iff_rowwise (B : ℕ) (j t : Fin B → ℕ)
    (T : Finset (Fin B)) (hT : ∀ ℓ, j ℓ ≠ 0 → ℓ ∈ T) :
    allocationResponseSupport B j t = T ↔
      ∀ ℓ, if j ℓ ≠ 0 then True else if ℓ ∈ T then 0 < t ℓ else t ℓ = 0 := by
  constructor
  · intro he ℓ
    have hm : j ℓ + t ℓ ≠ 0 ↔ ℓ ∈ T := by
      rw [← he]
      simp [allocationResponseSupport]
    split_ifs with hj hmem
    · have : j ℓ = 0 := by simpa using hj
      have := hm.mpr hmem
      omega
    · have : j ℓ = 0 := by simpa using hj
      have := mt hm.mp hmem
      omega
  · intro ht
    ext ℓ
    simp only [allocationResponseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ℓ ≠ 0
    · have hmem := hT ℓ hj
      simp only [hmem, iff_true]
      omega
    · have hj0 : j ℓ = 0 := by simpa using hj
      have := ht ℓ
      by_cases hmem : ℓ ∈ T
      · simp only [hj, hmem, if_false, if_true] at this
        simp only [hj0, zero_add, hmem, iff_true]
        omega
      · simp only [hj, hmem, if_false] at this
        simp [hj0, this, hmem]

/-- Each support-group coefficient is the exact rowwise-restricted allocation
sum needed by the allocation-energy bound, with no new statistical premise.  [For the stated data and conditions](hyp:B,d,h,u,j,k,T,hT,y), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_eq_rowwise
lemma allocationSupportCoeff_eq_rowwise (B d : ℕ) (h : ℝ) (u j : Fin B → ℕ)
    (k : ℕ) (T : Finset (Fin B)) (hT : ∀ ℓ, j ℓ ≠ 0 → ℓ ∈ T)
    (y : Fin B → ℝ) :
    allocationSupportCoeff B d h u j k T y =
      ∑ t ∈ Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) =>
        (∀ ℓ, if j ℓ ≠ 0 then True else
          if ℓ ∈ T then 0 < (t ℓ).val else (t ℓ).val = 0) ∧
            k = ∑ ℓ, (t ℓ).val),
        (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
          ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ) := by
  unfold allocationSupportCoeff
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    allocationResponseSupport_eq_iff_rowwise B j _ T hT, and_comm]

/-- A response support omitting any revealed-active row has no compatible
allocation; every compatible support gives the exact rowwise coefficient.  [For the stated data and conditions](hyp:B,d,h,u,j,k,T,y), [the stated conclusion holds](goal). -/
-- @node: allocationSupportCoeff_eq_rowwise_or_zero
lemma allocationSupportCoeff_eq_rowwise_or_zero (B d : ℕ) (h : ℝ)
    (u j : Fin B → ℕ) (k : ℕ) (T : Finset (Fin B)) (y : Fin B → ℝ) :
    allocationSupportCoeff B d h u j k T y =
      if ∀ ℓ, j ℓ ≠ 0 → ℓ ∈ T then
        ∑ t ∈ Finset.univ.filter (fun t : ∀ ℓ, Fin (u ℓ + 1) =>
          (∀ ℓ, if j ℓ ≠ 0 then True else
            if ℓ ∈ T then 0 < (t ℓ).val else (t ℓ).val = 0) ∧
              k = ∑ ℓ, (t ℓ).val),
          (∏ ℓ, ((u ℓ).choose (t ℓ).val : ℝ)) *
            ∏ ℓ, walshCoeff d h (j ℓ + (t ℓ).val) (y ℓ)
      else 0 := by
  split_ifs with hT
  · exact allocationSupportCoeff_eq_rowwise B d h u j k T hT y
  · unfold allocationSupportCoeff
    apply Finset.sum_eq_zero
    intro t ht
    exfalso
    apply hT
    intro ℓ hj
    have he := (Finset.mem_filter.mp ht).2.2
    rw [← he]
    simp only [allocationResponseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-- The exact nonconstant energy of the actual posterior splits by response
support before any Cauchy–Schwarz bound is applied.  [For the stated data and conditions](hyp:n,B,d,h,hd,H), [the stated conclusion holds](goal). -/
-- @node: actualLabelEnergy_support_sum
lemma actualLabelEnergy_support_sum (n B d : ℕ) (h : ℝ) (hd : 1 ≤ d)
    (H : OffDiag (Fin n) → Bool) :
    actualLabelEnergy n B d h H =
      ∑ i ∈ (Finset.univ : Finset
        (Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
          Fin (undiscovered n B d H + 1))).erase (∅, 0),
        (∑ T : Finset (Fin B), ∫ y : Fin B → ℝ,
          allocationSupportCoeff B d h (capacity n B d H)
            (fun ℓ => ((i.1.map (revealedLabelEmbedding n B d H)) ∩
              revealedSources n B d H ℓ).card) i.2.val T y ^ 2
            ∂Measure.pi (fun _ : Fin B => volume.withDensity
              (fun w => ENNReal.ofReal (refDensity d h w)))) /
          (Nat.choose (undiscovered n B d H) i.2.val : ℝ) := by
  unfold actualLabelEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [actualLabelWalshCoeff_support_energy n B d h hd H i]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
