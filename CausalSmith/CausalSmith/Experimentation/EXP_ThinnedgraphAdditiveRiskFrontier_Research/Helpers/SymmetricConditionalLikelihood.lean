module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.UniformHiddenSelection

/-!
# Conditional likelihood with symmetric hidden polynomials

The uniform original-label allocation average is replaced by its exact
binomial-weighted symmetric polynomial. The full graph and assignment marginal
and all reference-zero endpoints remain those of the actual experiment.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The posterior response density using exact binomial-weighted symmetric hidden polynomials,
extended by zero at incompatible graphs and reference-density zeros. -/
-- @node: symmetricHiddenWalshDensity
def symmetricHiddenWalshDensity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) : ℝ :=
  if hs : Nonempty (CompatiblePartition n B d hz.1) then
    if ∀ ℓ, 0 < refDensity d h (y ℓ) then
      (∏ ℓ, refDensity d h (y ℓ)) *
        (∑ J ∈ Fintype.piFinset
          (fun ℓ : Fin B => (revealedSources n B d hz.1 ℓ).powerset),
          (∏ ℓ, ∏ j ∈ J ℓ, signOf (hz.2 j)) *
          ∑ k ∈ Fintype.piFinset
            (fun ℓ : Fin B => Finset.range (capacity n B d hz.1 ℓ + 1)),
            (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
              ((∏ ℓ, (Nat.choose (capacity n B d hz.1 ℓ) (k ℓ) : ℝ)) *
                symmetricSignPoly (undiscovered n B d hz.1) (∑ ℓ, k ℓ)
                  (fun i => hz.2 (hiddenSourceLabelEmbedding n B d hfit hz.1
                    ((hiddenSourceEnumeration n B d hfit hz.1 hs.some).symm i)))))
    else 0
  else 0

/-- The symmetric hidden-subset expansion gives the full actual response density,
including every zero-density endpoint.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,hz,hH,y), [the stated conclusion holds](goal). -/
-- @node: symmetricHiddenWalshDensity_eq_blockDensity
lemma symmetricHiddenWalshDensity_eq_blockDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n))
    (hH : ValidRetainedGraph n B d hz.1) (y : Fin B → ℝ) :
    symmetricHiddenWalshDensity n B d hfit h hz y =
      blockDensity n B d true h hz.1 hz.2 y := by
  have hs : Nonempty (CompatiblePartition n B d hz.1) := by
    obtain ⟨_, s, hs⟩ := hH
    exact ⟨⟨s, hs⟩⟩
  rw [symmetricHiddenWalshDensity, dif_pos hs]
  split_ifs with hy
  · have he := blockDensity_symmetric_hidden_selection_expansion
      n B d hd hfit h hz.1 hz.2 hs.some y hy
    rw [← he]
    exact mul_div_cancel₀ _ (ne_of_gt (Finset.prod_pos (fun ℓ _ => hy ℓ)))
  · obtain ⟨ℓ, hℓ⟩ := not_forall.mp hy
    have hz0 : refDensity d h (y ℓ) = 0 :=
      le_antisymm (not_lt.mp hℓ) (refDensity_nonneg d h (y ℓ))
    exact (blockDensity_zero_of_reference_zero
      n B d hd hfit h hz.1 hz.2 hs.some y ℓ hz0).symm

/-- The reduced law retains its detailed graph and entire assignment while using
the symmetric hidden-subset likelihood.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq), [the stated conclusion holds](goal). -/
lemma reducedBlockLaw_symmetric_hidden_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1) :
    reducedBlockLaw n B d (thinnedDesign (Fin n) q) true h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
        (volume.withDensity (fun y => ENNReal.ofReal
          (symmetricHiddenWalshDensity n B d hfit h hz y))).map
            (fun y => (hz.1, hz.2, y))) := by
  rw [reducedBlockLaw_hidden_word_walsh_representation n B d h q hn hB hd hfit hh hq]
  apply MeasureTheory.Measure.bind_congr_right
  have hv : ∀ᵐ hz ∂(graphAssignMarginal n B d (thinnedDesign (Fin n) q)),
      ValidRetainedGraph n B d hz.1 :=
    (MeasureTheory.ae_map_iff (by fun_prop) (by measurability)).mp
      (retainedGraphMarginal_valid n B d (thinnedDesign (Fin n) q) hfit)
  filter_upwards [hv] with hz hH
  simp_rw [hiddenWordWalshDensity_eq_blockDensity n B d hd hfit h hz hH,
    symmetricHiddenWalshDensity_eq_blockDensity n B d hd hfit h hz hH]

/-- The conditional law given the complete detailed retained graph is the symmetric hidden-subset
likelihood; ancillary assignment coordinates are retained in the marginal.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_symmetric_hidden_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H =
      (retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H})⁻¹ •
        (((graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
          (volume.withDensity (fun y => ENNReal.ofReal
            (symmetricHiddenWalshDensity n B d hfit h hz y))).map
              (fun y => (hz.1, hz.2, y)))).restrict {x | x.1 = H}).map Prod.snd := by
  rw [conditionalBlockLaw,
    reducedBlockLaw_symmetric_hidden_walsh_representation n B d h q hn hB hd hfit hh hq]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
