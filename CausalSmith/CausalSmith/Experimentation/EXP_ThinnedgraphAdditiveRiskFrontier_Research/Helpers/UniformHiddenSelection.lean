module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenSelectionAveraging
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Uniform hidden-subset averaging

Average selected hidden slots over original-label permutations, keeping the
capacity-constrained posterior rather than independent row allocations.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Averaging a finite transitive group orbit gives the uniform average on its target.  [For the stated data and conditions](hyp:G,X,a,f), [the stated conclusion holds](goal). -/
-- @node: finite_transitive_orbit_average
lemma finite_transitive_orbit_average {G X : Type*} [Group G] [Fintype G]
    [Fintype X] [MulAction G X] [MulAction.IsPretransitive G X]
    (a : X) (f : X → ℝ) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (g • a) =
      (Fintype.card X : ℝ)⁻¹ * ∑ x : X, f x := by
  classical
  letI : Nonempty X := ⟨a⟩
  have hcG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have heq (x : X) : (∑ g : G, f (g • x)) = ∑ g : G, f (g • a) := by
    obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G a x
    rw [show (∑ g : G, f (g • b • a)) = ∑ g : G, f ((Equiv.mulRight b g) • a) by
      apply Finset.sum_congr rfl; intro g _; exact congrArg f (mul_smul g b a).symm]
    exact Equiv.sum_comp (Equiv.mulRight b) (fun g : G => f (g • a))
  have hs : (Fintype.card X : ℝ) * (∑ g : G, f (g • a)) =
      (Fintype.card G : ℝ) * (∑ x : X, f x) := by
    calc
      _ = ∑ x : X, ∑ g : G, f (g • x) := by simp_rw [heq]; simp
      _ = ∑ g : G, ∑ x : X, f (g • x) := Finset.sum_comm
      _ = ∑ g : G, ∑ x : X, f x := by
        apply Finset.sum_congr rfl
        intro g _
        exact Equiv.sum_comp (MulAction.toPerm g) f
      _ = _ := by simp
  field_simp
  nlinarith [hs]

/-- A selected set transported by a uniform label permutation is a uniform subset
of its original cardinality, including the empty-set endpoint.  [For the stated data and conditions](hyp:ι,E,x), [the stated conclusion holds](goal). -/
-- @node: permutation_monomial_average
lemma permutation_monomial_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Finset ι) (x : ι → ℝ) :
    (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
      (∑ e : Equiv.Perm ι, ∏ j ∈ E, x (e j)) =
    (Fintype.card ι |>.choose E.card : ℝ)⁻¹ *
      ∑ F ∈ Finset.univ.powersetCard E.card, ∏ j ∈ F, x j := by
  classical
  letI : MulAction.IsPretransitive (Equiv.Perm ι) (Set.powersetCard ι E.card) :=
    Set.powersetCard.isPretransitive
  have h := finite_transitive_orbit_average (G := Equiv.Perm ι)
    (⟨E, rfl⟩ : Set.powersetCard ι E.card) (fun F => ∏ j ∈ F.val, x j)
  have hm (e : Equiv.Perm ι) :
      (∏ j ∈ ((e • (⟨E, rfl⟩ : Set.powersetCard ι E.card)).val), x j) =
        ∏ j ∈ E, x (e j) := by
    rw [Set.powersetCard.coe_smul, Finset.smul_finset_def]
    exact Finset.prod_image (fun i _ j _ hij => e.injective hij)
  simp_rw [hm] at h
  have hc : Fintype.card (Set.powersetCard ι E.card) = (Fintype.card ι).choose E.card := by
    simpa only [Nat.card_eq_fintype_card] using (Set.powersetCard.card (α := ι) (n := E.card))
  rw [hc] at h
  convert h using 1
  congr 1
  exact Finset.sum_subtype (Finset.univ.powersetCard E.card)
    (fun F => by simp [Set.powersetCard, Finset.mem_powersetCard]) (fun F => ∏ j ∈ F, x j)

/-- Uniformly permuting the labels of a fixed row allocation averages every
selected slot family to the uniform subset with the same total degree.  [For the stated data and conditions](hyp:ι,B,g,k,x), [the stated conclusion holds](goal). -/
-- @node: fixed_word_selection_permutation_average
lemma fixed_word_selection_permutation_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (g : ι → Fin B) (k : Fin B → ℕ) (x : ι → ℝ) :
    (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
      (∑ e : Equiv.Perm ι, ∏ ℓ, ∑ E ∈
        (Finset.univ.filter (fun j => g j = ℓ)).powersetCard (k ℓ), ∏ j ∈ E, x (e j)) =
    (∏ ℓ, ((Finset.univ.filter (fun j => g j = ℓ)).card.choose (k ℓ) : ℝ)) *
      ((Fintype.card ι |>.choose (∑ ℓ, k ℓ) : ℝ)⁻¹ *
        ∑ E ∈ Finset.univ.powersetCard (∑ ℓ, k ℓ), ∏ j ∈ E, x j) := by
  classical
  let t (ℓ : Fin B) := (Finset.univ.filter (fun j => g j = ℓ)).powersetCard (k ℓ)
  have hmono (E : Fin B → Finset ι) (hE : E ∈ Fintype.piFinset t) :
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
        (∑ e : Equiv.Perm ι, ∏ ℓ, ∏ j ∈ E ℓ, x (e j)) =
      (Fintype.card ι |>.choose (∑ ℓ, k ℓ) : ℝ)⁻¹ *
        ∑ F ∈ Finset.univ.powersetCard (∑ ℓ, k ℓ), ∏ j ∈ F, x j := by
    have hsub (ℓ : Fin B) : E ℓ ⊆ Finset.univ.filter (fun j => g j = ℓ) :=
      (Finset.mem_powersetCard.mp ((Fintype.mem_piFinset.mp hE) ℓ)).1
    have hcard (ℓ : Fin B) : (E ℓ).card = k ℓ :=
      (Finset.mem_powersetCard.mp ((Fintype.mem_piFinset.mp hE) ℓ)).2
    have hdis : (↑(Finset.univ : Finset (Fin B)) : Set (Fin B)).PairwiseDisjoint E := by
      intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intro j hja hjb
      exact hab ((Finset.mem_filter.mp (hsub a hja)).2.symm.trans
        (Finset.mem_filter.mp (hsub b hjb)).2)
    have htotal : (Finset.univ.biUnion E).card = ∑ ℓ, k ℓ := by
      rw [Finset.card_biUnion hdis]
      simp_rw [hcard]
    simp_rw [← Finset.prod_biUnion hdis]
    simpa only [htotal] using permutation_monomial_average (Finset.univ.biUnion E) x
  simp_rw [Finset.prod_univ_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ E ∈ Fintype.piFinset t,
        (Fintype.card ι |>.choose (∑ ℓ, k ℓ) : ℝ)⁻¹ *
          ∑ F ∈ Finset.univ.powersetCard (∑ ℓ, k ℓ), ∏ j ∈ F, x j := by
      exact Finset.sum_congr rfl hmono
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset]
      simp only [t, Finset.card_powersetCard, Nat.cast_prod]

/-- The exact capacity-constrained posterior selection moment is the binomial
slot multiplicity times the uniform subset average on the original hidden labels.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s₀,x,k), [the stated conclusion holds](goal). -/
-- @node: hiddenWordSelectionAverage_eq_uniform_subset
lemma hiddenWordSelectionAverage_eq_uniform_subset (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (H : OffDiag (Fin n) → Bool)
    (s₀ : CompatiblePartition n B d H) (x : HiddenSource n B d H → ℝ)
    (k : Fin B → ℕ) :
    hiddenWordSelectionAverage n B d H x k =
      (∏ ℓ, (Nat.choose (capacity n B d H ℓ) (k ℓ) : ℝ)) *
        ((Fintype.card (HiddenSource n B d H) |>.choose (∑ ℓ, k ℓ) : ℝ)⁻¹ *
          ∑ E ∈ Finset.univ.powersetCard (∑ ℓ, k ℓ), ∏ j ∈ E, x j) := by
  classical
  letI : Nonempty (HiddenCompletion n B d H) :=
    ⟨compatiblePartitionEquivHiddenCompletion n B d hfit H s₀ s₀⟩
  have hc : (Fintype.card (HiddenCompletion n B d H) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card (Equiv.Perm (HiddenSource n B d H)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card (Equiv.Perm (HiddenSource n B d H)) : ℝ)⁻¹ *
        ∑ e : Equiv.Perm (HiddenSource n B d H),
          hiddenWordSelectionAverage n B d H (fun j => x (e j)) k := by
      simp_rw [hiddenWordSelectionAverage_relabel]
      simp [he]
    _ = (Fintype.card (HiddenCompletion n B d H) : ℝ)⁻¹ *
        ∑ g : HiddenCompletion n B d H,
          ((Fintype.card (Equiv.Perm (HiddenSource n B d H)) : ℝ)⁻¹ *
            ∑ e : Equiv.Perm (HiddenSource n B d H),
              ∏ ℓ, ∑ E ∈ (Finset.univ.filter (fun j => g.1 j = ℓ)).powersetCard (k ℓ),
                ∏ j ∈ E, x (e j)) := by
      unfold hiddenWordSelectionAverage
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by
      simp_rw [fixed_word_selection_permutation_average]
      have hg (g : HiddenCompletion n B d H) :
          (∏ ℓ, ((Finset.univ.filter (fun j => g.1 j = ℓ)).card.choose (k ℓ) : ℝ)) =
            ∏ ℓ, (Nat.choose (capacity n B d H ℓ) (k ℓ) : ℝ) := by
        simp_rw [g.2]
      simp_rw [hg]
      simp [hc]

/-- Enumerate the original hidden source labels by their exact total capacity. -/
-- @node: hiddenSourceEnumeration
def hiddenSourceEnumeration (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s₀ : CompatiblePartition n B d H) :
    HiddenSource n B d H ≃ Fin (undiscovered n B d H) :=
  (Fintype.equivFin _).trans (finCongr (hiddenSource_card n B d hfit H s₀))

/-- The actual posterior hidden moment equals the roadmap's symmetric sign
polynomial, with every hidden source sign read from its original assignment label.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s₀,z,k), [the stated conclusion holds](goal). -/
-- @node: hiddenWordSelectionAverage_eq_symmetricSignPoly
lemma hiddenWordSelectionAverage_eq_symmetricSignPoly (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (H : OffDiag (Fin n) → Bool)
    (s₀ : CompatiblePartition n B d H) (z : Assign (Fin n)) (k : Fin B → ℕ) :
    hiddenWordSelectionAverage n B d H
      (fun j => signOf (z (hiddenSourceLabelEmbedding n B d hfit H j))) k =
    (∏ ℓ, (Nat.choose (capacity n B d H ℓ) (k ℓ) : ℝ)) *
      symmetricSignPoly (undiscovered n B d H) (∑ ℓ, k ℓ)
        (fun i => z (hiddenSourceLabelEmbedding n B d hfit H
          ((hiddenSourceEnumeration n B d hfit H s₀).symm i))) := by
  rw [hiddenWordSelectionAverage_eq_uniform_subset n B d hfit H s₀,
    symmetricSignPoly, hiddenSource_card n B d hfit H s₀]
  congr 2
  let e := hiddenSourceEnumeration n B d hfit H s₀
  have hm : (Finset.univ : Finset (HiddenSource n B d H)).map e.toEmbedding =
      Finset.univ := by ext i; simp
  have he := powersetCard_monomial_sum_map e.toEmbedding Finset.univ (∑ ℓ, k ℓ)
    (fun i => signOf (z (hiddenSourceLabelEmbedding n B d hfit H (e.symm i))))
  rw [hm] at he
  simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using he.symm

/-- The full positive-reference likelihood after exact symmetric-polynomial
averaging of globally constrained hidden labels.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_symmetric_hidden_selection_expansion
lemma blockDensity_symmetric_hidden_selection_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) =
    ∑ J ∈ Fintype.piFinset (fun ℓ : Fin B => (revealedSources n B d H ℓ).powerset),
      (∏ ℓ, ∏ j ∈ J ℓ, signOf (z j)) *
      ∑ k ∈ Fintype.piFinset (fun ℓ : Fin B => Finset.range (capacity n B d H ℓ + 1)),
        (∏ ℓ, walshCoeff d h ((J ℓ).card + k ℓ) (y ℓ)) *
          ((∏ ℓ, (Nat.choose (capacity n B d H ℓ) (k ℓ) : ℝ)) *
            symmetricSignPoly (undiscovered n B d H) (∑ ℓ, k ℓ)
              (fun i => z (hiddenSourceLabelEmbedding n B d hfit H
                ((hiddenSourceEnumeration n B d hfit H s₀).symm i)))) := by
  have he := blockDensity_hidden_word_selection_expansion
    n B d hd hfit h H z s₀ y hy (Equiv.refl _)
  simp only [Equiv.refl_apply] at he
  simp_rw [hiddenWordSelectionAverage_eq_symmetricSignPoly n B d hfit H s₀] at he
  exact he

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
