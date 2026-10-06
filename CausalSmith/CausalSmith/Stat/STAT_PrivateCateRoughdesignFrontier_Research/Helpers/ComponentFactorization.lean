module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentPartition
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.SignBlockFactorization
/-! Pointwise products over the ordered shared-sign partition: fixed-sign conditional
likelihoods and fair null masses factor at every covariate vector. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.PrivateCateRoughdesign
variable (hL : ℝ) (n : ℕ)

/-- The finite union of the ordered components is the whole dataset index set.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: orderedComponents_biUnion
lemma orderedComponents_biUnion (x : Fin n → Covariate) :
    (orderedComponents hL n x).toFinset.biUnion id = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_biUnion, List.mem_toFinset, id_eq, Finset.mem_univ, iff_true]
  exact orderedComponents_cover hL n x i

/-- The finset underlying the component order is a disjoint partition.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: orderedComponents_pairwiseDisjoint
lemma orderedComponents_pairwiseDisjoint (x : Fin n → Covariate) :
    Set.PairwiseDisjoint ((orderedComponents hL n x).toFinset : Set (Finset (Fin n))) id := by
  classical
  intro C hC D hD hne
  exact orderedComponents_disjoint hL n x C D
    (List.mem_toFinset.mp hC) (List.mem_toFinset.mp hD) hne

/-- Multiplying vertex factors component by component equals the full dataset product.  [the theorem's stated inputs and assumptions](hyp:x,f), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:α). -/
-- @node: orderedComponents_prod
lemma orderedComponents_prod {α : Type*} [CommMonoid α]
    (x : Fin n → Covariate) (f : Fin n → α) :
    ((orderedComponents hL n x).map (fun C : Finset (Fin n) => ∏ i : C, f i)).prod = ∏ i, f i := by
  classical
  simp_rw [Finset.prod_coe_sort]
  rw [← List.prod_toFinset _ (orderedComponents_nodup hL n x)]
  have hp := Finset.prod_biUnion (f := f) (orderedComponents_pairwiseDisjoint hL n x)
  rw [orderedComponents_biUnion] at hp
  simpa only [id_eq] using hp.symm

/-- Component cardinalities sum to the number of dataset records.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: orderedComponents_card_sum
lemma orderedComponents_card_sum (x : Fin n → Covariate) :
    ((orderedComponents hL n x).map Finset.card).sum = n := by
  classical
  have hs := Finset.sum_biUnion (f := fun _ : Fin n => (1 : ℕ))
    (orderedComponents_pairwiseDisjoint hL n x)
  rw [orderedComponents_biUnion] at hs
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, id_eq, List.sum_toFinset _ (orderedComponents_nodup hL n x)] using hs.symm

/-- Conditional independence given signs factors its mark likelihood over the graph partition.  [the theorem's stated inputs and assumptions](hyp:z,lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: fixedSign_component_factorization
lemma fixedSign_component_factorization (x : Fin n → Covariate)
    (z : Fin n → Bool × Bool) (lam : SignVector hL) :
    (∏ i : Fin n, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4) =
      ((orderedComponents hL n x).map (fun C : Finset (Fin n) =>
        ∏ i : C, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4)).prod := by
  exact (orderedComponents_prod hL n x _).symm

/-- A fair component mass is the product of the fair one-record masses.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:C,z). -/
-- @node: nullMass_eq_vertex_prod
lemma nullMass_eq_vertex_prod (C : Finset (Fin n)) (z : Marks C) :
    nullMass n C z = ∏ _i : C, (1 / 4 : ℝ) := by
  simp [nullMass, zpow_neg, zpow_natCast, one_div]

/-- The fair null factors over components at every covariate vector.  [the theorem's stated inputs and assumptions](hyp:z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: nullMass_component_factorization
lemma nullMass_component_factorization (x : Fin n → Covariate)
    (z : Fin n → Bool × Bool) :
    (4 : ℝ)^(-(n : ℤ)) =
      ((orderedComponents hL n x).map (fun C => nullMass n C (fun i => z i))).prod := by
  simp_rw [nullMass_eq_vertex_prod]
  rw [orderedComponents_prod hL n x (fun _ => (1 / 4 : ℝ))]
  simp [zpow_neg, zpow_natCast, one_div]

open Classical in
/-- A component uses precisely those active signs nonzero at one of its vertices. -/
-- @node: componentSignIndices
def componentSignIndices (x : Fin n → Covariate) (C : Finset (Fin n)) :
    Finset (activeSigns hL) :=
  Finset.univ.filter (fun j => ∃ i ∈ C, envelope hL (x i) * frame hL j (x i) ≠ 0)

/-- The sign block membership test is the existence of a vertex using that coordinate.  [the theorem's stated inputs and assumptions](hyp:j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x,C). -/
-- @node: mem_componentSignIndices
lemma mem_componentSignIndices (x : Fin n → Covariate) (C : Finset (Fin n))
    (j : activeSigns hL) :
    j ∈ componentSignIndices hL n x C ↔
      ∃ i ∈ C, envelope hL (x i) * frame hL j (x i) ≠ 0 := by
  classical
  simp [componentSignIndices]

/-- Distinct ordered graph components use disjoint coordinate blocks of the latent signs.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: orderedComponents_signIndices_pairwiseDisjoint
lemma orderedComponents_signIndices_pairwiseDisjoint (x : Fin n → Covariate) :
    Set.PairwiseDisjoint ((orderedComponents hL n x).toFinset : Set (Finset (Fin n)))
      (componentSignIndices hL n x) := by
  classical
  intro C hC D hD hne
  apply Finset.disjoint_left.mpr
  intro j hjC hjD
  obtain ⟨i, hi, hij⟩ := (mem_componentSignIndices hL n x C j).mp hjC
  obtain ⟨l, hl, hlj⟩ := (mem_componentSignIndices hL n x D j).mp hjD
  obtain ⟨r, hr, rfl⟩ := (mem_orderedComponents hL n x C).mp (List.mem_toFinset.mp hC)
  obtain ⟨s, hs, rfl⟩ := (mem_orderedComponents hL n x D).mp (List.mem_toFinset.mp hD)
  have hrs : ¬(sharedGraph hL n x).Reachable r s := by
    intro hrs
    exact hne (componentVertices_eq_of_reachable hL n x r s hrs)
  exact hlj (component_activeSigns_disjoint hL n x r s i l hrs hi hl j hij)

/-- A component mark product is a function only of its selected sign block.  [the theorem's stated inputs and assumptions](hyp:C,z,lam,lam',hagree), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: componentLikelihood_dependsOn_signIndices
lemma componentLikelihood_dependsOn_signIndices (x : Fin n → Covariate)
    (C : Finset (Fin n)) (z : Marks C) (lam lam' : SignVector hL)
    (hagree : ∀ j ∈ componentSignIndices hL n x C, lam j = lam' j) :
    (∏ i : C, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4) =
      ∏ i : C, conditionalLikelihood hL lam' (x i) (z i).1 (z i).2 / 4 := by
  apply componentLikelihood_eq_of_activeSigns_agree hL n x C z lam lam'
  intro i j hj
  exact hagree j ((mem_componentSignIndices hL n x C j).mpr ⟨i, i.property, hj⟩)

/-- Mixing independent signs preserves the product over distinct shared-sign components.
This identity holds pointwise in the covariates, including all support boundaries.  [the theorem's stated inputs and assumptions](hyp:z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:x). -/
-- @node: fullAlternativeMass_component_factorization
lemma fullAlternativeMass_component_factorization (x : Fin n → Covariate)
    (z : Fin n → Bool × Bool) :
    fullAlternativeMass hL n x z =
      ((orderedComponents hL n x).map (fun C =>
        alternativeMass hL n x C (fun i => z i))).prod := by
  classical
  let F : Finset (Fin n) → SignVector hL → ℝ := fun C lam =>
    ∏ i : C, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4
  have hfactor := fairSignAverage_disjointBlocks_prod
    (orderedComponents hL n x).toFinset (componentSignIndices hL n x) F
    (orderedComponents_signIndices_pairwiseDisjoint hL n x)
    (fun C _ lam lam' hagree =>
      componentLikelihood_dependsOn_signIndices hL n x C (fun i => z i) lam lam' hagree)
  have hweight : Fintype.card (activeSigns hL) = (activeSigns hL).card :=
    Fintype.card_coe _
  rw [hweight] at hfactor
  have hprod (lam : SignVector hL) :
      (∏ C ∈ (orderedComponents hL n x).toFinset, F C lam) =
        ∏ i : Fin n, conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4 := by
    rw [List.prod_toFinset (fun C => F C lam) (orderedComponents_nodup hL n x)]
    exact orderedComponents_prod hL n x
      (fun i => conditionalLikelihood hL lam (x i) (z i).1 (z i).2 / 4)
  simp_rw [hprod] at hfactor
  change fullAlternativeMass hL n x z =
    ∏ C ∈ (orderedComponents hL n x).toFinset, alternativeMass hL n x C (fun i => z i) at hfactor
  rw [List.prod_toFinset (fun C => alternativeMass hL n x C (fun i => z i))
    (orderedComponents_nodup hL n x)] at hfactor
  exact hfactor
end CausalSmith.Stat.PrivateCateRoughdesign
