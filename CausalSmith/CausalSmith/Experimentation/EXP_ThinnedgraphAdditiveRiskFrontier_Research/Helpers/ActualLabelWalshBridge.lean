module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.LabelSubsetConditionalLikelihood
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenSignEnergy
public import Mathlib.Probability.Independence.Basic

/-!
# Transport of the actual labeled likelihood to independent signs

The original assignment coordinates indexed by revealed and hidden source labels
have their exact product law. Ancillary coordinates are integrated out by a
measure-preserving projection, rather than replacing hidden row assignments.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- An injective selection of actual assignment labels retains independent fair signs.  [For the stated data and conditions](hyp:ι,κ,e), [the stated conclusion holds](goal). -/
-- @node: halfBernoulli_map_embedding
lemma halfBernoulli_map_embedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) :
    (halfBernoulli ι).map (fun z i => z (e i)) = halfBernoulli κ := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  have hi := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : ι => bernoulliLaw (1 / 2))
    (X := fun _ (b : Bool) => b) (fun _ => measurable_id.aemeasurable)
  have hs := hi.precomp e.injective
  unfold halfBernoulli
  rw [hs.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  simp only [Measure.pi_map_eval, measure_univ, Finset.prod_const_one, one_smul]

/-- Two disjoint injective label selections have the exact independent sign law.  [For the stated data and conditions](hyp:ι,R,M,r,u,hru), [the stated conclusion holds](goal). -/
-- @node: halfBernoulli_map_disjoint_embeddings
lemma halfBernoulli_map_disjoint_embeddings {ι : Type*} [Fintype ι]
    (R M : ℕ) (r : Fin R ↪ ι) (u : Fin M ↪ ι)
    (hru : ∀ i j, r i ≠ u j) :
    (halfBernoulli ι).map (fun z => (fun i => z (r i), fun j => z (u j))) =
      (halfBernoulli (Fin R)).prod (halfBernoulli (Fin M)) := by
  let e : Fin R ⊕ Fin M ↪ ι :=
    ⟨Sum.elim r u, by
      intro a b hab
      cases a with
      | inl a => cases b with
        | inl b => exact congrArg Sum.inl (r.injective hab)
        | inr b => exact False.elim (hru a b hab)
      | inr a => cases b with
        | inl b => exact False.elim (hru b a hab.symm)
        | inr b => exact congrArg Sum.inr (u.injective hab)⟩
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  have he := halfBernoulli_map_embedding e
  have hp := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin R ⊕ Fin M => bernoulliLaw (1 / 2))).map_eq
  change (halfBernoulli (Fin R ⊕ Fin M)).map
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => Bool)) =
      (halfBernoulli (Fin R)).prod (halfBernoulli (Fin M)) at hp
  rw [← he] at hp
  rw [Measure.map_map (by fun_prop) (measurable_of_finite _)] at hp
  exact hp

/-- Enumerate every actually revealed source label once. -/
-- @node: revealedLabelEmbedding
def revealedLabelEmbedding (n B d : ℕ) (H : OffDiag (Fin n) → Bool) :
    Fin (Finset.univ.biUnion (revealedSources n B d H)).card ↪ Fin n :=
  (Finset.equivFin (Finset.univ.biUnion (revealedSources n B d H))).symm.toEmbedding.trans
    (Function.Embedding.subtype _)

/-- The enumerated revealed labels and original hidden labels are disjoint.  [For the stated data and conditions](hyp:n,B,d,hfit,H,i,j), [the stated conclusion holds](goal). -/
-- @node: revealed_hidden_label_ne
lemma revealed_hidden_label_ne (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool)
    (i : Fin (Finset.univ.biUnion (revealedSources n B d H)).card)
    (j : HiddenSource n B d H) :
    revealedLabelEmbedding n B d H i ≠ hiddenSourceLabelEmbedding n B d hfit H j := by
  intro he
  have hi := ((Finset.equivFin (Finset.univ.biUnion (revealedSources n B d H))).symm i).2
  change revealedLabelEmbedding n B d H i ∈
    Finset.univ.biUnion (revealedSources n B d H) at hi
  rw [he] at hi
  obtain ⟨ℓ, _, hℓ⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨_, v, _, hne, hv⟩ := (Finset.mem_filter.mp hℓ).2
  have hn := (sourceReveals_false_iff n B d H
    (hiddenSourceLabelEmbedding n B d hfit H j) j.1.isLt).mp j.2
  exact hn ⟨v, hne, hv⟩

/-- The signs occurring in the actual posterior likelihood have the product law
used in the hidden/revealed energy identity. The full assignment is the source.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s), [the stated conclusion holds](goal). -/
-- @node: actualLabelSigns_map
lemma actualLabelSigns_map (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) :
    (halfBernoulli (Fin n)).map (fun z =>
      (fun i => z (revealedLabelEmbedding n B d H i),
       fun j => z (hiddenSourceLabelEmbedding n B d hfit H
         ((hiddenSourceEnumeration n B d hfit H s).symm j)))) =
      (halfBernoulli (Fin (Finset.univ.biUnion (revealedSources n B d H)).card)).prod
        (halfBernoulli (Fin (undiscovered n B d H))) := by
  exact halfBernoulli_map_disjoint_embeddings _ _
    (revealedLabelEmbedding n B d H)
    ((hiddenSourceEnumeration n B d hfit H s).symm.toEmbedding.trans
      (hiddenSourceLabelEmbedding n B d hfit H))
    (fun i j => revealed_hidden_label_ne n B d hfit H i _)

/-- Transport the nonconstant energy identity back to the original assignment,
including all unused recipient and padding coordinates.  [For the stated data and conditions](hyp:Ω,ν,n,R,M,r,u,hmap,G,c,hzero,hc0,hm,hc), [the stated conclusion holds](goal). -/
-- @node: actualLabel_response_nonconstant_energy
lemma actualLabel_response_nonconstant_energy {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (n R M : ℕ)
    (r : Fin R ↪ Fin n) (u : Fin M ↪ Fin n)
    (hmap : (halfBernoulli (Fin n)).map
      (fun z => (fun i => z (r i), fun j => z (u j))) =
        (halfBernoulli (Fin R)).prod (halfBernoulli (Fin M)))
    (G : Finset (Finset (Fin R) × Fin (M + 1)))
    (c : (Finset (Fin R) × Fin (M + 1)) → Ω → ℝ)
    (hzero : (∅, 0) ∈ G) (hc0 : ∀ y, c (∅, 0) y = 1)
    (hm : ∀ i, Measurable (c i))
    (hc : ∀ i ∈ G, ∀ j ∈ G, Integrable (fun y => c i y * c j y) ν) :
    (∫ p : Assign (Fin n) × Ω,
      ((∑ i ∈ G, ((∏ j ∈ i.1, signOf (p.1 (r j))) *
        symmetricSignPoly M i.2.val (fun j => p.1 (u j))) * c i p.2) - 1) ^ 2
      ∂(halfBernoulli (Fin n)).prod ν) =
      ∑ i ∈ G.erase (∅, 0), (∫ y, c i y ^ 2 ∂ν) / (M.choose i.2.val : ℝ) := by
  let F : ((Fin R → Bool) × (Fin M → Bool)) × Ω → ℝ := fun p =>
    ((∑ i ∈ G, ((∏ j ∈ i.1, signOf (p.1.1 j)) *
      symmetricSignPoly M i.2.val p.1.2) * c i p.2) - 1) ^ 2
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.sub _ measurable_const
    apply Finset.measurable_sum
    intro i hi
    exact ((measurable_of_finite (fun x : (Fin R → Bool) × (Fin M → Bool) =>
      (∏ j ∈ i.1, signOf (x.1 j)) * symmetricSignPoly M i.2.val x.2)).comp
      measurable_fst).mul ((hm i).comp measurable_snd)
  have hp : ((halfBernoulli (Fin n)).prod ν).map
      (fun p => ((fun i => p.1 (r i), fun j => p.1 (u j)), p.2)) =
      ((halfBernoulli (Fin R)).prod (halfBernoulli (Fin M))).prod ν := by
    have hprod := Measure.map_prod_map (halfBernoulli (Fin n)) ν
      (f := fun z => (fun i => z (r i), fun j => z (u j)))
      (g := id) (measurable_of_finite _) measurable_id
    simp only [Prod.map_def, id_eq] at hprod
    rw [← hprod, hmap, Measure.map_id]
  have he := integral_map (μ := (halfBernoulli (Fin n)).prod ν)
    (φ := fun p => ((fun i => p.1 (r i), fun j => p.1 (u j)), p.2))
    (by fun_prop) hF.aestronglyMeasurable
  rw [hp] at he
  exact he.symm.trans (hidden_revealed_response_nonconstant_energy ν R M G c hzero hc0 hc)

/-- The revealed enumeration covers exactly the observed union of row labels.  [For the stated data and conditions](hyp:n,B,d,H), [the stated conclusion holds](goal). -/
-- @node: revealedLabelEmbedding_univ_map
lemma revealedLabelEmbedding_univ_map (n B d : ℕ) (H : OffDiag (Fin n) → Bool) :
    Finset.univ.map (revealedLabelEmbedding n B d H) =
      Finset.univ.biUnion (revealedSources n B d H) := by
  ext j
  constructor
  · rintro hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact ((Finset.equivFin (Finset.univ.biUnion (revealedSources n B d H))).symm i).2
  · intro hj
    refine Finset.mem_map.mpr ⟨
      Finset.equivFin (Finset.univ.biUnion (revealedSources n B d H)) ⟨j, hj⟩,
      Finset.mem_univ _, ?_⟩
    simp [revealedLabelEmbedding]

/-- The exact zero-hidden-degree coefficient contains only the zero row vector.  [For the stated data and conditions](hyp:n,B,d,h,H,y), [the stated conclusion holds](goal). -/
-- @node: groupedHiddenWalshCoeff_empty_zero
lemma groupedHiddenWalshCoeff_empty_zero (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (y : Fin B → ℝ) :
    groupedHiddenWalshCoeff n B d h H (fun _ => ∅) 0 y =
      ∏ ℓ, walshCoeff d h 0 (y ℓ) := by
  rw [groupedHiddenWalshCoeff_eq_bounded]
  have hf : Finset.univ.filter
      (fun k : ∀ ℓ : Fin B, Fin (capacity n B d H ℓ + 1) =>
        0 = ∑ ℓ, (k ℓ).val) = {fun _ => 0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      funext ℓ
      apply Fin.ext
      exact (Finset.sum_eq_zero_iff.mp hk.symm) ℓ (Finset.mem_univ ℓ)
    · rintro rfl
      simp
  rw [hf]
  simp

/-- On positive reference support the actual constant posterior coefficient is one.  [For the stated data and conditions](hyp:n,B,d,h,H,y,hy), [the stated conclusion holds](goal). -/
-- @node: groupedHiddenWalshCoeff_empty_zero_pos
lemma groupedHiddenWalshCoeff_empty_zero_pos (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    groupedHiddenWalshCoeff n B d h H (fun _ => ∅) 0 y = 1 := by
  rw [groupedHiddenWalshCoeff_empty_zero]
  simp_rw [walshCoeff_zero d h _ (hy _)]
  simp

/-- Actual response coefficients indexed by enumerated revealed subsets and
total hidden degree. The coefficients themselves keep all row capacities. -/
-- @node: actualLabelWalshCoeff
def actualLabelWalshCoeff (n B d : ℕ) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (i : Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
      Fin (undiscovered n B d H + 1)) (y : Fin B → ℝ) : ℝ :=
  groupedHiddenWalshCoeff n B d h H
    (fun ℓ => (i.1.map (revealedLabelEmbedding n B d H)) ∩ revealedSources n B d H ℓ)
    i.2.val y

/-- Injective label maps carry the full subset family to the image subset family.  [For the stated data and conditions](hyp:α,β,S,e), [the stated conclusion holds](goal). -/
-- @node: labeled_powerset_map
lemma labeled_powerset_map {α β : Type*}
    (S : Finset α) (e : α ↪ β) :
    (S.map e).powerset = S.powerset.map (Finset.mapEmbedding e).toEmbedding := by
  classical
  simp only [Finset.map_eq_image, RelEmbedding.coe_toEmbedding]
  rw [Finset.powerset_image]
  congr 1
  funext E
  exact (Finset.map_eq_image e E).symm

/-- The original-label likelihood is exactly the finite expansion indexed by
the independent sign projection, wherever the reference density is positive.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,s,z,y,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_actualLabel_walsh_expansion
lemma blockDensity_actualLabel_walsh_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (s : CompatiblePartition n B d H) (z : Assign (Fin n)) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) =
      ∑ i : Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
          Fin (undiscovered n B d H + 1),
        ((∏ j ∈ i.1, signOf (z (revealedLabelEmbedding n B d H j))) *
          symmetricSignPoly (undiscovered n B d H) i.2.val
            (fun j => z (hiddenSourceLabelEmbedding n B d hfit H
              ((hiddenSourceEnumeration n B d hfit H s).symm j)))) *
          actualLabelWalshCoeff n B d h H i y := by
  rw [blockDensity_grouped_hidden_walsh_expansion n B d hd hfit h H z s y hy,
    groupedHiddenWalsh_sum_labelSubsets n B d h H s]
  conv_lhs =>
    rw [← revealedLabelEmbedding_univ_map n B d H, labeled_powerset_map, Finset.sum_map]
  rw [Fintype.sum_prod_type]
  simp only [Finset.powerset_univ, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.prod_map, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  dsimp [actualLabelWalshCoeff]
  ring

/-- At each positive reference response the actual assignment norm of the
centered likelihood is exactly its nonconstant coefficient energy.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,s,y,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_actualLabel_nonconstant_energy
lemma blockDensity_actualLabel_nonconstant_energy (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (s : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    (∫ z : Assign (Fin n),
      (blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) - 1) ^ 2
      ∂halfBernoulli (Fin n)) =
      ∑ i ∈ (Finset.univ : Finset
        (Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
          Fin (undiscovered n B d H + 1))).erase (∅, 0),
        actualLabelWalshCoeff n B d h H i y ^ 2 /
          (Nat.choose (undiscovered n B d H) i.2.val : ℝ) := by
  let r := revealedLabelEmbedding n B d H
  let u := (hiddenSourceEnumeration n B d hfit H s).symm.toEmbedding.trans
    (hiddenSourceLabelEmbedding n B d hfit H)
  have hc0 : actualLabelWalshCoeff n B d h H (∅, 0) y = 1 := by
    simpa [actualLabelWalshCoeff] using
      groupedHiddenWalshCoeff_empty_zero_pos n B d h H y hy
  have he := actualLabel_response_nonconstant_energy (Measure.dirac ()) n
    (Finset.univ.biUnion (revealedSources n B d H)).card (undiscovered n B d H)
    r u (actualLabelSigns_map n B d hfit H s) Finset.univ
    (fun i (_ : Unit) => actualLabelWalshCoeff n B d h H i y)
    (Finset.mem_univ _) (fun _ => hc0) (fun _ => measurable_const)
    (fun _ _ _ _ => integrable_const _)
  rw [integral_prod _ (by
    let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
      bernoulliLaw_probability _ (by constructor <;> norm_num)
    let : IsProbabilityMeasure (halfBernoulli (Fin n)) := by
      unfold halfBernoulli; infer_instance
    exact Integrable.of_finite)] at he
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at he
  simp_rw [blockDensity_actualLabel_walsh_expansion n B d hd hfit h H s _ y hy]
  exact he

/-- The independent reference responses almost surely lie in positive row support.  [For the stated data and conditions](hyp:B,d,h), [the stated conclusion holds](goal). -/
-- @node: referenceRows_positive_ae
lemma referenceRows_positive_ae (B d : ℕ) (h : ℝ) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin B => volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w))),
      ∀ ℓ, 0 < refDensity d h (y ℓ) := by
  let ν := volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))
  let := referenceRowLaw_probability d h
  have hw : ∀ᵐ w ∂ν, 0 < refDensity d h w := by
    rw [ae_withDensity_iff (by fun_prop)]
    filter_upwards [] with w hw
    exact lt_of_le_of_ne (refDensity_nonneg d h w)
      (by intro hz; apply hw; rw [← hz]; simp)
  apply ae_all_iff.mpr
  intro ℓ
  have he : ∀ᵐ w ∂(Measure.pi (fun _ : Fin B => ν)).map
      (fun y : Fin B → ℝ => y ℓ), 0 < refDensity d h w := by
    rw [(measurePreserving_eval (fun _ : Fin B => ν) ℓ).map_eq]
    exact hw
  exact ae_of_ae_map (f := fun y : Fin B → ℝ => y ℓ)
    (p := fun w => 0 < refDensity d h w) (measurable_pi_apply ℓ).aemeasurable he

/-- Exact posterior coefficient cross products are integrable under the actual
row reference; no new regularity premise is needed.  [For the stated data and conditions](hyp:n,B,d,h,H,i,j), [the stated conclusion holds](goal). -/
-- @node: actualLabelWalshCoeff_cross_integrable
lemma actualLabelWalshCoeff_cross_integrable (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool)
    (i j : Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
      Fin (undiscovered n B d H + 1)) :
    Integrable (fun y => actualLabelWalshCoeff n B d h H i y *
      actualLabelWalshCoeff n B d h H j y)
      (Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) := by
  simp_rw [actualLabelWalshCoeff, groupedHiddenWalshCoeff_eq_bounded]
  exact hidden_support_sum_cross_integrable B d h _ _ _ _ _ _

/-- Integrating the actual original-label likelihood norm over the reference
responses gives precisely the nonconstant coefficient norms used in contraction.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,s), [the stated conclusion holds](goal). -/
-- @node: blockDensity_actualLabel_integrated_nonconstant_energy
lemma blockDensity_actualLabel_integrated_nonconstant_energy
    (n B d : ℕ) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) :
    (∫ y : Fin B → ℝ,
      (∫ z : Assign (Fin n),
        (blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) - 1) ^ 2
        ∂halfBernoulli (Fin n))
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) =
      ∑ i ∈ (Finset.univ : Finset
        (Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
          Fin (undiscovered n B d H + 1))).erase (∅, 0),
        (∫ y : Fin B → ℝ, actualLabelWalshCoeff n B d h H i y ^ 2
          ∂Measure.pi (fun _ : Fin B => volume.withDensity
            (fun w => ENNReal.ofReal (refDensity d h w)))) /
          (Nat.choose (undiscovered n B d H) i.2.val : ℝ) := by
  calc
    _ = ∫ y : Fin B → ℝ,
        ∑ i ∈ (Finset.univ : Finset
          (Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
            Fin (undiscovered n B d H + 1))).erase (∅, 0),
          actualLabelWalshCoeff n B d h H i y ^ 2 /
            (Nat.choose (undiscovered n B d H) i.2.val : ℝ)
        ∂Measure.pi (fun _ : Fin B => volume.withDensity
          (fun w => ENNReal.ofReal (refDensity d h w))) := by
      apply integral_congr_ae
      filter_upwards [referenceRows_positive_ae B d h] with y hy
      exact blockDensity_actualLabel_nonconstant_energy n B d hd hfit h H s y hy
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => ?_)]
      · apply Finset.sum_congr rfl
        intro i hi
        exact integral_div _ _
      · simp only [pow_two]
        exact (actualLabelWalshCoeff_cross_integrable n B d h H i i).div_const _

/-- Original-assignment energy of the posterior density ratio under the response reference. -/
-- @node: actualDensityEnergy
def actualDensityEnergy (n B d : ℕ) (h : ℝ) (H : OffDiag (Fin n) → Bool) : ℝ :=
  ∫ y : Fin B → ℝ, (∫ z : Assign (Fin n),
    (blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) - 1) ^ 2
    ∂halfBernoulli (Fin n))
    ∂Measure.pi (fun _ : Fin B => volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w)))

/-- Exact nonconstant posterior coefficient energy, retaining every hidden-degree weight. -/
-- @node: actualLabelEnergy
def actualLabelEnergy (n B d : ℕ) (h : ℝ) (H : OffDiag (Fin n) → Bool) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset
    (Finset (Fin (Finset.univ.biUnion (revealedSources n B d H)).card) ×
      Fin (undiscovered n B d H + 1))).erase (∅, 0),
    (∫ y : Fin B → ℝ, actualLabelWalshCoeff n B d h H i y ^ 2
      ∂Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w)))) /
      (Nat.choose (undiscovered n B d H) i.2.val : ℝ)

/-- The actual density energy is exactly the label coefficient energy on every
compatible detailed graph. This is the bridge consumed by contraction.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,s), [the stated conclusion holds](goal). -/
-- @node: actualDensityEnergy_eq_actualLabelEnergy
lemma actualDensityEnergy_eq_actualLabelEnergy (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (s : CompatiblePartition n B d H) :
    actualDensityEnergy n B d h H = actualLabelEnergy n B d h H :=
  blockDensity_actualLabel_integrated_nonconstant_energy n B d hd hfit h H s

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
