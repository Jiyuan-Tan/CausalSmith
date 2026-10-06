module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureHellinger
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SignComponents

/-! # Conditional label tensorization on the original record components

Finite sums over labels implement the conditional experiment at fixed original
covariates. Regrouping record labels into ownership fibers preserves Hellinger
distance; affinity tensorization then bounds it by the sum over components.
The factors may themselves be finite sign mixtures, so independence is needed
only between components, never between records in one component.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Normalized finite label masses have Hellinger discrepancy equal to twice
their affinity defect. [the documented result](goal) Under [the stated assumptions](hyp:f,g,hf0,hg0,hf1,hg1). -/
-- @node: mixture_label_hellinger_affinity
lemma mixture_label_hellinger_affinity {L : Type*} [Fintype L]
    (f g : L → ℝ) (hf0 : ∀ l, 0 ≤ f l) (hg0 : ∀ l, 0 ≤ g l)
    (hf1 : ∑ l, f l = 1) (hg1 : ∑ l, g l = 1) :
    (∑ l, (Real.sqrt (f l) - Real.sqrt (g l)) ^ 2) =
      2 * (1 - ∑ l, Real.sqrt (f l * g l)) := by
  have hp (l : L) : (Real.sqrt (f l) - Real.sqrt (g l)) ^ 2 =
      f l + g l - 2 * Real.sqrt (f l * g l) := by
    rw [Real.sqrt_mul (hf0 l)]
    nlinarith [Real.sq_sqrt (hf0 l), Real.sq_sqrt (hg0 l)]
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hf1, hg1]
  ring

/-- [The affinity of normalized nonnegative finite label masses lies in [0,1].](goal) Under [the stated assumptions](hyp:f,g,hf0,hg0,hf1,hg1). -/
-- @node: mixture_label_affinity_bounds
lemma mixture_label_affinity_bounds {L : Type*} [Fintype L]
    (f g : L → ℝ) (hf0 : ∀ l, 0 ≤ f l) (hg0 : ∀ l, 0 ≤ g l)
    (hf1 : ∑ l, f l = 1) (hg1 : ∑ l, g l = 1) :
    0 ≤ ∑ l, Real.sqrt (f l * g l) ∧ ∑ l, Real.sqrt (f l * g l) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _), ?_⟩
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun l (_ : l ∈ Finset.univ) => sq_nonneg (Real.sqrt (f l) - Real.sqrt (g l)))
  rw [mixture_label_hellinger_affinity f g hf0 hg0 hf1 hg1] at h
  linarith

/-- The conditional Hellinger discrepancy of finite independent label blocks is bounded by their summed discrepancies, by exact affinity factorization. the documented result Under the stated assumptions. [The stated hypotheses](hyp:f,g,hf0,hg0,hf1,hg1) hold, and [the stated conclusion follows](goal). -/
-- @node: mixture_label_tensor_le_sum
lemma mixture_label_tensor_le_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    {L : κ → Type*} [∀ c, Fintype (L c)]
    (f g : ∀ c, L c → ℝ)
    (hf0 : ∀ c l, 0 ≤ f c l) (hg0 : ∀ c l, 0 ≤ g c l)
    (hf1 : ∀ c, ∑ l, f c l = 1) (hg1 : ∀ c, ∑ l, g c l = 1) :
    (∑ l : ∀ c, L c,
      (Real.sqrt (∏ c, f c (l c)) - Real.sqrt (∏ c, g c (l c))) ^ 2) ≤
      ∑ c, ∑ l, (Real.sqrt (f c l) - Real.sqrt (g c l)) ^ 2 := by
  have hF0 : ∀ l : ∀ c, L c, 0 ≤ ∏ c, f c (l c) :=
    fun l => Finset.prod_nonneg (fun c _ => hf0 c (l c))
  have hG0 : ∀ l : ∀ c, L c, 0 ≤ ∏ c, g c (l c) :=
    fun l => Finset.prod_nonneg (fun c _ => hg0 c (l c))
  have hF1 : (∑ l : ∀ c, L c, ∏ c, f c (l c)) = 1 := by
    rw [← Fintype.prod_sum]; simp [hf1]
  have hG1 : (∑ l : ∀ c, L c, ∏ c, g c (l c)) = 1 := by
    rw [← Fintype.prod_sum]; simp [hg1]
  have hAffinity : (∑ l : ∀ c, L c,
      Real.sqrt ((∏ c, f c (l c)) * ∏ c, g c (l c))) =
      ∏ c, ∑ l, Real.sqrt (f c l * g c l) := by
    simp_rw [← Finset.prod_mul_distrib,
      Real.sqrt_prod _ (fun c _ => mul_nonneg (hf0 c _) (hg0 c _))]
    exact (Fintype.prod_sum (fun c l => Real.sqrt (f c l * g c l))).symm
  rw [mixture_label_hellinger_affinity _ _ hF0 hG0 hF1 hG1, hAffinity]
  have hb := fun c => mixture_label_affinity_bounds (f c) (g c)
    (hf0 c) (hg0 c) (hf1 c) (hg1 c)
  calc
    _ ≤ 2 * ∑ c, (1 - ∑ l, Real.sqrt (f c l * g c l)) :=
      mul_le_mul_of_nonneg_left (Causalean.Stat.one_sub_prod_le_sum _
        (fun c => (hb c).1) (fun c => (hb c).2)) (by norm_num)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      exact (mixture_label_hellinger_affinity (f c) (g c)
        (hf0 c) (hg0 c) (hf1 c) (hg1 c)).symm

/-- Regrouping all original labels into record-component fibers loses no information and transports the tensorized bound back to the original sample. the documented result Under the stated assumptions. [The stated hypotheses](hyp:f,g,hf0,hg0,hf1,hg1) hold, and [the stated conclusion follows](goal). -/
-- @node: mixture_label_fiber_tensor_le_sum
lemma mixture_label_fiber_tensor_le_sum {ι κ L : Type*}
    [Fintype ι] [Fintype κ] [Fintype L] [DecidableEq ι] [DecidableEq κ]
    (block : ι → κ)
    (f g : ∀ c, ({i : ι // block i = c} → L) → ℝ)
    (hf0 : ∀ c l, 0 ≤ f c l) (hg0 : ∀ c l, 0 ≤ g c l)
    (hf1 : ∀ c, ∑ l, f c l = 1) (hg1 : ∀ c, ∑ l, g c l = 1) :
    (∑ l : ι → L,
      (Real.sqrt (∏ c, f c (fun i => l i.1)) -
        Real.sqrt (∏ c, g c (fun i => l i.1))) ^ 2) ≤
      ∑ c, ∑ l, (Real.sqrt (f c l) - Real.sqrt (g c l)) ^ 2 := by
  let e : (ι → L) ≃ (∀ c, {i : ι // block i = c} → L) :=
    Equiv.piCongrFiberwise (fun _ => Equiv.refl _)
  calc
    _ = ∑ l : ∀ c, {i : ι // block i = c} → L,
        (Real.sqrt (∏ c, f c (l c)) - Real.sqrt (∏ c, g c (l c))) ^ 2 :=
      e.sum_comp (fun l =>
        (Real.sqrt (∏ c, f c (l c)) - Real.sqrt (∏ c, g c (l c))) ^ 2)
    _ ≤ _ := mixture_label_tensor_le_sum (κ := κ)
      (L := fun c => {i : ι // block i = c} → L) f g hf0 hg0 hf1 hg1

/-- [Conditional four-cell masses at any fixed covariate form a normalized
finite label distribution. [the documented result](goal) -/
-- @node: observedLaw_label_mass_normalized
lemma observedLaw_label_mass_normalized (P : ObservedLaw) (x : Covariate) :
    ∑ l : Bool × Bool, P.cells l.1 l.2 x = 1 := by
  rw [Fintype.sum_prod_type]
  exact P.normalized_cells x

/-- Averaging conditional product label masses over finitely many latent signs preserves normalization, including empty record components. the documented result Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: mixture_component_label_mass_normalized
lemma mixture_component_label_mass_normalized {ι S : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]
    (laws : S → ι → ObservedLaw) (x : ι → Covariate) :
    (∑ l : ι → Bool × Bool, (Fintype.card S : ℝ)⁻¹ *
      ∑ σ : S, ∏ i, (laws σ i).cells (l i).1 (l i).2 (x i)) = 1 := by
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h (σ : S) : (∑ l : ι → Bool × Bool,
      ∏ i, (laws σ i).cells (l i).1 (l i).2 (x i)) = 1 := by
    rw [← Fintype.prod_sum (fun i (l : Bool × Bool) =>
      (laws σ i).cells l.1 l.2 (x i))]
    simp_rw [observedLaw_label_mass_normalized]
    simp
  simp_rw [h]
  simp [Fintype.card_ne_zero]

/-- [Every conditional component mixture is nonnegative as a finite average of
products of the actual interior four-cell probabilities. [the documented result](goal) Under [the stated assumptions](hyp:x,l). -/
-- @node: mixture_component_label_mass_nonneg
lemma mixture_component_label_mass_nonneg {ι S : Type*}
    [Fintype ι] [Fintype S]
    (laws : S → ι → ObservedLaw) (x : ι → Covariate) (l : ι → Bool × Bool) :
    0 ≤ (Fintype.card S : ℝ)⁻¹ *
      ∑ σ : S, ∏ i, (laws σ i).cells (l i).1 (l i).2 (x i) := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg
    (fun i _ => (laws σ i).interior_cells _ _ _ |>.1.le))

/-- [The actual conditional label mass in one record block, averaged over its
owned endpoint signs. Labels outside that block are absent from the argument. -/
-- @node: conditionalComponentLabelMass
def conditionalComponentLabelMass {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [Fintype κ] [DecidableEq ι] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ)
    (laws : (ν → Bool) → ObservedLaw) (x : ι → Covariate)
    (c : κ) (l : {i : ι // block i = c} → Bool × Bool) : ℝ :=
  (Fintype.card ({s : ν // owner s = c} → Bool) : ℝ)⁻¹ *
    ∑ σ : {s : ν // owner s = c} → Bool,
      ∏ i : {i : ι // block i = c},
        (laws (componentSignExtension owner c σ)).cells (l i).1 (l i).2 (x i.1)

/-- Conditional component masses normalize even when their block is empty. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: conditionalComponentLabelMass_normalized
lemma conditionalComponentLabelMass_normalized {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [Fintype κ] [DecidableEq ι] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ)
    (laws : (ν → Bool) → ObservedLaw) (x : ι → Covariate) (c : κ) :
    ∑ l, conditionalComponentLabelMass owner block laws x c l = 1 := by
  exact mixture_component_label_mass_normalized
    (ι := {i : ι // block i = c}) (S := {s : ν // owner s = c} → Bool)
    (fun σ _ => laws (componentSignExtension owner c σ)) (fun i => x i.1)

/-- [Conditional component masses inherit nonnegativity from the actual laws.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:l). -/
-- @node: conditionalComponentLabelMass_nonneg
lemma conditionalComponentLabelMass_nonneg {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [Fintype κ] [DecidableEq ι] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ)
    (laws : (ν → Bool) → ObservedLaw) (x : ι → Covariate)
    (c : κ) (l : {i : ι // block i = c} → Bool × Bool) :
    0 ≤ conditionalComponentLabelMass owner block laws x c l := by
  exact mixture_component_label_mass_nonneg
    (ι := {i : ι // block i = c}) (S := {s : ν // owner s = c} → Bool)
    (fun σ _ => laws (componentSignExtension owner c σ)) (fun i => x i.1) l

/-- [Local dependence on owned signs factors the actual conditional label mass
on the full original record array into masses on disjoint record blocks. [the documented result](goal) Under [the stated assumptions](hyp:x,hlocal,l). -/
-- @node: conditional_label_mass_factorization
lemma conditional_label_mass_factorization {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [Fintype κ] [DecidableEq ι] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ)
    (laws : (ν → Bool) → ObservedLaw) (x : ι → Covariate)
    (hlocal : ∀ i σ τ, (∀ s, owner s = block i → σ s = τ s) →
      ∀ a y, (laws σ).cells a y (x i) = (laws τ).cells a y (x i))
    (l : ι → Bool × Bool) :
    (Fintype.card (ν → Bool) : ℝ)⁻¹ *
      (∑ σ : ν → Bool, ∏ i, (laws σ).cells (l i).1 (l i).2 (x i)) =
      ∏ c, conditionalComponentLabelMass owner block laws x c (fun i => l i.1) := by
  rw [signPrior_likelihood_factorization owner block
    (fun i σ => (laws σ).cells (l i).1 (l i).2 (x i))
    (fun i σ τ h => hlocal i σ τ h _ _)]
  unfold conditionalComponentLabelMass
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact Finset.prod_subtype _ (fun i => by simp)
    (fun i => (laws (componentSignExtension owner c σ)).cells (l i).1 (l i).2 (x i))

/-- At fixed original covariates the full finite-prior label Hellinger discrepancy is at most the sum over sign components. The proof uses the actual local-sign factorization and normalized component laws, without revealing signs or imposing independence between records inside a component. the documented result Under the stated assumptions. [The stated hypotheses](hyp:hlocal₀,hlocal₁) hold, and [the stated conclusion follows](goal). -/
-- @node: original_conditional_label_hellinger_le_components
lemma original_conditional_label_hellinger_le_components {ι ν κ : Type*}
    [Fintype ι] [Fintype ν] [Fintype κ] [DecidableEq ι] [DecidableEq ν] [DecidableEq κ]
    (owner : ν → κ) (block : ι → κ)
    (laws₀ laws₁ : (ν → Bool) → ObservedLaw) (x : ι → Covariate)
    (hlocal₀ : ∀ i σ τ, (∀ s, owner s = block i → σ s = τ s) →
      ∀ a y, (laws₀ σ).cells a y (x i) = (laws₀ τ).cells a y (x i))
    (hlocal₁ : ∀ i σ τ, (∀ s, owner s = block i → σ s = τ s) →
      ∀ a y, (laws₁ σ).cells a y (x i) = (laws₁ τ).cells a y (x i)) :
    (∑ l : ι → Bool × Bool,
      (Real.sqrt ((Fintype.card (ν → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i, (laws₀ σ).cells (l i).1 (l i).2 (x i)) -
       Real.sqrt ((Fintype.card (ν → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i, (laws₁ σ).cells (l i).1 (l i).2 (x i))) ^ 2) ≤
      ∑ c, ∑ l,
        (Real.sqrt (conditionalComponentLabelMass owner block laws₀ x c l) -
         Real.sqrt (conditionalComponentLabelMass owner block laws₁ x c l)) ^ 2 := by
  simp_rw [conditional_label_mass_factorization owner block laws₀ x hlocal₀,
    conditional_label_mass_factorization owner block laws₁ x hlocal₁]
  exact mixture_label_fiber_tensor_le_sum (ι := ι) (κ := κ) (L := Bool × Bool) block
    (conditionalComponentLabelMass owner block laws₀ x)
    (conditionalComponentLabelMass owner block laws₁ x)
    (conditionalComponentLabelMass_nonneg owner block laws₀ x)
    (conditionalComponentLabelMass_nonneg owner block laws₁ x)
    (conditionalComponentLabelMass_normalized owner block laws₀ x)
    (conditionalComponentLabelMass_normalized owner block laws₁ x)

end CausalSmith.Stat.LogoddsLowsmoothFrontier
