module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ComponentPriorRestriction
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairComponentSupport
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairMixtureParity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairProductDerivatives
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureAxes
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureConditionalIntegration
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureDensities
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureHellinger
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureMassNormalization
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureLabelTensorization
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedComponentSupport
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedMixtureTaylor
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedProductDerivatives
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureCovariateOccupancy
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SignComponents
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_CalibratedSupport
public import Causalean.Stat.Minimax.HellingerAffinity

/-! # T OriginalRecordMixtures

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
@[expose] public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

attribute [local instance] Classical.propDecidable

/-- [Non-singleton occupancy weight of a sign block; the unused-sign block
has no records and contributes zero. -/
-- @node: signComponentWeight
def signComponentWeight {n : ℕ} (k : ℕ) (x : Fin n → Covariate) (B : ℝ)
    (c : SignComponentBlock k x) : ℝ :=
  match c with
  | none => 0
  | some v => if 2 ≤ v.supp.toFinset.card then
      (v.supp.toFinset.card : ℝ)^4 * B^v.supp.toFinset.card else 0

/-- The occupancy weight vanishes exactly on the empty and singleton record
fibers. Their Hellinger contribution must be canceled rather than bounded crudely. [the documented result](goal) Under [the stated assumptions](hyp:x,hcard). -/
-- @node: signComponentWeight_eq_zero_of_small
lemma signComponentWeight_eq_zero_of_small {n : ℕ} (k : ℕ)
    (x : Fin n → Covariate) (B : ℝ) (c : SignComponentBlock k x)
    (hcard : Fintype.card {i : Fin n //
      some ((originalRecordSignGraph k x).connectedComponentMk i) = c} ≤ 1) :
    signComponentWeight k x B c = 0 := by
  rw [signComponent_record_card] at hcard
  cases c with
  | none => rfl
  | some v =>
    dsimp only at hcard
    simp only [signComponentWeight, if_neg (by omega : ¬2 ≤ v.supp.toFinset.card)]

/-- [Adding the empty unused-sign block leaves the exact component occupancy
sum unchanged, so singleton cancellation is retained. [the documented result](goal) -/
-- @node: signComponentWeight_sum
lemma signComponentWeight_sum (n k : ℕ) (x : Fin n → Covariate) (B : ℝ) :
    (∑ c : SignComponentBlock k x, signComponentWeight k x B c) =
      cellComponentWeight n k B x := by
  classical
  rw [cellComponentWeight_eq_components]
  let G := originalRecordSignGraph k x
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have huniv : (Finset.univ : Finset (SignComponentBlock k x)) =
      Finset.insertNone (Finset.univ : Finset G.ConnectedComponent) := by
    ext c
    cases c <;> simp
  rw [huniv, Finset.sum_insertNone]
  simp only [signComponentWeight, zero_add]
  apply Finset.sum_congr
  · ext c; simp
  · intro c hc; rfl

/-- [The actual mixed conditional likelihood factors over the original-record
sign graph, with every root and cell formula substituted. [the documented result](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hk). -/
-- @node: mixed_original_component_factorization
lemma mixed_original_component_factorization {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (b : Bool) (η ζ : ℝ) (x : Fin n → Covariate) (a y : Fin n → Bool) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    let cell := fun i σ => 4*mixedCells b k σ η ζ (a i) (y i) (x i)
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, ∏ i : Fin n, cell i σ) =
    ∏ c : SignComponentBlock k x,
      (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
        ∏ i ∈ Finset.univ.filter (fun i => block i = c),
          cell i (componentSignExtension owner c σ) := by
  apply recordCells_component_factorization k hk x
  intro i σ τ h
  rw [mixedCells_endpoint_congr b k σ τ η ζ (a i) (y i) (x i) h]

/-- [The actual fair mixture and comparator conditional likelihoods factor over
that same graph, uniformly through zero amplitudes and effects. [the documented result](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hk). -/
-- @node: fair_original_component_factorization
lemma fair_original_component_factorization {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (b : Bool) (t δ : ℝ) (x : Fin n → Covariate) (a y : Fin n → Bool) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    let cell := fun i σ => 4*fairCells b k σ t δ (a i) (y i) (x i)
    (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
      (∑ σ : Fin (k+1) → Bool, ∏ i : Fin n, cell i σ) =
    ∏ c : SignComponentBlock k x,
      (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
      ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
        ∏ i ∈ Finset.univ.filter (fun i => block i = c),
          cell i (componentSignExtension owner c σ) := by
  apply recordCells_component_factorization k hk x
  intro i σ τ h
  rw [fairCells_endpoint_congr b k σ τ t δ (a i) (y i) (x i) h]

/-- [Tensorization applies to the actual mixed laws conditional on every
original covariate, with labels regrouped only along latent-sign components. [the documented result](goal) Under [the stated assumptions](hyp:hk,hη,hζ,x). -/
-- @node: mixed_conditional_label_hellinger_le_components
lemma mixed_conditional_label_hellinger_le_components {n : ℕ}
    (k : ℕ) (hk : 1 ≤ k) (η ζ : ℝ)
    (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps) (x : Fin n → Covariate) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (∑ l : Fin n → Bool × Bool,
      (Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i, (mixedLaw false k σ η ζ).cells (l i).1 (l i).2 (x i)) -
       Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i, (mixedLaw true k σ η ζ).cells (l i).1 (l i).2 (x i))) ^ 2) ≤
      ∑ c : SignComponentBlock k x, ∑ l,
        (Real.sqrt (conditionalComponentLabelMass owner block
          (fun σ => mixedLaw false k σ η ζ) x c l) -
         Real.sqrt (conditionalComponentLabelMass owner block
          (fun σ => mixedLaw true k σ η ζ) x c l)) ^ 2 := by
  have hvalid (b : Bool) (σ : Fin (k+1) → Bool) :
      ValidCells (mixedCells b k σ η ζ) :=
    ((calib_constants_spec.2.2.2 k hk σ).1 η ζ hη hζ b).1
  apply original_conditional_label_hellinger_le_components
  all_goals
    intro i σ τ hsign a y
    simp only [mixedLaw, totalCellLaw, dif_pos (hvalid _ _), lawFromCells]
    apply mixedCells_endpoint_congr
    intro j hj
    unfold endpointSign
    rw [hsign _ (signComponentOwner_incident k hk x i j hj)]

/-- [The fair mixture is tensorized against its deterministic comparator on
exactly the same original covariate-dependent components. [the documented result](goal) Under [the stated assumptions](hyp:hk,ht,hδ,x). -/
-- @node: fair_conditional_label_hellinger_le_components
lemma fair_conditional_label_hellinger_le_components {n : ℕ}
    (k : ℕ) (hk : 1 ≤ k) (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ calibEps)
    (x : Fin n → Covariate) :
    let owner := signComponentOwner k x
    let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
    (∑ l : Fin n → Bool × Bool,
      (Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i, (fairLaw k σ t δ).cells (l i).1 (l i).2 (x i)) -
       Real.sqrt (∏ i, (fairComparator k t δ).cells (l i).1 (l i).2 (x i))) ^ 2) ≤
      ∑ c : SignComponentBlock k x, ∑ l,
        (Real.sqrt (conditionalComponentLabelMass owner block
          (fun σ => fairLaw k σ t δ) x c l) -
         Real.sqrt (conditionalComponentLabelMass owner block
          (fun _ => fairComparator k t δ) x c l)) ^ 2 := by
  have hvalid (σ : Fin (k+1) → Bool) : ValidCells (fairCells true k σ t δ) :=
    ((calib_constants_spec.2.2.2 k hk σ).2 t δ ht hδ true).1
  have h := original_conditional_label_hellinger_le_components
    (signComponentOwner k x)
    (fun i => some ((originalRecordSignGraph k x).connectedComponentMk i))
    (fun σ => fairLaw k σ t δ) (fun _ => fairComparator k t δ) x
    (by
      intro i σ τ hsign a y
      simp only [fairLaw, totalCellLaw, dif_pos (hvalid _), lawFromCells]
      apply fairCells_endpoint_congr
      intro j hj
      unfold endpointSign
      rw [hsign _ (signComponentOwner_incident k hk x i j hj)])
    (by intro i σ τ hsign a y; rfl)
  simpa [Fintype.card_ne_zero] using h

/-- [Common dominating reference for exactly n records. -/
def sampleReference (n : ℕ) : Measure (Fin n → Record) :=
  Causalean.Stat.UStatistic.LocalizedVariance.iidLaw recordReference n
/-- Unhalved squared Hellinger distance, through the actual Radon--Nikodym densities. -/
def originalRecordHellinger (n : ℕ) (Q Q' : Measure (Fin n → Record)) : ℝ :=
  Causalean.Stat.hellingerSqDensity (sampleReference n)
    (fun o => (Q.rnDeriv (sampleReference n) o).toReal)
    (fun o => (Q'.rnDeriv (sampleReference n) o).toReal)
/-- Identical original-record measures have zero squared Hellinger distance. [the stated conclusion](goal) holds. -/
-- @node: originalRecordHellinger_self
lemma originalRecordHellinger_self (n : ℕ) (Q : Measure (Fin n → Record)) :
    originalRecordHellinger n Q Q = 0 := by
  simp [originalRecordHellinger, Causalean.Stat.hellingerSqDensity]
/-- The mixed distance is exactly the integral of the actual finite-prior likelihoods. [the stated conclusion](goal) holds. -/
-- @node: mixed_originalRecordHellinger_density
lemma mixed_originalRecordHellinger_density (n k : ℕ) (η ζ : ℝ) :
    originalRecordHellinger n (mixedMixture false n k η ζ) (mixedMixture true n k η ζ) =
      Causalean.Stat.hellingerSqDensity (sampleReference n)
        (signMixtureCellDensity n k (fun σ => mixedLaw false k σ η ζ))
        (signMixtureCellDensity n k (fun σ => mixedLaw true k σ η ζ)) := by
  have h0 := finiteSignMixture_rnDeriv n k (fun σ => mixedLaw false k σ η ζ)
    (fun σ => totalCellLaw_uniform _)
  have h1 := finiteSignMixture_rnDeriv n k (fun σ => mixedLaw true k σ η ζ)
    (fun σ => totalCellLaw_uniform _)
  unfold originalRecordHellinger Causalean.Stat.hellingerSqDensity
  apply integral_congr_ae
  filter_upwards [h0, h1] with o ho0 ho1
  dsimp only [mixedMixture, fairMixture, sampleReference,
    Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] at ho0 ho1 ⊢
  rw [ho0, ho1]

/-- The fair distance uses the averaged random likelihood and the actual iid comparator likelihood. [the stated conclusion](goal) holds. -/
-- @node: fair_originalRecordHellinger_density
lemma fair_originalRecordHellinger_density (n k : ℕ) (t δ : ℝ) :
    originalRecordHellinger n (fairMixture n k t δ)
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t δ).measure n) =
      Causalean.Stat.hellingerSqDensity (sampleReference n)
        (signMixtureCellDensity n k (fun σ => fairLaw k σ t δ))
        (sampleCellDensity n (fairComparator k t δ)) := by
  have h0 := finiteSignMixture_rnDeriv n k (fun σ => fairLaw k σ t δ)
    (fun σ => totalCellLaw_uniform _)
  have h1 := uniformObservedLaw_iid_rnDeriv n (fairComparator k t δ)
    (totalCellLaw_uniform _)
  unfold originalRecordHellinger Causalean.Stat.hellingerSqDensity
  apply integral_congr_ae
  filter_upwards [h0, h1] with o ho0 ho1
  dsimp only [mixedMixture, fairMixture, sampleReference,
    Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] at ho0 ho1 ⊢
  rw [ho0, ho1]

/-- The mixed full-sample distance integrates the conditional label distance
against the common original covariate law, with no loss of observations. [the documented result](goal) -/
-- @node: mixed_originalRecordHellinger_conditional
lemma mixed_originalRecordHellinger_conditional (n k : ℕ) (η ζ : ℝ) :
    originalRecordHellinger n (mixedMixture false n k η ζ) (mixedMixture true n k η ζ) =
      ∫ x, Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => labelReference))
        (fun l => signMixtureCellDensity n k (fun σ => mixedLaw false k σ η ζ)
          (fun i => (x i, l i)))
        (fun l => signMixtureCellDensity n k (fun σ => mixedLaw true k σ η ζ)
          (fun i => (x i, l i))) ∂Measure.pi (fun _ : Fin n => uniformLaw) := by
  rw [mixed_originalRecordHellinger_density]
  exact mixture_hellinger_conditional_integral n _ _
    (signMixtureCellDensity_integrable n k _) (signMixtureCellDensity_integrable n k _)
    (signMixtureCellDensity_nonneg n k _) (signMixtureCellDensity_nonneg n k _)

/-- The fair mixture and comparator also share exactly the original covariate
marginal, so their distance is the integral of their conditional label distance. [the documented result](goal) -/
-- @node: fair_originalRecordHellinger_conditional
lemma fair_originalRecordHellinger_conditional (n k : ℕ) (t δ : ℝ) :
    originalRecordHellinger n (fairMixture n k t δ)
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t δ).measure n) =
      ∫ x, Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => labelReference))
        (fun l => signMixtureCellDensity n k (fun σ => fairLaw k σ t δ)
          (fun i => (x i, l i)))
        (fun l => sampleCellDensity n (fairComparator k t δ) (fun i => (x i, l i)))
        ∂Measure.pi (fun _ : Fin n => uniformLaw) := by
  rw [fair_originalRecordHellinger_density]
  exact mixture_hellinger_conditional_integral n _ _
    (signMixtureCellDensity_integrable n k _) (sampleCellDensity_integrable n _)
    (signMixtureCellDensity_nonneg n k _) (sampleCellDensity_nonneg n _)

/-- A one-record likelihood is just the original record's four-cell density. [the stated conclusion](goal) holds. -/
-- @node: sampleCellDensity_one
lemma sampleCellDensity_one (P : ObservedLaw) (o : Fin 1 → Record) :
    sampleCellDensity 1 P o = recordCellDensity P (o 0) := by
  simp [sampleCellDensity]

/-- Exact mixed singleton matching identifies the actual one-record mixture densities. Under the stated assumptions. [The stated hypotheses](hyp:hk,hη,hζ) hold, and [the stated conclusion follows](goal). -/
-- @node: mixed_singleton_density_matching
lemma mixed_singleton_density_matching (k : ℕ) (hk : 1 ≤ k) (η ζ : ℝ)
    (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps) :
    signMixtureCellDensity 1 k (fun σ => mixedLaw false k σ η ζ) =
      signMixtureCellDensity 1 k (fun σ => mixedLaw true k σ η ζ) := by
  funext o
  simp only [signMixtureCellDensity, sampleCellDensity_one, recordCellDensity,
    ← Finset.mul_sum]
  rw [(calib_singletons_spec k hk).1 η ζ hη hζ (o 0).2.1 (o 0).2.2 (o 0).1]

/-- [Exact fair singleton matching identifies the actual one-record mixture
with the comparator density, uniformly in the effect. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ). Under [the stated assumptions](hyp:hk). -/
-- @node: fair_singleton_density_matching
lemma fair_singleton_density_matching (k : ℕ) (hk : 1 ≤ k) (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ calibEps) :
    signMixtureCellDensity 1 k (fun σ => fairLaw k σ t δ) =
      sampleCellDensity 1 (fairComparator k t δ) := by
  funext o
  rw [signMixtureCellDensity_card_average]
  simp only [Fin.prod_univ_one, sampleCellDensity_one, recordCellDensity,
    ← Finset.mul_sum]
  have hmatch := (calib_singletons_spec k hk).2 t δ ht hδ
    (o 0).2.1 (o 0).2.2 (o 0).1
  calc
    _ = 4 * ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, (fairLaw k σ t δ).cells (o 0).2.1 (o 0).2.2 (o 0).1) := by ring
    _ = _ := by rw [hmatch]

/-- [With one original record the mixed Hellinger discrepancy vanishes exactly.](goal) Under [the stated assumptions](hyp:hk,hη,hζ). -/
-- @node: mixed_originalRecordHellinger_one
lemma mixed_originalRecordHellinger_one (k : ℕ) (hk : 1 ≤ k) (η ζ : ℝ)
    (hη : |η| ≤ calibEps) (hζ : |ζ| ≤ calibEps) :
    originalRecordHellinger 1 (mixedMixture false 1 k η ζ)
      (mixedMixture true 1 k η ζ) = 0 := by
  rw [mixed_originalRecordHellinger_density,
    mixed_singleton_density_matching k hk η ζ hη hζ]
  simp [Causalean.Stat.hellingerSqDensity]

/-- [With one original record the fair Hellinger discrepancy vanishes exactly.](goal) Under [the stated assumptions](hyp:hk,hδ). Under [the stated assumptions](hyp:ht). -/
-- @node: fair_originalRecordHellinger_one
lemma fair_originalRecordHellinger_one (k : ℕ) (hk : 1 ≤ k) (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ calibEps) :
    originalRecordHellinger 1 (fairMixture 1 k t δ)
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
        (fairComparator k t δ).measure 1) = 0 := by
  rw [fair_originalRecordHellinger_density,
    fair_singleton_density_matching k hk t δ ht hδ]
  simp [Causalean.Stat.hellingerSqDensity]

/-- Public occupancy threshold. -/
def mixtureKappa : ℝ := 1/(96*Real.exp 1)
/-- The explicit envelope constant uses the support theorem's same M. -/
def mixtureConstant : ℝ := 96*Real.exp 2*8^2*calibM^4
-- @node: lem:original-record-mixtures
/-- Both original-record mixture bounds, uniformly in effect, with no singleton remainder. [the stated conclusion](goal) holds. -/
lemma original_record_mixtures : 0 < mixtureKappa ∧ 0 < mixtureConstant ∧
  ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → (n : ℝ)/(k : ℝ) ≤ mixtureKappa →
  ∀ η ζ δ : ℝ, |η| ≤ calibEps → |ζ| ≤ calibEps → |δ| ≤ calibEps →
    originalRecordHellinger n (mixedMixture false n k η ζ) (mixedMixture true n k η ζ) ≤
      mixtureConstant*(n : ℝ)^2/(k : ℝ)*η^2*ζ^2 ∧
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) →
      originalRecordHellinger n (fairMixture n k t δ)
        (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t δ).measure n) ≤
          mixtureConstant*(n : ℝ)^2/(k : ℝ)*δ^4 := by
  have hConstants := calib_constants_spec
  refine ⟨?_, ?_, ?_⟩
  · unfold mixtureKappa
    positivity
  · unfold mixtureConstant
    have hM : 0 < calibM := hConstants.2.1
    positivity
  · intro n k hn hk hnk η ζ δ hη hζ hδ
    let componentWeight : ℝ :=
      ∫ x, cellComponentWeight n k 8 x ∂Measure.pi (fun _ : Fin n => uniformLaw)
    have hOccupancyBound (ω : ℝ) : calibM^4*ω^2*componentWeight ≤
        mixtureConstant*(n : ℝ)^2/(k : ℝ)*ω^2 :=
      mixture_weighted_component_integral_bound n k hk hnk calibM ω
    constructor
    · by_cases hn1 : n = 1
      · subst n
        rw [mixed_originalRecordHellinger_one k hk η ζ hη hζ]
        unfold mixtureConstant
        positivity
      by_cases hη0 : η = 0
      · subst η
        rw [mixedMixture_zero_left, originalRecordHellinger_self]
        simp
      by_cases hζ0 : ζ = 0
      · subst ζ
        rw [mixedMixture_zero_right, originalRecordHellinger_self]
        simp
      have hReduction :
          originalRecordHellinger n (mixedMixture false n k η ζ) (mixedMixture true n k η ζ) ≤
            calibM^4*(η*ζ)^2*componentWeight := by
        rw [mixed_originalRecordHellinger_conditional]
        have hConditional (x : Fin n → Covariate) :
            Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => labelReference))
              (fun l => signMixtureCellDensity n k (fun σ => mixedLaw false k σ η ζ)
                (fun i => (x i, l i)))
              (fun l => signMixtureCellDensity n k (fun σ => mixedLaw true k σ η ζ)
                (fun i => (x i, l i))) ≤
              calibM^4*(η*ζ)^2*cellComponentWeight n k 8 x := by
          rw [mixture_conditional_hellinger_eq_label_sum]
          apply (mixed_conditional_label_hellinger_le_components k hk η ζ hη hζ x).trans
          let owner := signComponentOwner k x
          let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
          have hDensity : ∀ c : SignComponentBlock k x,
              ∀ l : {i : Fin n // block i = c} → Bool × Bool,
              (Real.sqrt ((Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
                ∑ σ, ∏ i : {i : Fin n // block i = c},
                  recordCellDensity (mixedLaw false k (componentSignExtension owner c σ) η ζ) (x i.1,l i))-
               Real.sqrt ((Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
                ∑ σ, ∏ i : {i : Fin n // block i = c},
                  recordCellDensity (mixedLaw true k (componentSignExtension owner c σ) η ζ) (x i.1,l i)))^2 ≤
                calibM^4*(η*ζ)^2*signComponentWeight k x 8 c := by
            intro c l
            by_cases hsmall : Fintype.card {i : Fin n // block i = c} ≤ 1
            · have he := mixedDensity_small_block_matching k hk x c l η ζ hη hζ hsmall
              rw [he, sub_self, zero_pow (by decide : 2 ≠ 0),
                signComponentWeight_eq_zero_of_small k x 8 c hsmall, mul_zero]
            · have hb := mixed_component_hellinger_from_support k hk x c l η ζ hη hζ
              have hcard : 2 ≤ Fintype.card {i : Fin n // block i = c} := by omega
              have hw : signComponentWeight k x 8 c =
                  (Fintype.card {i : Fin n // block i = c} : ℝ)^4 *
                    8^(Fintype.card {i : Fin n // block i = c}) := by
                rw [signComponent_record_card] at hcard ⊢
                cases c with
                | none => simp at hcard
                | some v => simp only [signComponentWeight, if_pos hcard]
              apply hb.trans_eq
              rw [hw]
              ring
          calc
            _ ≤ ∑ c : SignComponentBlock k x,
                calibM^4*(η*ζ)^2*signComponentWeight k x 8 c := by
              apply Finset.sum_le_sum
              intro c hc
              exact conditionalComponent_mass_hellinger_le_density_bound owner block
                _ _ x c _ (hDensity c)
            _ = _ := by rw [← Finset.mul_sum, signComponentWeight_sum]
        calc
          _ ≤ ∫ x, calibM^4*(η*ζ)^2*cellComponentWeight n k 8 x
              ∂Measure.pi (fun _ : Fin n => uniformLaw) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => integral_nonneg (fun l => sq_nonneg _)))
              ((cellComponentWeight_integrable n k 8).const_mul _)
              (Filter.Eventually.of_forall hConditional)
          _ = _ := integral_const_mul _ _
      apply hReduction.trans
      apply (hOccupancyBound (η*ζ)).trans_eq
      ring
    · intro t ht
      by_cases hn1 : n = 1
      · subst n
        rw [fair_originalRecordHellinger_one k hk t δ ht hδ]
        unfold mixtureConstant
        positivity
      by_cases hδ0 : δ = 0
      · subst δ
        rw [fairMixture_zero_amplitude, originalRecordHellinger_self]
        simp
      have hReductionNonneg (d : ℝ) (hd : 0 ≤ d) (hdsmall : d ≤ calibEps) :
          originalRecordHellinger n (fairMixture n k t d)
            (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t d).measure n) ≤
              calibM^4*(d^2)^2*componentWeight := by
        rw [fair_originalRecordHellinger_conditional]
        have hConditional (x : Fin n → Covariate) :
            Causalean.Stat.hellingerSqDensity (Measure.pi (fun _ : Fin n => labelReference))
              (fun l => signMixtureCellDensity n k (fun σ => fairLaw k σ t d)
                (fun i => (x i, l i)))
              (fun l => sampleCellDensity n (fairComparator k t d) (fun i => (x i, l i))) ≤
              calibM^4*(d^2)^2*cellComponentWeight n k 8 x := by
          have hconstant (l : Fin n → Bool × Bool) :
              sampleCellDensity n (fairComparator k t d) (fun i => (x i,l i)) =
                signMixtureCellDensity n k (fun _ => fairComparator k t d)
                  (fun i => (x i,l i)) := by
            rw [signMixtureCellDensity_card_average]
            simp [sampleCellDensity, Fintype.card_ne_zero]
          simp_rw [hconstant]
          rw [mixture_conditional_hellinger_eq_label_sum]
          have hTensor := fair_conditional_label_hellinger_le_components k hk t d ht
            (by rw [abs_of_nonneg hd]; exact hdsmall) x
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ (by positivity :
              (Fintype.card (Fin (k+1) → Bool) : ℝ) ≠ 0), one_mul] at hTensor ⊢
          apply hTensor.trans
          let owner := signComponentOwner k x
          let block := fun i => some ((originalRecordSignGraph k x).connectedComponentMk i)
          have hDensity : ∀ c : SignComponentBlock k x,
              ∀ l : {i : Fin n // block i = c} → Bool × Bool,
              (Real.sqrt ((Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
                ∑ σ, ∏ i : {i : Fin n // block i = c},
                  recordCellDensity (fairLaw k (componentSignExtension owner c σ) t d) (x i.1,l i))-
               Real.sqrt ((Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ)⁻¹ *
                ∑ σ : {s : Fin (k+1) // owner s = c} → Bool,
                  ∏ i : {i : Fin n // block i = c},
                  recordCellDensity (fairComparator k t d) (x i.1,l i)))^2 ≤
                calibM^4*(d^2)^2*signComponentWeight k x 8 c := by
            intro c l
            by_cases hsmall : Fintype.card {i : Fin n // block i = c} ≤ 1
            · have he := fairDensity_small_block_matching k hk x c l t d ht
                (by rw [abs_of_nonneg hd]; exact hdsmall) hsmall
              rw [he, sub_self, zero_pow (by decide : 2 ≠ 0),
                signComponentWeight_eq_zero_of_small k x 8 c hsmall, mul_zero]
            · have hb := fair_component_hellinger_from_support k hk x c l t d ht
                (by rw [abs_of_nonneg hd]; exact hdsmall)
              have hcard : 2 ≤ Fintype.card {i : Fin n // block i = c} := by omega
              have hw : signComponentWeight k x 8 c =
                  (Fintype.card {i : Fin n // block i = c} : ℝ)^4 *
                    8^(Fintype.card {i : Fin n // block i = c}) := by
                rw [signComponent_record_card] at hcard ⊢
                cases c with
                | none => simp at hcard
                | some v => simp only [signComponentWeight, if_pos hcard]
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                ← mul_assoc, inv_mul_cancel₀ (by positivity :
                  (Fintype.card ({s : Fin (k+1) // owner s = c} → Bool) : ℝ) ≠ 0),
                one_mul]
              apply hb.trans_eq
              rw [hw]
              ring
          calc
            _ ≤ ∑ c : SignComponentBlock k x,
                calibM^4*(d^2)^2*signComponentWeight k x 8 c := by
              apply Finset.sum_le_sum
              intro c hc
              exact conditionalComponent_mass_hellinger_le_density_bound owner block
                _ _ x c _ (hDensity c)
            _ = _ := by rw [← Finset.mul_sum, signComponentWeight_sum]
        calc
          _ ≤ ∫ x, calibM^4*(d^2)^2*cellComponentWeight n k 8 x
              ∂Measure.pi (fun _ : Fin n => uniformLaw) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => integral_nonneg (fun l => sq_nonneg _)))
              ((cellComponentWeight_integrable n k 8).const_mul _)
              (Filter.Eventually.of_forall hConditional)
          _ = _ := integral_const_mul _ _
      have hSigned :
          originalRecordHellinger n (fairMixture n k t δ)
            (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t δ).measure n) =
          originalRecordHellinger n (fairMixture n k t |δ|)
            (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t |δ|).measure n) := by
        by_cases hd : 0 ≤ δ
        · rw [abs_of_nonneg hd]
        · rw [abs_of_neg (lt_of_not_ge hd), fairMixture_even, fairComparator_even]
      have hReduction :
          originalRecordHellinger n (fairMixture n k t δ)
            (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t δ).measure n) ≤
              calibM^4*(δ^2)^2*componentWeight := by
        rw [hSigned]
        simpa only [sq_abs] using hReductionNonneg |δ| (abs_nonneg δ) hδ
      apply hReduction.trans
      apply (hOccupancyBound (δ^2)).trans_eq
      ring
end CausalSmith.Stat.LogoddsLowsmoothFrontier
