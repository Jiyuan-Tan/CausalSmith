module
public import Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Pointwise
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Probability.Independence.Integration

/-!
# Centered outcome products in a shared-sign cell

The posterior outcome likelihood is the posterior average of finite products.
Independent outcome-score pairs across records give orthogonality of distinct
subsets. Integrability is derived from individual score and overlap-product
integrability, rather than assumed for the full likelihood product.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace Causalean.Stat.Minimax.Mixture.PoissonLatentSign

/-- The posterior outcome likelihood of a cell with scores uᵢ, at outcome values vᵢ, is
the average over the shared sign ±1, weighted by the two sign likelihoods and divided by
their sum, of the product over the selected records of 1 + γ · (±uᵢ)/(1 ± τuᵢ) · vᵢ. -/
def outcomeLikelihood {m : ℕ} (τ γ : ℝ) (c : Cell m) (v : Fin m → ℝ) : ℝ :=
  (signLikelihood τ c 1 *
      (∏ i ∈ selected c, (1 + γ * (c.1 i / (1 + τ * c.1 i)) * v i)) +
    signLikelihood τ c (-1) *
      (∏ i ∈ selected c, (1 + γ * ((-c.1 i) / (1 - τ * c.1 i)) * v i))) /
    denominator τ c

/-- The outcome likelihood expands over all selected subsets with their posterior coefficients. -/
theorem outcomeLikelihood_expansion {m : ℕ} (τ γ : ℝ) (c : Cell m)
    (v : Fin m → ℝ) :
    outcomeLikelihood τ γ c v = ∑ S ∈ (selected c).powerset,
      γ ^ S.card * posterior τ c S * ∏ i ∈ S, v i := by
  -- Finset.prod_one_add followed by distributing the posterior weights.
  -- This algebraic identity needs no denominator nonzero assumption: distribute
  -- division across the finite sum rather than canceling the denominator.
  classical
  unfold outcomeLikelihood posterior
  simp only [Finset.prod_one_add, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Centered outcome-score pairs are independent across records, have integrable
individual scores and pair products, zero means, and the specified common overlap. -/
structure CenteredOutcomePair {ι Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (v w : ι → Ω → ℝ) (z : ℝ) : Prop where
  /-- Pairs of scores are jointly independent across records. -/
  independent : iIndepFun (fun i ω => (v i ω, w i ω)) ρ
  /-- Each first score is integrable. -/
  integrable_left : ∀ i, Integrable (v i) ρ
  /-- Each second score is integrable. -/
  integrable_right : ∀ i, Integrable (w i) ρ
  /-- Each within-record overlap product is integrable. -/
  integrable_pair : ∀ i, Integrable (fun ω => v i ω * w i ω) ρ
  /-- Each first score has zero mean. -/
  centered_left : ∀ i, ∫ ω, v i ω ∂ρ = 0
  /-- Each second score has zero mean. -/
  centered_right : ∀ i, ∫ ω, w i ω ∂ρ = 0
  /-- Every record has overlap z. -/
  overlap : ∀ i, ∫ ω, v i ω * w i ω ∂ρ = z

/-- Regroup two subset products using one factor for each index in their union. -/
private theorem subset_pair_regroup {ι : Type*} [DecidableEq ι]
    (S R : Finset ι) (v w : ι → ℝ) :
    (∏ i ∈ S, v i) * (∏ i ∈ R, w i) =
      ∏ i ∈ S ∪ R, (if i ∈ S then v i else 1) * (if i ∈ R then w i else 1) := by
  rw [Finset.prod_mul_distrib]
  have hp (A B : Finset ι) (f : ι → ℝ) :
      (∏ i ∈ A ∪ B, if i ∈ A then f i else 1) = ∏ i ∈ A, f i := by
    rw [← Finset.prod_subset Finset.subset_union_left
      (fun i _ hi => if_neg hi)]
    exact Finset.prod_congr rfl (fun i hi => if_pos hi)
  rw [hp S R v, Finset.union_comm S R, hp R S w]

/-- Independence and individual integrability imply integrability of a finite product. -/
private theorem integrable_independent_finset {ι Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {f : ι → Ω → ℝ}
    (hf : iIndepFun f ρ) (hi : ∀ i, Integrable (f i) ρ) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, f i ω) ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hind := hf.indepFun_finsetProd_of_notMem₀
      (fun i => (hi i).aestronglyMeasurable.aemeasurable) ha
    have hind' : IndepFun (fun ω => ∏ i ∈ s, f i ω) (f a) ρ := by
      simpa only [Finset.prod_fn] using hind
    have hprod := hind'.symm.integrable_mul (hi a) ih
    simpa only [Pi.mul_def, Finset.prod_insert ha] using hprod

/-- The union factor is a measurable function of its score pair. -/
private theorem independent_union_factors {ι Ω : Type*} [DecidableEq ι]
    [MeasurableSpace Ω] {ρ : Measure Ω} {v w : ι → Ω → ℝ} {z : ℝ}
    (h : CenteredOutcomePair ρ v w z) (S R : Finset ι) :
    iIndepFun (fun i ω => (if i ∈ S then v i ω else 1) *
      (if i ∈ R then w i ω else 1)) ρ := by
  exact h.independent.comp
    (fun i (x : ℝ × ℝ) => (if i ∈ S then x.1 else 1) *
      (if i ∈ R then x.2 else 1))
    (fun i => by by_cases hs : i ∈ S <;> by_cases hr : i ∈ R <;>
      simp only [hs, hr, if_true, if_false] <;> fun_prop)

/-- Each union factor has one of the three assumed integrability receipts. -/
private theorem integrable_union_factor {ι Ω : Type*} [DecidableEq ι]
    [MeasurableSpace Ω] {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {v w : ι → Ω → ℝ} {z : ℝ} (h : CenteredOutcomePair ρ v w z)
    (S R : Finset ι) (i : ι) :
    Integrable (fun ω => (if i ∈ S then v i ω else 1) *
      (if i ∈ R then w i ω else 1)) ρ := by
  by_cases hs : i ∈ S <;> by_cases hr : i ∈ R
  · simpa [hs, hr] using h.integrable_pair i
  · simpa [hs, hr] using h.integrable_left i
  · simpa [hs, hr] using h.integrable_right i
  · simp [hs, hr]

/-- Products over two finite subsets are integrable for independent centered outcome pairs. -/
theorem integrable_subset_pair {ι Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {v w : ι → Ω → ℝ} {z : ℝ}
    (h : CenteredOutcomePair ρ v w z) (S R : Finset ι) :
    Integrable (fun ω => (∏ i ∈ S, v i ω) * ∏ i ∈ R, w i ω) ρ := by
  -- Regroup as a product on S∪R of v, w, or vw; reuse independent integration.
  -- Use the measurable map (x,y) ↦ (if i∈S then x else 1) *
  -- (if i∈R then y else 1) on each jointly independent pair. The integrability
  -- fields cover all membership cases; restrict the resulting family to S∪R.
  classical
  simp_rw [subset_pair_regroup S R]
  exact integrable_independent_finset (independent_union_factors h S R)
    (integrable_union_factor h S R) (S ∪ R)

/-- Distinct subset products are orthogonal; equal subsets have cross moment z to their size. -/
theorem integral_subset_pair {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {v w : ι → Ω → ℝ} {z : ℝ}
    (h : CenteredOutcomePair ρ v w z) (S R : Finset ι) :
    (∫ ω, (∏ i ∈ S, v i ω) * ∏ i ∈ R, w i ω ∂ρ) =
      if S = R then z ^ S.card else 0 := by
  -- For the same regrouped union product, use
  -- iIndepFun.integral_fun_prod_eq_prod_integral on the union subtype.
  -- When S≠R, a symmetric-difference index contributes a centered zero factor.
  classical
  let f : ι → Ω → ℝ := fun i ω =>
    (if i ∈ S then v i ω else 1) * (if i ∈ R then w i ω else 1)
  have hi : ∀ i, Integrable (f i) ρ := integrable_union_factor h S R
  have hind : iIndepFun f ρ := independent_union_factors h S R
  have hfactor : (∫ ω, (∏ i ∈ S, v i ω) * ∏ i ∈ R, w i ω ∂ρ) =
      ∏ i ∈ S ∪ R, ∫ ω, f i ω ∂ρ := by
    simp_rw [subset_pair_regroup S R]
    have hind' := hind.precomp (g := fun i : ↥(S ∪ R) => (i : ι)) Subtype.val_injective
    change (∫ ω, ∏ i ∈ S ∪ R, f i ω ∂ρ) = _
    simp_rw [← Finset.prod_coe_sort (S ∪ R)]
    exact hind'.integral_fun_prod_eq_prod_integral (fun i => (hi i).aestronglyMeasurable)
  rw [hfactor]
  by_cases heq : S = R
  · subst R
    simp only [Finset.union_self]
    calc
      (∏ i ∈ S, ∫ ω, f i ω ∂ρ) = ∏ _i ∈ S, z := by
        apply Finset.prod_congr rfl
        intro i hiS
        simpa [f, hiS] using h.overlap i
      _ = z ^ S.card := Finset.prod_const _
  · rw [if_neg heq]
    have hex : ∃ i, (i ∈ S ∧ i ∉ R) ∨ (i ∈ R ∧ i ∉ S) := by
      by_contra hn
      apply heq
      ext i
      have hh := (not_exists.mp hn) i
      constructor <;> intro hi
      · by_contra hr; exact hh (Or.inl ⟨hi, hr⟩)
      · by_contra hs; exact hh (Or.inr ⟨hi, hs⟩)
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (i := i)
    · rcases hi with hi | hi
      · exact Finset.mem_union_left R hi.1
      · exact Finset.mem_union_right S hi.1
    · rcases hi with hi | hi
      · simpa [f, hi.1, hi.2] using h.centered_left i
      · simpa [f, hi.1, hi.2] using h.centered_right i

/-- The two posterior outcome likelihoods have an integrable product under centered
independent outcome pairs, without requiring bounded outcome scores. -/
theorem integrable_outcomeLikelihood_pair {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {v w : Fin m → Ω → ℝ} {z : ℝ}
    (h : CenteredOutcomePair ρ v w z) (τ γ : ℝ) (c : Cell m) :
    Integrable (fun ω => outcomeLikelihood τ γ c (fun i => v i ω) *
      outcomeLikelihood τ γ c (fun i => w i ω)) ρ := by
  -- Expand both finite likelihood sums and use integrable_subset_pair for each
  -- double-sum term. No boundedness of outcome scores is needed.
  classical
  simp_rw [outcomeLikelihood_expansion, Finset.sum_mul, Finset.mul_sum]
  apply integrable_finsetSum
  intro S _
  apply integrable_finsetSum
  intro R _
  convert (integrable_subset_pair h S R).const_mul
    ((γ ^ S.card * posterior τ c S) * (γ ^ R.card * posterior τ c R)) using 1 <;>
    first | rfl | (funext ω; ring)

/-- The finite-cell cross moment is the sum of squared posterior subset coefficients
times the outcome amplitude and overlap powers. -/
theorem integral_outcomeLikelihood_pair {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {v w : Fin m → Ω → ℝ} {z : ℝ}
    (h : CenteredOutcomePair ρ v w z) (τ γ : ℝ) (c : Cell m) :
    (∫ ω, outcomeLikelihood τ γ c (fun i => v i ω) *
      outcomeLikelihood τ γ c (fun i => w i ω) ∂ρ) =
      ∑ S ∈ (selected c).powerset, γ ^ (2 * S.card) *
        posterior τ c S ^ 2 * z ^ S.card := by
  -- Integrate the finite double expansion using its termwise receipts, then
  -- integral_subset_pair eliminates every off-diagonal term.
  classical
  let a : Finset (Fin m) → ℝ := fun S => γ ^ S.card * posterior τ c S
  have ht (S R : Finset (Fin m)) : Integrable (fun ω =>
      (a S * ∏ i ∈ S, v i ω) * (a R * ∏ i ∈ R, w i ω)) ρ := by
    convert (integrable_subset_pair h S R).const_mul (a S * a R) using 1
    funext ω
    ring
  have hint (S R : Finset (Fin m)) :
      (∫ ω, (a S * ∏ i ∈ S, v i ω) * (a R * ∏ i ∈ R, w i ω) ∂ρ) =
      (a S * a R) * (if S = R then z ^ S.card else 0) := by
    have heq : (fun ω => (a S * ∏ i ∈ S, v i ω) * (a R * ∏ i ∈ R, w i ω)) =
        (fun ω => (a S * a R) * ((∏ i ∈ S, v i ω) * ∏ i ∈ R, w i ω)) := by
      funext ω
      ring
    rw [heq, integral_const_mul, integral_subset_pair h S R]
  simp_rw [outcomeLikelihood_expansion, Finset.sum_mul, Finset.mul_sum]
  change (∫ ω, ∑ S ∈ (selected c).powerset, ∑ R ∈ (selected c).powerset,
    (a S * ∏ i ∈ S, v i ω) * (a R * ∏ i ∈ R, w i ω) ∂ρ) = _
  rw [integral_finsetSum _ (fun S _ => integrable_finsetSum _ (fun R _ => ht S R))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [integral_finsetSum _ (fun R _ => ht S R)]
  simp_rw [hint]
  rw [Finset.sum_eq_single S]
  · dsimp [a]
    simp only [if_true, pow_mul, pow_two]
    ring
  · intro R _ hRS
    rw [if_neg (Ne.symm hRS), mul_zero]
  · intro hnot
    exact (hnot hS).elim

/-- Given [independent centered paired outcome scores with overlap](hyp:h), [a bounded
tilt of absolute value at most 1/4](hyp:hτ), [cell scores of absolute value at most
one](hyp:hu), and [an outcome amplitude](hyp:γ) γ, [the mean of the product of the two
posterior outcome likelihoods equals 1 + Σ over d = 1, …, m of γ^(2d) · (order-d subset
energy of the cell) · zᵈ, where m is the number of records and z the common overlap](goal). -/
theorem integral_outcomeLikelihood_pair_by_card {m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {v w : Fin m → Ω → ℝ} {z : ℝ} (h : CenteredOutcomePair ρ v w z)
    {τ : ℝ} (hτ : |τ| ≤ 1 / 4) {c : Cell m} (hu : ∀ i, |c.1 i| ≤ 1) (γ : ℝ) :
    (∫ ω, outcomeLikelihood τ γ c (fun i => v i ω) *
      outcomeLikelihood τ γ c (fun i => w i ω) ∂ρ) =
      1 + ∑ d ∈ Finset.range m, γ ^ (2 * (d + 1)) *
        subsetEnergy τ c (d + 1) * z ^ (d + 1) := by
  -- Import Mathlib.Algebra.BigOperators.Group.Finset.Powerset for
  -- Finset.sum_powerset; group the preceding identity by subset cardinality.
  -- Extend the range to m+1 since selected c ⊆ univ; powersetCard is empty
  -- above selected.card. Split order zero using posterior_empty hτ hu.
  classical
  rw [integral_outcomeLikelihood_pair h τ γ c, Finset.sum_powerset]
  let F : ℕ → ℝ := fun d => γ ^ (2 * d) * subsetEnergy τ c d * z ^ d
  have hg (d : ℕ) : (∑ S ∈ (selected c).powersetCard d,
      γ ^ (2 * S.card) * posterior τ c S ^ 2 * z ^ S.card) = F d := by
    dsimp [F]
    unfold subsetEnergy
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  simp_rw [hg]
  have hc : (selected c).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (selected c))
  have hz (d : ℕ) (hd : (selected c).card < d) : F d = 0 := by
    simp [F, subsetEnergy, Finset.powersetCard_eq_empty.mpr hd]
  have hext : (∑ d ∈ Finset.range ((selected c).card + 1), F d) =
      ∑ d ∈ Finset.range (m + 1), F d := by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hc 1))
    intro d hd hnot
    apply hz
    have hn : ¬ d < (selected c).card + 1 := by
      simpa only [Finset.mem_range] using hnot
    omega
  rw [hext, Finset.sum_range_succ']
  have h0 : F 0 = 1 := by simp [F, subsetEnergy, posterior_empty hτ hu]
  rw [h0]
  dsimp [F]
  ring

end Causalean.Stat.Minimax.Mixture.PoissonLatentSign
