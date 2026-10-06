module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.Membership
public import Causalean.Stat.Minimax.Mixture.PoissonLatentSign

/-!
Exact cell-sign posterior and its treated-outcome subset likelihood expansion against the null
propensity mixture.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Likelihood of a cell treatment assignment for a fixed sign. -/
def cellSignLikelihood {M : ℕ} (tau : ℝ) (u : Fin M → ℝ) (a : Fin M → Bool)
    (lambda : Bool) : ℝ :=
  ∏ i : Fin M, (1 + tau * signValue lambda * u i * signValue (a i))
/-- Posterior coefficient for one treated subset, retaining the exact signed term. -/
def cellPosteriorCoefficient {M : ℕ} (tau : ℝ) (u : Fin M → ℝ)
    (a : Fin M → Bool) (S : Finset (Fin M)) : ℝ :=
  ((∑ lambda : Bool, cellSignLikelihood tau u a lambda * 
    ∏ i ∈ S, signValue lambda * u i / (1 + tau * signValue lambda * u i)) / 
    (∑ lambda : Bool, cellSignLikelihood tau u a lambda))
/-- Exact finite treated-subset expansion of the cell alternative likelihood ratio. -/
def cellAlternativeRatio {M : ℕ} (tau gamma : ℝ) (u : Fin M → ℝ)
    (a : Fin M → Bool) (v : Fin M → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter (fun i => a i = true)).powerset,
    gamma ^ S.card * cellPosteriorCoefficient tau u a S * ∏ i ∈ S, v i
/-- In a singleton treated cell, the own-record propensity factor cancels exactly. -/
-- @node: singleton_posterior_cancellation
lemma singleton_posterior_cancellation (tau : ℝ) (ht : |tau| ≤ 1 / 4)
    (u : Fin 1 → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    cellPosteriorCoefficient tau u (fun _ => true) {0} = 0 := by
  have hb : |tau * u 0| ≤ 1 / 4 := by
    rw [abs_mul]
    calc
      |tau| * |u 0| ≤ (1 / 4 : ℝ) * 1 := mul_le_mul ht (hu 0) (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  have hp : 1 + tau * u 0 ≠ 0 := by
    have := (abs_le.mp hb).1
    linarith
  have hm : 1 - tau * u 0 ≠ 0 := by
    have := (abs_le.mp hb).2
    linarith
  simp [cellPosteriorCoefficient, cellSignLikelihood, signValue, ← sub_eq_add_neg]
  field_simp [hp, hm]
  ring

/-- The paper posterior is the reusable latent-sign posterior, with all treated
records selected and with one shared sign for the complete cell. -/
-- @node: cellPosteriorCoefficient_eq_posterior
lemma cellPosteriorCoefficient_eq_posterior {M : ℕ} (tau : ℝ)
    (u : Fin M → ℝ) (a : Fin M → Bool) (S : Finset (Fin M)) :
    cellPosteriorCoefficient tau u a S =
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.posterior tau (u, a, a) S := by
  simp only [cellPosteriorCoefficient, cellSignLikelihood, Fintype.sum_bool,
    signValue, Causalean.Stat.Minimax.Mixture.PoissonLatentSign.posterior,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.signLikelihood,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.denominator,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.sign,
    Bool.false_eq_true, ite_true, ite_false, one_mul, mul_one, mul_neg_one, neg_mul,
    ← sub_eq_add_neg]

/-- Every posterior subset obeys the geometric bound used in (37). -/
-- @node: cellPosteriorCoefficient_abs_le
lemma cellPosteriorCoefficient_abs_le {M : ℕ} (tau : ℝ)
    (ht : |tau| ≤ 1 / 4) (u : Fin M → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (a : Fin M → Bool) (S : Finset (Fin M)) :
    |cellPosteriorCoefficient tau u a S| ≤ (2 : ℝ) ^ S.card := by
  rw [cellPosteriorCoefficient_eq_posterior]
  exact Causalean.Stat.Minimax.Mixture.PoissonLatentSign.posterior_subset_bound ht hu S

/-- A treated singleton retains the collision factor M-1 from (35); the assignment
hypothesis is essential because only treated records cancel their own factor. -/
-- @node: cellPosteriorCoefficient_singleton_bound
lemma cellPosteriorCoefficient_singleton_bound {M : ℕ} (tau : ℝ)
    (ht : |tau| ≤ 1 / 4) (u : Fin M → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (a : Fin M → Bool) (i : Fin M) (hi : a i = true) :
    |cellPosteriorCoefficient tau u a {i}| ≤
      |tau| * ((M - 1 : ℕ) : ℝ) * (5 / 3 : ℝ) ^ M := by
  rw [cellPosteriorCoefficient_eq_posterior]
  apply Causalean.Stat.Minimax.Mixture.PoissonLatentSign.posterior_singleton_bound ht hu
  simpa [Causalean.Stat.Minimax.Mixture.PoissonLatentSign.active] using hi

/-- The expansion of the observable treated-cell ratio is exactly the reusable
posterior outcome likelihood, with positive assignment signs selected. -/
-- @node: cellAlternativeRatio_eq_outcomeLikelihood
lemma cellAlternativeRatio_eq_outcomeLikelihood {M : ℕ} (tau gamma : ℝ)
    (u : Fin M → ℝ) (a : Fin M → Bool) (v : Fin M → ℝ) :
    cellAlternativeRatio tau gamma u a v =
      Causalean.Stat.Minimax.Mixture.PoissonLatentSign.outcomeLikelihood
        tau gamma (u, a, a) v := by
  rw [Causalean.Stat.Minimax.Mixture.PoissonLatentSign.outcomeLikelihood_expansion]
  simp only [cellAlternativeRatio, cellPosteriorCoefficient_eq_posterior,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.selected]

/-- The posterior retains the constant term one, including empty cells. -/
-- @node: cellPosteriorCoefficient_empty
lemma cellPosteriorCoefficient_empty {M : ℕ} (tau : ℝ)
    (ht : |tau| ≤ 1 / 4) (u : Fin M → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (a : Fin M → Bool) : cellPosteriorCoefficient tau u a ∅ = 1 := by
  rw [cellPosteriorCoefficient_eq_posterior]
  exact Causalean.Stat.Minimax.Mixture.PoissonLatentSign.posterior_empty ht hu

/-- Multiplying the treated outcome factors and then mixing the common cell sign
recovers precisely the subset expansion (30). -/
-- @node: cellAlternativeRatio_eq_weighted_product
lemma cellAlternativeRatio_eq_weighted_product {M : ℕ} (tau gamma : ℝ)
    (u : Fin M → ℝ) (a : Fin M → Bool) (v : Fin M → ℝ) :
    cellAlternativeRatio tau gamma u a v =
      ((cellSignLikelihood tau u a true *
          ∏ i ∈ Finset.univ.filter (fun i => a i = true),
            (1 + gamma * (u i / (1 + tau * u i)) * v i)) +
       (cellSignLikelihood tau u a false *
          ∏ i ∈ Finset.univ.filter (fun i => a i = true),
            (1 + gamma * ((-u i) / (1 - tau * u i)) * v i))) /
        (cellSignLikelihood tau u a true + cellSignLikelihood tau u a false) := by
  rw [cellAlternativeRatio_eq_outcomeLikelihood]
  simp only [Causalean.Stat.Minimax.Mixture.PoissonLatentSign.outcomeLikelihood,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.signLikelihood,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.selected,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.denominator,
    Causalean.Stat.Minimax.Mixture.PoissonLatentSign.sign,
    cellSignLikelihood, signValue, Bool.false_eq_true, ite_true, ite_false,
    mul_one, mul_neg_one, neg_mul, ← sub_eq_add_neg]

/-- Conditional outcome integration keeps only matching subsets, as in (31).
The centering and independence contract is a conditional outcome fact; this result
does not identify the paper's observation-law density against its null mixture. -/
-- @node: cellAlternativeRatio_crossMoment
lemma cellAlternativeRatio_crossMoment {M : ℕ} {E : Type*} [MeasurableSpace E]
    (rho : Measure E) [IsProbabilityMeasure rho] (tau gamma : ℝ)
    (ht : |tau| ≤ 1 / 4) (u : Fin M → ℝ) (hu : ∀ i, |u i| ≤ 1)
    (a : Fin M → Bool) (v w : Fin M → E → ℝ) (z : ℝ)
    (h : Causalean.Stat.Minimax.Mixture.PoissonLatentSign.CenteredOutcomePair
      rho v w z) :
    (∫ o, cellAlternativeRatio tau gamma u a (fun i => v i o) *
      cellAlternativeRatio tau gamma u a (fun i => w i o) ∂rho) =
      1 + ∑ d ∈ Finset.range M, gamma ^ (2 * (d + 1)) *
        (∑ S ∈ (Finset.univ.filter (fun i => a i = true)).powersetCard (d + 1),
          cellPosteriorCoefficient tau u a S ^ 2) * z ^ (d + 1) := by
  simp_rw [cellAlternativeRatio_eq_outcomeLikelihood, cellPosteriorCoefficient_eq_posterior]
  exact Causalean.Stat.Minimax.Mixture.PoissonLatentSign.integral_outcomeLikelihood_pair_by_card
    h ht hu gamma

end CausalSmith.Stat.DensityEffectRoughNull
