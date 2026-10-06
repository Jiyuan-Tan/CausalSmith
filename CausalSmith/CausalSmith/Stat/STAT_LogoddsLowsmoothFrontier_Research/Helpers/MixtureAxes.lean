module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Calibration

/-! # Exact zero-amplitude identities for the original-record experiments

On the propensity axis the two mixed laws coincide draw by draw. On the
prognosis axis reversal of all endpoint signs reindexes the complete finite
prior. At zero fair amplitude every draw is the deterministic comparator.
These are identities of the actual sample measures, including totalization.
-/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Reversing every endpoint sign negates the entire shared-endpoint field.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: signFieldZ_reverse
lemma signFieldZ_reverse (k : ℕ) (σ : Fin (k + 1) → Bool) (x : Covariate) :
    signFieldZ k (fun i => !(σ i)) x = -signFieldZ k σ x := by
  have hs (b : Bool) : signValue (!b) = -signValue b := by
    cases b <;> norm_num [signValue]
  simp only [signFieldZ, endpointSign, hs]
  ring

/-- The covariance is exactly zero at zero effect, for any margins. [the stated conclusion](goal) holds. -/
-- @node: covarianceBranch_zero_effect
lemma covarianceBranch_zero_effect (ξ υ : ℝ) : covarianceBranch 0 ξ υ = 0 := by
  simp [covarianceBranch]

/-- Zero propensity amplitude makes the two mixed tables identical. [the stated conclusion](goal) holds. -/
-- @node: mixedCells_zero_left
lemma mixedCells_zero_left (k : ℕ) (σ : Fin (k + 1) → Bool) (ζ : ℝ) :
    mixedCells false k σ 0 ζ = mixedCells true k σ 0 ζ := by
  funext a y x
  simp [mixedCells, covarianceBranch_zero_effect]

/-- Zero prognosis amplitude turns sign reversal into a draw-wise table identity. [the stated conclusion](goal) holds. -/
-- @node: mixedCells_zero_right_reverse
lemma mixedCells_zero_right_reverse (k : ℕ) (σ : Fin (k + 1) → Bool) (η : ℝ) :
    mixedCells false k σ η 0 = mixedCells true k (fun i => !(σ i)) η 0 := by
  funext a y x
  simp [mixedCells, signFieldZ_reverse, covarianceBranch_zero_effect]

/-- The actual mixed sample measures agree on the zero propensity axis. [the stated conclusion](goal) holds. -/
-- @node: mixedMixture_zero_left
lemma mixedMixture_zero_left (n k : ℕ) (ζ : ℝ) :
    mixedMixture false n k 0 ζ = mixedMixture true n k 0 ζ := by
  unfold mixedMixture finiteSignMixture
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  dsimp only
  simp only [mixedLaw, mixedCells_zero_left]

/-- The uniform finite sign prior is invariant under simultaneous reversal. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:F). -/
-- @node: endpointSign_prior_reverse
lemma endpointSign_prior_reverse {A : Type*} [AddCommMonoid A] (k : ℕ)
    (F : (Fin (k + 1) → Bool) → A) :
    (∑ σ : Fin (k + 1) → Bool, F (fun i => !(σ i))) = ∑ σ, F σ := by
  apply Fintype.sum_bijective (fun σ : Fin (k + 1) → Bool => fun i => !(σ i))
  · constructor
    · intro σ τ h
      funext i
      have hi := congrFun h i
      cases hσ : σ i <;> cases hτ : τ i <;> simp_all
    · intro σ
      refine ⟨fun i => !(σ i), ?_⟩
      funext i
      simp
  · intro σ
    rfl

/-- The actual mixed sample measures agree on the zero prognosis axis after
reindexing the prior, without revealing any latent signs. [the documented result](goal) -/
-- @node: mixedMixture_zero_right
lemma mixedMixture_zero_right (n k : ℕ) (η : ℝ) :
    mixedMixture false n k η 0 = mixedMixture true n k η 0 := by
  unfold mixedMixture finiteSignMixture
  congr 1
  calc
    _ = ∑ σ : Fin (k + 1) → Bool,
        Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
          (mixedLaw true k (fun i => !(σ i)) η 0).measure n := by
      apply Finset.sum_congr rfl
      intro σ _
      dsimp only
      simp only [mixedLaw, mixedCells_zero_right_reverse]
    _ = _ := endpointSign_prior_reverse k (fun σ =>
      Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (mixedLaw true k σ η 0).measure n)

/-- At zero amplitude the comparator effect is the original effect. [the stated conclusion](goal) holds. -/
lemma comparatorEffect_zero_amplitude (t : ℝ) : comparatorEffect t 0 = t := by
  simp [comparatorEffect]

/-- Every zero-amplitude fair draw equals the comparator's table, regardless
of which value the common root selector returns. [the documented result](goal) -/
-- @node: fairCells_zero_amplitude
lemma fairCells_zero_amplitude (k : ℕ) (σ : Fin (k + 1) → Bool) (t : ℝ) :
    fairCells true k σ t 0 = fairCells false k (fun _ => false) t 0 := by
  funext a y x
  simp [fairCells, comparatorEffect_zero_amplitude]

/-- A uniform sign mixture of one common law is exactly that law's iid experiment. [the stated conclusion](goal) holds. -/
-- @node: finiteSignMixture_const
lemma finiteSignMixture_const (n k : ℕ) (P : ObservedLaw) :
    finiteSignMixture n k (fun _ => P) =
      Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n := by
  unfold finiteSignMixture
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  rw [zpow_neg, zpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, Nat.cast_pow, Nat.cast_ofNat, smul_smul]
  rw [ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_smul]

/-- At zero fair amplitude the entire original-record experiment equals its
comparator, including the normalization of the finite prior. [the documented result](goal) -/
-- @node: fairMixture_zero_amplitude
lemma fairMixture_zero_amplitude (n k : ℕ) (t : ℝ) :
    fairMixture n k t 0 =
      Causalean.Stat.UStatistic.LocalizedVariance.iidLaw (fairComparator k t 0).measure n := by
  have hdraw (σ : Fin (k + 1) → Bool) : fairLaw k σ t 0 = fairComparator k t 0 := by
    simp only [fairLaw, fairComparator, fairCells_zero_amplitude]
  simp only [fairMixture, hdraw]
  exact finiteSignMixture_const n k _

end CausalSmith.Stat.LogoddsLowsmoothFrontier
