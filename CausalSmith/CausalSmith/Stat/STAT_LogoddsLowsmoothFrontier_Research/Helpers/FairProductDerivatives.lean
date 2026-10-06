module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairMixtureParity
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureProductDerivatives

/-! # Fair component product differentiation

The actual hidden-sign mixture and comparator inherit the component derivative
bound from their one-record smoothness and derivative envelopes. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Product differentiation and finite averaging establish the fair component's
second-derivative estimate from one-record bounds, including the comparator's
substituted root and effect. [the documented result](goal) Under [the stated assumptions](hyp:ht,hd,hM,hs,hder). -/
-- @node: fairComponentDifference_second_derivative_bound
lemma fairComponentDifference_second_derivative_bound {n : ℕ} (k : ℕ)
    (I : Finset (Fin n)) (t : ℝ) (o : Fin n → Record) (d M : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hd : |d| ≤ 1/100) (hM : 1 ≤ M)
    (hs : ∀ (b : Bool) σ i, i ∈ I → ContDiffAt ℝ 2
      (fun z => recordCellDensity
        (if b then fairLaw k σ t z else fairComparator k t z) (o i)) d)
    (hder : ∀ (b : Bool) σ i, i ∈ I → ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
      ‖iteratedFDeriv ℝ m (fun z => recordCellDensity
        (if b then fairLaw k σ t z else fairComparator k t z) (o i)) d‖ ≤ M) :
    |iteratedDeriv 2 (fairComponentDifference k I t o) d| ≤
      2 * M ^ 2 * (I.card : ℝ) ^ 2 * 2 ^ I.card := by
  classical
  let f := fun (b : Bool) (σ : Fin (k+1) → Bool) i z => recordCellDensity
    (if b then fairLaw k σ t z else fairComparator k t z) (o i)
  have hval (b : Bool) (σ : Fin (k+1) → Bool) (i : Fin n) : |f b σ i d| ≤ 2 := by
    have hr := fairDensity_bounds b k σ t d ht hd (o i).2.1 (o i).2.2 (o i).1
    change (1/2 : ℝ) ≤ f b σ i d ∧ f b σ i d ≤ 2 at hr
    rw [abs_of_nonneg (by linarith [hr.1])]
    exact hr.2
  have hfirst (b : Bool) (σ : Fin (k+1) → Bool) (i : Fin n) (hi : i ∈ I) :
      |deriv (f b σ i) d| ≤ M := by
    have h := hder b σ i hi 1 le_rfl (by norm_num)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, Real.norm_eq_abs] at h
    exact h
  have hsecond (b : Bool) (σ : Fin (k+1) → Bool) (i : Fin n) (hi : i ∈ I) :
      |iteratedDeriv 2 (f b σ i) d| ≤ M := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      hder b σ i hi 2 (by norm_num) le_rfl
  have hprod (b : Bool) (σ : Fin (k+1) → Bool) :
      |iteratedDeriv 2 (fun z => ∏ i ∈ I, f b σ i z) d| ≤
        M^2 * (I.card : ℝ)^2 * 2^I.card :=
    (mixture_product_two_derivative_bounds I (f b σ) d M hM (hs b σ)
      (fun i _ => hval b σ i) (hfirst b σ) (hsecond b σ)).2.2
  have h := mixture_average_second_derivative_bound
    (fun σ z => ∏ i ∈ I, f true σ i z)
    (fun z => ∏ i ∈ I, f false (fun _ => false) i z) d _
    (fun σ => contDiffAt_prod (hs true σ))
    (contDiffAt_prod (hs false (fun _ => false)))
    (hprod true) (hprod false (fun _ => false))
  change |iteratedDeriv 2 (fairComponentDifference k I t o) d| ≤
    2 * (M^2 * (I.card : ℝ)^2 * 2^I.card) at h
  simpa only [mul_assoc] using h

/-- [The fair component Hellinger estimate now needs only the one-record analytic
envelopes. Product smoothness, its second derivative, and both Taylor
cancellations are assembled here rather than assumed at component level. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hM,hs,hder). -/
-- @node: fair_component_hellinger_of_record_derivatives
lemma fair_component_hellinger_of_record_derivatives {n : ℕ} (k : ℕ)
    (I : Finset (Fin n)) (t : ℝ) (o : Fin n → Record) (δ M : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100) (hM : 1 ≤ M)
    (hs : ∀ (b : Bool) σ i, i ∈ I → ∀ z ∈ Set.Icc 0 |δ|, ContDiffAt ℝ 2
      (fun w => recordCellDensity
        (if b then fairLaw k σ t w else fairComparator k t w) (o i)) z)
    (hder : ∀ (b : Bool) σ i, i ∈ I → ∀ z ∈ Set.Icc 0 |δ|,
      ∀ m : ℕ, 1 ≤ m → m ≤ 2 →
        ‖iteratedFDeriv ℝ m (fun w => recordCellDensity
          (if b then fairLaw k σ t w else fairComparator k t w) (o i)) z‖ ≤ M) :
    (Real.sqrt ((Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ *
        ∑ σ, ∏ i ∈ I, recordCellDensity (fairLaw k σ t δ) (o i)) -
      Real.sqrt (∏ i ∈ I, recordCellDensity (fairComparator k t δ) (o i)))^2 ≤
        M^4 * (I.card : ℝ)^4 * 8^I.card * δ^4 := by
  classical
  have hsDiff (z : ℝ) (hz : z ∈ Set.Icc 0 |δ|) :
      ContDiffAt ℝ 2 (fairComponentDifference k I t o) z := by
    unfold fairComponentDifference
    apply ContDiffAt.sub
    · apply ContDiffAt.mul contDiffAt_const
      apply ContDiffAt.sum
      intro σ _
      exact contDiffAt_prod (fun i hi => by simpa using hs true σ i hi z hz)
    · exact contDiffAt_prod (fun i hi => by
        simpa using hs false (fun _ => false) i hi z hz)
  apply fair_component_hellinger_taylor_bound k I t o δ M ht hδ
    ((hsDiff 0 ⟨le_rfl, abs_nonneg δ⟩).differentiableAt (by norm_num))
    (fun z hz => (hsDiff z hz).contDiffWithinAt)
  intro z hz
  have hz' : z ∈ Set.Icc 0 |δ| := ⟨hz.1.le, hz.2.le⟩
  have hzsmall : |z| ≤ 1/100 := by
    rw [abs_of_nonneg hz'.1]
    exact hz'.2.trans hδ
  exact fairComponentDifference_second_derivative_bound k I t o z M ht hzsmall hM
    (fun b σ i hi => hs b σ i hi z hz')
    (fun b σ i hi => hder b σ i hi z hz')

end CausalSmith.Stat.LogoddsLowsmoothFrontier
