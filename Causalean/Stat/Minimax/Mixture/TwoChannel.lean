module
public import Causalean.Stat.Minimax.Mixture.Iid
public import Causalean.Stat.Minimax.Mixture.SignOverlap

/-! # Two-channel iid sign mixtures

This module turns explicit likelihoods and one-observation overlap identities
into iid and independent two-channel overlaps.  Its uniform-mixture result
feeds the finite-sign Gaussian moment bound without application-specific constants.
-/
public section
namespace Causalean.Stat.Minimax.Mixture.TwoChannel
open Causalean.Stat.Minimax.Mixture
open Causalean.Stat.Minimax.Mixture.SignOverlap
open MeasureTheory
open scoped BigOperators ENNReal
/-- Given [a measurable sample space](hyp:Ω), [a reference probability law](hyp:μ),
[an alternative probability law](hyp:Q), [a likelihood](hyp:L), [its measurability
and nonnegativity](hyp:hL,hL0), and [its likelihood representation](hyp:hQ),
[the likelihood integrates to one under the reference law](goal). -/
theorem integral_likelihood_eq_one {Ω : Type*} [MeasurableSpace Ω] (μ Q : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] (L : Ω → ℝ) (hL : Measurable L) (hL0 : ∀ x, 0 ≤ L x) (hQ : Q = μ.withDensity (fun x =>
    ENNReal.ofReal (L x))) : ∫ x, L x ∂μ = 1 := by
  have hLeq : (fun x => (Q.rnDeriv μ x).toReal) =ᵐ[μ] L := by
    rw [hQ]
    filter_upwards [Measure.rnDeriv_withDensity μ hL.ennreal_ofReal] with x hx
    simp [hx, ENNReal.toReal_ofReal (hL0 x)]
  have hac : Q ≪ μ := by
    rw [hQ]
    exact withDensity_absolutelyContinuous μ _
  calc
    ∫ x, L x ∂μ = ∫ x, (Q.rnDeriv μ x).toReal ∂μ :=
      integral_congr_ae hLeq.symm
    _ = 1 := by simpa using (Measure.integral_toReal_rnDeriv hac)
/-- Given [a measurable sample space](hyp:Ω), [a reference probability law and
two alternative probability laws](hyp:μ,Q,R), [two likelihoods](hyp:L,M),
[their measurability](hyp:hL,hM), [their nonnegativity](hyp:hL0,hM0),
[their likelihood representations](hyp:hQ,hR), [an integrable one-observation
likelihood product](hyp:hpairInt), and [a sample size](hyp:n), [the iid pair
overlap is the corresponding power of the one-observation overlap](goal). -/
theorem iid_pair_overlap_of_likelihood {Ω : Type*} [MeasurableSpace Ω] (μ Q R : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (L M : Ω → ℝ) (hL : Measurable L) (hM : Measurable M) (hL0 : ∀ x,
    0 ≤ L x) (hM0 : ∀ x, 0 ≤ M x) (hQ : Q = μ.withDensity (fun x => ENNReal.ofReal (L x))) (hR : R = μ.withDensity (fun
    x => ENNReal.ofReal (M x))) (hpairInt : Integrable (fun x => L x * M x) μ) (n : ℕ) : (∫ x, (((Measure.pi (fun _ :
    Fin n => Q)).rnDeriv (Measure.pi (fun _ : Fin n => μ)) x).toReal) * (((Measure.pi (fun _ : Fin n => R)).rnDeriv
    (Measure.pi (fun _ : Fin n => μ)) x).toReal) ∂(Measure.pi (fun _ : Fin n => μ))) = (∫ x, L x * M x ∂μ) ^ n := by
  have hLeq : (fun x => (Q.rnDeriv μ x).toReal) =ᵐ[μ] L := by
    rw [hQ]
    filter_upwards [Measure.rnDeriv_withDensity μ hL.ennreal_ofReal] with x hx
    simp [hx, ENNReal.toReal_ofReal (hL0 x)]
  have hMeq : (fun x => (R.rnDeriv μ x).toReal) =ᵐ[μ] M := by
    rw [hR]
    filter_upwards [Measure.rnDeriv_withDensity μ hM.ennreal_ofReal] with x hx
    simp [hx, ENNReal.toReal_ofReal (hM0 x)]
  have hprod : (fun x => (Q.rnDeriv μ x).toReal *
      (R.rnDeriv μ x).toReal) =ᵐ[μ] (fun x => L x * M x) := by
    filter_upwards [hLeq, hMeq] with x hx hy
    simp [hx, hy]
  have hacQ : Q ≪ μ := by
    rw [hQ]
    exact withDensity_absolutelyContinuous μ _
  have hacR : R ≪ μ := by
    rw [hR]
    exact withDensity_absolutelyContinuous μ _
  have hint : Integrable (fun x => (Q.rnDeriv μ x).toReal *
      (R.rnDeriv μ x).toReal) μ := hpairInt.congr hprod.symm
  rw [Causalean.Stat.Minimax.Mixture.iidPairOverlap μ Q R hacQ hacR hint n]
  congr 1
  exact integral_congr_ae hprod
/-- Given [two measurable sample spaces](hyp:Ω₁,Ω₂), [two reference laws](hyp:μ₁,μ₂),
[two pairs of alternative laws](hyp:Q₁,R₁,Q₂,R₂), [two pairs of likelihoods](hyp:L₁,M₁,L₂,M₂),
[their measurability](hyp:hL₁,hM₁,hL₂,hM₂), [their nonnegativity](hyp:hL₁0,hM₁0,hL₂0,hM₂0),
[their likelihood representations](hyp:hQ₁,hR₁,hQ₂,hR₂), [integrable one-observation
likelihood products](hyp:hInt₁,hInt₂), and [two sample sizes](hyp:n₁,n₂),
[the independent iid pair overlap is the product of the two channel powers](goal). -/
theorem two_channel_pair_overlap {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (μ₁ : Measure Ω₁) (μ₂ :
    Measure Ω₂) (Q₁ R₁ : Measure Ω₁) (Q₂ R₂ : Measure Ω₂) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure Q₁] [IsProbabilityMeasure R₁] [IsProbabilityMeasure Q₂] [IsProbabilityMeasure R₂] (L₁ M₁ : Ω₁
    → ℝ) (L₂ M₂ : Ω₂ → ℝ) (hL₁ : Measurable L₁) (hM₁ : Measurable M₁) (hL₂ : Measurable L₂) (hM₂ : Measurable M₂) (hL₁0
    : ∀ x, 0 ≤ L₁ x) (hM₁0 : ∀ x, 0 ≤ M₁ x) (hL₂0 : ∀ x, 0 ≤ L₂ x) (hM₂0 : ∀ x, 0 ≤ M₂ x) (hQ₁ : Q₁ = μ₁.withDensity
    (fun x => ENNReal.ofReal (L₁ x))) (hR₁ : R₁ = μ₁.withDensity (fun x => ENNReal.ofReal (M₁ x))) (hQ₂ : Q₂ =
    μ₂.withDensity (fun x => ENNReal.ofReal (L₂ x))) (hR₂ : R₂ = μ₂.withDensity (fun x => ENNReal.ofReal (M₂ x))) (hInt₁
    : Integrable (fun x => L₁ x * M₁ x) μ₁) (hInt₂ : Integrable (fun x => L₂ x * M₂ x) μ₂) (n₁ n₂ : ℕ) : (∫ x,
    ((((Measure.pi (fun _ : Fin n₁ => Q₁)).prod (Measure.pi (fun _ : Fin n₂ => Q₂))).rnDeriv ((Measure.pi (fun _ : Fin
    n₁ => μ₁)).prod (Measure.pi (fun _ : Fin n₂ => μ₂))) x).toReal) * ((((Measure.pi (fun _ : Fin n₁ => R₁)).prod
    (Measure.pi (fun _ : Fin n₂ => R₂))).rnDeriv ((Measure.pi (fun _ : Fin n₁ => μ₁)).prod (Measure.pi (fun _ : Fin n₂
    => μ₂))) x).toReal) ∂((Measure.pi (fun _ : Fin n₁ => μ₁)).prod (Measure.pi (fun _ : Fin n₂ => μ₂)))) = (∫ x, L₁ x *
    M₁ x ∂μ₁) ^ n₁ * (∫ x, L₂ x * M₂ x ∂μ₂) ^ n₂ := by
  have hQ₁' := iid_absolutelyContinuous_of_likelihood μ₁ Q₁ L₁ hQ₁ n₁
  have hR₁' := iid_absolutelyContinuous_of_likelihood μ₁ R₁ M₁ hR₁ n₁
  have hQ₂' := iid_absolutelyContinuous_of_likelihood μ₂ Q₂ L₂ hQ₂ n₂
  have hR₂' := iid_absolutelyContinuous_of_likelihood μ₂ R₂ M₂ hR₂ n₂
  have hInt₁' := iid_pair_integrable_of_likelihood μ₁ Q₁ R₁ L₁ M₁
    hL₁ hM₁ hL₁0 hM₁0 hQ₁ hR₁ hInt₁ n₁
  have hInt₂' := iid_pair_integrable_of_likelihood μ₂ Q₂ R₂ L₂ M₂
    hL₂ hM₂ hL₂0 hM₂0 hQ₂ hR₂ hInt₂ n₂
  rw [product_pair_overlap
    (Measure.pi (fun _ : Fin n₁ => μ₁))
    (Measure.pi (fun _ : Fin n₁ => Q₁))
    (Measure.pi (fun _ : Fin n₁ => R₁))
    (Measure.pi (fun _ : Fin n₂ => μ₂))
    (Measure.pi (fun _ : Fin n₂ => Q₂))
    (Measure.pi (fun _ : Fin n₂ => R₂))
    hQ₁' hR₁' hQ₂' hR₂' hInt₁' hInt₂',
    iid_pair_overlap_of_likelihood μ₁ Q₁ R₁ L₁ M₁
      hL₁ hM₁ hL₁0 hM₁0 hQ₁ hR₁ hInt₁ n₁,
    iid_pair_overlap_of_likelihood μ₂ Q₂ R₂ L₂ M₂
      hL₂ hM₂ hL₂0 hM₂0 hQ₂ hR₂ hInt₂ n₂]
/-- Given [a positive sign-vector length and two sample sizes](hyp:K,n₁,n₂),
[two measurable sample spaces](hyp:Ω₁,Ω₂), [two reference laws](hyp:μ₁,μ₂),
[two sign-indexed families of probability laws](hyp:Q₁,Q₂), [two likelihood
families](hyp:L₁,L₂), [their measurability](hyp:hL₁,hL₂), [their nonnegativity](hyp:hL₁0,hL₂0),
[their likelihood representations](hyp:hQ₁,hQ₂), [integrable pair products](hyp:hInt₁,hInt₂),
[two overlap coefficients](hyp:ρ₁,ρ₂), and [their pairwise overlap identities](hyp:hPair₁,hPair₂),
[one plus the chi-squared divergence of the uniform two-channel iid mixture is
the uniform double average of its sign-overlap factors](goal). -/
theorem one_add_chiSqDiv_uniformMixture_twoChannel_sign {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (K n₁
    n₂ : ℕ) [NeZero K] (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (Q₁ : (Fin K → Bool) → Measure Ω₁) (Q₂ : (Fin K → Bool) →
    Measure Ω₂) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [∀ s, IsProbabilityMeasure (Q₁ s)] [∀ s,
    IsProbabilityMeasure (Q₂ s)] (L₁ : (Fin K → Bool) → Ω₁ → ℝ) (L₂ : (Fin K → Bool) → Ω₂ → ℝ) (hL₁ : ∀ s, Measurable
    (L₁ s)) (hL₂ : ∀ s, Measurable (L₂ s)) (hL₁0 : ∀ s x, 0 ≤ L₁ s x) (hL₂0 : ∀ s x, 0 ≤ L₂ s x) (hQ₁ : ∀ s, Q₁ s =
    μ₁.withDensity (fun x => ENNReal.ofReal (L₁ s x))) (hQ₂ : ∀ s, Q₂ s = μ₂.withDensity (fun x => ENNReal.ofReal (L₂ s
    x))) (hInt₁ : ∀ s t, Integrable (fun x => L₁ s x * L₁ t x) μ₁) (hInt₂ : ∀ s t, Integrable (fun x => L₂ s x * L₂ t x)
    μ₂) (ρ₁ ρ₂ : ℝ) (hPair₁ : ∀ s t, (∫ x, L₁ s x * L₁ t x ∂μ₁) = 1 + ρ₁ * innerSign s t / (K : ℝ)) (hPair₂ : ∀ s t, (∫
    x, L₂ s x * L₂ t x ∂μ₂) = 1 + ρ₂ * innerSign s t / (K : ℝ)) : 1 + Causalean.Stat.chiSqDiv
    (Causalean.Stat.Minimax.Mixture.uniformMixture (fun s => (Measure.pi (fun _ : Fin n₁ => Q₁ s)).prod (Measure.pi (fun
    _ : Fin n₂ => Q₂ s)))) ((Measure.pi (fun _ : Fin n₁ => μ₁)).prod (Measure.pi (fun _ : Fin n₂ => μ₂))) = (∑ s : Fin K
    → Bool, ∑ t : Fin K → Bool, (1 + ρ₁ * innerSign s t / (K : ℝ)) ^ n₁ * (1 + ρ₂ * innerSign s t / (K : ℝ)) ^ n₂) /
    (Fintype.card (Fin K → Bool) : ℝ) ^ 2 := by
  classical
  have hac (s : Fin K → Bool) :
      (Measure.pi (fun _ : Fin n₁ => Q₁ s)).prod
        (Measure.pi (fun _ : Fin n₂ => Q₂ s)) ≪
      (Measure.pi (fun _ : Fin n₁ => μ₁)).prod
        (Measure.pi (fun _ : Fin n₂ => μ₂)) :=
    (iid_absolutelyContinuous_of_likelihood μ₁ (Q₁ s) (L₁ s) (hQ₁ s) n₁).prod
      (iid_absolutelyContinuous_of_likelihood μ₂ (Q₂ s) (L₂ s) (hQ₂ s) n₂)
  have hpair (s t : Fin K → Bool) : Integrable
      (fun x =>
        (((Measure.pi (fun _ : Fin n₁ => Q₁ s)).prod
          (Measure.pi (fun _ : Fin n₂ => Q₂ s))).rnDeriv
          ((Measure.pi (fun _ : Fin n₁ => μ₁)).prod
            (Measure.pi (fun _ : Fin n₂ => μ₂))) x).toReal *
        (((Measure.pi (fun _ : Fin n₁ => Q₁ t)).prod
          (Measure.pi (fun _ : Fin n₂ => Q₂ t))).rnDeriv
          ((Measure.pi (fun _ : Fin n₁ => μ₁)).prod
            (Measure.pi (fun _ : Fin n₂ => μ₂))) x).toReal)
      ((Measure.pi (fun _ : Fin n₁ => μ₁)).prod
        (Measure.pi (fun _ : Fin n₂ => μ₂))) := by
    exact product_pair_integrable
      (Measure.pi (fun _ : Fin n₁ => μ₁))
      (Measure.pi (fun _ : Fin n₁ => Q₁ s))
      (Measure.pi (fun _ : Fin n₁ => Q₁ t))
      (Measure.pi (fun _ : Fin n₂ => μ₂))
      (Measure.pi (fun _ : Fin n₂ => Q₂ s))
      (Measure.pi (fun _ : Fin n₂ => Q₂ t))
      (iid_absolutelyContinuous_of_likelihood μ₁ (Q₁ s) (L₁ s) (hQ₁ s) n₁)
      (iid_absolutelyContinuous_of_likelihood μ₁ (Q₁ t) (L₁ t) (hQ₁ t) n₁)
      (iid_absolutelyContinuous_of_likelihood μ₂ (Q₂ s) (L₂ s) (hQ₂ s) n₂)
      (iid_absolutelyContinuous_of_likelihood μ₂ (Q₂ t) (L₂ t) (hQ₂ t) n₂)
      (iid_pair_integrable_of_likelihood μ₁ (Q₁ s) (Q₁ t) (L₁ s) (L₁ t)
        (hL₁ s) (hL₁ t) (hL₁0 s) (hL₁0 t) (hQ₁ s) (hQ₁ t) (hInt₁ s t) n₁)
      (iid_pair_integrable_of_likelihood μ₂ (Q₂ s) (Q₂ t) (L₂ s) (L₂ t)
        (hL₂ s) (hL₂ t) (hL₂0 s) (hL₂0 t) (hQ₂ s) (hQ₂ t) (hInt₂ s t) n₂)
  rw [Causalean.Stat.Minimax.Mixture.one_add_chiSqDiv_uniformMixture
    (fun s => (Measure.pi (fun _ : Fin n₁ => Q₁ s)).prod
      (Measure.pi (fun _ : Fin n₂ => Q₂ s)))
    ((Measure.pi (fun _ : Fin n₁ => μ₁)).prod
      (Measure.pi (fun _ : Fin n₂ => μ₂))) hac hpair]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [two_channel_pair_overlap μ₁ μ₂ (Q₁ s) (Q₁ t) (Q₂ s) (Q₂ t)
    (L₁ s) (L₁ t) (L₂ s) (L₂ t)
    (hL₁ s) (hL₁ t) (hL₂ s) (hL₂ t)
    (hL₁0 s) (hL₁0 t) (hL₂0 s) (hL₂0 t)
    (hQ₁ s) (hQ₁ t) (hQ₂ s) (hQ₂ t)
    (hInt₁ s t) (hInt₂ s t) n₁ n₂,
    hPair₁ s t, hPair₂ s t]
/-- Given [a positive sign-vector length and two sample sizes](hyp:K,n₁,n₂),
[two measurable sample spaces](hyp:Ω₁,Ω₂), [two reference laws](hyp:μ₁,μ₂),
[two sign-indexed families of probability laws](hyp:Q₁,Q₂), [two likelihood
families](hyp:L₁,L₂), [their measurability](hyp:hL₁,hL₂), [their nonnegativity](hyp:hL₁0,hL₂0),
[their likelihood representations](hyp:hQ₁,hQ₂), [integrable pair products](hyp:hInt₁,hInt₂),
[two overlap coefficients](hyp:ρ₁,ρ₂), and [their pairwise overlap identities](hyp:hPair₁,hPair₂),
[one plus the chi-squared divergence of the uniform two-channel iid mixture is
bounded by the corresponding Gaussian exponential moment](goal). -/
theorem one_add_chiSqDiv_uniformMixture_twoChannel_sign_le_exp {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (K n₁ n₂ : ℕ) [NeZero K] (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (Q₁ : (Fin K → Bool) → Measure Ω₁) (Q₂ : (Fin K → Bool)
    → Measure Ω₂) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [∀ s, IsProbabilityMeasure (Q₁ s)] [∀ s,
    IsProbabilityMeasure (Q₂ s)] (L₁ : (Fin K → Bool) → Ω₁ → ℝ) (L₂ : (Fin K → Bool) → Ω₂ → ℝ) (hL₁ : ∀ s, Measurable
    (L₁ s)) (hL₂ : ∀ s, Measurable (L₂ s)) (hL₁0 : ∀ s x, 0 ≤ L₁ s x) (hL₂0 : ∀ s x, 0 ≤ L₂ s x) (hQ₁ : ∀ s, Q₁ s =
    μ₁.withDensity (fun x => ENNReal.ofReal (L₁ s x))) (hQ₂ : ∀ s, Q₂ s = μ₂.withDensity (fun x => ENNReal.ofReal (L₂ s
    x))) (hInt₁ : ∀ s t, Integrable (fun x => L₁ s x * L₁ t x) μ₁) (hInt₂ : ∀ s t, Integrable (fun x => L₂ s x * L₂ t x)
    μ₂) (ρ₁ ρ₂ : ℝ) (hPair₁ : ∀ s t, (∫ x, L₁ s x * L₁ t x ∂μ₁) = 1 + ρ₁ * innerSign s t / (K : ℝ)) (hPair₂ : ∀ s t, (∫
    x, L₂ s x * L₂ t x ∂μ₂) = 1 + ρ₂ * innerSign s t / (K : ℝ)) : 1 + Causalean.Stat.chiSqDiv
    (Causalean.Stat.Minimax.Mixture.uniformMixture (fun s => (Measure.pi (fun _ : Fin n₁ => Q₁ s)).prod (Measure.pi (fun
    _ : Fin n₂ => Q₂ s)))) ((Measure.pi (fun _ : Fin n₁ => μ₁)).prod (Measure.pi (fun _ : Fin n₂ => μ₂))) ≤ Real.exp
    (((n₁ : ℝ) * ρ₁ + (n₂ : ℝ) * ρ₂) ^ 2 / (2 * (K : ℝ))) := by
  have hb₁ (s t : Fin K → Bool) :
      0 ≤ 1 + ρ₁ * innerSign s t / (K : ℝ) := by
    rw [← hPair₁ s t]
    exact integral_nonneg (fun x => mul_nonneg (hL₁0 s x) (hL₁0 t x))
  have hb₂ (s t : Fin K → Bool) :
      0 ≤ 1 + ρ₂ * innerSign s t / (K : ℝ) := by
    rw [← hPair₂ s t]
    exact integral_nonneg (fun x => mul_nonneg (hL₂0 s x) (hL₂0 t x))
  rw [one_add_chiSqDiv_uniformMixture_twoChannel_sign K n₁ n₂
    μ₁ μ₂ Q₁ Q₂ L₁ L₂ hL₁ hL₂ hL₁0 hL₂0 hQ₁ hQ₂
    hInt₁ hInt₂ ρ₁ ρ₂ hPair₁ hPair₂]
  exact uniform_sign_twoPower_le_exp K n₁ n₂ ρ₁ ρ₂ hb₁ hb₂
end Causalean.Stat.Minimax.Mixture.TwoChannel
