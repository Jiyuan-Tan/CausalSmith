module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentLikelihood

/-! Complete iid paired-tent mixture second moments and total variation. -/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Pairwise integrable densities make the centered uniform-mixture density square integrable. This statement assumes [the hac condition](hyp:hac), [the hpair condition](hyp:hpair). [This is the stated conclusion](goal). -/
-- @node: uniformMixture_sq_dev_integrable
lemma uniformMixture_sq_dev_integrable {Ω S : Type*} [MeasurableSpace Ω]
    [Fintype S] [Nonempty S] (Q : S → Measure Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] [∀ s, IsProbabilityMeasure (Q s)]
    (hac : ∀ s, Q s ≪ P)
    (hpair : ∀ s t, Integrable
      (fun x => ((Q s).rnDeriv P x).toReal * ((Q t).rnDeriv P x).toReal) P) :
    Integrable (fun x => (((Causalean.Stat.Minimax.Mixture.uniformMixture Q).rnDeriv P x).toReal-1)^2) P := by
  haveI := Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability Q
  let d (s : S) (x : Ω) := ((Q s).rnDeriv P x).toReal
  let p (x : Ω) := ((Causalean.Stat.Minimax.Mixture.uniformMixture Q).rnDeriv P x).toReal
  have hdouble : Integrable (fun x => ∑ s : S, ∑ t : S, d s x*d t x) P := by
    apply integrable_finsetSum Finset.univ
    intro s _
    apply integrable_finsetSum Finset.univ
    intro t _
    exact hpair s t
  have hpoint : (fun x => p x^2) =ᵐ[P]
      (fun x => (∑ s : S, ∑ t : S, d s x*d t x)/(Fintype.card S:ℝ)^2) := by
    filter_upwards [Causalean.Stat.Minimax.Mixture.uniformMixture_rnDeriv Q P] with x hx
    change p x = (∑ s : S, d s x)/(Fintype.card S:ℝ) at hx
    rw [hx, div_pow, sq, Finset.sum_mul_sum]
  have hsq : Integrable (fun x => p x^2) P :=
    (hdouble.div_const _).congr hpoint.symm
  have hp : Integrable p P := Measure.integrable_toReal_rnDeriv
  have heq : (fun x => (p x-1)^2) = (fun x => p x^2-2*p x+1) := by
    funext x
    ring
  change Integrable (fun x => (p x-1)^2) P
  rw [heq]
  exact (hsq.sub (hp.const_mul 2)).add (integrable_const 1)

/-- Enumerating the uniform signs in the canonical finite prior gives the library iid mixture. [This is the stated conclusion](goal). -/
-- @node: fair_sign_priorMixture_eq_uniformMixture
lemma fair_sign_priorMixture_eq_uniformMixture (k n : ℕ)
    (laws : (Fin k → Bool) → ObservedLaw) :
    priorMixture n (finitePriorOf (fun _ => (2:ℝ)^(-(k:ℤ))) laws) =
      Causalean.Stat.Minimax.Mixture.uniformMixture
        (fun σ : Fin k → Bool => Measure.pi (fun _ : Fin n => (laws σ).P)) := by
  unfold priorMixture priorWeight priorLaw finitePriorOf
    Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  have hw : ENNReal.ofReal ((2:ℝ)^(-(k:ℤ))) =
      (Fintype.card (Fin k → Bool):ℝ≥0∞)⁻¹ := by
    simp [Fintype.card_fun, Fintype.card_bool, zpow_neg, ENNReal.ofReal_inv_of_pos,
      ENNReal.ofReal_pow, zpow_natCast]
  simp_rw [hw]
  exact Fintype.sum_equiv (Fintype.equivFin (Fin k → Bool)).symm _ _ (fun _ => rfl)

/-- The canonical rare-mark prior enumerates the normalized uniform iid sign mixture. [This is the stated conclusion](goal). -/
-- @node: tentPrior_mixture_eq_uniformMixture
lemma tentPrior_mixture_eq_uniformMixture (n : ℕ) (v : Params) :
    priorMixture n (tentPrior true n v) =
      Causalean.Stat.Minimax.Mixture.uniformMixture
        (fun σ : Fin (tentRank n v/2) → Bool =>
          Measure.pi (fun _ : Fin n => (tentLaw true n v σ).P)) := by
  simpa only [tentPrior, Int.natCast_ediv, Nat.cast_ofNat] using
    fair_sign_priorMixture_eq_uniformMixture (tentRank n v/2) n (tentLaw true n v)

/-- Radon--Nikodym overlaps equal the explicitly integrated full-record likelihood overlaps. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_rnDeriv_overlap
lemma tent_rnDeriv_overlap (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ τ : Fin (tentRank n v/2) → Bool) :
    let P0 := (tentLaw false n v (fun _ => false)).P
    Integrable (fun o => ((tentLaw true n v σ).P.rnDeriv P0 o).toReal *
      ((tentLaw true n v τ).P.rnDeriv P0 o).toReal) P0 ∧
    (∫ o, ((tentLaw true n v σ).P.rnDeriv P0 o).toReal *
      ((tentLaw true n v τ).P.rnDeriv P0 o).toReal ∂P0) =
        1+(tentRarity n v*kappa0^2/6)*
          Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(tentRank n v/2:ℕ) := by
  dsimp only
  have he (s : Fin (tentRank n v/2) → Bool) :
      (fun o => ((tentLaw true n v s).P.rnDeriv (tentLaw false n v (fun _ => false)).P o).toReal) =ᵐ[
        (tentLaw false n v (fun _ => false)).P] tentLikelihood n v s := by
    rw [tentLaw_true_eq_withDensity v hv n hn s]
    filter_upwards [Measure.rnDeriv_withDensity _ (measurable_tentLikelihood n v s).ennreal_ofReal] with o ho
    rw [ho, ENNReal.toReal_ofReal (le_trans (by norm_num) (tentLikelihood_bounds n v s o).1)]
  have hp := (he σ).mul (he τ)
  exact ⟨(tentLikelihood_pair_integrable n v σ τ).congr hp.symm,
    (integral_congr_ae hp).trans (tentLikelihood_pair_overlap v hv n hn σ τ)⟩

/-- The actual original-record iid mixture obeys the paired-sign chi-square bound. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentMixture_chiSq_bound
lemma tentMixture_chiSq_bound (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    1+Causalean.Stat.chiSqDiv (priorMixture n (tentPrior true n v))
      (Measure.pi (fun _ : Fin n => (tentLaw false n v (fun _ => false)).P)) ≤
        Real.exp (kappa0^4/36) := by
  have hac (σ : Fin (tentRank n v/2) → Bool) :
      (tentLaw true n v σ).P ≪ (tentLaw false n v (fun _ => false)).P := by
    rw [tentLaw_true_eq_withDensity v hv n hn σ]
    exact withDensity_absolutelyContinuous _ _
  rw [tentPrior_mixture_eq_uniformMixture,
    Causalean.Stat.Minimax.Mixture.one_add_chiSqDiv_uniformMixture_iid
      _ _ hac (fun σ τ => (tent_rnDeriv_overlap v hv n hn σ τ).1)]
  simp_rw [(fun σ τ => (tent_rnDeriv_overlap v hv n hn σ τ).2)]
  exact tent_sign_overlap_average_le v hv n hn

/-- The numerical exponent is strictly smaller than the unit chi-square threshold. [This is the stated conclusion](goal). -/
-- @node: tent_likelihood_exp_lt_two
lemma tent_likelihood_exp_lt_two : Real.exp (kappa0^4/36) < 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (by norm_num [kappa0] : 0 ≤ kappa0^4/36)
    (by norm_num [kappa0] : kappa0^4/36 < 1)
  exact h.trans_lt (by norm_num [kappa0])

/-- Cauchy--Schwarz converts the actual full-record chi-square bound into strict total variation. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tentMixture_tv_lt_half
lemma tentMixture_tv_lt_half (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n => (tentLaw false n v (fun _ => false)).P))
      (priorMixture n (tentPrior true n v)) < 1/2 := by
  let P0 := (tentLaw false n v (fun _ => false)).P
  let Q (σ : Fin (tentRank n v/2) → Bool) := (tentLaw true n v σ).P
  have hac (σ : Fin (tentRank n v/2) → Bool) : Q σ ≪ P0 := by
    dsimp [Q, P0]
    rw [tentLaw_true_eq_withDensity v hv n hn σ]
    exact withDensity_absolutelyContinuous _ _
  have hpair := fun σ τ => (tent_rnDeriv_overlap v hv n hn σ τ).1
  have hpi (σ : Fin (tentRank n v/2) → Bool) :
      Measure.pi (fun _ : Fin n => Q σ) ≪ Measure.pi (fun _ : Fin n => P0) :=
    Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous _ _ (hac σ) n
  have hi := uniformMixture_sq_dev_integrable
    (fun σ => Measure.pi (fun _ : Fin n => Q σ)) (Measure.pi (fun _ : Fin n => P0)) hpi
    (fun σ τ => Causalean.Stat.Minimax.Mixture.iidPairIntegrable _ _ _ (hac σ) (hac τ) (hpair σ τ) n)
  have hu := Causalean.Stat.Minimax.Mixture.uniformMixture_absolutelyContinuous
    (fun σ => Measure.pi (fun _ : Fin n => Q σ)) (Measure.pi (fun _ : Fin n => P0)) hpi
  haveI := Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability
    (fun σ => Measure.pi (fun _ : Fin n => Q σ))
  have ht := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv _ _ hu hi
  have hchi := (tentMixture_chiSq_bound v hv n hn).trans_lt tent_likelihood_exp_lt_two
  rw [tentPrior_mixture_eq_uniformMixture] at hchi ⊢
  rw [Causalean.Stat.tvDist_symm]
  apply lt_of_le_of_lt ht
  have hs : Real.sqrt (Causalean.Stat.chiSqDiv
      (Causalean.Stat.Minimax.Mixture.uniformMixture (fun σ => Measure.pi (fun _ : Fin n => Q σ)))
      (Measure.pi (fun _ : Fin n => P0))) < 1 := by
    apply (Real.sqrt_lt (Causalean.Stat.chiSqDiv_nonneg) (by norm_num : (0:ℝ) ≤ 1)).2
    dsimp [Q, P0]
    linarith
  nlinarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
