module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryTentLikelihood

/-! Full iid signed-binary paired-tent mixture bounds. -/
public section
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The separate signed-binary prior enumerates the normalized uniform iid sign mixture. [This is the stated conclusion](goal). -/
-- @node: binaryTentPrior_mixture_eq_uniformMixture
lemma binaryTentPrior_mixture_eq_uniformMixture (n : ℕ) (w : Smooth3) :
    priorMixture n (binaryTentPrior true n w) =
      Causalean.Stat.Minimax.Mixture.uniformMixture
        (fun σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool =>
          Measure.pi (fun _ : Fin n => (binaryTentLaw true n w σ).P)) := by
  simpa only [binaryTentPrior, Int.natCast_ediv, Nat.cast_ofNat] using
    fair_sign_priorMixture_eq_uniformMixture (tentRank n (Params.ofBounded w)/2) n (binaryTentLaw true n w)

/-- Radon--Nikodym overlaps equal the explicitly integrated full-record likelihood overlaps. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTent_rnDeriv_overlap
lemma binaryTent_rnDeriv_overlap (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ τ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    let P0 := (binaryTentLaw false n w (fun _ => false)).P
    Integrable (fun o => ((binaryTentLaw true n w σ).P.rnDeriv P0 o).toReal *
      ((binaryTentLaw true n w τ).P.rnDeriv P0 o).toReal) P0 ∧
    (∫ o, ((binaryTentLaw true n w σ).P.rnDeriv P0 o).toReal *
      ((binaryTentLaw true n w τ).P.rnDeriv P0 o).toReal ∂P0) =
        1+(tentRarity n (Params.ofBounded w)*kappa0^2/6)*
          Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(tentRank n (Params.ofBounded w)/2:ℕ) := by
  dsimp only
  have he (s : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
      (fun o => ((binaryTentLaw true n w s).P.rnDeriv (binaryTentLaw false n w (fun _ => false)).P o).toReal) =ᵐ[
        (binaryTentLaw false n w (fun _ => false)).P] binaryTentLikelihood n w s := by
    rw [binaryTentLaw_true_eq_withDensity w hw n hn s]
    filter_upwards [Measure.rnDeriv_withDensity _ (measurable_binaryTentLikelihood n w s).ennreal_ofReal] with o ho
    rw [ho, ENNReal.toReal_ofReal (le_trans (by norm_num) (binaryTentLikelihood_bounds w hw n hn s o).1)]
  have hp := (he σ).mul (he τ)
  exact ⟨(binaryTentLikelihood_pair_integrable w hw n hn σ τ).congr hp.symm,
    (integral_congr_ae hp).trans (binaryTentLikelihood_pair_overlap w hw n hn σ τ)⟩

/-- The actual original-record iid mixture obeys the paired-sign chi-square bound. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentMixture_chiSq_bound
lemma binaryTentMixture_chiSq_bound (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n) :
    1+Causalean.Stat.chiSqDiv (priorMixture n (binaryTentPrior true n w))
      (Measure.pi (fun _ : Fin n => (binaryTentLaw false n w (fun _ => false)).P)) ≤
        Real.exp (kappa0^4/36) := by
  have hac (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
      (binaryTentLaw true n w σ).P ≪ (binaryTentLaw false n w (fun _ => false)).P := by
    rw [binaryTentLaw_true_eq_withDensity w hw n hn σ]
    exact withDensity_absolutelyContinuous _ _
  rw [binaryTentPrior_mixture_eq_uniformMixture,
    Causalean.Stat.Minimax.Mixture.one_add_chiSqDiv_uniformMixture_iid
      _ _ hac (fun σ τ => (binaryTent_rnDeriv_overlap w hw n hn σ τ).1)]
  simp_rw [(fun σ τ => (binaryTent_rnDeriv_overlap w hw n hn σ τ).2)]
  exact tent_sign_overlap_average_le (Params.ofBounded w) ⟨by norm_num [Params.ofBounded], hw⟩ n hn

/-- Cauchy--Schwarz converts the actual full-record chi-square bound into strict total variation. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentMixture_tv_lt_half
lemma binaryTentMixture_tv_lt_half (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n) :
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n => (binaryTentLaw false n w (fun _ => false)).P))
      (priorMixture n (binaryTentPrior true n w)) < 1/2 := by
  let P0 := (binaryTentLaw false n w (fun _ => false)).P
  let Q (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) := (binaryTentLaw true n w σ).P
  have hac (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) : Q σ ≪ P0 := by
    dsimp [Q, P0]
    rw [binaryTentLaw_true_eq_withDensity w hw n hn σ]
    exact withDensity_absolutelyContinuous _ _
  have hpair := fun σ τ => (binaryTent_rnDeriv_overlap w hw n hn σ τ).1
  have hpi (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
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
  have hchi := (binaryTentMixture_chiSq_bound w hw n hn).trans_lt tent_likelihood_exp_lt_two
  rw [binaryTentPrior_mixture_eq_uniformMixture] at hchi ⊢
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
