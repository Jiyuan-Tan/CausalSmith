module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TentMixture

/-! Full-record likelihoods for the separate signed-binary paired-tent construction. -/
@[expose] public section
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The binary likelihood changes only treated sign records. This statement assumes [the n parameter](hyp:n), [the w parameter](hyp:w), [the σ parameter](hyp:σ), [the o parameter](hyp:o). [This is the stated defined object](goal). -/
-- @node: binaryTentLikelihood
def binaryTentLikelihood (n : ℕ) (w : Smooth3)
    (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) (o : Record) : ℝ :=
  1 + if o.2.1 then
    if o.2.2 = 1 then tentEffect n (Params.ofBounded w) σ o.1
    else if o.2.2 = -1 then -tentEffect n (Params.ofBounded w) σ o.1 else 0
  else 0

/-- The likelihood on the complete binary record space is measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_binaryTentLikelihood
@[fun_prop] lemma measurable_binaryTentLikelihood (n : ℕ) (w : Smooth3)
    (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    Measurable (binaryTentLikelihood n w σ) := by
  unfold binaryTentLikelihood
  apply measurable_const.add
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · fun_prop
    · apply Measurable.ite
      · exact measurableSet_eq_fun (by fun_prop) measurable_const
      · fun_prop
      · exact measurable_const
  · exact measurable_const

/-- The likelihood is positive and bounded, including records outside sign support. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLikelihood_bounds
lemma binaryTentLikelihood_bounds (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) (o : Record) :
    15/16 ≤ binaryTentLikelihood n w σ o ∧ binaryTentLikelihood n w σ o ≤ 17/16 := by
  have hg := abs_le.mp (tentEffect_abs_le_one_sixteenth (Params.ofBounded w)
    ⟨by norm_num [Params.ofBounded], hw⟩ n hn σ o.1)
  unfold binaryTentLikelihood
  split_ifs <;> constructor <;> linarith [hg.1, hg.2]

/-- Integrating the binary law retains both treatment arms and both outcome signs. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn), [the f condition](hyp:f), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_lintegral
lemma binaryTentLaw_lintegral (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (ν : Bool) (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool)
    (f : Record → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ o, f o ∂(binaryTentLaw ν n w σ).P) =
      ∫⁻ x : unitInterval, ∑ a : Bool, ∑ b : Bool,
        ENNReal.ofReal ((1 + if a && ν then signVal b * tentEffect n (Params.ofBounded w) σ x
          else 0)/4) * f (x,a,signVal b) ∂design := by
  have hv : (Params.ofBounded w).Valid := ⟨by norm_num [Params.ofBounded], hw⟩
  let τ : Nuisance := if ν then
    ⟨tentEffect n (Params.ofBounded w) σ, continuous_tentEffect n (Params.ofBounded w) σ⟩ else 0
  have hc : (∀ x : unitInterval, 0 ≤ (ContinuousMap.const unitInterval (1/2:ℝ)) x ∧
      (ContinuousMap.const unitInterval (1/2:ℝ)) x ≤ 1) ∧
      (∀ x : unitInterval, |(0 : Nuisance) x| ≤ 1 ∧ |(0 : Nuisance) x + τ x| ≤ 1) := by
    constructor
    · intro x; norm_num
    · intro x
      have hh := (tentEffect_abs_le_one_sixteenth _ hv n hn σ x).trans (by norm_num : (1:ℝ)/16 ≤ 1)
      cases ν <;> simpa [τ] using (show |(0:ℝ)| ≤ 1 ∧ |tentEffect n (Params.ofBounded w) σ x| ≤ 1 from ⟨by norm_num, hh⟩)
  have hQ : ∀ a : Bool, IsMarkovKernel (binaryArm (if a then (0:Nuisance)+τ else 0)) := by
    intro a
    apply binaryArm_markov
    intro x
    cases a
    · simp
    · simpa using (hc.2 x).2
  letI := hQ
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  letI := recordKernel_markov (ContinuousMap.const unitInterval (1/2:ℝ)) (by fun_prop)
    (fun a => binaryArm (if a then (0:Nuisance)+τ else 0)) hc.1 hQ
  change (∫⁻ o, f o ∂(binaryRealization (ContinuousMap.const unitInterval (1/2)) 0 τ).P) = _
  rw [binaryRealization, dif_pos hc, Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro x
  change (∫⁻ r, f (x,r) ∂recordMeasure (ContinuousMap.const unitInterval (1/2:ℝ))
    (fun a => binaryArm (if a then (0:Nuisance)+τ else 0)) x) = _
  rw [recordMeasure, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    Measure.dirac_prod, Measure.dirac_prod,
    lintegral_map (by fun_prop) measurable_prodMk_left,
    lintegral_map (by fun_prop) measurable_prodMk_left]
  have hscale (t : ℝ) : (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal (t/2) = ENNReal.ofReal (t/4) := by
    calc
      _ = ENNReal.ofReal (1/2:ℝ) * ENNReal.ofReal (t/2) := by
        congr 1
        simp [ENNReal.ofReal_div_of_pos]
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
        congr 1
        ring
  cases ν <;> simp [τ, binaryArm, Fintype.sum_bool, signVal]
  all_goals
    simp only [binaryArmMeasure, lintegral_add_measure, lintegral_smul_measure,
      lintegral_dirac' _ (by fun_prop : Measurable (fun y => f (x,true,y))),
      lintegral_dirac' _ (by fun_prop : Measurable (fun y => f (x,false,y))),
      ContinuousMap.coe_mk, ContinuousMap.zero_apply, zero_add, sub_zero, smul_eq_mul,
      mul_add]
    simp only [show ENNReal.ofReal (1/2:ℝ) = (2:ℝ≥0∞)⁻¹ by simp [ENNReal.ofReal_div_of_pos],
      ← mul_assoc, hscale]
    ring_nf
    simp only [show ENNReal.ofReal (1/2:ℝ) = (2:ℝ≥0∞)⁻¹ by simp [ENNReal.ofReal_div_of_pos],
      show ENNReal.ofReal (1/4:ℝ) = (4:ℝ≥0∞)⁻¹ by simp [ENNReal.ofReal_div_of_pos],
      ← ENNReal.inv_pow]
    ring_nf
    simp only [← ENNReal.inv_pow]
    norm_num
    ring

/-- Every binary alternative is the likelihood tilt of the actual balanced binary null. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_true_eq_withDensity
lemma binaryTentLaw_true_eq_withDensity (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    (binaryTentLaw true n w σ).P = (binaryTentLaw false n w (fun _ => false)).P.withDensity
      (fun o => ENNReal.ofReal (binaryTentLikelihood n w σ o)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_binaryTentLikelihood n w σ).ennreal_ofReal hf,
    binaryTentLaw_lintegral w hw n hn true σ f hf,
    binaryTentLaw_lintegral w hw n hn false (fun _ => false) _ (by fun_prop)]
  apply lintegral_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Pi.mul_apply, Bool.and_false, Bool.false_eq_true, if_false, add_zero]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
  congr 1
  congr 1
  cases a <;> cases b <;> norm_num [binaryTentLikelihood, signVal] <;> ring

/-- Pairwise binary likelihood products are integrable under the complete null record law. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLikelihood_pair_integrable
lemma binaryTentLikelihood_pair_integrable (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ τ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    Integrable (fun o => binaryTentLikelihood n w σ o * binaryTentLikelihood n w τ o)
      (binaryTentLaw false n w (fun _ => false)).P := by
  apply Integrable.of_bound (by fun_prop) 4
  filter_upwards [] with o
  have hs := binaryTentLikelihood_bounds w hw n hn σ o
  have ht := binaryTentLikelihood_bounds w hw n hn τ o
  change |binaryTentLikelihood n w σ o * binaryTentLikelihood n w τ o| ≤ 4
  rw [abs_of_nonneg (mul_nonneg (by linarith [hs.1]) (by linarith [ht.1]))]
  nlinarith [mul_le_mul hs.2 ht.2 (by linarith [ht.1]) (by norm_num : (0:ℝ) ≤ 17/16)]

/-- The null integral is the average of all four binary record atoms, over the uniform design. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn), [the hf condition](hyp:hf), [the hf0 condition](hyp:hf0). [This is the stated conclusion](goal). -/
-- @node: binaryTentLaw_false_integral_nonneg
lemma binaryTentLaw_false_integral_nonneg (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (f : Record → ℝ) (hf : Measurable f) (hf0 : ∀ o, 0 ≤ f o) :
    (∫ o, f o ∂(binaryTentLaw false n w (fun _ => false)).P) =
      ∫ x : unitInterval, ∑ a : Bool, ∑ b : Bool, (1/4:ℝ)*f (x,a,signVal b) ∂design := by
  have hm : Measurable (fun x : unitInterval => ∑ a : Bool, ∑ b : Bool,
      (1/4:ℝ)*f (x,a,signVal b)) := by
    apply Finset.measurable_fun_sum
    intro a _
    apply Finset.measurable_fun_sum
    intro b _
    fun_prop
  have hnon (x : unitInterval) : 0 ≤ ∑ a : Bool, ∑ b : Bool, (1/4:ℝ)*f (x,a,signVal b) :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => mul_nonneg (by norm_num) (hf0 _)))
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnon) hm.aestronglyMeasurable,
    binaryTentLaw_lintegral w hw n hn false (fun _ => false) _ hf.ennreal_ofReal]
  congr 1
  apply lintegral_congr
  intro x
  simp only [Bool.and_false, Bool.false_eq_true, if_false, add_zero]
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg
    (fun b _ => mul_nonneg (by norm_num) (hf0 _)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (by norm_num) (hf0 _))]
  apply Finset.sum_congr rfl
  intro b _
  exact (ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)).symm

/-- Summing both arms and signs yields the exact one-observation overlap. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binaryTentLikelihood_pair_overlap
lemma binaryTentLikelihood_pair_overlap (w : Smooth3) (hw : w.Valid) (n : ℕ) (hn : 2 ≤ n)
    (σ τ : Fin (tentRank n (Params.ofBounded w)/2) → Bool) :
    (∫ o, binaryTentLikelihood n w σ o * binaryTentLikelihood n w τ o
      ∂(binaryTentLaw false n w (fun _ => false)).P) =
      1+(tentRarity n (Params.ofBounded w)*kappa0^2/6)*
        Causalean.Stat.Minimax.Mixture.SignOverlap.innerSign σ τ/(tentRank n (Params.ofBounded w)/2:ℕ) := by
  let v := Params.ofBounded w
  have hv : v.Valid := ⟨by norm_num [v, Params.ofBounded], hw⟩
  rw [binaryTentLaw_false_integral_nonneg w hw n hn _ (by fun_prop)
    (fun o => mul_nonneg (le_trans (by norm_num) (binaryTentLikelihood_bounds w hw n hn σ o).1)
      (le_trans (by norm_num) (binaryTentLikelihood_bounds w hw n hn τ o).1))]
  have hatom (x : unitInterval) :
      (∑ a : Bool, ∑ b : Bool, (1/4:ℝ) *
        (binaryTentLikelihood n w σ (x,a,signVal b) * binaryTentLikelihood n w τ (x,a,signVal b))) =
      1 + (kappa0^2 * (tentH n v^v.γ)^2/2) *
        (coarseTent (tentRank n v) σ x * coarseTent (tentRank n v) τ x) := by
    norm_num [Fintype.sum_bool, binaryTentLikelihood, signVal, tentEffect, v]
    ring
  simp_rw [hatom]
  letI : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hg : Integrable (fun x : unitInterval =>
      coarseTent (tentRank n v) σ x * coarseTent (tentRank n v) τ x) design := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (coarseTent_abs_le_one _ σ x) (abs_nonneg _) (coarseTent_abs_le_one _ τ x)
  have hN : 0 < tentRank n v := by have := (tentRank_bounds v hv n hn).1; omega
  have heven : 2*(tentRank n v/2) = tentRank n v := by unfold tentRank; omega
  have hc : (tentRank n v:ℝ) = 2*(tentRank n v/2:ℕ) := by exact_mod_cast heven.symm
  have hε : (tentH n v^v.γ)^2 = tentRarity n v := by
    unfold tentRarity
    rw [← Real.rpow_natCast, ← Real.rpow_mul (tentH_bounds v hv n hn).1.le]
    congr 1
    simp [qExp, v, Params.ofBounded]
    ring
  rw [integral_add (integrable_const 1) (hg.const_mul _), integral_const_mul,
    coarseTent_design_overlap _ hN, hε, hc]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  change 1 + _ = 1 + _
  dsimp only [v]
  ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
