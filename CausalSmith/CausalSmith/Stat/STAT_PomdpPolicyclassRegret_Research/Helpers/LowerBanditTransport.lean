module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerBanditObserved

/-! # Transport of bandit information to observable selectors

The Boolean selected-law experiment and the finite reward-symbol experiment
have the same one-step masses. Independent replication and reward decoding
therefore carry the information and testing bounds in (44) to the actual
observations, with the same revealed behavior and target list.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory InformationTheory
open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- The uniform context law in the fully observed lower experiment. -/
-- @node: lowerBanditContextLaw
noncomputable def lowerBanditContextLaw {d : Nat} (hd : 0 < d) : Measure (Fin d) := by
  letI : NeZero d := ⟨hd.ne'⟩
  exact (PMF.uniformOfFintype (Fin d)).toMeasure

/-- Uniform context redraw is a probability law. For [the code dimension](hyp:d) and
[the code dimension assumption](hyp:hd), this establishes
[the lower bandit context probability result](goal). -/
-- @node: lower_bandit_context_probability
lemma lower_bandit_context_probability {d : Nat} (hd : 0 < d) :
    IsProbabilityMeasure (lowerBanditContextLaw hd) := by
  letI : NeZero d := ⟨hd.ne'⟩
  change IsProbabilityMeasure (PMF.uniformOfFintype (Fin d)).toMeasure
  infer_instance

/-- Boolean success and failure correspond to reward symbols one and zero. -/
-- @node: lowerBanditSymbolEquiv
def lowerBanditSymbolEquiv (d : Nat) :
    SelectedCoord (Fin d) ≃ Fin d × Bool × Fin 2 :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm)

/-- The selected-law singleton has precisely the common-kernel symbol mass. For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0), [the g1 assumption](hyp:hg1), and
[the z](hyp:z), this establishes [the lower bandit selected singleton result](goal). -/
-- @node: lower_bandit_selected_singleton
lemma lower_bandit_selected_singleton {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16)
    (z : SelectedCoord (Fin d)) :
    (lowerBanditObservationLaw (lowerBanditContextLaw hd) word gamma {z}).toReal =
      lowerBanditSymbolWeight word gamma (lowerBanditSymbolEquiv d z) := by
  letI := lower_bandit_context_probability hd
  have hcell := selectedLaw_cell (lowerBanditContextLaw hd) (fun _ ↦ 1 / 2)
    (fun x ↦ lowerBanditRewardMean gamma (word x) false)
    (fun x ↦ lowerBanditRewardMean gamma (word x) true)
    (by fun_prop) (by fun_prop) (by fun_prop) (by intro x; norm_num)
    (fun x ↦ lower_bandit_reward_prob_unit gamma hg0 hg1 (word x) false)
    (fun x ↦ lower_bandit_reward_prob_unit gamma hg0 hg1 (word x) true)
    {z.1} (measurableSet_singleton _) z.2.1 z.2.2
  have hset : {w : SelectedCoord (Fin d) | w.1 ∈ ({z.1} : Set (Fin d)) ∧
      w.2.1 = z.2.1 ∧ w.2.2 = z.2.2} = {z} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    exact ⟨fun h ↦ Prod.ext h.1 (Prod.ext h.2.1 h.2.2), fun h ↦ by simp [h]⟩
  rw [hset, lintegral_singleton] at hcell
  change (selectedLaw _ _ _ _ {z}).toReal = _
  rw [hcell, ENNReal.toReal_mul]
  have hctx : (lowerBanditContextLaw hd {z.1}).toReal = (d : ℝ)⁻¹ := by
    letI : NeZero d := ⟨hd.ne'⟩
    simp [lowerBanditContextLaw, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  rw [hctx]
  have hmass : 0 ≤ cellMass (1 / 2)
      (lowerBanditRewardMean gamma (word z.1) false)
      (lowerBanditRewardMean gamma (word z.1) true) z.2.1 z.2.2 := by
    cases ha : z.2.1 <;> cases hy : z.2.2 <;>
      norm_num [cellMass, bitMass, ha, hy] <;>
      linarith [(lower_bandit_reward_quarter_band gamma hg0 hg1 (word z.1) false).1,
        (lower_bandit_reward_quarter_band gamma hg0 hg1 (word z.1) false).2,
        (lower_bandit_reward_quarter_band gamma hg0 hg1 (word z.1) true).1,
        (lower_bandit_reward_quarter_band gamma hg0 hg1 (word z.1) true).2]
  rw [ENNReal.toReal_ofReal hmass]
  cases ha : z.2.1 <;> cases hy : z.2.2 <;>
    simp [lowerBanditSymbolWeight, lowerBanditRewardWeight, lowerBanditSymbolEquiv,
      finTwoEquiv, cellMass, bitMass, ha, hy] <;> ring

/-- Encoding Boolean rewards gives the actual one-step finite-symbol measure. For
[the code dimension](hyp:d), [the code dimension assumption](hyp:hd), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the g0 assumption](hyp:hg0), and [the g1 assumption](hyp:hg1),
this establishes [the lower bandit selected symbol law result](goal). -/
-- @node: lower_bandit_selected_symbol_law
lemma lower_bandit_selected_symbol_law {d : Nat} (hd : 0 < d)
    (word : Fin d → Bool) (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16) :
    (lowerBanditObservationLaw (lowerBanditContextLaw hd) word gamma).map
      (lowerBanditSymbolEquiv d) = (lowerBanditSymbolPMF hd word gamma).toMeasure := by
  letI := lower_bandit_context_probability hd
  letI := lower_bandit_observation_probability (lowerBanditContextLaw hd) word gamma hg0 hg1
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : (lowerBanditSymbolEquiv d) ⁻¹' {w} = {(lowerBanditSymbolEquiv d).symm w} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (lowerBanditSymbolEquiv d).apply_eq_iff_eq_symm_apply
  rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [lower_bandit_selected_singleton hd word gamma hg0 hg1,
    (lowerBanditSymbolEquiv d).apply_symm_apply, lower_bandit_symbol_pmf_toReal hd word gamma hg0 hg1]

/-- Decode a Boolean bandit sample into its observable real rewards. -/
-- @node: lowerBanditObservedDecode
def lowerBanditObservedDecode (T d : Nat)
    (w : Fin T → SelectedCoord (Fin d)) : ObsView T d :=
  fun t ↦ ((w t).1, (w t).2.1, if (w t).2.2 then (1 : ℝ) else 0)

/-- The actual observed law is the decoded Boolean independent sample. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the codeword index](hyp:v), [the rate parameter](hyp:gamma),
[the signal parameter](hyp:eta), [the g0 assumption](hyp:hg0), and [the g1 assumption](hyp:hg1),
this establishes [the lower bandit actual selected law result](goal). -/
-- @node: lower_bandit_actual_selected_law
lemma lower_bandit_actual_selected_law (T M d : Nat) (hd : 0 < d)
    (hM : 2 ≤ M) (code : Fin M → Fin d → Bool) (v : Fin M)
    (gamma eta : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1 / 16) :
    obsLaw (lowerBanditExperiment T M d hd hM code v gamma eta).Mx.toRawB =
      (Measure.pi (fun _ : Fin T ↦
        lowerBanditObservationLaw (lowerBanditContextLaw hd) (code v) gamma)).map
        (lowerBanditObservedDecode T d) := by
  letI := lower_bandit_context_probability hd
  letI := lower_bandit_observation_probability (lowerBanditContextLaw hd) (code v) gamma hg0 hg1
  rw [lower_bandit_actual_observed_product_law T M d hd hM code v gamma eta hg0 hg1]
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin T ↦
    lowerBanditObservationLaw (lowerBanditContextLaw hd) (code v) gamma)
    (f := fun _ ↦ lowerBanditSymbolEquiv d)
    (fun _ ↦ (measurable_of_finite _).aemeasurable)
  simp_rw [lower_bandit_selected_symbol_law hd (code v) gamma hg0 hg1] at hpi
  rw [← hpi, Measure.map_map (by fun_prop) (measurable_of_finite _)]
  congr 1
  funext w t
  cases hy : (w t).2.2 <;>
    simp [Function.comp_def, lowerBanditSymbolEquiv, finTwoEquiv,
      lowerBanditObservedDecode, hy]

/-- Reward decoding preserves the finite KL budget (44) for actual observations. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the time horizon assumption](hyp:hT),
[the candidate-policy count assumption](hyp:hM), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the signal parameter](hyp:eta), this establishes
[the lower bandit actual information budget result](goal). -/
-- @node: lower_bandit_actual_information_budget
lemma lower_bandit_actual_information_budget (T M d : Nat) (hd : 0 < d)
    (hT : 1 ≤ T) (hM : 2 ≤ M) (code : Fin M → Fin d → Bool) (v : Fin M)
    (eta : ℝ) :
    klDiv (obsLaw (nX := d) (nH := 1) (lowerBanditExperiment T M d hd hM code v
      ((lowerBanditRewardAmplitude T M (by omega) hM)) eta).Mx.toRawB)
      (obsLaw (nX := d) (nH := 1) (lowerBanditExperiment T M d hd hM code v 0 eta).Mx.toRawB) ≠ ⊤ ∧
    (klDiv (obsLaw (nX := d) (nH := 1) (lowerBanditExperiment T M d hd hM code v
      ((lowerBanditRewardAmplitude T M (by omega) hM)) eta).Mx.toRawB)
      (obsLaw (nX := d) (nH := 1) (lowerBanditExperiment T M d hd hM code v 0 eta).Mx.toRawB)).toReal ≤
        Real.log (M : ℝ) / 64 := by
  letI := lower_bandit_context_probability hd
  obtain ⟨hg0, hg1⟩ := lower_bandit_reward_amplitude_bounds T M hT hM
  obtain ⟨hfin, hbudget⟩ := lower_bandit_product_information_budget
    (lowerBanditContextLaw hd) (code v) T M hT hM
  erw [lower_bandit_actual_selected_law T M d hd hM code v _ eta hg0.le hg1,
    lower_bandit_actual_selected_law T M d hd hM code v 0 eta (by norm_num) (by norm_num)]
  letI := lower_bandit_observation_probability (lowerBanditContextLaw hd) (code v)
    ((lowerBanditRewardAmplitude T M (by omega) hM)) hg0.le hg1
  letI := lower_bandit_observation_probability (lowerBanditContextLaw hd) (code v)
    0 (by norm_num) (by norm_num)
  have hmap := klDiv_map_le
    (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw
      (lowerBanditContextLaw hd) (code v) ((lowerBanditRewardAmplitude T M (by omega) hM))))
    (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw
      (lowerBanditContextLaw hd) (code v) 0))
    (measurable_of_finite (lowerBanditObservedDecode T d))
  exact ⟨ne_top_of_le_ne_top hfin hmap, (ENNReal.toReal_mono hfin hmap).trans hbudget⟩

/-- Every observable selector inherits the bandit sample's testing error floor. For
[the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the code dimension assumption](hyp:hd), [the time horizon assumption](hyp:hT),
[the candidate-policy count assumption](hyp:hM), [the binary code](hyp:code),
[the signal parameter](hyp:eta), and [the observable selector](hyp:sel), this establishes
[the lower bandit actual testing error result](goal). -/
-- @node: lower_bandit_actual_testing_error
lemma lower_bandit_actual_testing_error (T M d : Nat) (hd : 0 < d)
    (hT : 1 ≤ T) (hM : 2 ≤ M)
    (code : Fin M → Fin d → Bool) (eta : ℝ) (sel : ObservableSelector T M) :
    1 / 8 < (M : ℝ)⁻¹ * ∑ v : Fin M,
      (obsLaw (lowerBanditExperiment T M d hd hM code v
        ((lowerBanditRewardAmplitude T M (by omega) hM)) eta).Mx.toRawB).real
        {w | sel.1 d
          (fun _ a ↦ (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) a).toReal)
          (fun j x a ↦ (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal)
          w ≠ v} := by
  letI := lower_bandit_context_probability hd
  let ψ : ObsView T d → Fin M := sel.1 d
    (fun _ a ↦ (pmfOfRealWeight (fun _ : Bool ↦ (1 / 2 : ℝ)) a).toReal)
    (fun j x a ↦ (pmfOfRealWeight (lowerBanditPolicyWeight eta (code j) x) a).toReal)
  have hψ : Measurable ψ := sel.2 _ _ _
  have htest := lower_bandit_product_testing_error (lowerBanditContextLaw hd)
    T M hT hM code (ψ ∘ lowerBanditObservedDecode T d)
    (hψ.comp (measurable_of_finite _))
  obtain ⟨hg0, hg1⟩ := lower_bandit_reward_amplitude_bounds T M hT hM
  convert htest using 1
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [lower_bandit_actual_selected_law T M d hd hM code v _ eta hg0.le hg1]
  change ((Measure.pi _).map (lowerBanditObservedDecode T d) {w | ψ w ≠ v}).toReal = _
  have hbad : MeasurableSet {w | ψ w ≠ v} :=
    (measurableSet_eq_fun hψ measurable_const).compl
  rw [Measure.map_apply (measurable_of_finite _) hbad]
  rfl

/-- The legal bandit packing and its testing floor give the regret bound (45). For
[the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the lower bandit parametric component result](goal). -/
-- @node: lower_bandit_parametric_component
lemma lower_bandit_parametric_component (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (T M : Nat) (C : ℝ),
      (hT : 1 ≤ T) → (hM : 2 ≤ M) → 1 ≤ C →
      c1 * min 1 (Real.sqrt ((listInformationRatio T M (by omega) hM))) ≤
        minimaxRegret T M t0 zeta C := by
  let eta := min ((policyFactor zeta - 1) / 2) (1 / 2)
  have hL : 1 < policyFactor zeta := by
    exact Real.one_lt_exp_iff.mpr hzeta
  obtain ⟨heta0, hetaHalf, hetaL⟩ := lower_bandit_amplitude_bounds (policyFactor zeta) hL
  have heta1 : eta ≤ 1 := by dsimp [eta]; linarith
  refine ⟨eta / 256, div_pos heta0 (by norm_num), ?_⟩
  intro T M C hT hM hC
  obtain ⟨code, hcode⟩ := codeSeparated_exists M hM
  let d := codeDimension M
  let hd := codeDimension_pos M hM
  let gamma := (lowerBanditRewardAmplitude T M (by omega) hM)
  obtain ⟨hg0, hg1⟩ := lower_bandit_reward_amplitude_bounds T M hT hM
  let models := fun v ↦ lowerBanditExperiment T M d hd hM code v gamma eta
  have hClass : ∀ v, PolicyListClass t0 zeta C (models v) := fun v ↦
    lower_bandit_membership T M d hd hM code hcode v t0 zeta C gamma eta
      ht0 hzeta hC hg0.le hg1 heta0 heta1 hetaL
  have hgap : ∀ v w, w ≠ v → gamma * eta / 2 ≤
      policyValue (models v) v - policyValue (models v) w := fun v w hw ↦
    lower_bandit_model_gap T M d hd hM code hcode v w hw gamma eta hg0.le hg1 heta0.le heta1
  have htest : ∀ sel : ObservableSelector T M,
      (1 / 8 : ℝ) ≤ (M : ℝ)⁻¹ * ∑ v,
        (obsLaw (models v).Mx.toRawB).real
          {w | sel.1 (models v).nX (models v).Mx.b (models v).Mx.E w ≠ v} := by
    intro sel
    have h := lower_bandit_actual_testing_error T M d hd hT hM code eta sel
    exact h.le
  have hresult := testing_average_error_le_minimaxRegret hM t0 zeta C
    (gamma * eta / 2) (1 / 8) (by positivity) models hClass hgap htest
  calc
    _ = (gamma * eta / 2) * (1 / 8) := by
      dsimp [gamma, lowerBanditRewardAmplitude]
      ring
    _ ≤ _ := hresult

end CausalSmith.Stat.PomdpPolicyclassRegret
