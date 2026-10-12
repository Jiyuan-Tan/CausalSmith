module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Estimators
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.SeparatedPriorDecisions
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.TMarkedContraction
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Matching-prior testing lower bounds

The realized matching target and its size tail provide separation for the
independent risk and connected-interval testing arguments.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hfit), [The target is Borel because its only random coordinate is the finite matching.](goal) -/
-- @node: balanced_target_measurable
@[fun_prop] lemma balanced_target_measurable (n m : ℕ) (hfit : 2*m ≤ n)
    (σ : Bool) (δ : ℝ) :
    Measurable (fun ξ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte
      (balancedSchedule n m hfit σ δ ξ)) := by
  simp_rw [balancedSchedule_tte]
  fun_prop

/-- [The matching marginal of the independent parameter draws is the matching prior.](goal) -/
-- @node: balancedParamLaw_matching_marginal
lemma balancedParamLaw_matching_marginal (m : ℕ) :
    (balancedParamLaw m).map Prod.fst = matchingPrior m := by
  let := balancedParamLaw_probability m
  let := matchingPrior_probability m
  have hmass : (balancedParamLaw m) Set.univ = 1 := measure_univ
  unfold balancedParamLaw at hmass ⊢
  rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul] at hmass
  rw [Measure.map_fst_prod, hmass, one_smul]

/-- Given [the stated assumptions](hyp:hm), [The small-matching exceptional event retains the proved geometric tail.](goal) -/
-- @node: balancedParamLaw_small_matching
lemma balancedParamLaw_small_matching (m : ℕ) (hm : 256 ≤ m) :
    (balancedParamLaw m).real {ξ | ξ.1.size < kZero m} ≤ 1/256 := by
  change (balancedParamLaw m).real (Prod.fst ⁻¹' {M : Matching m | M.size < kZero m}) ≤ _
  rw [← map_measureReal_apply measurable_fst (MeasurableSet.of_discrete),
    balancedParamLaw_matching_marginal]
  exact (matchingPrior_size_tail_bound m hm).trans (kZero_geometric_tail_le m hm)

/-- Given [the stated assumptions](hyp:hfit,hm,hδ), [The realized target separates except when the matching size is below the threshold.](goal) -/
-- @node: balanced_target_separation
lemma balanced_target_separation (n m : ℕ) (hfit : 2*m ≤ n) (hm : 256 ≤ m)
    (δ : ℝ) (hδ : 0 < δ) :
    (balancedParamLaw m).real {ξ | CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte
      (balancedSchedule n m hfit true δ ξ) < 2*δ*(kZero m : ℝ)/n} ≤ 1/256 ∧
    (balancedParamLaw m).real {ξ | -(2*δ*(kZero m : ℝ)/n) <
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte
        (balancedSchedule n m hfit false δ ξ)} ≤ 1/256 := by
  let := balancedParamLaw_probability m
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsep (σ : Bool) :
      {ξ | (if σ then
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte
          (balancedSchedule n m hfit σ δ ξ) < 2*δ*(kZero m : ℝ)/n
        else -(2*δ*(kZero m : ℝ)/n) <
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte
            (balancedSchedule n m hfit σ δ ξ))} ⊆ {ξ | ξ.1.size < kZero m} := by
    intro ξ hξ
    by_contra h
    have hk : (kZero m : ℝ) ≤ ξ.1.size := by exact_mod_cast (Nat.le_of_not_gt h)
    have htarget := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2*δ by positivity)
    have hdiv := (div_le_div_iff_of_pos_right hn).mpr htarget
    cases σ <;> simp [balancedSchedule_tte,
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf, neg_div] at hξ
      <;> linarith
  constructor
  · exact (measureReal_mono (hsep true)).trans (balancedParamLaw_small_matching m hm)
  · exact (measureReal_mono (hsep false)).trans (balancedParamLaw_small_matching m hm)

/-- Given [the stated assumptions](hyp:hn,hδ), [At half-population matching size, the supported separation scale is at least δ/192.](goal) -/
-- @node: matching_separation_scale
lemma matching_separation_scale (n : ℕ) (hn : 512 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    δ/192 ≤ 2*δ*(kZero (n/2) : ℝ)/n ∧
    0 < 2*δ*(kZero (n/2) : ℝ)/n := by
  have hm : 256 ≤ n/2 := by omega
  have hfrac := kZero_ge_pool_fraction (n/2) hm
  have hnm : n ≤ 3*(n/2) := by omega
  have hnm' : (n : ℝ) ≤ 3*(n/2 : ℕ) := by exact_mod_cast hnm
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlow : δ/192 ≤ 2*δ*(kZero (n/2) : ℝ)/n := by
    apply (le_div_iff₀ hnpos).mpr
    nlinarith
  exact ⟨hlow, lt_of_lt_of_le (by positivity) hlow⟩

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,hδ,hδu,htv), [Applying the two decision tests to the same supported matching priors gives
MSE and connected-length bounds at the realized separation scale.](goal) -/
-- @node: matching_decision_lower
lemma matching_decision_lower (n d : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (q r δ : ℝ) (hqr : ChannelDomain q r)
    (hδ : 0 < δ) (hδu : δ ≤ 1/12)
    (htv : Causalean.Stat.tvDist
      (signLaw n (n/2) (by omega) (noisyDesign q r) true δ)
      (signLaw n (n/2) (by omega) (noisyDesign q r) false δ) ≤ 1/50) :
    ENNReal.ofReal (δ^2/147456) ≤ minimaxRisk (noisyDesign (V := Fin n) q r) d ∧
    ENNReal.ofReal (δ/192) ≤ minimaxLength (noisyDesign (V := Fin n) q r) d := by
  let m := n/2
  have hm : 256 ≤ m := by dsimp [m]; omega
  have hfit : 2*m ≤ n := by dsimp [m]; omega
  have hn4 : 4 ≤ n := by omega
  let a : ℝ := 2*δ*(kZero m : ℝ)/n
  have hscale : δ/192 ≤ a ∧ 0 < a := matching_separation_scale n hn δ hδ
  have ha1 : a ≤ 1 := by
    have hk : kZero m ≤ m := by dsimp [kZero]; omega
    have hkn : 2*kZero m ≤ n := by omega
    have hkn' : 2*(kZero m : ℝ) ≤ n := by exact_mod_cast hkn
    have hnpos : 0 < (n : ℝ) := by positivity
    dsimp [a]
    apply (div_le_iff₀ hnpos).mpr
    nlinarith
  let := balancedParamLaw_probability m
  have hclass (σ : Bool) : ∀ᵐ ξ ∂balancedParamLaw m,
      ScheduleClass (balancedSchedule n m hfit σ δ ξ) d :=
    (matching_support n m d hn4 hd hdu (by omega) hfit σ δ hδ hδu).1.mono
      (fun _ h => h.1)
  have hsep := balanced_target_separation n m hfit hm δ hδ
  have hdec := separated_prior_decisions n d q r hn4 hd hdu hqr
    (balancedParamLaw m) (balancedParamLaw m)
    (balancedSchedule n m hfit true δ) (balancedSchedule n m hfit false δ)
    (balancedRecord_kernel_measurable n m hfit q r δ hqr true)
    (balancedRecord_kernel_measurable n m hfit q r δ hqr false)
    (balanced_target_measurable n m hfit true δ)
    (balanced_target_measurable n m hfit false δ)
    a (1/256) (1/50) hscale.2 ha1 (by constructor <;> norm_num)
    (hclass true) (hclass false) hsep.1 hsep.2 htv
  constructor
  · refine (ENNReal.ofReal_le_ofReal ?_).trans hdec.1
    have hsquare : (δ/192)^2 ≤ a^2 := by nlinarith [hscale.1]
    nlinarith [sq_nonneg a]
  · refine (ENNReal.ofReal_le_ofReal ?_).trans hdec.2
    linarith [hscale.1, hscale.2]

/-- Given [the stated assumptions](hyp:hqr,hr), [The declared endpoint convention satisfies the same channel moment upper bound.](goal) -/
-- @node: positive_channel_kappa_upper
lemma positive_channel_kappa_upper (q r : ℝ) (hqr : ChannelDomain q r) (hr : 0 < r) :
    kappa q r ≤ 1 + q^2/r := by
  by_cases hr1 : r < 1
  · exact kappa_le_one_add_signal q r hr hr1 hqr.2.1 hqr.2.2
  · have he : r = 1 ∧ q = 1 := by constructor <;> linarith [hqr.2.1, hqr.2.2]
    simp [kappa, he.1, he.2]

/-- Given [the stated assumptions](hyp:hqr,hr), [Inverting the moment bound retains at least half of the truncated false-edge rate.](goal) -/
-- @node: false_rate_le_two_over_kappa
lemma false_rate_le_two_over_kappa (q r : ℝ) (hqr : ChannelDomain q r) (hr : 0 < r) :
    min 1 (r/q^2) * kappa q r ≤ 2 := by
  have hq : 0 < q := hr.trans_le hqr.2.1
  have hq2 : 0 < q^2 := sq_pos_of_pos hq
  have hk := positive_channel_kappa_upper q r hqr hr
  have hkr : kappa q r * r ≤ r + q^2 := by
    have := (mul_le_mul_of_nonneg_right hk hr.le)
    field_simp at this
    nlinarith
  by_cases hB : r ≤ q^2
  · rw [min_eq_right ((div_le_one hq2).mpr hB)]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hq2).mpr
    nlinarith
  · rw [min_eq_left ((one_le_div hq2).mpr (le_of_not_ge hB)), one_mul]
    have hratio : q^2/r ≤ 1 := (div_le_one hr).mpr (le_of_not_ge hB)
    linarith

/-- Given [the stated assumptions](hyp:hqr,hr), [The calibrated amplitude controls the false-edge rate with a constant strong
enough for the final three-cost assembly.](goal) -/
-- @node: calibrated_false_rate_bounds
lemma calibrated_false_rate_bounds (q r : ℝ) (hqr : ChannelDomain q r) (hr : 0 < r) :
    let δ := 1/(100*Real.pi*Real.sqrt (kappa q r))
    let k := 1/(4*10^9*Real.pi^2)
    k * min 1 (r/q^2) ≤ δ^2/147456 ∧
    k * Real.sqrt (min 1 (r/q^2)) ≤ δ/192 := by
  dsimp only
  let δ := 1/(100*Real.pi*Real.sqrt (kappa q r))
  let k := 1/(4*10^9*Real.pi^2)
  let t := min 1 (r/q^2)
  have hκ : 0 < kappa q r := lt_of_lt_of_le (by norm_num)
    (kappa_ge_one_of_positive q r hr hqr.2.1 hqr.2.2)
  have hs : 0 < Real.sqrt (kappa q r) := Real.sqrt_pos.mpr hκ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have ht : 0 ≤ t := le_min (by norm_num) (by positivity)
  have htk : t * kappa q r ≤ 2 := false_rate_le_two_over_kappa q r hqr hr
  have hidentity : δ^2 * kappa q r = 1/(10000*Real.pi^2) := by
    dsimp [δ]
    have hsquare := Real.sq_sqrt hκ.le
    field_simp
    nlinarith [hsquare]
  have hc : 2*k ≤ (1/(10000*Real.pi^2))/147456 := by
    dsimp [k]
    rw [← mul_div_assoc, mul_one, div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hrisk : k*t ≤ δ^2/147456 := by
    apply (mul_le_mul_iff_right₀ hκ).mp
    calc
      kappa q r * (k*t) = k*(t*kappa q r) := by ring
      _ ≤ k*2 := mul_le_mul_of_nonneg_left htk hk.le
      _ ≤ (1/(10000*Real.pi^2))/147456 := by linarith [hc]
      _ = kappa q r * (δ^2/147456) := by rw [← hidentity]; ring
  have hk4 : k ≤ 4 := by
    dsimp [k]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hsquare : (k * Real.sqrt t)^2 ≤ (δ/192)^2 := by
    rw [mul_pow, Real.sq_sqrt ht]
    have hkt : 0 ≤ k*t := mul_nonneg hk.le ht
    have hmul := mul_le_mul_of_nonneg_right hk4 hkt
    nlinarith [hrisk]
  change k*t ≤ δ^2/147456 ∧ k*Real.sqrt t ≤ δ/192
  exact ⟨hrisk, (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare⟩

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr,hr,hregime), [The calibrated planted matching tests yield both false-positive lower bounds,
with the stronger constant used in the paper's final numerical assembly.](goal) -/
-- @node: matching_false_positive_lower
lemma matching_false_positive_lower (n d : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (q r : ℝ) (hqr : ChannelDomain q r) (hr : 0 < r)
    (hregime : q/2 ≤ (n/2 : ℕ)*r) :
    ENNReal.ofReal ((1/(4*10^9*Real.pi^2)) * min 1 (r/q^2)) ≤
      minimaxRisk (noisyDesign (V := Fin n) q r) d ∧
    ENNReal.ofReal ((1/(4*10^9*Real.pi^2)) * Real.sqrt (min 1 (r/q^2))) ≤
      minimaxLength (noisyDesign (V := Fin n) q r) d := by
  let δ := 1/(100*Real.pi*Real.sqrt (kappa q r))
  have hκ1 := kappa_ge_one_of_positive q r hr hqr.2.1 hqr.2.2
  have hs1 : 1 ≤ Real.sqrt (kappa q r) := by
    simpa using Real.sqrt_le_sqrt hκ1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδu : δ ≤ 1/12 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hatoms := noisyDesign_atoms (V := Fin n) q r hqr
  have htv := (marked_contraction n (n/2) (by omega) (by omega) (by omega)
    q r δ hr hqr.2.1 hqr.2.2 hδ hδu (noisyDesign q r)
    hatoms.1 hatoms.2.1 hatoms.2.2).2.2.2.2 hregime rfl
  have hdec := matching_decision_lower n d hn hd hdu q r δ hqr hδ hδu htv.le
  have hcal := calibrated_false_rate_bounds q r hqr hr
  exact ⟨(ENNReal.ofReal_le_ofReal hcal.1).trans hdec.1,
    (ENNReal.ofReal_le_ofReal hcal.2).trans hdec.2⟩

end CausalSmith.Experimentation.NoisygraphTtePrecision
