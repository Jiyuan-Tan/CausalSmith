module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Estimators
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Public endpoint rates and sequence criteria

The public envelope comparison, endpoint evaluations, and convergence criterion
for the three extended costs.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

open Filter Topology
/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [The public envelope has the required clipped rate comparison.](goal) -/
-- @node: envelope_rate_le
lemma envelope_rate_le (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1)
    (q r : ℝ) (hqr : ChannelDomain q r) : boundedEnvelope n d q r ≤ 20 * rho n d q r := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : 0 ≤ (d : ℝ) := hd1.trans' (by norm_num)
  have hr0 := hqr.1
  have hq1 := hqr.2.2
  have hv1 := (boundedEnvelope_mem_Icc n d q r).2
  by_cases hq0 : 0 < q
  · let w : ℝ := (d : ℝ)^2/n + d/(n*q) + r/q^2
    have hw0 : 0 ≤ w := by dsimp [w]; positivity
    rw [rho, if_pos hq0]
    change boundedEnvelope n d q r ≤ 20 * min 1 w
    by_cases hw1 : 1 ≤ w
    · rw [min_eq_left hw1]
      linarith
    rw [min_eq_right (le_of_not_ge hw1)]
    by_cases hsmall : r ≤ q/2
    · have hgap : 0 < q-r := by linarith
      have hden : q^2/4 ≤ (q-r)^2 := by nlinarith
      have hbase : 5*((d : ℝ)+1)^2/n ≤ 20*((d : ℝ)^2/n) := by
        rw [← mul_div_assoc]
        apply (div_le_div_iff_of_pos_right hn0).mpr
        nlinarith
      have hnum : (d : ℝ)*q*(1-q) + ((n : ℝ)-1)*r*(1-r) ≤
          (d : ℝ)*q + (n : ℝ)*r := by
        have hn1 : 0 ≤ (n : ℝ)-1 := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          linarith
        have hfirst : (d : ℝ)*q*(1-q) ≤ (d : ℝ)*q := by
          nlinarith [mul_nonneg hd0 hq0.le]
        have hsecond : ((n : ℝ)-1)*r*(1-r) ≤ (n : ℝ)*r := by
          nlinarith [mul_nonneg hn1 hr0, mul_nonneg (mul_nonneg hn1 hr0) hr0]
        linarith
      have hacq : 4*((d : ℝ)*q*(1-q)+((n : ℝ)-1)*r*(1-r))/(n*(q-r)^2) ≤
          16*((d : ℝ)*q+(n : ℝ)*r)/(n*q^2) := by
        have hnp : 0 ≤ (d : ℝ)*q+(n : ℝ)*r := by positivity
        apply (div_le_div_iff₀ (by positivity : 0 < (n : ℝ)*(q-r)^2)
          (by positivity : 0 < (n : ℝ)*q^2)).mpr
        have hmult := mul_le_mul_of_nonneg_left hden hnp
        have hmult' := mul_le_mul_of_nonneg_left hnum (sq_nonneg q)
        nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hmult),
          mul_nonneg hn0.le (sub_nonneg.mpr hmult')]
      have hsplit : 16*((d : ℝ)*q+(n : ℝ)*r)/(n*q^2) =
          16*((d : ℝ)/(n*q) + r/q^2) := by
        field_simp
        <;> ring
      have hu : 5*((d : ℝ)+1)^2/n +
          4*((d : ℝ)*q*(1-q)+((n : ℝ)-1)*r*(1-r))/(n*(q-r)^2) ≤ 20*w := by
        rw [hsplit] at hacq
        dsimp [w]
        have hm : 0 ≤ (d : ℝ)/(n*q) + r/q^2 := by positivity
        linarith
      have hu0 : 0 ≤ 5*((d : ℝ)+1)^2/n +
          4*((d : ℝ)*q*(1-q)+((n : ℝ)-1)*r*(1-r))/(n*(q-r)^2) := by
        have hr1 : r ≤ 1 := hqr.2.1.trans hq1
        have hn1 : 0 ≤ (n : ℝ)-1 := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
          linarith
        positivity
      simp only [boundedEnvelope, upperEnvelope, if_pos (show r < q by linarith)]
      rw [ENNReal.toReal_min (by simp) (by simp), ENNReal.toReal_one,
        ENNReal.toReal_ofReal hu0]
      exact (min_le_right _ _).trans hu
    · have hprec : 1/2 ≤ r/q^2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hq0)).mpr
        nlinarith
      have hdeg : 0 ≤ (d : ℝ)^2/n := by positivity
      have hmiss : 0 ≤ (d : ℝ)/(n*q) := by positivity
      have hw : 1/2 ≤ w := by dsimp [w]; linarith
      linarith
  · simp only [rho, if_neg hq0]
    linarith

/-- Given [the stated assumptions](hyp:f), [Clipping a nonnegative extended cost at one preserves convergence to zero.](goal) -/
-- @node: tendsto_clipped_cost_zero_iff
lemma tendsto_clipped_cost_zero_iff {ι : Type*} {l : Filter ι} (f : ι → ℝ≥0∞) :
    Tendsto (fun i => min 1 (f i)) l (𝓝 0) ↔ Tendsto f l (𝓝 0) := by
  constructor
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    have hc : (0 : ℝ≥0∞) < ENNReal.ofReal (1/2) := by norm_num
    have ht : min ε (ENNReal.ofReal (1/2)) < (1 : ℝ≥0∞) :=
      (min_le_right _ _).trans_lt (by norm_num)
    filter_upwards [ENNReal.tendsto_nhds_zero.mp h _ (lt_min hε hc)] with i hi
    exact ((min_le_iff.mp hi).resolve_left (not_le.mpr ht)).trans (min_le_left _ _)
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.mp h ε hε] with i hi
    exact (min_le_right _ _).trans hi

/-- Given [the stated assumptions](hyp:hn,hqr), [The evaluated rate is the clipped sum of the three extended costs, including zero acquisition.](goal) -/
-- @node: rho_eq_clipped_extended_costs
lemma rho_eq_clipped_extended_costs (n d : ℕ) (hn : 4 ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) :
    ENNReal.ofReal (rho n d q r) =
      min 1 (degRatio n d + missRatio n d q + falseRatio q r) := by
  by_cases hq : q = 0
  · simp [rho, degRatio, missRatio, falseRatio, hq]
  · have hqpos : 0 < q := lt_of_le_of_ne (hqr.1.trans hqr.2.1) (Ne.symm hq)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 0 ≤ (d : ℝ)^2 / n := by positivity
    have hb : 0 ≤ (d : ℝ) / (n*q) := by positivity
    have hc : 0 ≤ r/q^2 := div_nonneg hqr.1 (sq_nonneg q)
    simp only [rho, if_pos hqpos, ENNReal.ofReal_min, ENNReal.ofReal_one,
      degRatio, missRatio, falseRatio, if_neg hq]
    rw [ENNReal.ofReal_add (add_nonneg ha hb) hc, ENNReal.ofReal_add ha hb]

/-- Given [the stated assumptions](hyp:hadm), [Along admissible sequences the clipped risk rate vanishes exactly when all three costs vanish.](goal) -/
-- @node: rate_tendsto_iff
lemma rate_tendsto_iff (ds : ℕ → ℕ) (qs rs : ℕ → ℝ) (hadm : AdmissibleSequences ds qs rs) :
    Tendsto (fun n => ENNReal.ofReal (rho n (ds n) (qs n) (rs n))) atTop (𝓝 0) ↔
    Tendsto (fun n => degRatio n (ds n)) atTop (𝓝 0) ∧
    Tendsto (fun n => missRatio n (ds n) (qs n)) atTop (𝓝 0) ∧
    Tendsto (fun n => falseRatio (qs n) (rs n)) atTop (𝓝 0) := by
  let cost := fun n => degRatio n (ds n) + missRatio n (ds n) (qs n) +
    falseRatio (qs n) (rs n)
  have heq : (fun n => ENNReal.ofReal (rho n (ds n) (qs n) (rs n))) =ᶠ[atTop]
      (fun n => min 1 (cost n)) := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    exact rho_eq_clipped_extended_costs n (ds n) hn (qs n) (rs n) (hadm n hn).2
  rw [tendsto_congr' heq, tendsto_clipped_cost_zero_iff]
  constructor
  · intro h
    have subcost (f : ℕ → ℝ≥0∞) (hf : ∀ n, f n ≤ cost n) :
        Tendsto f atTop (𝓝 0) := by
      apply ENNReal.tendsto_nhds_zero.mpr
      intro ε hε
      filter_upwards [ENNReal.tendsto_nhds_zero.mp h ε hε] with n hn
      exact (hf n).trans hn
    refine ⟨subcost _ (fun n => ?_), subcost _ (fun n => ?_), subcost _ (fun n => ?_)⟩
    · exact (le_add_right le_rfl).trans (le_add_right le_rfl)
    · exact (le_add_left le_rfl).trans (le_add_right le_rfl)
    · exact le_add_left le_rfl
  · rintro ⟨ha, hb, hc⟩
    simpa only [add_zero] using (ha.add hb).add hc

/-- Given [the stated assumptions](hyp:hn,hd,hdu), [Missing-only, uninformative, and fully supplied-graph endpoint evaluations.](goal) -/
-- @node: frontier_endpoints
lemma frontier_endpoints (n d : ℕ) (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n-1) :
    (∀ q : ℝ, q ∈ Set.Icc 0 1 → 0 < q →
      rho n d q 0 = min 1 ((d : ℝ)^2/n + d/(n*q))) ∧
    (∀ q : ℝ, q ∈ Set.Icc 0 1 → rho n d q q = 1) ∧
    min 1 ((d : ℝ)^2/n) ≤ rho n d 1 0 ∧
    rho n d 1 0 ≤ 2 * min 1 ((d : ℝ)^2/n) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hdn : 0 ≤ (d : ℝ) / n := div_nonneg hd0 hn0.le
  have hds : (d : ℝ) / n ≤ (d : ℝ)^2 / n := by
    apply div_le_div_of_nonneg_right _ hn0.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq hq0
    simp [rho, hq0]
  · intro q hq
    by_cases hq0 : 0 < q
    · have hprec : 1 ≤ q / q^2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hq0)).mpr
        nlinarith [hq.2]
      have hdeg : 0 ≤ (d : ℝ)^2 / n := by positivity
      have hmiss : 0 ≤ (d : ℝ) / ((n : ℝ)*q) := by positivity
      rw [rho, if_pos hq0, min_eq_left]
      linarith
    · simp [rho, hq0]
  · simp only [rho, zero_lt_one, ↓reduceIte, mul_one, zero_div, add_zero]
    apply le_min
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (le_add_of_nonneg_right hdn)
  · simp only [rho, zero_lt_one, ↓reduceIte, mul_one, zero_div, add_zero]
    by_cases hsmall : (d : ℝ)^2 / n ≤ 1
    · rw [min_eq_right hsmall]
      exact (min_le_right _ _).trans (by linarith)
    · rw [min_eq_left (le_of_not_ge hsmall)]
      exact (min_le_left _ _).trans (by norm_num)

end CausalSmith.Experimentation.NoisygraphTtePrecision
