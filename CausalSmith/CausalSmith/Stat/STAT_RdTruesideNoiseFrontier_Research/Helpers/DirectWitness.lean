module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.WitnessModel

/-!
# Direct bump witness legality

The clipped linear bump has the global modulus required by the direct-reduction
roadmap. Its Bernoulli perturbations belong to the same latent model class at
every noise scale, and their cutoff targets have the stated separation.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Both clipping operations contract distance, giving the global direct-bump Lipschitz bound. Given [the displayed inputs and assumptions](hyp:h,hh,x,t), [the stated mathematical conclusion holds](goal). -/
lemma directBump_lipschitz_bound (h : ℝ) (hh : 0 < h) (x t : ℝ) :
    |directBump h x - directBump h t| ≤ |x-t| / h := by
  rw [directBump_eq_clipped h hh x, directBump_eq_clipped h hh t]
  calc
    _ ≤ |(1 - max x 0 / h) - (1 - max t 0 / h)| :=
      abs_max_sub_max_le_abs _ _ 0
    _ = |max x 0 - max t 0| / h := by
      rw [show (1 - max x 0 / h) - (1 - max t 0 / h) =
        -( (max x 0 - max t 0) / h) by ring, abs_neg, abs_div, abs_of_pos hh]
    _ ≤ |x-t| / h := div_le_div_of_nonneg_right (abs_max_sub_max_le_abs x t 0) hh.le

/-- The full bump has oscillation at most one, including on the negative half-line. Given [the displayed inputs and assumptions](hyp:h,hh,x,t), [the stated mathematical conclusion holds](goal). -/
lemma directBump_oscillation_le_one (h : ℝ) (hh : 0 < h) (x t : ℝ) :
    |directBump h x - directBump h t| ≤ 1 := by
  have hx := directBump_mem h hh x
  have ht := directBump_mem h hh t
  exact abs_le.mpr ⟨by linarith [hx.1, ht.2], by linarith [hx.2, ht.1]⟩

/-- The unit oscillation and Lipschitz bound interpolate to the roadmap's fractional modulus. Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh,x,t), [the stated mathematical conclusion holds](goal). -/
lemma directBump_holder_pointwise (β h : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (hh : 0 < h) (x t : ℝ) :
    |directBump h x - directBump h t| ≤ h^(-β) * |x-t|^β := by
  by_cases he : x = t
  · subst t
    simp only [sub_self, abs_zero]
    positivity
  have hd : 0 < |x-t| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hz : 0 < |x-t| / h := div_pos hd hh
  have hid : (|x-t| / h)^β = h^(-β) * |x-t|^β := by
    rw [Real.div_rpow (abs_nonneg _) hh.le, Real.rpow_neg hh.le]
    ring
  rw [← hid]
  by_cases hs : |x-t| / h ≤ 1
  · exact (directBump_lipschitz_bound h hh x t).trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hz hs hβ.2)
  · exact (directBump_oscillation_le_one h hh x t).trans
      (Real.one_le_rpow (le_of_not_ge hs) hβ.1.le)

/-- The small direct perturbations stay inside the benchmark's mean interval everywhere. Given [the displayed inputs and assumptions](hyp:β,h,s,hβ,hh,x), [the stated mathematical conclusion holds](goal). -/
lemma directProbability_mean_bounds (β h : ℝ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    directProbability β h s x ∈ Icc (1/4 : ℝ) (3/4) := by
  have hv := directBump_mem h hh.1 x
  have hp0 := Real.rpow_nonneg hh.1.le β
  have hp1 := Real.rpow_le_one hh.1.le hh.2 hβ.1.le
  have hprod0 := mul_nonneg hp0 hv.1
  have hprod1 : h^β * directBump h x ≤ 1 := by
    simpa using mul_le_mul hp1 hv.2 hv.1 (by norm_num : (0 : ℝ) ≤ 1)
  cases s <;> simp only [directProbability, witnessSign, Bool.false_eq_true, if_false, if_true, kappa]
  all_goals constructor <;> nlinarith [hprod0, hprod1]

/-- Scaling the bump cancels its Hölder resolution factor, giving a modulus at most kappa. Given [the displayed inputs and assumptions](hyp:β,h,s,hβ,hh,x,t), [the stated mathematical conclusion holds](goal). -/
lemma directProbability_holder (β h : ℝ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hh : 0 < h) (x t : ℝ) :
    |directProbability β h s x - directProbability β h s t| ≤ kappa * |x-t|^β := by
  have hp0 := Real.rpow_nonneg hh.le β
  have hcancel : h^β * h^(-β) = 1 := by
    rw [← Real.rpow_add hh]
    simp
  have hv := directBump_holder_pointwise β h hβ hh x t
  have hsign : |witnessSign s| = 1 := by cases s <;> norm_num [witnessSign]
  rw [show directProbability β h s x - directProbability β h s t =
    witnessSign s * kappa * h^β * (directBump h x - directBump h t) by
      unfold directProbability; ring, abs_mul, abs_mul, abs_mul, hsign,
    abs_of_nonneg hp0, abs_of_nonneg (by norm_num [kappa] : 0 ≤ kappa), one_mul]
  calc
    _ ≤ kappa * h^β * (h^(-β) * |x-t|^β) :=
      mul_le_mul_of_nonneg_left hv (by unfold kappa; positivity)
    _ = kappa * (h^β * h^(-β)) * |x-t|^β := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- Each direct latent witness satisfies every model atom at every noise scale. Given [the displayed inputs and assumptions](hyp:β,h,σ,s,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_model (β h σ : ℝ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) 1) :
    Model β σ (directAltLaw β h s hβ hh) := by
  have hp := directProbability_properties β h s hβ hh
  constructor
  · exact witnessMeasure_error _ hp.1 hp.2.2
  · exact witnessMeasure_error_independent _ hp.1 hp.2.2
  · intro x hx
    change 1/4 ≤ uniformDensity x ∧ uniformDensity x ≤ 3/4
    norm_num [uniformDensity, hx]
  · intro d x hx
    change witnessMu (directProbability β h s) d x ∈ Icc (1/4 : ℝ) (3/4)
    cases d
    · norm_num [witnessMu]
    · exact directProbability_mean_bounds β h s hβ hh x
  · intro d x hx t ht
    change |witnessMu (directProbability β h s) d x -
      witnessMu (directProbability β h s) d t| ≤ _
    cases d
    · simp only [witnessMu, Bool.false_eq_true, if_false, sub_self, abs_zero]
      positivity
    · exact (directProbability_holder β h s hβ hh.1 x t).trans
        (mul_le_mul_of_nonneg_right (by norm_num [kappa] : kappa ≤ 2)
          (Real.rpow_nonneg (abs_nonneg _) _))

/-- The direct witness's causal target is its signed cutoff perturbation. Given [the displayed inputs and assumptions](hyp:β,h,s,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_theta (β h : ℝ) (s : Bool)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) 1) :
    theta (directAltLaw β h s hβ hh) = witnessSign s * kappa * h^β := by
  simp [theta, directAltLaw, bernoulliWitness, witnessMu, directProbability, directBump]

/-- The direct alternatives have the target separation used by the two-point argument. Given [the displayed inputs and assumptions](hyp:β,h,hβ,hh), [the stated mathematical conclusion holds](goal). -/
lemma directAltLaw_separation (β h : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) 1) :
    |theta (directAltLaw β h true hβ hh) - theta (directAltLaw β h false hβ hh)| =
      2 * kappa * h^β := by
  rw [directAltLaw_theta, directAltLaw_theta]
  have hp0 := Real.rpow_nonneg hh.1.le β
  norm_num only [witnessSign, if_true, Bool.false_eq_true, if_false]
  rw [show 1 * kappa * h^β - -1 * kappa * h^β = 2 * kappa * h^β by ring,
    abs_of_nonneg (by unfold kappa; positivity)]

/-- On its positive support the direct bump is exactly the declining linear segment. Given [the displayed inputs and assumptions](hyp:h,hh,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma directBump_eq_linear_on (h : ℝ) (hh : 0 < h) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) h) : directBump h x = 1-x/h := by
  rw [directBump, if_neg (not_lt.mpr hx.1), max_eq_left]
  have hd : x/h ≤ 1 := (div_le_one hh).mpr hx.2
  linarith

/-- The direct bump vanishes to the right of its positive support. Given [the displayed inputs and assumptions](hyp:h,hh,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma directBump_eq_zero_of_width_le (h : ℝ) (hh : 0 < h) {x : ℝ}
    (hx : h ≤ x) : directBump h x = 0 := by
  rw [directBump, if_neg (not_lt.mpr (hh.le.trans hx)), max_eq_right]
  have hd : 1 ≤ x/h := (le_div_iff₀ hh).mpr (by simpa using hx)
  linarith

/-- The direct bump has squared mass h/3 on its support, as used in DR.1. Given [the displayed inputs and assumptions](hyp:h,hh), [the stated mathematical conclusion holds](goal). -/
lemma directBump_sq_integral_support (h : ℝ) (hh : 0 < h) :
    (∫ x in (0 : ℝ)..h, (directBump h x)^2) = h/3 := by
  have he : (∫ x in (0 : ℝ)..h, (directBump h x)^2) =
      ∫ x in (0 : ℝ)..h, (1-x/h)^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (directBump h x)^2 = (1-x/h)^2
    rw [directBump_eq_linear_on h hh (by
      simpa only [uIcc_of_le hh.le] using hx)]
  rw [he]
  have hc := intervalIntegral.integral_comp_sub_div (fun x : ℝ => x^2)
    (a := 0) (b := h) (ne_of_gt hh) 1
  norm_num [integral_pow, hh.ne', smul_eq_mul] at hc ⊢
  simpa only [div_eq_mul_inv, one_mul] using hc

/-- Integrating over the whole treated arm gives the same squared mass, with no tail truncation. Given [the displayed inputs and assumptions](hyp:h,hh), [the stated mathematical conclusion holds](goal). -/
lemma directBump_sq_integral_arm (h : ℝ) (hh : h ∈ Ioc (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, (directBump h x)^2) = h/3 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => (directBump h x)^2) volume a b := by
    intro a b
    exact ((directBump_continuous h hh.1).pow 2).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 h) (hi h 1),
    directBump_sq_integral_support h hh.1]
  have hz : (∫ x in h..(1 : ℝ), (directBump h x)^2) = 0 := by
    calc
      _ = ∫ x in h..(1 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : h ≤ x := (uIcc_of_le hh.2 ▸ hx).1
        change (directBump h x)^2 = 0
        rw [directBump_eq_zero_of_width_le h hh.1 hx', zero_pow (by norm_num : 2 ≠ 0)]
      _ = 0 := by simp
  rw [hz, add_zero]

end CausalSmith.Stat.RdTruesideNoiseFrontier
