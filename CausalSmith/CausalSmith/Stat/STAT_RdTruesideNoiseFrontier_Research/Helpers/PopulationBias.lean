module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Covariance
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.TwoPoint

/-!
# Population endpoint-kernel bias

Positive normalized kernels preserve density and mean bounds, and the mean
Hölder condition gives the population ratio bias in FC.2–FC.3.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- A normalized positive endpoint kernel preserves pointwise density bounds (FC.2). Given [the displayed inputs and assumptions](hyp:L,hL,f,hf,a,b,hbounds), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_weighted_integral_bounds (L : ℕ) (hL : 1 ≤ L)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (a b : ℝ)
    (hbounds : ∀ x ∈ Icc (0 : ℝ) 1, a ≤ f x ∧ f x ≤ b) :
    a ≤ (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x) ∧
      (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x) ≤ b := by
  have hK : ContinuousOn (fun x => (endpointKernel L).eval x) (Icc (0 : ℝ) 1) := by
    fun_prop
  have hi := (hK.mul hf).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1) (μ := volume)
  have hia := (hK.mul (continuousOn_const (c := a))).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1) (μ := volume)
  have hib := (hK.mul (continuousOn_const (c := b))).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1) (μ := volume)
  have hlo := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hia hi
    (fun x hx => mul_le_mul_of_nonneg_left (hbounds x hx).1 (endpointKernel_nonneg L x hx))
  have hhi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi hib
    (fun x hx => mul_le_mul_of_nonneg_left (hbounds x hx).2 (endpointKernel_nonneg L x hx))
  simpa only [Pi.mul_apply, intervalIntegral.integral_mul_const, endpointKernel_integral_one L hL, one_mul]
    using And.intro hlo hhi

/-- Reflecting either arm sends its unit interval into the full latent score interval. Given [the displayed inputs and assumptions](hyp:d,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma arm_reflection_mem (d : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    sgn d * x ∈ Icc (-1 : ℝ) 1 := by
  cases d <;> simp only [sgn, Bool.false_eq_true, if_false, if_true, neg_one_mul, one_mul]
  all_goals constructor <;> linarith [hx.1, hx.2]

/-- Continuous latent versions stay continuous after restriction and arm reflection. Given [the displayed inputs and assumptions](hyp:d,f,hf), [the stated mathematical conclusion holds](goal). -/
lemma continuousOn_arm_reflection (d : Bool) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    ContinuousOn (fun x => f (sgn d * x)) (Icc (0 : ℝ) 1) := by
  exact hf.comp (by fun_prop) (fun x hx => arm_reflection_mem d hx)

/-- The FC.1 unmarked integral lies between one quarter and three quarters on either arm. Given [the displayed inputs and assumptions](hyp:P,hP,d,L,hL), [the stated mathematical conclusion holds](goal). -/
lemma arm_kernel_density_bounds (P : LatentLaw) (hP : DensityBounds P)
    (d : Bool) (L : ℕ) (hL : 1 ≤ L) :
    (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * P.f (sgn d * x)) ∈
      Icc (1/4 : ℝ) (3/4) := by
  exact endpointKernel_weighted_integral_bounds L hL _
    (continuousOn_arm_reflection d P.f P.f_cont) _ _
    (fun x hx => hP _ (arm_reflection_mem d hx))

/-- A positive density-weighted kernel average preserves the potential-mean range. Given [the displayed inputs and assumptions](hyp:L,hL,f,v,hf,hv,hfb,hvb), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_weighted_mean_bounds (L : ℕ) (hL : 1 ≤ L)
    (f v : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    (hfb : ∀ x ∈ Icc (0 : ℝ) 1, 1/4 ≤ f x ∧ f x ≤ 3/4)
    (hvb : ∀ x ∈ Icc (0 : ℝ) 1, 1/4 ≤ v x ∧ v x ≤ 3/4) :
    ((∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x * v x) /
      (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x)) ∈
      Icc (1/4 : ℝ) (3/4) := by
  have hK : ContinuousOn (fun x => (endpointKernel L).eval x) (Icc (0 : ℝ) 1) := by
    fun_prop
  have hW := hK.mul hf
  have hB := endpointKernel_weighted_integral_bounds L hL f hf _ _ hfb
  have hBp : 0 < ∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x := by
    linarith [hB.1]
  have hi := (hW.mul hv).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1) (μ := volume)
  have hlo := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ((hW.mul (continuousOn_const (c := (1/4 : ℝ)))).intervalIntegrable_of_Icc (by norm_num))
    hi (fun x hx => mul_le_mul_of_nonneg_left (hvb x hx).1
      (mul_nonneg (endpointKernel_nonneg L x hx) (by linarith [(hfb x hx).1])))
  have hhi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    ((hW.mul (continuousOn_const (c := (3/4 : ℝ)))).intervalIntegrable_of_Icc (by norm_num))
    (fun x hx => mul_le_mul_of_nonneg_left (hvb x hx).2
      (mul_nonneg (endpointKernel_nonneg L x hx) (by linarith [(hfb x hx).1])))
  simp only [Pi.mul_apply, intervalIntegral.integral_mul_const] at hlo hhi
  exact ⟨(le_div_iff₀ hBp).mpr (by simpa only [mul_comm] using hlo),
    (div_le_iff₀ hBp).mpr (by simpa only [mul_comm] using hhi)⟩

/-- The density and Hölder envelopes imply the six-times-moment population bias (FC.3). Given [the displayed inputs and assumptions](hyp:L,hL,β,hβ,f,v,hf,hv,hfb,hmod), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_weighted_mean_bias (L : ℕ) (hL : 1 ≤ L) (β : ℝ) (hβ : 0 ≤ β)
    (f v : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    (hfb : ∀ x ∈ Icc (0 : ℝ) 1, 1/4 ≤ f x ∧ f x ≤ 3/4)
    (hmod : ∀ x ∈ Icc (0 : ℝ) 1, |v x - v 0| ≤ 2 * x ^ β) :
    |(∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x * v x) /
      (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x) - v 0| ≤
        6 * kernelMoment L β := by
  let B := ∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x
  have hB := endpointKernel_weighted_integral_bounds L hL f hf _ _ hfb
  have hBp : 0 < B := by dsimp [B]; linarith [hB.1]
  have hK : ContinuousOn (fun x => (endpointKernel L).eval x) (Icc (0 : ℝ) 1) := by
    fun_prop
  have hW := hK.mul hf
  have hpow : ContinuousOn (fun x : ℝ => x ^ β) (Icc (0 : ℝ) 1) :=
    continuousOn_id.rpow_const (fun x hx => Or.inr hβ)
  have hdiff := hW.mul (hv.sub (continuousOn_const (c := v 0)))
  have hi : IntervalIntegrable (fun x => (endpointKernel L).eval x * f x * v x) volume 0 1 := by
    simpa only [Pi.mul_def] using (hW.mul hv).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hi0 : IntervalIntegrable (fun x => (endpointKernel L).eval x * f x * v 0) volume 0 1 := by
    simpa only [Pi.mul_def] using
      (hW.mul (continuousOn_const (c := v 0))).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hid : (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x * v x) / B - v 0 =
      (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x * (v x - v 0)) / B := by
    rw [show (fun x => (endpointKernel L).eval x * f x * (v x - v 0)) =
        (fun x => (endpointKernel L).eval x * f x * v x -
          (endpointKernel L).eval x * f x * v 0) by funext x; ring]
    -- `integral_linearity` does not normalize this interval integral.
    rw [intervalIntegral.integral_sub hi hi0, intervalIntegral.integral_mul_const]
    have hBn : (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x) ≠ 0 := ne_of_gt hBp
    dsimp [B]
    field_simp [hBn]
  have hnum : |∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * f x * (v x - v 0)| ≤
      (3/2) * kernelMoment L β := by
    apply (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans
    have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hdiff.abs.intervalIntegrable_of_Icc (by norm_num) (μ := volume))
      (((hpow.mul hK).const_mul (3/2)).intervalIntegrable_of_Icc (by norm_num))
      (fun x hx => ?_)
    · simpa only [Pi.mul_apply, Pi.sub_apply, intervalIntegral.integral_const_mul, kernelMoment]
        using hm
    · have hK0 := endpointKernel_nonneg L x hx
      have hf0 : 0 ≤ f x := by linarith [(hfb x hx).1]
      change |(endpointKernel L).eval x * f x * (v x - v 0)| ≤
        (3/2) * (x ^ β * (endpointKernel L).eval x)
      rw [abs_mul, abs_of_nonneg (mul_nonneg hK0 hf0)]
      calc
        _ ≤ ((endpointKernel L).eval x * f x) * (2 * x ^ β) :=
          mul_le_mul_of_nonneg_left (hmod x hx) (mul_nonneg hK0 hf0)
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left (hfb x hx).2
            (mul_nonneg hK0 (Real.rpow_nonneg hx.1 β))
          nlinarith
  have hM : 0 ≤ kernelMoment L β :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1 β) (endpointKernel_nonneg L x hx))
  rw [hid, abs_div, abs_of_pos hBp]
  apply (div_le_iff₀ hBp).mpr
  have hb : 1/4 ≤ B := hB.1
  nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 6 * kernelMoment L β by positivity)]

/-- Each FC.1 weighted potential mean is interior and approximates its cutoff trace (FC.3). Given [the displayed inputs and assumptions](hyp:P,β,σ,hP,hβ,d,L,hL), [the stated mathematical conclusion holds](goal). -/
lemma arm_kernel_mean_bounds_and_bias (P : LatentLaw) (β σ : ℝ)
    (hP : Model β σ P) (hβ : 0 ≤ β) (d : Bool) (L : ℕ) (hL : 1 ≤ L) :
    let a := (∫ x in (0 : ℝ)..1,
        (endpointKernel L).eval x * P.f (sgn d * x) * P.mu d (sgn d * x)) /
      (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x * P.f (sgn d * x))
    a ∈ Icc (1/4 : ℝ) (3/4) ∧ |a - P.mu d 0| ≤ 6 * kernelMoment L β := by
  have hf := continuousOn_arm_reflection d P.f P.f_cont
  have hv := continuousOn_arm_reflection d (P.mu d) (P.mu_cont d)
  have hfb : ∀ x ∈ Icc (0 : ℝ) 1, 1/4 ≤ P.f (sgn d * x) ∧ P.f (sgn d * x) ≤ 3/4 :=
    fun x hx => hP.density _ (arm_reflection_mem d hx)
  constructor
  · exact endpointKernel_weighted_mean_bounds L hL _ _ hf hv hfb
      (fun x hx => hP.means d _ (arm_reflection_mem d hx))
  · have hmod : ∀ x ∈ Icc (0 : ℝ) 1,
        |P.mu d (sgn d * x) - P.mu d (sgn d * 0)| ≤ 2 * x ^ β := by
      intro x hx
      have h := hP.holder d _ (arm_reflection_mem d hx) 0 (by norm_num)
      have habs : |sgn d * x| = x := by
        cases d <;> simp [sgn, abs_of_nonneg hx.1]
      simpa only [mul_zero, sub_zero, habs] using h
    simpa only [mul_zero] using
      endpointKernel_weighted_mean_bias L hL β hβ _ _ hf hv hfb hmod

end CausalSmith.Stat.RdTruesideNoiseFrontier
