module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.EmpiricalMoments
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.EmpiricalPopulationBridge
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.EmpiricalPopulationMoments
public import Causalean.Mathlib.Probability.LimitTheorems.Approximation.CharFunBound
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.PopulationBias
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.TwoPoint

/-!
# True-side Gaussian measurement-error endpoint frontier

Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- The denominator floor cannot increase error from a population denominator at least one quarter. Given [the displayed inputs and assumptions](hyp:b,B,hB), [the stated mathematical conclusion holds](goal). -/
lemma denominator_floor_error_le (b B : ℝ) (hB : 1/4 ≤ B) :
    |max b (1/8) - B| ≤ |b - B| := by
  by_cases hb : 1/8 ≤ b
  · rw [max_eq_left hb]
  · have hb' : b ≤ 1/8 := le_of_not_ge hb
    rw [max_eq_right hb', abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith

/-- Projection onto the potential-mean range decreases error from any mean in that range. Given [the displayed inputs and assumptions](hyp:r,a,ha), [the stated mathematical conclusion holds](goal). -/
lemma mean_projection_error_le (r a : ℝ) (ha : a ∈ Icc (1/4 : ℝ) (3/4)) :
    |max (1/4) (min (3/4) r) - a| ≤ |r - a| := by
  have h := (Set.abs_projIcc_sub_projIcc (a := (1/4 : ℝ)) (b := 3/4)
      (c := r) (d := a) (by norm_num))
  change |max (1/4) (min (3/4) r) - max (1/4) (min (3/4) a)| ≤ |r-a| at h
  simpa only [min_eq_right ha.2, max_eq_right ha.1] using h

/-- The floored, clipped ratio obeys the certificate's samplewise eight/six error bound. Given [the displayed inputs and assumptions](hyp:Ahat,Bhat,A,B,a,hB,ha,hA), [the stated mathematical conclusion holds](goal). -/
lemma clipped_ratio_error_le (Ahat Bhat A B a : ℝ)
    (hB : 1/4 ≤ B) (ha : a ∈ Icc (1/4 : ℝ) (3/4)) (hA : A = a*B) :
    |max (1/4) (min (3/4) (Ahat / max Bhat (1/8))) - a| ≤
      8*|Ahat-A| + 6*|Bhat-B| := by
  let H : ℝ := max Bhat (1/8)
  have hH : 1/8 ≤ H := le_max_right _ _
  have hHp : 0 < H := by linarith
  have haabs : |a| ≤ 3/4 := by rw [abs_of_nonneg (by linarith [ha.1])]; exact ha.2
  have hfloor : |H-B| ≤ |Bhat-B| := denominator_floor_error_le Bhat B hB
  apply (mean_projection_error_le _ a ha).trans
  have hid : Ahat/H-a = ((Ahat-A)+a*(B-H))/H := by rw [hA]; field_simp; ring
  rw [hid, abs_div, abs_of_pos hHp]
  apply (div_le_iff₀ hHp).mpr
  have hnum : |(Ahat-A)+a*(B-H)| ≤ |Ahat-A| + (3/4)*|Bhat-B| := by
    calc
      _ ≤ |Ahat-A| + |a*(B-H)| := abs_add_le _ _
      _ = |Ahat-A| + |a| * |H-B| := by rw [abs_mul, abs_sub_comm B H]
      _ ≤ _ := by gcongr
  have hscale : |Ahat-A| + (3/4)*|Bhat-B| ≤
      (8*|Ahat-A| + 6*|Bhat-B|)*H := by
    have hh := mul_le_mul_of_nonneg_left hH
      (show 0 ≤ 8*|Ahat-A| + 6*|Bhat-B| by positivity)
    nlinarith
  exact hnum.trans hscale

/-- The abstract ratio inequality applies to the actual arm averages on every sample. Given [the displayed inputs and assumptions](hyp:d,L,σ,n,s,A,B,a,hB,ha,hA), [the stated mathematical conclusion holds](goal). -/
lemma armRatio_error_le (d : Bool) (L : ℕ) (σ : ℝ) {n : ℕ}
    (s : Sample n) (A B a : ℝ) (hB : 1/4 ≤ B)
    (ha : a ∈ Icc (1/4 : ℝ) (3/4)) (hA : A = a*B) :
    |armRatio d L σ s - a| ≤
      8*|markedAvg d L σ s-A| + 6*|unmarkedAvg d L σ s-B| := by
  exact clipped_ratio_error_le _ _ A B a hB ha hA

/-- Simultaneous average errors and the two population bias bounds give the public error radius.
This is the deterministic assembly of (FC.3)--(FC.4), before any probability bound. Given [the displayed inputs and assumptions](hyp:L,hL,σ,n,z,P,A,B,a,M,t,hB,ha,hA,hbias,hmarked,hunmarked), [the stated mathematical conclusion holds](goal). -/
lemma thetaHat_error_le_of_average_errors (L : ℕ) (hL : 1 ≤ L) (σ : ℝ)
    {n : ℕ} (z : Input n) (P : LatentLaw) (A B a : Bool → ℝ) (M t : ℝ)
    (hB : ∀ d, 1/4 ≤ B d) (ha : ∀ d, a d ∈ Icc (1/4 : ℝ) (3/4))
    (hA : ∀ d, A d = a d * B d)
    (hbias : ∀ d, |a d - P.mu d 0| ≤ 6*M)
    (hmarked : ∀ d, |markedAvg d L σ z.1 - A d| ≤ t)
    (hunmarked : ∀ d, |unmarkedAvg d L σ z.1 - B d| ≤ t) :
    |thetaHat L σ z - theta P| ≤ 12*M + 28*t := by
  have harm (d : Bool) : |armRatio d L σ z.1 - a d| ≤ 14*t := by
    have h := armRatio_error_le d L σ z.1 (A d) (B d) (a d) (hB d) (ha d) (hA d)
    linarith [hmarked d, hunmarked d]
  have hsample : |(armRatio true L σ z.1 - armRatio false L σ z.1) -
      (a true - a false)| ≤ 28*t := by
    calc
      _ = |(armRatio true L σ z.1 - a true) -
          (armRatio false L σ z.1 - a false)| := by congr 1; ring
      _ ≤ |armRatio true L σ z.1 - a true| +
          |armRatio false L σ z.1 - a false| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (armRatio true L σ z.1 - a true) 0
          (armRatio false L σ z.1 - a false)
      _ ≤ _ := by linarith [harm true, harm false]
  have hpopulation : |(a true - a false) - theta P| ≤ 12*M := by
    calc
      _ = |(a true - P.mu true 0) - (a false - P.mu false 0)| := by
        unfold theta
        congr 1
        ring
      _ ≤ |a true - P.mu true 0| + |a false - P.mu false 0| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (a true - P.mu true 0) 0 (a false - P.mu false 0)
      _ ≤ _ := by linarith [hbias true, hbias false]
  rw [thetaHat, if_neg (by omega : L ≠ 0)]
  exact (abs_sub_le _ (a true - a false) _).trans
    (by linarith [hsample, hpopulation])

/-- The two ratio errors and population biases bound the effect error with each empirical
error retained separately, so expectation can be taken before applying moment bounds. Given [the displayed inputs and assumptions](hyp:L,hL,σ,n,z,P,A,B,a,M,hB,ha,hA,hbias), [the stated mathematical conclusion holds](goal). -/
lemma thetaHat_error_le_weighted_errors (L : ℕ) (hL : 1 ≤ L) (σ : ℝ)
    {n : ℕ} (z : Input n) (P : LatentLaw) (A B a : Bool → ℝ) (M : ℝ)
    (hB : ∀ d, 1/4 ≤ B d) (ha : ∀ d, a d ∈ Icc (1/4 : ℝ) (3/4))
    (hA : ∀ d, A d = a d * B d) (hbias : ∀ d, |a d - P.mu d 0| ≤ 6*M) :
    |thetaHat L σ z - theta P| ≤ 12*M +
      8*(|markedAvg true L σ z.1 - A true| + |markedAvg false L σ z.1 - A false|) +
      6*(|unmarkedAvg true L σ z.1 - B true| + |unmarkedAvg false L σ z.1 - B false|) := by
  have harm (d : Bool) := armRatio_error_le d L σ z.1 (A d) (B d) (a d)
    (hB d) (ha d) (hA d)
  have hb (d : Bool) := (abs_sub_le (armRatio d L σ z.1) (a d) (P.mu d 0)).trans
    (add_le_add (harm d) (hbias d))
  rw [thetaHat, if_neg (by omega : L ≠ 0), theta]
  calc
    _ = |(armRatio true L σ z.1 - P.mu true 0) -
        (armRatio false L σ z.1 - P.mu false 0)| := by congr 1; ring
    _ ≤ |armRatio true L σ z.1 - P.mu true 0| +
        |armRatio false L σ z.1 - P.mu false 0| := abs_sub _ _
    _ ≤ _ := by linarith [hb true, hb false]

/-- Normalization prevents the endpoint kernel's squared integral from vanishing. Given [the displayed inputs and assumptions](hyp:L,hL), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_sq_integral_pos (L : ℕ) (hL : 1 ≤ L) :
    0 < ∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2 := by
  have hc : Continuous (fun x : ℝ => (endpointKernel L).eval x) := by fun_prop
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x hx => sq_nonneg _)
  by_contra h
  have hz : (∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2) = 0 := by linarith
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    (by norm_num : (0 : ℝ) ≤ 1) (ae_of_all _ (fun x => sq_nonneg ((endpointKernel L).eval x)))
    ((hc.pow 2).intervalIntegrable 0 1)).mp hz
  have hzero : (fun x : ℝ => (endpointKernel L).eval x) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
    filter_upwards [hae] with x hx
    exact sq_eq_zero_iff.mp hx
  have hnorm := endpointKernel_integral_one L hL
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_congr_ae hzero] at hnorm
  simpa using hnorm

/-- The derivative-order-zero term makes the public variance strictly positive at every
noise scale, including zero; all remaining derivative terms are nonnegative. Given [the displayed inputs and assumptions](hyp:L,hL,σ), [the stated mathematical conclusion holds](goal). -/
lemma kernelVariance_pos (L : ℕ) (hL : 1 ≤ L) (σ : ℝ) : 0 < kernelVariance L σ := by
  have hnonneg (j : ℕ) : 0 ≤ σ^(2*j) / (Nat.factorial j : ℝ) *
      ∫ x in (0 : ℝ)..1, ((polyDeriv j (endpointKernel L)).eval x)^2 := by
    apply mul_nonneg
    · apply div_nonneg _ (by positivity)
      rw [Nat.mul_comm 2 j, pow_mul]
      exact sq_nonneg _
    · exact intervalIntegral.integral_nonneg (by norm_num) (fun x hx => sq_nonneg _)
  have hterm := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (kernelDegree L + 1)) => hnonneg j)
    (show 0 ∈ Finset.range (kernelDegree L + 1) from Finset.mem_range.mpr (by omega))
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    polyDeriv, Function.iterate_zero, id_eq] at hterm
  unfold kernelVariance
  exact mul_pos (by norm_num) ((endpointKernel_sq_integral_pos L hL).trans_le hterm)

/-- Cauchy–Schwarz converts an empirical centered second-moment bound into an absolute
first-moment bound on the normalized experiment (the probabilistic step of FC.6). Given [the displayed inputs and assumptions](hyp:Ω,μ,Z,hZ,v,hsecond), [the stated mathematical conclusion holds](goal). -/
lemma empirical_error_integral_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : MemLp Z 2 μ)
    (v : ℝ) (hsecond : (∫ z, (Z z)^2 ∂μ) ≤ v) :
    (∫ z, |Z z| ∂μ) ≤ Real.sqrt v := by
  have hcs := Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
    μ Z hZ
  simp only [Real.norm_eq_abs, sq_abs] at hcs
  exact hcs.trans (Real.sqrt_le_sqrt hsecond)

/-- Integrating the floored-ratio inequality and using all four empirical second moments
proves FC.6, including samples with an empty treatment arm. Given [the displayed inputs and assumptions](hyp:L,hL,σ,n,P,A,B,a,M,v,hB,ha,hA,hbias,hm,hu,hms,hus), [the stated mathematical conclusion holds](goal). -/
lemma thetaHat_absRisk_le_of_second_moments (L : ℕ) (hL : 1 ≤ L) (σ : ℝ)
    (n : ℕ) (P : LatentLaw) (A B a : Bool → ℝ) (M v : ℝ)
    (hB : ∀ d, 1/4 ≤ B d) (ha : ∀ d, a d ∈ Icc (1/4 : ℝ) (3/4))
    (hA : ∀ d, A d = a d * B d) (hbias : ∀ d, |a d - P.mu d 0| ≤ 6*M)
    (hm : ∀ d, MemLp (fun z : Input n => markedAvg d L σ z.1 - A d) 2 (experiment P σ n))
    (hu : ∀ d, MemLp (fun z : Input n => unmarkedAvg d L σ z.1 - B d) 2 (experiment P σ n))
    (hms : ∀ d, (∫ z : Input n, (markedAvg d L σ z.1 - A d)^2 ∂experiment P σ n) ≤ v)
    (hus : ∀ d, (∫ z : Input n, (unmarkedAvg d L σ z.1 - B d)^2 ∂experiment P σ n) ≤ v) :
    absRisk P σ n (thetaHat L σ) ≤ ENNReal.ofReal (12*M + 28*Real.sqrt v) := by
  letI := experiment_probability P σ n
  let em : Bool → Input n → ℝ := fun d z => |markedAvg d L σ z.1 - A d|
  let eu : Bool → Input n → ℝ := fun d z => |unmarkedAvg d L σ z.1 - B d|
  have him (d : Bool) : Integrable (em d) (experiment P σ n) :=
    ((hm d).integrable (by norm_num)).abs
  have hiu (d : Bool) : Integrable (eu d) (experiment P σ n) :=
    ((hu d).integrable (by norm_num)).abs
  have hbm (d : Bool) : (∫ z, em d z ∂experiment P σ n) ≤ Real.sqrt v :=
    empirical_error_integral_abs_le _ _ (hm d) v (hms d)
  have hbu (d : Bool) : (∫ z, eu d z ∂experiment P σ n) ≤ Real.sqrt v :=
    empirical_error_integral_abs_le _ _ (hu d) v (hus d)
  let G : Input n → ℝ := fun z => 12*M + 8*(em true z + em false z) +
    6*(eu true z + eu false z)
  have hiG : Integrable G (experiment P σ n) := by
    exact ((integrable_const (12*M)).add ((him true).add (him false) |>.const_mul 8)).add
      ((hiu true).add (hiu false) |>.const_mul 6)
  have he (z : Input n) : |thetaHat L σ z - theta P| ≤ G z :=
    thetaHat_error_le_weighted_errors L hL σ z P A B a M hB ha hA hbias
  have hGn : ∀ᵐ z ∂experiment P σ n, 0 ≤ G z :=
    ae_of_all _ (fun z => (abs_nonneg _).trans (he z))
  unfold absRisk
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (G z) ∂experiment P σ n :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (he z))
    _ = ENNReal.ofReal (∫ z, G z ∂experiment P σ n) :=
      (ofReal_integral_eq_lintegral_ofReal hiG hGn).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      dsimp only [G]
      integral_linearity
      simp only [integral_const, probReal_univ, one_smul]
      linarith [hbm true, hbm false, hbu true, hbu false]

/-- A target in the parameter range remains covered after intersecting a centered interval
with that range. This is the deterministic coverage step of the finite certificate. Given [the displayed inputs and assumptions](hyp:β,n,σ,L,z,θ,hθ,herr), [the stated mathematical conclusion holds](goal). -/
lemma polyInterval_covers_of_error_le (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ)
    (z : Input n) (θ : ℝ) (hθ : θ ∈ Icc (-1 : ℝ) 1)
    (herr : |thetaHat L σ z - θ| ≤ radius β n σ L) :
    z ∈ Causalean.Stat.coverageEvent (polyInterval β n σ L).lo
      (polyInterval β n σ L).hi θ := by
  have he := abs_le.mp herr
  change max (-1) (thetaHat L σ z - radius β n σ L) ≤ θ ∧
    θ ≤ min 1 (thetaHat L σ z + radius β n σ L)
  exact ⟨max_le hθ.1 (by linarith [he.2]), le_min hθ.2 (by linarith [he.1])⟩

/-- Chebyshev at the public forty-times-variance threshold bounds one failure by 1/40. Given [the displayed inputs and assumptions](hyp:Ω,μ,Z,hZ,hmean,v,hv,hvar), [the stated mathematical conclusion holds](goal). -/
lemma centered_error_failure_le_one_fortieth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZ : MemLp Z 2 μ) (hmean : (∫ z, Z z ∂μ) = 0) (v : ℝ)
    (hv : 0 < v) (hvar : variance Z μ ≤ v) :
    μ.real {z | Real.sqrt (40*v) < |Z z|} ≤ 1/40 := by
  have ht : 0 < Real.sqrt (40*v) := Real.sqrt_pos.mpr (by positivity)
  have hcheb := meas_ge_le_variance_div_sq hZ ht
  simp only [hmean, sub_zero, Real.sq_sqrt (by positivity : 0 ≤ 40*v)] at hcheb
  have hbound : variance Z μ / (40*v) ≤ 1/40 := by
    apply (div_le_iff₀ (by positivity : 0 < 40*v)).mpr
    nlinarith [hvar]
  have hsub : {z | Real.sqrt (40*v) < |Z z|} ⊆
      {z | Real.sqrt (40*v) ≤ |Z z|} := by
    intro z hz
    change Real.sqrt (40*v) < |Z z| at hz
    change Real.sqrt (40*v) ≤ |Z z|
    exact hz.le
  have hm : μ {z | Real.sqrt (40*v) < |Z z|} ≤ ENNReal.ofReal (1/40) :=
    (measure_mono hsub).trans
      (hcheb.trans (ENNReal.ofReal_le_ofReal hbound))
  exact (ENNReal.toReal_mono (by finiteness) hm).trans (by norm_num)

/-- The union bound for four measurable errors gives simultaneous control with probability 0.9. Given [the displayed inputs and assumptions](hyp:Ω,μ,Z,hZ,t,hfail), [the stated mathematical conclusion holds](goal). -/
lemma four_errors_probability_ge_nine_tenths {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Bool × Bool → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (t : ℝ)
    (hfail : ∀ i, μ.real {z | t < |Z i z|} ≤ 1/40) :
    (9/10 : ℝ) ≤ μ.real {z | ∀ i, |Z i z| ≤ t} := by
  let F : Set Ω := ⋃ i, {z | t < |Z i z|}
  have hF : MeasurableSet F := MeasurableSet.iUnion
    (fun i => measurableSet_lt measurable_const (hZ i).abs)
  have hsum : μ.real F ≤ 1/10 := by
    have hu := measureReal_iUnion_fintype_le (μ := μ) (fun i => {z | t < |Z i z|})
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfail i)
    have hc : (∑ i : Bool × Bool, (1/40 : ℝ)) = 1/10 := by norm_num
    exact hu.trans (hc ▸ hs)
  have hgood : {z | ∀ i, |Z i z| ≤ t} = Fᶜ := by
    ext z
    simp [F, not_lt]
  rw [hgood, measureReal_compl hF, probReal_univ]
  linarith

/-- Given [the displayed inputs and assumptions](hyp:d,n,L,σ), [the stated mathematical conclusion holds](goal). -/
@[fun_prop]
lemma markedAvg_input_measurable (d : Bool) (n L : ℕ) (σ : ℝ) :
    Measurable (fun z : Input n => markedAvg d L σ z.1) := by
  have hbit : Measurable bit := measurable_of_countable bit
  have hcell (i : Fin n) :
      Measurable (fun z : Input n => if (z.1 i).2.1 = d then (1 : ℝ) else 0) := by
    exact (measurable_of_countable (fun y : Bool => if y = d then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply i).comp measurable_fst |>.snd.fst)
  unfold markedAvg
  fun_prop

/-- Given [the displayed inputs and assumptions](hyp:d,n,L,σ), [the stated mathematical conclusion holds](goal). -/
@[fun_prop]
lemma unmarkedAvg_input_measurable (d : Bool) (n L : ℕ) (σ : ℝ) :
    Measurable (fun z : Input n => unmarkedAvg d L σ z.1) := by
  have hcell (i : Fin n) :
      Measurable (fun z : Input n => if (z.1 i).2.1 = d then (1 : ℝ) else 0) := by
    exact (measurable_of_countable (fun y : Bool => if y = d then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply i).comp measurable_fst |>.snd.fst)
  unfold unmarkedAvg
  fun_prop

/-- The four empirical-average failure bounds and population bias imply finite-sample coverage.
This assembles the probability and deterministic steps after FC.1 and FC.5 are established. Given [the displayed inputs and assumptions](hyp:β,σ,n,L,hL,P,A,B,a,hB,ha,hA,hbias,hθ,hfm,hfu), [the stated mathematical conclusion holds](goal). -/
lemma polyInterval_coverage_of_average_failure_bounds (β σ : ℝ) (n L : ℕ)
    (hL : 1 ≤ L) (P : LatentLaw) (A B a : Bool → ℝ)
    (hB : ∀ d, 1/4 ≤ B d) (ha : ∀ d, a d ∈ Icc (1/4 : ℝ) (3/4))
    (hA : ∀ d, A d = a d * B d)
    (hbias : ∀ d, |a d - P.mu d 0| ≤ 6 * kernelMoment L β)
    (hθ : theta P ∈ Icc (-1 : ℝ) 1)
    (hfm : ∀ d, (experiment P σ n).real {z : Input n |
      Real.sqrt (40 * kernelVariance L σ / n) < |markedAvg d L σ z.1 - A d|} ≤ 1/40)
    (hfu : ∀ d, (experiment P σ n).real {z : Input n |
      Real.sqrt (40 * kernelVariance L σ / n) < |unmarkedAvg d L σ z.1 - B d|} ≤ 1/40) :
    (9/10 : ℝ) ≤ (experiment P σ n).real
      (Causalean.Stat.coverageEvent (polyInterval β n σ L).lo
        (polyInterval β n σ L).hi (theta P)) := by
  letI := experiment_probability P σ n
  let Z : Bool × Bool → Input n → ℝ := fun i z =>
    if i.1 then markedAvg i.2 L σ z.1 - A i.2
      else unmarkedAvg i.2 L σ z.1 - B i.2
  have hZ (i : Bool × Bool) : Measurable (Z i) := by
    rcases i with ⟨k, d⟩
    cases k
    · exact (unmarkedAvg_input_measurable d n L σ).sub measurable_const
    · exact (markedAvg_input_measurable d n L σ).sub measurable_const
  have hfail (i : Bool × Bool) : (experiment P σ n).real
      {z | Real.sqrt (40 * kernelVariance L σ / n) < |Z i z|} ≤ 1/40 := by
    rcases i with ⟨k, d⟩
    cases k
    · exact hfu d
    · exact hfm d
  apply (four_errors_probability_ge_nine_tenths (experiment P σ n) Z hZ _ hfail).trans
  apply measureReal_mono (h₂ := by finiteness)
  intro z hz
  apply polyInterval_covers_of_error_le β n σ L z (theta P) hθ
  have he := thetaHat_error_le_of_average_errors L hL σ z P A B a
    (kernelMoment L β) (Real.sqrt (40 * kernelVariance L σ / n)) hB ha hA hbias
    (fun d => hz (true, d)) (fun d => hz (false, d))
  simpa only [radius, if_neg (by omega : L ≠ 0)] using he

/-- Intersecting the centered public interval with the target range can only shorten it. Given [the displayed inputs and assumptions](hyp:β,n,σ,L,z), [the stated mathematical conclusion holds](goal). -/
lemma polyInterval_length_le (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) (z : Input n) :
    Causalean.Stat.intervalLength ((polyInterval β n σ L).lo z)
      ((polyInterval β n σ L).hi z) ≤ 2 * radius β n σ L := by
  have hr := radius_nonneg β n σ L
  change max 0 (min 1 (thetaHat L σ z + radius β n σ L) -
    max (-1) (thetaHat L σ z - radius β n σ L)) ≤ 2 * radius β n σ L
  apply max_le
  · linarith
  · have hu := min_le_right (1 : ℝ) (thetaHat L σ z + radius β n σ L)
    have hl := le_max_right (-1 : ℝ) (thetaHat L σ z - radius β n σ L)
    linarith

/-- The sample experiment is normalized, so a pointwise radius bound also bounds expected length. Given [the displayed inputs and assumptions](hyp:β,n,σ,L,P), [the stated mathematical conclusion holds](goal). -/
lemma polyInterval_expectedLength_le (β : ℝ) (n : ℕ) (σ : ℝ) (L : ℕ) (P : LatentLaw) :
    expectedLength P σ n (polyInterval β n σ L) ≤
      ENNReal.ofReal (2 * radius β n σ L) := by
  letI := experiment_probability P σ n
  unfold expectedLength
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal (2 * radius β n σ L) ∂experiment P σ n := by
      apply lintegral_mono
      intro z
      exact ENNReal.ofReal_le_ofReal (polyInterval_length_le β n σ L z)
    _ = _ := by simp

/-- Deterministic public selection preserves the uniform twice-radius length bound, including index zero. Given [the displayed inputs and assumptions](hyp:β,n,σ), [the stated mathematical conclusion holds](goal). -/
lemma attainerLength_le_certificate (β : ℝ) (n : ℕ) (σ : ℝ) :
    attainerLength β n σ ≤ ENNReal.ofReal (2 * certificate β n σ) := by
  unfold attainerLength
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro P
  exact polyInterval_expectedLength_le β n σ (selectedDegree β n σ) P.val

/-- The selected index minimizes the radius over the finite public candidate set. Given [the displayed inputs and assumptions](hyp:β,n,σ,J,hJ), [the stated mathematical conclusion holds](goal). -/
lemma selectedDegree_radius_le (β : ℝ) (n : ℕ) (σ : ℝ) (J : ℕ)
    (hJ : J ≤ Lmax β n) : radius β n σ (selectedDegree β n σ) ≤ radius β n σ J := by
  classical
  have hm := Finset.min'_mem (minimizingDegrees β n σ) (minimizingDegrees_nonempty β n σ)
  simp only [minimizingDegrees, Finset.mem_filter] at hm
  exact hm.2 J (Finset.mem_range.mpr (by omega))

/-- The fallback candidate caps the selected certificate at one half. Given [the displayed inputs and assumptions](hyp:β,n,σ), [the stated mathematical conclusion holds](goal). -/
lemma certificate_le_half (β : ℝ) (n : ℕ) (σ : ℝ) : certificate β n σ ≤ 1/2 := by
  simpa only [certificate, radius, ite_true] using
    selectedDegree_radius_le β n σ 0 (Nat.zero_le _)

/-- The constant fallback interval covers every model target on every sample. Given [the displayed inputs and assumptions](hyp:β,σ,n,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma polyInterval_zero_coverage (β σ : ℝ) (n : ℕ) (P : LatentLaw)
    (hP : Model β σ P) :
    (experiment P σ n).real (Causalean.Stat.coverageEvent
      (polyInterval β n σ 0).lo (polyInterval β n σ 0).hi (theta P)) = 1 := by
  letI := experiment_probability P σ n
  have ht := abs_le.mp (theta_model_bounds β σ P hP)
  have he : Causalean.Stat.coverageEvent
      (polyInterval β n σ 0).lo (polyInterval β n σ 0).hi (theta P) = univ := by
    ext z
    simp only [Causalean.Stat.coverageEvent, mem_setOf_eq, mem_Icc, mem_univ, iff_true]
    change max (-1) (thetaHat 0 σ z - radius β n σ 0) ≤ theta P ∧
      theta P ≤ min 1 (thetaHat 0 σ z + radius β n σ 0)
    simp only [thetaHat, radius, ite_true]
    exact ⟨max_le (by linarith [ht.1]) (by linarith [ht.1]),
      le_min (by linarith [ht.2]) (by linarith [ht.2])⟩
  rw [he, probReal_univ]

/-- The zero estimator has risk at most the fallback radius, including an empty sample. Given [the displayed inputs and assumptions](hyp:β,σ,n,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma thetaHat_zero_absRisk_le (β σ : ℝ) (n : ℕ) (P : LatentLaw)
    (hP : Model β σ P) : absRisk P σ n (thetaHat 0 σ) ≤ ENNReal.ofReal (1/2 : ℝ) := by
  letI := experiment_probability P σ n
  unfold absRisk
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal (1/2 : ℝ) ∂experiment P σ n := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      simpa only [thetaHat, ite_true, zero_sub, abs_neg] using theta_model_bounds β σ P hP
    _ = _ := by simp

/-- Public deterministic selection preserves positive-degree honesty and fallback coverage. Given [the displayed inputs and assumptions](hyp:β,σ,n,hpositive), [the stated mathematical conclusion holds](goal). -/
lemma honestAttainer_of_positive_coverage (β σ : ℝ) (n : ℕ)
    (hpositive : ∀ L, 1 ≤ L → ∀ P, Model β σ P →
      (9/10 : ℝ) ≤ (experiment P σ n).real (Causalean.Stat.coverageEvent
        (polyInterval β n σ L).lo (polyInterval β n σ L).hi (theta P))) :
    honestAttainer β n σ ∈ honestIntervals β n σ := by
  intro P hP
  change (9/10 : ℝ) ≤ (experiment P σ n).real (Causalean.Stat.coverageEvent
    (polyInterval β n σ (selectedDegree β n σ)).lo
    (polyInterval β n σ (selectedDegree β n σ)).hi (theta P))
  by_cases hz : selectedDegree β n σ = 0
  · rw [hz, polyInterval_zero_coverage β σ n P hP]
    norm_num
  · exact hpositive _ (by omega) P hP

/-- Uniform fixed-degree risk bounds imply the selected certificate's worst-case risk bound. Given [the displayed inputs and assumptions](hyp:β,σ,n,hpositive), [the stated mathematical conclusion holds](goal). -/
lemma attainerRisk_of_positive_risk (β σ : ℝ) (n : ℕ)
    (hpositive : ∀ L, 1 ≤ L → ∀ P, Model β σ P →
      absRisk P σ n (thetaHat L σ) ≤ ENNReal.ofReal
        (12 * kernelMoment L β + 28 * Real.sqrt (kernelVariance L σ / n))) :
    attainerRisk β n σ ≤ ENNReal.ofReal (certificate β n σ) := by
  unfold attainerRisk
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro P
  change absRisk P.val σ n (thetaHat (selectedDegree β n σ) σ) ≤
    ENNReal.ofReal (radius β n σ (selectedDegree β n σ))
  by_cases hz : selectedDegree β n σ = 0
  · rw [hz]
    simpa only [radius, ite_true] using thetaHat_zero_absRisk_le β σ n P.val P.property
  · apply (hpositive _ (by omega) P.val P.property).trans
    apply ENNReal.ofReal_le_ofReal
    rw [radius, if_neg hz]
    have hv : 0 ≤ kernelVariance (selectedDegree β n σ) σ / (n : ℝ) := by
      apply div_nonneg _ (by positivity)
      unfold kernelVariance
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro j hj
      apply mul_nonneg
      · apply div_nonneg _ (by positivity)
        rw [Nat.mul_comm 2 j, pow_mul]
        exact sq_nonneg _
      exact intervalIntegral.integral_nonneg (by norm_num)
        (fun x hx => sq_nonneg _)
    have hs : Real.sqrt (kernelVariance (selectedDegree β n σ) σ / n) ≤
        Real.sqrt (40 * kernelVariance (selectedDegree β n σ) σ / n) := by
      apply Real.sqrt_le_sqrt
      calc
        _ ≤ 40 * (kernelVariance (selectedDegree β n σ) σ / n) := by linarith [hv]
        _ = _ := by ring
    linarith

/-- Finite-sample mean, risk and honesty certificates, followed by the uniform guarantees of selection. Given [the displayed inputs and assumptions](hyp:β,σ,n,L,P,hβ,hσ,hn,hL,hP), [the stated mathematical conclusion holds](goal). -/
-- @node: thm:finite-certificate
theorem finite_certificate (β σ : ℝ) (n L : ℕ) (P : LatentLaw)
    (hβ : β ∈ Ioc (0 : ℝ) 1) -- @realizes beta(public real smoothness with 0 < beta and beta ≤ 1)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hP : Model β σ P) : -- @realizes sigma([0,1]) @realizes n(integer at least two)
    (∀ d : Bool, 1/4 ≤ unmarkedMean d L σ P n) ∧ -- @realizes d(binary treatment index)
    absRisk P σ n (thetaHat L σ) ≤
      ENNReal.ofReal (12 * kernelMoment L β + 28 * Real.sqrt (kernelVariance L σ / n)) ∧
    (9/10 : ℝ) ≤ (experiment P σ n).real
      (Causalean.Stat.coverageEvent (polyInterval β n σ L).lo (polyInterval β n σ L).hi (theta P)) ∧
    honestAttainer β n σ ∈ honestIntervals β n σ ∧
    attainerRisk β n σ ≤ ENNReal.ofReal (certificate β n σ) ∧
    attainerLength β n σ ≤ ENNReal.ofReal (2 * certificate β n σ) := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  let hermite_of_gate : ClassicalHermiteFacts := classicalHermiteFacts
  have hfixed : ∀ J : ℕ, 1 ≤ J → ∀ Q : LatentLaw, Model β σ Q →
      (∀ d : Bool, 1/4 ≤ unmarkedMean d J σ Q n) ∧
      absRisk Q σ n (thetaHat J σ) ≤
        ENNReal.ofReal (12 * kernelMoment J β + 28 * Real.sqrt (kernelVariance J σ / n)) ∧
      (9/10 : ℝ) ≤ (experiment Q σ n).real
        (Causalean.Stat.coverageEvent (polyInterval β n σ J).lo
          (polyInterval β n σ J).hi (theta Q)) := by
    intro J hJ Q hQ
    letI := experiment_probability Q σ n
    let A : Bool → ℝ := fun d => ∫ x in (0 : ℝ)..1,
      (endpointKernel J).eval x * Q.f (sgn d * x) * Q.mu d (sgn d * x)
    let B : Bool → ℝ := fun d => ∫ x in (0 : ℝ)..1,
      (endpointKernel J).eval x * Q.f (sgn d * x)
    let a : Bool → ℝ := fun d => A d / B d
    let v := kernelVariance J σ / (n : ℝ)
    have hdata : (∀ d, unmarkedMean d J σ Q n = B d) ∧
        (∀ d, MemLp (fun z : Input n => markedAvg d J σ z.1 - A d) 2 (experiment Q σ n) ∧
          (∫ z : Input n, markedAvg d J σ z.1 - A d ∂experiment Q σ n) = 0 ∧
          (∫ z : Input n, (markedAvg d J σ z.1 - A d)^2 ∂experiment Q σ n) ≤ v) ∧
        (∀ d, MemLp (fun z : Input n => unmarkedAvg d J σ z.1 - B d) 2 (experiment Q σ n) ∧
          (∫ z : Input n, unmarkedAvg d J σ z.1 - B d ∂experiment Q σ n) = 0 ∧
          (∫ z : Input n, (unmarkedAvg d J σ z.1 - B d)^2 ∂experiment Q σ n) ≤ v) := by
      letI := empirical_Pobs_probability Q σ
      let F : Bool → Obs → ℝ := fun d o =>
        (if o.2.1 = d then 1 else 0) * bit o.2.2 *
          (inverseHeat J σ).eval (sgn d * o.1)
      let G : Bool → Obs → ℝ := fun d o =>
        (if o.2.1 = d then 1 else 0) * (inverseHeat J σ).eval (sgn d * o.1)
      have hsingle :
          (∀ d, (∫ o, F d o ∂Pobs Q σ) = A d ∧ MemLp (F d) 2 (Pobs Q σ) ∧
            (∫ o, (F d o)^2 ∂Pobs Q σ) ≤ kernelVariance J σ) ∧
          (∀ d, (∫ o, G d o ∂Pobs Q σ) = B d ∧ MemLp (G d) 2 (Pobs Q σ) ∧
            (∫ o, (G d o)^2 ∂Pobs Q σ) ≤ kernelVariance J σ) := by
        have hm (d : Bool) := observed_arm_summands_memLp_two hermite_of_gate β σ Q hQ d J
        constructor
        · intro d
          refine ⟨?_, (hm d).1, ?_⟩
          · simpa only [F, A] using
              marked_observed_integral_eq_endpoint legendre_of_gate hermite_of_gate
                β σ Q hQ hσ J hJ d
          · simpa only [F] using
              marked_observed_sq_le_kernelVariance legendre_of_gate hermite_of_gate
                β σ Q hQ hσ J hJ d
        · intro d
          refine ⟨?_, (hm d).2, ?_⟩
          · simpa only [G, B] using
              unmarked_observed_integral_eq_endpoint legendre_of_gate hermite_of_gate
                β σ Q hQ hσ J hJ d
          · simpa only [G] using
              unmarked_observed_sq_le_kernelVariance legendre_of_gate hermite_of_gate
                β σ Q hQ hσ J hJ d
      refine ⟨?_, ?_, ?_⟩
      · intro d
        exact (unmarkedMean_eq_single_observation Q σ n J d (by omega)
          ((hsingle.2 d).2.1.integrable (by norm_num))).trans (hsingle.2 d).1
      · intro d
        have hm := markedAvg_centered_moments_of_single_observation Q σ n J d
          (by omega) (hsingle.1 d).2.1 (hsingle.1 d).2.2
        change MemLp (fun z : Input n => markedAvg d J σ z.1 - ∫ o, F d o ∂Pobs Q σ)
            2 (experiment Q σ n) ∧
          (∫ z : Input n, markedAvg d J σ z.1 - ∫ o, F d o ∂Pobs Q σ
            ∂experiment Q σ n) = 0 ∧
          (∫ z : Input n, (markedAvg d J σ z.1 - ∫ o, F d o ∂Pobs Q σ)^2
            ∂experiment Q σ n) ≤ v at hm
        simpa only [(hsingle.1 d).1] using hm
      · intro d
        have hm := unmarkedAvg_centered_moments_of_single_observation Q σ n J d
          (by omega) (hsingle.2 d).2.1 (hsingle.2 d).2.2
        change MemLp (fun z : Input n => unmarkedAvg d J σ z.1 - ∫ o, G d o ∂Pobs Q σ)
            2 (experiment Q σ n) ∧
          (∫ z : Input n, unmarkedAvg d J σ z.1 - ∫ o, G d o ∂Pobs Q σ
            ∂experiment Q σ n) = 0 ∧
          (∫ z : Input n, (unmarkedAvg d J σ z.1 - ∫ o, G d o ∂Pobs Q σ)^2
            ∂experiment Q σ n) ≤ v at hm
        simpa only [(hsingle.2 d).1] using hm
    have hB (d : Bool) : 1/4 ≤ B d :=
      (endpointKernel_weighted_integral_bounds J hJ _
        (continuousOn_arm_reflection d Q.f Q.f_cont) _ _
        (fun x hx => hQ.density _ (arm_reflection_mem d hx))).1
    have ha (d : Bool) := arm_kernel_mean_bounds_and_bias Q β σ hQ hβ.1.le d J hJ
    have hA (d : Bool) : A d = a d * B d := by
      dsimp only [a]
      exact (div_mul_cancel₀ (A d) (by linarith [hB d] : B d ≠ 0)).symm
    refine ⟨fun d => hdata.1 d ▸ hB d, ?_, ?_⟩
    · exact thetaHat_absRisk_le_of_second_moments J hJ σ n Q A B a
        (kernelMoment J β) v hB (fun d => (ha d).1) hA (fun d => (ha d).2)
        (fun d => (hdata.2.1 d).1) (fun d => (hdata.2.2 d).1)
        (fun d => (hdata.2.1 d).2.2) (fun d => (hdata.2.2 d).2.2)
    · apply polyInterval_coverage_of_average_failure_bounds β σ n J hJ Q A B a
        hB (fun d => (ha d).1) hA (fun d => (ha d).2)
        (by have ht := abs_le.mp (theta_model_bounds β σ Q hQ); constructor <;> linarith [ht.1, ht.2])
      · intro d
        have hd := hdata.2.1 d
        have hv : variance (fun z : Input n => markedAvg d J σ z.1 - A d)
            (experiment Q σ n) ≤ v := by
          rw [variance_eq_integral hd.1.aemeasurable, hd.2.1]
          simpa only [sub_zero] using hd.2.2
        simpa only [v, mul_div_assoc] using centered_error_failure_le_one_fortieth
          (experiment Q σ n) _ hd.1 hd.2.1 v (div_pos (kernelVariance_pos J hJ σ) (by positivity)) hv
      · intro d
        have hd := hdata.2.2 d
        have hv : variance (fun z : Input n => unmarkedAvg d J σ z.1 - B d)
            (experiment Q σ n) ≤ v := by
          rw [variance_eq_integral hd.1.aemeasurable, hd.2.1]
          simpa only [sub_zero] using hd.2.2
        simpa only [v, mul_div_assoc] using centered_error_failure_le_one_fortieth
          (experiment Q σ n) _ hd.1 hd.2.1 v (div_pos (kernelVariance_pos J hJ σ) (by positivity)) hv
  have hcurrent := hfixed L hL P hP
  exact ⟨hcurrent.1, hcurrent.2.1, hcurrent.2.2,
    honestAttainer_of_positive_coverage β σ n (fun J hJ Q hQ => (hfixed J hJ Q hQ).2.2),
    attainerRisk_of_positive_risk β σ n (fun J hJ Q hQ => (hfixed J hJ Q hQ).2.1),
    attainerLength_le_certificate β n σ⟩

end CausalSmith.Stat.RdTruesideNoiseFrontier
