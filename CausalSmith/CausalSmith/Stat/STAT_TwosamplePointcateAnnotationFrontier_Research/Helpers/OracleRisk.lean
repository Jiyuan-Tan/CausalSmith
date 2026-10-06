module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.OracleMean

/-! # Oracle sampling and risk assembly
The labeled sample average has the variance reduction and clipping contraction
needed to combine its full-window Taylor bias with its stochastic error.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The untruncated localized inverse-propensity record statistic.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input z](hyp:z), [oracle record](goal) is the corresponding construction. -/
def oracleRecord {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (h : ℝ)
    (z : Cov d × Bool × Bool) : ℝ :=
  locWeight h z.1 * ((∑ u : PolyIdx d, r0 d h u * coarseBasis h z.1 u) *
    (bit z.2.1 * bit z.2.2 / designatedPropensity P hP z.1 -
      (1-bit z.2.1)*bit z.2.2 / (1-designatedPropensity P hP z.1)))

/-- The raw oracle average, with auxiliary records and randomization ignored.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input w](hyp:w), [oracle average](goal) is the corresponding construction. -/
def oracleAverage {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (h : ℝ)
    (w : Sample d n m) : ℝ := (n:ℝ)⁻¹ * ∑ i : Fin n, oracleRecord P hP h (w.1.1 i)

/-- Class membership fixes the observed covariate marginal to the known design.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the oracle observed design conclusion](goal) holds. -/
lemma oracle_observed_design {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    (obsLaw P).map (fun z => z.1) = uniformLaw d := by
  rw [obsLaw, Measure.map_map (by fun_prop) population_measurable_observed]
  change P.law.map Prod.fst = uniformLaw d
  have hs := canonicalLaw_spec P hP
  rw [← hs.1]
  exact hs.2.1

/-- Finite averaging preserves the bounded summands' finite moments.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the oracle average mem lp conclusion](goal) holds. -/
lemma oracleAverage_memLp {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) : MemLp (oracleAverage (n:=n) (m:=m) P hP h) 2 (experiment P n m) := by
  letI := population_experiment_probability P n m
  apply MemLp.const_mul
  apply memLp_finsetSum
  intro i hi
  exact (oracle_summand_memLp_top (experiment P n m) P hP h hh
    (fun w => w.1.1 i) (by fun_prop)).mono_exponent (by norm_num)

/-- The iid second-moment reduction gives an explicit oracle sampling bound.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the oracle average centered square bound conclusion](goal) holds. -/
lemma oracle_average_centered_square_bound {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hn : 0 < n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1) :
    (∫ w, (oracleAverage (n:=n) (m:=m) P hP h w -
      ∫ v, oracleAverage (n:=n) (m:=m) P hP h v ∂experiment P n m)^2 ∂experiment P n m) ≤
      (n:ℝ)⁻¹ * (eps⁻¹^2 * (h^(-(d:ℝ)) * ∑ u : PolyIdx d, (r0 d h u)^2)) := by
  letI := obsLaw_probability P
  have hF : MemLp (oracleRecord P hP h) 2 (obsLaw P) :=
    (oracle_summand_memLp_top (obsLaw P) P hP h hh id measurable_id).mono_exponent (by norm_num)
  have hm : (∫ w, oracleAverage (n:=n) (m:=m) P hP h w ∂experiment P n m) =
      ∫ z, oracleRecord P hP h z ∂obsLaw P := by
    rw [show (∫ w, oracleAverage (n:=n) (m:=m) P hP h w ∂experiment P n m) =
      ∫ x, (∑ u : PolyIdx d, r0 d h u * coarseBasis h x u)*tau P hP x ∂locLaw d h
      from oracle_average_mean P hP hn h hh hh']
    exact (oracle_summand_mean P hP h hh hh').symm
  rw [hm]
  exact (oracle_iid_centered_second_moment (m:=m) P hn _ hF).trans
    (mul_le_mul_of_nonneg_left
      (oracle_summand_second_moment_bound (obsLaw P) P hP h hh hh' id measurable_id
        (oracle_observed_design P hP)) (by positivity))

/-- Cauchy--Schwarz converts the sampling second moment to absolute deviation.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the oracle average absolute deviation conclusion](goal) holds. -/
lemma oracle_average_absolute_deviation {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hn : 0 < n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1) :
    (∫ w, |oracleAverage (n:=n) (m:=m) P hP h w -
      ∫ v, oracleAverage (n:=n) (m:=m) P hP h v ∂experiment P n m| ∂experiment P n m) ≤
      Real.sqrt ((n:ℝ)⁻¹ * (eps⁻¹^2 * (h^(-(d:ℝ)) * ∑ u : PolyIdx d, (r0 d h u)^2))) := by
  letI := population_experiment_probability P n m
  have hc := (oracleAverage_memLp (n:=n) (m:=m) P hP h hh).sub (memLp_const
    (∫ v, oracleAverage (n:=n) (m:=m) P hP h v ∂experiment P n m))
  have hcs := Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
    (experiment P n m) _ hc
  simp only [Real.norm_eq_abs, sq_abs] at hcs
  exact hcs.trans (Real.sqrt_le_sqrt (oracle_average_centered_square_bound P hP hn h hh hh'))

/-- The target evaluation coordinates have a bound independent of bandwidth.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the oracle target energy bound conclusion](goal) holds. -/
lemma oracle_target_energy_bound (d : ℕ) (h : ℝ) (hh : 0 < h) :
    (∑ u : PolyIdx d, (r0 d h u)^2) ≤
      (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2 := by
  have hx : x0 d ∈ locCube d h := by
    intro i
    constructor <;> change _ ≤ _ <;> simp only [x0] <;> linarith
  calc
    _ ≤ ∑ _u : PolyIdx d, ((4:ℝ)^d)^2 := by
      apply Finset.sum_le_sum
      intro u hu
      have hb := coarseBasis_abs_bound d h hh (x0 d) hx u
      change |r0 d h u| ≤ (4:ℝ)^d at hb
      nlinarith [sq_abs (r0 d h u), abs_nonneg (r0 d h u)]
    _ = _ := by simp

/-- Inverse effective sample size has standard deviation equal to the oracle rate.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input gamma](hyp:gamma), [the specified input hn](hyp:hn), [the specified input hg](hyp:hg), [the oracle bandwidth sqrt identity conclusion](goal) holds. -/
lemma oracle_bandwidth_sqrt_identity (d n : ℕ) (gamma : ℝ)
    (hn : 0 < n) (hg : 1 ≤ gamma) :
    Real.sqrt ((n:ℝ)⁻¹ * ((n:ℝ)^(-(1/(2*gamma+d))))^(-(d:ℝ))) =
      oracleRate d gamma n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hh : 0 < (n:ℝ)^(-(1/(2*gamma+d))) := Real.rpow_pos_of_pos hn0 _
  rw [show (n:ℝ)⁻¹ * ((n:ℝ)^(-(1/(2*gamma+d))))^(-(d:ℝ)) =
    ((n:ℝ)*((n:ℝ)^(-(1/(2*gamma+d))))^d)⁻¹ by
      rw [mul_inv_rev, Real.rpow_neg hh.le, Real.rpow_natCast]; ring]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul (by positivity)]
  convert oracle_bandwidth_sampling_identity d n gamma hn hg using 1 <;> norm_num

/-- The tuned oracle average has a uniform absolute sampling deviation at the oracle rate.  Given [the specified input d](hyp:d), [the specified input gamma](hyp:gamma), [the specified input hg](hyp:hg), [the overlap level eps](hyp:eps), [the oracle tuned absolute deviation conclusion](goal) holds. -/
lemma oracle_tuned_absolute_deviation (d : ℕ) (gamma eps : ℝ) (hg : 1 ≤ gamma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (alpha beta L : ℝ) (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      (∫ w, |oracleAverage (n:=n) (m:=m) P hP ((n:ℝ)^(-(1/(2*gamma+d)))) w -
        ∫ v, oracleAverage (n:=n) (m:=m) P hP ((n:ℝ)^(-(1/(2*gamma+d)))) v
          ∂experiment P n m| ∂experiment P n m) ≤ C*oracleRate d gamma n := by
  let K : ℝ := (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2
  refine ⟨Real.sqrt (eps⁻¹^2*K)+1, by positivity, ?_⟩
  intro n m hn alpha beta L P hP
  have hn0 : 0 < n := by omega
  obtain ⟨hh, hh'⟩ := oracle_bandwidth_bounds d n gamma hn hg
  have hb := oracle_average_absolute_deviation (m:=m) P hP hn0 _ hh hh'
  have hk := oracle_target_energy_bound d _ hh
  have hs : Real.sqrt ((n:ℝ)⁻¹ * (eps⁻¹^2 *
      (((n:ℝ)^(-(1/(2*gamma+d))))^(-(d:ℝ)) * ∑ u : PolyIdx d,
        (r0 d ((n:ℝ)^(-(1/(2*gamma+d)))) u)^2))) ≤
      Real.sqrt (eps⁻¹^2*K)*oracleRate d gamma n := by
    calc
      _ ≤ Real.sqrt ((eps⁻¹^2*K)*((n:ℝ)⁻¹ *
        ((n:ℝ)^(-(1/(2*gamma+d))))^(-(d:ℝ)))) := by
        apply Real.sqrt_le_sqrt
        dsimp [K]
        nlinarith [mul_le_mul_of_nonneg_left hk
          (by positivity : 0 ≤ (n:ℝ)⁻¹ * eps⁻¹^2 * ((n:ℝ)^(-(1/(2*gamma+d))))^(-(d:ℝ)))]
      _ = _ := by rw [Real.sqrt_mul (by dsimp [K]; positivity),
        oracle_bandwidth_sqrt_identity d n gamma hn0 hg]
  apply (hb.trans hs).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (by unfold oracleRate; positivity)

/-- The continuous target lies in the clipping interval by the two arm-mean range conditions.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the oracle target in clip conclusion](goal) holds. -/
lemma oracle_target_in_clip {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    tau P hP (x0 d) ∈ Icc (-1) 1 := by
  have hx : x0 d ∈ cube d := by intro i; norm_num [x0, cube]
  have hs := canonicalLaw_spec P hP
  have hc := hs.2.2.2.2.2.2.2.1 (x0 d) hx
  have ht := hs.2.2.2.2.2.2.2.2 (x0 d) hx
  simp only [tau, designatedTreated, designatedControl, if_pos hx]
  constructor <;> linarith [hc.1, hc.2, ht.1, ht.2]

/-- The stipulated smoother clips exactly the raw oracle sample average.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input w](hyp:w), [the oracle smoother eq clip average conclusion](goal) holds. -/
lemma oracleSmoother_eq_clip_average {d n m : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) (w : Sample d n m) :
    oracleSmoother d gamma n m w (designatedPropensity P hP) =
      clip (oracleAverage P hP ((n:ℝ)^(-(1/(2*gamma+d)))) w) := by
  unfold oracleSmoother oracleAverage oracleRecord
  dsimp only
  simp only [mul_assoc]

/-- Taylor bias plus iid sampling deviation bounds the clipped oracle risk uniformly.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the oracle smoother upper rate conclusion](goal) holds. -/
lemma oracle_smoother_upper_rate (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
        (∫⁻ w, ENNReal.ofReal
          |oracleSmoother d gamma n m w (designatedPropensity P hP) - tau P hP (x0 d)|
          ∂experiment P n m) ≤ ENNReal.ofReal (C*oracleRate d gamma n) := by
  obtain ⟨Cb, hCb, hb⟩ := oracle_tuned_average_bias d alpha beta gamma L eps hdom
  obtain ⟨Cs, hCs, hs⟩ := oracle_tuned_absolute_deviation d gamma eps hdom.2.2.2.2.2.1
  refine ⟨Cs+Cb, add_pos hCs hCb, ?_⟩
  intro n m hn P hP
  letI := population_experiment_probability P n m
  let H := (n:ℝ)^(-(1/(2*gamma+d)))
  let A := oracleAverage (n:=n) (m:=m) P hP H
  let mu := ∫ w, A w ∂experiment P n m
  let target := tau P hP (x0 d)
  obtain ⟨hh, hh'⟩ := oracle_bandwidth_bounds d n gamma hn hdom.2.2.2.2.2.1
  have hA : Integrable A (experiment P n m) :=
    (oracleAverage_memLp P hP H hh).integrable (by norm_num)
  have hcenter : Integrable (fun w => |A w-mu|) (experiment P n m) :=
    (hA.sub (integrable_const mu)).abs
  have herror : Integrable (fun w =>
      |oracleSmoother d gamma n m w (designatedPropensity P hP)-target|) (experiment P n m) := by
    apply Integrable.mono' ((hA.sub (integrable_const target)).abs)
      (by dsimp [target]; fun_prop)
    filter_upwards [] with w
    simp only [Real.norm_eq_abs, abs_abs]
    rw [oracleSmoother_eq_clip_average]
    exact clipping_contraction (A w) target (oracle_target_in_clip P hP)
  have hb' : |mu-target| ≤ Cb*oracleRate d gamma n := hb n m hn P hP
  have hs' : (∫ w, |A w-mu| ∂experiment P n m) ≤ Cs*oracleRate d gamma n :=
    hs n m hn alpha beta L P hP
  have hr : (∫ w, |oracleSmoother d gamma n m w (designatedPropensity P hP)-target|
      ∂experiment P n m) ≤ (Cs+Cb)*oracleRate d gamma n := by
    calc
      _ ≤ ∫ w, (|A w-mu|+|mu-target|) ∂experiment P n m := by
        apply integral_mono herror (hcenter.add (integrable_const _))
        intro w
        dsimp only [Pi.add_apply]
        rw [oracleSmoother_eq_clip_average]
        exact (clipping_contraction (A w) target (oracle_target_in_clip P hP)).trans
          (abs_sub_le (A w) mu target)
      _ = (∫ w, |A w-mu| ∂experiment P n m)+|mu-target| := by
        rw [integral_add hcenter (integrable_const _)]
        simp
      _ ≤ _ := by nlinarith [hs', hb']
  rw [← ofReal_integral_eq_lintegral_ofReal herror
    (Filter.Eventually.of_forall (fun w => abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hr

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
