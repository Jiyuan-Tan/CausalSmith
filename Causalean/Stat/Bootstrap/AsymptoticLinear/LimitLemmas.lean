module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.Basic
public import Causalean.Stat.Inference.Studentize

/-!
# Limit lemmas for bootstrap validity and random confidence bounds

This module isolates the generic probability arguments needed by the estimator-level bootstrap
theorems: triangle control for Kolmogorov distance, conditional Slutsky under a coupled remainder,
quantile convergence from random uniform CDF convergence, and coverage with random endpoints.
It also records the exact centered-Gaussian equal-tail probabilities used by percentile and basic
intervals.
-/

public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

/-- [Kolmogorov CDF distance obeys the triangle inequality](goal), with [one real probability
law](hyp:nu) as the intermediate point between [the first law](hyp:mu) and [the final
law](hyp:xi). -/
theorem cdfKolmogorov_triangle
    (mu nu xi : ProbabilityMeasure ℝ) :
    cdfKolmogorov mu xi <=
    cdfKolmogorov mu nu +
        cdfKolmogorov nu xi := by
  unfold cdfKolmogorov
  have hb (rho sigma : ProbabilityMeasure ℝ) : BddAbove (range fun t : ℝ ↦
      |cdf (rho : Measure ℝ) t - cdf (sigma : Measure ℝ) t|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [abs_le]
    constructor <;>
      linarith [cdf_nonneg (rho : Measure ℝ) t, cdf_le_one (rho : Measure ℝ) t,
        cdf_nonneg (sigma : Measure ℝ) t, cdf_le_one (sigma : Measure ℝ) t]
  refine ciSup_le fun t ↦ ?_
  calc
    |cdf (mu : Measure ℝ) t - cdf (xi : Measure ℝ) t| ≤
        |cdf (mu : Measure ℝ) t - cdf (nu : Measure ℝ) t| +
          |cdf (nu : Measure ℝ) t - cdf (xi : Measure ℝ) t| := by
            simpa [Real.dist_eq] using
              (dist_triangle (cdf (mu : Measure ℝ) t) (cdf (nu : Measure ℝ) t)
                (cdf (xi : Measure ℝ) t))
    _ ≤ (⨆ t, |cdf (mu : Measure ℝ) t - cdf (nu : Measure ℝ) t|) +
          ⨆ t, |cdf (nu : Measure ℝ) t - cdf (xi : Measure ℝ) t| :=
      add_le_add (le_ciSup (hb mu nu) t) (le_ciSup (hb nu xi) t)

/-- For [a sequence of data-dependent conditional laws](hyp:nu) and [a linear term together with
a remainder](hyp:linear,remainder) that are [measurable for every sample size and
outcome](hyp:hlinearMeas,hremainderMeas), and [a limiting law](hyp:G) whose [distribution function
is continuous](hyp:hGcont): if [the conditional law of the linear term approaches the limit in
Kolmogorov distance, in sampling probability](hyp:hlinear) and [the conditional remainder is
small in conditional probability, with sampling probability tending to
one](hyp:hremainder), then [the conditional law of their sum approaches the same limit in
Kolmogorov distance, in sampling probability](goal). -/
theorem conditionalSlutsky_cdfKolmogorov_inProb
    {Omega Y : Type*} [MeasurableSpace Omega] [MeasurableSpace Y]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (nu : ℕ -> Omega -> ProbabilityMeasure Y)
    (linear remainder : ℕ -> Omega -> Y -> ℝ)
    (hlinearMeas : forall n omega, Measurable (linear n omega))
    (hremainderMeas : forall n omega, Measurable (remainder n omega))
    (G : ProbabilityMeasure ℝ)
    (hGcont : Continuous (cdf (G : Measure ℝ)))
    (hlinear : Tendsto_inProb
      (fun n omega => cdfKolmogorov
        ((nu n omega).map (hlinearMeas n omega).aemeasurable) G)
      (fun _ => 0) mu)
    (hremainder : forall epsilon : ℝ, 0 < epsilon ->
      Tendsto
        (fun n => mu.real {omega |
          epsilon < ((nu n omega : ProbabilityMeasure Y) : Measure Y).real
            {y | epsilon < abs (remainder n omega y)}})
        atTop (nhds 0)) :
    Tendsto_inProb
      (fun n omega => cdfKolmogorov
        ((nu n omega).map
          ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable) G)
      (fun _ => 0) mu := by
  rw [Tendsto_inProb_iff,
    tendstoInMeasure_iff_measureReal_dist]
  rw [Tendsto_inProb_iff,
    tendstoInMeasure_iff_measureReal_dist] at hlinear
  intro epsilon hepsilon
  let eta := epsilon / 4
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  have hshift : TendstoUniformly
      (fun d t : ℝ => cdf (G : Measure ℝ) (t + d))
      (cdf (G : Measure ℝ)) (𝓝 0) := by
    refine tendstoUniformly_of_monotone_of_tendsto_at
      (F := fun d t : ℝ => cdf (G : Measure ℝ) (t + d))
      (G := cdf (G : Measure ℝ)) ?_ ?_ ?_
      (monotone_cdf (G : Measure ℝ)) hGcont
      (tendsto_cdf_atBot (G : Measure ℝ)) (tendsto_cdf_atTop (G : Measure ℝ)) ?_
    · intro d x y hxy
      exact monotone_cdf (G : Measure ℝ) (by linarith)
    · exact fun d t => cdf_nonneg (G : Measure ℝ) (t + d)
    · exact fun d t => cdf_le_one (G : Measure ℝ) (t + d)
    · intro t
      have htadd : Tendsto (fun d : ℝ => t + d) (𝓝 0) (𝓝 (t + 0)) :=
        tendsto_const_nhds.add tendsto_id
      change Tendsto ((cdf (G : Measure ℝ)) ∘ fun d : ℝ => t + d)
        (𝓝 0) (𝓝 (cdf (G : Measure ℝ) t))
      simpa only [add_zero] using hGcont.continuousAt.tendsto.comp htadd
  have hshiftEventually : ∀ᶠ d : ℝ in 𝓝 0,
      ∀ t : ℝ, dist (cdf (G : Measure ℝ) t)
        (cdf (G : Measure ℝ) (t + d)) < eta :=
    (Metric.tendstoUniformly_iff.1 hshift) eta heta
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hshiftEventually
  let delta := min (r / 2) (eta / 2)
  have hdelta : 0 < delta := lt_min (half_pos hr) (half_pos heta)
  have hdeltalt : delta < eta := (min_le_right _ _).trans_lt (half_lt_self heta)
  have hdeltaBall : delta ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hdelta]
    exact (min_le_left _ _).trans_lt (half_lt_self hr)
  have hoscPlus (t : ℝ) :
      dist (cdf (G : Measure ℝ) (t + delta)) (cdf (G : Measure ℝ) t) < eta :=
    by simpa [dist_comm] using hball hdeltaBall t
  have hoscMinus (t : ℝ) :
      dist (cdf (G : Measure ℝ) t) (cdf (G : Measure ℝ) (t - delta)) < eta := by
    simpa [sub_add_cancel, dist_comm] using hoscPlus (t - delta)
  have hcdfError (rho sigma : ProbabilityMeasure ℝ) (t : ℝ) :
      |cdf (rho : Measure ℝ) t - cdf (sigma : Measure ℝ) t| ≤
        cdfKolmogorov rho sigma := by
    unfold cdfKolmogorov
    apply le_ciSup (c := t)
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [abs_le]
    constructor <;>
      linarith [cdf_nonneg (rho : Measure ℝ) x, cdf_le_one (rho : Measure ℝ) x,
        cdf_nonneg (sigma : Measure ℝ) x, cdf_le_one (sigma : Measure ℝ) x]
  have hupperCDF (n : ℕ) (omega : Omega) (t : ℝ) :
      cdf (((nu n omega).map
        ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable) : Measure ℝ) t ≤
      cdf (((nu n omega).map (hlinearMeas n omega).aemeasurable) : Measure ℝ) (t + delta) +
        ((nu n omega : ProbabilityMeasure Y) : Measure Y).real
          {y | delta < abs (remainder n omega y)} := by
    rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply_of_aemeasurable
        ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable
        measurableSet_Iic,
      Measure.map_apply_of_aemeasurable (hlinearMeas n omega).aemeasurable
        measurableSet_Iic]
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro y hy
    by_cases htail : delta < abs (remainder n omega y)
    · exact Or.inr htail
    · left
      simp only [mem_preimage, mem_Iic] at hy ⊢
      rw [not_lt] at htail
      have hremLower := (abs_le.mp htail).1
      change linear n omega y + remainder n omega y ≤ t at hy
      linarith
  have hlowerCDF (n : ℕ) (omega : Omega) (t : ℝ) :
      cdf (((nu n omega).map (hlinearMeas n omega).aemeasurable) : Measure ℝ) (t - delta) ≤
      cdf (((nu n omega).map
        ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable) : Measure ℝ) t +
        ((nu n omega : ProbabilityMeasure Y) : Measure Y).real
          {y | delta < abs (remainder n omega y)} := by
    rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
      ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply_of_aemeasurable (hlinearMeas n omega).aemeasurable
        measurableSet_Iic,
      Measure.map_apply_of_aemeasurable
        ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable
        measurableSet_Iic]
    refine (measureReal_mono ?_).trans (measureReal_union_le _ _)
    intro y hy
    by_cases htail : delta < abs (remainder n omega y)
    · exact Or.inr htail
    · left
      simp only [mem_preimage, mem_Iic] at hy ⊢
      rw [not_lt] at htail
      have hremUpper := (abs_le.mp htail).2
      change linear n omega y + remainder n omega y ≤ t
      linarith
  have hsumBound (n : ℕ) (omega : Omega) :
      cdfKolmogorov
          ((nu n omega).map
            ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable) G ≤
        cdfKolmogorov
          ((nu n omega).map (hlinearMeas n omega).aemeasurable) G +
        ((nu n omega : ProbabilityMeasure Y) : Measure Y).real
          {y | delta < abs (remainder n omega y)} + eta := by
    unfold cdfKolmogorov
    refine ciSup_le fun t => ?_
    have hu := hupperCDF n omega t
    have hl := hlowerCDF n omega t
    have hePlus := hcdfError
      ((nu n omega).map (hlinearMeas n omega).aemeasurable) G (t + delta)
    have heMinus := hcdfError
      ((nu n omega).map (hlinearMeas n omega).aemeasurable) G (t - delta)
    unfold cdfKolmogorov at hePlus heMinus
    rw [abs_le] at hePlus heMinus
    have hoPlus := hoscPlus t
    have hoMinus := hoscMinus t
    rw [Real.dist_eq, abs_lt] at hoPlus hoMinus
    rw [abs_le]
    constructor <;> linarith
  have hsubset (n : ℕ) :
      {omega | epsilon ≤ dist
        (cdfKolmogorov
          ((nu n omega).map
            ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable) G) 0} ⊆
      {omega | eta ≤ dist
        (cdfKolmogorov
          ((nu n omega).map (hlinearMeas n omega).aemeasurable) G) 0} ∪
      {omega | delta < ((nu n omega : ProbabilityMeasure Y) : Measure Y).real
        {y | delta < abs (remainder n omega y)}} := by
    intro omega hbad
    by_contra hnot
    rw [mem_union, not_or] at hnot
    simp only [mem_ofPred_eq] at hbad hnot
    have hlinNonneg := cdfKolmogorov_nonneg
      ((nu n omega).map (hlinearMeas n omega).aemeasurable) G
    have hsumNonneg := cdfKolmogorov_nonneg
      ((nu n omega).map
        ((hlinearMeas n omega).add (hremainderMeas n omega)).aemeasurable) G
    have hlinlt : cdfKolmogorov
        ((nu n omega).map (hlinearMeas n omega).aemeasurable) G < eta := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hlinNonneg] at hnot
      exact lt_of_not_ge hnot.1
    have htaile : ((nu n omega : ProbabilityMeasure Y) : Measure Y).real
        {y | delta < abs (remainder n omega y)} ≤ delta := le_of_not_gt hnot.2
    have hsumb := hsumBound n omega
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsumNonneg] at hbad
    dsimp [eta] at *
    linarith
  have hlinearEta := hlinear eta heta
  have hremainderDelta := hremainder delta hdelta
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_)
    (by simpa only [zero_add] using hlinearEta.add hremainderDelta)
  exact (measureReal_mono (hsubset n)).trans (measureReal_union_le _ _)

/-- For [a sequence of data-dependent probability laws on the real line](hyp:nu), [a limiting
law](hyp:G) and [an interior quantile level](hyp:hbeta0,hbeta1), suppose the limiting law's
distribution function is [continuous at its lower quantile](hyp:hGcont) and [has a smaller value
at every lower point and a larger value at every higher point than at that quantile](hyp:hGstrict),
and [the Kolmogorov distance between the data-dependent laws and the limit
tends to zero in sampling probability](hyp:hdist).
Then [the random lower quantiles converge in sampling probability to the limiting
quantile](goal). -/
theorem quantile_tendsto_inProb_of_cdfKolmogorov
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (nu : ℕ -> Omega -> ProbabilityMeasure ℝ) (G : ProbabilityMeasure ℝ)
    {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hGcont : ContinuousAt (cdf (G : Measure ℝ))
      (quantile (G : Measure ℝ) beta))
    (hGstrict : StrictlyIncreasingAt (cdf (G : Measure ℝ))
      (quantile (G : Measure ℝ) beta))
    (hdist : Tendsto_inProb
      (fun n omega => cdfKolmogorov (nu n omega) G)
      (fun _ => 0) mu) :
    Tendsto_inProb
      (fun n omega => quantile (nu n omega : Measure ℝ) beta)
      (fun _ => quantile (G : Measure ℝ) beta) mu := by
  rw [Tendsto_inProb_iff,
    tendstoInMeasure_iff_measureReal_dist]
  rw [Tendsto_inProb_iff,
    tendstoInMeasure_iff_measureReal_dist] at hdist
  intro epsilon hepsilon
  let q := quantile (G : Measure ℝ) beta
  have hcdfq : cdf (G : Measure ℝ) q = beta := by
    exact cdf_quantile_eq (G : Measure ℝ) hbeta0 hbeta1 hGcont
  have hleft : cdf (G : Measure ℝ) (q - epsilon / 2) < beta := by
    have h := hGstrict.1 (q - epsilon / 2) (by linarith)
    simpa only [q, hcdfq] using h
  have hright : beta < cdf (G : Measure ℝ) (q + epsilon / 2) := by
    have h := hGstrict.2 (q + epsilon / 2) (by linarith)
    simpa only [q, hcdfq] using h
  let delta := min
    (beta - cdf (G : Measure ℝ) (q - epsilon / 2))
    (cdf (G : Measure ℝ) (q + epsilon / 2) - beta) / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hcdfError (rho sigma : ProbabilityMeasure ℝ) (t : ℝ) :
      |cdf (rho : Measure ℝ) t - cdf (sigma : Measure ℝ) t| ≤
        cdfKolmogorov rho sigma := by
    unfold cdfKolmogorov
    apply le_ciSup (c := t)
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [abs_le]
    constructor <;>
      linarith [cdf_nonneg (rho : Measure ℝ) x, cdf_le_one (rho : Measure ℝ) x,
        cdf_nonneg (sigma : Measure ℝ) x, cdf_le_one (sigma : Measure ℝ) x]
  have hsubset (n : ℕ) :
      {omega | epsilon ≤ dist
        (quantile (nu n omega : Measure ℝ) beta) q} ⊆
      {omega | delta ≤ dist
        (cdfKolmogorov (nu n omega) G) 0} := by
    intro omega hbad
    have hkolNonneg := cdfKolmogorov_nonneg (nu n omega) G
    by_contra hnot
    have hkoldist : dist (cdfKolmogorov (nu n omega) G) 0 < delta :=
      lt_of_not_ge hnot
    have hkol : cdfKolmogorov (nu n omega) G < delta := by
      simpa [Real.dist_eq, abs_of_nonneg hkolNonneg] using hkoldist
    have hdeltaLeft :
        delta ≤ (beta - cdf (G : Measure ℝ) (q - epsilon / 2)) / 2 := by
      dsimp [delta]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hdeltaRight :
        delta ≤ (cdf (G : Measure ℝ) (q + epsilon / 2) - beta) / 2 := by
      dsimp [delta]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have herrorLeft := hcdfError (nu n omega) G (q - epsilon / 2)
    have herrorRight := hcdfError (nu n omega) G (q + epsilon / 2)
    rw [abs_le] at herrorLeft herrorRight
    have hnuLeft : cdf (nu n omega : Measure ℝ) (q - epsilon / 2) < beta := by
      linarith
    have hnuRight : beta < cdf (nu n omega : Measure ℝ) (q + epsilon / 2) := by
      linarith
    have hqLower : q - epsilon / 2 <
        quantile (nu n omega : Measure ℝ) beta := by
      by_contra h
      have := (quantile_le_iff hbeta0 hbeta1).1 (le_of_not_gt h)
      linarith
    have hqUpper : quantile (nu n omega : Measure ℝ) beta ≤
        q + epsilon / 2 :=
      (quantile_le_iff hbeta0 hbeta1).2 hnuRight.le
    change epsilon ≤ dist
      (quantile (nu n omega : Measure ℝ) beta) q at hbad
    rw [Real.dist_eq] at hbad
    have hgood :
        |quantile (nu n omega : Measure ℝ) beta - q| < epsilon := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  have hdistDelta := hdist delta hdelta
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) hdistDelta
  exact measureReal_mono (hsubset n)

/-- Suppose [a statistic is almost-everywhere measurable at every sample size](hyp:hSnMeas) and
[converges in distribution to a limiting law](hyp:hSn), [two random interval
endpoints](hyp:lower,upper) are [measurable](hyp:hlowerMeas,hupperMeas) and converge in sampling
probability to [fixed endpoints](hyp:a,b) — [the lower one](hyp:hlower) and [the upper
one](hyp:hupper) — with [the fixed endpoints ordered](hyp:hab) and [the limiting law putting no
mass on the interval's boundary](hyp:hboundary). Then [the probability that the statistic falls
in the random interval converges to the limiting law's mass on the fixed interval](goal). -/
theorem tendsto_dist_random_Icc_coverage
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {Sn : ℕ -> Omega -> ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hSnMeas : forall n, AEMeasurable (Sn n) mu)
    (hSn : Tendsto_dist Sn Q mu hSnMeas)
    (lower upper : ℕ -> Omega -> ℝ) (a b : ℝ)
    (hlowerMeas : forall n, Measurable (lower n))
    (hupperMeas : forall n, Measurable (upper n))
    (hlower : Tendsto_inProb lower (fun _ => a) mu)
    (hupper : Tendsto_inProb upper (fun _ => b) mu)
    (hab : a <= b) (hboundary : Q (frontier (Icc a b)) = 0) :
    Tendsto
      (fun n => mu.real {omega | Sn n omega ∈ Icc (lower n omega) (upper n omega)})
      atTop (nhds (Q.real (Icc a b))) := by
  let F : ℝ → (ℝ × ℝ) × ℝ := fun z => ((z, a), b)
  let E : Set ((ℝ × ℝ) × ℝ) :=
    {p | p.1.2 ≤ p.1.1} ∩ {p | p.1.1 ≤ p.2}
  have hSn' : TendstoInDistribution Sn atTop id (fun _ => mu) Q := by
    refine
      { forall_aemeasurable := hSnMeas
        aemeasurable_limit := measurable_id.aemeasurable
        tendsto := ?_ }
    have ht := (Tendsto_dist_iff Sn Q mu hSnMeas).1 hSn
    simpa only [Measure.map_id] using ht
  have hSnLower : TendstoInDistribution
      (fun n omega => (Sn n omega, lower n omega)) atTop
      (fun z : ℝ => (z, a)) (fun _ => mu) Q :=
    hSn'.prodMk_of_tendstoInMeasure_const Sn lower id hlower
      (fun n => (hlowerMeas n).aemeasurable)
  have hJoint : TendstoInDistribution
      (fun n omega => ((Sn n omega, lower n omega), upper n omega)) atTop
      F (fun _ => mu) Q :=
    hSnLower.prodMk_of_tendstoInMeasure_const
      (fun n omega => (Sn n omega, lower n omega)) upper
      (fun z : ℝ => (z, a)) hupper
      (fun n => (hupperMeas n).aemeasurable)
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  have hfront_subset :
      frontier E ⊆
        {p : (ℝ × ℝ) × ℝ | p.1.2 = p.1.1} ∪
          {p : (ℝ × ℝ) × ℝ | p.1.1 = p.2} := by
    calc
      frontier E ⊆
          frontier {p : (ℝ × ℝ) × ℝ | p.1.2 ≤ p.1.1} ∪
            frontier {p : (ℝ × ℝ) × ℝ | p.1.1 ≤ p.2} := by
              dsimp [E]
              exact (frontier_inter_subset _ _).trans
                (union_subset_union inter_subset_left inter_subset_right)
      _ ⊆
          {p : (ℝ × ℝ) × ℝ | p.1.2 = p.1.1} ∪
            {p : (ℝ × ℝ) × ℝ | p.1.1 = p.2} :=
        union_subset_union (frontier_le_subset_eq (by fun_prop) (by fun_prop))
          (frontier_le_subset_eq (by fun_prop) (by fun_prop))
  have hlimitBoundary : (Q.map F) (frontier E) = 0 := by
    rw [Measure.map_apply_of_aemeasurable (by fun_prop) isClosed_frontier.measurableSet]
    refine measure_mono_null ?_ hboundary
    intro z hz
    have hz' := hfront_subset hz
    rw [frontier_Icc hab]
    simpa [F, eq_comm] using hz'
  have hport :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
      hJoint.tendsto (E := E) (by
        change ((Q.map F) (frontier E)).toNNReal = 0
        simp [hlimitBoundary])
  have hreal := NNReal.continuous_coe.tendsto _ |>.comp hport
  have hmap_n (n : ℕ) :
      (mu.map (fun omega => ((Sn n omega, lower n omega), upper n omega))) E =
        mu {omega | Sn n omega ∈ Icc (lower n omega) (upper n omega)} := by
    rw [Measure.map_apply_of_aemeasurable (hJoint.forall_aemeasurable n) hEmeas]
    rfl
  have hmap_limit : (Q.map F) E = Q (Icc a b) := by
    rw [Measure.map_apply_of_aemeasurable (by fun_prop) hEmeas]
    congr 1
  simpa [Function.comp_def, ProbabilityMeasure.coe_mk,
    ENNReal.coe_toNNReal_eq_toReal, Measure.real, hmap_n, hmap_limit] using hreal

/-- A centered Gaussian with [positive variance](hyp:hv) assigns [probability one minus the
nominal error level to the interval between its two equal-tail quantiles](goal) when [the error
level lies strictly between zero and one](hyp:halpha0,halpha1). -/
theorem gaussianReal_quantile_Icc_toReal
    {v : NNReal} (hv : 0 < v) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    (gaussianReal 0 v).real
      (Icc
        (Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (alpha / 2))
        (Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (1 - alpha / 2))) =
      1 - alpha := by
  haveI : NullSingletonClass (gaussianReal 0 v) :=
    nullSingletonClass_gaussianReal hv.ne'
  have hs : 0 < Real.sqrt (v : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast hv
  have hp0 : 0 < alpha / 2 := by linarith
  have hp1 : alpha / 2 < 1 := by linarith
  have hq0 : 0 < 1 - alpha / 2 := by linarith
  have hq1 : 1 - alpha / 2 < 1 := by linarith
  let a := Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (alpha / 2)
  let b := Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (1 - alpha / 2)
  have ha : cdf (gaussianReal 0 v) a = alpha / 2 := by
    rw [cdf_gaussianReal_zero hv]
    simp only [a, mul_div_cancel_left₀ _ hs.ne']
    exact Causalean.Mathlib.stdNormalCDF_probit hp0 hp1
  have hb : cdf (gaussianReal 0 v) b = 1 - alpha / 2 := by
    rw [cdf_gaussianReal_zero hv]
    simp only [b, mul_div_cancel_left₀ _ hs.ne']
    exact Causalean.Mathlib.stdNormalCDF_probit hq0 hq1
  have hmeasure : (gaussianReal 0 v) (Ioc a b) =
      ENNReal.ofReal (cdf (gaussianReal 0 v) b - cdf (gaussianReal 0 v) a) := by
    calc
      (gaussianReal 0 v) (Ioc a b) =
          (cdf (gaussianReal 0 v)).measure (Ioc a b) := by
            rw [ProbabilityTheory.measure_cdf]
      _ = ENNReal.ofReal
          (cdf (gaussianReal 0 v) b - cdf (gaussianReal 0 v) a) := by
            rw [StieltjesFunction.measure_Ioc]
  calc
    (gaussianReal 0 v).real (Icc a b) =
        (gaussianReal 0 v).real (Ioc a b) :=
      (measureReal_congr (Ioc_ae_eq_Icc (μ := gaussianReal 0 v))).symm
    _ = (ENNReal.ofReal
        (cdf (gaussianReal 0 v) b - cdf (gaussianReal 0 v) a)).toReal := by
      rw [measureReal_def, hmeasure]
    _ = (ENNReal.ofReal (1 - alpha)).toReal := by rw [ha, hb]; congr 2 <;> ring
    _ = 1 - alpha := ENNReal.toReal_ofReal (by linarith)

/-- By symmetry, a centered Gaussian with [positive variance](hyp:hv) assigns [probability one
minus the nominal error level to the interval obtained by negating and reversing its equal-tail
quantiles](goal) when [the error level lies strictly between zero and
one](hyp:halpha0,halpha1). -/
theorem gaussianReal_reflectedQuantile_Icc_toReal
    {v : NNReal} (hv : 0 < v) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    (gaussianReal 0 v).real
      (Icc
        (-(Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (1 - alpha / 2)))
        (-(Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (alpha / 2)))) =
      1 - alpha := by
  have hp0 : 0 < alpha / 2 := by linarith
  have hp1 : alpha / 2 < 1 := by linarith
  have hq0 : 0 < 1 - alpha / 2 := by linarith
  have hq1 : 1 - alpha / 2 < 1 := by linarith
  have hsym : -Causalean.Mathlib.probit (1 - alpha / 2) =
      Causalean.Mathlib.probit (alpha / 2) := by
    apply Causalean.Mathlib.stdNormalCDF_strictMono.injective
    rw [Causalean.Mathlib.stdNormalCDF_neg,
      Causalean.Mathlib.stdNormalCDF_probit hq0 hq1,
      Causalean.Mathlib.stdNormalCDF_probit hp0 hp1]
    ring
  have hsym' : -Causalean.Mathlib.probit (alpha / 2) =
      Causalean.Mathlib.probit (1 - alpha / 2) := by
    linarith
  have hlower :
      -(Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (1 - alpha / 2)) =
        Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (alpha / 2) := by
    calc
      -(Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (1 - alpha / 2)) =
          Real.sqrt (v : ℝ) * (-Causalean.Mathlib.probit (1 - alpha / 2)) := by ring
      _ = Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (alpha / 2) := by rw [hsym]
  have hupper :
      -(Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (alpha / 2)) =
        Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (1 - alpha / 2) := by
    calc
      -(Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (alpha / 2)) =
          Real.sqrt (v : ℝ) * (-Causalean.Mathlib.probit (alpha / 2)) := by ring
      _ = Real.sqrt (v : ℝ) * Causalean.Mathlib.probit (1 - alpha / 2) := by rw [hsym']
  rw [hlower, hupper]
  exact gaussianReal_quantile_Icc_toReal hv halpha0 halpha1

end

end Causalean.Stat
