module
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Support

/-!
# One-dimensional quantile transport and CDF distance

This module proves the atom-valid one-dimensional identity between the
absolute-distance cost of the shared-uniform quantile coupling and the
integrated absolute difference of two CDFs on a common compact interval. It
also exposes the support, integrability, threshold-kernel, and Tonelli facts
used by that identity.
-/

public section

open MeasureTheory ProbabilityTheory Set Causalean.Stat

namespace Causalean.Stat.Quantile.Transport

/-- A [probability law](hyp:μ) [concentrated on a closed interval](hyp:hμ) has
[a quantile in that interval at almost every interior level](goal). -/
lemma quantile_mem_Icc_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hμ : μ (Icc a b)ᶜ = 0) :
    ∀ᵐ u ∂unifOI, quantile μ u ∈ Icc a b := by
  /- Pull back the conull interval along `quantile_map_uniform μ`; use
     `aemeasurable_quantile_unifOI` to identify the preimage measure. -/
  have h : ∀ᵐ x ∂μ, x ∈ Icc a b := by
    rw [ae_iff]
    exact hμ
  rw [← quantile_map_uniform μ] at h
  exact (ae_map_iff (aemeasurable_quantile_unifOI μ) measurableSet_Icc).mp h

/-- [Two probability laws](hyp:μ,ν) have [an absolute CDF difference
integrable over the given finite interval](goal). -/
lemma intervalIntegrable_abs_cdf_sub (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => |cdf μ t - cdf ν t|) volume a b := by
  /- Monotonicity gives measurability of each CDF; `cdf_nonneg` and
     `cdf_le_one` bound the integrand by one on the finite interval. -/
  apply (intervalIntegrable_iff).2
  apply Measure.integrableOn_of_bounded (M := 1) (by simp only [uIoc]; exact measure_Ioc_lt_top.ne)
  · simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (((monotone_cdf μ).measurable.sub (monotone_cdf ν).measurable).norm).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_abs]
    have hμ := cdf_nonneg μ t
    have hν := cdf_nonneg ν t
    have hμ' := cdf_le_one μ t
    have hν' := cdf_le_one ν t
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- [Two probability laws](hyp:μ,ν) [concentrated on one closed interval](hyp:hμ,hν)
have [an integrable absolute quantile difference over the unit interval](goal). -/
lemma intervalIntegrable_abs_quantile_sub (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0) :
    IntervalIntegrable (fun u : ℝ => |quantile μ u - quantile ν u|)
      volume 0 1 := by
  /- Combine `aemeasurable_quantile_unifOI` with `quantile_mem_Icc_ae`;
     the distance is bounded by `b-a` almost everywhere. -/
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => |quantile μ u - quantile ν u|) unifOI :=
    by simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (((aemeasurable_quantile_unifOI μ).sub
        (aemeasurable_quantile_unifOI ν)).norm).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂unifOI,
      ‖|quantile μ u - quantile ν u|‖ ≤ b - a := by
    filter_upwards [quantile_mem_Icc_ae μ hμ, quantile_mem_Icc_ae ν hν] with u hu hv
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_le.mpr ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = unifOI := by
    rw [unifOI, restrict_Ioo_eq_restrict_Ioc]
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
  change Integrable (fun u : ℝ => |quantile μ u - quantile ν u|)
    (volume.restrict (Ioc (0 : ℝ) 1))
  rw [hrest]
  exact Integrable.of_bound hmeas (b - a) hbound

private lemma integral_abs_cut_indicators (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ u in (0 : ℝ)..1,
      |(if u ≤ p then (1 : ℝ) else 0) - (if u ≤ q then 1 else 0)|) =
      |p - q| := by
  by_cases hpq : p ≤ q
  · have heq : ∀ u : ℝ, |(if u ≤ p then (1 : ℝ) else 0) -
        (if u ≤ q then 1 else 0)| =
        (Ioc p q).indicator (fun _ => (1 : ℝ)) u := by
      intro u
      by_cases hpu : u ≤ p <;> by_cases hqu : u ≤ q <;>
        simp [Set.indicator, hpu, hqu, Set.mem_Ioc] <;> linarith
    simp_rw [heq]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hs : Ioc (0 : ℝ) 1 ∩ Ioc p q = Ioc p q := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · exact And.right
      · intro hu
        exact ⟨⟨lt_of_le_of_lt hp0 hu.1, hu.2.trans hq1⟩, hu⟩
    rw [hs, setIntegral_const]
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hpq),
      abs_of_nonpos (sub_nonpos.mpr hpq)]
  · have hqp : q ≤ p := le_of_not_ge hpq
    have heq : ∀ u : ℝ, |(if u ≤ p then (1 : ℝ) else 0) -
        (if u ≤ q then 1 else 0)| =
        (Ioc q p).indicator (fun _ => (1 : ℝ)) u := by
      intro u
      by_cases hpu : u ≤ p <;> by_cases hqu : u ≤ q <;>
        simp [Set.indicator, hpu, hqu, Set.mem_Ioc] <;> linarith
    simp_rw [heq]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hs : Ioc (0 : ℝ) 1 ∩ Ioc q p = Ioc q p := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · exact And.right
      · intro hu
        exact ⟨⟨lt_of_le_of_lt hq0 hu.1, hu.2.trans hp1⟩, hu⟩
    rw [hs, setIntegral_const]
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hqp),
      abs_of_nonneg (sub_nonneg.mpr hqp)]

/-- [Two probability laws and a threshold](hyp:μ,ν,t) have [a mean lower-ray
indicator disagreement equal to the absolute difference of their CDFs there](goal). -/
lemma threshold_indicator_integral_eq_cdf_distance (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) :
    (∫ u in (0 : ℝ)..1,
      |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
        (if quantile ν u ≤ t then 1 else 0)|) =
      |cdf μ t - cdf ν t| := by
  /- On (0,1), `quantile_le_iff` turns both predicates into
     `u ≤ cdf _ t`. Their symmetric difference is the interval between
     the two CDF values, including its right endpoint; that endpoint has
     zero Lebesgue measure. Use `cdf_nonneg` and `cdf_le_one`. -/
  have hcongr :
      (∫ u in (0 : ℝ)..1,
        |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
          (if quantile ν u ≤ t then 1 else 0)|) =
      ∫ u in (0 : ℝ)..1,
        |(if u ≤ cdf μ t then (1 : ℝ) else 0) -
          (if u ≤ cdf ν t then 1 else 0)| := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
    intro u hu
    change |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
      (if quantile ν u ≤ t then 1 else 0)| =
      |(if u ≤ cdf μ t then (1 : ℝ) else 0) -
        (if u ≤ cdf ν t then 1 else 0)|
    simp only [quantile_le_iff hu.1 hu.2]
  rw [hcongr]
  exact integral_abs_cut_indicators (cdf μ t) (cdf ν t)
    (cdf_nonneg μ t) (cdf_le_one μ t) (cdf_nonneg ν t) (cdf_le_one ν t)

/-- [Two probability laws](hyp:μ,ν) and [an ordered finite interval](hyp:hab)
give [an integrable lower-ray disagreement kernel under the product of the
uniform-level law and restricted Lebesgue measure](goal). -/
lemma indicator_kernel_integrable (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a ≤ b) :
    Integrable
      (fun z : ℝ × ℝ =>
        |(if quantile μ z.1 ≤ z.2 then (1 : ℝ) else 0) -
          (if quantile ν z.1 ≤ z.2 then 1 else 0)|)
      (unifOI.prod (volume.restrict (Ioc a b))) := by
  /- Pull a.e. measurability of each quantile on `unifOI` to the product;
     comparisons with the measurable second projection are a.e. measurable.
     The kernel is bounded by one, and the product measure is finite. -/
  let ρ : Measure (ℝ × ℝ) := unifOI.prod (volume.restrict (Ioc a b))
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  haveI : IsFiniteMeasure ρ := by dsimp [ρ]; infer_instance
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => quantile μ z.1) ρ :=
    (aemeasurable_quantile_unifOI μ).comp_fst |>.aestronglyMeasurable
  have hn : AEStronglyMeasurable (fun z : ℝ × ℝ => quantile ν z.1) ρ :=
    (aemeasurable_quantile_unifOI ν).comp_fst |>.aestronglyMeasurable
  have ht : AEStronglyMeasurable (fun z : ℝ × ℝ => z.2) ρ :=
    measurable_snd.aestronglyMeasurable
  have hc : AEStronglyMeasurable (fun _ : ℝ × ℝ => (1 : ℝ)) ρ :=
    aestronglyMeasurable_const
  have hμ : AEStronglyMeasurable
      (fun z : ℝ × ℝ => if quantile μ z.1 ≤ z.2 then (1 : ℝ) else 0) ρ := by
    convert hc.indicator₀ (nullMeasurableSet_le hm.aemeasurable ht.aemeasurable) using 1
    ext z
    simp [Set.indicator]
  have hν : AEStronglyMeasurable
      (fun z : ℝ × ℝ => if quantile ν z.1 ≤ z.2 then (1 : ℝ) else 0) ρ := by
    convert hc.indicator₀ (nullMeasurableSet_le hn.aemeasurable ht.aemeasurable) using 1
    ext z
    simp [Set.indicator]
  have hk : AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        |(if quantile μ z.1 ≤ z.2 then (1 : ℝ) else 0) -
          (if quantile ν z.1 ≤ z.2 then 1 else 0)|) ρ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hμ.sub hν).norm
  exact Integrable.of_bound hk 1 (by
    filter_upwards with z
    split_ifs <;> norm_num)

/-- [Two probability laws](hyp:μ,ν) and [an ordered finite interval](hyp:hab)
have [equal iterated lower-ray disagreement integrals in either order](goal). -/
lemma indicator_integral_swap (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a ≤ b) :
    (∫ u in (0 : ℝ)..1, ∫ t in a..b,
      |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
        (if quantile ν u ≤ t then 1 else 0)|) =
    ∫ t in a..b, ∫ u in (0 : ℝ)..1,
      |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
        (if quantile ν u ≤ t then 1 else 0)| := by
  /- Write both interval integrals as set integrals on `Ioc`, identify the
     first factor with `unifOI`, then use `integral_integral_swap` with
     `indicator_kernel_integrable`. -/
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = unifOI := by
    rw [unifOI, restrict_Ioo_eq_restrict_Ioc]
  simp_rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hrest]
  exact integral_integral_swap (indicator_kernel_integrable μ ν hab)

/-- [Two points in a common closed interval](hyp:hx,hy) have [a distance equal
to the integral of their lower-ray indicator disagreement](goal). -/
lemma abs_sub_eq_integral_Icc_indicator {a b x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |x - y| = ∫ t in a..b,
      |(if x ≤ t then (1 : ℝ) else 0) - (if y ≤ t then 1 else 0)| := by
  /- Split on `x ≤ y`. In the first branch the integrand is the indicator
     of `Ico x y`; in the second it is the indicator of `Ico y x`.
     Restrict to `Ioc a b`, then use `Real.volume_Ioc` (or the equal-volume
     half-open variant). Endpoint choices do not change the integral. -/
  by_cases hxy : x ≤ y
  · have heq : ∀ᵐ t ∂volume, |(if x ≤ t then (1 : ℝ) else 0) -
        (if y ≤ t then 1 else 0)| =
        (Ioc x y).indicator (fun _ => (1 : ℝ)) t := by
      filter_upwards [volume.ae_ne x, volume.ae_ne y] with t htx hty
      have hxt' : x < t ↔ x ≤ t := by
        constructor
        · exact le_of_lt
        · intro h
          exact lt_of_le_of_ne h (Ne.symm htx)
      have hyt' : t ≤ y ↔ t < y := by
        constructor
        · intro h
          exact lt_of_le_of_ne h hty
        · exact le_of_lt
      by_cases hxt : x ≤ t <;> by_cases hyt : y ≤ t <;>
        simp_all [Set.indicator, Set.mem_Ioc, not_le] <;> grind
    rw [intervalIntegral.integral_congr_ae (heq.mono fun t ht _ => ht)]
    rw [intervalIntegral.integral_of_le (le_trans hx.1 hx.2)]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hs : Ioc a b ∩ Ioc x y = Ioc x y := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · exact And.right
      · intro ht
        exact ⟨⟨lt_of_le_of_lt hx.1 ht.1, ht.2.trans hy.2⟩, ht⟩
    rw [hs, setIntegral_const]
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal
      (sub_nonneg.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hxy)]
  · have hyx : y ≤ x := le_of_not_ge hxy
    have heq : ∀ᵐ t ∂volume, |(if x ≤ t then (1 : ℝ) else 0) -
        (if y ≤ t then 1 else 0)| =
        (Ioc y x).indicator (fun _ => (1 : ℝ)) t := by
      filter_upwards [volume.ae_ne x, volume.ae_ne y] with t htx hty
      have hxt' : y < t ↔ y ≤ t := by
        constructor
        · exact le_of_lt
        · intro h
          exact lt_of_le_of_ne h (Ne.symm hty)
      have hyt' : t ≤ x ↔ t < x := by
        constructor
        · intro h
          exact lt_of_le_of_ne h htx
        · exact le_of_lt
      by_cases hxt : x ≤ t <;> by_cases hyt : y ≤ t <;>
        simp_all [Set.indicator, Set.mem_Ioc, not_le] <;> grind
    rw [intervalIntegral.integral_congr_ae (heq.mono fun t ht _ => ht)]
    rw [intervalIntegral.integral_of_le (le_trans hx.1 hx.2)]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hs : Ioc a b ∩ Ioc y x = Ioc y x := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · exact And.right
      · intro ht
        exact ⟨⟨lt_of_le_of_lt hy.1 ht.1, ht.2.trans hx.2⟩, ht⟩
    rw [hs, setIntegral_const]
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal
      (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr hyx)]

/-- [Two probability laws](hyp:μ,ν) [concentrated on one closed interval](hyp:hμ,hν)
have [a quantile cost equal to the iterated lower-ray indicator integral](goal). -/
lemma quantile_cost_eq_indicator_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0) :
    (∫ u in (0 : ℝ)..1, |quantile μ u - quantile ν u|) =
      ∫ u in (0 : ℝ)..1, ∫ t in a..b,
        |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
          (if quantile ν u ≤ t then 1 else 0)| := by
  /- Apply the preceding pointwise identity on the intersection of
     `quantile_mem_Icc_ae μ hμ` and `quantile_mem_Icc_ae ν hν`. Convert
     `unifOI` to the interval restriction on `Ioc 0 1` as in
     `intervalIntegrable_abs_quantile_sub`, then use
     `intervalIntegral.integral_congr_ae`. -/
  have hrest : volume.restrict (Ioc (0 : ℝ) 1) = unifOI := by
    rw [unifOI, restrict_Ioo_eq_restrict_Ioc]
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hrest]
  filter_upwards [quantile_mem_Icc_ae μ hμ, quantile_mem_Icc_ae ν hν] with u hu hv
  exact abs_sub_eq_integral_Icc_indicator hu hv

/-- [Two probability laws](hyp:μ,ν), [an ordered common closed interval](hyp:hab),
and [concentration of each law on it](hyp:hμ,hν) give [an iterated
quantile-indicator integral equal to their integrated CDF distance](goal). -/
lemma indicator_integral_eq_cdf_distance (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0) :
    (∫ u in (0 : ℝ)..1, ∫ t in a..b,
      |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
        (if quantile ν u ≤ t then 1 else 0)|) =
      ∫ t in a..b, |cdf μ t - cdf ν t| := by
  calc
    _ = ∫ t in a..b, ∫ u in (0 : ℝ)..1,
          |(if quantile μ u ≤ t then (1 : ℝ) else 0) -
            (if quantile ν u ≤ t then 1 else 0)| :=
      indicator_integral_swap μ ν hab
    _ = ∫ t in a..b, |cdf μ t - cdf ν t| := by
      apply intervalIntegral.integral_congr
      intro t _
      exact threshold_indicator_integral_eq_cdf_distance μ ν t

/-- [Two probability laws](hyp:μ,ν), [an ordered common compact interval](hyp:hab),
and [concentration of both laws on that interval](hyp:hμ,hν) give [the identity
between shared-uniform quantile transport cost and integrated CDF distance](goal). -/
theorem quantile_transport_eq_cdf_distance (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0) :
    (∫ u in (0 : ℝ)..1, |quantile μ u - quantile ν u|) =
      ∫ t in a..b, |cdf μ t - cdf ν t| := by
  exact (quantile_cost_eq_indicator_integral μ ν hμ hν).trans
    (indicator_integral_eq_cdf_distance μ ν hab hμ hν)

end Causalean.Stat.Quantile.Transport
