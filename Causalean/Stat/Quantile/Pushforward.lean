module
public import Causalean.Stat.Quantile.Transport
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lipschitz pushforwards of one-dimensional quantile transport

This module proves that applying a measurable Lipschitz transformation to two
compactly supported real probability laws cannot increase their shared-uniform
quantile transport cost by more than the Lipschitz factor.  The proof works
through arbitrary couplings, so it applies unchanged to atomic laws and to
decreasing transformations.
-/

public section

open MeasureTheory ProbabilityTheory Set Causalean.Stat

namespace Causalean.Stat.Quantile.Pushforward

/-- [Two probability laws](hyp:μ,ν) [concentrated on the common closed interval
from `a` to `b`](hyp:a,b,hμ,hν) and [a coupling of them](hyp:π,hπ) have
[an integrable absolute coordinate difference](goal). -/
lemma coupling_abs_cost_integrable (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) π := by
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have h₁ : ∀ᵐ z ∂π, z.1 ∈ Icc a b := by
    have hh : ∀ᵐ x ∂μ, x ∈ Icc a b := by
      rw [ae_iff]
      exact hμ
    rw [← hπ.map_fst] at hh
    exact (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp hh
  have h₂ : ∀ᵐ z ∂π, z.2 ∈ Icc a b := by
    have hh : ∀ᵐ x ∂ν, x ∈ Icc a b := by
      rw [ae_iff]
      exact hν
    rw [← hπ.map_snd] at hh
    exact (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mp hh
  apply Integrable.of_bound (by fun_prop) (b - a)
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  rw [Real.norm_eq_abs, abs_abs]
  exact abs_le.mpr ⟨by linarith [hz₁.1, hz₂.2], by linarith [hz₁.2, hz₂.1]⟩

/-- [Two probability laws](hyp:μ,ν), [a coupling of them](hyp:π,hπ), and
[a threshold](hyp:t) have [a CDF difference at that threshold bounded by the
coupling's expected lower-ray-indicator disagreement](goal). -/
lemma cdf_distance_le_threshold_disagreement (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) (t : ℝ) :
    |cdf μ t - cdf ν t| ≤
      ∫ z : ℝ × ℝ,
        |(if z.1 ≤ t then (1 : ℝ) else 0) -
          (if z.2 ≤ t then 1 else 0)| ∂π := by
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hind (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      (∫ x : ℝ, (if x ≤ t then (1 : ℝ) else 0) ∂ρ) = cdf ρ t := by
    have heq : (fun x : ℝ => if x ≤ t then (1 : ℝ) else 0) =
        (Iic t).indicator (fun _ => (1 : ℝ)) := by
      funext x
      simp [Set.indicator, Set.mem_Iic]
    rw [heq, integral_indicator measurableSet_Iic, setIntegral_const, cdf_eq_real]
    simp [measureReal_def]
  have hm : Measurable (fun x : ℝ => if x ≤ t then (1 : ℝ) else 0) := by
    convert (measurable_const.indicator measurableSet_Iic :
      Measurable ((Iic t).indicator (fun _ : ℝ => (1 : ℝ)))) using 1
    funext x
    by_cases hx : x ≤ t <;> simp [Set.indicator, hx]
  have h₁ : Integrable (fun z : ℝ × ℝ => if z.1 ≤ t then (1 : ℝ) else 0) π := by
    apply Integrable.of_bound (hm.comp measurable_fst).aestronglyMeasurable 1
    filter_upwards with z
    change ‖if z.1 ≤ t then (1 : ℝ) else 0‖ ≤ 1
    split_ifs <;> norm_num
  have h₂ : Integrable (fun z : ℝ × ℝ => if z.2 ≤ t then (1 : ℝ) else 0) π := by
    apply Integrable.of_bound (hm.comp measurable_snd).aestronglyMeasurable 1
    filter_upwards with z
    change ‖if z.2 ≤ t then (1 : ℝ) else 0‖ ≤ 1
    split_ifs <;> norm_num
  have hμ' : (∫ z : ℝ × ℝ, (if z.1 ≤ t then (1 : ℝ) else 0) ∂π) = cdf μ t := by
    calc
      _ = ∫ x : ℝ, (if x ≤ t then (1 : ℝ) else 0) ∂μ := by
        rw [← hπ.map_fst, integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable]
      _ = cdf μ t := hind μ
  have hν' : (∫ z : ℝ × ℝ, (if z.2 ≤ t then (1 : ℝ) else 0) ∂π) = cdf ν t := by
    calc
      _ = ∫ x : ℝ, (if x ≤ t then (1 : ℝ) else 0) ∂ν := by
        rw [← hπ.map_snd, integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable]
      _ = cdf ν t := hind ν
  rw [← hμ', ← hν', ← integral_sub h₁ h₂]
  exact abs_integral_le_integral_abs

/-- [Two probability laws](hyp:μ,ν) [concentrated on the ordered common closed
interval from `a` to `b`](hyp:a,b,hab,hμ,hν) and [a coupling](hyp:π,hπ) have
[integrated lower-ray disagreement equal to expected absolute coordinate
distance](goal). -/
lemma coupling_indicator_integral_eq_cost (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    (∫ t in a..b, ∫ z : ℝ × ℝ,
      |(if z.1 ≤ t then (1 : ℝ) else 0) -
        (if z.2 ≤ t then 1 else 0)| ∂π) =
      ∫ z : ℝ × ℝ, |z.1 - z.2| ∂π := by
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  let ρ : Measure ℝ := volume.restrict (Ioc a b)
  haveI : IsFiniteMeasure ρ := by
    dsimp [ρ]
    exact isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let k : ℝ → (ℝ × ℝ) → ℝ := fun t z =>
    |(if z.1 ≤ t then (1 : ℝ) else 0) - (if z.2 ≤ t then 1 else 0)|
  have hk : Integrable (fun p : ℝ × (ℝ × ℝ) => k p.1 p.2) (ρ.prod π) := by
    have h₁ : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        if p.2.1 ≤ p.1 then (1 : ℝ) else 0) := by
      exact measurable_const.ite (measurableSet_le measurable_snd.fst measurable_fst)
        measurable_const
    have h₂ : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        if p.2.2 ≤ p.1 then (1 : ℝ) else 0) := by
      exact measurable_const.ite (measurableSet_le measurable_snd.snd measurable_fst)
        measurable_const
    have hm : Measurable (fun p : ℝ × (ℝ × ℝ) => k p.1 p.2) := by
      simpa [k, Real.norm_eq_abs] using (h₁.sub h₂).norm
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards with p
    change ‖|(if p.2.1 ≤ p.1 then (1 : ℝ) else 0) -
      (if p.2.2 ≤ p.1 then 1 else 0)|‖ ≤ 1
    split_ifs <;> norm_num
  have hswap : (∫ t in a..b, ∫ z : ℝ × ℝ, k t z ∂π) =
      ∫ z : ℝ × ℝ, (∫ t in a..b, k t z) ∂π := by
    simp_rw [intervalIntegral.integral_of_le hab]
    simpa only [ρ] using (integral_integral_swap (f := k) hk)
  have h₁ : ∀ᵐ z ∂π, z.1 ∈ Icc a b := by
    have hh : ∀ᵐ x ∂μ, x ∈ Icc a b := by
      rw [ae_iff]
      exact hμ
    rw [← hπ.map_fst] at hh
    exact (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp hh
  have h₂ : ∀ᵐ z ∂π, z.2 ∈ Icc a b := by
    have hh : ∀ᵐ x ∂ν, x ∈ Icc a b := by
      rw [ae_iff]
      exact hν
    rw [← hπ.map_snd] at hh
    exact (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mp hh
  change (∫ t in a..b, ∫ z : ℝ × ℝ, k t z ∂π) =
    ∫ z : ℝ × ℝ, |z.1 - z.2| ∂π
  rw [hswap]
  apply integral_congr_ae
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  exact (Causalean.Stat.Quantile.Transport.abs_sub_eq_integral_Icc_indicator hz₁ hz₂).symm

/-- [Two probability laws](hyp:μ,ν) [concentrated on the ordered common closed
interval from `a` to `b`](hyp:a,b,hab,hμ,hν) and [a coupling](hyp:π,hπ) have
[integrated CDF distance no larger than the coupling's expected absolute
coordinate distance](goal). -/
theorem cdf_distance_le_coupling_cost (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    (∫ t in a..b, |cdf μ t - cdf ν t|) ≤
      ∫ z : ℝ × ℝ, |z.1 - z.2| ∂π := by
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  let ρ : Measure ℝ := volume.restrict (Ioc a b)
  haveI : IsFiniteMeasure ρ := by
    dsimp [ρ]
    exact isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let k : ℝ → (ℝ × ℝ) → ℝ := fun t z =>
    |(if z.1 ≤ t then (1 : ℝ) else 0) - (if z.2 ≤ t then 1 else 0)|
  have hk : Integrable (fun p : ℝ × (ℝ × ℝ) => k p.1 p.2) (ρ.prod π) := by
    have h₁ : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        if p.2.1 ≤ p.1 then (1 : ℝ) else 0) := by
      exact measurable_const.ite (measurableSet_le measurable_snd.fst measurable_fst)
        measurable_const
    have h₂ : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        if p.2.2 ≤ p.1 then (1 : ℝ) else 0) := by
      exact measurable_const.ite (measurableSet_le measurable_snd.snd measurable_fst)
        measurable_const
    have hm : Measurable (fun p : ℝ × (ℝ × ℝ) => k p.1 p.2) := by
      simpa [k, Real.norm_eq_abs] using (h₁.sub h₂).norm
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards with p
    change ‖|(if p.2.1 ≤ p.1 then (1 : ℝ) else 0) -
      (if p.2.2 ≤ p.1 then 1 else 0)|‖ ≤ 1
    split_ifs <;> norm_num
  have hg : IntervalIntegrable (fun t : ℝ => ∫ z : ℝ × ℝ, k t z ∂π)
      volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    change Integrable (fun t : ℝ => ∫ z : ℝ × ℝ, k t z ∂π) ρ
    exact hk.integral_prod_left
  calc
    (∫ t in a..b, |cdf μ t - cdf ν t|) ≤
        ∫ t in a..b, ∫ z : ℝ × ℝ, k t z ∂π := by
      apply intervalIntegral.integral_mono hab
        (Causalean.Stat.Quantile.Transport.intervalIntegrable_abs_cdf_sub μ ν a b) hg
      intro t
      exact cdf_distance_le_threshold_disagreement μ ν hπ t
    _ = ∫ z : ℝ × ℝ, |z.1 - z.2| ∂π :=
      coupling_indicator_integral_eq_cost μ ν hab hμ hν hπ

/-- [Two probability laws](hyp:μ,ν) [concentrated on the ordered common closed
interval from `a` to `b`](hyp:a,b,hab,hμ,hν) and [a coupling](hyp:π,hπ) have
[shared-uniform quantile cost no larger than the coupling's expected absolute
coordinate distance](goal). -/
theorem quantile_cost_le_coupling_cost (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    (∫ u in (0 : ℝ)..1, |quantile μ u - quantile ν u|) ≤
      ∫ z : ℝ × ℝ, |z.1 - z.2| ∂π := by
  rw [Causalean.Stat.Quantile.Transport.quantile_transport_eq_cdf_distance
    μ ν hab hμ hν]
  exact cdf_distance_le_coupling_cost μ ν hab hμ hν hπ

/-- [A measurable transformation](hyp:f,hf) sends [a coupling of two real
laws](hyp:μ,ν,π,hπ) to [a coupling of their transformed laws](goal) by acting
on both coordinates. -/
lemma map_pair_isCoupling (μ ν : Measure ℝ)
    (f : ℝ → ℝ) (hf : Measurable f)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    IsCoupling (π.map (fun z : ℝ × ℝ => (f z.1, f z.2))) (μ.map f) (ν.map f) := by
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hp : Measurable (fun z : ℝ × ℝ => (f z.1, f z.2)) :=
    (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  refine ⟨Measure.isProbabilityMeasure_map hp.aemeasurable, ?_, ?_⟩
  · calc
      (π.map (fun z : ℝ × ℝ => (f z.1, f z.2))).map Prod.fst
          = π.map (f ∘ Prod.fst) := by rw [Measure.map_map measurable_fst hp]; rfl
      _ = μ.map f := by rw [← hπ.map_fst, Measure.map_map hf measurable_fst]
  · calc
      (π.map (fun z : ℝ × ℝ => (f z.1, f z.2))).map Prod.snd
          = π.map (f ∘ Prod.snd) := by rw [Measure.map_map measurable_snd hp]; rfl
      _ = ν.map f := by rw [← hπ.map_snd, Measure.map_map hf measurable_snd]

/-- [A law](hyp:μ) [concentrated on the ordered interval from `a`
to `b`](hyp:a,b,hab,hμ), mapped by [a measurable transformation](hyp:f,hf)
with [a Lipschitz factor](hyp:L) [that is nonnegative](hyp:hL) [and controls the transformation on that interval](hyp:hLip), is
[concentrated on the corresponding bounded image interval](goal). -/
lemma map_supported_in_lipschitz_range (μ : Measure ℝ)
    {a b L : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hL : 0 ≤ L)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |f x - f y| ≤ L * |x - y|) :
    (μ.map f) (Icc (f a - L * (b - a)) (f a + L * (b - a)))ᶜ = 0 := by
  let J := Icc (f a - L * (b - a)) (f a + L * (b - a))
  have hpre : f ⁻¹' Jᶜ ⊆ (Icc a b)ᶜ := by
    intro x hx hxab
    have hax := hLip x hxab a ⟨le_refl a, hab⟩
    have hdist : |x - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr hxab.1)]
      linarith [hxab.2]
    have hbound : |f x - f a| ≤ L * (b - a) :=
      hax.trans (mul_le_mul_of_nonneg_left hdist hL)
    have hj : f x ∈ J := by
      dsimp [J]
      have hh := abs_le.mp hbound
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    exact hx hj
  change (μ.map f) Jᶜ = 0
  rw [Measure.map_apply hf measurableSet_Icc.compl]
  exact measure_mono_null hpre hμ

/-- [A coupling of two probability laws](hyp:μ,ν,π,hπ) [concentrated on the
ordered interval from `a` to `b`](hyp:a,b,hab,hμ,hν), mapped by [a measurable
transformation](hyp:f,hf) with [a Lipschitz factor](hyp:L) [that is nonnegative](hyp:hL) [and controls the transformation there](hyp:hLip), has [image absolute cost at most that factor times its source
cost](goal). -/
lemma mapped_coupling_cost_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b L : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    (hL : 0 ≤ L) (f : ℝ → ℝ) (hf : Measurable f)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |f x - f y| ≤ L * |x - y|)
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) :
    (∫ z : ℝ × ℝ, |z.1 - z.2| ∂(π.map (fun z : ℝ × ℝ => (f z.1, f z.2)))) ≤
      L * ∫ z : ℝ × ℝ, |z.1 - z.2| ∂π := by
  letI : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hp : Measurable (fun z : ℝ × ℝ => (f z.1, f z.2)) :=
    (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  have h₁ : ∀ᵐ z ∂π, z.1 ∈ Icc a b := by
    have hh : ∀ᵐ x ∂μ, x ∈ Icc a b := by rw [ae_iff]; exact hμ
    rw [← hπ.map_fst] at hh
    exact (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp hh
  have h₂ : ∀ᵐ z ∂π, z.2 ∈ Icc a b := by
    have hh : ∀ᵐ x ∂ν, x ∈ Icc a b := by rw [ae_iff]; exact hν
    rw [← hπ.map_snd] at hh
    exact (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mp hh
  have hle : ∀ᵐ z ∂π, |f z.1 - f z.2| ≤ L * |z.1 - z.2| := by
    filter_upwards [h₁, h₂] with z hz₁ hz₂
    exact hLip z.1 hz₁ z.2 hz₂
  have hsrc := coupling_abs_cost_integrable μ ν hμ hν hπ
  have hrhs : Integrable (fun z : ℝ × ℝ => L * |z.1 - z.2|) π :=
    hsrc.const_mul L
  have hlhs : Integrable (fun z : ℝ × ℝ => |f z.1 - f z.2|) π := by
    apply hrhs.mono'
    · exact ((hf.comp measurable_fst).sub (hf.comp measurable_snd)).norm.aestronglyMeasurable
    · filter_upwards [hle] with z hz
      rw [Real.norm_eq_abs, abs_abs]
      exact hz
  rw [integral_map hp.aemeasurable (by fun_prop : AEStronglyMeasurable
    (fun z : ℝ × ℝ => |z.1 - z.2|) (π.map (fun z : ℝ × ℝ => (f z.1, f z.2))))]
  calc
    (∫ z : ℝ × ℝ, |f z.1 - f z.2| ∂π) ≤
        ∫ z : ℝ × ℝ, L * |z.1 - z.2| ∂π :=
      integral_mono_ae hlhs hrhs hle
    _ = L * ∫ z : ℝ × ℝ, |z.1 - z.2| ∂π := by rw [integral_const_mul]

/-- [Two probability laws](hyp:μ,ν) [concentrated on an ordered common closed
interval](hyp:a,b,hab,hμ,hν), and [a measurable transformation](hyp:f,hf)
with [a Lipschitz factor](hyp:L) [that is nonnegative](hyp:hL) [and controls the transformation on that interval](hyp:hLip), have
[image quantile transport cost at most that factor times their source cost](goal). This conclusion allows atoms and decreasing transformations. -/
theorem quantile_pushforward_lipschitzOn (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b L : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    (hL : 0 ≤ L) (f : ℝ → ℝ) (hf : Measurable f)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |f x - f y| ≤ L * |x - y|) :
    (∫ u in (0 : ℝ)..1,
      |quantile (μ.map f) u - quantile (ν.map f) u|) ≤
      L * ∫ u in (0 : ℝ)..1, |quantile μ u - quantile ν u| := by
  letI : IsProbabilityMeasure (μ.map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (ν.map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let c := f a - L * (b - a)
  let d := f a + L * (b - a)
  have hcd : c ≤ d := by
    dsimp [c, d]
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    nlinarith [mul_nonneg hL hba]
  have hμ' : (μ.map f) (Icc c d)ᶜ = 0 :=
    map_supported_in_lipschitz_range μ hab hμ hL f hf hLip
  have hν' : (ν.map f) (Icc c d)ᶜ = 0 :=
    map_supported_in_lipschitz_range ν hab hν hL f hf hLip
  let π := comonotoneCoupling μ ν
  have hπ : IsCoupling π μ ν := isCoupling_comonotoneCoupling μ ν
  have hπ' : IsCoupling (π.map (fun z : ℝ × ℝ => (f z.1, f z.2)))
      (μ.map f) (ν.map f) := map_pair_isCoupling μ ν f hf hπ
  have hopt := quantile_cost_le_coupling_cost (μ.map f) (ν.map f)
    hcd hμ' hν' hπ'
  have hcost := mapped_coupling_cost_le μ ν hab hμ hν hL f hf hLip hπ
  have hquant :
      (∫ z : ℝ × ℝ, |z.1 - z.2| ∂π) =
        ∫ u in (0 : ℝ)..1, |quantile μ u - quantile ν u| := by
    have hpair : AEMeasurable (fun u : ℝ => (quantile μ u, quantile ν u)) unifOI :=
      (aemeasurable_quantile_unifOI μ).prodMk (aemeasurable_quantile_unifOI ν)
    have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => |z.1 - z.2|) π := by
      fun_prop
    change (∫ z : ℝ × ℝ, |z.1 - z.2| ∂
      (unifOI.map (fun u : ℝ => (quantile μ u, quantile ν u)))) = _
    rw [integral_map hpair hmeas]
    have hrest : volume.restrict (Ioc (0 : ℝ) 1) = unifOI := by
      rw [unifOI, restrict_Ioo_eq_restrict_Ioc]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hrest]
  exact hopt.trans (hcost.trans_eq (congrArg (L * ·) hquant))

/-- [Two probability laws](hyp:μ,ν) [concentrated on an ordered common closed
interval](hyp:a,b,hab,hμ,hν), and [a measurable globally Lipschitz
transformation](hyp:f,hf,L,hL,hLip), have [image quantile transport cost at
most the global Lipschitz factor times their source cost](goal). -/
theorem quantile_pushforward_lipschitz (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b L : ℝ} (hab : a ≤ b)
    (hμ : μ (Icc a b)ᶜ = 0) (hν : ν (Icc a b)ᶜ = 0)
    (hL : 0 ≤ L) (f : ℝ → ℝ) (hf : Measurable f)
    (hLip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) :
    (∫ u in (0 : ℝ)..1,
      |quantile (μ.map f) u - quantile (ν.map f) u|) ≤
      L * ∫ u in (0 : ℝ)..1, |quantile μ u - quantile ν u| := by
  exact quantile_pushforward_lipschitzOn μ ν hab hμ hν hL f hf
    (fun x _ y _ => hLip x y)

end Causalean.Stat.Quantile.Pushforward
