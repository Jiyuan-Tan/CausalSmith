module
public import Causalean.Stat.Minimax.OverlapCoupling
public import Causalean.Stat.Minimax.Pinsker

/-!
# Kullback--Leibler likelihood-ratio tails

This file develops the likelihood-ratio truncation estimates used in the
Tsybakov form of Fano's method. The positive log-likelihood tail is bounded by
KL plus its Pinsker correction, and measurable event probabilities are
compared across absolutely continuous laws below a likelihood threshold.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped ENNReal

private lemma density_mul_negPart_log_le_negPart_sub_one {x : ℝ} (hx : 0 ≤ x) :
    x * (-Real.log x)⁺ ≤ (x - 1)⁻ := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  by_cases hx1 : x ≤ 1
  · rw [negPart_eq_neg.mpr (sub_nonpos.mpr hx1)]
    have hlog : -Real.log x ≤ x⁻¹ - 1 := by
      rw [← Real.log_inv]
      exact Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    have := mul_le_mul_of_nonneg_left hlog hx.le
    field_simp [hx.ne'] at this ⊢
    by_cases hlog0 : Real.log x ≤ 0
    · rw [posPart_eq_self.mpr (neg_nonneg.mpr hlog0)]
      nlinarith
    · rw [posPart_eq_zero.mpr (neg_nonpos.mpr (le_of_not_ge hlog0))]
      nlinarith
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    rw [negPart_eq_zero.mpr (sub_nonneg.mpr hx1')]
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1'
    rw [posPart_eq_zero.mpr (neg_nonpos.mpr hlog0)]
    simp

/-- For [two probability laws](hyp:μ,ν), if [the first is absolutely continuous
with respect to the second](hyp:hac) and [their log-likelihood ratio is
integrable](hyp:hint), then [the expected negative part of that log-likelihood
ratio is at most their total-variation distance](goal). -/
theorem llr_negPart_integral_le_tvDist
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ) :
    ∫ x, (-llr μ ν x)⁺ ∂μ ≤ tvDist μ ν := by
  let p : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal
  let d : Ω → ℝ := fun x => p x - 1
  have hp : Integrable p ν := Measure.integrable_toReal_rnDeriv
  have hd : Integrable d ν := hp.sub (integrable_const 1)
  have hd0 : ∫ x, d x ∂ν = 0 := by
    rw [show d = fun x => p x - 1 from rfl, integral_sub hp (integrable_const 1)]
    rw [show p = fun x => (μ.rnDeriv ν x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hac]
    simp [probReal_univ]
  have hneg : Integrable (fun x => (-llr μ ν x)⁺) μ := by
    simp only [PosPart.posPart]
    exact hint.neg.sup (integrable_const 0)
  rw [← integral_toReal_rnDeriv_mul hac]
  have hpoint : ∀ x,
      p x * (-llr μ ν x)⁺ ≤ (d x)⁻ := by
    intro x
    simpa [p, d, llr] using
      density_mul_negPart_log_le_negPart_sub_one
        (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv ν x).toReal)
  have hle :
      ∫ x, p x * (-llr μ ν x)⁺ ∂ν ≤ ∫ x, (d x)⁻ ∂ν := by
    apply integral_mono
    · exact (integrable_toReal_rnDeriv_mul_iff hac).2 hneg
    · simp only [NegPart.negPart]
      exact hd.neg.sup (integrable_const 0)
    · exact hpoint
  refine hle.trans ?_
  have habs := integral_abs_eq_two_mul_integral_negPart_add_integral hd
  rw [hd0, add_zero] at habs
  have htv := tvDist_eq_half_integral_abs_rnDeriv_sub μ ν ν hac (by rfl)
  have hrnself :
      (fun x => |(μ.rnDeriv ν x).toReal - (ν.rnDeriv ν x).toReal|) =ᵐ[ν]
        fun x => |d x| := by
    filter_upwards [Measure.rnDeriv_self ν] with x hx
    simp [d, p, hx]
  rw [integral_congr_ae hrnself] at htv
  rw [htv, habs]
  ring_nf
  exact le_rfl

/-- For [two probability laws](hyp:μ,ν), [absolute continuity](hyp:hac), an
[integrable log-likelihood ratio](hyp:hint), and a [positive threshold](hyp:t,ht),
[the probability under the first law that the log-likelihood ratio exceeds the
threshold is at most `(KL + sqrt(KL/2)) / t`](goal). -/
theorem llr_tail_le_kl_add_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {x | t < llr μ ν x} ≤
      ((InformationTheory.klDiv μ ν).toReal +
        Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2)) / t := by
  let f : Ω → ℝ := llr μ ν
  have hf : Integrable f μ := hint
  have hpos : Integrable (fun x => (f x)⁺) μ := by
    simp only [PosPart.posPart]
    exact hf.sup (integrable_const 0)
  have hneg : Integrable (fun x => (-f x)⁺) μ := by
    simp only [PosPart.posPart]
    exact hf.neg.sup (integrable_const 0)
  have hsplit :
      ∫ x, (f x)⁺ ∂μ = ∫ x, f x ∂μ + ∫ x, (-f x)⁺ ∂μ := by
    rw [← integral_add hf hneg]
    apply integral_congr_ae
    filter_upwards [] with x
    rcases le_total 0 (f x) with hx | hx
    · simp [hx]
    · simp [hx]
  have hkl :
      (InformationTheory.klDiv μ ν).toReal = ∫ x, f x ∂μ := by
    exact InformationTheory.toReal_klDiv_of_measure_eq hac (by simp [measure_univ])
  have hfin : InformationTheory.klDiv μ ν ≠ ⊤ :=
    InformationTheory.klDiv_ne_top_iff.mpr ⟨hac, hint⟩
  have hpinsker := pinskerBound_of_ac_of_ne_top μ ν hac hfin
  have hnegLe : ∫ x, (-f x)⁺ ∂μ ≤ tvDist μ ν := by
    exact llr_negPart_integral_le_tvDist μ ν hac hint
  have hposLe :
      ∫ x, (f x)⁺ ∂μ ≤
        (InformationTheory.klDiv μ ν).toReal +
          Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2) := by
    rw [hsplit, ← hkl]
    exact add_le_add le_rfl (hnegLe.trans hpinsker)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun x => (f x)⁺)
    (Filter.Eventually.of_forall fun x => posPart_nonneg (f x)) hpos t
  have hsubset : {x | t < f x} ⊆ {x | t ≤ (f x)⁺} := by
    intro x hx
    exact hx.le.trans (le_posPart (f x))
  have hmono : μ.real {x | t < f x} ≤ μ.real {x | t ≤ (f x)⁺} :=
    measureReal_mono hsubset (measure_ne_top _ _)
  have hmul : t * μ.real {x | t < f x} ≤ ∫ x, (f x)⁺ ∂μ :=
    (mul_le_mul_of_nonneg_left hmono ht.le).trans hmarkov
  change μ.real {x | t < f x} ≤ _
  rw [le_div_iff₀ ht]
  simpa [mul_comm] using hmul.trans hposLe

/-- For [two probability laws](hyp:μ,ν), [absolute continuity](hyp:hac), a
[measurable event](hyp:A,hA), and a [log-likelihood threshold](hyp:t), [the
first law's event probability is at most `exp(t)` times the second law's event
probability plus the first law's above-threshold probability](goal). -/
theorem measureReal_le_exp_mul_add_llr_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) {A : Set Ω} (hA : MeasurableSet A) (t : ℝ) :
    μ.real A ≤ Real.exp t * ν.real A + μ.real {x | t < llr μ ν x} := by
  let B : Set Ω := {x | llr μ ν x ≤ t}
  let T : Set Ω := {x | t < llr μ ν x}
  let p : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hB : MeasurableSet B :=
    measurableSet_le (measurable_llr μ ν) measurable_const
  have hT : MeasurableSet T :=
    measurableSet_lt measurable_const (measurable_llr μ ν)
  have hcover : A ⊆ (A ∩ B) ∪ T := by
    intro x hx
    by_cases hxt : t < llr μ ν x
    · exact Or.inr hxt
    · exact Or.inl ⟨hx, le_of_not_gt hxt⟩
  have hp : Integrable p ν := Measure.integrable_toReal_rnDeriv
  have hp_bound : μ.real (A ∩ B) ≤ Real.exp t * ν.real A := by
    rw [← Measure.setIntegral_toReal_rnDeriv hac (A ∩ B)]
    calc
      ∫ x in A ∩ B, p x ∂ν ≤ ∫ _x in A ∩ B, Real.exp t ∂ν := by
        apply setIntegral_mono_on hp.integrableOn (integrable_const _)
          (hA.inter hB)
        intro x hx
        dsimp [p]
        by_cases hpx : (μ.rnDeriv ν x).toReal = 0
        · rw [hpx]
          exact (Real.exp_pos t).le
        · rw [← Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hpx))]
          exact Real.exp_le_exp.mpr hx.2
      _ = Real.exp t * ν.real (A ∩ B) := by
        rw [setIntegral_const]
        simp [mul_comm]
      _ ≤ Real.exp t * ν.real A := by
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono Set.inter_subset_left (measure_ne_top _ _))
          (Real.exp_pos t).le
  calc
    μ.real A ≤ μ.real ((A ∩ B) ∪ T) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ.real (A ∩ B) + μ.real T := measureReal_union_le _ _
    _ ≤ Real.exp t * ν.real A + μ.real T := add_le_add hp_bound le_rfl
    _ = Real.exp t * ν.real A + μ.real {x | t < llr μ ν x} := rfl

end Causalean.Stat
