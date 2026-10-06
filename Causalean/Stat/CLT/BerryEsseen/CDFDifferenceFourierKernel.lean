module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceIntegrable

/-! # An integrable oriented interval kernel

The signed half-line indicators below have support between their endpoints.
Finite first moments make the resulting Fourier kernel integrable over two
independent observations and Lebesgue measure. This is the domination needed
for the CDF Fourier Fubini interchange.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The signed Fourier kernel of the interval oriented from `a` to `b` is
the Fourier exponential times `1_{a ≤ x} - 1_{b ≤ x}`. The choice of weak
inequality makes averaging over laws with atoms recover their `Iic` CDFs. -/
noncomputable def orientedFourierKernel (t a b x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
    (((if a ≤ x then 1 else 0 : ℝ) - (if b ≤ x then 1 else 0 : ℝ)) : ℂ)

private theorem norm_orientedFourierKernel (t a b x : ℝ) :
    ‖orientedFourierKernel t a b x‖ =
      (Set.Ico a b).indicator (1 : ℝ → ℝ) x +
      (Set.Ico b a).indicator (1 : ℝ → ℝ) x := by
  simp only [orientedFourierKernel, norm_mul, Complex.norm_exp_ofReal_mul_I,
    one_mul, Set.indicator_apply, Set.mem_Ico]
  split_ifs <;> simp_all <;> linarith

private theorem measurable_orientedFourierKernel (t : ℝ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ =>
      orientedFourierKernel t p.1.1 p.1.2 p.2) := by
  have h₁ : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.1 ≤ p.2} :=
    measurableSet_le (measurable_fst.comp measurable_fst) measurable_snd
  have h₂ : MeasurableSet {p : (ℝ × ℝ) × ℝ | p.1.2 ≤ p.2} :=
    measurableSet_le (measurable_snd.comp measurable_fst) measurable_snd
  unfold orientedFourierKernel
  have hm₁ : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      if p.1.1 ≤ p.2 then (1 : ℝ) else 0) :=
    measurable_const.ite h₁ measurable_const
  have hm₂ : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      if p.1.2 ≤ p.2 then (1 : ℝ) else 0) :=
    measurable_const.ite h₂ measurable_const
  exact ((measurable_const.mul measurable_snd).complex_ofReal.mul
    measurable_const).cexp.mul (hm₁.complex_ofReal.sub hm₂.complex_ofReal)

private theorem integral_norm_orientedFourierKernel (t a b : ℝ) :
    ∫ x, ‖orientedFourierKernel t a b x‖ = |b - a| := by
  simp_rw [norm_orientedFourierKernel]
  rw [integral_add]
  · rw [integral_indicator_one measurableSet_Ico,
      integral_indicator_one measurableSet_Ico, Real.volume_real_Ico,
      Real.volume_real_Ico]
    rcases le_total a b with hab | hba
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      simp [max_eq_left (sub_nonneg.mpr hab), max_eq_right (sub_nonpos.mpr hab)]
    · rw [abs_of_nonpos (sub_nonpos.mpr hba)]
      simp [max_eq_right (sub_nonpos.mpr hba), max_eq_left (sub_nonneg.mpr hba)]
  · exact ((integrableOn_const (μ := (volume : Measure ℝ))
      (s := Set.Ico a b) (by simp)).integrable_indicator measurableSet_Ico)
  · exact ((integrableOn_const (μ := (volume : Measure ℝ))
      (s := Set.Ico b a) (by simp)).integrable_indicator measurableSet_Ico)

private theorem orientedFourierKernel_integrable_fiber (t a b : ℝ) :
    Integrable (fun x => orientedFourierKernel t a b x) volume := by
  have hm : Measurable (fun x => orientedFourierKernel t a b x) := by
    have hm' := (measurable_orientedFourierKernel t).comp
      (show Measurable (fun x : ℝ => ((a, b), x)) from
        measurable_const.prodMk measurable_id)
    simpa only [Function.comp_def] using hm'
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  simp_rw [norm_orientedFourierKernel]
  exact
    ((integrableOn_const (μ := (volume : Measure ℝ)) (s := Set.Ico a b)
      (by simp)).integrable_indicator measurableSet_Ico).add
      ((integrableOn_const (μ := (volume : Measure ℝ)) (s := Set.Ico b a)
        (by simp)).integrable_indicator measurableSet_Ico)

/-- For [two probability laws with finite first moments](hyp:hμ,hν),
[the oriented interval Fourier kernel is integrable jointly in its two
endpoints, drawn independently from the two laws, and the Lebesgue
variable](goal). -/
theorem orientedFourierKernel_integrable
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun a : ℝ => a) μ)
    (hν : Integrable (fun b : ℝ => b) ν)
    (t : ℝ) :
    Integrable
      (fun p : ℝ × (ℝ × ℝ) => orientedFourierKernel t p.1 p.2.1 p.2.2)
      (μ.prod (ν.prod volume)) := by
  have hpair : Integrable (fun p : ℝ × ℝ => |p.2 - p.1|) (μ.prod ν) := by
    have hh := ((hν.comp_snd μ).sub (hμ.comp_fst ν)).abs
    simpa only [Pi.sub_apply] using hh
  have hgroup : Integrable
      (fun p : (ℝ × ℝ) × ℝ => orientedFourierKernel t p.1.1 p.1.2 p.2)
      ((μ.prod ν).prod volume) := by
    apply (integrable_prod_iff
      (measurable_orientedFourierKernel t).aestronglyMeasurable).mpr
    constructor
    · filter_upwards [] with p
      exact orientedFourierKernel_integrable_fiber t p.1 p.2
    · simpa only [integral_norm_orientedFourierKernel] using hpair
  apply ((measurePreserving_prodAssoc μ ν (volume : Measure ℝ)).integrable_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding).mp
  simpa [Function.comp_def, MeasurableEquiv.prodAssoc] using hgroup

end Causalean.Stat.CLT.BerryEsseen
