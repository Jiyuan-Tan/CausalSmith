module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL.Density

/-!
# Selected-law log likelihood

Uniformly interior cell probabilities make the selected-law log likelihood
ratio a bounded measurable function and therefore integrable.
-/

public section

open MeasureTheory

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

private theorem cellMass_mem_Icc {η p q₀ q₁ : ℝ} (hη : 0 < η)
    (hp : p ∈ Set.Icc η (1 - η))
    (hq₀ : q₀ ∈ Set.Icc η (1 - η))
    (hq₁ : q₁ ∈ Set.Icc η (1 - η)) (a y : Bool) :
    cellMass p q₀ q₁ a y ∈ Set.Icc (η ^ 2) 1 := by
  have hbit (t : ℝ) (ht : t ∈ Set.Icc η (1 - η)) (b : Bool) :
      bitMass t b ∈ Set.Icc η 1 := by
    cases b with
    | false =>
        change η ≤ 1 - t ∧ 1 - t ≤ 1
        constructor <;> linarith [ht.1, ht.2]
    | true =>
        change η ≤ t ∧ t ≤ 1
        constructor <;> linarith [ht.1, ht.2]
  unfold cellMass
  have h₁ := hbit p hp a
  have h₂ : bitMass (if a then q₁ else q₀) y ∈ Set.Icc η 1 := by
    cases a with
    | false => exact hbit q₀ hq₀ y
    | true => exact hbit q₁ hq₁ y
  constructor
  · simpa [pow_two] using
      (mul_le_mul h₁.1 h₂.1 hη.le (le_trans hη.le h₁.1))
  · simpa using
      (mul_le_mul h₁.2 h₂.2 (le_trans hη.le h₂.1) (by norm_num : (0 : ℝ) ≤ 1))

private theorem measurable_selectedCellRatio {X : Type u} [MeasurableSpace X]
    {e q₀ q₁ q₀' q₁' : X → ℝ} (he : Measurable e)
    (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁') :
    Measurable (selectedCellRatio e q₀ q₁ q₀' q₁') := by
  have hc (p q s : X → ℝ) (hp : Measurable p) (hq : Measurable q)
      (hs : Measurable s) :
      Measurable (fun z : SelectedCoord X =>
        cellMass (p z.1) (q z.1) (s z.1) z.2.1 z.2.2) := by
    unfold cellMass bitMass
    apply Measurable.mul
    · apply Measurable.ite
      · measurability
      · exact hp.comp (by fun_prop)
      · exact measurable_const.sub (hp.comp (by fun_prop))
    · apply Measurable.ite
      · measurability
      · apply Measurable.ite
        · measurability
        · exact hs.comp (by fun_prop)
        · exact hq.comp (by fun_prop)
      · exact measurable_const.sub (by
          apply Measurable.ite
          · measurability
          · exact hs.comp (by fun_prop)
          · exact hq.comp (by fun_prop))
  unfold selectedCellRatio
  exact ENNReal.measurable_ofReal.comp
    ((hc e q₀ q₁ he hq₀ hq₁).div (hc e q₀' q₁' he hq₀' hq₁'))

/-- [The logarithm of the positive cellwise density ratio is integrable](goal)
under [the first selected law](hyp:μ,e,q₀,q₁) when [all five parameter
functions are measurable](hyp:he,hq₀,hq₁,hq₀',hq₁') and
[uniformly interior](hyp:hη0,hηhalf,heη,hq₀η,hq₁η,hq₀'η,hq₁'η).

For every selected cell, its mass under either law lies in `[η²,1]`.
Consequently the real density ratio stays in `[η²,η⁻²]`; its logarithm is
bounded. Use finiteness of `selectedLaw` from `selectedLaw_probability`.
-/
theorem selectedCellRatio_log_integrable {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ q₀' q₁' : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁')
    {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1 / 2)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hq₁η : ∀ x, q₁ x ∈ Set.Icc η (1 - η))
    (hq₀'η : ∀ x, q₀' x ∈ Set.Icc η (1 - η))
    (hq₁'η : ∀ x, q₁' x ∈ Set.Icc η (1 - η)) :
    Integrable (fun z => Real.log (selectedCellRatio e q₀ q₁ q₀' q₁' z).toReal)
      (selectedLaw μ e q₀ q₁) := by
  have he01 (x : X) : e x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases heη x with ⟨hl, hu⟩
    constructor <;> linarith
  have hq₀01 (x : X) : q₀ x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hq₀η x with ⟨hl, hu⟩
    constructor <;> linarith
  have hq₁01 (x : X) : q₁ x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hq₁η x with ⟨hl, hu⟩
    constructor <;> linarith
  letI : IsProbabilityMeasure (selectedLaw μ e q₀ q₁) :=
    selectedLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
  have hmeas : Measurable
      (fun z => Real.log (selectedCellRatio e q₀ q₁ q₀' q₁' z).toReal) :=
    Real.measurable_log.comp
      (ENNReal.measurable_toReal.comp
        (measurable_selectedCellRatio he hq₀ hq₁ hq₀' hq₁'))
  apply Integrable.of_mem_Icc (Real.log (η ^ 2)) (-Real.log (η ^ 2))
    hmeas.aemeasurable
  filter_upwards [] with z
  obtain ⟨x, ⟨a, y⟩⟩ := z
  have hA := cellMass_mem_Icc hη0 (heη x) (hq₀η x) (hq₁η x) a y
  have hB := cellMass_mem_Icc hη0 (heη x) (hq₀'η x) (hq₁'η x) a y
  have hη2 : 0 < η ^ 2 := pow_pos hη0 _
  have hApos : 0 < cellMass (e x) (q₀ x) (q₁ x) a y := lt_of_lt_of_le hη2 hA.1
  have hBpos : 0 < cellMass (e x) (q₀' x) (q₁' x) a y := lt_of_lt_of_le hη2 hB.1
  have hlogA₁ := Real.log_le_log hη2 hA.1
  have hlogA₂ := Real.log_le_log hApos hA.2
  have hlogB₁ := Real.log_le_log hη2 hB.1
  have hlogB₂ := Real.log_le_log hBpos hB.2
  change Real.log (ENNReal.ofReal
    (cellMass (e x) (q₀ x) (q₁ x) a y /
      cellMass (e x) (q₀' x) (q₁' x) a y)).toReal ∈
    Set.Icc (Real.log (η ^ 2)) (-Real.log (η ^ 2))
  rw [ENNReal.toReal_ofReal (le_of_lt (div_pos hApos hBpos)),
    Real.log_div (ne_of_gt hApos) (ne_of_gt hBpos)]
  simp only [Set.mem_Icc, Real.log_one] at *
  constructor <;> linarith

/-- [The selected-law log likelihood equals the logarithm of the cellwise
ratio almost everywhere under the first law](goal) for a [probability base](hyp:μ),
[measurable parameters](hyp:he,hq₀,hq₁,hq₀',hq₁'), and
[uniform interior bounds](hyp:hη0,hηhalf,heη,hq₀η,hq₁η,hq₀'η,hq₁'η).

Use `selectedLaw_eq_withDensity`, `rnDeriv_withDensity`, and absolute
continuity to transfer the almost-everywhere identity to the first law.
-/
theorem selectedLaw_llr_ae_eq_cell_log {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ q₀' q₁' : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁')
    {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1 / 2)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hq₁η : ∀ x, q₁ x ∈ Set.Icc η (1 - η))
    (hq₀'η : ∀ x, q₀' x ∈ Set.Icc η (1 - η))
    (hq₁'η : ∀ x, q₁' x ∈ Set.Icc η (1 - η)) :
    llr (selectedLaw μ e q₀ q₁) (selectedLaw μ e q₀' q₁') =ᵐ[selectedLaw μ e q₀ q₁]
      fun z => Real.log (selectedCellRatio e q₀ q₁ q₀' q₁' z).toReal := by
  have he01 (x : X) : e x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases heη x with ⟨hl, hu⟩
    constructor <;> linarith
  have hq₀'01 (x : X) : q₀' x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hq₀'η x with ⟨hl, hu⟩
    constructor <;> linarith
  have hq₁'01 (x : X) : q₁' x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hq₁'η x with ⟨hl, hu⟩
    constructor <;> linarith
  letI : IsProbabilityMeasure (selectedLaw μ e q₀' q₁') :=
    selectedLaw_probability μ e q₀' q₁' he hq₀' hq₁' he01 hq₀'01 hq₁'01
  have hderiv :
      (selectedLaw μ e q₀ q₁).rnDeriv (selectedLaw μ e q₀' q₁')
        =ᵐ[selectedLaw μ e q₀' q₁'] selectedCellRatio e q₀ q₁ q₀' q₁' := by
    conv_lhs => rw [selectedLaw_eq_withDensity μ e q₀ q₁ q₀' q₁'
      he hq₀ hq₁ hq₀' hq₁' hη0 hηhalf heη hq₀η hq₁η hq₀'η hq₁'η]
    exact Measure.rnDeriv_withDensity _
      (measurable_selectedCellRatio he hq₀ hq₁ hq₀' hq₁')
  have hac := selectedLaw_ac μ e q₀ q₁ q₀' q₁' he hq₀ hq₁ hq₀' hq₁'
    hη0 hηhalf heη hq₀η hq₁η hq₀'η hq₁'η
  filter_upwards [hac.ae_le hderiv] with z hz
  exact congrArg (fun (t : ENNReal) => Real.log t.toReal) hz

/-- [The selected-law log likelihood ratio is integrable under the first
selected law](goal) for a [probability base](hyp:μ),
[measurable parameters](hyp:he,hq₀,hq₁,hq₀',hq₁'), and
[uniform interior bounds](hyp:hη0,hηhalf,heη,hq₀η,hq₁η,hq₀'η,hq₁'η).

Apply `selectedCellRatio_log_integrable` and
`selectedLaw_llr_ae_eq_cell_log`.
-/
theorem selectedLaw_llr_integrable {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ q₀' q₁' : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁')
    {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1 / 2)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hq₁η : ∀ x, q₁ x ∈ Set.Icc η (1 - η))
    (hq₀'η : ∀ x, q₀' x ∈ Set.Icc η (1 - η))
    (hq₁'η : ∀ x, q₁' x ∈ Set.Icc η (1 - η)) :
    Integrable (llr (selectedLaw μ e q₀ q₁) (selectedLaw μ e q₀' q₁'))
      (selectedLaw μ e q₀ q₁) := by
  exact (selectedCellRatio_log_integrable μ e q₀ q₁ q₀' q₁'
    he hq₀ hq₁ hq₀' hq₁' hη0 hηhalf heη hq₀η hq₁η hq₀'η hq₁'η).congr
      (selectedLaw_llr_ae_eq_cell_log μ e q₀ q₁ q₀' q₁'
        he hq₀ hq₁ hq₀' hq₁' hη0 hηhalf heη hq₀η hq₁η hq₀'η hq₁'η).symm

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL
