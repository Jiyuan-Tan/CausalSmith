module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL.Likelihood
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Cellwise integration for selected Bernoulli laws

The log density ratio of two selected laws can be integrated by first summing
over the four treatment and outcome cells at each covariate value.
-/

public section

open MeasureTheory

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- [The expected cellwise log likelihood ratio is the covariate integral of
the four cell contributions](goal) for a [probability covariate law](hyp:μ),
[measurable propensity and outcome means](hyp:he,hq₀,hq₁,hq₀',hq₁'), and
[uniform interior bounds](hyp:hη0,heη,hq₀η,hq₁η,hq₀'η,hq₁'η).

Use the explicit `selectedLaw` density and coordinate swap. Apply
`integral_map`, `integral_withDensity_eq_integral_toReal_smul₀`, Fubini for the product with
the finite counting measure, and `integral_count`; positivity identifies
`selectedCellRatio` with the real quotient in every cell.
-/
theorem selectedLaw_integral_cell_log_eq_sum {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ q₀' q₁' : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁')
    {η : ℝ} (hη0 : 0 < η)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hq₁η : ∀ x, q₁ x ∈ Set.Icc η (1 - η))
    (hq₀'η : ∀ x, q₀' x ∈ Set.Icc η (1 - η))
    (hq₁'η : ∀ x, q₁' x ∈ Set.Icc η (1 - η)) :
    (∫ z, Real.log (selectedCellRatio e q₀ q₁ q₀' q₁' z).toReal
      ∂selectedLaw μ e q₀ q₁) =
      ∫ x, ∑ a : Bool, ∑ y : Bool,
        cellMass (e x) (q₀ x) (q₁ x) a y *
          Real.log (cellMass (e x) (q₀ x) (q₁ x) a y /
            cellMass (e x) (q₀' x) (q₁' x) a y) ∂μ := by
  let ν : Measure ((Bool × Bool) × X) :=
    ((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)).prod μ
  let f : ((Bool × Bool) × X) → SelectedCoord X := fun z => (z.2, z.1)
  let g : SelectedCoord X → ℝ :=
    fun z => Real.log (selectedCellRatio e q₀ q₁ q₀' q₁' z).toReal
  have hf : Measurable f := by fun_prop
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
  have hg : Measurable g := by
    unfold g selectedCellRatio
    exact Real.measurable_log.comp
      (ENNReal.measurable_toReal.comp
        (ENNReal.measurable_ofReal.comp
          ((hc e q₀ q₁ he hq₀ hq₁).div (hc e q₀' q₁' he hq₀' hq₁'))))
  have hd : Measurable (selectedDensity e q₀ q₁) := by
    change Measurable (fun z : (Bool × Bool) × X =>
      ENNReal.ofReal (cellMass (e z.2) (q₀ z.2) (q₁ z.2) z.1.1 z.1.2))
    simpa [f, Function.comp_def] using
      (ENNReal.measurable_ofReal.comp (hc e q₀ q₁ he hq₀ hq₁)).comp hf
  have htop : ∀ᵐ z ∂ν, selectedDensity e q₀ q₁ z < ⊤ := by
    filter_upwards [] with z
    simp [selectedDensity]
  have hgi : Integrable g (selectedLaw μ e q₀ q₁) :=
    selectedCellRatio_log_integrable μ e q₀ q₁ q₀' q₁'
      he hq₀ hq₁ hq₀' hq₁' hη0 heη hq₀η hq₁η hq₀'η hq₁'η
  have hwi : Integrable (g ∘ f) (ν.withDensity (selectedDensity e q₀ q₁)) := by
    exact (integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable).1 hgi
  have hprod : Integrable
      (fun z : (Bool × Bool) × X =>
        (selectedDensity e q₀ q₁ z).toReal * g (f z)) ν := by
    simpa [smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable htop).1 hwi
  have hpos (p : ℝ) (hp : p ∈ Set.Icc η (1 - η)) (b : Bool) :
      0 < bitMass p b := by
    cases b with
    | false => change 0 < 1 - p; linarith [hp.2]
    | true => change 0 < p; exact lt_of_lt_of_le hη0 hp.1
  have hcellpos (x : X) (a y : Bool) :
      0 < cellMass (e x) (q₀ x) (q₁ x) a y ∧
        0 < cellMass (e x) (q₀' x) (q₁' x) a y := by
    unfold cellMass
    constructor
    · exact mul_pos (hpos (e x) (heη x) a)
        (by cases a with
          | false => exact hpos (q₀ x) (hq₀η x) y
          | true => exact hpos (q₁ x) (hq₁η x) y)
    · exact mul_pos (hpos (e x) (heη x) a)
        (by cases a with
          | false => exact hpos (q₀' x) (hq₀'η x) y
          | true => exact hpos (q₁' x) (hq₁'η x) y)
  have hpoint (z : (Bool × Bool) × X) :
      (selectedDensity e q₀ q₁ z).toReal * g (f z) =
        cellMass (e z.2) (q₀ z.2) (q₁ z.2) z.1.1 z.1.2 *
          Real.log (cellMass (e z.2) (q₀ z.2) (q₁ z.2) z.1.1 z.1.2 /
            cellMass (e z.2) (q₀' z.2) (q₁' z.2) z.1.1 z.1.2) := by
    obtain ⟨⟨a, y⟩, x⟩ := z
    dsimp [selectedDensity, g, f, selectedCellRatio]
    rw [ENNReal.toReal_ofReal (hcellpos x a y).1.le,
      ENNReal.toReal_ofReal (div_pos (hcellpos x a y).1 (hcellpos x a y).2).le]
  change ∫ z, g z ∂(ν.withDensity (selectedDensity e q₀ q₁)).map f = _
  rw [integral_map hf.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hd.aemeasurable htop]
  simp only [smul_eq_mul]
  rw [integral_prod_symm _ hprod]
  congr 1
  funext x
  rw [integral_fintype (hf := Integrable.of_finite)]
  simp_rw [hpoint]
  have hm (a y : Bool) :
      (Measure.count.prod (Measure.count : Measure Bool) : Measure (Bool × Bool))
        {(a, y)} = 1 := by
    rw [show ({(a, y)} : Set (Bool × Bool)) = ({a} : Set Bool) ×ˢ {y} by ext ⟨b, c⟩; simp]
    rw [Measure.prod_prod]
    simp
  simp [measureReal_def, hm, Fintype.sum_prod_type]

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL
