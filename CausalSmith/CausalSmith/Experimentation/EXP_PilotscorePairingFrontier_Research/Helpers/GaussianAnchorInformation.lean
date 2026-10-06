module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.GaussianAnchorLaw
public import Causalean.Mathlib.InformationTheory.GaussianKL

/-!
# Information bounds for Gaussian anchor laws

This module computes the exact common-variance divergence of Gaussian anchor
fibers and laws, then transports the bound through randomized pilot observation
and finite iid pilot samples.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ}

private lemma gaussianAnchorFiber_fibre (g : XSpace d → ℝ) (v : NNReal)
    (x : XSpace d) :
    gaussianAnchorFiber g v x {u | u.1 = x}ᶜ = 0 := by
  have hmap := congrArg (fun μ : Measure (XSpace d) => μ ({x}ᶜ))
    (gaussianAnchorFiber_map_fst g v x)
  rw [Measure.map_apply measurable_fst (MeasurableSet.singleton x).compl,
    Measure.dirac_apply' _ (MeasurableSet.singleton x).compl] at hmap
  have hset : Prod.fst ⁻¹' ({x}ᶜ : Set (XSpace d)) =
      {u : UnitRecord d | u.1 = x}ᶜ := by
    ext u
    simp
  rw [hset] at hmap
  simpa using hmap

private lemma gaussianAnchorFiber_ac (g g' : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (x : XSpace d) :
    gaussianAnchorFiber g v x ≪ gaussianAnchorFiber g' v x := by
  unfold gaussianAnchorFiber
  exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
    ((Causalean.Mathlib.InformationTheory.gaussianReal_ac_gaussianReal
      (g x) (g' x) hv hv).prod
      (Causalean.Mathlib.InformationTheory.gaussianReal_ac_gaussianReal
        (g x) (g' x) hv hv))

/-- For [two common conditional means](hyp:g,g'), [a common nonzero
variance](hyp:v,hv), and [a recorded covariate](hyp:x), [the exact divergence
between the corresponding two-outcome Gaussian fibers is the squared mean gap
divided by the variance](goal). -/
lemma gaussianAnchorFiber_klDiv_eq (g g' : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (x : XSpace d) :
    InformationTheory.klDiv (gaussianAnchorFiber g v x)
        (gaussianAnchorFiber g' v x) =
      ENNReal.ofReal ((g x - g' x) ^ 2 / (v : ℝ)) := by
  let μ := gaussianReal (g x) v
  let ν := gaussianReal (g' x) v
  let πμ := μ.prod μ
  let πν := ν.prod ν
  have hac : μ ≪ ν :=
    Causalean.Mathlib.InformationTheory.gaussianReal_ac_gaussianReal
      (g x) (g' x) hv hv
  have hint : Integrable (llr μ ν) μ :=
    Causalean.Mathlib.InformationTheory.integrable_llr_gaussianReal
      (g x) (g' x) hv
  have hsingle : InformationTheory.klDiv μ ν =
      ENNReal.ofReal ((g x - g' x) ^ 2 / (2 * (v : ℝ))) :=
    Causalean.Mathlib.InformationTheory.gaussianReal_klDiv_eq_of_ne_zero
      (g x) (g' x) v hv
  have hπac : πμ ≪ πν := hac.prod hac
  have hπint : Integrable (llr πμ πν) πμ :=
    Causalean.Mathlib.InformationTheory.ProductKL.llr_prod_integrable
      μ ν μ ν hac hac hint hint
  have hπfin : InformationTheory.klDiv πμ πν ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hπac hπint
  have hπreal : (InformationTheory.klDiv πμ πν).toReal =
      2 * ((g x - g' x) ^ 2 / (2 * (v : ℝ))) := by
    rw [Causalean.Mathlib.InformationTheory.ProductKL.klDiv_prod_toReal_add
      μ ν μ ν hac hac hint hint, hsingle]
    rw [ENNReal.toReal_ofReal]
    · ring
    · positivity
  have hπ : InformationTheory.klDiv πμ πν =
      ENNReal.ofReal ((g x - g' x) ^ 2 / (v : ℝ)) := by
    rw [← ENNReal.ofReal_toReal hπfin, hπreal]
    congr 1
    have hvpos : 0 < (v : ℝ) := by exact_mod_cast (zero_lt_iff.mpr hv)
    field_simp
  have hdiracInt : Integrable
      (llr (Measure.dirac x) (Measure.dirac x)) (Measure.dirac x) := by
    rw [integrable_congr (llr_self (Measure.dirac x))]
    exact integrable_zero _ _ _
  have houterFin : InformationTheory.klDiv
      ((Measure.dirac x).prod πμ) ((Measure.dirac x).prod πν) ≠ ⊤ := by
    exact InformationTheory.klDiv_ne_top
      (Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl hπac)
      (Causalean.Mathlib.InformationTheory.ProductKL.llr_prod_integrable
        (Measure.dirac x) (Measure.dirac x) πμ πν
        Measure.AbsolutelyContinuous.rfl hπac hdiracInt hπint)
  unfold gaussianAnchorFiber
  rw [← ENNReal.ofReal_toReal houterFin]
  rw [Causalean.Mathlib.InformationTheory.ProductKL.klDiv_prod_toReal_add
    (Measure.dirac x) (Measure.dirac x) πμ πν
    Measure.AbsolutelyContinuous.rfl hπac hdiracInt hπint]
  rw [InformationTheory.klDiv_self, hπ]
  simp only [ENNReal.toReal_zero, zero_add]
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- For [two measurable common conditional means](hyp:g,g',hg,hg') and [a
common nonzero variance](hyp:v,hv), [the divergence between their Gaussian
anchor laws is the cube average of the exact fiber divergence](goal). -/
lemma gaussianAnchorLaw_klDiv_eq_lintegral (g g' : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (hg : Measurable g) (hg' : Measurable g') :
    InformationTheory.klDiv (gaussianAnchorLaw g v) (gaussianAnchorLaw g' v) =
      ∫⁻ x, ENNReal.ofReal ((g x - g' x) ^ 2 / (v : ℝ)) ∂cubeMeasure d := by
  let κ : Kernel (XSpace d) (UnitRecord d) :=
    Kernel.mk (gaussianAnchorFiber g v) (measurable_gaussianAnchorFiber g v hg)
  let η : Kernel (XSpace d) (UnitRecord d) :=
    Kernel.mk (gaussianAnchorFiber g' v) (measurable_gaussianAnchorFiber g' v hg')
  letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
  letI : IsMarkovKernel κ := by
    refine ⟨?_⟩
    exact gaussianAnchorFiber_isProbabilityMeasure g v
  letI : IsMarkovKernel η := by
    refine ⟨?_⟩
    exact gaussianAnchorFiber_isProbabilityMeasure g' v
  have hchain : InformationTheory.klDiv
      ((cubeMeasure d).bind κ) ((cubeMeasure d).bind η) =
      ∫⁻ x, InformationTheory.klDiv (κ x) (η x) ∂cubeMeasure d := by
    apply Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
      (m := cubeMeasure d) (κ := κ) (η := η)
      (proj := Prod.fst) (hproj := measurable_fst)
    · exact measurableSet_eq_fun measurable_fst (measurable_fst.comp measurable_snd)
    · exact Filter.Eventually.of_forall (gaussianAnchorFiber_fibre g v)
    · exact Filter.Eventually.of_forall (gaussianAnchorFiber_fibre g' v)
    · exact Filter.Eventually.of_forall (gaussianAnchorFiber_ac g g' v hv)
  change InformationTheory.klDiv ((cubeMeasure d).bind κ)
    ((cubeMeasure d).bind η) = _
  rw [hchain]
  apply lintegral_congr
  intro x
  exact gaussianAnchorFiber_klDiv_eq g g' v hv x

/-- For [two measurable common conditional means](hyp:g,g',hg,hg'), [a
common nonzero variance](hyp:v,hv), and [integrability of their squared
gap](hyp:hsq), [the exact Gaussian anchor-law divergence is the cube-integrated
squared gap divided by the common variance](goal). -/
lemma gaussianAnchorLaw_klDiv_eq (g g' : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (hg : Measurable g) (hg' : Measurable g')
    (hsq : Integrable (fun x => (g x - g' x) ^ 2) (cubeMeasure d)) :
    InformationTheory.klDiv (gaussianAnchorLaw g v) (gaussianAnchorLaw g' v) =
      ENNReal.ofReal ((∫ x, (g x - g' x) ^ 2 ∂cubeMeasure d) / (v : ℝ)) := by
  rw [gaussianAnchorLaw_klDiv_eq_lintegral g g' v hv hg hg']
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (zero_lt_iff.mpr hv)
  have hint : Integrable (fun x => (g x - g' x) ^ 2 / (v : ℝ))
      (cubeMeasure d) := hsq.div_const (v : ℝ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => div_nonneg (sq_nonneg _) hvpos.le)]
  congr 1
  rw [integral_div]

/-- For [two measurable common conditional means](hyp:g,g',hg,hg'), [a
common nonzero variance](hyp:v,hv), [an integrable squared gap](hyp:hsq), and
[an upper bound on its cube integral](hyp:B,hB,hgap), [their Gaussian anchor-law
divergence is at most that bound divided by the variance](goal). -/
lemma gaussianAnchorLaw_klDiv_le_of_integral (g g' : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (hg : Measurable g) (hg' : Measurable g')
    (hsq : Integrable (fun x => (g x - g' x) ^ 2) (cubeMeasure d))
    (B : ℝ) (hB : 0 ≤ B)
    (hgap : (∫ x, (g x - g' x) ^ 2 ∂cubeMeasure d) ≤ B) :
    InformationTheory.klDiv (gaussianAnchorLaw g v) (gaussianAnchorLaw g' v) ≤
      ENNReal.ofReal (B / (v : ℝ)) := by
  rw [gaussianAnchorLaw_klDiv_eq g g' v hv hg hg' hsq]
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right hgap (by positivity)

private lemma gaussianInformation_fairCoin_probability :
    IsProbabilityMeasure fairCoin := by
  constructor
  simpa [fairCoin] using ENNReal.inv_two_add_inv_two

private lemma gaussianInformation_observedPilot_measurable :
    Measurable (fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2) := by
  unfold observedPilot
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.prodMk
  · fun_prop
  apply Measurable.ite
  · exact measurable_snd (measurableSet_singleton true)
  · fun_prop
  · fun_prop

private lemma gaussianInformation_pilotUnitLaw_probability
    (P : Measure (UnitRecord d)) (hP : IsProbabilityMeasure P) :
    IsProbabilityMeasure (pilotUnitLaw P) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure fairCoin := gaussianInformation_fairCoin_probability
  unfold pilotUnitLaw
  exact Measure.isProbabilityMeasure_map
    gaussianInformation_observedPilot_measurable.aemeasurable

/-- For [two probability unit laws](hyp:P,Q,hP,hQ), [a finite one-unit KL
budget](hyp:B,hB,hunit), and [a pilot sample size](hyp:m), [randomized pilot
observation followed by an iid finite product has KL at most `m` times that
budget](goal). -/
lemma pilotProduct_klDiv_le_of_unit (m : ℕ)
    (P Q : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P) (hQ : IsProbabilityMeasure Q)
    (B : ℝ) (hB : 0 ≤ B)
    (hunit : InformationTheory.klDiv P Q ≤ ENNReal.ofReal B) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw P)
      (Measure.pi fun _ : Fin m => pilotUnitLaw Q) ≤
        ENNReal.ofReal ((m : ℝ) * B) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    gaussianInformation_pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure (pilotUnitLaw Q) :=
    gaussianInformation_pilotUnitLaw_probability Q hQ
  have hone : InformationTheory.klDiv (pilotUnitLaw P) (pilotUnitLaw Q) ≤
      ENNReal.ofReal B := (pilotUnitLaw_klDiv_le P Q hP hQ).trans hunit
  have honeFin : InformationTheory.klDiv (pilotUnitLaw P) (pilotUnitLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hone
  obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp honeFin
  have ht := Causalean.Mathlib.InformationTheory.productKL_tensorization
    m (pilotUnitLaw P) (pilotUnitLaw Q) hac hint
  rw [← ENNReal.ofReal_toReal ht.1]
  apply ENNReal.ofReal_le_ofReal
  calc
    (InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw P)
      (Measure.pi fun _ : Fin m => pilotUnitLaw Q)).toReal
        ≤ (m : ℝ) * (InformationTheory.klDiv
          (pilotUnitLaw P) (pilotUnitLaw Q)).toReal := ht.2.2
    _ ≤ (m : ℝ) * B := by
      gcongr
      exact ENNReal.toReal_le_of_le_ofReal hB hone

/-- For [two measurable Gaussian anchor means](hyp:g,g',hg,hg'), [a common
nonzero variance](hyp:v,hv), [an integrable squared gap](hyp:hsq), and [a cube
integral bound](hyp:B,hB,hgap), [the iid randomized-pilot laws have KL at most
the sample size times the gap bound divided by the common variance](goal). -/
lemma gaussianAnchorPilotProduct_klDiv_le_of_integral
    (m : ℕ) (g g' : XSpace d → ℝ) (v : NNReal)
    (hv : v ≠ 0) (hg : Measurable g) (hg' : Measurable g')
    (hsq : Integrable (fun x => (g x - g' x) ^ 2) (cubeMeasure d))
    (B : ℝ) (hB : 0 ≤ B)
    (hgap : (∫ x, (g x - g' x) ^ 2 ∂cubeMeasure d) ≤ B) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw (gaussianAnchorLaw g v))
      (Measure.pi fun _ : Fin m => pilotUnitLaw (gaussianAnchorLaw g' v)) ≤
        ENNReal.ofReal ((m : ℝ) * B / (v : ℝ)) := by
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast (zero_lt_iff.mpr hv)
  have hunit := gaussianAnchorLaw_klDiv_le_of_integral
    g g' v hv hg hg' hsq B hB hgap
  have hlift := pilotProduct_klDiv_le_of_unit m
    (gaussianAnchorLaw g v) (gaussianAnchorLaw g' v)
    (gaussianAnchorLaw_isProbabilityMeasure g v hg)
    (gaussianAnchorLaw_isProbabilityMeasure g' v hg')
    (B / (v : ℝ)) (div_nonneg hB hvpos.le) hunit
  convert hlift using 1
  congr 1
  ring

end CausalSmith.Experimentation.PilotscorePairingFrontier
