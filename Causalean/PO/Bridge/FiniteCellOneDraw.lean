module
public import Causalean.PO.Bridge.FiniteCellGFormula

/-!
# One-draw moments of a finite-cell observed table

The cell identities defining `FiniteCellData` yield population moments for treatment
indicators and observed arm outcomes. Covariate-measurable integrable weights retain
the same identities. These are the one-coordinate inputs to pair-kernel transport.
-/

public section

open MeasureTheory
open ProbabilityTheory
open Causalean.PO.Bridge

namespace Causalean.PO.Bridge

variable {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (D : FiniteCellData Ω γ μ)

private theorem integral_weighted_condExp (w k : γ → ℝ) (f : Ω → ℝ)
    (hwmeas : Measurable w) (hkmeas : Measurable k)
    (hw : Integrable w (μ.map D.X)) (hf : Integrable f μ)
    (hfb : ∀ ω, ‖f ω‖ ≤ 1)
    (hce : μ[f | D.sigmaX] =ᵐ[μ] fun ω => k (D.X ω)) :
    ∫ ω, w (D.X ω) * f ω ∂μ =
      ∫ x, w x * k x ∂(μ.map D.X) := by
  have hweight : Integrable (fun ω => w (D.X ω)) μ :=
    (integrable_map_measure hwmeas.aestronglyMeasurable
      D.measurable_X.aemeasurable).1 hw
  have hproduct : Integrable (fun ω => f ω * w (D.X ω)) μ :=
    hweight.bdd_mul hf.aestronglyMeasurable (ae_of_all _ hfb)
  have hweightSigma : AEStronglyMeasurable[D.sigmaX]
      (fun ω => w (D.X ω)) μ :=
    (hwmeas.comp (comap_measurable D.X)).aestronglyMeasurable
  have hpull := condExp_mul_of_aestronglyMeasurable_right
    hweightSigma hproduct hf
  calc
    ∫ ω, w (D.X ω) * f ω ∂μ = ∫ ω, f ω * w (D.X ω) ∂μ := by
      congr 1; funext ω; ring
    _ = ∫ ω, μ[(fun ω => f ω * w (D.X ω)) | D.sigmaX] ω ∂μ :=
      (integral_condExp D.sigmaX_le).symm
    _ = ∫ ω, μ[f | D.sigmaX] ω * w (D.X ω) ∂μ := integral_congr_ae hpull
    _ = ∫ ω, w (D.X ω) * k (D.X ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hce] with ω hω
      rw [hω, mul_comm]
    _ = ∫ x, w x * k x ∂(μ.map D.X) :=
      (integral_map D.measurable_X.aemeasurable
        (hwmeas.mul hkmeas).aestronglyMeasurable).symm

/-- A [finite-cell observed table](hyp:D), [treatment arm](hyp:d), [covariate
weight](hyp:w), [measurability of that weight](hyp:hm), and [its integrability
under the covariate law](hyp:hw) give [the weighted treatment-arm indicator
mean through the finite-cell arm probability](goal). -/
theorem integral_weighted_arm (d : Bool) (w : γ → ℝ) (hm : Measurable w)
    (hw : Integrable w (μ.map D.X)) :
    ∫ ω, w (D.X ω) * armIndicator d (D.A ω) ∂μ =
      ∫ x, w x * D.armProb d x ∂(μ.map D.X) := by
  apply integral_weighted_condExp D w (D.armProb d)
    (fun ω => armIndicator d (D.A ω)) hm (D.measurable_armProb d) hw
    (D.integrable_armIndicator d) ?_ (D.condExp_arm d)
  intro ω
  simp only [armIndicator]
  split_ifs <;> simp

/-- A [finite-cell observed table](hyp:D), [treatment arm](hyp:d), [covariate
weight](hyp:w), [measurability of that weight](hyp:hm), and [its integrability
under the covariate law](hyp:hw) give [the weighted observed arm-outcome mean
through the finite-cell arm regression](goal). -/
theorem integral_weighted_observedProduct (d : Bool) (w : γ → ℝ)
    (hm : Measurable w) (hw : Integrable w (μ.map D.X)) :
    ∫ ω, w (D.X ω) * armIndicator d (D.A ω) *
        boolReal (observedY D.A D.Y0 D.Y1 ω) ∂μ =
      ∫ x, w x * D.armProb d x * D.mean d x ∂(μ.map D.X) := by
  have h := integral_weighted_condExp D w
    (fun x => D.armProb d x * D.mean d x)
    (fun ω => armIndicator d (D.A ω) *
      boolReal (observedY D.A D.Y0 D.Y1 ω)) hm
    ((D.measurable_armProb d).mul (D.measurable_mean d)) hw
    (D.integrable_observedProduct d) (by
      intro ω
      simp only [armIndicator, boolReal]
      split_ifs <;> simp) (D.condExp_observedProduct d)
  simpa only [mul_assoc] using h

variable [StandardBorelSpace Ω]

/-- A [finite-cell observed table](hyp:D), [selected treatment arm](hyp:d),
[covariate weight](hyp:w), [measurability of that weight](hyp:hm), [its
integrability under the covariate law](hyp:hw), [conditional independence of
treatment and the selected potential outcome given covariates](hyp:hCI), and
[almost-surely positive probability of that arm](hyp:hpos) give [the weighted
potential-outcome mean through the observed arm regression](goal). -/
theorem integral_weighted_potential (d : Bool) (w : γ → ℝ)
    (hm : Measurable w) (hw : Integrable w (μ.map D.X))
    (hCI : CondIndepFun D.sigmaX D.sigmaX_le D.A (D.potential d) μ)
    (hpos : ∀ᵐ ω ∂μ, D.armProb d (D.X ω) ≠ 0) :
    ∫ ω, w (D.X ω) * boolReal (D.potential d ω) ∂μ =
      ∫ x, w x * D.mean d x ∂(μ.map D.X) := by
  apply integral_weighted_condExp D w (D.mean d)
    (fun ω => boolReal (D.potential d ω)) hm (D.measurable_mean d) hw
    (by
      convert D.integrable_potential d using 1
      funext ω
      cases d <;> rfl)
    ?_ (D.condExp_potential d hCI hpos)
  intro ω
  simp only [boolReal]
  split_ifs <;> simp

/-- A [finite-cell observed table](hyp:D), [covariate weight](hyp:w),
[measurability of that weight](hyp:hm), [its integrability under the covariate
law](hyp:hw), [armwise conditional independence](hyp:hCI), and [almost-surely
positive probabilities for both arms](hyp:hpos) give [the weighted
treated-minus-control potential contrast through the two arm regressions](goal). -/
theorem integral_weighted_treated_sub_control (w : γ → ℝ)
    (hm : Measurable w) (hw : Integrable w (μ.map D.X))
    (hCI : ∀ d, CondIndepFun D.sigmaX D.sigmaX_le D.A (D.potential d) μ)
    (hpos : ∀ d, ∀ᵐ ω ∂μ, D.armProb d (D.X ω) ≠ 0) :
    ∫ ω, w (D.X ω) * (boolReal (D.Y1 ω) - boolReal (D.Y0 ω)) ∂μ =
      ∫ x, w x * (D.mean true x - D.mean false x) ∂(μ.map D.X) := by
  have h1 : Integrable (fun ω => boolReal (D.Y1 ω)) μ := by
    simpa [FiniteCellData.potential] using D.integrable_potential true
  have h0 : Integrable (fun ω => boolReal (D.Y0 ω)) μ := by
    simpa [FiniteCellData.potential] using D.integrable_potential false
  apply integral_weighted_condExp D w
    (fun x => D.mean true x - D.mean false x)
    (fun ω => boolReal (D.Y1 ω) - boolReal (D.Y0 ω)) hm
    ((D.measurable_mean true).sub (D.measurable_mean false)) hw
    (h1.sub h0) ?_ (D.condExp_treated_sub_control hCI hpos)
  intro ω
  cases D.Y1 ω <;> cases D.Y0 ω <;> simp [boolReal]

omit [StandardBorelSpace Ω] in
/-- A [finite-cell observed table](hyp:D) under the ambient probability law
induces [a probability law on observed covariate, treatment, and outcome
triplets](goal). -/
theorem observedLaw_isProbability : IsProbabilityMeasure D.observedLaw := by
  rw [D.observedLaw_eq_map]
  apply Measure.isProbabilityMeasure_map
  have hY : Measurable (observedY D.A D.Y0 D.Y1) := by
    exact Measurable.ite
      (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  exact (D.measurable_X.prodMk (D.measurable_A.prodMk hY)).aemeasurable

omit [StandardBorelSpace Ω] in
/-- A [finite-cell observed table](hyp:D), [treatment arm](hyp:d), [covariate
weight](hyp:w), [measurability of that weight](hyp:hm), and [its integrability
under the covariate law](hyp:hw) give [the observed-law treatment indicator
mean through the arm probability](goal). -/
theorem integral_observedLaw_weighted_arm (d : Bool) (w : γ → ℝ)
    (hm : Measurable w) (hw : Integrable w (μ.map D.X)) :
    ∫ z : γ × Bool × Bool, w z.1 * armIndicator d z.2.1 ∂D.observedLaw =
      ∫ x, w x * D.armProb d x ∂(μ.map D.X) := by
  have hY : Measurable (observedY D.A D.Y0 D.Y1) := by
    exact Measurable.ite
      (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  have hmap : Measurable
      (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
    D.measurable_X.prodMk (D.measurable_A.prodMk hY)
  have hArm : Measurable
      (fun z : γ × Bool × Bool => armIndicator d z.2.1) := by
    unfold armIndicator
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hintegrand : Measurable
      (fun z : γ × Bool × Bool => w z.1 * armIndicator d z.2.1) :=
    (hm.comp measurable_fst).mul hArm
  rw [D.observedLaw_eq_map,
    integral_map hmap.aemeasurable hintegrand.aestronglyMeasurable]
  exact integral_weighted_arm D d w hm hw

omit [StandardBorelSpace Ω] in
/-- A [finite-cell observed table](hyp:D), [treatment arm](hyp:d), [covariate
weight](hyp:w), [measurability of that weight](hyp:hm), and [its integrability
under the covariate law](hyp:hw) give [the observed-law weighted arm-outcome
mean through the arm probability and regression](goal). -/
theorem integral_observedLaw_weighted_observedProduct (d : Bool) (w : γ → ℝ)
    (hm : Measurable w) (hw : Integrable w (μ.map D.X)) :
    ∫ z : γ × Bool × Bool,
        w z.1 * armIndicator d z.2.1 * boolReal z.2.2 ∂D.observedLaw =
      ∫ x, w x * D.armProb d x * D.mean d x ∂(μ.map D.X) := by
  have hY : Measurable (observedY D.A D.Y0 D.Y1) := by
    exact Measurable.ite
      (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  have hmap : Measurable
      (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
    D.measurable_X.prodMk (D.measurable_A.prodMk hY)
  have hArm : Measurable
      (fun z : γ × Bool × Bool => armIndicator d z.2.1) := by
    unfold armIndicator
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hBool : Measurable
      (fun z : γ × Bool × Bool => boolReal z.2.2) := by
    unfold boolReal
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hintegrand : Measurable
      (fun z : γ × Bool × Bool =>
        w z.1 * armIndicator d z.2.1 * boolReal z.2.2) :=
    ((hm.comp measurable_fst).mul hArm).mul hBool
  rw [D.observedLaw_eq_map,
    integral_map hmap.aemeasurable hintegrand.aestronglyMeasurable]
  exact integral_weighted_observedProduct D d w hm hw

/-- A [finite-cell observed table](hyp:D), [treatment arm](hyp:d), [covariate
weight and center](hyp:w,c), [their measurability](hyp:hm,hc), [integrable
weight](hyp:hw), and [integrable weighted center](hyp:hwc) give [the
observed-law centered arm-outcome mean through the arm probability and
regression](goal). The center may be unbounded. -/
theorem integral_observedLaw_weighted_centered (d : Bool)
    (w c : γ → ℝ) (hm : Measurable w) (hc : Measurable c)
    (hw : Integrable w (μ.map D.X))
    (hwc : Integrable (fun x => w x * c x) (μ.map D.X)) :
    ∫ z : γ × Bool × Bool,
        w z.1 * (armIndicator d z.2.1 * (boolReal z.2.2 - c z.1))
          ∂D.observedLaw =
      ∫ x, w x * (D.armProb d x * (D.mean d x - c x))
        ∂(μ.map D.X) := by
  have hY : Measurable (observedY D.A D.Y0 D.Y1) := by
    exact Measurable.ite
      (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  have hmap : Measurable
      (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
    D.measurable_X.prodMk (D.measurable_A.prodMk hY)
  have hweight : Integrable (fun ω => w (D.X ω)) μ :=
    (integrable_map_measure hm.aestronglyMeasurable
      D.measurable_X.aemeasurable).1 hw
  have hweightc : Integrable (fun ω => w (D.X ω) * c (D.X ω)) μ :=
    (integrable_map_measure (hm.mul hc).aestronglyMeasurable
      D.measurable_X.aemeasurable).1 hwc
  have hbase : Integrable (fun z : γ × Bool × Bool => w z.1) D.observedLaw := by
    rw [D.observedLaw_eq_map]
    exact (integrable_map_measure (hm.comp measurable_fst).aestronglyMeasurable
      hmap.aemeasurable).2 hweight
  have hbasec : Integrable
      (fun z : γ × Bool × Bool => w z.1 * c z.1) D.observedLaw := by
    rw [D.observedLaw_eq_map]
    exact (integrable_map_measure
      ((hm.mul hc).comp measurable_fst).aestronglyMeasurable
      hmap.aemeasurable).2 hweightc
  have hArm : Measurable
      (fun z : γ × Bool × Bool => armIndicator d z.2.1) := by
    unfold armIndicator
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hBool : Measurable
      (fun z : γ × Bool × Bool => boolReal z.2.2) := by
    unfold boolReal
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)
      measurable_const measurable_const
  have hArmBound : ∀ z : γ × Bool × Bool, ‖armIndicator d z.2.1‖ ≤ (1 : ℝ) := by
    intro z
    simp only [armIndicator]
    split_ifs <;> simp
  have hBoolBound : ∀ z : γ × Bool × Bool, ‖boolReal z.2.2‖ ≤ (1 : ℝ) := by
    intro z
    simp only [boolReal]
    split_ifs <;> simp
  have hLarm : Integrable
      (fun z : γ × Bool × Bool => w z.1 * armIndicator d z.2.1)
        D.observedLaw :=
    hbase.mul_bdd hArm.aestronglyMeasurable (ae_of_all _ hArmBound)
  have hLprod : Integrable
      (fun z : γ × Bool × Bool =>
        w z.1 * armIndicator d z.2.1 * boolReal z.2.2) D.observedLaw :=
    hLarm.mul_bdd hBool.aestronglyMeasurable (ae_of_all _ hBoolBound)
  have hLcenter : Integrable
      (fun z : γ × Bool × Bool =>
        w z.1 * c z.1 * armIndicator d z.2.1) D.observedLaw :=
    hbasec.mul_bdd hArm.aestronglyMeasurable (ae_of_all _ hArmBound)
  have hRarm : Integrable (fun x => w x * D.armProb d x) (μ.map D.X) :=
    hw.mul_bdd (D.measurable_armProb d).aestronglyMeasurable
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(D.armProb_mem_Icc d x).1], (D.armProb_mem_Icc d x).2⟩))
  have hRprod : Integrable
      (fun x => w x * D.armProb d x * D.mean d x) (μ.map D.X) :=
    hRarm.mul_bdd (D.measurable_mean d).aestronglyMeasurable
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(D.mean_mem_Icc d x).1], (D.mean_mem_Icc d x).2⟩))
  have hRcenter : Integrable
      (fun x => w x * c x * D.armProb d x) (μ.map D.X) :=
    hwc.mul_bdd (D.measurable_armProb d).aestronglyMeasurable
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(D.armProb_mem_Icc d x).1], (D.armProb_mem_Icc d x).2⟩))
  calc
    _ = (∫ z : γ × Bool × Bool,
          w z.1 * armIndicator d z.2.1 * boolReal z.2.2 ∂D.observedLaw) -
        (∫ z : γ × Bool × Bool,
          (w z.1 * c z.1) * armIndicator d z.2.1 ∂D.observedLaw) := by
      rw [← integral_sub hLprod hLcenter]
      congr 1
      funext z
      ring
    _ = (∫ x, w x * D.armProb d x * D.mean d x ∂(μ.map D.X)) -
        (∫ x, (w x * c x) * D.armProb d x ∂(μ.map D.X)) := by
      rw [integral_observedLaw_weighted_observedProduct D d w hm hw,
        integral_observedLaw_weighted_arm D d (fun x => w x * c x) (hm.mul hc) hwc]
    _ = _ := by
      rw [← integral_sub hRprod hRcenter]
      congr 1
      funext x
      ring

end Causalean.PO.Bridge
