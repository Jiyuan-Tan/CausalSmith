module
public import Causalean.Stat.Concentration.Hoeffding.RandomDesign.Tail
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Coefficients
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.MGF
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Maximal
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Template

/-! # Conditional selected-mesh coefficient fibres -/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.RandomDesignWeightedHoeffding
open scoped Classical

/-- Treatment and covariate coordinates of a sample. For [the stated inputs and conditions](hyp:ω), [the `sampleDesign` object being defined](goal). -/
def sampleDesign {d n : ℕ} (ω : Fin n → Obs d) :
    Fin n → (Fin d → ℝ) × Bool :=
  fun i => ((ω i).1, (ω i).2.1)

/-- The treated outcome residual on a fixed complete-design fibre, extended
by zero on untreated coordinates. For [the stated inputs and conditions](hyp:P,ω,i,ξ), [the `conditionalTreatedResidual` object being defined](goal). -/
noncomputable def conditionalTreatedResidual {d n : ℕ}
    (P : Measure (Obs d)) [IsFiniteMeasure P]
    (ω : Fin n → Obs d) (i : Fin n) (ξ : Fin n → Obs d) : ℝ :=
  if (ω i).2.1 = true then
    (ξ i).2.2 - treatedRegression P (ω i).1
  else 0

/-- Replace each response by its treated conditional mean, with an arbitrary
zero value on untreated coordinates. For [the stated inputs and conditions](hyp:P,ω), [the `conditionalMeanSample` object being defined](goal). -/
noncomputable def conditionalMeanSample {d n : ℕ}
    (P : Measure (Obs d)) [IsFiniteMeasure P]
    (ω : Fin n → Obs d) : Fin n → Obs d :=
  fun i => ((ω i).1, (ω i).2.1,
    if (ω i).2.1 = true then treatedRegression P (ω i).1 else 0)

/-- For [the stated dimensions](hyp:d,n), [the complete vector of covariates and
treatment arms is measurable](goal). -/
@[fun_prop] lemma sampleDesign_measurable {d n : ℕ} :
    Measurable (sampleDesign (d := d) (n := n)) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun ω : Fin n → Obs d => ((ω i).1, (ω i).2.1))
  fun_prop

/-- The treated residual condition holds at every coordinate of an IID sample. [For the stated inputs and conditions](hyp:d,n,B,P,Q,hIID,hres), [the asserted conclusion holds](goal). -/
lemma boundedResidual_on_iid_sample {d n : ℕ} {B : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P)
    (hres : BoundedMeanSubGaussianResidual P B) :
    ∀ᵐ ω ∂Q, ∀ i : Fin n, ∀ t : ℝ,
      Integrable (fun y : ℝ => Real.exp (t * (y - treatedRegression P (ω i).1)))
        (treatedKernel P (ω i).1) ∧
      mgf (fun y : ℝ => y - treatedRegression P (ω i).1)
        (treatedKernel P (ω i).1) t ≤ Real.exp (B ^ 2 * t ^ 2 / 2) := by
  have hP : ∀ᵐ z ∂P, ∀ t : ℝ,
      Integrable (fun y : ℝ => Real.exp (t * (y - treatedRegression P z.1)))
        (treatedKernel P z.1) ∧
      mgf (fun y : ℝ => y - treatedRegression P z.1)
        (treatedKernel P z.1) t ≤ Real.exp (B ^ 2 * t ^ 2 / 2) := by
    have hx := ae_of_ae_map measurable_fst.aemeasurable hres
    filter_upwards [hx] with z hz
    exact hz.2
  have hi : ∀ i : Fin n, ∀ᵐ ω ∂Q, ∀ t : ℝ,
      Integrable (fun y : ℝ => Real.exp (t * (y - treatedRegression P (ω i).1)))
        (treatedKernel P (ω i).1) ∧
      mgf (fun y : ℝ => y - treatedRegression P (ω i).1)
        (treatedKernel P (ω i).1) t ≤ Real.exp (B ^ 2 * t ^ 2 / 2) := by
    intro i
    have hmap : Q.map (fun ω : Fin n → Obs d => ω i) = P := by
      rw [hIID]
      simpa using Measure.pi_map_eval (fun _ : Fin n => P) i
    have hP' : ∀ᵐ z ∂Q.map (fun ω : Fin n → Obs d => ω i), ∀ t : ℝ,
        Integrable (fun y : ℝ => Real.exp (t * (y - treatedRegression P z.1)))
          (treatedKernel P z.1) ∧
        mgf (fun y : ℝ => y - treatedRegression P z.1)
          (treatedKernel P z.1) t ≤ Real.exp (B ^ 2 * t ^ 2 / 2) := by
      simpa only [hmap] using hP
    exact ae_of_ae_map (μ := Q) (f := fun ω : Fin n → Obs d => ω i)
      (measurable_pi_apply i).aemeasurable hP'
  exact ae_all_iff.mpr hi

/-- The iid observation law disintegrates over the complete treatment and
covariate design as a product of one-observation outcome kernels. [For the stated inputs and conditions](hyp:d,n,P), [the asserted conclusion holds](goal). -/
lemma sampleDesign_outcome_product_law {d n : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] :
    (Measure.pi (fun _ : Fin n => P)).map
        (fun ω => (sampleDesign ω, fun i => (ω i).2.2)) =
      Causalean.Stat.attachKernel
        (Measure.pi (fun _ : Fin n => P.map (fun z => (z.1, z.2.1))))
        (Causalean.Stat.finProductKernel n
          (condDistrib (fun z : Obs d => z.2.2)
            (fun z : Obs d => (z.1, z.2.1)) P)) := by
  let design : Obs d → (Fin d → ℝ) × Bool := fun z => (z.1, z.2.1)
  let Y : Obs d → ℝ := fun z => z.2.2
  have hdesign : Measurable design := by fun_prop
  have hY : Measurable Y := by fun_prop
  have hsame :
      (fun z : Fin n → Obs d =>
        (designVector design z,
          fun i => Y (z i))) =
        (fun ω => (sampleDesign ω, fun i => (ω i).2.2)) := by
    rfl
  rw [← hsame]
  exact product_observation_law_map_design_outcome P design hdesign Y hY

/-- Given the complete design, the outcome vector has the product of the
one-observation conditional outcome laws. [For the stated inputs and conditions](hyp:d,n,P,Q,hIID), [the asserted conclusion holds](goal). -/
lemma sampleDesign_conditional_outcome_product_law {d n : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P) :
    ∀ᵐ x ∂Q.map sampleDesign,
      condDistrib (fun ω : Fin n → Obs d => fun i => (ω i).2.2)
          sampleDesign Q x =
        Causalean.Stat.finProductKernel n
          (condDistrib (fun z : Obs d => z.2.2)
            (fun z : Obs d => (z.1, z.2.1)) P) x := by
  subst Q
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    sampleDesign_measurable (by fun_prop)
  have hdesignLaw :
      (Measure.pi (fun _ : Fin n => P)).map sampleDesign =
        Measure.pi (fun _ : Fin n =>
          P.map (fun z : Obs d => (z.1, z.2.1))) := by
    exact Causalean.Stat.map_pi_finCoordinatewise n P
      (phi := fun z : Obs d => (z.1, z.2.1)) (by fun_prop)
  rw [hdesignLaw]
  exact sampleDesign_outcome_product_law P

/-- The conditional complete-sample law sends its response vector to the
product of the one-observation response kernels. [For the stated inputs and conditions](hyp:d,n,P,Q,hIID), [the asserted conclusion holds](goal). -/
lemma sampleDesign_conditional_sample_outcome_product_law {d n : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P) :
    ∀ᵐ ω ∂Q,
      (condDistrib id sampleDesign Q (sampleDesign ω)).map
          (fun ξ : Fin n → Obs d => fun i => (ξ i).2.2) =
        Causalean.Stat.finProductKernel n
          (condDistrib (fun z : Obs d => z.2.2)
            (fun z : Obs d => (z.1, z.2.1)) P) (sampleDesign ω) := by
  have hcomp := condDistrib_comp (μ := Q) (mβ := inferInstance) (X := sampleDesign)
    (Y := id) aemeasurable_id
    (f := fun ξ : Fin n → Obs d => fun i => (ξ i).2.2) (by fun_prop)
  have hresp : Measurable (fun ξ : Fin n → Obs d => fun i => (ξ i).2.2) := by
    fun_prop
  have hprod := sampleDesign_conditional_outcome_product_law P Q hIID
  have hdesign : ∀ᵐ x ∂Q.map sampleDesign,
      (condDistrib id sampleDesign Q x).map
          (fun ξ : Fin n → Obs d => fun i => (ξ i).2.2) =
        Causalean.Stat.finProductKernel n
          (condDistrib (fun z : Obs d => z.2.2)
            (fun z : Obs d => (z.1, z.2.1)) P) x := by
    filter_upwards [hcomp, hprod] with x hc hp
    simpa only [Kernel.map_apply _ hresp] using hc.symm.trans hp
  exact ae_of_ae_map sampleDesign_measurable.aemeasurable hdesign

/-- Under the complete-design conditional law, each response coordinate has
the corresponding one-observation conditional response law. [For the stated inputs and conditions](hyp:d,n,P,Q,hIID), [the asserted conclusion holds](goal). -/
lemma sampleDesign_conditional_response_coordinate_law {d n : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P) :
    ∀ᵐ ω ∂Q, ∀ i : Fin n,
      (condDistrib id sampleDesign Q (sampleDesign ω)).map
          (fun ξ : Fin n → Obs d => (ξ i).2.2) =
        condDistrib (fun z : Obs d => z.2.2)
          (fun z : Obs d => (z.1, z.2.1)) P (sampleDesign ω i) := by
  filter_upwards [sampleDesign_conditional_sample_outcome_product_law P Q hIID]
    with ω hproduct
  intro i
  let μ := condDistrib id sampleDesign Q (sampleDesign ω)
  let K := condDistrib (fun z : Obs d => z.2.2)
    (fun z : Obs d => (z.1, z.2.1)) P
  have hpi : μ.map (fun ξ : Fin n → Obs d => fun r => (ξ r).2.2) =
      Measure.pi (fun r : Fin n => K (sampleDesign ω r)) := by
    simpa only [μ, K, Causalean.Stat.finProductKernel_apply] using hproduct
  calc
    μ.map (fun ξ : Fin n → Obs d => (ξ i).2.2) =
        (μ.map (fun ξ : Fin n → Obs d => fun r => (ξ r).2.2)).map
          (Function.eval i) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (Measure.pi (fun r : Fin n => K (sampleDesign ω r))).map
          (Function.eval i) := by rw [hpi]
    _ = K (sampleDesign ω i) := by
      rw [Measure.pi_map_eval]
      simp

/-- On almost every fixed-design fibre, every treated response residual has
the one-observation exponential integrability and MGF bound. [For the stated inputs and conditions](hyp:d,n,B,P,Q,hIID,hres), [the asserted conclusion holds](goal). -/
lemma sampleDesign_conditional_treatedResidual_mgf {d n : ℕ} {B : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P)
    (hres : BoundedMeanSubGaussianResidual P B) :
    ∀ᵐ ω ∂Q, ∀ i : Fin n, (ω i).2.1 = true → ∀ t : ℝ,
      Integrable (fun ξ : Fin n → Obs d =>
        Real.exp (t * ((ξ i).2.2 - treatedRegression P (ω i).1)))
          (condDistrib id sampleDesign Q (sampleDesign ω)) ∧
      mgf (fun ξ : Fin n → Obs d =>
        (ξ i).2.2 - treatedRegression P (ω i).1)
          (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
        Real.exp (B ^ 2 * t ^ 2 / 2) := by
  filter_upwards [boundedResidual_on_iid_sample P Q hIID hres,
    sampleDesign_conditional_response_coordinate_law P Q hIID]
    with ω hresω hcoord
  intro i hi t
  let μ := condDistrib id sampleDesign Q (sampleDesign ω)
  let X : (Fin n → Obs d) → ℝ := fun ξ => (ξ i).2.2
  let R : ℝ → ℝ := fun y => y - treatedRegression P (ω i).1
  have hmap : μ.map X = treatedKernel P (ω i).1 := by
    simpa only [μ, X, sampleDesign, treatedKernel, hi] using hcoord i
  constructor
  · have hint := (hresω i t).1
    rw [← hmap] at hint
    have hcomp := (integrable_map_measure hint.aestronglyMeasurable
      (show AEMeasurable X μ by fun_prop)).mp hint
    simpa only [μ, X, R, Function.comp_def] using hcomp
  · have hbound := (hresω i t).2
    rw [← hmap] at hbound
    rw [mgf_map (show AEMeasurable X μ by fun_prop) (by fun_prop)] at hbound
    simpa only [μ, X, R, Function.comp_def] using hbound

/-- Conditional on the design, the response coordinates are independent. [For the stated inputs and conditions](hyp:d,n,P,Q,hIID), [the asserted conclusion holds](goal). -/
lemma sampleDesign_conditional_outcome_independent {d n : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P) :
    ∀ᵐ ω ∂Q, iIndepFun (fun i (ξ : Fin n → Obs d) => (ξ i).2.2)
      (condDistrib id sampleDesign Q (sampleDesign ω)) := by
  filter_upwards [sampleDesign_conditional_sample_outcome_product_law P Q hIID]
    with ω hproduct
  let μ := condDistrib id sampleDesign Q (sampleDesign ω)
  let K := condDistrib (fun z : Obs d => z.2.2)
    (fun z : Obs d => (z.1, z.2.1)) P
  have hpi : μ.map (fun ξ : Fin n → Obs d => fun i => (ξ i).2.2) =
      Measure.pi (fun i : Fin n => K (sampleDesign ω i)) := by
    simpa only [μ, K, Causalean.Stat.finProductKernel_apply] using hproduct
  apply (iIndepFun_iff_map_fun_eq_pi_map (μ := μ)
    (f := fun i (ξ : Fin n → Obs d) => (ξ i).2.2)
    (by intro i; exact (show Measurable (fun ξ : Fin n → Obs d => (ξ i).2.2)
      by fun_prop).aemeasurable)).2
  rw [hpi]
  congr 1
  funext i
  have hcoord : μ.map (fun ξ : Fin n → Obs d => (ξ i).2.2) =
      (Measure.pi (fun i : Fin n => K (sampleDesign ω i))).map (Function.eval i) := by
    rw [← hpi, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hcoord, Measure.pi_map_eval]
  simp

/-- Almost every complete-design fibre carries independent residual
coordinates with the original uniform exponential-moment bound. [For the stated inputs and conditions](hyp:d,n,B,P,Q,hIID,hres), [the asserted conclusion holds](goal). -/
lemma sampleDesign_conditional_residual_family {d n : ℕ} {B : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P)
    (hres : BoundedMeanSubGaussianResidual P B) :
    ∀ᵐ ω ∂Q,
      iIndepFun (fun i ξ => conditionalTreatedResidual P ω i ξ)
        (condDistrib id sampleDesign Q (sampleDesign ω)) ∧
      ∀ i : Fin n, ∀ t : ℝ,
        Integrable (fun ξ => Real.exp
          (t * conditionalTreatedResidual P ω i ξ))
            (condDistrib id sampleDesign Q (sampleDesign ω)) ∧
        mgf (conditionalTreatedResidual P ω i)
            (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
          Real.exp (B ^ 2 * t ^ 2 / 2) := by
  filter_upwards [sampleDesign_conditional_outcome_independent P Q hIID,
    sampleDesign_conditional_treatedResidual_mgf P Q hIID hres]
    with ω hindep htreated
  constructor
  · simpa only [conditionalTreatedResidual, Function.comp_def] using
      hindep.comp
        (fun i y => if (ω i).2.1 = true then
          y - treatedRegression P (ω i).1 else 0)
        (by
          intro i
          by_cases hi : (ω i).2.1 = true <;> simp [hi] <;> fun_prop)
  · intro i t
    by_cases hi : (ω i).2.1 = true
    · have hfun : conditionalTreatedResidual P ω i =
          fun ξ => (ξ i).2.2 - treatedRegression P (ω i).1 := by
        funext ξ
        simp [conditionalTreatedResidual, hi]
      rw [hfun]
      exact htreated i hi t
    · have hfun : conditionalTreatedResidual P ω i =
          fun _ => 0 := by
        funext ξ
        simp [conditionalTreatedResidual, hi]
      rw [hfun]
      constructor
      · change Integrable (fun _ : Fin n → Obs d => Real.exp (t * 0))
          (condDistrib id sampleDesign Q (sampleDesign ω))
        simp
      · change mgf (fun _ : Fin n → Obs d => 0)
          (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
            Real.exp (B ^ 2 * t ^ 2 / 2)
        simp [mgf]
        positivity

/-- Every fixed-design residual coordinate is integrable and has mean zero
under almost every conditional sample law. [For the stated inputs and conditions](hyp:d,n,B,P,Q,hIID,hres), [the asserted conclusion holds](goal). -/
lemma sampleDesign_conditional_residual_mean_zero {d n : ℕ} {B : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P)
    (hres : BoundedMeanSubGaussianResidual P B) :
    ∀ᵐ ω ∂Q, ∀ i : Fin n,
      Integrable (conditionalTreatedResidual P ω i)
          (condDistrib id sampleDesign Q (sampleDesign ω)) ∧
      ∫ ξ, conditionalTreatedResidual P ω i ξ
          ∂condDistrib id sampleDesign Q (sampleDesign ω) = 0 := by
  filter_upwards [boundedResidual_on_iid_sample P Q hIID hres,
    sampleDesign_conditional_response_coordinate_law P Q hIID]
    with ω hresω hcoord
  intro i
  by_cases hi : (ω i).2.1 = true
  · let μ := condDistrib id sampleDesign Q (sampleDesign ω)
    let X : (Fin n → Obs d) → ℝ := fun ξ => (ξ i).2.2
    let R : ℝ → ℝ := fun y => y - treatedRegression P (ω i).1
    letI : IsProbabilityMeasure (treatedKernel P (ω i).1) := by
      unfold treatedKernel
      infer_instance
    have hmap : μ.map X = treatedKernel P (ω i).1 := by
      simpa only [μ, X, sampleDesign, treatedKernel, hi] using hcoord i
    have hRint : Integrable R (treatedKernel P (ω i).1) := by
      have hp := (hresω i (1 : ℝ)).1
      have hn := (hresω i (-1 : ℝ)).1
      have hm := integrable_pow_of_integrable_exp_mul
        (X := R) (t := (1 : ℝ)) (by norm_num) (by simpa [R] using hp)
          (by simpa [R] using hn) 1
      simpa [R] using hm
    have hcomp : Integrable (R ∘ X) μ := by
      have hRmap : Integrable R (μ.map X) := by
        rw [hmap]
        exact hRint
      exact (integrable_map_measure hRmap.aestronglyMeasurable
        (show AEMeasurable X μ by fun_prop)).mp hRmap
    have hfun : conditionalTreatedResidual P ω i = R ∘ X := by
      funext ξ
      simp [conditionalTreatedResidual, hi, R, X]
    constructor
    · simpa only [hfun] using hcomp
    · rw [hfun]
      change ∫ ξ, (R ∘ X) ξ ∂μ = 0
      have hRmap : Integrable R (μ.map X) := by
        rw [hmap]
        exact hRint
      have hYint : Integrable (fun y : ℝ => y) (treatedKernel P (ω i).1) := by
        have hc : Integrable (fun _ : ℝ => treatedRegression P (ω i).1)
            (treatedKernel P (ω i).1) := integrable_const _
        exact (hRint.add hc).congr (Filter.Eventually.of_forall (fun y => by simp [R]))
      calc
        ∫ ξ, (R ∘ X) ξ ∂μ = ∫ y, R y ∂μ.map X :=
          (integral_map (show AEMeasurable X μ by fun_prop)
            hRmap.aestronglyMeasurable).symm
        _ = ∫ y, R y ∂treatedKernel P (ω i).1 := by rw [hmap]
        _ = 0 := by
          change (∫ y, y - treatedRegression P (ω i).1
            ∂treatedKernel P (ω i).1) = 0
          rw [integral_sub hYint (integrable_const _)]
          simp [treatedRegression]
  · have hfun : conditionalTreatedResidual P ω i = fun _ => 0 := by
      funext ξ
      simp [conditionalTreatedResidual, hi]
    rw [hfun]
    simp

/-- Conditional on the observed design, the complete sample has that design
almost surely.  This supplies the fibre hypothesis for the coefficient
identity below. [For the stated inputs and conditions](hyp:d,n,Q), [the asserted conclusion holds](goal). -/
lemma sampleDesign_condDistrib_fibre {d n : ℕ}
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q] :
    ∀ᵐ ω ∂Q, ∀ᵐ ξ ∂condDistrib id sampleDesign Q (sampleDesign ω),
      sampleDesign ξ = sampleDesign ω := by
  have hcomp : condDistrib sampleDesign sampleDesign Q =ᵐ[Q.map sampleDesign]
      (condDistrib id sampleDesign Q).map sampleDesign := by
    simpa only [Function.comp_def, id_eq] using
      (condDistrib_comp (μ := Q) sampleDesign
        (Y := id) aemeasurable_id sampleDesign_measurable)
  have hself := condDistrib_self (μ := Q) sampleDesign
  have hdesign : ∀ᵐ x ∂Q.map sampleDesign,
      (condDistrib id sampleDesign Q x).map sampleDesign = Measure.dirac x := by
    filter_upwards [hcomp, hself] with x hc hs
    simpa only [Kernel.map_apply _ sampleDesign_measurable, Kernel.id_apply] using
      hc.symm.trans hs
  have hdesign' := ae_of_ae_map sampleDesign_measurable.aemeasurable hdesign
  filter_upwards [hdesign'] with ω hω
  have hs : (condDistrib id sampleDesign Q (sampleDesign ω))
      {ξ | sampleDesign ξ = sampleDesign ω} = 1 := by
    have hm := congrArg (fun μ : Measure (Fin n → (Fin d → ℝ) × Bool) =>
      μ {sampleDesign ω}) hω
    rw [Measure.map_apply sampleDesign_measurable (measurableSet_singleton _)] at hm
    simp at hm
    change (condDistrib id sampleDesign Q (sampleDesign ω))
      {ξ | sampleDesign ξ = sampleDesign ω} = 1 at hm
    exact hm
  exact (MeasureTheory.ae_iff.mpr (by
    have hp : IsProbabilityMeasure (condDistrib id sampleDesign Q (sampleDesign ω)) :=
      inferInstance
    change (condDistrib id sampleDesign Q (sampleDesign ω))
      {ξ | sampleDesign ξ = sampleDesign ω}ᶜ = 0
    have hset : MeasurableSet {ξ | sampleDesign ξ = sampleDesign ω} := by
      change MeasurableSet (sampleDesign ⁻¹' {sampleDesign ω})
      exact sampleDesign_measurable (measurableSet_singleton _)
    rw [measure_compl hset (by rw [hs]; simp), measure_univ, hs]
    simp))

/-- A fibre of the design map has a fixed Gram matrix; its coefficient
variation is exactly the inverse Gram applied to the response variation. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,hdesign), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_of_sampleDesign_eq {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hdesign : sampleDesign ξ = sampleDesign ω) :
    coefHat m j ξ k - coefHat m j ω k =
      Matrix.mulVec (gramHat m j ω k)⁻¹
        (responseMoment m j ξ k - responseMoment m j ω k) := by
  apply coefHat_sub_of_design_eq m j ω ξ k
  intro i
  have hi := congrFun hdesign i
  change ((ξ i).1, (ξ i).2.1) = ((ω i).1, (ω i).2.1) at hi
  exact ⟨congrArg (fun p : (Fin d → ℝ) × Bool => p.1) hi,
    congrArg (fun p : (Fin d → ℝ) × Bool => p.2) hi⟩

/-- On a fixed design fibre, one coefficient coordinate is a finite weighted
sum of the treated response residuals. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,α,hdesign), [the asserted conclusion holds](goal). -/
lemma coefHat_coordinate_residual_sum {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (hdesign : sampleDesign ξ = sampleDesign ω) :
    (coefHat m j ξ k - coefHat m j ω k) α =
      ∑ α' : MonoIndex d m, (gramHat m j ω k)⁻¹ α α' *
        ((tensorCount d m : ℝ)⁻¹ *
          ∑ ℓ : Fin d → Fin (m + 1),
            (treatedCount m j ω k ℓ : ℝ)⁻¹ *
              ∑ i : Fin n, if (ω i).2.1 = true ∧
                  (ω i).1 ∈ scaledMicroCell d m j k ℓ then
                  monoVec d m (fun a => ((ω i).1 a - cubeCorner d j k a) /
                    meshWidth j) α' * ((ξ i).2.2 - (ω i).2.2)
                else 0) := by
  classical
  rw [coefHat_sub_of_sampleDesign_eq m j ω ξ k hdesign]
  simp only [Matrix.mulVec, dotProduct]
  congr 1
  funext α'
  congr 1
  apply responseMoment_sub_of_design_eq m j ω ξ k
  intro i
  have hi := congrFun hdesign i
  change ((ξ i).1, (ξ i).2.1) = ((ω i).1, (ω i).2.1) at hi
  exact ⟨congrArg (fun p : (Fin d → ℝ) × Bool => p.1) hi,
    congrArg (fun p : (Fin d → ℝ) × Bool => p.2) hi⟩

/-- On a design fibre, the coefficient difference is the weighted sum of
outcome differences, with all weights fixed by the conditioning design. [For the stated inputs and conditions](hyp:d,n,m,j,ω,ξ,k,α,hdesign), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_of_sampleDesign_eq_weighted_sum {d n : ℕ} (m j : ℕ)
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (hdesign : sampleDesign ξ = sampleDesign ω) :
    (coefHat m j ξ k - coefHat m j ω k) α =
      ∑ i : Fin n, coefResidualWeight m j ω k α i *
        ((ξ i).2.2 - (ω i).2.2) := by
  have hd : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1 := by
    intro i
    have hi := congrFun hdesign i
    change ((ξ i).1, (ξ i).2.1) = ((ω i).1, (ω i).2.1) at hi
    exact ⟨congrArg (fun p : (Fin d → ℝ) × Bool => p.1) hi,
      congrArg (fun p : (Fin d → ℝ) × Bool => p.2) hi⟩
  have hs : (fun i : Fin n => ((ξ i).1, (ξ i).2.1, (ω i).2.2)) = ω := by
    funext i
    obtain ⟨hx, ha⟩ := hd i
    exact Prod.ext hx (Prod.ext ha rfl)
  simpa only [hs] using
    coefHat_sub_conditionalMeanSample_weighted_sum_of_design_eq
      m j ω ξ (fun i => (ω i).2.2) k α hd

/-- On a complete-design fibre, subtracting the fitted coefficient at the
conditional-mean sample leaves exactly the weighted residual sum. [For the stated inputs and conditions](hyp:d,n,m,j,P,ω,ξ,k,α,hdesign), [the asserted conclusion holds](goal). -/
lemma coefHat_sub_conditionalMeanSample_eq_residual_sum {d n : ℕ} (m j : ℕ)
    (P : Measure (Obs d)) [IsFiniteMeasure P]
    (ω ξ : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (hdesign : sampleDesign ξ = sampleDesign ω) :
    coefHat m j ξ k α - coefHat m j (conditionalMeanSample P ω) k α =
      ∑ i : Fin n, coefResidualWeight m j ω k α i *
        conditionalTreatedResidual P ω i ξ := by
  classical
  have hd : ∀ i, (ξ i).1 = (ω i).1 ∧ (ξ i).2.1 = (ω i).2.1 := by
    intro i
    have hi := congrFun hdesign i
    change ((ξ i).1, (ξ i).2.1) = ((ω i).1, (ω i).2.1) at hi
    exact ⟨congrArg (fun p : (Fin d → ℝ) × Bool => p.1) hi,
      congrArg (fun p : (Fin d → ℝ) × Bool => p.2) hi⟩
  let mean : Fin n → ℝ := fun i =>
    if (ω i).2.1 = true then treatedRegression P (ω i).1 else 0
  have hsamp : (fun i => ((ξ i).1, (ξ i).2.1, mean i)) =
      conditionalMeanSample P ω := by
    funext i
    obtain ⟨hx, ha⟩ := hd i
    simp only [conditionalMeanSample, mean]
    exact Prod.ext hx (Prod.ext ha rfl)
  have hbase := coefHat_sub_conditionalMeanSample_weighted_sum_of_design_eq
    m j ω ξ mean k α hd
  simp only [Pi.sub_apply, hsamp] at hbase
  rw [hbase]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (ω i).2.1 = true
  · simp [mean, conditionalTreatedResidual, hi]
  · rw [coefResidualWeight_zero_of_untreated m j ω k α i
      (Bool.eq_false_of_not_eq_true hi)]
    simp

/-- Conditional centre of one fitted coefficient given all designs and arms. For [the stated inputs and conditions](hyp:Q,m,j,ω,k,α), [the `conditionalCoefCentre` object being defined](goal). -/
noncomputable def conditionalCoefCentre {d n : ℕ} (Q : Measure (Fin n → Obs d))
    [IsFiniteMeasure Q] (m j : ℕ) (ω : Fin n → Obs d)
    (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) : ℝ :=
  ∫ ξ, coefHat m j ξ k α ∂condDistrib id sampleDesign Q (sampleDesign ω)

/-- The conditional coefficient centre is the fitted coefficient obtained by
replacing treated responses with their conditional means. [For the stated inputs and conditions](hyp:d,n,B,P,Q,hIID,hres), [the asserted conclusion holds](goal). -/
lemma conditionalCoefCentre_eq_conditionalMeanSample {d n : ℕ} {B : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P)
    (hres : BoundedMeanSubGaussianResidual P B) :
    ∀ᵐ ω ∂Q, ∀ (m j : ℕ) (k : Fin d → Fin (2 ^ j))
      (α : MonoIndex d m),
      conditionalCoefCentre Q m j ω k α =
        coefHat m j (conditionalMeanSample P ω) k α := by
  filter_upwards [sampleDesign_condDistrib_fibre Q,
    sampleDesign_conditional_residual_mean_zero P Q hIID hres]
    with ω hfibre hzero
  intro m j k α
  let μ := condDistrib id sampleDesign Q (sampleDesign ω)
  let c := coefHat m j (conditionalMeanSample P ω) k α
  let S : (Fin n → Obs d) → ℝ := fun ξ =>
    ∑ i : Fin n, coefResidualWeight m j ω k α i *
      conditionalTreatedResidual P ω i ξ
  have hterm : ∀ i : Fin n, Integrable
      (fun ξ => coefResidualWeight m j ω k α i *
        conditionalTreatedResidual P ω i ξ) μ := by
    intro i
    exact (hzero i).1.const_mul _
  have hSint : Integrable S μ := by
    dsimp only [S]
    exact integrable_finset_sum Finset.univ (fun i _ => hterm i)
  have htermMean : ∀ i : Fin n,
      ∫ ξ, coefResidualWeight m j ω k α i *
        conditionalTreatedResidual P ω i ξ ∂μ = 0 := by
    intro i
    rw [integral_const_mul, (hzero i).2, mul_zero]
  have hSmean : ∫ ξ, S ξ ∂μ = 0 := by
    dsimp only [S]
    rw [integral_finset_sum Finset.univ (fun i _ => hterm i)]
    simp [htermMean]
  have hcoef : ∀ᵐ ξ ∂μ, coefHat m j ξ k α = c + S ξ := by
    filter_upwards [hfibre] with ξ hdesign
    have h := coefHat_sub_conditionalMeanSample_eq_residual_sum
      m j P ω ξ k α hdesign
    dsimp only [c, S]
    linarith
  unfold conditionalCoefCentre
  change (∫ ξ, coefHat m j ξ k α ∂μ) = c
  rw [integral_congr_ae hcoef]
  rw [integral_add (integrable_const c) hSint, integral_const, hSmean]
  simp

end CausalSmith.Stat.WeakOverlap
