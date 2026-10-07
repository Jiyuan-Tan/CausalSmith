module
public import Causalean.Mathlib.Probability.Independence.Conditional.CondExp
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Finite-cell g-formula bridge

This module turns a binary observed table specified through setwise kernel
identities into conditional means of binary potential outcomes.  It provides
the real-integral conversion, arm and outcome-product conditional expectations,
and the conditional treated-minus-control contrast without requiring a full
potential-outcome system.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence.Conditional

namespace Causalean
namespace PO
namespace Bridge

/-- The [Boolean value](hyp:b) is represented by [its zero-or-one real-valued
outcome](goal), [using one for true and zero for false](step:1). -/
def boolReal (b : Bool) : ℝ := if b then 1 else 0

/-- The [selected treatment arm](hyp:d) and [realized treatment arm](hyp:a)
determine [the real-valued arm indicator](goal), [which is one exactly when the
arms agree](step:1). -/
def armIndicator (d a : Bool) : ℝ := if a = d then 1 else 0

/-- The [realized treatment](hyp:A), [control potential outcome](hyp:Y0),
[treated potential outcome](hyp:Y1), and [sample-space unit](hyp:ω) determine
[the observed Boolean outcome](goal), [by selecting the potential outcome for
the realized arm](step:1). -/
def observedY (A Y0 Y1 : Ω → Bool) (ω : Ω) : Bool :=
  if A ω then Y1 ω else Y0 ω

/-- A [sample space](hyp:Ω), [covariate space](hyp:γ), and [population
measure](hyp:μ) determine a binary observed table with covariate-indexed arm
probabilities and outcome means. Its fields record the covariate, the binary
treatment, and the two binary potential outcomes; measurable arm-probability
and outcome-mean functions of the covariate with values between zero and one;
integrability; the observed law as the joint law of covariate, treatment, and
realized outcome; and the setwise cell identities expressing the probability of
each treatment-outcome cell over a covariate set through those functions. -/
structure FiniteCellData (Ω γ : Type*) [MeasurableSpace Ω] [MeasurableSpace γ]
    (μ : Measure Ω) where
  X : Ω → γ
  A : Ω → Bool
  Y0 : Ω → Bool
  Y1 : Ω → Bool
  armProb : Bool → γ → ℝ
  mean : Bool → γ → ℝ
  observedLaw : Measure (γ × Bool × Bool)
  measurable_X : Measurable X
  measurable_A : Measurable A
  measurable_Y0 : Measurable Y0
  measurable_Y1 : Measurable Y1
  measurable_armProb : ∀ d, Measurable (armProb d)
  measurable_mean : ∀ d, Measurable (mean d)
  armProb_mem_Icc : ∀ d x, armProb d x ∈ Set.Icc (0 : ℝ) 1
  mean_mem_Icc : ∀ d x, mean d x ∈ Set.Icc (0 : ℝ) 1
  integrable_armProb : ∀ d, Integrable (fun ω => armProb d (X ω)) μ
  integrable_product : ∀ d,
    Integrable (fun ω => armProb d (X ω) * mean d (X ω)) μ
  integrable_potential : ∀ d : Bool,
    Integrable (fun ω => boolReal (if d then Y1 ω else Y0 ω)) μ
  observedLaw_eq_map :
    observedLaw = μ.map (fun ω => (X ω, A ω, observedY A Y0 Y1 ω))
  cell_kernel : ∀ (s : Set γ), MeasurableSet s → ∀ d y : Bool,
    observedLaw {z | z.1 ∈ s ∧ z.2.1 = d ∧ z.2.2 = y} =
      ∫⁻ x in s, ENNReal.ofReal
        (armProb d x * (if y then mean d x else 1 - mean d x)) ∂(μ.map X)

/-- The [binary observed table](hyp:D) determines [the covariate σ-algebra](goal),
[by pulling the covariate-space σ-algebra back along its covariate map](step:1). -/
@[instance_reducible] def FiniteCellData.sigmaX
    {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    {μ : Measure Ω} (D : FiniteCellData Ω γ μ) : MeasurableSpace Ω :=
  MeasurableSpace.comap D.X inferInstance

/-- The [binary observed table](hyp:D) and [intervention arm](hyp:d) determine
[the selected Boolean potential outcome](goal), [by choosing the treated
potential outcome for the true arm and the control potential outcome otherwise](step:1). -/
def FiniteCellData.potential {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    {μ : Measure Ω} (D : FiniteCellData Ω γ μ) (d : Bool) : Ω → Bool :=
  if d then D.Y1 else D.Y0

variable {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
variable {μ : Measure Ω} [IsFiniteMeasure μ] (D : FiniteCellData Ω γ μ)

/-- The [binary observed table](hyp:D) and [treatment arm](hyp:d) imply
[integrability of that arm's indicator](goal), [because the indicator is
measurable and bounded by one under the finite population measure](step:1). -/
theorem FiniteCellData.integrable_armIndicator (d : Bool) :
    Integrable (fun ω => armIndicator d (D.A ω)) μ := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (Measurable.ite (measurableSet_eq_fun D.measurable_A measurable_const)
      measurable_const measurable_const).aestronglyMeasurable
  · filter_upwards [] with ω
    simp only [armIndicator]
    split_ifs <;> simp

/-- The [binary observed table](hyp:D) and [treatment arm](hyp:d) imply
[integrability of the arm indicator times the observed binary outcome](goal),
[because this product is measurable and bounded by one under the finite
population measure](step:1). -/
theorem FiniteCellData.integrable_observedProduct (d : Bool) :
    Integrable (fun ω => armIndicator d (D.A ω) *
      boolReal (observedY D.A D.Y0 D.Y1 ω)) μ := by
  refine Integrable.of_bound ?_ 1 ?_
  · have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
      Measurable.ite (measurableSet_eq_fun D.measurable_A measurable_const)
        D.measurable_Y1 D.measurable_Y0
    exact ((Measurable.ite (measurableSet_eq_fun D.measurable_A measurable_const)
      measurable_const measurable_const).mul
      (Measurable.ite (measurableSet_eq_fun hY measurable_const)
        measurable_const measurable_const)).aestronglyMeasurable
  · filter_upwards [] with ω
    simp only [armIndicator, boolReal]
    split_ifs <;> simp

omit [IsFiniteMeasure μ] in
/-- The [binary observed table](hyp:D), [treatment arm](hyp:d), [outcome
value](hyp:y), [covariate set](hyp:s), and [measurability of that set](hyp:hs)
imply [that the corresponding observed-law cell is the matching event in the
original sample space](goal). -/
theorem FiniteCellData.measure_cell_pullback (d y : Bool)
    (s : Set γ) (hs : MeasurableSet s) :
    D.observedLaw {z | z.1 ∈ s ∧ z.2.1 = d ∧ z.2.2 = y} =
      μ {ω | D.X ω ∈ s ∧ D.A ω = d ∧ observedY D.A D.Y0 D.Y1 ω = y} := by
  rw [D.observedLaw_eq_map]
  have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
    Measurable.ite (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  have hmap : Measurable (fun ω => (D.X ω, D.A ω, observedY D.A D.Y0 D.Y1 ω)) :=
    D.measurable_X.prodMk (D.measurable_A.prodMk hY)
  rw [Measure.map_apply hmap]
  · rfl
  · simpa only [Set.ofPred_and, Set.preimage, Function.comp_apply, Set.inter_assoc] using
      ((hs.preimage measurable_fst).inter
      (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
        (measurable_const : Measurable (fun _ : γ × Bool × Bool => d)))).inter
      (measurableSet_eq_fun (measurable_snd.comp measurable_snd)
        (measurable_const : Measurable (fun _ : γ × Bool × Bool => y)))

omit [IsFiniteMeasure μ] in
/-- The [binary observed table](hyp:D), [treatment arm](hyp:d), [outcome
value](hyp:y), [covariate set](hyp:s), and [measurability of that set](hyp:hs)
imply [the real set-integral identity for the corresponding observed cell](goal). -/
theorem FiniteCellData.setIntegral_cell (d y : Bool)
    (s : Set γ) (hs : MeasurableSet s) :
    ∫ ω in D.X ⁻¹' s,
      armIndicator d (D.A ω) *
        armIndicator y (observedY D.A D.Y0 D.Y1 ω) ∂μ =
      ∫ x in s, D.armProb d x *
        (if y then D.mean d x else 1 - D.mean d x) ∂(μ.map D.X) := by
  let t : Set Ω := {ω | D.A ω = d ∧ observedY D.A D.Y0 D.Y1 ω = y}
  have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
    Measurable.ite (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  have ht : MeasurableSet t :=
    (measurableSet_eq_fun D.measurable_A measurable_const).inter
      (measurableSet_eq_fun hY measurable_const)
  have hleft :
      (∫ ω in D.X ⁻¹' s, armIndicator d (D.A ω) *
        armIndicator y (observedY D.A D.Y0 D.Y1 ω) ∂μ) =
        μ.real {ω | D.X ω ∈ s ∧ D.A ω = d ∧
          observedY D.A D.Y0 D.Y1 ω = y} := by
    have hfun : ∀ ω, armIndicator d (D.A ω) *
        armIndicator y (observedY D.A D.Y0 D.Y1 ω) =
        t.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      simp only [armIndicator, t, Set.indicator, Set.mem_ofPred_eq]
      split_ifs <;> simp_all
    simp_rw [hfun]
    rw [setIntegral_indicator ht, setIntegral_one_eq_measureReal]
    congr 1
  have hfm : Measurable (fun x => D.armProb d x *
      (if y then D.mean d x else 1 - D.mean d x)) := by
    cases y
    · exact (D.measurable_armProb d).mul (measurable_const.sub (D.measurable_mean d))
    · exact (D.measurable_armProb d).mul (D.measurable_mean d)
  have hnn : ∀ x, 0 ≤ D.armProb d x *
      (if y then D.mean d x else 1 - D.mean d x) := by
    intro x
    apply mul_nonneg (D.armProb_mem_Icc d x).1
    rcases D.mean_mem_Icc d x with ⟨h0, h1⟩
    cases y <;> simp <;> linarith
  calc
    _ = μ.real {ω | D.X ω ∈ s ∧ D.A ω = d ∧
        observedY D.A D.Y0 D.Y1 ω = y} := hleft
    _ = (D.observedLaw {z | z.1 ∈ s ∧ z.2.1 = d ∧ z.2.2 = y}).toReal := by
      rw [measureReal_def, D.measure_cell_pullback d y s hs]
    _ = (∫⁻ x in s, ENNReal.ofReal
        (D.armProb d x * (if y then D.mean d x else 1 - D.mean d x)) ∂(μ.map D.X)).toReal := by
      rw [D.cell_kernel s hs d y]
    _ = _ := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (μ := (μ.map D.X).restrict s) (ae_of_all _ hnn) hfm.aestronglyMeasurable]

/-- The [binary observed table](hyp:D), [treatment arm](hyp:d), [covariate
set](hyp:s), and [measurability of that set](hyp:hs) imply [the set-integral
identity for the arm indicator](goal), [by summing the two outcome cells](step:1). -/
theorem FiniteCellData.setIntegral_arm (d : Bool)
    (s : Set γ) (hs : MeasurableSet s) :
    ∫ ω in D.X ⁻¹' s, armIndicator d (D.A ω) ∂μ =
      ∫ x in s, D.armProb d x ∂(μ.map D.X) := by
  have hY : Measurable (observedY D.A D.Y0 D.Y1) :=
    Measurable.ite (measurableSet_eq_fun D.measurable_A measurable_const)
      D.measurable_Y1 D.measurable_Y0
  have hintL (y : Bool) : Integrable (fun ω => armIndicator d (D.A ω) *
      armIndicator y (observedY D.A D.Y0 D.Y1 ω)) μ := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact ((Measurable.ite (measurableSet_eq_fun D.measurable_A measurable_const)
        measurable_const measurable_const).mul
        (Measurable.ite (measurableSet_eq_fun hY measurable_const)
          measurable_const measurable_const)).aestronglyMeasurable
    · filter_upwards [] with ω
      simp only [armIndicator]
      split_ifs <;> simp
  have hmeas (y : Bool) : Measurable (fun x => D.armProb d x *
      (if y then D.mean d x else 1 - D.mean d x)) := by
    cases y
    · exact (D.measurable_armProb d).mul (measurable_const.sub (D.measurable_mean d))
    · exact (D.measurable_armProb d).mul (D.measurable_mean d)
  have hintR (y : Bool) : Integrable (fun x => D.armProb d x *
      (if y then D.mean d x else 1 - D.mean d x)) (μ.map D.X) := by
    apply (integrable_map_measure (hmeas y).aestronglyMeasurable
      D.measurable_X.aemeasurable).2
    cases y
    · convert (D.integrable_armProb d).sub (D.integrable_product d) using 1
      funext ω
      simp [mul_sub]
    · simpa [Function.comp_def] using D.integrable_product d
  have hL :
      (∫ ω in D.X ⁻¹' s, armIndicator d (D.A ω) ∂μ) =
      (∫ ω in D.X ⁻¹' s, armIndicator d (D.A ω) *
        armIndicator true (observedY D.A D.Y0 D.Y1 ω) ∂μ) +
      (∫ ω in D.X ⁻¹' s, armIndicator d (D.A ω) *
        armIndicator false (observedY D.A D.Y0 D.Y1 ω) ∂μ) := by
    rw [← integral_add (hintL true).restrict (hintL false).restrict]
    apply integral_congr_ae
    filter_upwards [] with ω
    cases observedY D.A D.Y0 D.Y1 ω <;> simp [armIndicator]
  have hR :
      (∫ x in s, D.armProb d x * D.mean d x ∂(μ.map D.X)) +
      (∫ x in s, D.armProb d x * (1 - D.mean d x) ∂(μ.map D.X)) =
      ∫ x in s, D.armProb d x ∂(μ.map D.X) := by
    simpa using (integral_add (hintR true).restrict (hintR false).restrict).symm.trans (by
      apply integral_congr_ae
      filter_upwards [] with x
      simp
      ring)
  calc
    _ = _ := hL
    _ = (∫ x in s, D.armProb d x * D.mean d x ∂(μ.map D.X)) +
        (∫ x in s, D.armProb d x * (1 - D.mean d x) ∂(μ.map D.X)) := by
      rw [D.setIntegral_cell d true s hs, D.setIntegral_cell d false s hs]
      simp
    _ = _ := hR

omit [IsFiniteMeasure μ] in
/-- The [binary observed table](hyp:D), [treatment arm](hyp:d), [covariate
set](hyp:s), and [measurability of that set](hyp:hs) imply [the set-integral
identity for the observed outcome times the arm indicator](goal), [because a
true Boolean outcome is its real indicator](step:1). -/
theorem FiniteCellData.setIntegral_observedProduct (d : Bool)
    (s : Set γ) (hs : MeasurableSet s) :
    ∫ ω in D.X ⁻¹' s,
      armIndicator d (D.A ω) * boolReal (observedY D.A D.Y0 D.Y1 ω) ∂μ =
      ∫ x in s, D.armProb d x * D.mean d x ∂(μ.map D.X) := by
  simpa [boolReal, armIndicator] using D.setIntegral_cell d true s hs

variable {μ : Measure Ω}
variable (D : FiniteCellData Ω γ μ)

/-- The [binary observed table](hyp:D) has [a covariate σ-algebra contained in
the ambient σ-algebra](goal), [because its covariate map is measurable](step:1). -/
theorem FiniteCellData.sigmaX_le : D.sigmaX ≤ (inferInstance : MeasurableSpace Ω) :=
  D.measurable_X.comap_le

variable [StandardBorelSpace Ω] [IsFiniteMeasure μ]

/-- The [binary observed table](hyp:D), [conditional independence of the
potential-outcome pair and treatment](hyp:hCI), and [selected arm](hyp:d) imply
[conditional independence of treatment and that arm's potential outcome](goal),
[by measurable projection of the potential-outcome pair](step:1). -/
theorem FiniteCellData.condIndep_potential_of_pair
    (hCI : CondIndepFun D.sigmaX D.sigmaX_le
      (fun ω => (D.Y0 ω, D.Y1 ω)) D.A μ) (d : Bool) :
    CondIndepFun D.sigmaX D.sigmaX_le D.A (D.potential d) μ := by
  cases d
  · have h := hCI.symm.comp measurable_id
      (measurable_fst : Measurable (fun p : Bool × Bool => p.1))
    simpa [FiniteCellData.potential, Function.comp_def] using h
  · have h := hCI.symm.comp measurable_id
      (measurable_snd : Measurable (fun p : Bool × Bool => p.2))
    simpa [FiniteCellData.potential, Function.comp_def] using h

omit [StandardBorelSpace Ω] in
/-- The [binary observed table](hyp:D) and [treatment arm](hyp:d) imply [that
the conditional expectation of the arm indicator is the covariate-indexed
arm-probability kernel](goal), [by conditional-expectation uniqueness from the
setwise arm identity](step:1). -/
theorem FiniteCellData.condExp_arm (d : Bool) :
    μ[fun ω => armIndicator d (D.A ω) | D.sigmaX]
      =ᵐ[μ] fun ω => D.armProb d (D.X ω) := by
  have hmeas : Measurable[D.sigmaX] (fun ω => D.armProb d (D.X ω)) :=
    (D.measurable_armProb d).comp (comap_measurable D.X)
  have h := ae_eq_condExp_of_forall_setIntegral_eq D.sigmaX_le
    (D.integrable_armIndicator d)
    (fun _ _ _ => (D.integrable_armProb d).integrableOn)
    (fun s hs _ => by
      change MeasurableSet[MeasurableSpace.comap D.X inferInstance] s at hs
      rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨t, ht, rfl⟩
      exact (setIntegral_map ht (D.measurable_armProb d).aestronglyMeasurable
        D.measurable_X.aemeasurable).symm.trans (D.setIntegral_arm d t ht).symm)
    hmeas.aestronglyMeasurable
  exact h.symm

omit [StandardBorelSpace Ω] in
/-- The [binary observed table](hyp:D) and [treatment arm](hyp:d) imply [that
the conditional expectation of observed outcome times the arm indicator is the
arm-probability kernel times the arm-specific mean kernel](goal), [by
conditional-expectation uniqueness from the positive-outcome cell](step:1). -/
theorem FiniteCellData.condExp_observedProduct (d : Bool) :
    μ[fun ω => armIndicator d (D.A ω) *
      boolReal (observedY D.A D.Y0 D.Y1 ω) | D.sigmaX]
      =ᵐ[μ] fun ω => D.armProb d (D.X ω) * D.mean d (D.X ω) := by
  have hkernel : Measurable (fun x => D.armProb d x * D.mean d x) :=
    (D.measurable_armProb d).mul (D.measurable_mean d)
  have hmeas : Measurable[D.sigmaX]
      (fun ω => D.armProb d (D.X ω) * D.mean d (D.X ω)) :=
    hkernel.comp (comap_measurable D.X)
  have h := ae_eq_condExp_of_forall_setIntegral_eq D.sigmaX_le
    (D.integrable_observedProduct d)
    (fun _ _ _ => (D.integrable_product d).integrableOn)
    (fun s hs _ => by
      change MeasurableSet[MeasurableSpace.comap D.X inferInstance] s at hs
      rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨t, ht, rfl⟩
      exact (setIntegral_map ht hkernel.aestronglyMeasurable
        D.measurable_X.aemeasurable).symm.trans
          (D.setIntegral_observedProduct d t ht).symm)
    hmeas.aestronglyMeasurable
  exact h.symm

omit [StandardBorelSpace Ω] [IsFiniteMeasure μ] in
/-- The [binary observed table](hyp:D), [treatment arm](hyp:d), and [sample-space
unit](hyp:ω) imply [that the observed arm-outcome product equals the product
using the selected potential outcome](goal), [because the observed outcome
selects that arm's potential outcome whenever its indicator is nonzero](step:1). -/
theorem FiniteCellData.observedProduct_eq_potentialProduct (d : Bool) (ω : Ω) :
    armIndicator d (D.A ω) * boolReal (observedY D.A D.Y0 D.Y1 ω) =
      armIndicator d (D.A ω) * boolReal (D.potential d ω) := by
  cases d <;> cases hA : D.A ω <;>
    simp [armIndicator, observedY, FiniteCellData.potential, hA]

/-- The [binary observed table](hyp:D), [treatment arm](hyp:d), and [conditional
independence of treatment and the selected potential outcome given covariates](hyp:hCI)
imply [the conditional-expectation product factorization for the observed
arm-outcome product](goal), [by consistency of the observed selection and
conditional independence](step:1). -/
theorem FiniteCellData.condExp_product_factor (d : Bool)
    (hCI : CondIndepFun D.sigmaX D.sigmaX_le D.A (D.potential d) μ) :
    μ[fun ω => armIndicator d (D.A ω) *
      boolReal (observedY D.A D.Y0 D.Y1 ω) | D.sigmaX]
      =ᵐ[μ]
        (μ[fun ω => armIndicator d (D.A ω) | D.sigmaX]) *
        (μ[fun ω => boolReal (D.potential d ω) | D.sigmaX]) := by
  have hproduct : Integrable
      (fun ω => armIndicator d (D.A ω) * boolReal (D.potential d ω)) μ := by
    convert D.integrable_observedProduct d using 1
    funext ω
    exact (D.observedProduct_eq_potentialProduct d ω).symm
  have hpotential : Measurable (D.potential d) := by
    cases d <;> simp [FiniteCellData.potential, D.measurable_Y0, D.measurable_Y1]
  have hcongr :
      μ[fun ω => armIndicator d (D.A ω) *
        boolReal (observedY D.A D.Y0 D.Y1 ω) | D.sigmaX]
        =ᵐ[μ] μ[fun ω => armIndicator d (D.A ω) *
          boolReal (D.potential d ω) | D.sigmaX] :=
    condExp_congr_ae (Filter.Eventually.of_forall
      (fun ω => D.observedProduct_eq_potentialProduct d ω))
  exact hcongr.trans <| condExp_mul_of_condIndep (μ := μ) (m := D.sigmaX)
    D.sigmaX_le (f := D.A) (g := D.potential d)
    D.measurable_A hpotential hCI (u := armIndicator d) (v := boolReal)
    (by fun_prop) (by fun_prop) (D.integrable_armIndicator d)
    (by
      cases d with
      | false => simpa [FiniteCellData.potential] using D.integrable_potential false
      | true => simpa [FiniteCellData.potential] using D.integrable_potential true)
    hproduct

/-- The [binary observed table](hyp:D), [treatment arm](hyp:d), [conditional
independence of treatment and the selected potential outcome given covariates](hyp:hCI),
and [almost-everywhere nonzero arm probability](hyp:hpos) imply [that the
selected potential outcome's conditional mean is the observed-table mean
kernel](goal), [by cancelling the arm-probability factor](step:1). -/
theorem FiniteCellData.condExp_potential (d : Bool)
    (hCI : CondIndepFun D.sigmaX D.sigmaX_le D.A (D.potential d) μ)
    (hpos : ∀ᵐ ω ∂μ, D.armProb d (D.X ω) ≠ 0) :
    μ[fun ω => boolReal (D.potential d ω) | D.sigmaX]
      =ᵐ[μ] fun ω => D.mean d (D.X ω) := by
  filter_upwards [D.condExp_observedProduct d, D.condExp_product_factor d hCI,
    D.condExp_arm d, hpos] with ω hobs hfact harm hnonzero
  simp only [Pi.mul_apply] at hfact
  rw [harm] at hfact
  exact mul_left_cancel₀ hnonzero (hfact.symm.trans hobs)

/-- The [binary observed table](hyp:D), [arm-by-arm conditional independence](hyp:hCI),
and [almost-everywhere nonzero probabilities for both arms](hyp:hpos) imply [that
the conditional treated-minus-control potential-outcome contrast equals the
difference of the observed-table mean kernels](goal), [by conditional-expectation
linearity and the two arm-specific identities](step:1). -/
theorem FiniteCellData.condExp_treated_sub_control
    (hCI : ∀ d, CondIndepFun D.sigmaX D.sigmaX_le D.A (D.potential d) μ)
    (hpos : ∀ d, ∀ᵐ ω ∂μ, D.armProb d (D.X ω) ≠ 0) :
    μ[fun ω => boolReal (D.Y1 ω) - boolReal (D.Y0 ω) | D.sigmaX]
      =ᵐ[μ] fun ω => D.mean true (D.X ω) - D.mean false (D.X ω) := by
  have h1 : Integrable (fun ω => boolReal (D.Y1 ω)) μ := by
    simpa [FiniteCellData.potential] using D.integrable_potential true
  have h0 : Integrable (fun ω => boolReal (D.Y0 ω)) μ := by
    simpa [FiniteCellData.potential] using D.integrable_potential false
  have hsub := condExp_sub h1 h0 D.sigmaX
  have hinput :
      ((fun ω => boolReal (D.Y1 ω)) - (fun ω => boolReal (D.Y0 ω))) =
      (fun ω => boolReal (D.Y1 ω) - boolReal (D.Y0 ω)) := by
    funext ω
    rfl
  have houtput :
      ((fun ω => D.mean true (D.X ω)) - (fun ω => D.mean false (D.X ω))) =
      (fun ω => D.mean true (D.X ω) - D.mean false (D.X ω)) := by
    funext ω
    rfl
  simpa only [hinput, houtput, FiniteCellData.potential] using
    hsub.trans ((D.condExp_potential true (hCI true) (hpos true)).sub
      (D.condExp_potential false (hCI false) (hpos false)))

/-- The [binary observed table](hyp:D), [joint conditional independence of the
potential-outcome pair and treatment](hyp:hCI), and [almost-everywhere nonzero
probabilities for both arms](hyp:hpos) imply [that the conditional
treated-minus-control potential-outcome contrast equals the difference of the
observed-table mean kernels](goal), [by projecting joint independence to each arm](step:1). -/
theorem FiniteCellData.condExp_treated_sub_control_of_pair
    (hCI : CondIndepFun D.sigmaX D.sigmaX_le
      (fun ω => (D.Y0 ω, D.Y1 ω)) D.A μ)
    (hpos : ∀ d, ∀ᵐ ω ∂μ, D.armProb d (D.X ω) ≠ 0) :
    μ[fun ω => boolReal (D.Y1 ω) - boolReal (D.Y0 ω) | D.sigmaX]
      =ᵐ[μ] fun ω => D.mean true (D.X ω) - D.mean false (D.X ω) := by
  exact D.condExp_treated_sub_control (D.condIndep_potential_of_pair hCI) hpos

end Bridge
end PO
end Causalean
