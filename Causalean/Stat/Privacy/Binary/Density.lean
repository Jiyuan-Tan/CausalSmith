module
public import Causalean.Mathlib.Analysis.Convex.Chord
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Binary private experiments and their Radon–Nikodym densities

Two rows of an arbitrary measurable-output Boolean-input Markov kernel are
dominated by their sum. The real densities define the output law, score,
Fisher information, balanced density, and normalized contrast. Setwise local
privacy controls the contrast almost everywhere.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Stat.Privacy.Binary

variable {Z : Type*} [MeasurableSpace Z]

/-- A [Boolean-input Markov kernel](hyp:Q) at [privacy level](hyp:ε) has [setwise
local privacy](goal) when either output row gives every measurable event at most
[`exp ε` times the other row's mass](step:1). -/
def SetwisePrivate (Q : Kernel Bool Z) (ε : ℝ) : Prop :=
  ∀ b c s, MeasurableSet s → Q b s ≤ ENNReal.ofReal (Real.exp ε) * Q c s

/-- A [Boolean-input Markov kernel](hyp:Q) determines [its common row-sum
reference measure](goal), [given by the sum of its positive and negative output rows](step:1).
Here `true` denotes the positive sign. -/
def reference (Q : Kernel Bool Z) : Measure Z := Q true + Q false

/-- A [Boolean-input Markov kernel](hyp:Q), [an input sign](hyp:b), and [an output
point](hyp:z) determine [the real Radon–Nikodym density of that output row relative
to the row sum](goal), [given by its Radon–Nikodym derivative](step:1). -/
def rowDensity (Q : Kernel Bool Z) (b : Bool) (z : Z) : ℝ :=
  ((Q b).rnDeriv (reference Q) z).toReal

/-- A [privacy level](hyp:ε) determines [its binary local-privacy contraction
parameter](goal), [given by the ratio `(exp ε - 1)/(exp ε + 1)`](step:1). -/
def contraction (ε : ℝ) : ℝ :=
  (Real.exp ε - 1) / (Real.exp ε + 1)

/-- A [Boolean-input Markov kernel](hyp:Q) and [an output point](hyp:z) determine
[the balanced density](goal), [given by half the sum of the two row densities](step:1). -/
def balancedDensity (Q : Kernel Bool Z) (z : Z) : ℝ :=
  (rowDensity Q true z + rowDensity Q false z) / 2

/-- A [Boolean-input Markov kernel](hyp:Q) and [an output point](hyp:z) determine
[the normalized density contrast](goal), [given as zero where both row densities
vanish through real division](step:1). -/
def contrast (Q : Kernel Bool Z) (z : Z) : ℝ :=
  (rowDensity Q true z - rowDensity Q false z) /
    (rowDensity Q true z + rowDensity Q false z)

/-- A [Boolean-input Markov kernel](hyp:Q), [a sign-family parameter](hyp:τ), and
[an output point](hyp:z) determine [the Bernoulli-mixture output density](goal),
[given by weights `(1 + τ)/2` and `(1 - τ)/2`](step:1). -/
def mixtureDensity (Q : Kernel Bool Z) (τ : ℝ) (z : Z) : ℝ :=
  (1 + τ) / 2 * rowDensity Q true z +
    (1 - τ) / 2 * rowDensity Q false z

/-- A [Boolean-input Markov kernel](hyp:Q) and [a sign-family parameter](hyp:τ)
determine [the Bernoulli-mixture output law](goal), [given by the convex mixture of
its positive and negative rows](step:1). -/
def outputLaw (Q : Kernel Bool Z) (τ : ℝ) : Measure Z :=
  ENNReal.ofReal ((1 + τ) / 2) • Q true +
    ENNReal.ofReal ((1 - τ) / 2) • Q false

/-- A [Boolean-input Markov kernel](hyp:Q) and [an output point](hyp:z) determine
[the parameter derivative of the Bernoulli-mixture density](goal), [given by half
the difference of the two row densities](step:1). -/
def derivativeDensity (Q : Kernel Bool Z) (z : Z) : ℝ :=
  (rowDensity Q true z - rowDensity Q false z) / 2

/-- A [Boolean-input Markov kernel](hyp:Q), [a sign-family parameter](hyp:τ), and
[an output point](hyp:z) determine [the guarded likelihood score](goal), [given by
the derivative divided by positive mixture density and zero otherwise](step:1). -/
def score (Q : Kernel Bool Z) (τ : ℝ) (z : Z) : ℝ :=
  if 0 < mixtureDensity Q τ z then
    derivativeDensity Q z / mixtureDensity Q τ z
  else 0

/-- A [Boolean-input Markov kernel](hyp:Q) and [a sign-family parameter](hyp:τ)
determine [the scalar output Fisher information](goal), [given by the row-sum-reference
integral of mixture density times squared guarded score](step:1). -/
def information (Q : Kernel Bool Z) (τ : ℝ) : ℝ :=
  ∫ z, mixtureDensity Q τ z * (score Q τ z) ^ 2 ∂reference Q

/-- A [Boolean-input Markov kernel](hyp:Q) has [a finite row-sum reference
measure](goal). -/
theorem reference_finite (Q : Kernel Bool Z) [IsMarkovKernel Q] :
    IsFiniteMeasure (reference Q) := by
  unfold reference
  infer_instance

/-- A [Boolean-input Markov kernel](hyp:Q) and [an input sign](hyp:b) give [a
measurable real row density](goal) on the output σ-algebra. -/
theorem measurable_rowDensity (Q : Kernel Bool Z) (b : Bool) :
    Measurable (rowDensity Q b) := by
  exact ((Q b).measurable_rnDeriv (reference Q)).ennreal_toReal

/-- A [Boolean-input Markov kernel](hyp:Q) and [an input sign](hyp:b) give [an
output row absolutely continuous with respect to the row-sum measure](goal). -/
theorem row_ac (Q : Kernel Bool Z) (b : Bool) :
    Q b ≪ reference Q := by
  cases b
  · change Q false ≪ Q true + Q false
    exact rfl.absolutelyContinuous.add_right' _
  · change Q true ≪ Q true + Q false
    exact rfl.absolutelyContinuous.add_right _

/-- A [Boolean-input Markov kernel](hyp:Q) and [an input sign](hyp:b) make [its
Radon–Nikodym density reconstruct the corresponding output row exactly](goal),
including on zero-reference-mass sets. -/
theorem row_eq_withDensity (Q : Kernel Bool Z) [IsMarkovKernel Q] (b : Bool) :
    Q b = (reference Q).withDensity
      (fun z => ENNReal.ofReal (rowDensity Q b z)) := by
  haveI : IsFiniteMeasure (reference Q) := reference_finite Q
  haveI : IsFiniteMeasure (Q b) := inferInstance
  have h : ∀ᵐ z ∂reference Q, (Q b).rnDeriv (reference Q) z ≠ ⊤ :=
    (Q b).rnDeriv_ne_top (reference Q)
  have heq : (fun z => ENNReal.ofReal (rowDensity Q b z)) =ᵐ[reference Q]
      (Q b).rnDeriv (reference Q) := by
    filter_upwards [h] with z hz
    simp only [rowDensity, ENNReal.ofReal_toReal hz]
  rw [← Measure.withDensity_rnDeriv_eq (Q b) (reference Q) (row_ac Q b)]
  exact withDensity_congr_ae heq.symm

/-- A [Boolean-input Markov kernel](hyp:Q) and [an interior sign-family
parameter](hyp:τ,hτ) make [the Bernoulli-mixture output law equal to the measure
with its stated mixture density](goal) relative to the row-sum reference. -/
theorem outputLaw_eq_withDensity (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (τ : ℝ) (hτ : |τ| < 1) :
    outputLaw Q τ = (reference Q).withDensity
      (fun z => ENNReal.ofReal (mixtureDensity Q τ z)) := by
  have hp : 0 ≤ (1 + τ) / 2 := by have := (abs_lt.mp hτ).1; linarith
  have hm : 0 ≤ (1 - τ) / 2 := by have := (abs_lt.mp hτ).2; linarith
  have hpoint : (fun z => ENNReal.ofReal (mixtureDensity Q τ z)) =
      (fun z => ENNReal.ofReal ((1 + τ) / 2) • ENNReal.ofReal (rowDensity Q true z) +
        ENNReal.ofReal ((1 - τ) / 2) • ENNReal.ofReal (rowDensity Q false z)) := by
    funext z
    have ht : 0 ≤ rowDensity Q true z := ENNReal.toReal_nonneg
    have hf : 0 ≤ rowDensity Q false z := ENNReal.toReal_nonneg
    dsimp [mixtureDensity]
    rw [ENNReal.ofReal_add (mul_nonneg hp ht) (mul_nonneg hm hf), ENNReal.ofReal_mul hp,
      ENNReal.ofReal_mul hm]
  rw [outputLaw, row_eq_withDensity Q true, row_eq_withDensity Q false, hpoint]
  rw [← withDensity_smul _ (measurable_rowDensity Q true).ennreal_ofReal,
    ← withDensity_smul _ (measurable_rowDensity Q false).ennreal_ofReal]
  exact (withDensity_add_left
    ((measurable_rowDensity Q true).ennreal_ofReal.const_smul _)
      (fun z => ENNReal.ofReal ((1 - τ) / 2) • ENNReal.ofReal (rowDensity Q false z))).symm

/-- A [Boolean-input Markov kernel](hyp:Q), [a sign-family parameter](hyp:τ), and
[an output point](hyp:z) make [the Bernoulli-mixture density differentiable with
the stated row-difference derivative](goal). -/
theorem hasDerivAt_mixtureDensity (Q : Kernel Bool Z) (τ : ℝ) (z : Z) :
    HasDerivAt (fun t => mixtureDensity Q t z) (derivativeDensity Q z) τ := by
  have h := ((hasDerivAt_id τ).add_const 1 |>.div_const 2 |>.mul_const
    (rowDensity Q true z)).add
      (((hasDerivAt_const τ 1).sub (hasDerivAt_id τ) |>.div_const 2).mul_const
        (rowDensity Q false z))
  have hfun : (fun t => mixtureDensity Q t z) =
      (fun t => (t + 1) / 2 * rowDensity Q true z) +
        (fun t => (1 - t) / 2 * rowDensity Q false z) := by
    funext t
    dsimp [mixtureDensity]
    ring
  have hder : derivativeDensity Q z =
      1 / 2 * rowDensity Q true z + (0 - 1) / 2 * rowDensity Q false z := by
    dsimp [derivativeDensity]
    ring
  rw [hfun, hder]
  exact h

/-- A [Boolean-input Markov kernel](hyp:Q), [a privacy level](hyp:ε), and [setwise
local privacy](hyp:hpriv) make [the two Radon–Nikodym row densities satisfy the
corresponding privacy inequalities almost everywhere](goal) under their common
reference measure. -/
theorem ae_density_private (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (ε : ℝ) (hpriv : SetwisePrivate Q ε) :
    ∀ᵐ z ∂reference Q,
      rowDensity Q true z ≤ Real.exp ε * rowDensity Q false z ∧
      rowDensity Q false z ≤ Real.exp ε * rowDensity Q true z := by
  haveI : IsFiniteMeasure (reference Q) := reference_finite Q
  have hpair (b c : Bool) :
      ∀ᵐ z ∂reference Q,
        rowDensity Q b z ≤ Real.exp ε * rowDensity Q c z := by
    have hle : (Q b).rnDeriv (reference Q) ≤ᵐ[reference Q]
        fun z => ENNReal.ofReal (Real.exp ε) * (Q c).rnDeriv (reference Q) z := by
      apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
        ((Q b).measurable_rnDeriv (reference Q))
      intro s hs _
      rw [lintegral_const_mul _ ((Q c).measurable_rnDeriv (reference Q))]
      have hb := Measure.withDensity_rnDeriv_eq (Q b) (reference Q) (row_ac Q b)
      have hc := Measure.withDensity_rnDeriv_eq (Q c) (reference Q) (row_ac Q c)
      rw [← withDensity_apply ((Q b).rnDeriv (reference Q)) hs, hb,
        ← withDensity_apply ((Q c).rnDeriv (reference Q)) hs, hc]
      exact hpriv b c s hs
    filter_upwards [hle, (Q c).rnDeriv_ne_top (reference Q)] with z hz hzc
    rw [← ENNReal.ofReal_toReal hzc,
      ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos ε))] at hz
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (le_of_lt (Real.exp_pos ε)) ENNReal.toReal_nonneg) hz
  filter_upwards [hpair true false, hpair false true] with z h₁ h₂
  exact ⟨h₁, h₂⟩

/-- A [Boolean-input Markov kernel](hyp:Q) has [balanced density with unit integral
under its row-sum reference measure](goal). -/
theorem integral_balancedDensity (Q : Kernel Bool Z) [IsMarkovKernel Q] :
    ∫ z, balancedDensity Q z ∂reference Q = 1 := by
  haveI : IsFiniteMeasure (reference Q) := reference_finite Q
  have ht : Integrable (rowDensity Q true) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hf : Integrable (rowDensity Q false) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hrow (b : Bool) : ∫ z, rowDensity Q b z ∂reference Q = 1 := by
    change (∫ z, ((Q b).rnDeriv (reference Q) z).toReal ∂reference Q) = 1
    rw [Measure.integral_toReal_rnDeriv (row_ac Q b)]
    simp [measureReal_def]
  simp only [balancedDensity, integral_div, integral_add ht hf, hrow]
  norm_num

/-- A [Boolean-input Markov kernel](hyp:Q) has [balanced density times normalized
contrast with mean zero under its row-sum reference measure](goal). -/
theorem integral_balanced_contrast (Q : Kernel Bool Z) [IsMarkovKernel Q] :
    ∫ z, balancedDensity Q z * contrast Q z ∂reference Q = 0 := by
  haveI : IsFiniteMeasure (reference Q) := reference_finite Q
  have ht : Integrable (rowDensity Q true) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hf : Integrable (rowDensity Q false) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hpoint (z : Z) : balancedDensity Q z * contrast Q z =
      derivativeDensity Q z := by
    let a := rowDensity Q true z
    let b := rowDensity Q false z
    have ha : 0 ≤ a := ENNReal.toReal_nonneg
    have hb : 0 ≤ b := ENNReal.toReal_nonneg
    by_cases hs : a + b = 0
    · have hza : a = 0 := by linarith
      have hzb : b = 0 := by linarith
      simp [balancedDensity, contrast, derivativeDensity, a, b, hza, hzb]
    · dsimp [balancedDensity, contrast, derivativeDensity]
      change (a + b) / 2 * ((a - b) / (a + b)) = (a - b) / 2
      field_simp
  rw [show (fun z => balancedDensity Q z * contrast Q z) = derivativeDensity Q from
    funext hpoint]
  have hrow (b : Bool) : ∫ z, rowDensity Q b z ∂reference Q = 1 := by
    change (∫ z, ((Q b).rnDeriv (reference Q) z).toReal ∂reference Q) = 1
    rw [Measure.integral_toReal_rnDeriv (row_ac Q b)]
    simp [measureReal_def]
  change (∫ z, (rowDensity Q true z - rowDensity Q false z) / 2 ∂reference Q) = 0
  simp only [integral_div, integral_sub ht hf, hrow]
  norm_num

/-- A [positive privacy level](hyp:hε) at [the supplied privacy parameter](hyp:ε)
has [a contraction parameter in the half-open unit interval](goal). -/
theorem contraction_mem (ε : ℝ) (hε : 0 < ε) :
    0 ≤ contraction ε ∧ contraction ε < 1 := by
  have he : 1 < Real.exp ε := (Real.one_lt_exp_iff).2 hε
  unfold contraction
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · exact (div_lt_one (by linarith)).2 (by linarith)

/-- A [Boolean-input Markov kernel](hyp:Q), [a positive privacy level](hyp:ε,hε),
and [setwise local privacy](hyp:hpriv) make [the absolute normalized row contrast
almost everywhere bounded by the sharp contraction parameter](goal). -/
theorem ae_abs_contrast_le (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (ε : ℝ) (hε : 0 < ε) (hpriv : SetwisePrivate Q ε) :
    ∀ᵐ z ∂reference Q, |contrast Q z| ≤ contraction ε := by
  have hk := (contraction_mem ε hε).1
  have he : 1 < Real.exp ε := (Real.one_lt_exp_iff).2 hε
  filter_upwards [ae_density_private Q ε hpriv] with z hz
  let a := rowDensity Q true z
  let b := rowDensity Q false z
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  by_cases hs : a + b = 0
  · have hza : a = 0 := by linarith
    have hzb : b = 0 := by linarith
    simpa [contrast, a, b, hza, hzb] using hk
  · have hspos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
    have hnum : |a - b| * (Real.exp ε + 1) ≤
        (Real.exp ε - 1) * (a + b) := by
      calc
        |a - b| * (Real.exp ε + 1) = |(a - b) * (Real.exp ε + 1)| := by
          rw [abs_mul, abs_of_pos (show 0 < Real.exp ε + 1 by linarith)]
        _ ≤ (Real.exp ε - 1) * (a + b) :=
          (abs_le).2 ⟨by nlinarith [hz.2], by nlinarith [hz.1]⟩
    change |(a - b) / (a + b)| ≤ (Real.exp ε - 1) / (Real.exp ε + 1)
    rw [abs_div, abs_of_pos hspos]
    exact (div_le_div_iff₀ hspos (by linarith)).2 hnum

/-- A [Boolean-input Markov kernel](hyp:Q) at [a sign-family parameter](hyp:τ) has
[the same Fisher information as the guarded likelihood-score API](goal) when that
API is supplied the Bernoulli-mixture density and its derivative. -/
theorem information_eq_causalean_fisher (Q : Kernel Bool Z) (τ : ℝ) :
    information Q τ =
      Causalean.Stat.Minimax.ObservationDependentVanTrees.fisherInformation
        (reference Q) (mixtureDensity Q)
        (fun _ z => derivativeDensity Q z) τ := by
  rfl

/-- A [Boolean-input Markov kernel](hyp:Q) at [an interior sign-family
parameter](hyp:τ,hτ) has [Fisher information equal to the balanced-density
contrast integral](goal), including zero-density outputs. -/
theorem information_eq_contrast_integral (Q : Kernel Bool Z)
    [IsMarkovKernel Q] (τ : ℝ) (hτ : |τ| < 1) :
    information Q τ =
      ∫ z, balancedDensity Q z * contrast Q z ^ 2 /
        (1 + τ * contrast Q z) ∂reference Q := by
  change (∫ z, mixtureDensity Q τ z * score Q τ z ^ 2 ∂reference Q) = _
  congr 1
  funext z
  let a := rowDensity Q true z
  let b := rowDensity Q false z
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  by_cases hs : a + b = 0
  · have hza : a = 0 := by linarith
    have hzb : b = 0 := by linarith
    simp [mixtureDensity, score, derivativeDensity, balancedDensity, contrast,
      a, b, hza, hzb]
  · have hspos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
    have hd : |(a - b) / (a + b)| ≤ 1 := by
      rw [abs_div, abs_of_pos hspos]
      apply (div_le_iff₀ hspos).2
      have habs : |a - b| ≤ a + b := (abs_le).2 ⟨by linarith, by linarith⟩
      simpa using habs
    have htd : |τ * ((a - b) / (a + b))| < 1 := by
      rw [abs_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hτ))
        (abs_nonneg ((a - b) / (a + b)))]
    have hfactor : 0 < 1 + τ * ((a - b) / (a + b)) := by
      have := (abs_lt.mp htd).1
      linarith
    have hmix : mixtureDensity Q τ z =
        (a + b) / 2 * (1 + τ * ((a - b) / (a + b))) := by
      change (1 + τ) / 2 * a + (1 - τ) / 2 * b = _
      field_simp [hs]
      ring
    have hmixpos : 0 < mixtureDensity Q τ z := by
      rw [hmix]
      exact mul_pos (by linarith) hfactor
    simp only [score, if_pos hmixpos, balancedDensity, contrast,
      derivativeDensity]
    change mixtureDensity Q τ z * (((a - b) / 2) / mixtureDensity Q τ z) ^ 2 =
      (a + b) / 2 * ((a - b) / (a + b)) ^ 2 /
        (1 + τ * ((a - b) / (a + b)))
    rw [hmix]
    field_simp

/-- A [Boolean-input Markov kernel](hyp:Q), [a positive privacy level](hyp:ε,hε),
[an interior sign-family parameter](hyp:τ,hτ), and [setwise local privacy](hyp:hpriv)
give [a scalar output Fisher-information bound equal to the randomized-response
value](goal). -/
theorem information_le_sharp (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (ε τ : ℝ) (hε : 0 < ε) (hτ : |τ| < 1)
    (hpriv : SetwisePrivate Q ε) :
    information Q τ ≤
      contraction ε ^ 2 / (1 - contraction ε ^ 2 * τ ^ 2) := by
  haveI : IsFiniteMeasure (reference Q) := reference_finite Q
  have hk0 := (contraction_mem ε hε).1
  have hk1 := (contraction_mem ε hε).2
  have hδ := ae_abs_contrast_le Q ε hε hpriv
  have ht : Integrable (rowDensity Q true) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hf : Integrable (rowDensity Q false) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hbal : Integrable (balancedDensity Q) (reference Q) := by
    unfold balancedDensity
    exact (ht.add hf).div_const 2
  have hbc : Integrable (fun z => balancedDensity Q z * contrast Q z)
      (reference Q) := by
    apply Integrable.mono' (hbal.mul_const (contraction ε))
    · exact ((measurable_rowDensity Q true).add
        (measurable_rowDensity Q false)).div_const 2 |>.mul
          (((measurable_rowDensity Q true).sub
            (measurable_rowDensity Q false)).div
            ((measurable_rowDensity Q true).add
              (measurable_rowDensity Q false))) |>.aestronglyMeasurable
    · filter_upwards [hδ] with z hz
      have hb : 0 ≤ balancedDensity Q z := by
        unfold balancedDensity
        exact div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
          (by norm_num)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb]
      exact mul_le_mul_of_nonneg_left hz hb
  let C := contraction ε ^ 2 / (1 - contraction ε ^ 2 * τ ^ 2)
  have hright : Integrable (fun z => C *
      (balancedDensity Q z - τ * (balancedDensity Q z * contrast Q z)))
      (reference Q) := by
    exact (hbal.sub (hbc.const_mul τ)).const_mul C
  rw [information_eq_contrast_integral Q τ hτ]
  have hmain :
      (∫ z, balancedDensity Q z * contrast Q z ^ 2 /
        (1 + τ * contrast Q z) ∂reference Q) ≤
      ∫ z, C * (balancedDensity Q z -
        τ * (balancedDensity Q z * contrast Q z)) ∂reference Q := by
    apply integral_mono_of_nonneg
    · filter_upwards [hδ] with z hz
      have hb : 0 ≤ balancedDensity Q z := by
        unfold balancedDensity
        exact div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
          (by norm_num)
      have htd : |τ * contrast Q z| < 1 := by
        rw [abs_mul]
        nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hτ))
          (abs_nonneg (contrast Q z))]
      have hden : 0 < 1 + τ * contrast Q z := by
        have := (abs_lt.mp htd).1
        linarith
      exact div_nonneg (mul_nonneg hb (sq_nonneg _)) (le_of_lt hden)
    · exact hright
    · filter_upwards [hδ] with z hz
      have hb : 0 ≤ balancedDensity Q z := by
        unfold balancedDensity
        exact div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
          (by norm_num)
      have hc := Causalean.Mathlib.Analysis.Convex.contrast_chord
        (contraction ε) τ (contrast Q z) hk0 hk1 hτ hz
      have := mul_le_mul_of_nonneg_left hc hb
      dsimp [C]
      convert this using 1 <;> ring
  calc
    (∫ z, balancedDensity Q z * contrast Q z ^ 2 /
        (1 + τ * contrast Q z) ∂reference Q) ≤
        ∫ z, C * (balancedDensity Q z -
          τ * (balancedDensity Q z * contrast Q z)) ∂reference Q := hmain
    _ = C := by
      rw [integral_const_mul, integral_sub hbal (hbc.const_mul τ),
        integral_const_mul, integral_balancedDensity Q,
        integral_balanced_contrast Q]
      ring
    _ = _ := rfl

end Causalean.Stat.Privacy.Binary
