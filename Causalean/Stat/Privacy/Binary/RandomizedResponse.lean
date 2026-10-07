module
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Causalean.Stat.Privacy.Binary.Density

/-!
# Binary randomized response and countable outputs

The Boolean randomized-response kernel realizes both extremal private
contrasts and attains the sharp Fisher bound. For countable measurable
outputs, the Radon–Nikodym integral becomes the usual sum over atoms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Stat.Privacy.Binary

/-- A [privacy level](hyp:ε) and [Boolean input sign](hyp:b) determine [the
probability of a positive randomized-response report](goal), equal to
[`exp ε/(exp ε + 1)` for positive input and `1/(exp ε + 1)` for negative input](step:1). -/
def responseProbability (ε : ℝ) (b : Bool) : ℝ :=
  if b then Real.exp ε / (Real.exp ε + 1)
  else 1 / (Real.exp ε + 1)

/-- A [privacy level](hyp:ε) determines [the Boolean-output randomized-response
kernel](goal), [which reports a positive sign with probability `exp ε/(exp ε + 1)` when the
input is positive and `1/(exp ε + 1)` when it is negative, and a negative sign
otherwise](step:1). -/
def randomizedResponse (ε : ℝ) : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun b =>
    Causalean.Mathlib.Probability.bernoulliBool (responseProbability ε b)

/-- At [any privacy level](hyp:ε), [binary randomized response is a Markov kernel](goal). -/
theorem randomizedResponse_markov (ε : ℝ) :
    IsMarkovKernel (randomizedResponse ε) := by
  have he : 0 < Real.exp ε := Real.exp_pos ε
  refine ⟨fun b => ?_⟩
  cases b
  · change IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliBool (1 / (Real.exp ε + 1)))
    apply Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < Real.exp ε + 1)).2
      linarith
  · change IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliBool
        (Real.exp ε / (Real.exp ε + 1)))
    apply Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < Real.exp ε + 1)).2
      linarith

/-- A [positive privacy level](hyp:hε) at [the supplied parameter](hyp:ε) makes
[binary randomized response satisfy pairwise setwise local privacy](goal). -/
theorem randomizedResponse_private (ε : ℝ) (hε : 0 < ε) :
    SetwisePrivate (randomizedResponse ε) ε := by
  intro b c s hs
  have he : 0 < Real.exp ε := Real.exp_pos ε
  have he1 : 0 < Real.exp ε + 1 := by linarith
  have hege : 1 ≤ Real.exp ε := (Real.one_lt_exp_iff.mpr hε).le
  have hcomp₁ : 1 - (Real.exp ε + 1)⁻¹ =
      Real.exp ε / (Real.exp ε + 1) := by
    rw [inv_eq_one_div]
    field_simp
    <;> ring
  have hcomp₂ : 1 - Real.exp ε / (Real.exp ε + 1) =
      (Real.exp ε + 1)⁻¹ := by
    rw [inv_eq_one_div]
    field_simp
    <;> ring
  have hself (x : ENNReal) : x ≤ ENNReal.ofReal (Real.exp ε) * x := by
    calc
      x = 1 * x := by simp
      _ ≤ ENNReal.ofReal (Real.exp ε) * x := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hege
  have hqp : ENNReal.ofReal ((Real.exp ε + 1)⁻¹) ≤
      ENNReal.ofReal (Real.exp ε) *
        ENNReal.ofReal (Real.exp ε / (Real.exp ε + 1)) := by
    rw [← ENNReal.ofReal_mul he.le]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_eq_one_div]
    apply (div_le_iff₀ he1).2
    rw [mul_assoc, div_mul_cancel₀ _ he1.ne']
    nlinarith [sq_nonneg (Real.exp ε - 1)]
  have hpq : ENNReal.ofReal (Real.exp ε / (Real.exp ε + 1)) ≤
      ENNReal.ofReal (Real.exp ε) *
        ENNReal.ofReal ((Real.exp ε + 1)⁻¹) := by
    rw [← ENNReal.ofReal_mul he.le]
    apply ENNReal.ofReal_le_ofReal
    exact (div_eq_mul_inv (Real.exp ε) (Real.exp ε + 1)).le
  change (Causalean.Mathlib.Probability.bernoulliBool
      (responseProbability ε b)) s ≤
    ENNReal.ofReal (Real.exp ε) *
      (Causalean.Mathlib.Probability.bernoulliBool
        (responseProbability ε c)) s
  cases b <;> cases c <;>
    by_cases ht : true ∈ s <;>
    by_cases hf : false ∈ s <;>
    simp [responseProbability,
      Causalean.Mathlib.Probability.bernoulliBool,
      Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
      ht, hf, hcomp₁, hcomp₂]
  all_goals first
    | exact hself _
    | exact hqp
    | exact hpq
    | rw [mul_add]; exact add_le_add (hself _) (hself _)
    | rw [mul_add]; exact add_le_add hqp hpq
    | rw [mul_add]; exact add_le_add hpq hqp

variable {Z : Type*} [MeasurableSpace Z] [Countable Z]
  [MeasurableSingletonClass Z]

/-- A [Boolean-input Markov kernel](hyp:Q), intended for a countable measurable output
alphabet, and [a sign-family parameter](hyp:τ) determine [the atomic scalar Fisher
information](goal), [given by the sum over output points of the squared difference of the two
row masses divided by four times the mixture mass `((1 + τ)·positive + (1 - τ)·negative)/2`,
with atoms whose denominator vanishes contributing zero](step:1). Equivalently each atom
contributes its squared half-difference of row masses divided by its mixture mass. -/
def discreteInformation (Q : Kernel Bool Z) (τ : ℝ) : ℝ :=
  ∑' z : Z,
    ((Q true {z}).toReal - (Q false {z}).toReal) ^ 2 /
      (2 * ((1 + τ) * (Q true {z}).toReal +
        (1 - τ) * (Q false {z}).toReal))

private theorem rowDensity_mul_atom (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (b : Bool) (z : Z) :
    (reference Q).real {z} * rowDensity Q b z = (Q b).real {z} := by
  haveI : IsFiniteMeasure (reference Q) := reference_finite Q
  have h := congrArg (fun μ : Measure Z => μ {z}) (row_eq_withDensity Q b)
  rw [withDensity_apply _ (measurableSet_singleton z)] at h
  rw [lintegral_singleton' ((measurable_rowDensity Q b).ennreal_ofReal) z] at h
  change ((reference Q) {z}).toReal * rowDensity Q b z = ((Q b) {z}).toReal
  rw [h]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (show 0 ≤ rowDensity Q b z from ENNReal.toReal_nonneg)]
  exact mul_comm _ _

private theorem integrable_contrast_fisher (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (τ : ℝ) (hτ : |τ| < 1) :
    Integrable (fun z => balancedDensity Q z * contrast Q z ^ 2 /
      (1 + τ * contrast Q z)) (reference Q) := by
  haveI : IsFiniteMeasure (reference Q) := reference_finite Q
  have ht : Integrable (rowDensity Q true) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hf : Integrable (rowDensity Q false) (reference Q) :=
    Measure.integrable_toReal_rnDeriv
  have hb : Integrable (balancedDensity Q) (reference Q) :=
    (ht.add hf).div_const 2
  apply Integrable.mono' (hb.const_mul (1 / (1 - |τ|)))
  · have hm : Measurable (balancedDensity Q) :=
      ((measurable_rowDensity Q true).add (measurable_rowDensity Q false)).div_const 2
    have hc : Measurable (contrast Q) :=
      ((measurable_rowDensity Q true).sub (measurable_rowDensity Q false)).div
        ((measurable_rowDensity Q true).add (measurable_rowDensity Q false))
    exact ((hm.mul (hc.pow_const 2)).div
      (measurable_const.add (measurable_const.mul hc))).aestronglyMeasurable
  · filter_upwards [] with z
    let a := rowDensity Q true z
    let b := rowDensity Q false z
    have ha : 0 ≤ a := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    have hbal : 0 ≤ balancedDensity Q z := by
      change 0 ≤ (a + b) / 2
      positivity
    have hδ : |contrast Q z| ≤ 1 := by
      by_cases hs : a + b = 0
      · have hza : a = 0 := by linarith
        have hzb : b = 0 := by linarith
        simp [contrast, a, b, hza, hzb]
      · have hspos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb0) (Ne.symm hs)
        change |(a - b) / (a + b)| ≤ 1
        rw [abs_div, abs_of_pos hspos]
        exact (div_le_iff₀ hspos).2 ((abs_le).2 ⟨by linarith, by linarith⟩)
    have hgap : 0 < 1 - |τ| := by linarith
    have hden : 1 - |τ| ≤ 1 + τ * contrast Q z := by
      have hmul : |τ * contrast Q z| ≤ |τ| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hδ
      have := (neg_abs_le (τ * contrast Q z))
      linarith
    have hdenpos : 0 < 1 + τ * contrast Q z := lt_of_lt_of_le hgap hden
    have hsq : contrast Q z ^ 2 ≤ 1 := by
      have := (abs_le.mp hδ)
      nlinarith [sq_nonneg (1 - contrast Q z), sq_nonneg (1 + contrast Q z)]
    have hnonneg : 0 ≤ balancedDensity Q z * contrast Q z ^ 2 /
        (1 + τ * contrast Q z) :=
      div_nonneg (mul_nonneg hbal (sq_nonneg _)) hdenpos.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    change balancedDensity Q z * contrast Q z ^ 2 /
        (1 + τ * contrast Q z) ≤
      1 / (1 - |τ|) * balancedDensity Q z
    rw [mul_comm (1 / (1 - |τ|))]
    calc
      balancedDensity Q z * contrast Q z ^ 2 /
          (1 + τ * contrast Q z) ≤ balancedDensity Q z / (1 - |τ|) := by
        apply (div_le_div_iff₀ hdenpos hgap).2
        calc
          (balancedDensity Q z * contrast Q z ^ 2) * (1 - |τ|) ≤
              balancedDensity Q z * (1 - |τ|) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa using mul_le_mul_of_nonneg_left hsq hbal) hgap.le
          _ ≤ balancedDensity Q z * (1 + τ * contrast Q z) := by gcongr
      _ = balancedDensity Q z * (1 / (1 - |τ|)) := by
        rw [div_eq_mul_inv, one_div]

/-- A [Boolean-input Markov kernel](hyp:Q) on a countable measurable output alphabet
at [an interior sign-family parameter](hyp:τ,hτ) has [Radon–Nikodym Fisher
information equal to its atomic Fisher sum](goal). -/
theorem information_eq_discrete (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (τ : ℝ) (hτ : |τ| < 1) :
    information Q τ = discreteInformation Q τ := by
  rw [information_eq_contrast_integral Q τ hτ,
    integral_countable' (integrable_contrast_fisher Q τ hτ)]
  unfold discreteInformation
  congr 1
  funext z
  let r := (reference Q).real {z}
  let a := rowDensity Q true z
  let b := rowDensity Q false z
  have hma : r * a = (Q true {z}).toReal := rowDensity_mul_atom Q true z
  have hmb : r * b = (Q false {z}).toReal := rowDensity_mul_atom Q false z
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  change r * (balancedDensity Q z * contrast Q z ^ 2 /
      (1 + τ * contrast Q z)) = _
  rw [← hma, ← hmb]
  by_cases hr0 : r = 0
  · simp [hr0]
  by_cases hs : a + b = 0
  · have hza : a = 0 := by linarith
    have hzb : b = 0 := by linarith
    simp [balancedDensity, contrast, a, b, hza, hzb]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hspos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  have hct : 0 < 1 + τ := by have := (abs_lt.mp hτ).1; linarith
  have hcf : 0 < 1 - τ := by have := (abs_lt.mp hτ).2; linarith
  have hD : 0 < (1 + τ) * a + (1 - τ) * b := by
    by_cases hza : a = 0
    · have hbpos : 0 < b := by linarith
      simpa [hza] using mul_pos hcf hbpos
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hza)
      exact add_pos_of_pos_of_nonneg (mul_pos hct hapos)
        (mul_nonneg hcf.le hb)
  have hden : 0 < 1 + τ * ((a - b) / (a + b)) := by
    have heq : 1 + τ * ((a - b) / (a + b)) =
        ((1 + τ) * a + (1 - τ) * b) / (a + b) := by
      field_simp
      <;> ring
    rw [heq]
    exact div_pos hD hspos
  change r * (((a + b) / 2) * ((a - b) / (a + b)) ^ 2 /
      (1 + τ * ((a - b) / (a + b)))) =
    (r * a - r * b) ^ 2 /
      (2 * ((1 + τ) * (r * a) + (1 - τ) * (r * b)))
  field_simp [hr0, hs, hden.ne', hD.ne']
  <;> ring

/-- A [positive privacy level](hyp:ε,hε) and [an interior sign-family
parameter](hyp:τ,hτ) make [binary randomized response attain the sharp scalar
Fisher-information bound](goal): its output Fisher information equals `c² / (1 - c² τ²)`
exactly, where `c = (exp ε - 1)/(exp ε + 1)` is the contraction parameter. -/
theorem randomizedResponse_information_eq (ε τ : ℝ)
    (hε : 0 < ε) (hτ : |τ| < 1) :
    letI : IsMarkovKernel (randomizedResponse ε) := randomizedResponse_markov ε
    information (randomizedResponse ε) τ =
      contraction ε ^ 2 / (1 - contraction ε ^ 2 * τ ^ 2) := by
  letI : IsMarkovKernel (randomizedResponse ε) := randomizedResponse_markov ε
  let e := Real.exp ε
  let p := e / (e + 1)
  let q := 1 / (e + 1)
  have he : 0 < e := Real.exp_pos ε
  have he1 : 0 < e + 1 := by linarith
  have hp : 0 < p := div_pos he he1
  have hq : 0 < q := div_pos (by norm_num) he1
  have hcq : 1 - q = p := by
    dsimp [p, q]
    field_simp
    <;> ring
  have hcp : 1 - p = q := by
    dsimp [p, q]
    field_simp
    <;> ring
  have hqi : (Real.exp ε + 1)⁻¹ = q := by
    dsimp [q, e]
    rw [one_div]
  have hmass (b z : Bool) :
      ((randomizedResponse ε b) {z}).toReal =
        if b = z then p else q := by
    change ((Causalean.Mathlib.Probability.bernoulliBool
      (responseProbability ε b)) {z}).toReal = if b = z then p else q
    cases b <;> cases z <;>
      simp [responseProbability, Causalean.Mathlib.Probability.bernoulliBool,
        Measure.add_apply, Measure.smul_apply]
    all_goals try rw [hqi]
    all_goals first
      | (change (ENNReal.ofReal (1 - q)).toReal = p
         rw [hcq, ENNReal.toReal_ofReal hp.le])
      | (change (ENNReal.ofReal q).toReal = q
         rw [ENNReal.toReal_ofReal hq.le])
      | (change (ENNReal.ofReal (1 - p)).toReal = q
         rw [hcp, ENNReal.toReal_ofReal hq.le])
      | (change (ENNReal.ofReal p).toReal = p
         rw [ENNReal.toReal_ofReal hp.le])
  rw [information_eq_discrete (randomizedResponse ε) τ hτ]
  simp only [discreteInformation, tsum_fintype]
  simp [hmass]
  have hsum : p + q = 1 := by
    dsimp [p, q]
    field_simp
    <;> ring
  have hk : contraction ε = p - q := by
    dsimp [contraction, p, q, e]
    field_simp
    <;> ring
  let d₁ := (1 + τ) * p + (1 - τ) * q
  let d₂ := (1 + τ) * q + (1 - τ) * p
  have hct : 0 < 1 + τ := by have := (abs_lt.mp hτ).1; linarith
  have hcf : 0 < 1 - τ := by have := (abs_lt.mp hτ).2; linarith
  have hd₁ : 0 < d₁ := add_pos (mul_pos hct hp) (mul_pos hcf hq)
  have hd₂ : 0 < d₂ := add_pos (mul_pos hct hq) (mul_pos hcf hp)
  have hden : d₁ * d₂ = 1 - (p - q) ^ 2 * τ ^ 2 := by
    calc
      d₁ * d₂ = (p + q) ^ 2 - (p - q) ^ 2 * τ ^ 2 := by dsimp [d₁, d₂]; ring
      _ = _ := by rw [hsum]; ring
  rw [hk]
  change (p - q) ^ 2 / (2 * d₁) + (q - p) ^ 2 / (2 * d₂) =
    (p - q) ^ 2 / (1 - (p - q) ^ 2 * τ ^ 2)
  rw [← hden]
  field_simp [hd₁.ne', hd₂.ne']
  nlinarith [hsum]

/-- A [Boolean-input Markov kernel](hyp:Q) on a countable measurable output alphabet,
[a positive privacy level](hyp:ε,hε), [an interior sign-family parameter](hyp:τ,hτ),
and [setwise local privacy](hyp:hpriv) give [the sharp atomic Fisher-information
bound](goal): the atomic Fisher information is at most `c² / (1 - c² τ²)`, where
`c = (exp ε - 1)/(exp ε + 1)` is the contraction parameter. This statement is the upper
bound only. -/
theorem discreteInformation_le_sharp (Q : Kernel Bool Z) [IsMarkovKernel Q]
    (ε τ : ℝ) (hε : 0 < ε) (hτ : |τ| < 1)
    (hpriv : SetwisePrivate Q ε) :
    discreteInformation Q τ ≤
      contraction ε ^ 2 / (1 - contraction ε ^ 2 * τ ^ 2) := by
  rw [← information_eq_discrete Q τ hτ]
  exact information_le_sharp Q ε τ hε hτ hpriv

end Causalean.Stat.Privacy.Binary
