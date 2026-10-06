module
public import Causalean.Stat.Coupling.AtomicTransport

/-!
# CDF gaps and the Kantorovich--Rubinstein potential of finite atomic laws

This module defines the cumulative distribution function of a finite atomic law, the CDF gap of
two laws, the cut-crossing quantities of a transport plan, and the CDF-sign potential.  It proves
that the integrated absolute CDF gap is dominated by every transport cost, and the finite-atomic
integration-by-parts identity expressing the expectation contrast of the CDF-sign potential
through the CDF gap.
-/

@[expose] public section

namespace Causalean.Stat.Coupling

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace AtomicLaw

/-- The cumulative distribution function of a finite atomic representation. -/
noncomputable def cdf {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) (x : ℝ) : ℝ :=
  ∑ i, if μ.atom i ≤ x then μ.weight i else 0

/-- The pointwise difference of the two finite atomic cumulative distribution functions. -/
noncomputable def cdfGap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : ℝ :=
  μ.cdf x - ν.cdf x

/-- The signed amount of a transport plan crossing the cut at `x`, counted positively from the
left side of the cut to the right side and negatively in the reverse direction. -/
noncomputable def signedCrossing {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) (x : ℝ) : ℝ :=
  ∑ i, ∑ j, π.mass i j *
    (if μ.atom i ≤ x ∧ x < ν.atom j then 1
      else if ν.atom j ≤ x ∧ x < μ.atom i then -1 else 0)

/-- The unsigned amount of a transport plan crossing the cut at `x`, counting transport in both
directions. -/
noncomputable def crossingEnvelope {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) (x : ℝ) : ℝ :=
  ∑ i, ∑ j, π.mass i j *
    (if μ.atom i ≤ x ∧ x < ν.atom j ∨ ν.atom j ≤ x ∧ x < μ.atom i then 1 else 0)

/-- A transport plan has no counterflow when, at every real cut, mass crosses in at most one of
the two possible directions. -/
def CutMonotone {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) : Prop :=
  ∀ x,
    (∑ i, ∑ j, if μ.atom i ≤ x ∧ x < ν.atom j then π.mass i j else 0) = 0 ∨
    (∑ i, ∑ j, if ν.atom j ≤ x ∧ x < μ.atom i then π.mass i j else 0) = 0

/-- The sign selector used to build an attaining Kantorovich--Rubinstein potential. -/
noncomputable def cdfSign {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : ℝ :=
  if 0 < cdfGap μ ν x then 1 else if cdfGap μ ν x < 0 then -1 else 0

private theorem measurable_cdf {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) :
    Measurable μ.cdf := by
  classical
  unfold cdf
  change Measurable (fun x => ∑ i : ι,
    if μ.atom i ≤ x then μ.weight i else 0)
  apply Finset.measurable_sum Finset.univ
  intro i hi
  exact Measurable.ite
    (show MeasurableSet (Ici (μ.atom i)) from measurableSet_Ici)
    measurable_const measurable_const

private theorem measurable_cdfSign {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : Measurable (cdfSign μ ν) := by
  classical
  unfold cdfSign cdfGap
  have hgap : Measurable fun x => μ.cdf x - ν.cdf x :=
    (measurable_cdf μ).sub (measurable_cdf ν)
  exact Measurable.ite (measurableSet_Ioi.preimage hgap) measurable_const
    (Measurable.ite (measurableSet_Iio.preimage hgap) measurable_const measurable_const)

private theorem abs_cdfSign_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : |cdfSign μ ν x| ≤ 1 := by
  unfold cdfSign
  split_ifs <;> norm_num

private theorem cdfSign_intervalIntegrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (a b : ℝ) :
    IntervalIntegrable (cdfSign μ ν) volume a b := by
  rw [intervalIntegrable_iff']
  apply volume.integrableOn_of_bounded (ne_of_lt isCompact_uIcc.measure_lt_top)
  · exact (measurable_cdfSign μ ν).aestronglyMeasurable
  · filter_upwards with x
    simpa [Real.norm_eq_abs] using abs_cdfSign_le_one μ ν x

/-- The piecewise-linear primitive of the sign of the finite atomic CDF difference. -/
noncomputable def krPotential {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, cdfSign μ ν t

/-- The CDF-sign potential is one-Lipschitz. -/
theorem krPotential_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : LipschitzWith 1 (krPotential μ ν) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  change |(∫ t in (0 : ℝ)..x, cdfSign μ ν t) -
    ∫ t in (0 : ℝ)..y, cdfSign μ ν t| ≤ (1 : ℝ) * |x - y|
  rw [
    intervalIntegral.integral_interval_sub_left
      (cdfSign_intervalIntegrable μ ν 0 x) (cdfSign_intervalIntegrable μ ν 0 y)]
  simpa [Real.norm_eq_abs, abs_sub_comm] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => by simpa [Real.norm_eq_abs] using abs_cdfSign_le_one μ ν t) :
      ‖∫ t in y..x, cdfSign μ ν t‖ ≤ (1 : ℝ) * |x - y|)

/-- The canonical CDF-sign potential is normalized to vanish at zero. -/
@[simp] theorem krPotential_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : krPotential μ ν 0 = 0 := by
  simp [krPotential]

/-- The finite-sum CDF of a valid atomic representation is the real mass of the corresponding
closed lower ray under its represented measure. -/
theorem cdf_eq_toMeasure_Iic {ι : Type*} [Fintype ι]
    (μ : AtomicLaw ι) (hμ : μ.Valid) (x : ℝ) :
    μ.cdf x = (μ.toMeasure (Iic x)).toReal := by
  /- Expand the finite sum measure, evaluate each Dirac mass on `Iic x`, and use
  `ENNReal.toReal_ofReal` with `hμ.1`. -/
  classical
  simp only [cdf, toMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iic,
    Set.indicator_apply, Pi.one_apply]
  rw [ENNReal.toReal_sum (by
    intro i hi
    split_ifs <;> simp [ENNReal.ofReal_ne_top])]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hix : μ.atom i ≤ x
  · simp [hix, ENNReal.toReal_ofReal (hμ.1 i)]
  · simp [hix]

/-- Valid finite atomic representations of the same measure have identical CDFs, even when their
slot types and labellings are unrelated. -/
theorem cdf_eq_of_toMeasure_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid)
    (h : μ.toMeasure = ν.toMeasure) : μ.cdf = ν.cdf := by
  funext x
  rw [cdf_eq_toMeasure_Iic μ hμ x, cdf_eq_toMeasure_Iic ν hν x, h]

private noncomputable def cutIndicator (a b x : ℝ) : ℝ :=
  if a ≤ x ∧ x < b then 1 else 0

private theorem cutIndicator_eq_indicator (a b : ℝ) :
    cutIndicator a b = (Ico a b).indicator (1 : ℝ → ℝ) := by
  funext x
  simp [cutIndicator, Set.indicator_apply, Set.mem_Ico]

private theorem cutIndicator_integrable (a b : ℝ) :
    Integrable (cutIndicator a b) volume := by
  rw [cutIndicator_eq_indicator]
  exact (integrableOn_const (μ := volume) (s := Ico a b) (by simp)).integrable_indicator
    measurableSet_Ico

private theorem integral_cutIndicator (a b : ℝ) :
    (∫ x, cutIndicator a b x) = max (b - a) 0 := by
  rw [cutIndicator_eq_indicator, integral_indicator_one measurableSet_Ico,
    Real.volume_real_Ico]

private theorem signedCut_eq (a b x : ℝ) :
    (if a ≤ x ∧ x < b then (1 : ℝ)
      else if b ≤ x ∧ x < a then -1 else 0) =
      cutIndicator a b x - cutIndicator b a x := by
  unfold cutIndicator
  split_ifs with h₁ h₂ h₃ h₄ <;> simp_all <;> linarith

private theorem unsignedCut_eq (a b x : ℝ) :
    (if a ≤ x ∧ x < b ∨ b ≤ x ∧ x < a then (1 : ℝ) else 0) =
      cutIndicator a b x + cutIndicator b a x := by
  unfold cutIndicator
  split_ifs with h₁ h₂ h₃ <;> simp_all <;> linarith

private theorem signedPair_integrable (m a b : ℝ) :
    Integrable (fun x => m *
      (if a ≤ x ∧ x < b then (1 : ℝ)
        else if b ≤ x ∧ x < a then -1 else 0)) volume := by
  simp_rw [signedCut_eq]
  exact ((cutIndicator_integrable a b).sub (cutIndicator_integrable b a)).const_mul m

private theorem unsignedPair_integrable (m a b : ℝ) :
    Integrable (fun x => m *
      (if a ≤ x ∧ x < b ∨ b ≤ x ∧ x < a then (1 : ℝ) else 0)) volume := by
  simp_rw [unsignedCut_eq]
  exact ((cutIndicator_integrable a b).add (cutIndicator_integrable b a)).const_mul m

/-- For every transport plan, the CDF difference at a cut is exactly its signed crossing mass at
that cut. -/
theorem cdfGap_eq_signedCrossing {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) (x : ℝ) :
    cdfGap μ ν x = signedCrossing π x := by
  /- Expand both marginals, distribute their finite sums, and partition each pair of atoms by
  its position relative to `x`.  This is purely finite algebra and uses no validity premise. -/
  classical
  unfold cdfGap cdf signedCrossing
  calc
    (∑ i, if μ.atom i ≤ x then μ.weight i else 0) -
        (∑ j, if ν.atom j ≤ x then ν.weight j else 0) =
        (∑ i, ∑ j, if μ.atom i ≤ x then π.mass i j else 0) -
          (∑ j, ∑ i, if ν.atom j ≤ x then π.mass i j else 0) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [← π.fst_marginal i]
        by_cases hix : μ.atom i ≤ x <;> simp [hix]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [← π.snd_marginal j]
        by_cases hjx : ν.atom j ≤ x <;> simp [hjx]
    _ = ∑ i, ∑ j, π.mass i j *
          (if μ.atom i ≤ x ∧ x < ν.atom j then 1
            else if ν.atom j ≤ x ∧ x < μ.atom i then -1 else 0) := by
      rw [Finset.sum_comm (f := fun j i =>
        if ν.atom j ≤ x then π.mass i j else 0),
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hix : μ.atom i ≤ x
      · by_cases hjx : ν.atom j ≤ x
        · simp [hix, hjx, not_lt_of_ge hix, not_lt_of_ge hjx]
        · have hxj : x < ν.atom j := lt_of_not_ge hjx
          simp [hix, hjx, hxj]
      · have hxi : x < μ.atom i := lt_of_not_ge hix
        by_cases hjx : ν.atom j ≤ x
        · simp [hix, hjx, hxi]
        · simp [hix, hjx]

/-- Pointwise triangle inequality for cut flow integrates to domination by the unsigned crossing
envelope. -/
theorem integral_abs_cdfGap_le_integral_crossingEnvelope {ι κ : Type*}
    [Fintype ι] [Fintype κ] {μ : AtomicLaw ι} {ν : AtomicLaw κ}
    (π : TransportPlan μ ν) :
    (∫ x, |cdfGap μ ν x|) ≤ ∫ x, crossingEnvelope π x := by
  /- Use `cdfGap_eq_signedCrossing`, the nonnegativity of plan masses, and finite-sum
  integrability of half-open interval indicators. -/
  classical
  have hsigned : Integrable (signedCrossing π) volume := by
    unfold signedCrossing
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact signedPair_integrable (π.mass i j) (μ.atom i) (ν.atom j)
  have hgap : Integrable (cdfGap μ ν) volume := by
    rw [show cdfGap μ ν = signedCrossing π from
      funext fun x => cdfGap_eq_signedCrossing π x]
    exact hsigned
  have henvelope : Integrable (crossingEnvelope π) volume := by
    unfold crossingEnvelope
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact unsignedPair_integrable (π.mass i j) (μ.atom i) (ν.atom j)
  apply integral_mono hgap.abs henvelope
  intro x
  change |cdfGap μ ν x| ≤ crossingEnvelope π x
  rw [cdfGap_eq_signedCrossing π x]
  unfold signedCrossing crossingEnvelope
  calc
    |∑ i, ∑ j, π.mass i j *
        (if μ.atom i ≤ x ∧ x < ν.atom j then 1
          else if ν.atom j ≤ x ∧ x < μ.atom i then -1 else 0)| ≤
        ∑ i, |∑ j, π.mass i j *
          (if μ.atom i ≤ x ∧ x < ν.atom j then 1
            else if ν.atom j ≤ x ∧ x < μ.atom i then -1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |π.mass i j *
          (if μ.atom i ≤ x ∧ x < ν.atom j then 1
            else if ν.atom j ≤ x ∧ x < μ.atom i then -1 else 0)| := by
      exact Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, π.mass i j *
          (if μ.atom i ≤ x ∧ x < ν.atom j ∨
            ν.atom j ≤ x ∧ x < μ.atom i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (π.nonneg i j)]
      split_ifs with h₁ h₂ h₃ <;> simp_all [π.nonneg i j]

/-- The integral of the unsigned crossing envelope is exactly the absolute-distance cost of the
transport plan. -/
theorem integral_crossingEnvelope_eq_transportCost {ι κ : Type*}
    [Fintype ι] [Fintype κ] {μ : AtomicLaw ι} {ν : AtomicLaw κ}
    (π : TransportPlan μ ν) :
    (∫ x, crossingEnvelope π x) = transportCost π := by
  /- Swap the finite sums with the integral.  Each half-open interval indicator has Lebesgue
  integral equal to the distance between its two endpoints. -/
  classical
  unfold crossingEnvelope transportCost
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j hj
      simp_rw [unsignedCut_eq]
      rw [integral_const_mul,
        integral_add (cutIndicator_integrable (μ.atom i) (ν.atom j))
          (cutIndicator_integrable (ν.atom j) (μ.atom i)),
        integral_cutIndicator, integral_cutIndicator]
      by_cases hij : μ.atom i ≤ ν.atom j
      · rw [abs_of_nonpos (sub_nonpos.mpr hij)]
        simp [hij]
      · have hji : ν.atom j ≤ μ.atom i := le_of_not_ge hij
        rw [abs_of_nonneg (sub_nonneg.mpr hji)]
        simp [hij, hji]
    · intro j hj
      exact unsignedPair_integrable (π.mass i j) (μ.atom i) (ν.atom j)
  · intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact unsignedPair_integrable (π.mass i j) (μ.atom i) (ν.atom j)

/-- [Two finite atomic laws with finite slot types](hyp:ι,κ,μ,ν), [valid probability weights](hyp:hμ,hν), and [any transport plan between them](hyp:π) satisfy [the lower bound of transport cost by integrated absolute CDF gap](goal). -/
theorem integral_abs_cdfGap_le_transportCost {ι κ : Type*}
    [Fintype ι] [Fintype κ] {μ : AtomicLaw ι} {ν : AtomicLaw κ}
    (hμ : μ.Valid) (hν : ν.Valid) (π : TransportPlan μ ν) :
    (∫ x, |cdfGap μ ν x|) ≤ transportCost π := by
  rw [← integral_crossingEnvelope_eq_transportCost π]
  exact integral_abs_cdfGap_le_integral_crossingEnvelope π

private theorem cdfSign_mul_cutIndicator_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (a b : ℝ) :
    Integrable (fun x => cdfSign μ ν x * cutIndicator a b x) volume := by
  by_cases hab : a ≤ b
  · have hOn : IntegrableOn (cdfSign μ ν) (Ico a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp
        (cdfSign_intervalIntegrable μ ν a b)
    have hIndicator := hOn.integrable_indicator measurableSet_Ico
    have hfun : (fun x => cdfSign μ ν x * cutIndicator a b x) =
        (Ico a b).indicator (cdfSign μ ν) := by
      funext x
      rw [cutIndicator_eq_indicator]
      simp [Set.indicator_apply]
    rw [hfun]
    exact hIndicator
  · have hzero : cutIndicator a b = 0 := by
      funext x
      unfold cutIndicator
      split_ifs with hx
      · exact (hab (hx.1.trans hx.2.le)).elim
      · rfl
    simp [hzero]

private theorem cdfSign_mul_signedCut_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (a b : ℝ) :
    Integrable (fun x => cdfSign μ ν x *
      (if a ≤ x ∧ x < b then (1 : ℝ)
        else if b ≤ x ∧ x < a then -1 else 0)) volume := by
  have h := (cdfSign_mul_cutIndicator_integrable μ ν a b).sub
    (cdfSign_mul_cutIndicator_integrable μ ν b a)
  have hfun : (fun x => cdfSign μ ν x *
      (if a ≤ x ∧ x < b then (1 : ℝ)
        else if b ≤ x ∧ x < a then -1 else 0)) =
      (fun x => cdfSign μ ν x * cutIndicator a b x) -
        fun x => cdfSign μ ν x * cutIndicator b a x := by
    funext x
    rw [signedCut_eq]
    simp only [Pi.sub_apply]
    ring
  rw [hfun]
  exact h

private theorem intervalIntegral_cdfSign_eq_integral_mul_signedCut
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (a : ℝ) :
    (∫ t in (0 : ℝ)..a, cdfSign μ ν t) =
      ∫ t, cdfSign μ ν t *
        (if 0 ≤ t ∧ t < a then (1 : ℝ)
          else if a ≤ t ∧ t < 0 then -1 else 0) := by
  by_cases ha : 0 ≤ a
  · rw [intervalIntegral.integral_of_le ha, ← integral_Ico_eq_integral_Ioc,
      ← integral_indicator measurableSet_Ico]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 ≤ x ∧ x < a
    · simp [hx]
    · have hback : ¬(a ≤ x ∧ x < 0) := by
        rintro ⟨hax, hx0⟩
        linarith
      simp [hx, hback]
  · have ha0 : a ≤ 0 := le_of_not_ge ha
    rw [intervalIntegral.integral_of_ge ha0, ← integral_Ico_eq_integral_Ioc,
      ← integral_indicator measurableSet_Ico, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : a ≤ x ∧ x < 0
    · have hfront : ¬(0 ≤ x ∧ x < a) := by
        rintro ⟨hx0, hxa⟩
        linarith
      simp [hx, hfront]
    · have hfront : ¬(0 ≤ x ∧ x < a) := by
        rintro ⟨hx0, hxa⟩
        exact ha (hx0.trans hxa.le)
      simp [hx, hfront]

private theorem weighted_signedCut_sum_eq
    {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) (hμ : μ.Valid) (x : ℝ) :
    (∑ i, μ.weight i *
      (if 0 ≤ x ∧ x < μ.atom i then (1 : ℝ)
        else if μ.atom i ≤ x ∧ x < 0 then -1 else 0)) =
      if 0 ≤ x then 1 - μ.cdf x else -μ.cdf x := by
  classical
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    calc
      (∑ i, μ.weight i *
          (if 0 ≤ x ∧ x < μ.atom i then (1 : ℝ)
            else if μ.atom i ≤ x ∧ x < 0 then -1 else 0)) =
          ∑ i, (μ.weight i - if μ.atom i ≤ x then μ.weight i else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hai : μ.atom i ≤ x
            · simp [hx, hai, not_lt_of_ge hai]
            · have hxia : x < μ.atom i := lt_of_not_ge hai
              simp [hx, hai, hxia]
      _ = (∑ i, μ.weight i) - ∑ i, if μ.atom i ≤ x then μ.weight i else 0 :=
        Finset.sum_sub_distrib (s := Finset.univ) (fun i => μ.weight i)
          (fun i => if μ.atom i ≤ x then μ.weight i else 0)
      _ = 1 - μ.cdf x := by rw [hμ.2]; rfl
  · have hx0 : x < 0 := lt_of_not_ge hx
    rw [if_neg hx]
    calc
      (∑ i, μ.weight i *
          (if 0 ≤ x ∧ x < μ.atom i then (1 : ℝ)
            else if μ.atom i ≤ x ∧ x < 0 then -1 else 0)) =
          ∑ i, -(if μ.atom i ≤ x then μ.weight i else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hai : μ.atom i ≤ x <;> simp [hx, hx0, hai]
      _ = -∑ i, if μ.atom i ≤ x then μ.weight i else 0 :=
        Finset.sum_neg_distrib (s := Finset.univ)
          (fun i => if μ.atom i ≤ x then μ.weight i else 0)
      _ = -μ.cdf x := rfl

private theorem integrable_finset_sum_of_integrable
    {α ι : Type*} [MeasurableSpace α] (m : Measure α)
    (s : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) m) :
    Integrable (fun x => ∑ i ∈ s, f i x) m := by
  have h := Finset.sum_induction (fun i => f i) (fun g => Integrable g m)
    (fun _ _ hg hh => hg.add hh) (integrable_zero α ℝ m) hf
  convert h using 1
  ext x
  simp

/-- Finite-atomic integration by parts expresses the expectation contrast of the CDF-sign
potential as the negative integral of the sign times the CDF gap. -/
theorem integral_krPotential_sub_eq_neg_integral_cdfSign_mul_cdfGap
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    μ.integral (krPotential μ ν) - ν.integral (krPotential μ ν) =
      -(∫ x, cdfSign μ ν x * cdfGap μ ν x) := by
  /- Expand the finite expectations and oriented interval integrals, interchange finite sums
  with integration.  A useful local bridge is

      (∫ t in 0..a, g t) = ∫ t, g t *
        (if 0 ≤ t ∧ t < a then 1 else if a ≤ t ∧ t < 0 then -1 else 0),

  proved by splitting on `0 ≤ a`, rewriting the interval integral as a restricted integral,
  and changing `Ioc` to `Ico` modulo the endpoint null sets.  After distributing the finite
  sums, split pointwise on `0 ≤ t`: `hμ.2` and `hν.2` identify each weighted signed-cut sum
  with `1 - cdf` on the nonnegative half-line and with `-cdf` on the negative half-line.
  Thus their difference is `-cdfGap` everywhere, while finite sums of compact interval
  indicators provide all integrability side conditions needed by `integral_finsetSum`. -/
  classical
  let signedCutAt : ℝ → ℝ → ℝ := fun a x =>
    if 0 ≤ x ∧ x < a then 1 else if a ≤ x ∧ x < 0 then -1 else 0
  have hμIntegral : μ.integral (krPotential μ ν) =
      ∫ x, cdfSign μ ν x * ∑ i, μ.weight i * signedCutAt (μ.atom i) x := by
    unfold AtomicLaw.integral krPotential
    calc
      (∑ i, μ.weight i * ∫ t in (0 : ℝ)..μ.atom i, cdfSign μ ν t) =
          ∑ i, ∫ x, μ.weight i *
            (cdfSign μ ν x * signedCutAt (μ.atom i) x) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [intervalIntegral_cdfSign_eq_integral_mul_signedCut]
            rw [integral_const_mul]
      _ = ∫ x, ∑ i, μ.weight i *
          (cdfSign μ ν x * signedCutAt (μ.atom i) x) := by
            rw [integral_finsetSum Finset.univ]
            intro i hi
            exact (cdfSign_mul_signedCut_integrable μ ν 0 (μ.atom i)).const_mul
              (μ.weight i)
      _ = ∫ x, cdfSign μ ν x * ∑ i, μ.weight i * signedCutAt (μ.atom i) x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
  have hνIntegral : ν.integral (krPotential μ ν) =
      ∫ x, cdfSign μ ν x * ∑ j, ν.weight j * signedCutAt (ν.atom j) x := by
    unfold AtomicLaw.integral krPotential
    calc
      (∑ j, ν.weight j * ∫ t in (0 : ℝ)..ν.atom j, cdfSign μ ν t) =
          ∑ j, ∫ x, ν.weight j *
            (cdfSign μ ν x * signedCutAt (ν.atom j) x) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [intervalIntegral_cdfSign_eq_integral_mul_signedCut]
            rw [integral_const_mul]
      _ = ∫ x, ∑ j, ν.weight j *
          (cdfSign μ ν x * signedCutAt (ν.atom j) x) := by
            rw [integral_finsetSum Finset.univ]
            intro j hj
            exact (cdfSign_mul_signedCut_integrable μ ν 0 (ν.atom j)).const_mul
              (ν.weight j)
      _ = ∫ x, cdfSign μ ν x * ∑ j, ν.weight j * signedCutAt (ν.atom j) x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  have hμInt : Integrable (fun x => cdfSign μ ν x *
      ∑ i, μ.weight i * signedCutAt (μ.atom i) x) volume := by
    have hsum := integrable_finset_sum_of_integrable volume Finset.univ
      (fun i x => μ.weight i * (cdfSign μ ν x * signedCutAt (μ.atom i) x))
      (fun i hi => (cdfSign_mul_signedCut_integrable μ ν 0 (μ.atom i)).const_mul
        (μ.weight i))
    convert hsum using 1
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hνInt : Integrable (fun x => cdfSign μ ν x *
      ∑ j, ν.weight j * signedCutAt (ν.atom j) x) volume := by
    have hsum := integrable_finset_sum_of_integrable volume Finset.univ
      (fun j x => ν.weight j * (cdfSign μ ν x * signedCutAt (ν.atom j) x))
      (fun j hj => (cdfSign_mul_signedCut_integrable μ ν 0 (ν.atom j)).const_mul
        (ν.weight j))
    convert hsum using 1
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hμIntegral, hνIntegral, ← integral_sub hμInt hνInt]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  have hμsum := weighted_signedCut_sum_eq μ hμ x
  have hνsum := weighted_signedCut_sum_eq ν hν x
  change (
      cdfSign μ ν x * ∑ i, μ.weight i * signedCutAt (μ.atom i) x) -
      cdfSign μ ν x * ∑ j, ν.weight j * signedCutAt (ν.atom j) x =
    -(cdfSign μ ν x * cdfGap μ ν x)
  change (∑ i, μ.weight i * signedCutAt (μ.atom i) x) = _ at hμsum
  change (∑ j, ν.weight j * signedCutAt (ν.atom j) x) = _ at hνsum
  rw [hμsum, hνsum]
  unfold cdfGap
  by_cases hx : 0 ≤ x <;> simp [hx] <;> ring

end AtomicLaw

end Causalean.Stat.Coupling
