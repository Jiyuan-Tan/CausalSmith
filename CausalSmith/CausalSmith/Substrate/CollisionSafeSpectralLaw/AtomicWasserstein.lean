import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.Compactness.Compact

/-!
# Finite atomic one-dimensional Wasserstein duality

This module defines finite atomic probability laws with arbitrary finite slot types and the
finite transport-polytope primal cost for `|x-y|`.  It proves the one-dimensional CDF formula,
exact Kantorovich--Rubinstein duality, and an explicit attaining Lipschitz potential.  The API is
extensional in the represented measure, so permutations, zero slots, and atom splitting or merging
do not affect the distance.
-/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

/-- A labelled finite atomic real law, prior to imposing nonnegativity and unit total mass. -/
structure AtomicLaw (ι : Type*) where
  weight : ι → ℝ
  atom : ι → ℝ

namespace AtomicLaw

/-- Nonnegative weights with total mass one make a finite atomic representation a probability law. -/
def Valid {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) : Prop :=
  (∀ i, 0 ≤ μ.weight i) ∧ ∑ i, μ.weight i = 1

/-- The probability measure represented by a valid finite list of weighted atoms. -/
noncomputable def toMeasure {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (μ.weight i) • Measure.dirac (μ.atom i)

/-- The finite weighted expectation of a scalar test function. -/
def integral {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) (f : ℝ → ℝ) : ℝ :=
  ∑ i, μ.weight i * f (μ.atom i)

/-- For a valid law, finite weighted expectation agrees with integration against its represented
atomic probability measure. -/
theorem integral_eq_measureIntegral {ι : Type*} [Fintype ι]
    (μ : AtomicLaw ι) (hμ : μ.Valid) (f : ℝ → ℝ) (hf : Continuous f) :
    μ.integral f = ∫ x, f x ∂μ.toMeasure := by
  classical
  rw [toMeasure, integral_finsetSum_measure]
  · simp [integral, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (hμ.1 _)]
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A valid finite atomic representation defines a probability measure. -/
theorem toMeasure_isProbability {ι : Type*} [Fintype ι]
    (μ : AtomicLaw ι) (hμ : μ.Valid) : IsProbabilityMeasure μ.toMeasure := by
  constructor
  simp [toMeasure]
  convert congrArg ENNReal.ofReal hμ.2 using 1 <;>
    simp [ENNReal.ofReal_sum_of_nonneg, hμ.1]

/-- A finite transport plan has nonnegative entries and the prescribed two marginals. -/
structure TransportPlan {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) where
  mass : ι → κ → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  fst_marginal : ∀ i, ∑ j, mass i j = μ.weight i
  snd_marginal : ∀ j, ∑ i, mass i j = ν.weight j

/-- The absolute-distance cost of a finite transport plan. -/
def transportCost {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) : ℝ :=
  ∑ i, ∑ j, π.mass i j * |μ.atom i - ν.atom j|

/-- Finite-atomic one-Wasserstein distance as the infimum over the transport polytope. -/
noncomputable def w1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : ℝ :=
  sInf {c : ℝ | ∃ π : TransportPlan μ ν, transportCost π = c}

/-- Every feasible finite transport plan upper-bounds finite-atomic one-Wasserstein distance. -/
theorem w1_le_transportCost {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) :
    w1 μ ν ≤ transportCost π := by
  unfold w1
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨q, rfl⟩
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (q.nonneg i j) (abs_nonneg _)
  · exact ⟨π, rfl⟩

/-- The finite transport polytope attains the one-Wasserstein infimum for two valid laws. -/
theorem exists_optimalTransportPlan {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, transportCost π = w1 μ ν := by
  classical
  let S : Set (ι → κ → ℝ) := {m |
    (∀ i j, 0 ≤ m i j) ∧
    (∀ i, ∑ j, m i j = μ.weight i) ∧
    ∀ j, ∑ i, m i j = ν.weight j}
  have hSne : S.Nonempty := by
    refine ⟨fun i j => μ.weight i * ν.weight j, ?_⟩
    refine ⟨fun i j => mul_nonneg (hμ.1 i) (hν.1 j), ?_, ?_⟩
    · intro i
      rw [← Finset.mul_sum, hν.2, mul_one]
    · intro j
      rw [← Finset.sum_mul, hμ.2, one_mul]
  have hweight_le_one (i : ι) : μ.weight i ≤ 1 := by
    rw [← hμ.2]
    exact Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)
  have hSsub : S ⊆ Set.Icc (fun _ _ => 0) (fun _ _ => 1) := by
    intro m hm
    refine ⟨fun i j => hm.1 i j, fun i j => ?_⟩
    calc
      m i j ≤ ∑ r, m i r :=
        Finset.single_le_sum (fun r _ => hm.1 i r) (Finset.mem_univ j)
      _ = μ.weight i := hm.2.1 i
      _ ≤ 1 := hweight_le_one i
  have hSclosed : IsClosed S := by
    dsimp [S]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le
            (continuous_const : Continuous (fun _ : ι → κ → ℝ => (0 : ℝ)))
            (by fun_prop : Continuous (fun m : ι → κ → ℝ => m i j)))
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ j, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => μ.weight i)))
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun j => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ i, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => ν.weight j)))
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed hSsub
  let cost : (ι → κ → ℝ) → ℝ := fun m =>
    ∑ i, ∑ j, m i j * |μ.atom i - ν.atom j|
  have hcost_cont : Continuous cost := by
    unfold cost
    fun_prop
  obtain ⟨m, hmS, hmmin⟩ := hScompact.exists_isMinOn hSne hcost_cont.continuousOn
  let π : TransportPlan μ ν :=
    { mass := m
      nonneg := hmS.1
      fst_marginal := hmS.2.1
      snd_marginal := hmS.2.2 }
  refine ⟨π, ?_⟩
  have hvalues_ne : ({c : ℝ | ∃ q : TransportPlan μ ν, transportCost q = c}).Nonempty :=
    ⟨transportCost π, π, rfl⟩
  have hvalues_bdd : BddBelow {c : ℝ | ∃ q : TransportPlan μ ν, transportCost q = c} := by
    refine ⟨0, ?_⟩
    rintro c ⟨q, rfl⟩
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (q.nonneg i j) (abs_nonneg _)
  apply le_antisymm
  · unfold w1
    apply le_csInf hvalues_ne
    rintro c ⟨q, rfl⟩
    simpa [cost, transportCost, π] using
      hmmin ⟨q.nonneg, q.fst_marginal, q.snd_marginal⟩
  · unfold w1
    exact csInf_le hvalues_bdd ⟨π, rfl⟩

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

private theorem krPotential_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ]
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

/-- The integrated absolute CDF gap is a lower bound for the cost of every finite transport plan.
This is the cut-flow inequality underlying one-dimensional transport optimality. -/
theorem integral_abs_cdfGap_le_transportCost {ι κ : Type*}
    [Fintype ι] [Fintype κ] {μ : AtomicLaw ι} {ν : AtomicLaw κ}
    (hμ : μ.Valid) (hν : ν.Valid) (π : TransportPlan μ ν) :
    (∫ x, |cdfGap μ ν x|) ≤ transportCost π := by
  rw [← integral_crossingEnvelope_eq_transportCost π]
  exact integral_abs_cdfGap_le_integral_crossingEnvelope π

/-- The quadratic displacement objective used only to select a no-counterflow plan from the
finite transport polytope. -/
def transportSqCost {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) : ℝ :=
  ∑ i, ∑ j, π.mass i j * (μ.atom i - ν.atom j) ^ 2

/-- Among all transport plans between two valid finite atomic laws, one minimizes the quadratic
displacement objective. -/
theorem exists_transportPlan_minimizing_sqCost
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, ∀ q : TransportPlan μ ν,
      transportSqCost π ≤ transportSqCost q := by
  /- Reuse the compact finite transport polytope argument from `exists_optimalTransportPlan`,
  replacing absolute displacement by the continuous quadratic objective. -/
  classical
  let S : Set (ι → κ → ℝ) := {m |
    (∀ i j, 0 ≤ m i j) ∧
    (∀ i, ∑ j, m i j = μ.weight i) ∧
    ∀ j, ∑ i, m i j = ν.weight j}
  have hSne : S.Nonempty := by
    refine ⟨fun i j => μ.weight i * ν.weight j, ?_⟩
    refine ⟨fun i j => mul_nonneg (hμ.1 i) (hν.1 j), ?_, ?_⟩
    · intro i
      rw [← Finset.mul_sum, hν.2, mul_one]
    · intro j
      rw [← Finset.sum_mul, hμ.2, one_mul]
  have hweight_le_one (i : ι) : μ.weight i ≤ 1 := by
    rw [← hμ.2]
    exact Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)
  have hSsub : S ⊆ Set.Icc (fun _ _ => 0) (fun _ _ => 1) := by
    intro m hm
    refine ⟨fun i j => hm.1 i j, fun i j => ?_⟩
    calc
      m i j ≤ ∑ r, m i r :=
        Finset.single_le_sum (fun r _ => hm.1 i r) (Finset.mem_univ j)
      _ = μ.weight i := hm.2.1 i
      _ ≤ 1 := hweight_le_one i
  have hSclosed : IsClosed S := by
    dsimp [S]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le
            (continuous_const : Continuous (fun _ : ι → κ → ℝ => (0 : ℝ)))
            (by fun_prop : Continuous (fun m : ι → κ → ℝ => m i j)))
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ j, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => μ.weight i)))
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun j => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ i, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => ν.weight j)))
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed hSsub
  let cost : (ι → κ → ℝ) → ℝ := fun m =>
    ∑ i, ∑ j, m i j * (μ.atom i - ν.atom j) ^ 2
  have hcost_cont : Continuous cost := by
    unfold cost
    fun_prop
  obtain ⟨m, hmS, hmmin⟩ := hScompact.exists_isMinOn hSne hcost_cont.continuousOn
  let π : TransportPlan μ ν :=
    { mass := m
      nonneg := hmS.1
      fst_marginal := hmS.2.1
      snd_marginal := hmS.2.2 }
  refine ⟨π, fun q => ?_⟩
  simpa [cost, transportSqCost, π] using
    hmmin ⟨q.nonneg, q.fst_marginal, q.snd_marginal⟩

/-- A quadratic-cost-minimizing finite transport plan cannot send positive mass in opposite
directions across the same real cut. -/
theorem cutMonotone_of_sqCost_minimal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν)
    (hmin : ∀ q : TransportPlan μ ν, transportSqCost π ≤ transportSqCost q) :
    CutMonotone π := by
  /- If positive entries `(i,j)` and `(k,l)` cross a cut in opposite directions, move their
  common minimum mass from `(i,j),(k,l)` to `(i,l),(k,j)`.  Marginals and nonnegativity are
  preserved, while the quadratic objective falls by
  `2 * ε * (μ.atom k - μ.atom i) * (ν.atom j - ν.atom l) > 0`. -/
  classical
  intro x
  by_contra hcounter
  rw [not_or] at hcounter
  let right : ℝ :=
    ∑ i, ∑ j, if μ.atom i ≤ x ∧ x < ν.atom j then π.mass i j else 0
  let left : ℝ :=
    ∑ i, ∑ j, if ν.atom j ≤ x ∧ x < μ.atom i then π.mass i j else 0
  have hright_nonneg : 0 ≤ right := by
    dsimp [right]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hleft_nonneg : 0 ≤ left := by
    dsimp [left]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hright_ne : right ≠ 0 := by
    simpa [right] using hcounter.1
  have hleft_ne : left ≠ 0 := by
    simpa [left] using hcounter.2
  have hright_pos : 0 < right := lt_of_le_of_ne hright_nonneg (Ne.symm hright_ne)
  have hleft_pos : 0 < left := lt_of_le_of_ne hleft_nonneg (Ne.symm hleft_ne)
  obtain ⟨i, hi, hi_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact π.nonneg i j
        · exact le_rfl)).mp hright_pos
  obtain ⟨j, hj, hij_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl)).mp hi_pos
  have hij_cut : μ.atom i ≤ x ∧ x < ν.atom j := by
    by_contra hij
    simp [hij] at hij_pos
  have hij_mass : 0 < π.mass i j := by
    simpa [hij_cut] using hij_pos
  obtain ⟨k, hk, hk_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg fun l _ => by
        split_ifs
        · exact π.nonneg k l
        · exact le_rfl)).mp hleft_pos
  obtain ⟨l, hl, hkl_pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun l _ => by
      split_ifs
      · exact π.nonneg k l
      · exact le_rfl)).mp hk_pos
  have hkl_cut : ν.atom l ≤ x ∧ x < μ.atom k := by
    by_contra hkl
    simp [hkl] at hkl_pos
  have hkl_mass : 0 < π.mass k l := by
    simpa [hkl_cut] using hkl_pos
  have hsource : μ.atom i < μ.atom k := lt_of_le_of_lt hij_cut.1 hkl_cut.2
  have htarget : ν.atom l < ν.atom j := lt_of_le_of_lt hkl_cut.1 hij_cut.2
  have hik : i ≠ k := by
    intro hik
    subst k
    exact (lt_irrefl _ hsource)
  have hjl : j ≠ l := by
    intro hjl
    subst l
    exact (lt_irrefl _ htarget)
  let ε : ℝ := min (π.mass i j) (π.mass k l)
  have hε_pos : 0 < ε := by
    exact lt_min hij_mass hkl_mass
  have hε_ij : ε ≤ π.mass i j := min_le_left _ _
  have hε_kl : ε ≤ π.mass k l := min_le_right _ _
  let q : TransportPlan μ ν :=
    { mass := fun a b =>
        π.mass a b
          - (if a = i ∧ b = j then ε else 0)
          - (if a = k ∧ b = l then ε else 0)
          + (if a = i ∧ b = l then ε else 0)
          + (if a = k ∧ b = j then ε else 0)
      nonneg := by
        intro a b
        by_cases hai : a = i <;> by_cases hak : a = k <;>
          by_cases hbj : b = j <;> by_cases hbl : b = l <;>
          simp_all [sub_nonneg.mpr hε_ij, sub_nonneg.mpr hε_kl,
            π.nonneg] <;>
          exact add_nonneg (π.nonneg _ _) (le_of_lt hε_pos)
      fst_marginal := by
        intro a
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        by_cases hai : a = i
        · subst a
          simp [π.fst_marginal, hik]
        · by_cases hak : a = k
          · subst a
            simp [π.fst_marginal, hai, Ne.symm hik]
          · simp [π.fst_marginal, hai, hak]
      snd_marginal := by
        intro b
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        by_cases hbj : b = j
        · subst b
          simp [π.snd_marginal, hjl]
        · by_cases hbl : b = l
          · subst b
            simp [π.snd_marginal, hbj, Ne.symm hjl]
          · simp [π.snd_marginal, hbj, hbl] }
  have hsum_single (a : ι) (b : κ) (f : ι → κ → ℝ) :
      (∑ u, ∑ v, if u = a ∧ v = b then f u v else 0) = f a b := by
    calc
      _ = ∑ v, if a = a ∧ v = b then f a v else 0 := by
        apply Finset.sum_eq_single a
        · intro u hu hua
          simp [hua]
        · simp
      _ = f a b := by simp
  have hcost : transportSqCost q = transportSqCost π -
      2 * ε * (μ.atom k - μ.atom i) * (ν.atom j - ν.atom l) := by
    unfold transportSqCost
    dsimp [q]
    simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [hik, hjl, hsum_single]
    ring
  have hdecrease : 0 < 2 * ε * (μ.atom k - μ.atom i) * (ν.atom j - ν.atom l) := by
    positivity
  have hstrict : transportSqCost q < transportSqCost π := by
    rw [hcost]
    linarith
  exact (not_lt_of_ge (hmin q)) hstrict

/-- Any two valid finite atomic laws have a transport plan with no simultaneous flow in opposite
directions across any cut. -/
theorem exists_cutMonotone_transportPlan
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, CutMonotone π := by
  obtain ⟨π, hπ⟩ := exists_transportPlan_minimizing_sqCost μ ν hμ hν
  exact ⟨π, cutMonotone_of_sqCost_minimal π hπ⟩

/-- A no-counterflow transport plan attains the integrated absolute CDF gap. -/
theorem transportCost_eq_integral_abs_cdfGap_of_cutMonotone
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν)
    (hπ : CutMonotone π) :
    transportCost π = ∫ x, |cdfGap μ ν x| := by
  /- At each cut, `CutMonotone` turns the absolute signed crossing mass into the unsigned
  crossing envelope.  Integrate and use `integral_crossingEnvelope_eq_transportCost`. -/
  classical
  rw [← integral_crossingEnvelope_eq_transportCost π]
  apply integral_congr_ae
  filter_upwards with x
  let right : ℝ :=
    ∑ i, ∑ j, if μ.atom i ≤ x ∧ x < ν.atom j then π.mass i j else 0
  let left : ℝ :=
    ∑ i, ∑ j, if ν.atom j ≤ x ∧ x < μ.atom i then π.mass i j else 0
  have hright : 0 ≤ right := by
    dsimp [right]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hleft : 0 ≤ left := by
    dsimp [left]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact π.nonneg i j
      · exact le_rfl
  have hsigned : signedCrossing π x = right - left := by
    unfold signedCrossing
    dsimp [right, left]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hr : μ.atom i ≤ x ∧ x < ν.atom j
    · have hl : ¬(ν.atom j ≤ x ∧ x < μ.atom i) := by
        rintro ⟨hjx, hxi⟩
        exact (not_lt_of_ge hjx) hr.2
      simp [hr, hl]
    · by_cases hl : ν.atom j ≤ x ∧ x < μ.atom i
      · simp [hr, hl]
      · simp [hr, hl]
  have henvelope : crossingEnvelope π x = right + left := by
    unfold crossingEnvelope
    dsimp [right, left]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hr : μ.atom i ≤ x ∧ x < ν.atom j
    · have hl : ¬(ν.atom j ≤ x ∧ x < μ.atom i) := by
        rintro ⟨hjx, hxi⟩
        exact (not_lt_of_ge hjx) hr.2
      simp [hr, hl]
    · by_cases hl : ν.atom j ≤ x ∧ x < μ.atom i
      · simp [hr, hl]
      · simp [hr, hl]
  rw [cdfGap_eq_signedCrossing π x, hsigned, henvelope]
  rcases hπ x with hright_zero | hleft_zero
  · change right = 0 at hright_zero
    rw [hright_zero, zero_sub, abs_neg, abs_of_nonneg hleft, zero_add]
  · change left = 0 at hleft_zero
    rw [hleft_zero, sub_zero, abs_of_nonneg hright, add_zero]

/-- Two valid finite atomic laws have a monotone transport plan whose absolute-distance cost is
exactly the integrated absolute CDF gap. -/
theorem exists_transportPlan_cost_eq_integral_abs_cdfGap
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, transportCost π = ∫ x, |cdfGap μ ν x| := by
  obtain ⟨π, hπ⟩ := exists_cutMonotone_transportPlan μ ν hμ hν
  exact ⟨π, transportCost_eq_integral_abs_cdfGap_of_cutMonotone π hπ⟩

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

/-- The CDF sign selector multiplied by the CDF gap is its absolute value. -/
theorem cdfSign_mul_cdfGap_eq_abs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) :
    cdfSign μ ν x * cdfGap μ ν x = |cdfGap μ ν x| := by
  unfold cdfSign
  split_ifs with hpos hneg
  · simp [abs_of_pos hpos]
  · have hnonpos : cdfGap μ ν x ≤ 0 := le_of_not_gt hpos
    simp [abs_of_neg hneg]
  · have hzero : cdfGap μ ν x = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
    simp [hzero]

/-- The expectation contrast of the CDF-sign potential has absolute value equal to the integrated
absolute CDF gap.  This is finite-atomic integration by parts with cancellation outside the
atoms. -/
theorem abs_integral_krPotential_sub_eq_integral_abs_cdfGap
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    |μ.integral (krPotential μ ν) - ν.integral (krPotential μ ν)| =
      ∫ x, |cdfGap μ ν x| := by
  rw [integral_krPotential_sub_eq_neg_integral_cdfSign_mul_cdfGap μ ν hμ hν]
  have hfun : (fun x => cdfSign μ ν x * cdfGap μ ν x) =
      fun x => |cdfGap μ ν x| := by
    funext x
    exact cdfSign_mul_cdfGap_eq_abs μ ν x
  rw [hfun, abs_neg, abs_of_nonneg]
  exact integral_nonneg fun x => abs_nonneg _

/-- On the real line, finite-atomic one-Wasserstein distance is the integral of the absolute CDF
difference. -/
theorem w1_eq_integral_abs_cdfGap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    w1 μ ν = ∫ x, |cdfGap μ ν x| := by
  obtain ⟨πcdf, hπcdf⟩ :=
    exists_transportPlan_cost_eq_integral_abs_cdfGap μ ν hμ hν
  obtain ⟨πopt, hπopt⟩ := exists_optimalTransportPlan μ ν hμ hν
  apply le_antisymm
  · rw [← hπcdf]
    exact w1_le_transportCost πcdf
  · rw [← hπopt]
    exact integral_abs_cdfGap_le_transportCost hμ hν πopt

/-- Transport cost weakly dominates the expectation contrast of every one-Lipschitz test
function. -/
theorem lipschitz_integral_sub_le_transportCost {ι κ : Type*}
    [Fintype ι] [Fintype κ] {μ : AtomicLaw ι} {ν : AtomicLaw κ}
    (π : TransportPlan μ ν) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    |μ.integral f - ν.integral f| ≤ transportCost π := by
  classical
  have hrewrite : μ.integral f - ν.integral f =
      ∑ i, ∑ j, π.mass i j * (f (μ.atom i) - f (ν.atom j)) := by
    rw [integral, integral]
    calc
      (∑ i, μ.weight i * f (μ.atom i)) - ∑ j, ν.weight j * f (ν.atom j) =
          (∑ i, ∑ j, π.mass i j * f (μ.atom i)) -
            ∑ j, ∑ i, π.mass i j * f (ν.atom j) := by
              congr 1
              · apply Finset.sum_congr rfl
                intro i hi
                rw [← π.fst_marginal i, Finset.sum_mul]
              · apply Finset.sum_congr rfl
                intro j hj
                rw [← π.snd_marginal j, Finset.sum_mul]
      _ = ∑ i, ∑ j, π.mass i j * (f (μ.atom i) - f (ν.atom j)) := by
            rw [Finset.sum_comm (f := fun j i => π.mass i j * f (ν.atom j))]
            simp only [Finset.sum_sub_distrib, mul_sub]
  rw [hrewrite, transportCost]
  calc
    |∑ i, ∑ j, π.mass i j * (f (μ.atom i) - f (ν.atom j))| ≤
        ∑ i, ∑ j, |π.mass i j * (f (μ.atom i) - f (ν.atom j))| := by
      calc
        |∑ i, ∑ j, π.mass i j * (f (μ.atom i) - f (ν.atom j))| ≤
            ∑ i, |∑ j, π.mass i j * (f (μ.atom i) - f (ν.atom j))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, |π.mass i j * (f (μ.atom i) - f (ν.atom j))| := by
          exact Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, π.mass i j * |μ.atom i - ν.atom j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (π.nonneg i j)]
      apply mul_le_mul_of_nonneg_left _ (π.nonneg i j)
      simpa [Real.dist_eq] using hf.dist_le_mul (μ.atom i) (ν.atom j)

/-- Finite-atomic one-Wasserstein distance satisfies Kantorovich--Rubinstein weak duality. -/
theorem lipschitz_integral_sub_le_w1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    |μ.integral f - ν.integral f| ≤ w1 μ ν := by
  obtain ⟨π, hπ⟩ := exists_optimalTransportPlan μ ν hμ hν
  rw [← hπ]
  exact lipschitz_integral_sub_le_transportCost π f hf

/-- The CDF-sign potential is one-Lipschitz and attains the finite-atomic
Kantorovich--Rubinstein dual value. -/
theorem krPotential_attains {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    LipschitzWith 1 (krPotential μ ν) ∧
      w1 μ ν = |μ.integral (krPotential μ ν) - ν.integral (krPotential μ ν)| := by
  refine ⟨krPotential_lipschitz μ ν, ?_⟩
  rw [w1_eq_integral_abs_cdfGap μ ν hμ hν,
    abs_integral_krPotential_sub_eq_integral_abs_cdfGap μ ν hμ hν]

/-- Exact finite-atomic Kantorovich--Rubinstein duality on the real line, with absolute
expectation contrast. -/
theorem w1_eq_sSup_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    w1 μ ν = sSup {r : ℝ | ∃ f : ℝ → ℝ,
      LipschitzWith 1 f ∧ r = |μ.integral f - ν.integral f|} := by
  let S : Set ℝ := {r : ℝ | ∃ f : ℝ → ℝ,
    LipschitzWith 1 f ∧ r = |μ.integral f - ν.integral f|}
  obtain ⟨hpotLip, hpotEq⟩ := krPotential_attains μ ν hμ hν
  have hpotMem : |μ.integral (krPotential μ ν) - ν.integral (krPotential μ ν)| ∈ S :=
    ⟨krPotential μ ν, hpotLip, rfl⟩
  have hSne : S.Nonempty := ⟨_, hpotMem⟩
  have hSbdd : BddAbove S := by
    refine ⟨w1 μ ν, ?_⟩
    rintro r ⟨f, hf, rfl⟩
    exact lipschitz_integral_sub_le_w1 μ ν hμ hν f hf
  change w1 μ ν = sSup S
  apply le_antisymm
  · rw [hpotEq]
    exact le_csSup hSbdd hpotMem
  · exact csSup_le hSne fun r hr => by
      obtain ⟨f, hf, rfl⟩ := hr
      exact lipschitz_integral_sub_le_w1 μ ν hμ hν f hf

/-- A uniform bound on one-Lipschitz expectation contrasts directly bounds finite-atomic
one-Wasserstein distance. -/
theorem w1_le_of_lipschitz_integral_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid)
    {ε : ℝ} (h : ∀ f : ℝ → ℝ, LipschitzWith 1 f →
      |μ.integral f - ν.integral f| ≤ ε) :
    w1 μ ν ≤ ε := by
  obtain ⟨hLip, hEq⟩ := krPotential_attains μ ν hμ hν
  rw [hEq]
  exact h (krPotential μ ν) hLip

/-- One-Wasserstein distance depends only on the represented measures, allowing unrelated finite
slot types; hence permutations, zero-weight slots, and splitting or merging coincident atoms are
all invisible. -/
theorem w1_congr_toMeasure {ι ι' κ κ' : Type*}
    [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    (μ : AtomicLaw ι) (μ' : AtomicLaw ι') (ν : AtomicLaw κ) (ν' : AtomicLaw κ')
    (hμ : μ.Valid) (hμ' : μ'.Valid) (hν : ν.Valid) (hν' : ν'.Valid)
    (hleft : μ.toMeasure = μ'.toMeasure) (hright : ν.toMeasure = ν'.toMeasure) :
    w1 μ ν = w1 μ' ν' := by
  rw [w1_eq_integral_abs_cdfGap μ ν hμ hν,
    w1_eq_integral_abs_cdfGap μ' ν' hμ' hν']
  have hleftCdf : μ.cdf = μ'.cdf :=
    cdf_eq_of_toMeasure_eq μ μ' hμ hμ' hleft
  have hrightCdf : ν.cdf = ν'.cdf :=
    cdf_eq_of_toMeasure_eq ν ν' hν hν' hright
  apply integral_congr_ae
  filter_upwards with x
  rw [cdfGap, cdfGap, congrFun hleftCdf x, congrFun hrightCdf x]

end AtomicLaw

end CausalSmith.Substrate.CollisionSafeSpectralLaw
