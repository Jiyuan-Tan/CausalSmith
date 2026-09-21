/-!
# Finite atomic one-dimensional Wasserstein: duality

This module proves exact Kantorovich--Rubinstein duality for finite atomic probability laws on
the real line and constructs the CDF-sign Lipschitz potential that attains the dual value.
-/

import Causalean.Stat.Coupling.FiniteAtomicWasserstein.Transport

namespace Causalean.Stat.Coupling

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace AtomicLaw

private noncomputable def cutIndicator (a b x : ℝ) : ℝ :=
  if a ≤ x ∧ x < b then 1 else 0

private theorem cutIndicator_eq_indicator (a b : ℝ) :
    cutIndicator a b = (Ico a b).indicator (1 : ℝ → ℝ) := by
  funext x
  simp [cutIndicator, Set.indicator_apply, Set.mem_Ico]

private theorem signedCut_eq (a b x : ℝ) :
    (if a ≤ x ∧ x < b then (1 : ℝ)
      else if b ≤ x ∧ x < a then -1 else 0) =
      cutIndicator a b x - cutIndicator b a x := by
  unfold cutIndicator
  split_ifs with h₁ h₂ h₃ h₄ <;> simp_all <;> linarith

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

/-- [Two finite atomic laws](hyp:μ,ν) with [nonnegative weights summing to one](hyp:hμ,hν) have [a one-Wasserstein distance equal to the largest absolute expectation contrast over one-Lipschitz real tests](goal).

The preceding canonical CDF-sign potential attains this supremum. -/
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

end Causalean.Stat.Coupling
