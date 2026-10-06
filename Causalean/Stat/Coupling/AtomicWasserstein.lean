module
public import Causalean.Stat.Coupling.AtomicCutMonotone

/-!
# Finite atomic one-dimensional Wasserstein duality

This module proves the one-dimensional CDF formula for the finite-atomic one-Wasserstein
distance, exact Kantorovich--Rubinstein duality, and an explicit attaining Lipschitz potential.
The API is extensional in the represented measure, so permutations, zero slots, and atom splitting
or merging do not affect the distance.  The atomic laws and transport plans, the CDF and potential
calculus, and the cut-monotone plan it builds on live in `AtomicTransport`, `AtomicCdf` and
`AtomicCutMonotone`, all re-exported from here.
-/

public section

namespace Causalean.Stat.Coupling

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace AtomicLaw

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

/-- [Two finite atomic laws with finite slot types](hyp:ι,κ,μ,ν) and [valid probability weights](hyp:hμ,hν) have [one-Wasserstein distance equal to the supremum of absolute expectation contrasts over one-Lipschitz functions](goal). -/
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
