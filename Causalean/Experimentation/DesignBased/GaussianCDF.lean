/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Standard normal CDF facts (design-based presentation)

Thin adapter exposing the standard-normal cumulative distribution function to the design-based
interval theorems in the `.real (Iic t)` presentation they rely on definitionally.  The function
and every fact below are the canonical `Causalean.Mathlib.stdNormalCDF` from
`Causalean/Mathlib/Probability/StdNormalCDF.lean` — the single source of truth for the standard
normal CDF — re-exported under the `DesignBased.stdNormalCdf` name via `stdNormalCdf_eq`.  No proof
is duplicated here: nonnegativity, the upper bound, monotonicity, symmetry, and continuity all
delegate to the canonical lemmas.
-/

import Causalean.Mathlib.Probability.StdNormalCDF
import Causalean.Experimentation.DesignBased.InProb

/-! # Standard normal CDF adapter

The design-based standard-normal CDF is a namespace-local presentation of the canonical
Mathlib-facing CDF.

The definition `stdNormalCdf` uses the `.real (Iic t)` probability-measure presentation needed by
design-based interval and CLT statements, while `stdNormalCdf_eq` identifies it with
`Causalean.Mathlib.stdNormalCDF`. The remaining lemmas forward the reusable facts needed
downstream: nonnegativity, the upper bound by one, monotonicity, symmetry
`stdNormalCdf_neg`, and continuity `continuous_stdNormalCdf`.
-/

open MeasureTheory Set Filter Topology

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- For [a real threshold](hyp:t), [the standard normal cumulative distribution function](goal)
is the probability that a standard normal random variable is no greater than that threshold.

It is definitionally the canonical `Causalean.Mathlib.stdNormalCDF` (see `stdNormalCdf_eq`) in
the probability-measure presentation used by the design-based interval theorems. -/
noncomputable def stdNormalCdf (t : ℝ) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 1).real (Set.Iic t)

/-- The design-based `.real (Iic)` presentation agrees with the canonical `stdNormalCDF`. -/
@[simp] lemma stdNormalCdf_eq (t : ℝ) : stdNormalCdf t = Causalean.Mathlib.stdNormalCDF t := by
  rw [Causalean.Mathlib.stdNormalCDF_def]; exact (ProbabilityTheory.cdf_eq_real _ t).symm

/-- The standard-normal cumulative probability is nonnegative. -/
lemma stdNormalCdf_nonneg (t : ℝ) : 0 ≤ stdNormalCdf t := by
  rw [stdNormalCdf_eq]; exact Causalean.Mathlib.stdNormalCDF_nonneg t

/-- The standard-normal cumulative probability is at most one. -/
lemma stdNormalCdf_le_one (t : ℝ) : stdNormalCdf t ≤ 1 := by
  rw [stdNormalCdf_eq]; exact Causalean.Mathlib.stdNormalCDF_le_one t

/-- The standard-normal cumulative distribution function is monotone in its threshold. -/
lemma monotone_stdNormalCdf : Monotone stdNormalCdf := by
  rw [show stdNormalCdf = Causalean.Mathlib.stdNormalCDF from funext stdNormalCdf_eq]
  exact Causalean.Mathlib.stdNormalCDF_monotone

/-- **Symmetry of the standard normal CDF.** For [any threshold `t`](hyp:t), [the standard
normal CDF satisfies `Φ(−t) = 1 − Φ(t)`](goal). -/
lemma stdNormalCdf_neg (t : ℝ) : stdNormalCdf (-t) = 1 - stdNormalCdf t := by
  rw [stdNormalCdf_eq, stdNormalCdf_eq]; exact Causalean.Mathlib.stdNormalCDF_neg t

/-- **Continuity of the standard normal CDF.** [The standard normal cumulative distribution
function `Φ` is continuous](goal). -/
@[fun_prop]
lemma continuous_stdNormalCdf : Continuous stdNormalCdf := by
  rw [show stdNormalCdf = Causalean.Mathlib.stdNormalCDF from funext stdNormalCdf_eq]
  exact Causalean.Mathlib.stdNormalCDF_continuous

namespace FiniteDesign

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]

/-- For [a sequence of finite-design laws](hyp:D) and [real-valued statistics](hyp:T), if [their
CDFs converge pointwise to the standard normal CDF](hyp:hT), then [the statistics are bounded in
probability](goal). -/
theorem boundedInProb_of_stdNormalCDF (D : ∀ n, FiniteDesign (Ω n))
    (T : ∀ n, Ω n → ℝ)
    (hT : ∀ x : ℝ, Tendsto (fun n => (D n).Pr (fun z => T n z ≤ x))
      atTop (𝓝 (stdNormalCdf x))) :
    BoundedInProb D T := by
  intro η hη
  have htop : Tendsto stdNormalCdf atTop (𝓝 1) := by
    rw [show stdNormalCdf = Causalean.Mathlib.stdNormalCDF by
      funext x; exact stdNormalCdf_eq x]
    exact Causalean.Mathlib.stdNormalCDF_tendsto_atTop
  have hevent : ∀ᶠ x : ℝ in atTop, 1 - stdNormalCdf x < η / 4 := by
    have h := (Metric.tendsto_nhds.1 htop) (η / 4) (by linarith)
    filter_upwards [h] with x hx
    rw [Real.dist_eq] at hx
    linarith [(abs_lt.1 hx).1]
  obtain ⟨R, hRtail, hRpos⟩ :=
    (hevent.and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨2 * R, ?_⟩
  have hneg := hT (-R)
  have hpos := hT R
  have hsum : Tendsto (fun n =>
      (D n).Pr (fun z => T n z ≤ -R) +
        (1 - (D n).Pr (fun z => T n z ≤ R))) atTop
      (𝓝 (2 * (1 - stdNormalCdf R))) := by
    convert hneg.add (tendsto_const_nhds.sub hpos) using 1
    · rw [stdNormalCdf_neg]
      ring
  have hsumSmall : ∀ᶠ n in atTop,
      (D n).Pr (fun z => T n z ≤ -R) +
        (1 - (D n).Pr (fun z => T n z ≤ R)) < η := by
    have hlimlt : 2 * (1 - stdNormalCdf R) < η := by linarith
    exact hsum.eventually (eventually_lt_nhds hlimlt)
  filter_upwards [hsumSmall] with n hn
  have hcompl : (D n).Pr (fun z => ¬ T n z ≤ R) =
      1 - (D n).Pr (fun z => T n z ≤ R) := by
    have hs := (D n).Pr_split (fun _ => True) (fun z => T n z ≤ R)
    have htrue : (D n).Pr (fun _ => True) = 1 := by
      unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
      simp [(D n).p_sum]
    rw [htrue] at hs
    simp only [true_and] at hs
    linarith
  calc
    (D n).Pr (fun z => 2 * R ≤ |T n z|)
        ≤ (D n).Pr (fun z => T n z ≤ -R ∨ ¬ T n z ≤ R) := by
          apply (D n).Pr_mono
          intro z hz
          rcases le_total (T n z) 0 with hnonpos | hnonneg
          · left
            rw [abs_of_nonpos hnonpos] at hz
            linarith
          · right
            rw [abs_of_nonneg hnonneg] at hz
            linarith
    _ ≤ (D n).Pr (fun z => T n z ≤ -R) +
          (D n).Pr (fun z => ¬ T n z ≤ R) := Pr_or_le _ _ _
    _ ≤ η := by rw [hcompl]; exact hn.le

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
