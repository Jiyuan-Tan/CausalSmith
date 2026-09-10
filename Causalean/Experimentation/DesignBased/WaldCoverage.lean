/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Experimentation.DesignBased.DesignCore
import Causalean.Experimentation.DesignBased.GaussianCDF
import Mathlib.Order.LiminfLimsup

/-!
# Design-based conservative Wald-interval coverage

A paper-agnostic asymptotic-coverage transfer for two-sided Wald intervals built from a
*deterministic conservative* standard error. It is stated over abstract per-stage sequences — a
design `D n`, an estimator `est n`, a target `θ n`, the true variance scale `v n`, a conservative
(dominating) variance `v̂ n`, and the normalization size `m n` — so every design-based paper with a
studentized CLT and a conservative variance estimator can instantiate it in one line instead of
re-cloning the liminf/`Pr_split`/coverage argument (as the exposure-mapping, two-stage, and
bipartite-interference formalizations each previously did).
-/

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]

open Classical in
/-- **Conservative Wald-interval liminf coverage.** Consider [a sequence of finite
designs](hyp:D) with [an estimator `est n` of a target `θ n`](hyp:est). Suppose [the
normalization size `m n` is eventually positive](hyp:hmpos), [the true variance scale `v n` is
eventually positive](hyp:hvarpos), and [a deterministic conservative variance `v̂ n` eventually
dominates `v n`](hyp:hvar_le). Suppose further that [the studentized statistic
`√(m n)·(est n − θ n)/√(v n)` has design-probability CDF converging to the standard-normal CDF at
`z`](hyp:hclt) and [at `−z`](hyp:hclt_neg), where [`z` is nonnegative](hyp:hz0) and [satisfies
`Φ(z) = 1 − α/2`](hyp:hz). Then [the two-sided interval `|θ n − est n| ≤ z·√(v̂ n / m n)` has
asymptotic (liminf) coverage at least `1 − α`](goal).

The dominating conservative variance is what makes the interval *conservative*: replacing the true
`v n` by the larger `v̂ n` only widens it, so the standard-normal coverage limit becomes a lower
bound on the realized coverage. -/
lemma conservative_wald_liminf_of_studentized_cdf
    (D : ∀ n, FiniteDesign (Ω n))
    (est : ∀ n, Ω n → ℝ) (θ v vhat m : ℕ → ℝ)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hvarpos : ∀ᶠ n in atTop, 0 < v n)
    (hvar_le : ∀ᶠ n in atTop, v n ≤ vhat n)
    (α z : ℝ)
    (hclt : Tendsto (fun n =>
        (D n).Pr (fun zz =>
          Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) ≤ z))
        atTop (𝓝 (stdNormalCdf z)))
    (hclt_neg : Tendsto (fun n =>
        (D n).Pr (fun zz =>
          Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) ≤ -z))
        atTop (𝓝 (stdNormalCdf (-z))))
    (hz0 : 0 ≤ z) (hz : stdNormalCdf z = 1 - α / 2) :
    1 - α ≤ liminf (fun n =>
        (D n).Pr (fun zz =>
          |θ n - est n zz| ≤ z * Real.sqrt (vhat n / m n)))
        atTop := by
  classical
  set S : ℕ → ℝ := fun n =>
    (D n).Pr (fun zz =>
      Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) ≤ z) with hSdef
  set Lo : ℕ → ℝ := fun n =>
    (D n).Pr (fun zz =>
      Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) ≤ -z) with hLodef
  set Iv : ℕ → ℝ := fun n =>
    (D n).Pr (fun zz =>
      |θ n - est n zz| ≤ z * Real.sqrt (vhat n / m n)) with hIdef
  have hS : Tendsto S atTop (𝓝 (stdNormalCdf z)) := by
    simpa [S] using hclt
  have hLo : Tendsto Lo atTop (𝓝 (stdNormalCdf (-z))) := by
    simpa [Lo] using hclt_neg
  have hlim : Tendsto (fun n => S n - Lo n) atTop (𝓝 (1 - α)) := by
    have h := hS.sub hLo
    rw [stdNormalCdf_neg z, hz] at h
    have he : (1 - α / 2) - (1 - (1 - α / 2)) = 1 - α := by ring
    rwa [he] at h
  have hbound : ∀ᶠ n in atTop, S n - Lo n ≤ Iv n := by
    filter_upwards [hvarpos, hmpos, hvar_le] with n hvpos hmposn hvarlen
    set W : Ω n → ℝ := fun zz =>
      Real.sqrt (m n) * (est n zz - θ n) / Real.sqrt (v n) with hWdef
    have hsplit := (D n).Pr_split (fun zz => W zz ≤ z) (fun zz => W zz ≤ -z)
    have hfirst : (D n).Pr (fun zz => W zz ≤ z ∧ W zz ≤ -z) = Lo n := by
      apply (D n).Pr_congr
      intro zz
      constructor
      · exact fun h => h.2
      · intro h2
        exact ⟨le_trans h2 (by linarith [hz0]), h2⟩
    have hSLo : S n - Lo n =
        (D n).Pr (fun zz => W zz ≤ z ∧ ¬ W zz ≤ -z) := by
      have : S n = (D n).Pr (fun zz => W zz ≤ z ∧ W zz ≤ -z)
          + (D n).Pr (fun zz => W zz ≤ z ∧ ¬ W zz ≤ -z) := by
        simpa [S, W, hWdef] using hsplit
      rw [this, hfirst]
      ring
    rw [hSLo]
    apply (D n).Pr_mono
    intro zz hzz
    obtain ⟨hzhi, hzlo_not⟩ := hzz
    rw [not_le] at hzlo_not
    have habsW : |W zz| ≤ z := abs_le.mpr ⟨le_of_lt hzlo_not, hzhi⟩
    set vn : ℝ := v n with hvndef
    set vhatn : ℝ := vhat n with hvhatndef
    set cardR : ℝ := m n with hcardRdef
    have hcardposR : 0 < cardR := by simpa [cardR] using hmposn
    have hsvar : 0 < Real.sqrt vn := Real.sqrt_pos.mpr (by simpa [vn] using hvpos)
    have hscard : 0 < Real.sqrt cardR := Real.sqrt_pos.mpr hcardposR
    have habs_est : |est n zz - θ n| ≤ z * Real.sqrt vn / Real.sqrt cardR := by
      rw [hWdef, abs_div, abs_mul, abs_of_pos hsvar,
        abs_of_nonneg (Real.sqrt_nonneg cardR), div_le_iff₀ hsvar] at habsW
      have hmul : Real.sqrt cardR * |est n zz - θ n| ≤ z * Real.sqrt vn := by
        simpa [vn, cardR, mul_comm, mul_left_comm, mul_assoc] using habsW
      exact (le_div_iff₀ hscard).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    have hsqrt_le : Real.sqrt vn / Real.sqrt cardR ≤ Real.sqrt (vhatn / cardR) := by
      rw [← Real.sqrt_div (le_of_lt (by simpa [vn] using hvpos)) cardR]
      exact Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right (by simpa [vn, vhatn] using hvarlen) hcardposR.le)
    have hscale_le : z * Real.sqrt vn / Real.sqrt cardR ≤ z * Real.sqrt (vhatn / cardR) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hsqrt_le hz0
    have habs_tau : |θ n - est n zz| ≤ z * Real.sqrt (vhatn / cardR) := by
      rw [abs_sub_comm]
      exact habs_est.trans hscale_le
    simpa [Iv, vhatn, cardR] using habs_tau
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun n => S n - Lo n) :=
    hlim.isBoundedUnder_ge
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop Iv :=
    isCoboundedUnder_ge_of_le atTop (x := (1 : ℝ)) (fun n => (D n).Pr_le_one _)
  calc
    1 - α = liminf (fun n => S n - Lo n) atTop := hlim.liminf_eq.symm
    _ ≤ liminf Iv atTop := Filter.liminf_le_liminf hbound hbdd hcobdd
    _ = liminf (fun n =>
        (D n).Pr (fun zz =>
          |θ n - est n zz| ≤ z * Real.sqrt (vhat n / m n)))
        atTop := by rfl

/-- For [a sequence of finite-design laws](hyp:D) and [real-valued statistics](hyp:T), if [their
CDFs converge pointwise to a limit CDF](hyp:F,hT), [the limit CDF is continuous](hyp:hF), and [the
symmetric-band radius is nonnegative](hyp:c,hc), then [the closed symmetric-band probabilities
converge to the difference of the limiting CDF at the two endpoints](goal). -/
lemma finiteDesign_symmetricBand_tendsto (D : ∀ n, FiniteDesign (Ω n))
    (T : ∀ n, Ω n → ℝ) (F : ℝ → ℝ)
    (hT : ∀ x : ℝ, Tendsto (fun n => (D n).Pr (fun z => T n z ≤ x))
      atTop (𝓝 (F x)))
    (hF : Continuous F) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n => (D n).Pr (fun z => -c ≤ T n z ∧ T n z ≤ c))
      atTop (𝓝 (F c - F (-c))) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε8 : 0 < ε / 8 := by linarith
  obtain ⟨δ, hδ, hcont⟩ :=
    (Metric.continuousAt_iff.1 hF.continuousAt) (ε / 8) hε8
  let d : ℝ := δ / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdlt : dist (-c - d) (-c) < δ := by
    rw [Real.dist_eq]
    dsimp [d]
    rw [show -c - δ / 2 - -c = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith : 0 < δ / 2)]
    linarith
  have hFd : |F (-c - d) - F (-c)| < ε / 8 := by
    simpa [Real.dist_eq] using hcont hdlt
  let S : ℕ → ℝ := fun n => (D n).Pr (fun z => T n z ≤ c)
  let L : ℕ → ℝ := fun n => (D n).Pr (fun z => T n z ≤ -c)
  let Ld : ℕ → ℝ := fun n => (D n).Pr (fun z => T n z ≤ -c - d)
  let J : ℕ → ℝ := fun n => (D n).Pr (fun z => -c ≤ T n z ∧ T n z ≤ c)
  have hS := hT c
  have hL := hT (-c)
  have hLd := hT (-c - d)
  have hevS : ∀ᶠ n in atTop, |S n - F c| < ε / 8 := by
    simpa [S, Real.dist_eq] using (Metric.tendsto_nhds.1 hS) (ε / 8) hε8
  have hevL : ∀ᶠ n in atTop, |L n - F (-c)| < ε / 8 := by
    simpa [L, Real.dist_eq] using (Metric.tendsto_nhds.1 hL) (ε / 8) hε8
  have hevLd : ∀ᶠ n in atTop, |Ld n - F (-c - d)| < ε / 8 := by
    simpa [Ld, Real.dist_eq] using (Metric.tendsto_nhds.1 hLd) (ε / 8) hε8
  have hbounds : ∀ n, S n - L n ≤ J n ∧ J n ≤ S n - Ld n := by
    intro n
    have hlo := (D n).Pr_split (fun z => T n z ≤ c) (fun z => T n z ≤ -c)
    have hld := (D n).Pr_split (fun z => T n z ≤ c) (fun z => T n z ≤ -c - d)
    have hlofirst : (D n).Pr (fun z => T n z ≤ c ∧ T n z ≤ -c) = L n := by
      apply (D n).Pr_congr
      intro z
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h.trans (by linarith), h⟩
    have hldfirst : (D n).Pr (fun z => T n z ≤ c ∧ T n z ≤ -c - d) = Ld n := by
      apply (D n).Pr_congr
      intro z
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨h.trans (by linarith), h⟩
    have hloeq : S n - L n =
        (D n).Pr (fun z => T n z ≤ c ∧ ¬ T n z ≤ -c) := by
      have : S n = (D n).Pr (fun z => T n z ≤ c ∧ T n z ≤ -c) +
          (D n).Pr (fun z => T n z ≤ c ∧ ¬ T n z ≤ -c) := by
        simpa [S, L] using hlo
      rw [this, hlofirst]
      ring
    have hldeq : S n - Ld n =
        (D n).Pr (fun z => T n z ≤ c ∧ ¬ T n z ≤ -c - d) := by
      have : S n = (D n).Pr (fun z => T n z ≤ c ∧ T n z ≤ -c - d) +
          (D n).Pr (fun z => T n z ≤ c ∧ ¬ T n z ≤ -c - d) := by
        simpa [S, Ld] using hld
      rw [this, hldfirst]
      ring
    constructor
    · rw [hloeq]
      apply (D n).Pr_mono
      intro z hz
      exact ⟨le_of_not_ge hz.2, hz.1⟩
    · rw [hldeq]
      apply (D n).Pr_mono
      intro z hz
      constructor
      · exact hz.2
      · rw [not_le]
        linarith
  apply Filter.eventually_atTop.1
  filter_upwards [hevS, hevL, hevLd] with n hnS hnL hnLd
  rw [Real.dist_eq, abs_lt]
  rcases hbounds n with ⟨hlower, hupper⟩
  rcases abs_lt.1 hnS with ⟨hnSlo, hnShi⟩
  rcases abs_lt.1 hnL with ⟨hnLlo, hnLhi⟩
  rcases abs_lt.1 hnLd with ⟨hnLdlo, hnLdhi⟩
  rcases abs_lt.1 hFd with ⟨hFdlo, hFdhi⟩
  constructor <;> linarith

end DesignBased
end Experimentation
end Causalean
