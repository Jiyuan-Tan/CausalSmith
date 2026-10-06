/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.SteinMethod.Solution
public import Mathlib.Order.Filter.AtTopBot.Ring
public import Causalean.Mathlib.Probability.SteinMethod.Bounds_Part1

/-!
# Uniform bounds on the Stein solution (Chen–Goldstein–Shao)

For an absolutely continuous test function `h` with bounded derivative `‖h'‖_∞ ≤ L`, the Stein
solution `f_h` is uniformly bounded by `L` and its derivative by `2·L`:

    ‖f_h‖_∞ ≤ L,   ‖f_h'‖_∞ ≤ 2·L.

This file proves `steinSol_deriv_abs_le` and `steinSol_deriv_lipschitz`; the
companion bound `steinSol_abs_le` is proved in `Bounds_Part1`. The last packages the
second-derivative bound
as Lipschitz control of `f_h'`. The proof develops the needed Gaussian tail
moment identities, two-sided lower Mills-ratio bounds, and the cancellation
inequalities behind Chen-Goldstein-Shao Lemma 2.4, equation (2.13). These are
the bounds that make the local-dependence Stein estimate work for test functions such as
`h = cos(t * ·)` and `h = sin(t * ·)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Real

namespace Causalean.Mathlib.Probability.SteinMethod

/-! ### Lower Mills-ratio bound

The derivative bound needs a *lower* bound on the Gaussian tail
`∫_{Ioi w} φ ≥ (w/(w²+1))·φ w` for `w ≥ 0` (in fact for all `w`).  We obtain it from the
fact that `hMills w := ∫_{Ioi w} φ − (w/(w²+1))·φ w` is antitone with limit `0` at `+∞`. -/

/-- `∫_{Iic u} φ` has derivative `φ w` (fundamental theorem of calculus). -/
private theorem Iic_phi_hasDerivAt (w : ℝ) :
    HasDerivAt (fun u => ∫ x in Set.Iic u, phi x) (phi w) w := by
  set a : ℝ := w - 1 with ha_def
  have hIIc : ∀ u : ℝ, IntegrableOn phi (Set.Iic u) := fun u => phi_integrable.integrableOn
  have hGeq : ∀ u : ℝ, (∫ x in Set.Iic u, phi x)
      = (∫ x in Set.Iic a, phi x) + ∫ x in a..u, phi x := by
    intro u
    have := intervalIntegral.integral_Iic_sub_Iic (hIIc a) (hIIc u)
    linarith [this]
  have hivint : IntervalIntegrable phi MeasureTheory.volume a w :=
    phi_integrable.intervalIntegrable
  have hd : HasDerivAt (fun u => ∫ x in a..u, phi x) (phi w) w :=
    intervalIntegral.integral_hasDerivAt_right hivint
      phi_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter phi_continuous.continuousAt
  have hd' : HasDerivAt (fun u => (∫ x in Set.Iic a, phi x) + ∫ x in a..u, phi x) (phi w) w := by
    simpa using hd.const_add (∫ x in Set.Iic a, phi x)
  exact hd'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => hGeq u))

/-- `∫_{Ioi u} φ` has derivative `−φ w`. -/
private theorem m_hasDerivAt (w : ℝ) :
    HasDerivAt (fun u => ∫ x in Set.Ioi u, phi x) (-phi w) w := by
  have hsplit : ∀ u : ℝ, (∫ x in Set.Ioi u, phi x)
      = (∫ x, phi x) - ∫ x in Set.Iic u, phi x := by
    intro u
    have := integral_add_compl (μ := volume) (f := phi) (measurableSet_Iic (a := u)) phi_integrable
    rw [Set.compl_Iic] at this; linarith [this]
  have hd : HasDerivAt (fun u => (∫ x, phi x) - ∫ x in Set.Iic u, phi x) (-phi w) w := by
    simpa using (Iic_phi_hasDerivAt w).const_sub (∫ x, phi x)
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => hsplit u))

/-- `∫_{Ioi u} φ → 0` as `u → +∞`. -/
private theorem m_tendsto_atTop :
    Filter.Tendsto (fun u => ∫ x in Set.Ioi u, phi x) Filter.atTop (nhds 0) := by
  have hcov : AECover (volume : Measure ℝ) Filter.atTop (fun u : ℝ => Set.Iic u) :=
    aecover_Iic Filter.tendsto_id
  have hIic : Filter.Tendsto (fun u => ∫ x in Set.Iic u, phi x) Filter.atTop (nhds (∫ x, phi x)) :=
    hcov.integral_tendsto_of_countably_generated phi_integrable
  have hsplit : ∀ u : ℝ, (∫ x in Set.Ioi u, phi x)
      = (∫ x, phi x) - ∫ x in Set.Iic u, phi x := by
    intro u
    have := integral_add_compl (μ := volume) (f := phi) (measurableSet_Iic (a := u)) phi_integrable
    rw [Set.compl_Iic] at this; linarith [this]
  have hlim : Filter.Tendsto (fun u => (∫ x, phi x) - ∫ x in Set.Iic u, phi x) Filter.atTop
      (nhds ((∫ x, phi x) - ∫ x, phi x)) := Filter.Tendsto.const_sub _ hIic
  rw [sub_self] at hlim
  exact hlim.congr (fun u => (hsplit u).symm)

/-- The Mills witness function `hMills w = ∫_{Ioi w} φ − (w/(w²+1))·φ w`. -/
private noncomputable def hMills (w : ℝ) : ℝ :=
  (∫ x in Set.Ioi w, phi x) - (w / (w ^ 2 + 1)) * phi w

private theorem hMills_hasDerivAt (w : ℝ) :
    HasDerivAt hMills (-(2 / (w ^ 2 + 1) ^ 2) * phi w) w := by
  have hden : (w ^ 2 + 1) ≠ 0 := by positivity
  have hm := m_hasDerivAt w
  have hphi : HasDerivAt phi (-w * phi w) w := by
    unfold phi
    have hpow : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-w) w := by
      have := ((hasDerivAt_pow 2 w).div_const 2).fun_neg
      simpa [neg_div, pow_one] using this.congr_deriv (by ring)
    have hcomp : HasDerivAt (fun y => Real.exp (-y ^ 2 / 2))
        (Real.exp (-w ^ 2 / 2) * (-w)) w := (Real.hasDerivAt_exp _).comp w hpow
    exact hcomp.congr_deriv (by ring)
  have hr : HasDerivAt (fun u => u / (u ^ 2 + 1)) ((1 - w ^ 2) / (w ^ 2 + 1) ^ 2) w := by
    have hnum : HasDerivAt (fun u : ℝ => u) 1 w := hasDerivAt_id w
    have hden' : HasDerivAt (fun u : ℝ => u ^ 2 + 1) (2 * w) w := by
      simpa using (hasDerivAt_pow 2 w).add_const 1
    exact (hnum.fun_div hden' hden).congr_deriv (by field_simp; ring)
  have hrp : HasDerivAt (fun u => (u / (u ^ 2 + 1)) * phi u)
      ((1 - w ^ 2) / (w ^ 2 + 1) ^ 2 * phi w + (w / (w ^ 2 + 1)) * (-w * phi w)) w := hr.mul hphi
  exact (hm.fun_sub hrp).congr_deriv (by field_simp; ring)

private theorem hMills_antitone : Antitone hMills := by
  apply antitone_of_deriv_nonpos (fun x => (hMills_hasDerivAt x).differentiableAt)
  intro x
  rw [(hMills_hasDerivAt x).deriv]
  have hp := (phi_pos x).le
  have : 0 ≤ (2 / (x ^ 2 + 1) ^ 2) * phi x := mul_nonneg (by positivity) hp
  linarith

private theorem phi_tendsto_atTop : Filter.Tendsto phi Filter.atTop (nhds 0) := by
  have := neg_phi_tendsto_atTop
  simpa using this.neg

private theorem rphi_tendsto :
    Filter.Tendsto (fun u : ℝ => (u / (u ^ 2 + 1)) * phi u) Filter.atTop (nhds 0) := by
  have hbdd : ∀ u : ℝ, |u / (u ^ 2 + 1)| ≤ 1 := by
    intro u
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < u ^ 2 + 1), div_le_one (by positivity)]
    nlinarith [sq_nonneg (|u| - 1), sq_abs u, abs_nonneg u]
  have hphi0 := phi_tendsto_atTop
  rw [Metric.tendsto_atTop] at hphi0 ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hphi0 ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  simp only [Real.dist_eq, sub_zero] at hb ⊢
  calc |(n / (n ^ 2 + 1)) * phi n| = |n / (n ^ 2 + 1)| * |phi n| := by rw [abs_mul]
    _ ≤ 1 * |phi n| := by gcongr; exact hbdd n
    _ = |phi n| := one_mul _
    _ < ε := hb

private theorem hMills_tendsto : Filter.Tendsto hMills Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun u => (∫ x in Set.Ioi u, phi x) - (u / (u ^ 2 + 1)) * phi u)
      Filter.atTop (nhds (0 - 0)) := m_tendsto_atTop.sub rphi_tendsto
  rw [sub_zero] at h
  exact h

/-- **Lower Mills bound:** `(w/(w²+1))·φ w ≤ ∫_{Ioi w} φ` for every `w`. -/
private theorem lower_mills (w : ℝ) :
    (w / (w ^ 2 + 1)) * phi w ≤ ∫ x in Set.Ioi w, phi x := by
  have hnn : 0 ≤ hMills w := hMills_antitone.le_of_tendsto hMills_tendsto w
  unfold hMills at hnn
  linarith

/-- **Lower Mills bound, left tail:** `(-w/(w²+1))·φ w ≤ ∫_{Iic w} φ`. -/
private theorem lower_mills_left (w : ℝ) :
    (-w / (w ^ 2 + 1)) * phi w ≤ ∫ x in Set.Iic w, phi x := by
  have hrefl : (∫ x in Set.Ioi (-w), phi x) = ∫ x in Set.Iic w, phi x := by
    have h := integral_comp_neg_Ioi (c := -w) (f := phi)
    have hev : (fun x => phi (-x)) = phi := by
      funext x; unfold phi; rw [neg_pow_two]
    rw [hev] at h
    simpa using h
  have hlm := lower_mills (-w)
  rw [hrefl] at hlm
  have hphi : phi (-w) = phi w := by unfold phi; rw [neg_pow_two]
  rw [hphi] at hlm
  have hsq : (-w) ^ 2 = w ^ 2 := by ring
  rw [hsq] at hlm
  exact hlm

/-- `√(2π)·(h w − E[h(Z)]) = −(∫_{Iic w}(h−h w)φ + ∫_{Ioi w}(h−h w)φ)`. -/
private theorem sqrt_mul_centered_eq {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ} (hb : ∀ x, |h x| ≤ C)
    (w : ℝ) :
    Real.sqrt (2 * π) * (h w - gExpect h) =
      -((∫ x in Set.Iic w, (h x - h w) * phi x) + ∫ x in Set.Ioi w, (h x - h w) * phi x) := by
  -- `K·(h w − c) = ∫ (h w − h x) φ`, and the latter splits over `Iic w ∪ Ioi w`.
  have hdiffInt : Integrable (fun x => (h x - h w) * phi x) := by
    have h1 : Integrable (fun x => h x * phi x) := mul_phi_integrable hh hb
    have h2 : Integrable (fun x => h w * phi x) := phi_integrable.const_mul _
    have hsub := h1.sub h2
    refine hsub.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Pi.sub_apply]; ring
  have hsplit : (∫ x, (h x - h w) * phi x)
      = (∫ x in Set.Iic w, (h x - h w) * phi x) + ∫ x in Set.Ioi w, (h x - h w) * phi x := by
    have := integral_add_compl (μ := volume) (measurableSet_Iic (a := w)) hdiffInt
    rw [Set.compl_Iic] at this; linarith [this]
  -- `∫ (h x − h w) φ = ∫ h x φ − h w·K = K·c − h w·K = -K·(h w − c)`.
  have hKc : Real.sqrt (2 * π) * gExpect h = ∫ x, h x * phi x := by
    rw [gExpect_eq, ← mul_assoc, mul_inv_cancel₀ (by positivity : Real.sqrt (2 * π) ≠ 0), one_mul]
  have hInt : (∫ x, (h x - h w) * phi x) = (∫ x, h x * phi x) - h w * Real.sqrt (2 * π) := by
    have h1 : Integrable (fun x => h x * phi x) := mul_phi_integrable hh hb
    have h2 : Integrable (fun x => h w * phi x) := phi_integrable.const_mul _
    have heq : (fun x => (h x - h w) * phi x) = (fun x => h x * phi x - h w * phi x) := by
      funext x; ring
    rw [heq, integral_sub h1 h2, integral_const_mul, integral_phi]
  rw [← hsplit, hInt, ← hKc]
  ring

/-- Pure arithmetic fact `(|w|·K + 1) ≤ K·(w²+1)` for `K ≥ 4/3` (here `K ≥ 1` suffices with the
square term), used twice in the derivative crux. -/
private theorem mills_arith {w k : ℝ} (hk : 4 / 3 ≤ k) :
    w * k + 1 ≤ k * (w ^ 2 + 1) ∧ -w * k + 1 ≤ k * (w ^ 2 + 1) := by
  have hkpos : 0 < k := by linarith
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg hkpos.le (sq_nonneg (w - 1 / 2)), hk]
  · nlinarith [mul_nonneg hkpos.le (sq_nonneg (w + 1 / 2)), hk]

/-- The analytic crux of the derivative bound, as a pure real inequality.  With
`e = e^{w²/2}`, `p = ∫_{Ioi w}φ`, `q = ∫_{Iic w}φ`, `f = φ w`, `k = √(2π)`, the two-sided
lower Mills bounds give `e·(w q + f)·(f − w p) ≤ k`. -/
private theorem crux_pure {e p q f k w : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (he : 0 < e) (hk43 : 4 / 3 ≤ k)
    (hef : e * f = 1) (hpq : q + p = k) (hf1 : f ≤ 1)
    (hao : 0 ≤ f - w * p) (hai : 0 ≤ w * q + f)
    (hmillsR : (w / (w ^ 2 + 1)) * f ≤ p)
    (hmillsL : (-w / (w ^ 2 + 1)) * f ≤ q) :
    e * ((w * q + f) * (f - w * p)) ≤ k := by
  have hden : (0:ℝ) < w ^ 2 + 1 := by positivity
  have hkpos : 0 < k := by linarith
  have hpleK : p ≤ k := by linarith
  have hqleK : q ≤ k := by linarith
  have hEaoNonneg : 0 ≤ e * (f - w * p) := mul_nonneg he.le hao
  have hEaiNonneg : 0 ≤ e * (w * q + f) := mul_nonneg he.le hai
  rcases le_or_gt 0 w with hw | hw
  · -- w ≥ 0
    have hwEPlb : w ^ 2 / (w ^ 2 + 1) ≤ w * e * p := by
      have h1 : w * ((w / (w ^ 2 + 1)) * f) ≤ w * p := mul_le_mul_of_nonneg_left hmillsR hw
      have h2 : w * ((w / (w ^ 2 + 1)) * f) = (w ^ 2 / (w ^ 2 + 1)) * f := by ring
      rw [h2] at h1
      have h3 : e * ((w ^ 2 / (w ^ 2 + 1)) * f) ≤ e * (w * p) := mul_le_mul_of_nonneg_left h1 he.le
      have h4 : e * ((w ^ 2 / (w ^ 2 + 1)) * f) = (w ^ 2 / (w ^ 2 + 1)) * (e * f) := by ring
      rw [h4, hef, mul_one] at h3
      nlinarith [h3]
    have hEao_le : e * (f - w * p) ≤ 1 / (w ^ 2 + 1) := by
      have heq : e * (f - w * p) = 1 - w * e * p := by nlinarith [hef]
      rw [heq, le_div_iff₀ hden]
      have hmul := mul_le_mul_of_nonneg_right hwEPlb hden.le
      rw [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
      nlinarith [hmul]
    have hai_le : w * q + f ≤ w * k + 1 := by
      have : w * q ≤ w * k := mul_le_mul_of_nonneg_left hqleK hw; linarith
    calc e * ((w * q + f) * (f - w * p)) = (w * q + f) * (e * (f - w * p)) := by ring
      _ ≤ (w * k + 1) * (1 / (w ^ 2 + 1)) := by
          apply mul_le_mul hai_le hEao_le hEaoNonneg
          have : (0:ℝ) ≤ w * k := mul_nonneg hw hkpos.le; linarith
      _ ≤ k := by rw [mul_one_div, div_le_iff₀ hden]; exact (mills_arith hk43).1
  · -- w < 0
    have hnw : 0 < -w := by linarith
    have hwEQub : w * e * q ≤ -(w ^ 2 / (w ^ 2 + 1)) := by
      have h1 : (-w) * ((-w / (w ^ 2 + 1)) * f) ≤ (-w) * q :=
        mul_le_mul_of_nonneg_left hmillsL hnw.le
      have h2 : (-w) * ((-w / (w ^ 2 + 1)) * f) = (w ^ 2 / (w ^ 2 + 1)) * f := by ring
      rw [h2] at h1
      have h3 : e * ((w ^ 2 / (w ^ 2 + 1)) * f) ≤ e * ((-w) * q) :=
        mul_le_mul_of_nonneg_left h1 he.le
      have h4 : e * ((w ^ 2 / (w ^ 2 + 1)) * f) = (w ^ 2 / (w ^ 2 + 1)) * (e * f) := by ring
      rw [h4, hef, mul_one] at h3
      nlinarith [h3]
    have hEai_le : e * (w * q + f) ≤ 1 / (w ^ 2 + 1) := by
      have heq : e * (w * q + f) = w * e * q + 1 := by nlinarith [hef]
      rw [heq, le_div_iff₀ hden]
      have hmul := mul_le_mul_of_nonneg_right hwEQub hden.le
      rw [neg_mul, div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
      nlinarith [hmul]
    have hao_le : f - w * p ≤ -w * k + 1 := by
      have : -w * p ≤ -w * k := mul_le_mul_of_nonneg_left hpleK hnw.le; nlinarith [hf1]
    calc e * ((w * q + f) * (f - w * p)) = (f - w * p) * (e * (w * q + f)) := by ring
      _ ≤ (-w * k + 1) * (1 / (w ^ 2 + 1)) := by
          apply mul_le_mul hao_le hEai_le hEaiNonneg
          have : (0:ℝ) ≤ -w * k := mul_nonneg hnw.le hkpos.le; linarith
      _ ≤ k := by rw [mul_one_div, div_le_iff₀ hden]; exact (mills_arith hk43).2

/-- **Sup bound on the derivative of the Stein solution** in terms of the `h`-derivative bound. -/
theorem steinSol_deriv_abs_le (h : ℝ → ℝ) {C L : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h) (w : ℝ) :
    |deriv (steinSol h) w| ≤ 2 * L := by
  set K : ℝ := Real.sqrt (2 * π) with hKdef
  have hKpos : 0 < K := Real.sqrt_pos.mpr (by positivity)
  have hKge43 : 4 / 3 ≤ K := by
    rw [hKdef, show (4/3:ℝ) = Real.sqrt ((4/3)^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt; nlinarith [Real.two_le_pi]
  set P : ℝ := ∫ x in Set.Ioi w, phi x with hP
  set Q : ℝ := ∫ x in Set.Iic w, phi x with hQ
  set A : ℝ := ∫ x in Set.Iic w, (h x - h w) * phi x with hA
  set B : ℝ := ∫ x in Set.Ioi w, (h x - h w) * phi x with hB
  set E : ℝ := Real.exp (w ^ 2 / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hPpos : 0 ≤ P := by
    rw [hP]; exact setIntegral_nonneg measurableSet_Ioi (fun x _ => (phi_pos x).le)
  have hQpos : 0 ≤ Q := by
    rw [hQ]; exact setIntegral_nonneg measurableSet_Iic (fun x _ => (phi_pos x).le)
  -- The two nonnegative tail "first moments".
  have hao : phi w - w * P = ∫ x in Set.Ioi w, (x - w) * phi x := by
    rw [hP]; exact (integral_Ioi_sub_mul_phi w).symm
  have hai : w * Q + phi w = ∫ x in Set.Iic w, (w - x) * phi x := by
    rw [hQ]; exact (integral_Iic_sub_mul_phi w).symm
  have haoNonneg : 0 ≤ phi w - w * P := by
    rw [hao]; exact setIntegral_nonneg measurableSet_Ioi
      (fun x hx => mul_nonneg (by have := Set.mem_Ioi.mp hx; linarith) (phi_pos x).le)
  have haiNonneg : 0 ≤ w * Q + phi w := by
    rw [hai]; exact setIntegral_nonneg measurableSet_Iic
      (fun x hx => mul_nonneg (by have := Set.mem_Iic.mp hx; linarith) (phi_pos x).le)
  -- `E·φ w = 1`.
  have hEphi : E * phi w = 1 := exp_mul_phi w
  -- Stein equation and the weighted identity give the c-free derivative identity.
  have hstein : deriv (steinSol h) w = w * steinSol h w + (h w - gExpect h) :=
    (steinSol_hasDerivAt h hdiff.continuous hb w).deriv
  have hwid : K * steinSol h w = E * (P * A - Q * B) := by
    rw [hKdef, hP, hQ, hA, hB, hE]
    exact steinSol_weighted_identity hdiff.continuous hb w
  have hKD : K * (h w - gExpect h) = -(A + B) := by
    rw [hKdef, hA, hB]; exact sqrt_mul_centered_eq hdiff.continuous hb w
  -- `K·deriv = w·E·(P A − Q B) − (A + B) = −E·(A·aₒ + B·aᵢ)`.
  have hKderiv : K * deriv (steinSol h) w = -(E * (A * (phi w - w * P) + B * (w * Q + phi w))) := by
    have hexpand : K * deriv (steinSol h) w = w * (K * steinSol h w) + K * (h w - gExpect h) := by
      rw [hstein]; ring
    rw [hexpand, hwid, hKD]
    -- `w·E(PA−QB) − (A+B) = −E(A(φ w−wP)+B(wQ+φ w))`, using `E·φ w = 1`.
    linear_combination (A + B) * hEphi
  -- Bound `K·|deriv| ≤ 2·L·E·(w Q + φ w)·(φ w − w P)`.
  have hAbound : |A| ≤ L * (w * Q + phi w) := by
    rw [hA, hQ]; exact abs_integral_diff_phi_Iic_le hdiff.continuous hb hd hdiff w
  have hBbound : |B| ≤ L * (phi w - w * P) := by
    rw [hB, hP]; exact abs_integral_diff_phi_Ioi_le hdiff.continuous hb hd hdiff w
  have hLnn : 0 ≤ L := le_trans (abs_nonneg (deriv h 0)) (hd 0)
  have hbound : K * |deriv (steinSol h) w| ≤ 2 * L * (E * ((w * Q + phi w) * (phi w - w * P))) := by
    calc K * |deriv (steinSol h) w|
        = |K * deriv (steinSol h) w| := by rw [abs_mul, abs_of_nonneg hKpos.le]
      _ = E * |A * (phi w - w * P) + B * (w * Q + phi w)| := by
          rw [hKderiv, abs_neg, abs_mul, abs_of_nonneg hEpos.le]
      _ ≤ E * (|A| * (phi w - w * P) + |B| * (w * Q + phi w)) := by
          gcongr
          calc |A * (phi w - w * P) + B * (w * Q + phi w)|
              ≤ |A * (phi w - w * P)| + |B * (w * Q + phi w)| := abs_add_le _ _
            _ = |A| * (phi w - w * P) + |B| * (w * Q + phi w) := by
                rw [abs_mul, abs_mul, abs_of_nonneg haoNonneg, abs_of_nonneg haiNonneg]
      _ ≤ E * (L * (w * Q + phi w) * (phi w - w * P)
              + L * (phi w - w * P) * (w * Q + phi w)) := by
          gcongr
      _ = 2 * L * (E * ((w * Q + phi w) * (phi w - w * P))) := by ring
  -- `P, Q ≤ K`.
  have hPQK : Q + P = K := by rw [hQ, hP, hKdef]; exact integral_Iic_add_Ioi_phi w
  have hPleK : P ≤ K := by linarith
  have hQleK : Q ≤ K := by linarith
  have hden : (0:ℝ) < w ^ 2 + 1 := by positivity
  have hEaoNonneg : 0 ≤ E * (phi w - w * P) := mul_nonneg hEpos.le haoNonneg
  have hEaiNonneg : 0 ≤ E * (w * Q + phi w) := mul_nonneg hEpos.le haiNonneg
  -- `φ w ≤ 1`.
  have hphi_le_one : phi w ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 by simp]; unfold phi
    apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg w]
  -- The analytic crux, via the pure inequality `crux_pure` and two-sided lower Mills.
  have hcrux : E * ((w * Q + phi w) * (phi w - w * P)) ≤ K :=
    crux_pure hPpos hQpos hEpos hKge43 hEphi hPQK hphi_le_one haoNonneg haiNonneg
      (by rw [hP]; exact lower_mills w) (by rw [hQ]; exact lower_mills_left w)
  -- Conclude.
  have hfinal : K * |deriv (steinSol h) w| ≤ 2 * L * K := by
    calc K * |deriv (steinSol h) w|
        ≤ 2 * L * (E * ((w * Q + phi w) * (phi w - w * P))) := hbound
      _ ≤ 2 * L * K := by
          have h2L : 0 ≤ 2 * L := by linarith
          exact mul_le_mul_of_nonneg_left hcrux h2L
  have hfinal' : K * |deriv (steinSol h) w| ≤ K * (2 * L) := by
    rw [mul_comm K (2 * L)]; exact hfinal
  exact le_of_mul_le_mul_left hfinal' hKpos

/-! ### Second-derivative bound `‖f_h''‖ ≤ 2L`

The Stein equation `f' = w·f + (h − c)` differentiates to `f'' = f + w·f' + h'`, where the term
`w·f'` is individually unbounded.  Substituting the Stein equation once more gives the *crux*
`f'' = (1+w²)·f + w·(h − c) + h'`, and the unbounded part is precisely `(1+w²)·f + w·(h − c)`,
which is in fact bounded by `L` thanks to the two-sided lower Mills bounds — this is the
cancellation underlying Chen–Goldstein–Shao Lemma 2.4, equation (2.13). The pure inequality below
packages it. -/

/-- The analytic crux of the *second*-derivative bound, as a pure real inequality.  With
`e = e^{w²/2}`, `p = ∫_{Ioi w}φ`, `q = ∫_{Iic w}φ`, `f = φ w`, `k = √(2π)`, and the two
coefficients `cA = (1+w²)·e·p − w`, `cB = (1+w²)·e·q + w` (both nonnegative by the lower Mills
bounds), one has the sharp identity `(w q + f)·cA + (f − w p)·cB = k`.  Together with
`|a| ≤ L·(w q + f)` and `|b| ≤ L·(f − w p)` this yields `|a·cA − b·cB| ≤ k·L`. -/
private theorem crux2_pure {e p q f k w a b L : ℝ}
    (he : 0 < e)
    (hef : e * f = 1) (hpq : q + p = k)
    (ha : |a| ≤ L * (w * q + f)) (hb : |b| ≤ L * (f - w * p))
    (hmillsR : (w / (w ^ 2 + 1)) * f ≤ p)
    (hmillsL : (-w / (w ^ 2 + 1)) * f ≤ q) :
    |a * ((1 + w ^ 2) * e * p - w) - b * ((1 + w ^ 2) * e * q + w)| ≤ k * L := by
  have hden : (0:ℝ) < w ^ 2 + 1 := by positivity
  -- Both coefficients are nonnegative.
  have hcA : 0 ≤ (1 + w ^ 2) * e * p - w := by
    have h1 : e * ((w / (w ^ 2 + 1)) * f) ≤ e * p := mul_le_mul_of_nonneg_left hmillsR he.le
    have h2 : e * ((w / (w ^ 2 + 1)) * f) = (w / (w ^ 2 + 1)) * (e * f) := by ring
    rw [h2, hef, mul_one] at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 hden.le, mul_div_cancel₀ w (ne_of_gt hden)]
  have hcB : 0 ≤ (1 + w ^ 2) * e * q + w := by
    have h1 : e * ((-w / (w ^ 2 + 1)) * f) ≤ e * q := mul_le_mul_of_nonneg_left hmillsL he.le
    have h2 : e * ((-w / (w ^ 2 + 1)) * f) = (-w / (w ^ 2 + 1)) * (e * f) := by ring
    rw [h2, hef, mul_one] at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 hden.le, mul_div_cancel₀ (-w) (ne_of_gt hden)]
  -- The sharp identity `aᵢ·cA + aₒ·cB = k`.
  have hidentity :
      (w * q + f) * ((1 + w ^ 2) * e * p - w) + (f - w * p) * ((1 + w ^ 2) * e * q + w) = k := by
    linear_combination (p + q) * (1 + w ^ 2) * hef + hpq
  -- Triangle inequality plus the coefficient bounds, then the identity.
  calc |a * ((1 + w ^ 2) * e * p - w) - b * ((1 + w ^ 2) * e * q + w)|
      ≤ |a * ((1 + w ^ 2) * e * p - w)| + |b * ((1 + w ^ 2) * e * q + w)| := abs_sub _ _
    _ = |a| * ((1 + w ^ 2) * e * p - w) + |b| * ((1 + w ^ 2) * e * q + w) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hcA, abs_of_nonneg hcB]
    _ ≤ (L * (w * q + f)) * ((1 + w ^ 2) * e * p - w)
          + (L * (f - w * p)) * ((1 + w ^ 2) * e * q + w) := by
        gcongr
    _ = L * ((w * q + f) * ((1 + w ^ 2) * e * p - w)
          + (f - w * p) * ((1 + w ^ 2) * e * q + w)) := by ring
    _ = L * k := by rw [hidentity]
    _ = k * L := by ring

/-- **Crux of the second-derivative bound.** The combination `(1+w²)·f_h(w) + w·(h(w) − E[h(Z)])`
— equal to `f_h''(w) − h'(w)` — is uniformly bounded by `L`. -/
private theorem steinSol_crux_le (h : ℝ → ℝ) (hh : Continuous h) {C L : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h)
    (w : ℝ) :
    |(1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)| ≤ L := by
  set K : ℝ := Real.sqrt (2 * π) with hKdef
  have hKpos : 0 < K := Real.sqrt_pos.mpr (by positivity)
  set P : ℝ := ∫ x in Set.Ioi w, phi x with hP
  set Q : ℝ := ∫ x in Set.Iic w, phi x with hQ
  set A : ℝ := ∫ x in Set.Iic w, (h x - h w) * phi x with hA
  set B : ℝ := ∫ x in Set.Ioi w, (h x - h w) * phi x with hB
  set E : ℝ := Real.exp (w ^ 2 / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hEphi : E * phi w = 1 := exp_mul_phi w
  -- Weighted identity for `f` and centering identity for `h − c`, both c-free.
  have hwid : K * steinSol h w = E * (P * A - Q * B) := by
    rw [hKdef, hP, hQ, hA, hB, hE]; exact steinSol_weighted_identity hh hb w
  have hKD : K * (h w - gExpect h) = -(A + B) := by
    rw [hKdef, hA, hB]; exact sqrt_mul_centered_eq hh hb w
  -- `K·crux = A·cA − B·cB` with `cA = (1+w²)EP − w`, `cB = (1+w²)EQ + w`.
  have hKcrux : K * ((1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)) =
      A * ((1 + w ^ 2) * E * P - w) - B * ((1 + w ^ 2) * E * Q + w) := by
    have hexpand : K * ((1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)) =
        (1 + w ^ 2) * (K * steinSol h w) + w * (K * (h w - gExpect h)) := by ring
    rw [hexpand, hwid, hKD]; ring
  -- Bounds on `|A|`, `|B|`.
  have hAbound : |A| ≤ L * (w * Q + phi w) := by
    rw [hA, hQ]; exact abs_integral_diff_phi_Iic_le hh hb hd hdiff w
  have hBbound : |B| ≤ L * (phi w - w * P) := by
    rw [hB, hP]; exact abs_integral_diff_phi_Ioi_le hh hb hd hdiff w
  have hPQK : Q + P = K := by rw [hQ, hP, hKdef]; exact integral_Iic_add_Ioi_phi w
  -- Apply the pure inequality.
  have hbound : K * |(1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)| ≤ K * L := by
    calc K * |(1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)|
        = |K * ((1 + w ^ 2) * steinSol h w + w * (h w - gExpect h))| := by
          rw [abs_mul, abs_of_nonneg hKpos.le]
      _ = |A * ((1 + w ^ 2) * E * P - w) - B * ((1 + w ^ 2) * E * Q + w)| := by rw [hKcrux]
      _ ≤ K * L :=
          crux2_pure hEpos hEphi hPQK hAbound hBbound
            (by rw [hP]; exact lower_mills w) (by rw [hQ]; exact lower_mills_left w)
  exact le_of_mul_le_mul_left hbound hKpos

/-- For a bounded differentiable test function, the derivative of its standard-normal Stein
solution is differentiable at each point, with derivative equal to the solution value plus the
point times its first derivative plus the derivative of the test function. -/
theorem steinSol_deriv_hasDerivAt (h : ℝ → ℝ) {C : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hdiff : Differentiable ℝ h) (w : ℝ) :
    HasDerivAt (deriv (steinSol h))
      (steinSol h w + (w * deriv (steinSol h) w + deriv h w)) w := by
  -- `deriv (steinSol h) = fun u => u * steinSol h u + (h u - gExpect h)` (Stein equation).
  have hderiv_eq : deriv (steinSol h) = fun u => u * steinSol h u + (h u - gExpect h) := by
    funext u; exact (steinSol_hasDerivAt h hdiff.continuous hb u).deriv
  -- `f` is differentiable with derivative `deriv (steinSol h) w`.
  have hfderiv : deriv (steinSol h) w = w * steinSol h w + (h w - gExpect h) :=
    (steinSol_hasDerivAt h hdiff.continuous hb w).deriv
  have hf : HasDerivAt (steinSol h) (deriv (steinSol h) w) w := by
    rw [hfderiv]; exact steinSol_hasDerivAt h hdiff.continuous hb w
  rw [hderiv_eq]
  -- Differentiate `u ↦ u·f(u) + (h u − c)`.
  have hprod : HasDerivAt (fun u => u * steinSol h u)
      (1 * steinSol h w + w * deriv (steinSol h) w) w :=
    (hasDerivAt_id w).mul hf
  have hh' : HasDerivAt (fun u => h u - gExpect h) (deriv h w) w :=
    ((hdiff w).hasDerivAt).sub_const _
  exact (hprod.fun_add hh').congr_deriv (by rw [hfderiv]; ring)

/-- The absolute second derivative of the standard-normal Stein solution at each point is at most
twice the uniform bound on the derivative of the test function. -/
theorem steinSol_secondDeriv_abs_le (h : ℝ → ℝ) {C L : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h)
    (w : ℝ) :
    |steinSol h w + (w * deriv (steinSol h) w + deriv h w)| ≤ 2 * L := by
  -- `f + w f' + h' = (1+w²) f + w (h − c) + h'`, using the Stein equation `f' = w f + (h − c)`.
  have hstein : deriv (steinSol h) w = w * steinSol h w + (h w - gExpect h) :=
    (steinSol_hasDerivAt h hdiff.continuous hb w).deriv
  have hrewrite : steinSol h w + (w * deriv (steinSol h) w + deriv h w) =
      ((1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)) + deriv h w := by
    rw [hstein]; ring
  rw [hrewrite]
  calc |((1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)) + deriv h w|
      ≤ |(1 + w ^ 2) * steinSol h w + w * (h w - gExpect h)| + |deriv h w| := abs_add_le _ _
    _ ≤ L + L := by
        gcongr
        · exact steinSol_crux_le h hdiff.continuous hb hd hdiff w
        · exact hd w
    _ = 2 * L := by ring

/-- For [a real-valued test function and derivative bound](hyp:h,C,L), if [the function is
uniformly bounded](hyp:hb), [its derivative is uniformly bounded](hyp:hd), and [the function is
differentiable](hyp:hdiff), then for [any two evaluation points](hyp:u,v), [the derivatives of
its standard-normal Stein solution differ by at most twice the derivative bound times the
distance between those points](goal).

**Lipschitz bound on the derivative of the Stein solution** (equivalent to `‖f_h''‖ ≤ 2L`;
Chen–Goldstein–Shao Lemma 2.4, equation (2.13)). The form `f_h'` is `2L`-Lipschitz is what the
Taylor step in the local-dependence Stein bound consumes. -/
theorem steinSol_deriv_lipschitz (h : ℝ → ℝ) {C L : ℝ}
    (hb : ∀ x, |h x| ≤ C) (hd : ∀ x, |deriv h x| ≤ L) (hdiff : Differentiable ℝ h)
    (u v : ℝ) :
    |deriv (steinSol h) u - deriv (steinSol h) v| ≤ 2 * L * |u - v| := by
  -- Mean value inequality: `deriv (steinSol h)` is differentiable everywhere with second
  -- derivative bounded by `2L`, so it is `2L`-Lipschitz.
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (f := deriv (steinSol h)) (s := Set.univ)
    (fun z _ => (steinSol_deriv_hasDerivAt h hb hdiff z).differentiableAt)
    (fun z _ => by
      rw [Real.norm_eq_abs, (steinSol_deriv_hasDerivAt h hb hdiff z).deriv]
      exact steinSol_secondDeriv_abs_le h hb hd hdiff z)
    convex_univ (Set.mem_univ v) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using hbound

end Causalean.Mathlib.Probability.SteinMethod
