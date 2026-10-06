/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): consistency of the direct-effect contrast estimator

Along a sequence of two-stage Hudgens–Halloran experiments (`LHExperiment`) in which the number of
groups grows, the Horvitz-Thompson estimator converges in probability to the population average
control-minus-treatment direct-effect contrast. This is the negative of the treatment-minus-control
contrast used by Liu–Hudgens (2014). The argument is the lightweight finite Chebyshev inequality
applied to the two-stage variance: the estimator is unbiased (so the estimand equals its
expectation), Chebyshev bounds the deviation probability by `directVar / ε²`, and bounded potential
outcomes, fixed within-group allocation counts on the design support, and `C → ∞` imply that this
variance vanishes.
-/

module
public import Causalean.Experimentation.DesignBased.EdgeVarianceBound
public import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup
public import Causalean.Stat.FiniteDesign.Chebyshev
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Direct-contrast consistency

The two-stage estimator of the control-minus-treatment direct-effect contrast is consistent from
bounded potential outcomes, fixed within-group allocations on the design support, and a growing
number of selected groups. This contrast is the negative of the Liu–Hudgens treatment-minus-control
estimand.

This file proves Chebyshev consistency for the sign-reversed Liu–Hudgens direct contrast along a
sequence of two-stage experiments.
-/

public section

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

private lemma abs_groupEst_le_of_bounded
    {ι : Type*} {n : ι → ℕ}
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (z : Bool)
    {m B : ℝ} (hm : 0 < m)
    (hY : ∀ (j : Fin (n i)) (w : WAssign n i), |Y i j w| ≤ B)
    (w : WAssign n i) (hcount : (∑ j, if w j = z then (1 : ℝ) else 0) = m) :
    |groupEst Y i z m w| ≤ B := by
  have hsum : |∑ j, if w j = z then Y i j w else 0|
      ≤ ∑ j, if w j = z then B else 0 := by
    calc
      |∑ j, if w j = z then Y i j w else 0|
          ≤ ∑ j, |if w j = z then Y i j w else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, if w j = z then B else 0 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        by_cases hj : w j = z
        · simp [hj, hY j w]
        · simp [hj]
  unfold groupEst
  rw [abs_div, abs_of_pos hm]
  calc
    |∑ j, if w j = z then Y i j w else 0| / m
        ≤ (∑ j, if w j = z then B else 0) / m :=
          div_le_div_of_nonneg_right hsum hm.le
    _ = B := by
      rw [show (∑ j, if w j = z then B else 0) =
          B * ∑ j, if w j = z then (1 : ℝ) else 0 by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by by_cases hj : w j = z <;> simp [hj])]
      rw [hcount, mul_div_cancel_right₀ B hm.ne']

private lemma abs_E_le_of_abs_le_on_support {Ω : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (X : Ω → ℝ) {B : ℝ}
    (hX : ∀ ω, D.p ω ≠ 0 → |X ω| ≤ B) : |D.E X| ≤ B := by
  unfold FiniteDesign.E
  calc
    |∑ ω, D.p ω * X ω| ≤ ∑ ω, |D.p ω * X ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, D.p ω * B := by
      refine Finset.sum_le_sum (fun ω _ => ?_)
      rw [abs_mul, abs_of_nonneg (D.p_nonneg ω)]
      by_cases hp : D.p ω = 0
      · simp [hp]
      · exact mul_le_mul_of_nonneg_left (hX ω hp) (D.p_nonneg ω)
    _ = B := by rw [← Finset.sum_mul, D.p_sum, one_mul]

private lemma Var_le_sq_of_abs_le {Ω : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (X : Ω → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ ω, D.p ω ≠ 0 → |X ω| ≤ B) : D.Var X ≤ B ^ 2 := by
  have hsq : ∀ ω, D.p ω ≠ 0 → (X ω) ^ 2 ≤ B ^ 2 := fun ω hp => by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hB).2 (hX ω hp)
  have hE : D.E (fun ω => (X ω) ^ 2) ≤ B ^ 2 := by
    unfold FiniteDesign.E
    calc
      ∑ ω, D.p ω * X ω ^ 2 ≤ ∑ ω, D.p ω * B ^ 2 := by
        refine Finset.sum_le_sum (fun ω _ => ?_)
        by_cases hp : D.p ω = 0
        · simp [hp]
        · exact mul_le_mul_of_nonneg_left (hsq ω hp) (D.p_nonneg ω)
      _ = B ^ 2 := by rw [← Finset.sum_mul, D.p_sum, one_mul]
  rw [FiniteDesign.Var_eq]
  nlinarith [sq_nonneg (D.E X)]

/-- **Consistency of the direct-effect contrast estimator (Liu–Hudgens 2014).** Along [a sequence
of two-stage experiments](hyp:Exp), suppose [potential outcomes are uniformly bounded by a
nonnegative constant](hyp:hY,hB), [control and treatment allocation counts are
positive](hyp:hm0pos,hm1pos), [every within-group assignment with nonzero design probability has
those fixed allocation counts](hyp:hcount0,hcount1), [the number of groups assigned the treatment
strategy is positive and no larger than the
population](hyp:hCpos,hCN),
and [that number tends to infinity](hyp:hCtendsto). Then, for [every positive tolerance](hyp:hε),
[the control-minus-treatment direct-effect estimator converges in probability to its population
contrast](goal). This contrast is the negative of Liu–Hudgens' treatment-minus-control estimand.

Proof: rewrite the estimand as the estimator's expectation (unbiasedness, `E_estD`), bound the
deviation probability by `directVar / ε²` (Chebyshev + `var_estD`), and derive
`directVar ≤ 36 B²/C` from the primitive bounded-outcome and fixed-allocation conditions. The
support premises have the form supplied by `crd_supp`; off-support assignments are unconstrained. -/
theorem estDirect_consistent_of_bounded_outcomes (Exp : ℕ → LHExperiment)
    {B : ℝ} (hB : 0 ≤ B)
    (hY : ∀ n i j (w : Fin ((Exp n).gsize i) → Bool), |(Exp n).Y i j w| ≤ B)
    (hm0pos : ∀ n i, 0 < (Exp n).m0 i) (hm1pos : ∀ n i, 0 < (Exp n).m1 i)
    (hcount0 : ∀ n i (w : Fin ((Exp n).gsize i) → Bool), ((Exp n).ψ i).p w ≠ 0 →
      (∑ j, if w j = false then (1 : ℝ) else 0) = (Exp n).m0 i)
    (hcount1 : ∀ n i (w : Fin ((Exp n).gsize i) → Bool), ((Exp n).ψ i).p w ≠ 0 →
      (∑ j, if w j = true then (1 : ℝ) else 0) = (Exp n).m1 i)
    (hCpos : ∀ n, 0 < (Exp n).C)
    (hCN : ∀ n, (Exp n).C ≤ (Fintype.card (Exp n).ι : ℝ))
    (hCtendsto : Tendsto (fun n => (Exp n).C) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Exp n).jointD.Pr (fun sw => ε ≤ |(Exp n).estD sw - (Exp n).DEbar|))
      atTop (𝓝 0) := by
  have hVar0 : Tendsto (fun n => (Exp n).directVar) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => 36 * B ^ 2 / (Exp n).C) atTop (𝓝 0) :=
      hCtendsto.const_div_atTop (36 * B ^ 2)
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hupper
    · rw [← (Exp n).var_estD]
      exact (Exp n).jointD.E_nonneg (fun _ => sq_nonneg _)
    · let E := Exp n
      have hNnat0 : Fintype.card E.ι ≠ 0 := by
        intro h
        apply E.hN
        simp [h]
      have hNnat1 : Fintype.card E.ι ≠ 1 := by
        intro h
        apply E.hN1
        norm_num [h]
      have hN2 : 2 ≤ Fintype.card E.ι := by omega
      have hNr : 0 < (Fintype.card E.ι : ℝ) := by positivity
      have hN2r : (2 : ℝ) ≤ (Fintype.card E.ι : ℝ) := by exact_mod_cast hN2
      have hN1r : 0 < (Fintype.card E.ι : ℝ) - 1 := by linarith
      have hg0 : ∀ i w, (E.ψ i).p w ≠ 0 →
          |groupEst E.Y i false (E.m0 i) w| ≤ B := fun i w hw =>
        abs_groupEst_le_of_bounded E.Y i false (hm0pos n i) (hY n i) w (hcount0 n i w hw)
      have hg1 : ∀ i w, (E.ψ i).p w ≠ 0 →
          |groupEst E.Y i true (E.m1 i) w| ≤ B := fun i w hw =>
        abs_groupEst_le_of_bounded E.Y i true (hm1pos n i) (hY n i) w (hcount1 n i w hw)
      have hdiff : ∀ i w, (E.ψ i).p w ≠ 0 →
          |groupEst E.Y i false (E.m0 i) w - groupEst E.Y i true (E.m1 i) w| ≤ 2 * B := by
        intro i w hw
        calc
          |groupEst E.Y i false (E.m0 i) w - groupEst E.Y i true (E.m1 i) w|
              ≤ |groupEst E.Y i false (E.m0 i) w| +
                  |groupEst E.Y i true (E.m1 i) w| := abs_sub _ _
          _ ≤ 2 * B := by linarith [hg0 i w hw, hg1 i w hw]
      have hgm0 : ∀ i, |groupMean E.ψ E.Y i false| ≤ B := by
        intro i
        rw [← E_groupEst E.ψ E.Y i false (E.m0 i) (E.hm0 i) (E.hn i) (E.hprop0 i)]
        exact abs_E_le_of_abs_le_on_support (E.ψ i) _ (hg0 i)
      have hgm1 : ∀ i, |groupMean E.ψ E.Y i true| ≤ B := by
        intro i
        rw [← E_groupEst E.ψ E.Y i true (E.m1 i) (E.hm1 i) (E.hn i) (E.hprop1 i)]
        exact abs_E_le_of_abs_le_on_support (E.ψ i) _ (hg1 i)
      let μ : E.ι → ℝ := fun i => groupMean E.ψ E.Y i false - groupMean E.ψ E.Y i true
      have hμ : ∀ i, |μ i| ≤ 2 * B := by
        intro i
        calc
          |μ i| ≤ |groupMean E.ψ E.Y i false| + |groupMean E.ψ E.Y i true| := abs_sub _ _
          _ ≤ 2 * B := by linarith [hgm0 i, hgm1 i]
      have hμbar : |(∑ i, μ i) / (Fintype.card E.ι : ℝ)| ≤ 2 * B := by
        rw [abs_div, abs_of_pos hNr]
        calc
          |∑ i, μ i| / (Fintype.card E.ι : ℝ)
              ≤ (∑ i, |μ i|) / (Fintype.card E.ι : ℝ) :=
                div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hNr.le
          _ ≤ (∑ _i : E.ι, 2 * B) / (Fintype.card E.ι : ℝ) :=
                div_le_div_of_nonneg_right
                  (Finset.sum_le_sum (fun i _ => hμ i)) hNr.le
          _ = 2 * B := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            field_simp
      have hSmu : SmuVar μ ≤ 32 * B ^ 2 := by
        unfold SmuVar
        apply (div_le_iff₀ hN1r).2
        calc
          ∑ i, (μ i - (∑ i, μ i) / (Fintype.card E.ι : ℝ)) ^ 2
              ≤ ∑ _i : E.ι, (4 * B) ^ 2 := by
                refine Finset.sum_le_sum (fun i _ => ?_)
                have hdev : |μ i - (∑ i, μ i) / (Fintype.card E.ι : ℝ)| ≤ 4 * B := by
                  calc
                    |μ i - (∑ i, μ i) / (Fintype.card E.ι : ℝ)|
                        ≤ |μ i| + |(∑ i, μ i) / (Fintype.card E.ι : ℝ)| := abs_sub _ _
                    _ ≤ 4 * B := by linarith [hμ i, hμbar]
                rw [← sq_abs]
                exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdev
          _ = (Fintype.card E.ι : ℝ) * (4 * B) ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ ≤ 32 * B ^ 2 * ((Fintype.card E.ι : ℝ) - 1) := by
                have hNupper : (Fintype.card E.ι : ℝ) ≤
                    2 * ((Fintype.card E.ι : ℝ) - 1) := by linarith
                nlinarith [sq_nonneg B]
      have hwithin : ∑ i, (E.ψ i).Var
          (fun w => groupEst E.Y i false (E.m0 i) w - groupEst E.Y i true (E.m1 i) w)
          ≤ (Fintype.card E.ι : ℝ) * (2 * B) ^ 2 := by
        calc
          ∑ i, (E.ψ i).Var
              (fun w => groupEst E.Y i false (E.m0 i) w - groupEst E.Y i true (E.m1 i) w)
              ≤ ∑ _i : E.ι, (2 * B) ^ 2 := by
                refine Finset.sum_le_sum (fun i _ => ?_)
                exact Var_le_sq_of_abs_le (E.ψ i) _ (by positivity) (hdiff i)
          _ = (Fintype.card E.ι : ℝ) * (2 * B) ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (1 - E.C / (Fintype.card E.ι : ℝ)) / E.C * SmuVar μ +
          1 / (E.C * (Fintype.card E.ι : ℝ)) *
            (∑ i, (E.ψ i).Var
              (fun w => groupEst E.Y i false (E.m0 i) w - groupEst E.Y i true (E.m1 i) w))
        ≤ 36 * B ^ 2 / E.C
      have hCr : 0 < E.C := hCpos n
      have hCNr : E.C ≤ (Fintype.card E.ι : ℝ) := hCN n
      have hfrac : E.C / (Fintype.card E.ι : ℝ) ≤ 1 := (div_le_one hNr).2 hCNr
      have hcoef : 0 ≤ (1 - E.C / (Fintype.card E.ι : ℝ)) / E.C := by
        exact div_nonneg (sub_nonneg.mpr hfrac) hCr.le
      have hcoef_le : (1 - E.C / (Fintype.card E.ι : ℝ)) / E.C ≤ 1 / E.C := by
        apply div_le_div_of_nonneg_right _ hCr.le
        have : 0 ≤ E.C / (Fintype.card E.ι : ℝ) := div_nonneg hCr.le hNr.le
        linarith
      have hwithinCoef : 0 ≤ 1 / (E.C * (Fintype.card E.ι : ℝ)) := by positivity
      have hSmuNonneg : 0 ≤ SmuVar μ := by
        unfold SmuVar
        positivity
      have honeC : 0 ≤ 1 / E.C := by positivity
      calc
        _ ≤ (1 / E.C) * (32 * B ^ 2) +
            (1 / (E.C * (Fintype.card E.ι : ℝ))) *
              ((Fintype.card E.ι : ℝ) * (2 * B) ^ 2) :=
          add_le_add (mul_le_mul hcoef_le hSmu hSmuNonneg honeC)
            (mul_le_mul_of_nonneg_left hwithin hwithinCoef)
        _ = 36 * B ^ 2 / E.C := by field_simp; ring
  refine squeeze_zero (g := fun n => (Exp n).directVar / ε ^ 2)
      (fun n => ?_) (fun n => ?_) ?_
  · -- `0 ≤ Pr_n`: a probability is nonnegative.
    exact (Exp n).jointD.Pr_nonneg _
  · -- `Pr_n ≤ directVar_n / ε²` by Chebyshev, recentering via unbiasedness.
    have hcenter : (Exp n).DEbar = (Exp n).jointD.E (Exp n).estD := ((Exp n).E_estD).symm
    change (Exp n).jointD.Pr (fun sw => ε ≤ |(Exp n).estD sw - (Exp n).DEbar|)
        ≤ (Exp n).directVar / ε ^ 2
    rw [hcenter, ← (Exp n).var_estD]
    exact (Exp n).jointD.chebyshev (Exp n).estD hε
  · -- `directVar_n / ε² → 0 / ε² = 0`.
    simpa using hVar0.div_const (ε ^ 2)

end TwoStageInterference
end Experimentation
end Causalean
