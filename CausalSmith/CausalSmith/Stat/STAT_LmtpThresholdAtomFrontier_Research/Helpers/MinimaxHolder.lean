/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxMembership
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.BumpHolder
import Causalean.Stat.Nonparametric.Approximation.HolderTaylor

/-! # Taylor certification for the localized minimax bump -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Set
open scoped BigOperators

noncomputable section

private lemma ellOf_eq_holderDerivOrder (beta : ℝ) :
    ellOf beta = Causalean.Stat.Nonparametric.holderDerivOrder beta := rfl

/-- A global smoothness and top-derivative Hölder bound imply the exact
within-interval Taylor remainder convention used by `HolderRegression`. The result uses [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hf` condition](hyp:hf), [the `htop` condition](hyp:htop). [This is the stated conclusion](goal).
-/
lemma taylorWithin_remainder_of_holder
    {f : ℝ → ℝ} {beta L : ℝ} (hbeta : 0 < beta) (hL : 0 ≤ L)
    (hf : ContDiff ℝ (ellOf beta) f)
    (htop : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv (ellOf beta) f x - iteratedDeriv (ellOf beta) f y| ≤
        L * |x - y| ^ (beta - (ellOf beta : ℝ))) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |f t - ∑ j ∈ Finset.range (ellOf beta + 1),
          iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) s *
            (t - s) ^ j / (Nat.factorial j : ℝ)| ≤ L * |t - s| ^ beta := by
  intro s hs t ht
  have hrem := Causalean.Stat.Nonparametric.holder_taylor_remainder
    (f := f) (M := L) (β := beta) (lo := 0) (hi := 1) (t := s) (a := t)
    hbeta hL hs ht (by simpa [ellOf_eq_holderDerivOrder] using hf)
    (by simpa [ellOf_eq_holderDerivOrder] using htop)
  have hpoly :
      Causalean.Stat.Nonparametric.taylorPoly (ellOf beta) f s t =
        ∑ j ∈ Finset.range (ellOf beta + 1),
          iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) s *
            (t - s) ^ j / (Nat.factorial j : ℝ) := by
    unfold Causalean.Stat.Nonparametric.taylorPoly
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ ellOf beta := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hwithin : iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) s =
        iteratedDeriv j f s := by
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
        ((hf.of_le (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hjle))).contDiffAt) hs
    rw [hwithin]
    ring
  rw [← hpoly]
  calc
    |f t - Causalean.Stat.Nonparametric.taylorPoly (ellOf beta) f s t| ≤
        L / (Nat.factorial (ellOf beta) : ℝ) * |t - s| ^ beta := by
          simpa [ellOf_eq_holderDerivOrder] using hrem
    _ ≤ L * |t - s| ^ beta := by
      have hfacNat : 1 ≤ Nat.factorial (ellOf beta) :=
        Nat.succ_le_iff.mpr (Nat.factorial_pos _)
      have hfac : (1 : ℝ) ≤ Nat.factorial (ellOf beta) := by exact_mod_cast hfacNat
      have hdiv : L / (Nat.factorial (ellOf beta) : ℝ) ≤ L := by
        exact div_le_self hL hfac
      exact mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg (abs_nonneg _) _)

/-- Fixed amplitude and the localized smooth bump satisfy the paper's exact
Taylor-remainder Hölder member uniformly over all admissible centers and bandwidths. The result uses [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL). [This is the stated conclusion](goal).
-/
lemma exists_minimaxBump_amplitude (beta L : ℝ) (hbeta : 0 < beta) (hL : 0 < L) :
    ∃ amplitude : ℝ, 0 < amplitude ∧ amplitude ≤ 1 / 4 ∧
      ∀ {delta h : ℝ}, 0 ≤ delta → delta ≤ 1 → 0 < h → h ≤ 1 →
        let q := fun a : ℝ => amplitude * h ^ beta *
          CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
        ContinuousOn (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) 1) ∧
        (∀ a ∈ Set.Icc (0 : ℝ) 1, 1 / 2 + q a ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |(1 / 2 + q t) - ∑ j ∈ Finset.range (ellOf beta + 1),
              iteratedDerivWithin j (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) 1) s *
                (t - s) ^ j / (Nat.factorial j : ℝ)| ≤ L * |t - s| ^ beta := by
  let M := min L 1
  have hM : 0 < M := lt_min hL zero_lt_one
  obtain ⟨amplitude, hamp, hampM, hball⟩ :=
    CausalSmith.Stat.DoseResponseMinimax.doseBump_holder_gate beta M 0 1 hbeta hM
  refine ⟨amplitude, hamp, hampM.trans ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right (min_le_right L 1) (by norm_num)).trans_eq (by norm_num)
  intro delta h hdelta hdelta1 hh hh1
  dsimp only
  let q := fun a : ℝ => amplitude * h ^ beta *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  have hqball := hball (ζ := (1 : ℝ)) (h := h) (Or.inr rfl) hh hh1
  have hsmoothTop : ContDiff ℝ (⊤ : ℕ∞) q := by
    dsimp [q]
    exact contDiff_const.mul
      (CausalSmith.Stat.DoseResponseMinimax.doseContDiffBump.contDiff.comp
        ((contDiff_id.sub contDiff_const).div_const h))
  have hsmooth : ContDiff ℝ (ellOf beta) (fun a => 1 / 2 + q a) :=
    contDiff_const.add (hsmoothTop.of_le
      (WithTop.coe_le_coe.mpr
        (show (ellOf beta : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  have hcont : ContinuousOn (fun a => 1 / 2 + q a) (Set.Icc (0 : ℝ) 1) :=
    hsmooth.continuous.continuousOn
  have hqnonneg (a : ℝ) : 0 ≤ q a := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hamp.le (Real.rpow_nonneg hh.le _))
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqle (a : ℝ) : q a ≤ 1 / 4 := by
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one ((a - delta) / h)
    have hhpow : h ^ beta ≤ 1 := Real.rpow_le_one hh.le hh1 hbeta.le
    have ha4 : amplitude ≤ 1 / 4 := hampM.trans
      ((div_le_div_of_nonneg_right (min_le_right L 1) (by norm_num)).trans_eq (by norm_num))
    calc
      q a ≤ amplitude * h ^ beta * 1 :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg hamp.le (Real.rpow_nonneg hh.le _))
      _ ≤ amplitude * 1 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hhpow hamp.le
      _ ≤ 1 / 4 := by simpa using ha4
  refine ⟨hcont, ?_, ?_⟩
  · intro a ha
    exact ⟨by linarith [hqnonneg a], by linarith [hqle a]⟩
  apply taylorWithin_remainder_of_holder hbeta hL.le hsmooth
  intro x hx y hy
  have hxd : x - delta ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hyd : y - delta ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have htop := hqball.2.2 (x - delta)
    (by simpa [CausalSmith.Stat.DoseResponseMinimax.doseWindow] using hxd)
    (y - delta)
    (by simpa [CausalSmith.Stat.DoseResponseMinimax.doseWindow] using hyd)
  have htranslate (j : ℕ) (a : ℝ) :
      iteratedDeriv j q a =
        iteratedDeriv j
          (fun u : ℝ => amplitude * h ^ beta *
            CausalSmith.Stat.DoseResponseMinimax.doseBump ((u - 0) / h))
          (a - delta) := by
    let f0 := fun u : ℝ => amplitude * h ^ beta *
      CausalSmith.Stat.DoseResponseMinimax.doseBump ((u - 0) / h)
    have hfun : q = fun a => f0 (a - delta) := by
      funext a
      simp [q, f0]
    change iteratedDeriv j q a = iteratedDeriv j f0 (a - delta)
    rw [hfun]
    exact congrFun (iteratedDeriv_comp_sub_const (n := j) (f := f0) (s := delta)) a
  have hdist : |(x - delta) - (y - delta)| = |x - y| := by ring_nf
  have htopq :
      |iteratedDeriv (ellOf beta) q x - iteratedDeriv (ellOf beta) q y| ≤
        M * |x - y| ^ (beta - (ellOf beta : ℝ)) := by
    rw [htranslate (ellOf beta) x, htranslate (ellOf beta) y]
    simpa [ellOf, hdist] using htop
  have hML : M ≤ L := min_le_left _ _
  have htopL := htopq.trans (mul_le_mul_of_nonneg_right hML
    (Real.rpow_nonneg (abs_nonneg _) _))
  by_cases hell : ellOf beta = 0
  · simpa [hell, iteratedDeriv_zero] using htopL
  · have hellpos : 0 < ellOf beta := Nat.pos_of_ne_zero hell
    rw [iteratedDeriv_const_add hellpos (1 / 2 : ℝ),
      iteratedDeriv_const_add hellpos (1 / 2 : ℝ)]
    exact htopL

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
