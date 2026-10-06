module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialLocalRiskOrder

/-! # Sequential removal of the van Trees prior-radius penalty

This file separates the two limits in a local van Trees argument.  At a fixed
prior radius `R`, the prior Fisher-information term `40 / R ^ 2` remains after
the sample-size limit.  Only after transferring that fixed-radius bound to the
local asymptotic risk may one send `R` to infinity.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

/-- At fixed positive prior radius, convergence of the experiment information
gives convergence of the full reciprocal denominator, including the prior
information term. For [the displayed inputs and conditions](hyp:info,I,R,hI), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hinfo), these specify the stated inputs. -/
lemma tendsto_inv_info_add_priorRadius
    (info : ℕ → ℝ) (I R : ℝ) (hI : 0 < I)
    (hinfo : Tendsto info atTop (nhds I)) :
    Tendsto (fun n => 1 / (info n + 40 / R ^ 2)) atTop
      (nhds (1 / (I + 40 / R ^ 2))) := by
  have hdenom : Tendsto (fun n => info n + 40 / R ^ 2) atTop
      (nhds (I + 40 / R ^ 2)) :=
    hinfo.add tendsto_const_nhds
  have hdenom_ne : I + 40 / R ^ 2 ≠ 0 := by
    have hprior : 0 ≤ 40 / R ^ 2 := div_nonneg (by norm_num) (sq_nonneg R)
    exact ne_of_gt (hI.trans_le (le_add_of_nonneg_right hprior))
  exact tendsto_const_nhds.div hdenom hdenom_ne

/-- A finite-sample lower bound with a fixed prior radius first yields the
corresponding penalized reciprocal-information local asymptotic bound. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,H,hH,info,I,R,hI,hinfo,hlower), these specify the stated inputs. -/
lemma priorRadius_bound_le_localAsymptoticRisk {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p H : ℝ)
    (hH : 0 < H) (info : ℕ → ℝ) (I R : ℝ) (hI : 0 < I)
    (hinfo : Tendsto info atTop (nhds I))
    (hlower : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 / (info n + 40 / R ^ 2)) ≤
        localWorstRisk P θ p H n) :
    ENNReal.ofReal (1 / (I + 40 / R ^ 2)) ≤
      localAsymptoticRisk P θ p := by
  exact ofReal_le_localAsymptoticRisk_of_bayes_envelope
    P θ p H hH _ _ (tendsto_inv_info_add_priorRadius info I R hI hinfo) hlower

/-- Correct two-step assembly for a family of finite-sample van Trees bounds. Under [the stated assumptions](hyp:hI,hH,hinfo,hlower), [the inv information le local Asymptotic Risk of prior Radius family](goal).

Under the stated assumptions, the inv information le local Asymptotic Risk of prior Radius family.

For every positive prior radius, the sample-size limit retains the penalty `40 / R²`. The conclusion removes that penalty only through a second limit along the radii `R = k + 1`. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. -/
lemma inv_information_le_localAsymptoticRisk_of_priorRadius_family
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p I : ℝ)
    (H : ℝ → ℝ) (info : ℝ → ℕ → ℝ) (hI : 0 < I)
    (hH : ∀ R, 0 < R → 0 < H R)
    (hinfo : ∀ R, 0 < R → Tendsto (info R) atTop (nhds I))
    (hlower : ∀ R, 0 < R → ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 / (info R n + 40 / R ^ 2)) ≤
        localWorstRisk P θ p (H R) n) :
    ENNReal.ofReal (1 / I) ≤ localAsymptoticRisk P θ p := by
  let radius : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hradius_pos (k : ℕ) : 0 < radius k := by
    dsimp [radius]
    positivity
  have hfixed (k : ℕ) :
      ENNReal.ofReal (1 / (I + 40 / (radius k) ^ 2)) ≤
        localAsymptoticRisk P θ p :=
    priorRadius_bound_le_localAsymptoticRisk
      P θ p (H (radius k)) (hH _ (hradius_pos k))
      (info (radius k)) I (radius k) hI
      (hinfo _ (hradius_pos k)) (hlower _ (hradius_pos k))
  have hinv_radius : Tendsto (fun k : ℕ => 1 / radius k) atTop (nhds 0) := by
    simpa only [radius] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0))
  have hinv_radius' : Tendsto (fun k : ℕ => (radius k)⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using hinv_radius
  have hprior : Tendsto (fun k : ℕ => 40 / (radius k) ^ 2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_const_nhds.mul (hinv_radius'.pow 2) :
        Tendsto (fun k : ℕ => (40 : ℝ) * ((radius k)⁻¹) ^ 2)
          atTop (nhds ((40 : ℝ) * 0 ^ 2)))
  have hrecip : Tendsto (fun k : ℕ => 1 / (I + 40 / (radius k) ^ 2))
      atTop (nhds (1 / I)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hdenom : Tendsto (fun k : ℕ => I + 40 / (radius k) ^ 2)
        atTop (nhds I) := by
      simpa only [add_zero] using tendsto_const_nhds.add hprior
    change Tendsto ((fun _ : ℕ => (1 : ℝ)) /
      (fun k : ℕ => I + 40 / (radius k) ^ 2)) atTop (nhds (1 / I))
    exact hone.div hdenom (ne_of_gt hI)
  have hofReal : Tendsto
      (fun k : ℕ => ENNReal.ofReal (1 / (I + 40 / (radius k) ^ 2)))
      atTop (nhds (ENNReal.ofReal (1 / I))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrecip
  exact le_of_tendsto' hofReal hfixed

end CausalSmith.Stat.LdpAteEfficiencySurface
