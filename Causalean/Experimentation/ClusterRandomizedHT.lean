/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.Designs.ClusterRandomization
import Mathlib.Tactic.NormNum

/-!
# Middleton & Aronow (2015): cluster-randomized Horvitz-Thompson ATE

This file formalizes the cluster-randomized Horvitz-Thompson identity behind Middleton and
Aronow's average-treatment-effect result. Treatment is assigned independently by cluster, each
cluster has treated and control cluster-total potential outcomes, and inverse-probability weighting
recovers the finite-population average treatment effect after normalization by the total number of
units.

The file records the cluster Horvitz-Thompson treated/control totals, the unit-count denominator,
the normalized effect estimator, the normalized finite-population ATE estimand, and the
unbiasedness theorem (a direct consequence of the first-order cluster inclusion probability).
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace ClusterRandomizedHT

open DesignBased

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- For [a finite population of clusters](hyp:C), [cluster treatment probabilities](hyp:p),
[treated potential-outcome totals for the clusters](hyp:y1), and [a realized cluster
assignment](hyp:z), the [Horvitz–Thompson treated total](goal) is the sum, over clusters, of
each treated cluster's potential-outcome total weighted by the reciprocal of its treatment
probability. -/
noncomputable def htTreatedTotal (p y1 : C → ℝ) (z : C → Bool) : ℝ :=
  ∑ c, (treatInd c z / p c) * y1 c

/-- For [a finite population of clusters](hyp:C), [cluster treatment probabilities](hyp:p),
[control potential-outcome totals for the clusters](hyp:y0), and [a realized cluster
assignment](hyp:z), the [Horvitz–Thompson control total](goal) is the sum, over clusters, of
each untreated cluster's potential-outcome total weighted by the reciprocal of its control
probability. -/
noncomputable def htControlTotal (p y0 : C → ℝ) (z : C → Bool) : ℝ :=
  ∑ c, ((1 - treatInd c z) / (1 - p c)) * y0 c

/-- For [a finite population of clusters](hyp:C) and [the number of experimental units in each
cluster](hyp:n), the [total number of experimental units](goal) is the sum of the cluster sizes. -/
noncomputable def totalUnits (n : C → ℕ) : ℝ := ∑ c, (n c : ℝ)

/-- For [a finite population of clusters](hyp:C), [cluster treatment probabilities](hyp:p), [the
number of units in each cluster](hyp:n), [treated and control potential-outcome totals](hyp:y1,y0),
and [a realized cluster assignment](hyp:z), the [Middleton--Aronow Horvitz--Thompson average
treatment-effect estimator](goal) is the inverse-probability-weighted treated total minus control
total, divided by the total number of units. -/
noncomputable def htClusterEffect (p : C → ℝ) (n : C → ℕ) (y1 y0 : C → ℝ)
    (z : C → Bool) : ℝ :=
  (htTreatedTotal p y1 z - htControlTotal p y0 z) / totalUnits n

/-- For [a finite population of clusters](hyp:C), [the number of units in each cluster](hyp:n), and
[treated and control potential-outcome totals](hyp:y1,y0), the [finite-population average treatment
effect](goal) is the sum of treated-minus-control cluster totals divided by the total number of
units. -/
noncomputable def totalEffect (n : C → ℕ) (y1 y0 : C → ℝ) : ℝ :=
  (∑ c, (y1 c - y0 c)) / totalUnits n

/-- The HT treated total is unbiased for the treated-arm population total `∑ y1 c`: each cluster is
treated with probability `p c`, which the inverse weight `1 / p c` exactly undoes. -/
theorem E_htTreatedTotal (p y1 : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (hppos : ∀ c, 0 < p c) :
    (clusterDesign p hp0 hp1).E (htTreatedTotal p y1) = ∑ c, y1 c := by
  change (bernoulliDesign p hp0 hp1).E (fun z => ∑ c, treatInd c z / p c * y1 c)
    = ∑ c, y1 c
  rw [show (fun z => ∑ c, treatInd c z / p c * y1 c)
        = (fun z => ∑ c, y1 c / p c * treatInd c z) from
      funext (fun z => Finset.sum_congr rfl (fun c _ => by ring))]
  rw [FiniteDesign.E_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [FiniteDesign.E_const_mul _ (y1 c / p c) (treatInd c)]
  have hE : (bernoulliDesign p hp0 hp1).E (treatInd c) = p c := by
    -- `simp` no longer eta-expands the partially applied `treatInd c`, so state the
    -- goal in the applied form (defeq) and rewrite there.
    show (bernoulliDesign p hp0 hp1).E (fun z => (fun b => if b then (1 : ℝ) else 0) (z c))
        = p c
    rw [bernoulliDesign_E_treatInd p hp0 hp1 c (fun b => if b then (1 : ℝ) else 0)]
    norm_num
  rw [hE]
  exact div_mul_cancel₀ (y1 c) (hppos c).ne'

/-- The HT control total is unbiased for the control-arm population total `∑ y0 c`: each cluster
is a control with probability `1 − p c`, undone by the weight `1 / (1 − p c)`. -/
theorem E_htControlTotal (p y0 : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (hp1' : ∀ c, p c < 1) :
    (clusterDesign p hp0 hp1).E (htControlTotal p y0) = ∑ c, y0 c := by
  have hone : ∀ c, (bernoulliDesign p hp0 hp1).E (fun z => 1 - treatInd c z) = 1 - p c := by
    intro c
    rw [show (fun z => (1 : ℝ) - treatInd c z)
          = (fun z => (fun _ => (1 : ℝ)) z - treatInd c z) from rfl,
      FiniteDesign.E_sub, FiniteDesign.E_const]
    have hE : (bernoulliDesign p hp0 hp1).E (treatInd c) = p c := by
      -- `simp` no longer eta-expands the partially applied `treatInd c`, so state the
      -- goal in the applied form (defeq) and rewrite there.
      show (bernoulliDesign p hp0 hp1).E (fun z => (fun b => if b then (1 : ℝ) else 0) (z c))
          = p c
      rw [bernoulliDesign_E_treatInd p hp0 hp1 c (fun b => if b then (1 : ℝ) else 0)]
      norm_num
    rw [hE]
  change (bernoulliDesign p hp0 hp1).E
      (fun z => ∑ c, (1 - treatInd c z) / (1 - p c) * y0 c)
    = ∑ c, y0 c
  rw [show (fun z => ∑ c, (1 - treatInd c z) / (1 - p c) * y0 c)
        = (fun z => ∑ c, y0 c / (1 - p c) * (1 - treatInd c z)) from
      funext (fun z => Finset.sum_congr rfl (fun c _ => by ring))]
  rw [FiniteDesign.E_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [FiniteDesign.E_const_mul _ (y0 c / (1 - p c)) (fun z => 1 - treatInd c z), hone c]
  exact div_mul_cancel₀ (y0 c) (sub_ne_zero.mpr (hp1' c).ne')

/-- **Unbiasedness for the finite-population average treatment effect.** Consider cluster
randomization where each cluster `c` is assigned treatment with probability `p c`; suppose
[`p c` lies between `0` and `1`](hyp:hp0,hp1) and, more sharply, [`p c` lies strictly between
`0` and `1`](hyp:hppos,hp1'), and [the total number of units across clusters is
positive](hyp:hNpos). Then [the Middleton–Aronow Horvitz–Thompson estimator of the effect — the
inverse-probability-weighted treated-minus-control cluster-total contrast, normalized by the
total unit count — is unbiased for the finite-population average treatment effect, the analogous
unweighted contrast of the cluster-total potential outcomes normalized by the same unit
count](goal). -/
theorem E_htClusterEffect (p : C → ℝ) (n : C → ℕ) (y1 y0 : C → ℝ) (hp0 : ∀ c, 0 ≤ p c)
    (hp1 : ∀ c, p c ≤ 1) (hppos : ∀ c, 0 < p c) (hp1' : ∀ c, p c < 1)
    (hNpos : 0 < totalUnits n) :
    (clusterDesign p hp0 hp1).E (htClusterEffect p n y1 y0) = totalEffect n y1 y0 := by
  unfold htClusterEffect totalEffect
  have hNne : totalUnits n ≠ 0 := ne_of_gt hNpos
  rw [show (fun z => (htTreatedTotal p y1 z - htControlTotal p y0 z) / totalUnits n)
        = (fun z => (htTreatedTotal p y1 z - htControlTotal p y0 z) * (totalUnits n)⁻¹) from
      funext (fun z => by rw [div_eq_mul_inv])]
  rw [FiniteDesign.E_mul_const, FiniteDesign.E_sub, E_htTreatedTotal p y1 hp0 hp1 hppos,
    E_htControlTotal p y0 hp0 hp1 hp1', ← Finset.sum_sub_distrib, div_eq_mul_inv]

end ClusterRandomizedHT
end Experimentation
end Causalean
