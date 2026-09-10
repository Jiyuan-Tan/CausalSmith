/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.PiTransport
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Occupancy-weighted residual means: design statistics

This module defines totalized group/arm counts and residual sample means for a
finite product sample.  Every zero-count boundary is part of the definition,
including the completely empty sample and an empty group type.  It also exposes
the measurability API needed to integrate the statistics under a product law.
-/

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

variable {Omega kappa : Type*} [MeasurableSpace Omega]
  [Fintype kappa] [DecidableEq kappa]
  [MeasurableSpace kappa] [MeasurableSingletonClass kappa]

/-- Given [a sample space](hyp:Omega), [a group-label space](hyp:kappa),
[a group-label map](hyp:group), [a Boolean arm-assignment map](hyp:arm), [an arm label](hyp:a),
and [a group label](hyp:k), the [arm--group event](goal) is the set of sample-space outcomes
whose group and arm labels equal the requested labels. -/
def armGroupEvent (group : Omega -> kappa) (arm : Omega -> Bool)
    (a : Bool) (k : kappa) : Set Omega :=
  {omega | group omega = k ∧ arm omega = a}

/-- Given [a sample space](hyp:Omega), [a group-label space](hyp:kappa),
[a group-label map](hyp:group), and [a group label](hyp:k), the [group event](goal) is the set
of sample-space outcomes having that group label, irrespective of arm assignment. -/
def groupEvent (group : Omega -> kappa) (k : kappa) : Set Omega :=
  {omega | group omega = k}

/-- Given [a sample space](hyp:Omega), [a group-label space](hyp:kappa),
[a real-valued outcome](hyp:Y), [a supplied real center for every arm and group](hyp:center),
[an arm label](hyp:a), [a group label](hyp:k), and [a sample-space outcome](hyp:omega), the
[arm--group residual](goal) is that outcome minus the center supplied for its requested arm and group. -/
def armGroupResidual (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (a : Bool) (k : kappa) (omega : Omega) : Real :=
  Y omega - center a k

/-- Given [a sample space](hyp:Omega), [a group-label space](hyp:kappa),
[a group-label map](hyp:group), [a Boolean arm-assignment map](hyp:arm), [a real-valued
outcome](hyp:Y), [arm--group centers](hyp:center), [an arm label](hyp:a), and [a group label](hyp:k),
the [supported arm--group residual](goal) equals the corresponding residual on the requested
arm--group event and zero outside that event. -/
noncomputable def supportedArmGroupResidual (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (a : Bool) (k : kappa) : Omega -> Real :=
  (armGroupEvent group arm a k).indicator (armGroupResidual Y center a k)

/-- Given [a sample space](hyp:Omega), [a group-label space](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), and [a sample of that size](hyp:z), the [sample design](goal)
maps every sample coordinate to its pair of group and arm labels. -/
def sampleDesign {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) : Fin n -> kappa × Bool :=
  fun i => (group (z i), arm (z i))

/-- Given [a sample space](hyp:Omega), [a group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), [a sample](hyp:z), [an arm label](hyp:a), and [a group label](hyp:k),
the [arm--group count](goal) is the number of sample coordinates whose two labels equal those requested. -/
def groupArmCount {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) (a : Bool) (k : kappa) : Nat :=
  (Finset.univ.filter fun i => group (z i) = k ∧ arm (z i) = a).card

/-- Given [a sample space](hyp:Omega), [a group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), [a sample](hyp:z), and [a group label](hyp:k), the [group count](goal)
is the sum of the sample counts in that group for the false and true arm labels. -/
def groupCount {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) (k : kappa) : Nat :=
  groupArmCount group arm z false k + groupArmCount group arm z true k

/-- Given [a sample space](hyp:Omega), [a group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), [a sample](hyp:z), and [a group label](hyp:k), the [usable-group
condition](goal) holds exactly when [the count in the false arm is positive](step:1) and [the
count in the true arm is positive](step:2). -/
def usableGroup {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) (k : kappa) : Prop :=
  0 < groupArmCount group arm z false k ∧
    0 < groupArmCount group arm z true k

/-- Given [a sample space](hyp:Omega), [a finite group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), and [a sample](hyp:z), the [usable-group total](goal) is the sum
of group counts over precisely those groups represented by both arm labels. -/
noncomputable def usableGroupTotal {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (z : Fin n -> Omega) : Nat := by
  classical
  exact ∑ k, if usableGroup group arm z k then groupCount group arm z k else 0

/-- Given [a sample space](hyp:Omega), [a group-label space](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), [a real-valued outcome](hyp:Y), [arm--group centers](hyp:center),
[a sample](hyp:z), [an arm label](hyp:a), and [a group label](hyp:k), the [arm--group residual
sum](goal) adds the supported residuals of all sample coordinates. -/
noncomputable def armResidualSum {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (z : Fin n -> Omega) (a : Bool) (k : kappa) : Real :=
  ∑ i, supportedArmGroupResidual group arm Y center a k (z i)

/-- Given [a sample space](hyp:Omega), [a group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), [a real-valued outcome](hyp:Y), [arm--group centers](hyp:center),
[a sample](hyp:z), [an arm label](hyp:a), and [a group label](hyp:k), the [totalized arm--group
residual mean](goal) is its residual sum divided by its count when that count is positive, and zero otherwise. -/
noncomputable def armResidualMean {n : Nat} (group : Omega -> kappa) (arm : Omega -> Bool)
    (Y : Omega -> Real) (center : Bool -> kappa -> Real)
    (z : Fin n -> Omega) (a : Bool) (k : kappa) : Real :=
  if 0 < groupArmCount group arm z a k then
    (groupArmCount group arm z a k : Real)⁻¹ *
      armResidualSum group arm Y center z a k
  else 0

/-- Given [a measurable sample space](hyp:Omega), [a finite group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a measure on the sample space](hyp:_mu), [a group-label map](hyp:group),
[a Boolean arm-assignment map](hyp:arm), [a real-valued outcome](hyp:Y), [arm--group centers](hyp:center),
and [a sample](hyp:z), the [occupancy-weighted residual statistic](goal) is the usable-group-occupancy-weighted
average of treated-minus-control residual means, totalized to zero when no group is usable.

The measure fixes the intended public API but does not alter this sample statistic. -/
noncomputable def occupancyWeightedResidual {n : Nat} (_mu : Measure Omega)
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (z : Fin n -> Omega) : Real := by
  classical
  exact if 0 < usableGroupTotal group arm z then
      (usableGroupTotal group arm z : Real)⁻¹ *
        ∑ k, if usableGroup group arm z k then
          (groupCount group arm z k : Real) *
            (armResidualMean group arm Y center z true k -
              armResidualMean group arm Y center z false k)
        else 0
    else 0

/-- Given [a sample space](hyp:Omega), [a finite group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), and [a sample](hyp:z), the [inverse usable-group total](goal) is
the reciprocal usable-group total when that total is positive and is zero otherwise. -/
noncomputable def inverseUsableGroupTotal {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (z : Fin n -> Omega) : Real :=
  if 0 < usableGroupTotal group arm z then
    (usableGroupTotal group arm z : Real)⁻¹
  else 0

/-- Given [a sample space](hyp:Omega), [a finite group-label space whose labels can be compared for equality](hyp:kappa),
[a nonnegative integer sample size](hyp:n), [a group-label map](hyp:group), [a Boolean
arm-assignment map](hyp:arm), and [a sample](hyp:z), the [occupancy design-variance factor](goal)
is the squared reciprocal usable-group total times the sum, over usable groups, of squared group
counts times the two reciprocal arm counts, and is zero when no group is usable. -/
noncomputable def occupancyDesignVarianceFactor {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (z : Fin n -> Omega) : Real := by
  classical
  exact if 0 < usableGroupTotal group arm z then
      (usableGroupTotal group arm z : Real)⁻¹ ^ 2 *
        ∑ k, if usableGroup group arm z k then
          (groupCount group arm z k : Real) ^ 2 *
            ((groupArmCount group arm z true k : Real)⁻¹ +
              (groupArmCount group arm z false k : Real)⁻¹)
        else 0
    else 0

/-- A [measurable group label](hyp:hgroup) has [measurable group fibers](goal). -/
lemma measurableSet_groupEvent (group : Omega -> kappa) (hgroup : Measurable group)
    (k : kappa) : MeasurableSet (groupEvent group k) := by
  change MeasurableSet (group ⁻¹' {k})
  exact (measurableSet_singleton k).preimage hgroup

/-- [Measurable group and arm labels](hyp:hgroup,harm) have [measurable joint
arm/group fibers](goal). -/
lemma measurableSet_armGroupEvent (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (a : Bool) (k : kappa) :
    MeasurableSet (armGroupEvent group arm a k) := by
  rw [show armGroupEvent group arm a k =
      groupEvent group k ∩ {omega | arm omega = a} by ext omega; simp [armGroupEvent, groupEvent]]
  exact (measurableSet_groupEvent group hgroup k).inter
    ((measurableSet_singleton a).preimage harm)

/-- Restricting a measurable function to a joint arm/group cell — keeping its values on the
cell and setting it to zero outside — leaves it measurable, whenever the group and arm labels
are measurable.

This is the side-condition-free form of `Measurable.indicator` for these cells: it discharges
the cell's own measurability, so the function-property tactics can apply it with nothing left
over to prove. -/
@[fun_prop]
lemma measurable_armGroupEvent_indicator {beta : Type*} [MeasurableSpace beta] [Zero beta]
    (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (a : Bool) (k : kappa)
    {f : Omega -> beta} (hf : Measurable f) :
    Measurable ((armGroupEvent group arm a k).indicator f) :=
  hf.indicator (measurableSet_armGroupEvent group arm hgroup harm a k)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the coordinatewise
finite design measurable](goal). -/
@[fun_prop]
lemma measurable_sampleDesign {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (sampleDesign (n := n) group arm) := by
  apply measurable_pi_lambda
  intro i
  exact (hgroup.comp (measurable_pi_apply i :
    Measurable fun z : Fin n -> Omega => z i)).prodMk
    (harm.comp (measurable_pi_apply i :
      Measurable fun z : Fin n -> Omega => z i))

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [each fixed
arm/group count measurable on a finite product sample](goal). -/
@[fun_prop]
lemma measurable_groupArmCount {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (a : Bool) (k : kappa) :
    Measurable (fun z : Fin n -> Omega => groupArmCount group arm z a k) := by
  let count : (Fin n -> kappa × Bool) -> Nat := fun d =>
    (Finset.univ.filter fun i => (d i).1 = k ∧ (d i).2 = a).card
  have hcount : Measurable count := Measurable.of_discrete
  change Measurable (count ∘ sampleDesign group arm)
  exact hcount.comp (measurable_sampleDesign group arm hgroup harm)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [each fixed group
count measurable on the finite product sample space](goal). -/
@[fun_prop]
lemma measurable_groupCount {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (k : kappa) :
    Measurable (fun z : Fin n -> Omega => groupCount group arm z k) := by
  unfold groupCount
  change Measurable ((fun z : Fin n -> Omega => groupArmCount group arm z false k) +
    fun z => groupArmCount group arm z true k)
  exact (measurable_groupArmCount group arm hgroup harm false k).add
    (measurable_groupArmCount group arm hgroup harm true k)

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the event that a
fixed empirical group has both arms represented measurable](goal). -/
lemma measurableSet_usableGroup {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm)
    (k : kappa) :
    MeasurableSet {z : Fin n -> Omega | usableGroup group arm z k} := by
  have hfalse := measurable_groupArmCount (n := n) group arm hgroup harm false k
  have htrue := measurable_groupArmCount (n := n) group arm hgroup harm true k
  exact (measurableSet_lt measurable_const hfalse).inter
    (measurableSet_lt measurable_const htrue)

/-- A quantity defined by two branches, selected according to whether a fixed empirical group
has both arms represented, is measurable whenever both branches are and the group and arm
labels are measurable.

This is the side-condition-free form of `Measurable.ite` for the usable-group test. -/
@[fun_prop]
lemma measurable_usableGroup_ite {n : Nat} {beta : Type*} [MeasurableSpace beta]
    (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm) (k : kappa)
    [DecidablePred (fun z : Fin n -> Omega => usableGroup group arm z k)]
    {f g : (Fin n -> Omega) -> beta} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z : Fin n -> Omega =>
      if usableGroup group arm z k then f z else g z) :=
  Measurable.ite (measurableSet_usableGroup group arm hgroup harm k) hf hg

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the total occupancy
in empirically usable groups measurable](goal). -/
@[fun_prop]
lemma measurable_usableGroupTotal {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) := by
  classical
  unfold usableGroupTotal
  apply Finset.measurable_sum
  intro k hk
  exact Measurable.ite (measurableSet_usableGroup group arm hgroup harm k)
    (measurable_groupCount group arm hgroup harm k) measurable_const

/-- A [measurable outcome](hyp:hY) makes [each arm/group-centered residual
measurable](goal). -/
@[fun_prop]
lemma measurable_armGroupResidual (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (armGroupResidual Y center a k) := by
  unfold armGroupResidual
  change Measurable (Y - fun _ => center a k)
  exact hY.sub measurable_const

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[each residual restricted to its own arm/group cell measurable](goal). -/
@[fun_prop]
lemma measurable_supportedArmGroupResidual (group : Omega -> kappa)
    (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (supportedArmGroupResidual group arm Y center a k) := by
  unfold supportedArmGroupResidual
  exact (measurable_armGroupResidual Y center hY a k).indicator
    (measurableSet_armGroupEvent group arm hgroup harm a k)

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[each arm/group residual sum measurable on the finite product sample
space](goal). -/
@[fun_prop]
lemma measurable_armResidualSum {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (fun z : Fin n -> Omega =>
      armResidualSum group arm Y center z a k) := by
  classical
  unfold armResidualSum
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_supportedArmGroupResidual group arm Y center hgroup harm hY a k).comp
    (measurable_pi_apply i : Measurable fun z : Fin n -> Omega => z i)

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[each zero-safe arm/group residual mean measurable on the finite product sample
space](goal). -/
@[fun_prop]
lemma measurable_armResidualMean {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) (a : Bool) (k : kappa) :
    Measurable (fun z : Fin n -> Omega =>
      armResidualMean group arm Y center z a k) := by
  let count := fun z : Fin n -> Omega => groupArmCount group arm z a k
  have hcount : Measurable count :=
    measurable_groupArmCount group arm hgroup harm a k
  have hpos : MeasurableSet {z | 0 < count z} :=
    measurableSet_lt measurable_const hcount
  have hcast : Measurable (fun z => (count z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hcount
  unfold armResidualMean
  exact Measurable.ite hpos
    (hcast.inv.mul (measurable_armResidualSum group arm Y center hgroup harm hY a k))
    measurable_const

/-- [Measurable group labels, arm labels, and outcomes](hyp:hgroup,harm,hY) make
[the zero-safe occupancy-weighted residual measurable on the finite product
sample space](goal). -/
@[fun_prop]
lemma measurable_occupancyWeightedResidual {n : Nat} (mu : Measure Omega)
    (group : Omega -> kappa) (arm : Omega -> Bool) (Y : Omega -> Real)
    (center : Bool -> kappa -> Real) (hgroup : Measurable group)
    (harm : Measurable arm) (hY : Measurable Y) :
    Measurable (occupancyWeightedResidual (n := n) mu group arm Y center) := by
  classical
  have htotal : Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) :=
    measurable_usableGroupTotal group arm hgroup harm
  have hpos : MeasurableSet {z : Fin n -> Omega |
      0 < usableGroupTotal group arm z} :=
    measurableSet_lt measurable_const htotal
  have htotalCast : Measurable (fun z : Fin n -> Omega =>
      (usableGroupTotal group arm z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htotal
  have hsum : Measurable (fun z : Fin n -> Omega =>
      ∑ k, if usableGroup group arm z k then
        (groupCount group arm z k : Real) *
          (armResidualMean group arm Y center z true k -
            armResidualMean group arm Y center z false k)
      else 0) := by
    apply Finset.measurable_sum
    intro k hk
    have hgroupCount := measurable_groupCount (n := n) group arm hgroup harm k
    have hgroupCountCast : Measurable (fun z : Fin n -> Omega =>
        (groupCount group arm z k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hgroupCount
    exact Measurable.ite (measurableSet_usableGroup group arm hgroup harm k)
      (hgroupCountCast.mul
        ((measurable_armResidualMean group arm Y center hgroup harm hY true k).sub
          (measurable_armResidualMean group arm Y center hgroup harm hY false k)))
      measurable_const
  unfold occupancyWeightedResidual
  exact Measurable.ite hpos (htotalCast.inv.mul hsum) measurable_const

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the zero-safe
reciprocal usable occupancy measurable on the finite product sample
space](goal). -/
@[fun_prop]
lemma measurable_inverseUsableGroupTotal {n : Nat} (group : Omega -> kappa)
    (arm : Omega -> Bool) (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (inverseUsableGroupTotal (n := n) group arm) := by
  have htotal : Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) :=
    measurable_usableGroupTotal group arm hgroup harm
  have hpos : MeasurableSet {z : Fin n -> Omega |
      0 < usableGroupTotal group arm z} :=
    measurableSet_lt measurable_const htotal
  have htotalCast : Measurable (fun z : Fin n -> Omega =>
      (usableGroupTotal group arm z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htotal
  unfold inverseUsableGroupTotal
  exact Measurable.ite hpos htotalCast.inv measurable_const

/-- [Measurable group and arm labels](hyp:hgroup,harm) make [the zero-safe
occupancy design variance factor measurable on the finite product sample
space](goal). -/
@[fun_prop]
lemma measurable_occupancyDesignVarianceFactor {n : Nat}
    (group : Omega -> kappa) (arm : Omega -> Bool)
    (hgroup : Measurable group) (harm : Measurable arm) :
    Measurable (occupancyDesignVarianceFactor (n := n) group arm) := by
  classical
  have htotal : Measurable (fun z : Fin n -> Omega => usableGroupTotal group arm z) :=
    measurable_usableGroupTotal group arm hgroup harm
  have hpos : MeasurableSet {z : Fin n -> Omega |
      0 < usableGroupTotal group arm z} :=
    measurableSet_lt measurable_const htotal
  have htotalCast : Measurable (fun z : Fin n -> Omega =>
      (usableGroupTotal group arm z : Real)) :=
    (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htotal
  have hsum : Measurable (fun z : Fin n -> Omega =>
      ∑ k, if usableGroup group arm z k then
        (groupCount group arm z k : Real) ^ 2 *
          ((groupArmCount group arm z true k : Real)⁻¹ +
            (groupArmCount group arm z false k : Real)⁻¹)
      else 0) := by
    apply Finset.measurable_sum
    intro k hk
    have hgroupCount := measurable_groupCount (n := n) group arm hgroup harm k
    have hgroupCountCast : Measurable (fun z : Fin n -> Omega =>
        (groupCount group arm z k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hgroupCount
    have htrue := measurable_groupArmCount (n := n) group arm hgroup harm true k
    have hfalse := measurable_groupArmCount (n := n) group arm hgroup harm false k
    have htrueCast : Measurable (fun z : Fin n -> Omega =>
        (groupArmCount group arm z true k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp htrue
    have hfalseCast : Measurable (fun z : Fin n -> Omega =>
        (groupArmCount group arm z false k : Real)) :=
      (Measurable.of_discrete : Measurable fun m : Nat => (m : Real)).comp hfalse
    exact Measurable.ite (measurableSet_usableGroup group arm hgroup harm k)
      ((hgroupCountCast.pow measurable_const).mul
        (htrueCast.inv.add hfalseCast.inv)) measurable_const
  unfold occupancyDesignVarianceFactor
  exact Measurable.ite hpos
    ((htotalCast.inv.pow measurable_const).mul hsum) measurable_const

end Causalean.Stat
