/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Measurable minimizers on compact Euclidean action sets

This module provides an exact Borel measurable argmin rule for a jointly Borel objective whose
action sections are continuous on a fixed nonempty compact subset of a finite-dimensional
Euclidean space.  It also specializes the result to a measurable nearest-point rule.  Neither
result assumes convexity or uniqueness of the minimizer.

The hypotheses are the compact-action specialization of Brown--Purves, *Measurable Selections of
Extrema* (1973), Corollary 1: the fixed feasible sections are compact, hence sigma-compact, and
continuity supplies the required lower semicontinuity and exact attainment.
-/

open Metric Set

namespace Causalean.Mathlib.MeasureTheory

noncomputable section

-- The Euclidean metric/Borel instances on `EuclideanSpace ℝ ι` use the finite enumeration.
set_option linter.unusedFintypeInType false

private theorem measurable_compact_sInf
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y]
    (K : Set Y) (hKne : K.Nonempty)
    (g : X × Y → ℝ) (hg : Measurable g)
    (hgc : ∀ x, ContinuousOn (fun y => g (x, y)) K) :
    Measurable (fun x => sInf ((fun y => g (x, y)) '' K)) := by
  letI : Nonempty K := Set.nonempty_coe_sort.mpr hKne
  let d : ℕ → K := TopologicalSpace.denseSeq K
  have hd : Dense (range d) := by
    simpa only [DenseRange, d] using TopologicalSpace.denseRange_denseSeq K
  have he_surj : Function.Surjective
      (fun n : ℕ => (⟨d n, mem_range_self n⟩ : range d)) := by
    rintro ⟨z, n, rfl⟩
    exact ⟨n, rfl⟩
  have hm : Measurable (fun x => ⨅ n, g (x, (d n : K).1)) :=
    Measurable.iInf (fun _ => hg.comp (measurable_id.prodMk measurable_const))
  convert hm using 1
  funext x
  rw [sInf_image']
  have he := Dense.ciInf' hd (hgc x).domRestrict
  change (⨅ s : range d, g (x, (s.1 : K).1)) = ⨅ i : K, g (x, i.1) at he
  calc
    (⨅ a : K, g (x, a.1)) = ⨅ s : range d, g (x, (s.1 : K).1) := he.symm
    _ = ⨅ n, g (x, (d n : K).1) :=
      (he_surj.iInf_comp (fun s : range d => g (x, (s.1 : K).1))).symm

private theorem measurableSet_exists_compact_eq_zero
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y]
    (K : Set Y) (hK : IsCompact K) (hKne : K.Nonempty)
    (g : X × Y → ℝ) (hg : Measurable g)
    (hgc : ∀ x, ContinuousOn (fun y => g (x, y)) K)
    (hg0 : ∀ x y, y ∈ K → 0 ≤ g (x, y)) :
    MeasurableSet {x | ∃ y ∈ K, g (x, y) = 0} := by
  have hm := measurable_compact_sInf K hKne g hg hgc
  have heq : {x | ∃ y ∈ K, g (x, y) = 0} =
      (fun x => sInf ((fun y => g (x, y)) '' K)) ⁻¹' {0} := by
    ext x
    obtain ⟨z, hzK, hzval, hzmin⟩ := hK.exists_sInf_image_eq_and_le hKne (hgc x)
    constructor
    · rintro ⟨y, hyK, hy0⟩
      have hle : g (x, z) ≤ 0 := by simpa [hy0] using hzmin y hyK
      have hge : 0 ≤ g (x, z) := hg0 x z hzK
      simp only [mem_preimage, mem_singleton_iff]
      rw [hzval]
      exact le_antisymm hle hge
    · intro hx
      refine ⟨z, hzK, ?_⟩
      simpa only [mem_preimage, mem_singleton_iff] using hzval ▸ hx
  rw [heq]
  exact measurableSet_singleton 0 |>.preimage hm

private lemma abs_add_max_eq_zero_iff (a b : ℝ) :
    |a| + max b 0 = 0 ↔ a = 0 ∧ b ≤ 0 := by
  constructor
  · intro h
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : b ≤ max b 0 := le_max_left _ _
    have hm : 0 ≤ max b 0 := le_max_right _ _
    exact ⟨abs_eq_zero.mp (by linarith), by linarith⟩
  · rintro ⟨rfl, hb⟩
    simp [hb]

private lemma abs_add_max_add_max_eq_zero_iff (a b c : ℝ) :
    |a| + max b 0 + max c 0 = 0 ↔ a = 0 ∧ b ≤ 0 ∧ c ≤ 0 := by
  constructor
  · intro h
    have ha : 0 ≤ |a| := abs_nonneg a
    have hb : b ≤ max b 0 := le_max_left _ _
    have hc : c ≤ max c 0 := le_max_left _ _
    have hmb : 0 ≤ max b 0 := le_max_right _ _
    have hmc : 0 ≤ max c 0 := le_max_right _ _
    exact ⟨abs_eq_zero.mp (by linarith), by linarith, by linarith⟩
  · rintro ⟨rfl, hb, hc⟩
    simp [hb, hc]

set_option maxHeartbeats 800000 in
-- The nested measurable-search construction requires more elaboration than the default budget.
/-- A [jointly Borel real objective](hyp:f,hf) with [continuous action sections](hyp:hfc) on a
fixed [nonempty compact action set](hyp:K,hK,hKne) in finite-dimensional Euclidean space admits
a [Borel measurable, feasible rule that minimizes the objective at every parameter](goal).

This is an exact selector: no uniqueness or convexity is assumed. The `StandardBorelSpace`
hypothesis records the standard measurable-extrema setting on the parameter space; the action
space has its canonical Euclidean Borel structure.

Proof strategy: specialize the Brown--Purves compact-section construction.  First use a countable
dense subset of each fixed nonempty compact feasible set to prove that its pointwise minimum value
is measurable.  This also makes compact-fiber hit tests measurable: encode membership in the
argmin fiber and finitely many closed-ball constraints by a nonnegative continuous penalty, whose
minimum over `K` is zero exactly when the constrained fiber is nonempty.  A least-index search in a
countable dense family then gives successively closer measurable finite-valued approximants.  Pick
each new approximant close both to the argmin fiber and to the preceding approximant, so the
sequence is Cauchy while its distance to the closed argmin fiber tends to zero. Completeness puts
the limit in that fiber, and `measurable_of_tendsto_metrizable` makes the pointwise limit
measurable.
-/
theorem borelMeasurable_compact_argmin_selector
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {ι : Type*} [Fintype ι]
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hKne : K.Nonempty)
    (f : X × EuclideanSpace ℝ ι → ℝ) (hf : Measurable f)
    (hfc : ∀ x, ContinuousOn (fun y => f (x, y)) K) :
    ∃ π : X → EuclideanSpace ℝ ι,
      Measurable π ∧ ∀ x, π x ∈ K ∧ ∀ y ∈ K, f (x, π x) ≤ f (x, y) := by
  classical
  let v : X → ℝ := fun x => sInf ((fun y => f (x, y)) '' K)
  have hv : Measurable v := measurable_compact_sInf K hKne f hf hfc
  have hmin : ∀ x, ∃ z ∈ K, f (x, z) = v x ∧ ∀ y ∈ K, f (x, z) ≤ f (x, y) := by
    intro x
    obtain ⟨z, hzK, hzv, hzmin⟩ := hK.exists_sInf_image_eq_and_le hKne (hfc x)
    exact ⟨z, hzK, hzv.symm, hzmin⟩
  letI : Nonempty K := Set.nonempty_coe_sort.mpr hKne
  let d : ℕ → K := TopologicalSpace.denseSeq K
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq K
  let r : ℕ → ℝ := fun n => 1 / 2 ^ n
  have hr_pos : ∀ n, 0 < r n := by
    intro n
    simp only [r]
    positivity
  let Approx : ℕ → Type _ := fun n =>
    {a : X → EuclideanSpace ℝ ι //
      Measurable a ∧ ∀ x, ∃ z ∈ K, f (x, z) = v x ∧ dist z (a x) ≤ r n}
  have hbase : Approx 0 := by
    let p : ℕ → X → Prop := fun k x =>
      ∃ z ∈ K,
        |f (x, z) - v x| + max (dist z (d k : EuclideanSpace ℝ ι) - r 0) 0 = 0
    have hp : ∀ k, MeasurableSet {x | p k x} := by
      intro k
      simpa only [p] using measurableSet_exists_compact_eq_zero K hK hKne
        (fun xz => |f xz - v xz.1| +
          max (dist xz.2 (d k : EuclideanSpace ℝ ι) - r 0) 0)
        ((hf.sub (hv.comp measurable_fst)).norm.add
          (((measurable_snd.dist measurable_const).sub_const (r 0)).max measurable_const))
        (fun x => by
          change ContinuousOn (fun y => |f (x, y) - v x| +
            max (dist y (d k : EuclideanSpace ℝ ι) - r 0) 0) K
          exact ((hfc x).sub continuousOn_const).abs.add
            ((((continuous_id.dist continuous_const).sub continuous_const).max
              continuous_const).continuousOn))
        (fun _ _ _ => add_nonneg (abs_nonneg _) (le_max_right _ _))
    have hex : ∀ x, ∃ k, p k x := by
      intro x
      obtain ⟨z, hzK, hzv, _⟩ := hmin x
      obtain ⟨k, hk⟩ := hd.exists_dist_lt (⟨z, hzK⟩ : K) (hr_pos 0)
      refine ⟨k, z, hzK, ?_⟩
      rw [hzv, sub_self, abs_zero]
      have hk' : dist z (d k : EuclideanSpace ℝ ι) ≤ r 0 := by
        simpa only [Subtype.dist_eq] using hk.le
      simp [hk']
    let a : X → EuclideanSpace ℝ ι := fun x =>
      (d (Nat.find (hex x)) : EuclideanSpace ℝ ι)
    have ha : Measurable a := by
      simpa only [a] using
        (Measurable.find (f := fun k (_ : X) => (d k : EuclideanSpace ℝ ι))
          (fun _ => measurable_const) hp hex)
    refine ⟨a, ha, ?_⟩
    intro x
    obtain ⟨z, hzK, hz⟩ := Nat.find_spec (hex x)
    have hz' := (abs_add_max_eq_zero_iff
      (f (x, z) - v x) (dist z (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) - r 0)).mp hz
    refine ⟨z, hzK, sub_eq_zero.mp hz'.1, ?_⟩
    change dist z (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) ≤ r 0
    linarith [hz'.2]
  have hstep : ∀ n, ∀ prev : Approx n,
      {next : Approx (n + 1) //
        ∀ x, dist (prev.1 x) (next.1 x) ≤ r n + r (n + 1)} := by
    intro n prev
    let p : ℕ → X → Prop := fun k x =>
      ∃ z ∈ K,
        |f (x, z) - v x| + max (dist z (prev.1 x) - r n) 0 +
          max (dist z (d k : EuclideanSpace ℝ ι) - r (n + 1)) 0 = 0
    have hp : ∀ k, MeasurableSet {x | p k x} := by
      intro k
      simpa only [p] using measurableSet_exists_compact_eq_zero K hK hKne
        (fun xz => |f xz - v xz.1| + max (dist xz.2 (prev.1 xz.1) - r n) 0 +
          max (dist xz.2 (d k : EuclideanSpace ℝ ι) - r (n + 1)) 0)
        (((hf.sub (hv.comp measurable_fst)).norm.add
          (((measurable_snd.dist (prev.2.1.comp measurable_fst)).sub_const (r n)).max
            measurable_const)).add
          (((measurable_snd.dist measurable_const).sub_const (r (n + 1))).max
            measurable_const))
        (fun x => by
          change ContinuousOn (fun y => |f (x, y) - v x| +
            max (dist y (prev.1 x) - r n) 0 +
            max (dist y (d k : EuclideanSpace ℝ ι) - r (n + 1)) 0) K
          exact (((hfc x).sub continuousOn_const).abs.add
            ((((continuous_id.dist continuous_const).sub continuous_const).max
              continuous_const).continuousOn)).add
            ((((continuous_id.dist continuous_const).sub continuous_const).max
              continuous_const).continuousOn))
        (fun _ _ _ => add_nonneg
          (add_nonneg (abs_nonneg _) (le_max_right _ _)) (le_max_right _ _))
    have hex : ∀ x, ∃ k, p k x := by
      intro x
      obtain ⟨z, hzK, hzv, hzprev⟩ := prev.2.2 x
      obtain ⟨k, hk⟩ := hd.exists_dist_lt (⟨z, hzK⟩ : K) (hr_pos (n + 1))
      refine ⟨k, z, hzK, ?_⟩
      rw [hzv, sub_self, abs_zero]
      have hk' : dist z (d k : EuclideanSpace ℝ ι) ≤ r (n + 1) := by
        simpa only [Subtype.dist_eq] using hk.le
      simp [hzprev, hk']
    let a : X → EuclideanSpace ℝ ι := fun x =>
      (d (Nat.find (hex x)) : EuclideanSpace ℝ ι)
    have ha : Measurable a := by
      simpa only [a] using
        (Measurable.find (f := fun k (_ : X) => (d k : EuclideanSpace ℝ ι))
          (fun _ => measurable_const) hp hex)
    refine ⟨⟨a, ha, ?_⟩, ?_⟩
    · intro x
      obtain ⟨z, hzK, hz⟩ := Nat.find_spec (hex x)
      have hz' := (abs_add_max_add_max_eq_zero_iff
        (f (x, z) - v x) (dist z (prev.1 x) - r n)
        (dist z (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) - r (n + 1))).mp hz
      refine ⟨z, hzK, sub_eq_zero.mp hz'.1, ?_⟩
      change dist z (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) ≤ r (n + 1)
      linarith [hz'.2.2]
    · intro x
      obtain ⟨z, _, hz⟩ := Nat.find_spec (hex x)
      have hz' := (abs_add_max_add_max_eq_zero_iff
        (f (x, z) - v x) (dist z (prev.1 x) - r n)
        (dist z (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) - r (n + 1))).mp hz
      change dist (prev.1 x) (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) ≤
        r n + r (n + 1)
      calc
        dist (prev.1 x) (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) ≤
            dist (prev.1 x) z + dist z (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) :=
          dist_triangle _ _ _
        _ ≤ r n + r (n + 1) := by
          have h₁ : dist z (prev.1 x) ≤ r n := by linarith [hz'.2.1]
          have h₂ : dist z (d (Nat.find (hex x)) : EuclideanSpace ℝ ι) ≤ r (n + 1) := by
            linarith [hz'.2.2]
          exact add_le_add (dist_comm z _ ▸ h₁) h₂
  let approximants : ∀ n, Approx n := fun n =>
    Nat.rec hbase (fun n prev => (hstep n prev).1) n
  let a : ℕ → X → EuclideanSpace ℝ ι := fun n => (approximants n).1
  have ha_meas : ∀ n, Measurable (a n) := fun n => (approximants n).2.1
  have ha_near : ∀ n x, ∃ z ∈ K, f (x, z) = v x ∧ dist z (a n x) ≤ r n :=
    fun n => (approximants n).2.2
  have ha_step : ∀ n x, dist (a n x) (a (n + 1) x) ≤ r n + r (n + 1) := by
    intro n x
    exact (hstep n (approximants n)).2 x
  have ha_cauchy : ∀ x, CauchySeq (fun n => a n x) := by
    intro x
    apply cauchySeq_of_le_geometric_two (C := 3)
    intro n
    calc
      dist (a n x) (a (n + 1) x) ≤ r n + r (n + 1) := ha_step n x
      _ = 3 / 2 / 2 ^ n := by
        simp only [r, pow_succ]
        field_simp
        ring
  choose π hπ using fun x => cauchySeq_tendsto_of_complete (ha_cauchy x)
  have hπ_meas : Measurable π := by
    apply measurable_of_tendsto_metrizable ha_meas
    exact tendsto_pi_nhds.mpr hπ
  refine ⟨π, hπ_meas, ?_⟩
  intro x
  have hr_zero : Filter.Tendsto r Filter.atTop (nhds 0) := by
    simpa only [r, one_div, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) (by positivity : 0 ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1))
  choose z hzK hzv hza using fun n => ha_near n x
  have hzπ : Filter.Tendsto z Filter.atTop (nhds (π x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hza0 : Filter.Tendsto (fun n => dist (z n) (a n x)) Filter.atTop (nhds 0) := by
      apply squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg)
        (Filter.Eventually.of_forall hza)
      exact hr_zero
    have haπ0 : Filter.Tendsto (fun n => dist (a n x) (π x)) Filter.atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.mp (hπ x)
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (Filter.Eventually.of_forall fun n => dist_triangle (z n) (a n x) (π x))
    simpa only [zero_add] using hza0.add haπ0
  have hπK : π x ∈ K := hK.isClosed.mem_of_tendsto hzπ (Filter.Eventually.of_forall hzK)
  refine ⟨hπK, ?_⟩
  intro y hyK
  have hzπK : Filter.Tendsto z Filter.atTop (nhdsWithin (π x) K) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzπ, Filter.Eventually.of_forall hzK⟩
  have hcomp : Filter.Tendsto (fun n => f (x, z n)) Filter.atTop
      (nhds (f (x, π x))) := ((hfc x) (π x) hπK).tendsto.comp hzπK
  have hconst : Filter.Tendsto (fun _ : ℕ => v x) Filter.atTop (nhds (v x)) :=
    tendsto_const_nhds
  have : f (x, π x) = v x := tendsto_nhds_unique hcomp (by simpa only [hzv] using hconst)
  rw [this]
  obtain ⟨z₀, _, hz₀, hz₀min⟩ := hmin x
  rw [← hz₀]
  exact hz₀min y hyK

/-- Every [nonempty compact subset](hyp:K,hK,hKne) of a finite-dimensional Euclidean space
admits a [total Borel measurable nearest-point rule whose chosen point is feasible and realizes
the exact distance infimum](goal).

The rule is defined on the whole ambient space.  Ties are resolved measurably; the set need not be
convex and a nearest point need not be unique.  `Metric.infDist x K` is Mathlib's infimum of
`dist x y` over `y ∈ K`.

Proof strategy: invoke `borelMeasurable_compact_argmin_selector` for squared Euclidean distance,
using joint continuity for measurability and action-section continuity.  Nonnegativity makes
minimization of the square equivalent to minimization of distance, and
`IsCompact.exists_infDist_eq_dist` identifies the attained value with `Metric.infDist x K`. -/
theorem borelMeasurable_nearestPoint_selector
    {ι : Type*} [Fintype ι]
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ π : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
      Measurable π ∧ ∀ x, π x ∈ K ∧ dist x (π x) = infDist x K := by
  obtain ⟨π, hπmeas, hπ⟩ := borelMeasurable_compact_argmin_selector K hK hKne
    (fun xy => dist xy.1 xy.2 ^ 2)
    ((continuous_fst.dist continuous_snd).pow 2).measurable
    (fun _ => ((continuous_const.dist continuous_id).pow 2).continuousOn)
  refine ⟨π, hπmeas, fun x => ⟨(hπ x).1, ?_⟩⟩
  obtain ⟨y, hyK, hy⟩ := hK.exists_infDist_eq_dist hKne x
  apply le_antisymm
  · rw [hy]
    have hsquare := (hπ x).2 y hyK
    have hπnonneg : 0 ≤ dist x (π x) := dist_nonneg
    have hynonneg : 0 ≤ dist x y := dist_nonneg
    nlinarith
  · exact infDist_le_dist_of_mem (hπ x).1

end

end Causalean.Mathlib.MeasureTheory
