/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.IntervalArithmetic.FiniteSearch
public import Causalean.Stat.Minimax.LeCam

/-! # Assouad hypercube minimax bound

This file develops Assouad's lower bound for statistical experiments indexed by
a Boolean hypercube. It introduces coordinate flips and Hamming risk, then
uses coordinatewise total-variation bounds between neighboring experiments to
derive average and worst-case minimax lower bounds.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- Given [a hypercube dimension](hyp:d), [a coordinate of that hypercube](hyp:j), and [a Boolean hypercube vertex](hyp:τ), [the coordinate-flipped vertex](goal) agrees with the given vertex at every coordinate except the specified one, where it takes the opposite Boolean value. -/
def flipBit (j : Fin d) (τ : Fin d → Bool) : Fin d → Bool :=
  Function.update τ j (!τ j)

/-- Flipping a coordinate changes that coordinate to the opposite Boolean value. -/
@[simp] theorem flipBit_self (j : Fin d) (τ : Fin d → Bool) : flipBit j τ j = !τ j :=
  Function.update_self _ _ _

/-- Flipping the same coordinate twice is the identity. -/
theorem flipBit_involutive (j : Fin d) : Function.Involutive (flipBit j) := by
  intro τ
  funext k
  by_cases h : k = j
  · subst h; simp [flipBit]
  · simp [flipBit, Function.update_of_ne h]

/-- Given [a hypercube dimension](hyp:d) and [a coordinate of that hypercube](hyp:j), [the coordinate-flip permutation](goal) is the bijection of Boolean hypercube vertices that flips precisely the specified coordinate. -/
def flipPerm (j : Fin d) : Equiv.Perm (Fin d → Bool) :=
  ⟨flipBit j, flipBit j, flipBit_involutive j, flipBit_involutive j⟩

/-- The coordinate-flip permutation acts by flipping that coordinate. -/
@[simp] theorem flipPerm_apply (j : Fin d) (τ : Fin d → Bool) :
    flipPerm j τ = flipBit j τ := rfl

/-- Given [a measurable sample space](hyp:Ω,mΩ), [a hypercube dimension](hyp:d), [a measure for every Boolean hypercube vertex](hyp:P), [an estimator returning a Boolean vertex from each sample outcome](hyp:est), and [a true vertex](hyp:τ), [the Hamming risk](goal) is the sum, over coordinates, of the measure of the outcomes at which the estimator differs from that true vertex under its associated measure. -/
noncomputable def hammingRisk (P : (Fin d → Bool) → Measure Ω)
    (est : Ω → Fin d → Bool) (τ : Fin d → Bool) : ℝ :=
  ∑ j, (P τ).real {ω | est ω j ≠ τ j}

variable (P : (Fin d → Bool) → Measure Ω) [∀ τ, IsProbabilityMeasure (P τ)]
  (est : Ω → Fin d → Bool)

/-- Coordinate-decoding error sets are measurable, being complements of the
measurable level sets `{ω | est ω j = b}`. -/
theorem measurableSet_decode_ne (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    (j : Fin d) (b : Bool) : MeasurableSet {ω | est ω j ≠ b} := by
  have h : {ω | est ω j ≠ b} = {ω | est ω j = b}ᶜ := by ext ω; simp
  rw [h]; exact (hmeas j b).compl

/-- The `j`-th decoding-error set at the flipped vertex is the complement of the
one at `τ`: the estimator's `j`-th bit either matches `τ j` or its flip, never both. -/
theorem decode_ne_flip_compl (j : Fin d) (τ : Fin d → Bool) :
    {ω | est ω j ≠ (flipBit j τ) j} = {ω | est ω j ≠ τ j}ᶜ := by
  have boollem : ∀ a b : Bool, (a ≠ !b) ↔ (a = b) := by decide
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, flipBit_self, not_not]
  exact boollem (est ω j) (τ j)

/-- **Per-coordinate pair bound.** For each vertex `τ`, the coordinate-`j` error mass
at `τ` plus the one at its `j`-flip is at least `1 − tvDist (P τ) (P (flip j τ))`.
This is the two-point testing bound applied to the `j`-th decoded bit. -/
theorem hammingRisk_pair_ge (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    (j : Fin d) (τ : Fin d → Bool) :
    1 - tvDist (P τ) (P (flipBit j τ))
      ≤ (P τ).real {ω | est ω j ≠ τ j}
        + (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j} := by
  have hS : MeasurableSet {ω | est ω j ≠ τ j} := measurableSet_decode_ne est hmeas j (τ j)
  rw [decode_ne_flip_compl est j τ]
  exact one_sub_tvDist_le_test (μ := P τ) (ν := P (flipBit j τ)) hS

/-- **Per-coordinate lower bound.** Summed over the cube, the coordinate-`j` error mass
is at least half the cube-sum of `1 − tvDist (P τ) (P (flip j τ))`, via pairing each
vertex with its `j`-flip (an involution that preserves the sum). -/
theorem sum_decode_ge (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    (j : Fin d) :
    ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ)))
      ≤ 2 * ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by
  -- Reindexing by the `j`-flip permutation leaves the cube-sum invariant.
  have hreindex :
      ∑ τ, (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j}
        = ∑ τ, (P τ).real {ω | est ω j ≠ τ j} :=
    Equiv.sum_comp (flipPerm j) (fun σ => (P σ).real {ω | est ω j ≠ σ j})
  calc ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ)))
      ≤ ∑ τ, ((P τ).real {ω | est ω j ≠ τ j}
            + (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j}) :=
        Finset.sum_le_sum (fun τ _ => hammingRisk_pair_ge P est hmeas j τ)
    _ = (∑ τ, (P τ).real {ω | est ω j ≠ τ j})
          + ∑ τ, (P (flipBit j τ)).real {ω | est ω j ≠ (flipBit j τ) j} :=
        Finset.sum_add_distrib
    _ = 2 * ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by rw [hreindex]; ring

/-- **Assouad's lemma (average form).**  Assume [each coordinate's decoded-bit event is
measurable](hyp:hmeas). If [every hypercube vertex's law is within total variation `β` of each of
its `d` neighbouring vertices' laws](hyp:hβ), then [the average Hamming risk over the cube is at
least `(d / 2)(1 − β)`](goal). Choosing the dimension `d` large and the per-coordinate divergence
`β` small forces a large number of mis-decoded coordinates. -/
theorem assouad_average (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    {β : ℝ} (hβ : ∀ j τ, tvDist (P τ) (P (flipBit j τ)) ≤ β) :
    (d / 2 : ℝ) * (1 - β)
      ≤ (∑ τ, hammingRisk P est τ) / (Fintype.card (Fin d → Bool)) := by
  set C : ℝ := (Fintype.card (Fin d → Bool) : ℝ) with hC
  have hCnat : 0 < Fintype.card (Fin d → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have hCpos : (0 : ℝ) < C := by rw [hC]; exact_mod_cast hCnat
  -- Per coordinate: `C·(1−β)/2 ≤ ∑_τ (coordinate-j error mass)`.
  have hG : ∀ j, C * (1 - β) / 2 ≤ ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by
    intro j
    have hcoord := sum_decode_ge P est hmeas j
    have hβsum : C * (1 - β) ≤ ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ))) := by
      have h1 : ∑ _τ : Fin d → Bool, (1 - β)
          ≤ ∑ τ, (1 - tvDist (P τ) (P (flipBit j τ))) :=
        Finset.sum_le_sum (fun τ _ => by linarith [hβ j τ])
      have h2 : ∑ _τ : Fin d → Bool, (1 - β) = C * (1 - β) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hC]
      linarith [h1, h2]
    linarith [hβsum, hcoord]
  -- Sum the coordinate bounds, then divide by the cube size.
  have hswap : ∑ τ, hammingRisk P est τ
      = ∑ j, ∑ τ, (P τ).real {ω | est ω j ≠ τ j} := by
    simp_rw [hammingRisk]; rw [Finset.sum_comm]
  have hfinal : (d : ℝ) * (C * (1 - β) / 2) ≤ ∑ τ, hammingRisk P est τ := by
    rw [hswap]
    have h2 : (d : ℝ) * (C * (1 - β) / 2) = ∑ _j : Fin d, (C * (1 - β) / 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h2]
    exact Finset.sum_le_sum (fun j _ => hG j)
  rw [le_div_iff₀ hCpos]
  have hrw : (d / 2 : ℝ) * (1 - β) * C = (d : ℝ) * (C * (1 - β) / 2) := by ring
  rw [hrw]; exact hfinal

/-- **Assouad's lemma (existence form).** Under the same hypotheses — [each coordinate's
decoded-bit event is measurable](hyp:hmeas) and [every vertex's law is within total variation
`β` of each of its `d` neighbours](hyp:hβ) — [some vertex `τ` forces Hamming risk at least
`(d / 2)(1 − β)`](goal): no cube estimator can decode every vertex's coordinates reliably when
neighbouring laws are statistically close. -/
theorem assouad_exists (hmeas : ∀ j (b : Bool), MeasurableSet {ω | est ω j = b})
    {β : ℝ} (hβ : ∀ j τ, tvDist (P τ) (P (flipBit j τ)) ≤ β) :
    ∃ τ, (d / 2 : ℝ) * (1 - β) ≤ hammingRisk P est τ := by
  set C : ℝ := (Fintype.card (Fin d → Bool) : ℝ) with hC
  have hCnat : 0 < Fintype.card (Fin d → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have hCpos : (0 : ℝ) < C := by rw [hC]; exact_mod_cast hCnat
  have havg := assouad_average P est hmeas hβ
  rw [← hC] at havg
  by_contra hcon
  push_neg at hcon
  have hstrict : ∑ τ, hammingRisk P est τ < C * ((d / 2 : ℝ) * (1 - β)) := by
    calc ∑ τ, hammingRisk P est τ
        < ∑ _τ : Fin d → Bool, ((d / 2 : ℝ) * (1 - β)) :=
          Finset.sum_lt_sum_of_nonempty ⟨fun _ => false, Finset.mem_univ _⟩
            (fun τ _ => hcon τ)
      _ = C * ((d / 2 : ℝ) * (1 - β)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hC]
  rw [le_div_iff₀ hCpos] at havg
  nlinarith [havg, hstrict]

/-! ## Parameter-space risk form -/

open Causalean.Mathlib.Analysis.IntervalArithmetic.FiniteSearch

/-- Given [a finite family of parameter vertices](hyp:θ), [a measurable parameter-valued
estimator](hyp:θhat,hθhat), [there exists a measurable, deterministically tie-broken nearest-vertex
decoder](goal): at every observation its chosen vertex is no farther from the estimator than any
competing vertex. -/
theorem exists_measurable_nearestVertex
    {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (θ : (Fin d → Bool) → Θ) (θhat : Ω → Θ) (hθhat : Measurable θhat) :
    ∃ decode : Ω → Fin d → Bool, Measurable decode ∧
      ∀ ω τ, dist (θhat ω) (θ (decode ω)) ≤ dist (θhat ω) (θ τ) := by
  classical
  let Cube := Fin d → Bool
  have hcard : 1 ≤ Fintype.card Cube := Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  let n : ℕ := Fintype.card Cube - 1
  have hcard_eq : Fintype.card Cube = n + 1 := by
    dsimp [n]
    omega
  let e : Cube ≃ Fin (n + 1) :=
    (Fintype.equivFin Cube).trans (finCongr hcard_eq)
  let scores : Ω → Fin (n + 1) → ℝ := fun ω i => dist (θhat ω) (θ (e.symm i))
  let selected : Ω → Fin (n + 1) := fun ω => leastScoreIndex (scores ω)
  let decode : Ω → Cube := fun ω => e.symm (selected ω)
  have hscores : Measurable scores := by
    apply measurable_pi_lambda
    intro i
    exact (continuous_id.dist continuous_const).measurable.comp hθhat
  have hselected : Measurable selected :=
    measurable_leastScoreIndex.comp hscores
  have heinv : Measurable e.symm := measurable_of_finite _
  refine ⟨decode, heinv.comp hselected, ?_⟩
  intro ω τ
  simpa [decode, selected, scores] using
    leastScoreIndex_minimal (scores ω) (e τ)

/-- Given [a family of experiment laws](hyp:P), [parameter vertices](hyp:θ), [a
parameter-valued estimator](hyp:θhat), and [a true cube vertex](hyp:τ), the [extended
expected metric risk](goal) is the lintegral of the estimator's distance from the true
parameter. -/
noncomputable def parameterRiskLIntegral {Θ : Type*} [PseudoMetricSpace Θ]
    (P : (Fin d → Bool) → Measure Ω) (θ : (Fin d → Bool) → Θ)
    (θhat : Ω → Θ) (τ : Fin d → Bool) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (dist (θhat ω) (θ τ)) ∂(P τ)

/-- **Assouad's lemma in parameter-risk form.** For [hypercube laws](hyp:P),
[parameter vertices](hyp:θ), [a nonnegative separation scale](hyp:hs), [an estimator](hyp:θhat),
and [a measurable nearest-vertex decoder](hyp:decode,hdecode,hnearest), if [vertices are
separated by twice the scale times Hamming distance](hyp:hsep) and [neighboring laws have
total variation at most `β`](hyp:hβ), then [some vertex has expected metric loss at least
`(d*s/2)(1-β)`](goal).

This is Tsybakov (2009), Theorem 2.12.  The factor-two separation is the theorem's
standard convention; it is what converts a decoding error into loss at least `s`.
The extended-valued risk requires no integrability assumption. -/
theorem assouad_parameter_risk
    {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (P : (Fin d → Bool) → Measure Ω) [∀ τ, IsProbabilityMeasure (P τ)]
    (θ : (Fin d → Bool) → Θ) {s β : ℝ} (hs : 0 ≤ s)
    (θhat : Ω → Θ) (decode : Ω → Fin d → Bool)
    (hdecode : ∀ j (b : Bool), MeasurableSet {ω | decode ω j = b})
    (hnearest : ∀ ω τ, dist (θhat ω) (θ (decode ω)) ≤ dist (θhat ω) (θ τ))
    (hsep : ∀ τ σ,
      2 * s * (∑ j, if τ j ≠ σ j then (1 : ℝ) else 0) ≤ dist (θ τ) (θ σ))
    (hβ : ∀ j τ, tvDist (P τ) (P (flipBit j τ)) ≤ β) :
    ∃ τ, ENNReal.ofReal ((d * s / 2 : ℝ) * (1 - β)) ≤
      parameterRiskLIntegral P θ θhat τ := by
  classical
  obtain ⟨τ, hτ⟩ := assouad_exists P decode hdecode hβ
  refine ⟨τ, ?_⟩
  let count : Ω → ℝ := fun ω => ∑ j, if decode ω j ≠ τ j then 1 else 0
  have hcount_nonneg : ∀ ω, 0 ≤ count ω := by
    intro ω
    apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> norm_num
  have hgeom : ∀ ω, s * count ω ≤ dist (θhat ω) (θ τ) := by
    intro ω
    have htriangle : dist (θ (decode ω)) (θ τ) ≤
        dist (θhat ω) (θ (decode ω)) + dist (θhat ω) (θ τ) := by
      calc
        dist (θ (decode ω)) (θ τ) ≤
            dist (θ (decode ω)) (θhat ω) + dist (θhat ω) (θ τ) :=
          dist_triangle _ _ _
        _ = dist (θhat ω) (θ (decode ω)) + dist (θhat ω) (θ τ) := by
          rw [dist_comm (θ (decode ω)) (θhat ω)]
    have htwo : 2 * s * count ω ≤ 2 * dist (θhat ω) (θ τ) := by
      calc
        2 * s * count ω ≤ dist (θ (decode ω)) (θ τ) := by
          simpa [count] using hsep (decode ω) τ
        _ ≤ 2 * dist (θhat ω) (θ τ) := by
          linarith [htriangle, hnearest ω τ]
    linarith
  have hRiskCount : ENNReal.ofReal (hammingRisk P decode τ) =
      ∫⁻ ω, ENNReal.ofReal (count ω) ∂(P τ) := by
    rw [hammingRisk, ENNReal.ofReal_sum_of_nonneg]
    · calc
        ∑ j, ENNReal.ofReal ((P τ).real { ω | decode ω j ≠ τ j }) =
            ∑ j, ∫⁻ ω, if decode ω j ≠ τ j then (1 : ENNReal) else 0 ∂(P τ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [MeasureTheory.Measure.real_def,
            ENNReal.ofReal_toReal (measure_ne_top (P τ) _)]
          have hset := measurableSet_decode_ne decode hdecode j (τ j)
          rw [← lintegral_indicator_one hset]
          apply lintegral_congr
          intro ω
          simp [Set.indicator, apply_ite]
        _ = ∫⁻ ω, ∑ j, if decode ω j ≠ τ j then (1 : ENNReal) else 0 ∂(P τ) := by
          rw [lintegral_finset_sum]
          intro j hj
          exact Measurable.ite (measurableSet_decode_ne decode hdecode j (τ j))
            measurable_const measurable_const
        _ = ∫⁻ ω, ENNReal.ofReal (count ω) ∂(P τ) := by
          apply lintegral_congr
          intro ω
          change (∑ j, if decode ω j ≠ τ j then (1 : ENNReal) else 0) =
            ENNReal.ofReal (∑ j, if decode ω j ≠ τ j then (1 : ℝ) else 0)
          rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro j hj
            split_ifs <;> simp
          · intro j hj
            split_ifs <;> norm_num
    · intro j hj
      exact measureReal_nonneg
  calc
    ENNReal.ofReal ((d * s / 2 : ℝ) * (1 - β)) =
        ENNReal.ofReal (s * ((d / 2 : ℝ) * (1 - β))) := by ring_nf
    _ ≤ ENNReal.ofReal (s * hammingRisk P decode τ) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hτ hs)
    _ = ENNReal.ofReal s * ∫⁻ ω, ENNReal.ofReal (count ω) ∂(P τ) := by
      rw [ENNReal.ofReal_mul hs, hRiskCount]
    _ = ∫⁻ ω, ENNReal.ofReal (s * count ω) ∂(P τ) := by
      have hcount_meas : Measurable (fun ω => ENNReal.ofReal (count ω)) := by
        apply Measurable.ennreal_ofReal
        change Measurable (fun ω => ∑ j, if decode ω j ≠ τ j then 1 else 0)
        exact Finset.measurable_sum Finset.univ fun j hj => Measurable.ite
          (measurableSet_decode_ne decode hdecode j (τ j)) measurable_const measurable_const
      rw [← lintegral_const_mul _ hcount_meas]
      apply lintegral_congr
      intro ω
      rw [ENNReal.ofReal_mul hs]
    _ ≤ parameterRiskLIntegral P θ θhat τ := by
      unfold parameterRiskLIntegral
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (hgeom ω)

/-- **Assouad parameter-risk bound with the decoder constructed automatically.** For
[hypercube laws](hyp:P), [parameter vertices](hyp:θ), [a nonnegative separation
scale](hyp:hs), and [a measurable parameter estimator](hyp:θhat,hθhat), if [vertices are
separated by twice the scale times Hamming distance](hyp:hsep) and [neighboring laws have total
variation at most `β`](hyp:hβ), then [some vertex has expected metric loss at least
`(d*s/2)(1-β)`](goal). -/
theorem assouad_parameter_risk_of_measurable
    {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (P : (Fin d → Bool) → Measure Ω) [∀ τ, IsProbabilityMeasure (P τ)]
    (θ : (Fin d → Bool) → Θ) {s β : ℝ} (hs : 0 ≤ s)
    (θhat : Ω → Θ) (hθhat : Measurable θhat)
    (hsep : ∀ τ σ,
      2 * s * (∑ j, if τ j ≠ σ j then (1 : ℝ) else 0) ≤ dist (θ τ) (θ σ))
    (hβ : ∀ j τ, tvDist (P τ) (P (flipBit j τ)) ≤ β) :
    ∃ τ, ENNReal.ofReal ((d * s / 2 : ℝ) * (1 - β)) ≤
      parameterRiskLIntegral P θ θhat τ := by
  obtain ⟨decode, hdecode, hnearest⟩ :=
    exists_measurable_nearestVertex θ θhat hθhat
  apply assouad_parameter_risk P θ hs θhat decode
  · intro j b
    exact measurableSet_eq_fun ((measurable_pi_apply j).comp hdecode) measurable_const
  · exact hnearest
  · exact hsep
  · exact hβ

end Causalean.Stat
