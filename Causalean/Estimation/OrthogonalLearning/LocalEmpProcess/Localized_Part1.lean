/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized regime bridge, Part 1: definitions and fallback bounds

This first part defines the localized regimes and proves their conservative bounded-loss
fallback bounds. Parts 2 and 3 prove the sharp critical-radius variants.

Sibling: `Causalean/Estimation/OrthogonalLearning/LocalEmpProcess/Rademacher.lean` realises the same predicate
under a global Rademacher bound. Downstream callers pick
whichever bridge fits the problem at hand; the localized version
includes a countable-class critical-radius bridge for settings where the
`‖θ−θ₀‖` slot of the modulus inequality matters.

References:
* Foster, Syrgkanis, *Orthogonal statistical learning*, Ann. Statist.
  51 (2023) 879–908, Lemma 14 (the localized rate `O(δ_n)`
  with critical radius `δ_n`).
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Theorem 3.3.

## Output

Across all three parts, the development provides three bridge families.

* `localEmpProcessModulus_of_localized_bounded` and its a.e. analogue give a
  low-hypothesis fallback with the conservative deterministic envelope
  `ρ n := √(2 · b)`.
* `localEmpProcessModulus_of_localized_sharp` gives the separable-class
  Foster-Syrgkanis critical-radius envelope
  `ρ n := (10 · L + 3) · criticalRadius (ψ |B(n)|)` on nonempty fold-B samples.
* `localEmpProcessModulus_of_localized_sharp_ae` obtains the same sharp envelope
  from an a.e. centred-loss bound by clamping the centred loss on a conull set
  and transferring the event back to the original system.

## Fallback schema proved in this part

```
theorem localEmpProcessModulus_of_localized
    (S : LearningSystem Ω μ Z P_Z Θ G) (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid) (g : G)
    {ψ : ℕ → ℝ → ℝ} {b : ℝ}
    (hreg : LocalizedRademacherRegime S S_iid split g idx norm ψ b)
    (hpop_center : ∀ θ ∈ S.Θ_set, |S.L θ g - S.L S.θ₀ g| ≤ b)
    {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun _n => Real.sqrt (2 * b)) δ g
```
-/

module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Local
public import Causalean.Stat.Concentration.Localization.UniformDeviation
public import Causalean.Stat.Concentration.Localization.CriticalRadius
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # Localized Rademacher Moduli

This first part defines the everywhere and almost-everywhere localized Rademacher regimes,
proves their conservative bounded-loss modulus bridges, and defines the centered clamping
predicate used later. The sharp critical-radius bridges are in Parts 2 and 3.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
  Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- For [an orthogonal statistical-learning system](hyp:S), [an independent and identically distributed sample from its observation law](hyp:_S_iid), [a one-shot sample split](hyp:_split), [a nuisance function](hyp:g), [a sequence indexing candidate targets](hyp:idx), [a norm on real-valued observation functions](hyp:norm), [a family of real complexity envelopes](hyp:ψ), and [a real bound](hyp:b), the [localized Rademacher regime](goal) requires: [the bound is nonnegative](step:1); [the centered loss is bounded in absolute value by that bound for every observation and candidate target](step:2); [each complexity envelope is sub-root](step:3); and [at every sample size, the envelope upper-bounds the population Rademacher complexity of the indexed centered-loss class on the split's validation fold](step:4).

**Localized regime predicate for a `LearningSystem`.**

For a fixed nuisance `g`, viewed as a centred loss class on `Z` indexed
by a countable dense sequence `idx : ℕ → S.Θ_set`:

* `0 ≤ b` and `|ℓ z θ g − ℓ z θ₀ g| ≤ b` uniformly over `Θ_set` —
  the boundedness needed by McDiarmid.
* `IsStarShapedEnvelope ψ` — the sub-root condition on the population complexity
  envelope.
* `RademacherUpperBound` — `ψ` upper-bounds the population Rademacher
  complexity of the centred loss class (zero-out `starHull` form) on a
  fold-B-sized sample drawn from `P_Z`, uniformly in `n`.

The Lipschitz control `norm F_θ ≤ L · ‖θ − θ₀‖` of the centred loss class
is **NOT** part of the regime; it is consumed only by the sharp bridge
`localEmpProcessModulus_of_localized_sharp` as a separate explicit
`(L : ℝ) (hL_nonneg) (hF_lip)` triple. The bounded fallback bridge does
not need it.

The `idx` parameter mirrors the global-Rademacher bridge
(`localEmpProcessModulus_of_bounded_rademacher`): FoML's symmetrization and
McDiarmid headlines need a countable index, while `S.Θ_set` is typically
uncountable. The bridge theorem lifts from the `ℕ`-indexed sup back to a
`↥S.Θ_set` sup via `separableSpaceSup_eq_real`.

The `norm` parameter is the choice of function-space norm (e.g. the
sup-norm or the population L²-norm) that the localization in
`RademacherUpperBound` is taken in. Downstream callers pick whichever
matches their critical-radius envelope `ψ`. -/
def LocalizedRademacherRegime
    (S : LearningSystem Ω μ Z P_Z Θ G) (_S_iid : IIDSample Ω Z μ P_Z)
    (_split : OneShotSplit _S_iid) (g : G)
    (idx : ℕ → S.Θ_set)
    (norm : (Z → ℝ) → ℝ)
    (ψ : ℕ → ℝ → ℝ) (b : ℝ) : Prop :=
  0 ≤ b ∧
    (∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b) ∧
    (∀ n, IsStarShapedEnvelope (ψ n)) ∧
    ∀ n : ℕ,
      RademacherUpperBound
        (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) (_split.foldB n).card (ψ (_split.foldB n).card)

/-- For [an orthogonal statistical-learning system](hyp:S), [an independent and identically distributed sample from its observation law](hyp:_S_iid), [a one-shot sample split](hyp:_split), [a nuisance function](hyp:g), [a sequence indexing candidate targets](hyp:idx), [a norm on real-valued observation functions](hyp:norm), [a family of real complexity envelopes](hyp:ψ), and [a real bound](hyp:b), the [almost-everywhere localized Rademacher regime](goal) requires: [the bound is nonnegative](step:1); [for almost every observation under the observation law, the centered loss is bounded in absolute value by that bound for every candidate target](step:2); [each complexity envelope is sub-root](step:3); and [at every sample size, the envelope upper-bounds the population Rademacher complexity of the indexed centered-loss class on the split's validation fold](step:4).

**Almost-everywhere localized regime predicate for a `LearningSystem`.**

This is the satisfiable analogue of `LocalizedRademacherRegime`: the centred-loss
envelope is required only under the population law. The sub-root and
Rademacher-envelope fields are unchanged. -/
def LocalizedRademacherRegimeAE
    (S : LearningSystem Ω μ Z P_Z Θ G) (_S_iid : IIDSample Ω Z μ P_Z)
    (_split : OneShotSplit _S_iid) (g : G)
    (idx : ℕ → S.Θ_set)
    (norm : (Z → ℝ) → ℝ)
    (ψ : ℕ → ℝ → ℝ) (b : ℝ) : Prop :=
  0 ≤ b ∧
    (∀ᵐ z ∂P_Z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b) ∧
    (∀ n, IsStarShapedEnvelope (ψ n)) ∧
    ∀ n : ℕ,
      RademacherUpperBound
        (fun (k : ℕ) (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) (_split.foldB n).card (ψ (_split.foldB n).card)

private lemma empRiskFoldB_centered_abs_le
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (hbound : ∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b)
    (n : ℕ) (ω : Ω) {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |empRiskFoldB S S_iid split n ω θ g
        - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b := by
  classical
  by_cases hm0 : (split.foldB n).card = 0
  · have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
    simp [empRiskFoldB, hfold_empty, hb]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    have hm_pos : 0 < ((split.foldB n).card : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    have hcenter :
        empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g =
          ((split.foldB n).card : ℝ)⁻¹ *
            ∑ i ∈ split.foldB n,
              (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
      simp [empRiskFoldB]
      ring
    rw [hcenter]
    calc
      |((split.foldB n).card : ℝ)⁻¹ *
          ∑ i ∈ split.foldB n,
            (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)|
          = ((split.foldB n).card : ℝ)⁻¹ *
              |∑ i ∈ split.foldB n,
                (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)| := by
            rw [abs_mul, abs_of_nonneg]
            exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ ((split.foldB n).card : ℝ)⁻¹ * (∑ _i ∈ split.foldB n, b) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                (Finset.sum_le_sum fun i _hi => hbound (S_iid.Z i ω) θ hθ)
            · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ = b := by
            simp
            field_simp [ne_of_gt hm_pos]

private lemma empRiskFoldB_centered_abs_le_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (n : ℕ) (ω : Ω)
    (hω : ∀ i ∈ split.foldB n, ∀ θ ∈ S.Θ_set,
      |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |empRiskFoldB S S_iid split n ω θ g
        - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b := by
  classical
  by_cases hm0 : (split.foldB n).card = 0
  · have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
    simp [empRiskFoldB, hfold_empty, hb]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    have hm_pos : 0 < ((split.foldB n).card : ℝ) := Nat.cast_pos.mpr hm_pos_nat
    have hcenter :
        empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g =
          ((split.foldB n).card : ℝ)⁻¹ *
            ∑ i ∈ split.foldB n,
              (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
      simp [empRiskFoldB]
      ring
    rw [hcenter]
    calc
      |((split.foldB n).card : ℝ)⁻¹ *
          ∑ i ∈ split.foldB n,
            (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)|
          = ((split.foldB n).card : ℝ)⁻¹ *
              |∑ i ∈ split.foldB n,
                (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)| := by
            rw [abs_mul, abs_of_nonneg]
            exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ ((split.foldB n).card : ℝ)⁻¹ * (∑ _i ∈ split.foldB n, b) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                (Finset.sum_le_sum fun i hi => hω i hi θ hθ)
            · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ = b := by
            simp
            field_simp [ne_of_gt hm_pos]

/-- **Uniform-bound fallback bridge.** Under [a localized Rademacher regime — a uniform
bound `b` on the centred pointwise loss difference together with a sub-root Rademacher-
complexity envelope ψ](hyp:hreg), and given that [the population excess risk at every
admissible parameter is likewise bounded by `b`](hyp:hpop_center), then for any confidence
level [`0 < δ ≤ 1`](hyp:_hδ,_hδ') [the local empirical-process modulus condition holds,
with the constant envelope `ρ n := √(2 · b)`](goal).

Under an `LocalizedRademacherRegime` and an explicit centred population-risk
bound, the `LocalEmpProcessModulus` predicate holds with the
conservative envelope `ρ n := √(2 · b)`.

This bridge is a **legitimate low-hypothesis option**: it does NOT use
the sub-root envelope `ψ`, the critical radius, the Lipschitz field, or
any concentration step. It only consumes the uniform centred bound
`b` from the regime plus the population-side bound `hpop_center`.
Useful when the caller has not (yet) supplied the critical-radius /
Rademacher integrability machinery required by
`localEmpProcessModulus_of_localized_sharp`, but already knows that the
centred loss is uniformly bounded.

The rate `ρ n := √(2 · b)` is a *constant* in `n`, so this version does
NOT recover the Foster–Syrgkanis Lemma 14 rate. Use the sharp variant
when the problem at hand has a critical radius.

**Hypotheses.** `[IsProbabilityMeasure μ]` is needed for the
`μ E ≥ 1 - ENNReal.ofReal δ` event-mass bound. The additional
`hpop_center` hypothesis records the population counterpart of the
pointwise centred-loss bound in `hreg`; it is necessary here because the
raw losses need not be integrable from the centred pointwise bound
alone. -/
theorem localEmpProcessModulus_of_localized_bounded
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set]
    (g : G)
    (idx : ℕ → S.Θ_set)
    {norm : (Z → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ} {b : ℝ}
    (hreg : LocalizedRademacherRegime S S_iid split g idx norm ψ b)
    (hpop_center : ∀ θ ∈ S.Θ_set, |S.L θ g - S.L S.θ₀ g| ≤ b)
    {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun _n => Real.sqrt (2 * b)) δ g := by
  intro n
  classical
  obtain ⟨hb, hbound, _hsub, _hub⟩ := hreg
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · rw [measure_univ]
    exact tsub_le_self
  · intro ω _ θ hθ
    have hpop_abs : |S.L θ g - S.L S.θ₀ g| ≤ b := hpop_center θ hθ
    have hemp_abs :
        |empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b :=
      empRiskFoldB_centered_abs_le S S_iid split hb hbound n ω hθ
    have hmain :
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g) ≤ 2 * b := by
      have hpop_le : S.L θ g - S.L S.θ₀ g ≤ b :=
        (le_abs_self _).trans hpop_abs
      have hemp_ge :
          -b ≤ empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g :=
        (abs_le.mp hemp_abs).1
      linarith
    have hρsq :
        (Real.sqrt (2 * b)) ^ 2 = 2 * b := by
      rw [Real.sq_sqrt]
      nlinarith
    have hρ_nonneg : 0 ≤ Real.sqrt (2 * b) := Real.sqrt_nonneg _
    have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
    calc
      (S.L θ g - S.L S.θ₀ g)
          - (empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g)
          ≤ 2 * b := hmain
      _ = (Real.sqrt (2 * b)) ^ 2 := hρsq.symm
      _ ≤ Real.sqrt (2 * b) * ‖θ - S.θ₀‖ + (Real.sqrt (2 * b)) ^ 2 := by
        nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]

/-- **Almost-everywhere uniform-bound fallback bridge.** Under [an almost-everywhere
localized Rademacher regime — a `P_Z`-a.e. bound `b` on the centred pointwise loss
difference together with a sub-root Rademacher-complexity envelope ψ](hyp:hreg), and given
that [the population excess risk at every admissible parameter is likewise bounded by
`b`](hyp:hpop_center), then for any confidence level [`0 < δ ≤ 1`](hyp:_hδ,_hδ') [the local
empirical-process modulus condition holds, with the constant envelope
`ρ n := √(2 · b)`](goal).

This is the a.e. analogue of
`localEmpProcessModulus_of_localized_bounded`. The event is the conull fold-B
sample event on which the centred-loss envelope holds at every estimation-fold
sample point. -/
theorem localEmpProcessModulus_of_localized_bounded_ae
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set]
    (g : G)
    (idx : ℕ → S.Θ_set)
    {norm : (Z → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ} {b : ℝ}
    (hreg : LocalizedRademacherRegimeAE S S_iid split g idx norm ψ b)
    (hpop_center : ∀ θ ∈ S.Θ_set, |S.L θ g - S.L S.θ₀ g| ≤ b)
    {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun _n => Real.sqrt (2 * b)) δ g := by
  intro n
  classical
  obtain ⟨hb, hbound_ae, _hsub, _hub⟩ := hreg
  let Gn : Set Ω :=
    {ω | ∀ i ∈ split.foldB n, ∀ θ ∈ S.Θ_set,
      |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b}
  have hsample_all_ae : ∀ i : ℕ, ∀ᵐ ω ∂μ,
      ∀ θ ∈ S.Θ_set,
        |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b := by
    intro i
    have hlaw_i : μ.map (S_iid.Z i) = P_Z := by
      rw [← (S_iid.identDist i).map_eq, S_iid.law]
    have hmap : ∀ᵐ z ∂μ.map (S_iid.Z i),
        ∀ θ ∈ S.Θ_set, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ≤ b := by
      simpa [hlaw_i] using hbound_ae
    exact ae_of_ae_map (S_iid.meas i).aemeasurable hmap
  have hGn_ae : ∀ᵐ ω ∂μ, ω ∈ Gn := by
    have hfin : ∀ᵐ ω ∂μ, ∀ i ∈ split.foldB n,
        ∀ θ ∈ S.Θ_set,
          |S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g| ≤ b := by
      simpa using (Finset.eventually_all (split.foldB n)).2
        (fun i _hi => hsample_all_ae i)
    simpa [Gn] using hfin
  have hGn_null : μ Gnᶜ = 0 := ae_iff.mp hGn_ae
  rcases exists_measurable_superset_of_null hGn_null with
    ⟨N, hGn_compl_subset_N, hN_meas, hN_null⟩
  refine ⟨Set.univ \ N, MeasurableSet.univ.diff hN_meas, ?_, ?_⟩
  · rw [measure_diff_null hN_null, measure_univ]
    exact tsub_le_self
  · intro ω hω θ hθ
    have hωG : ω ∈ Gn := by
      by_contra hnot
      exact hω.2 (hGn_compl_subset_N hnot)
    have hpop_abs : |S.L θ g - S.L S.θ₀ g| ≤ b := hpop_center θ hθ
    have hemp_abs :
        |empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g| ≤ b :=
      empRiskFoldB_centered_abs_le_ae S S_iid split hb n ω
        (by simpa [Gn] using hωG) hθ
    have hmain :
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g) ≤ 2 * b := by
      have hpop_le : S.L θ g - S.L S.θ₀ g ≤ b :=
        (le_abs_self _).trans hpop_abs
      have hemp_ge :
          -b ≤ empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g :=
        (abs_le.mp hemp_abs).1
      linarith
    have hρsq :
        (Real.sqrt (2 * b)) ^ 2 = 2 * b := by
      rw [Real.sq_sqrt]
      nlinarith
    have hρ_nonneg : 0 ≤ Real.sqrt (2 * b) := Real.sqrt_nonneg _
    have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
    calc
      (S.L θ g - S.L S.θ₀ g)
          - (empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g)
          ≤ 2 * b := hmain
      _ = (Real.sqrt (2 * b)) ^ 2 := hρsq.symm
      _ ≤ Real.sqrt (2 * b) * ‖θ - S.θ₀‖ + (Real.sqrt (2 * b)) ^ 2 := by
        nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]

/-- For [an orthogonal statistical-learning system](hyp:S) and [a real clamp radius](hyp:b), the [centered clamped target-minimization condition](goal) states that every candidate target has auxiliary population risk at least that of the designated target, where its excess loss relative to the designated target is clamped to $[-b,b]$.

The target minimizes the auxiliary population risk whose centered excess
loss has been clamped to radius `b`.

This is the minimizer condition needed when an a.e.-bounded empirical-process
proof replaces the original centered loss by
`ℓ(θ₀, g₀) + clamp(ℓ(θ, g₀) − ℓ(θ₀, g₀))`. -/
def CenteredClampedThetaMinimizes
    (S : LearningSystem Ω μ Z P_Z Θ G) (b : ℝ) : Prop :=
  ∀ θ ∈ S.Θ_set,
    ∫ z, S.ℓ z S.θ₀ S.g₀
        + max (-b) (min b (S.ℓ z S.θ₀ S.g₀ - S.ℓ z S.θ₀ S.g₀)) ∂P_Z
      ≤
    ∫ z, S.ℓ z S.θ₀ S.g₀
        + max (-b) (min b (S.ℓ z θ S.g₀ - S.ℓ z S.θ₀ S.g₀)) ∂P_Z

end OrthogonalLearning
end Estimation
end Causalean
