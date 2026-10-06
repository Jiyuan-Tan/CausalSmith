/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized regime bridge, Part 2: sharp everywhere-bounded result

This second part proves the sharp critical-radius bridge under an everywhere bounded centered
loss. Part 1 supplies the regime definitions and fallback bounds; Part 3 supplies the
almost-everywhere and singleton variants.

Sibling: `Causalean/Estimation/OrthogonalLearning/LocalEmpProcess/Rademacher.lean` realises the same predicate
under a global Rademacher bound. Downstream callers pick
whichever bridge fits the problem at hand; the localized version uses a
countable dense index to cover a separable target class.

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

## Fallback schema from Part 1

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
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Localized_Part1

/-! # Localized Rademacher Moduli

This second part proves `localEmpProcessModulus_of_localized_sharp`, the everywhere-bounded
separable critical-radius bridge with envelope
`(10 · L + 3) · criticalRadius (ψ |B(n)|)`. The regime definitions and fallback bounds are in
Part 1; the almost-everywhere and singleton forms are in Part 3.
-/

public section

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
  Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]
/-- **Localized critical-radius modulus, separable Foster–Syrgkanis form.** Fix [a learning
system](hyp:S), [an IID sample](hyp:S_iid), [a one-shot split](hyp:split), and [a nuisance
value](hyp:g). Suppose [the loss is continuous in the target for every observation](hyp:hg_cont)
and [a sequence of targets](hyp:idx) has [dense range](hyp:idx_dense). For [a localization
norm](hyp:norm), [complexity envelopes](hyp:ψ), and [constants `b`, `L`, and
`Rmax`](hyp:b,L,Rmax), assume [the indexed localized Rademacher regime](hyp:hreg), [nonnegativity
of `L`](hyp:hL_nonneg), [Lipschitz localization](hyp:hF_lip), [measurability](hyp:hℓ_meas),
[a nonnegative localization norm and its variance proxy](hyp:hnorm_nonneg,hvariance),
[integrability](hyp:hℓ_int), [the diameter bound](hyp:hF_diam), [positive critical
radii](hyp:hcrit_pos), [an indexed population Rademacher upper bound](hyp:hψ_ub),
[samplewise boundedness](hyp:_hrad_bdd), and [integrability of the empirical Rademacher
process](hyp:hrad_int). At [confidence `δ`](hyp:δ), with [`0 < δ ≤ 1`](hyp:hδ,hδ'), suppose
[one finite peeling depth covers `Rmax` and absorbs its concentration slack](hyp:hδ_dom). Then
[the local empirical-process modulus holds with the critical-radius envelope, using
`√(2b)` only when fold B is empty](goal).

The envelope is `(10 * L + 3) * criticalRadius (ψ |B(n)|)`, with the
deterministic `sqrt (2 * b)` fallback when fold B is empty.  A countable
dense family supplies the concentration event; continuity extends its closed
inequality to the full target class.  The single-depth condition `hδ_dom`
is the peeling-aware critical-radius lower bound in this scalar adaptation of
Foster--Syrgkanis Lemma 14. -/
theorem localEmpProcessModulus_of_localized_sharp
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set]
    (g : G)
    (hg_cont : ∀ z, Continuous fun (θ : S.Θ_set) => S.ℓ z θ.val g)
    (idx : ℕ → S.Θ_set)
    (idx_dense : DenseRange idx)
    {norm : (Z → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ} {b L Rmax : ℝ}
    (hreg : LocalizedRademacherRegime S S_iid split g idx norm ψ b)
    (hL_nonneg : 0 ≤ L)
    (hF_lip : ∀ θ ∈ S.Θ_set,
      norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) ≤ L * ‖θ - S.θ₀‖)
    (hnorm_nonneg : ∀ θ ∈ S.Θ_set,
      0 ≤ norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g))
    (hvariance : ∀ θ ∈ S.Θ_set,
      variance (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) P_Z ≤
        norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) ^ 2)
    (hℓ_meas : ∀ θ ∈ S.Θ_set, Measurable (fun z => S.ℓ z θ g))
    (hℓ_int : ∀ θ ∈ S.Θ_set, Integrable (fun z => S.ℓ z θ g) P_Z)
    (hF_diam : ∀ θ ∈ S.Θ_set,
      norm (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) ≤ Rmax)
    -- n-dependent critical-radius hypotheses (ψ m is the envelope at sample size m).
    (hcrit_pos : ∀ m : ℕ, 0 < criticalRadius (ψ m))
    (hψ_ub : ∀ m : ℕ,
      RademacherUpperBound
        (fun k (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) m (ψ m))
    -- BddAbove hypothesis needed by the bridge lemma inside `localized_uniform_deviation`.
    (_hrad_bdd : ∀ m r, ∀ S_fin : Fin m → Z, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam ℕ =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut
            (fun k (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
            norm r p (S_fin k)|))
    -- Integrability of the upper empirical Rademacher process; consumed by the
    -- bridge lemma inside `localized_uniform_deviation`.
    (hrad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              (fun k (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
              norm r) ((id : Z → Z) ∘ ω))
        (Measure.pi (fun _ => P_Z)))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    -- Critical-radius lower bound for the Lemma 14 adaptation (peeling-aware):
    -- for a dyadic shell count `K` covering `Rmax`, the normalized Bousquet
    -- slack at confidence `δ / (2 (K + 1))` is at most the critical radius.
    -- The `K + 1` accounts for the union over
    -- `K + 1` dyadic shells in the peeling argument; the factor `2` keeps the
    -- intersection event mass `≥ 1 − δ` strictly. This absorbs every
    -- shellwise variance-sensitive tails into the `δ_n²` part of the modulus.
    (hδ_dom : ∀ n : ℕ, 0 < (split.foldB n).card →
      ∃ K : ℕ,
      Rmax ≤ (criticalRadius (ψ (split.foldB n).card)) * (2 : ℝ) ^ K ∧
      2 * Real.sqrt
          ((1 + 8 * b) * Real.log (2 * ((K : ℝ) + 1) / δ) /
            (split.foldB n).card)
        + 8 * b * Real.log (2 * ((K : ℝ) + 1) / δ) /
            ((split.foldB n).card * criticalRadius (ψ (split.foldB n).card))
        ≤ criticalRadius (ψ (split.foldB n).card)) :
    LocalEmpProcessModulus S S_iid split
      (fun n =>
        if (split.foldB n).card = 0 then Real.sqrt (2 * b)
        else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) δ g := by
  intro n
  classical
  obtain ⟨hb, hbound, hsub, _hub_idx⟩ := hreg
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  by_cases hm0 : (split.foldB n).card = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ θ hθ
      have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
      have hcenter_int :
          Integrable (fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g) P_Z :=
        (hℓ_int θ hθ).sub (hℓ_int S.θ₀ S.θ₀_mem)
      have hmean_eq :
          (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
            S.L θ g - S.L S.θ₀ g := by
        change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
          (∫ z, S.ℓ z θ g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
        exact integral_sub (hℓ_int θ hθ) (hℓ_int S.θ₀ S.θ₀_mem)
      have hpop_abs : |S.L θ g - S.L S.θ₀ g| ≤ b := by
        rw [← hmean_eq]
        calc
          |∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z|
              ≤ ∫ z, |S.ℓ z θ g - S.ℓ z S.θ₀ g| ∂P_Z :=
                abs_integral_le_integral_abs
          _ ≤ ∫ _z, b ∂P_Z := by
                apply integral_mono
                · exact hcenter_int.abs
                · exact integrable_const b
                · intro z
                  exact hbound z θ hθ
          _ = b := by simp
      have hρsq :
          (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
           else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 =
            2 * b := by
        rw [if_pos hm0, Real.sq_sqrt]
        nlinarith
      have hρ_nonneg :
          0 ≤
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) := by
        rw [if_pos hm0]
        exact Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
      calc
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
            = S.L θ g - S.L S.θ₀ g := by
                simp [empRiskFoldB, hfold_empty]
        _ ≤ b := (le_abs_self _).trans hpop_abs
        _ ≤ 2 * b := by nlinarith
        _ =
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 :=
              hρsq.symm
        _ ≤
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) *
              ‖θ - S.θ₀‖
              +
            (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
             else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 := by
              nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]
  · have hm_pos_nat : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    let m : ℕ := (split.foldB n).card
    let δn : ℝ := criticalRadius (ψ m)
    haveI : Nonempty Z := nonempty_of_isProbabilityMeasure P_Z
    let F : ℕ → Z → ℝ :=
      fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g
    have hF_meas : ∀ k : ℕ, Measurable (F k) := by
      intro k
      exact (hℓ_meas (idx k).val (idx k).property).sub
        (hℓ_meas S.θ₀ S.θ₀_mem)
    let Rloc : LocalizedRegime Z ℕ Z F norm P_Z (id : Z → Z) :=
      { b := b
        b_nonneg := hb
        bound := by
          intro k z
          exact hbound z (idx k).val (idx k).property
        variance_proxy := by
          intro k
          simpa [F] using hvariance (idx k).val (idx k).property
        ψ := ψ
        ψ_isStarShapedEnvelope := hsub
        ψ_ub := by
          intro m'
          simpa [F] using hψ_ub m' }
    have hnonempty_modulus :
        ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
          ∀ ω ∈ E, ∀ i : ℕ,
            (S.L (idx i).val g - S.L S.θ₀ g)
              - (empRiskFoldB S S_iid split n ω (idx i).val g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
              ≤ ((10 * L + 3) * δn) * ‖(idx i).val - S.θ₀‖
                  + ((10 * L + 3) * δn) ^ 2 := by
      rcases hδ_dom n hm_pos_nat with ⟨K, hK, hslackK⟩
      have hfoldB_peeling_bridge :
          ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
            ∀ ω ∈ E, ∀ i : ℕ,
              (S.L (idx i).val g - S.L S.θ₀ g)
                - (empRiskFoldB S S_iid split n ω (idx i).val g
                    - empRiskFoldB S S_iid split n ω S.θ₀ g)
                ≤ 10 * L * δn * ‖(idx i).val - S.θ₀‖
                    + 5 * δn ^ 2 := by
        let η : ℝ := δ / (2 * ((K : ℝ) + 1))
        have hη_pos : 0 < η := by
          have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
          exact div_pos hδ hden
        have hη_le_one : η ≤ 1 := by
          have hden_pos : 0 < 2 * ((K : ℝ) + 1) := by positivity
          have hden_ge_one : 1 ≤ 2 * ((K : ℝ) + 1) := by
            have hK_nonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg K
            nlinarith
          dsimp [η]
          rw [div_le_iff₀ hden_pos]
          nlinarith [hδ']
        have hEk_per_shell :
            ∀ k : Fin (K + 1),
              ∃ E_k : Set (Fin m → Z), MeasurableSet E_k ∧
                Measure.pi (fun _ : Fin m => P_Z) E_k ≥ 1 - ENNReal.ofReal η ∧
                ∀ ω ∈ E_k, ∀ i : ℕ,
                  norm (F i) ≤ δn * (2 : ℝ) ^ (k : ℕ) →
                    |(m : ℝ)⁻¹ *
                        (Finset.univ.sum fun j : Fin m => F i ((id : Z → Z) (ω j)))
                        - P_Z[fun z => F i ((id : Z → Z) z)]|
                      ≤ 5 * (δn * (2 : ℝ) ^ (k : ℕ)) * δn := by
          intro k
          have hr_lb : criticalRadius (Rloc.ψ m) ≤ δn * (2 : ℝ) ^ (k : ℕ) := by
            have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) := by
              exact one_le_pow₀ (a := (2 : ℝ)) (n := (k : ℕ))
                (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
            have hδn_nonneg : 0 ≤ δn := le_of_lt (hcrit_pos m)
            simpa [Rloc, δn] using
              (mul_le_mul_of_nonneg_left hpow_one hδn_nonneg)
          rcases localized_uniform_deviation F norm P_Z (id : Z → Z)
              measurable_id hF_meas
              (fun i => by simpa [F] using hnorm_nonneg (idx i).val (idx i).property)
              Rloc hη_pos hη_le_one m
              (by simpa [m] using hm_pos_nat)
              (r := δn * (2 : ℝ) ^ (k : ℕ))
              hr_lb
              (by simpa [Rloc, δn] using hcrit_pos m)
              (by simpa [F] using _hrad_bdd m (δn * (2 : ℝ) ^ (k : ℕ)))
              (by simpa [F, Function.comp_def] using
                hrad_int m (δn * (2 : ℝ) ^ (k : ℕ))) with
            ⟨E_k, hE_k_meas, hE_k_prob, hE_k_bound⟩
          refine ⟨E_k, hE_k_meas, hE_k_prob, ?_⟩
          intro ω hω i hir
          have h := hE_k_bound ω hω i hir
          have hη_inv : 1 / η = 2 * ((K : ℝ) + 1) / δ := by
            dsimp [η]
            field_simp [ne_of_gt hδ]
          have hx : 0 ≤ Real.log (2 * ((K : ℝ) + 1) / δ) := by
            apply Real.log_nonneg
            rw [le_div_iff₀ hδ]
            nlinarith [hδ', (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))]
          have htail := bousquet_shell_slack_le
            (b := b) (ρ := δn) (q := δn * (2 : ℝ) ^ (k : ℕ))
            (c := criticalRadius (ψ m))
            (x := Real.log (2 * ((K : ℝ) + 1) / δ)) (n := m)
            hb (by simpa [δn] using hcrit_pos m)
            (by
              have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) :=
                one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
              simpa [δn] using mul_le_mul_of_nonneg_left hpow (hcrit_pos m).le)
            (by simp [δn]) hx (by show 0 < m; simpa [m] using hm_pos_nat)
            (by simpa [m, δn] using hslackK)
          rw [hη_inv] at h
          calc
            _ ≤ 4 * (δn * (2 : ℝ) ^ (k : ℕ)) * criticalRadius (ψ m)
                + 2 * Real.sqrt
                    (((δn * (2 : ℝ) ^ (k : ℕ)) ^ 2 +
                      8 * b * (δn * (2 : ℝ) ^ (k : ℕ)) *
                        criticalRadius (ψ m)) *
                      Real.log (2 * ((K : ℝ) + 1) / δ) / m)
                + 8 * b * Real.log (2 * ((K : ℝ) + 1) / δ) / m := by
              simpa [Rloc, δn, one_div, div_eq_mul_inv, mul_comm, mul_left_comm,
                mul_assoc] using h
            _ ≤ 5 * (δn * (2 : ℝ) ^ (k : ℕ)) * δn := by
              have hq0 : 0 ≤ δn * (2 : ℝ) ^ (k : ℕ) :=
                mul_nonneg (by simpa [δn] using (hcrit_pos m).le) (by positivity)
              have hcrit : criticalRadius (ψ m) = δn := rfl
              rw [hcrit] at htail ⊢
              nlinarith
        have hEtot_intersection :
            ∃ Etot : Set (Fin m → Z), MeasurableSet Etot ∧
              Measure.pi (fun _ : Fin m => P_Z) Etot ≥ 1 - ENNReal.ofReal δ ∧
              ∀ k : Fin (K + 1), Etot ⊆ (hEk_per_shell k).choose := by
          let μπ : Measure (Fin m → Z) := Measure.pi (fun _ : Fin m => P_Z)
          let Ek : Fin (K + 1) → Set (Fin m → Z) :=
            fun k => (hEk_per_shell k).choose
          let Etot : Set (Fin m → Z) := ⋂ k, Ek k
          have hEk_meas : ∀ k, MeasurableSet (Ek k) := by
            intro k
            exact (hEk_per_shell k).choose_spec.1
          have hEk_compl_le : ∀ k, μπ ((Ek k)ᶜ) ≤ ENNReal.ofReal η := by
            intro k
            have hprob : μπ (Ek k) ≥ 1 - ENNReal.ofReal η :=
              (hEk_per_shell k).choose_spec.2.1
            have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal η + μπ (Ek k) := by
              simpa [add_comm] using (tsub_le_iff_right.mp hprob)
            rw [measure_compl (hEk_meas k) (measure_ne_top _ _), measure_univ]
            exact tsub_le_iff_right.mpr hone_le
          have hEtot_meas : MeasurableSet Etot := by
            exact MeasurableSet.iInter hEk_meas
          have hbad_subset : Etotᶜ ⊆ ⋃ k, (Ek k)ᶜ := by
            simp [Etot]
          have hbad_le : μπ (Etotᶜ) ≤ ENNReal.ofReal δ := by
            calc
              μπ (Etotᶜ) ≤ μπ (⋃ k, (Ek k)ᶜ) := measure_mono hbad_subset
              _ ≤ ∑ k : Fin (K + 1), μπ ((Ek k)ᶜ) :=
                measure_iUnion_fintype_le μπ fun k => (Ek k)ᶜ
              _ ≤ ∑ _k : Fin (K + 1), ENNReal.ofReal η := by
                exact Finset.sum_le_sum fun k _hk => hEk_compl_le k
              _ = (K + 1 : ℕ) * ENNReal.ofReal η := by simp
              _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ)) * ENNReal.ofReal η := by
                have hcoe :
                    ((K : ENNReal) + 1) = ENNReal.ofReal ((K : ℝ) + 1) := by
                  calc
                    ((K : ENNReal) + 1)
                        = ENNReal.ofReal (K : ℝ) + ENNReal.ofReal (1 : ℝ) := by
                          simp
                    _ = ENNReal.ofReal ((K : ℝ) + 1) :=
                          (ENNReal.ofReal_add (Nat.cast_nonneg K) (by norm_num)).symm
                simpa [Nat.cast_add, Nat.cast_one] using congrArg
                  (fun x => x * ENNReal.ofReal η) hcoe
              _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * η) := by
                rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (((K + 1 : ℕ) : ℝ)))]
              _ = ENNReal.ofReal (δ / 2) := by
                congr 1
                dsimp [η]
                have hcast : (((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1) := by norm_num
                rw [hcast]
                field_simp
              _ ≤ ENNReal.ofReal δ := by
                exact ENNReal.ofReal_le_ofReal (by linarith [hδ])
          refine ⟨Etot, hEtot_meas, ?_, ?_⟩
          · rw [measure_compl hEtot_meas (measure_ne_top _ _), measure_univ] at hbad_le
            have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal δ + μπ Etot :=
              tsub_le_iff_right.mp hbad_le
            exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
          · intro k
            exact Set.iInter_subset (fun k => Ek k) k
        rcases hEtot_intersection with ⟨Etot, hEtot_meas, hEtot_prob, hEtot_subset⟩
        let e : Fin m ≃o split.foldB n := (split.foldB n).orderIsoOfFin rfl
        let Y : Ω → Fin m → Z := fun ω j => S_iid.Z (e j).val ω
        have hY_meas : Measurable Y := by
          apply measurable_pi_lambda
          intro j
          exact S_iid.meas (e j).val
        have hY_law : μ.map Y = Measure.pi (fun _ : Fin m => P_Z) := by
          let YB : Ω → split.foldB n → Z := fun ω i => S_iid.Z i.val ω
          let T : (split.foldB n → Z) ≃ᵐ (Fin m → Z) :=
            MeasurableEquiv.piCongrLeft (fun _ : Fin m => Z) e.symm.toEquiv
          have hY_eq : Y = T ∘ YB := by
            funext ω j
            simpa [Y, YB, T] using
              (MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm.toEquiv)
                (β := fun _ : Fin m => Z)
                (x := fun i : split.foldB n => S_iid.Z i.val ω) (i := e j)).symm
          rw [hY_eq, ← Measure.map_map T.measurable
            (measurable_pi_lambda YB fun i => S_iid.meas i.val)]
          · rw [Causalean.Stat.oneShot_iid S_iid split n]
            simpa [T] using Measure.pi_map_piCongrLeft (e := e.symm.toEquiv)
              (β := fun _ : Fin m => Z) (μ := fun _ : Fin m => P_Z)
        refine ⟨Y ⁻¹' Etot, hEtot_meas.preimage hY_meas, ?_, ?_⟩
        · rw [← Measure.map_apply hY_meas hEtot_meas, hY_law]
          exact hEtot_prob
        · intro ω hω i
          let θs : S.Θ_set := idx i
          have hShell_select :
              ∃ k₀ : Fin (K + 1),
                norm (F i) ≤ δn * (2 : ℝ) ^ (k₀ : ℕ) ∧
                5 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn
                  ≤ 10 * L * δn * ‖θs.val - S.θ₀‖ + 5 * δn ^ 2 := by
            have hδn_pos : 0 < δn := hcrit_pos m
            have hδn_nonneg : 0 ≤ δn := le_of_lt hδn_pos
            have hnormF_le_L :
                norm (F i) ≤ L * ‖θs.val - S.θ₀‖ := by
              simpa [F, θs] using hF_lip θs.val θs.property
            have htop : norm (F i) ≤ δn * (2 : ℝ) ^ K := by
              exact (hF_diam θs.val θs.property).trans hK
            by_cases hsmall : norm (F i) ≤ δn
            · let kzero : Fin (K + 1) := ⟨0, Nat.succ_pos K⟩
              refine ⟨kzero, ?_, ?_⟩
              · change norm (F i) ≤ δn * (2 : ℝ) ^ (0 : ℕ)
                rw [pow_zero, mul_one]
                exact hsmall
              · have hLdist_nonneg : 0 ≤ L * ‖θs.val - S.θ₀‖ :=
                  mul_nonneg hL_nonneg (norm_nonneg _)
                have hnonneg : 0 ≤ 10 * δn * (L * ‖θs.val - S.θ₀‖) := by
                  nlinarith [hδn_nonneg, hLdist_nonneg]
                change 5 * (δn * (2 : ℝ) ^ (0 : ℕ)) * δn
                    ≤ 10 * L * δn * ‖θs.val - S.θ₀‖ + 5 * δn ^ 2
                rw [pow_zero, mul_one]
                nlinarith [hnonneg, sq_nonneg δn]
            · let p : ℕ → Prop := fun j => norm (F i) ≤ δn * (2 : ℝ) ^ j
              have hex : ∃ j, p j := ⟨K, htop⟩
              let j0 : ℕ := Nat.find hex
              have hj0_spec : p j0 := Nat.find_spec hex
              have hj0_pos : 0 < j0 := by
                by_contra hj0_not
                have hj0_zero : j0 = 0 := Nat.eq_zero_of_not_pos hj0_not
                have : norm (F i) ≤ δn := by
                  change norm (F i) ≤ δn * (2 : ℝ) ^ j0 at hj0_spec
                  rw [hj0_zero, pow_zero, mul_one] at hj0_spec
                  exact hj0_spec
                exact hsmall this
              have hj0_le_K : j0 ≤ K := Nat.find_min' hex htop
              refine ⟨⟨j0, Nat.lt_succ_of_le hj0_le_K⟩, hj0_spec, ?_⟩
              have hprev_not : ¬ p (j0 - 1) := by
                have hlt : j0 - 1 < j0 := Nat.sub_one_lt (Nat.ne_of_gt hj0_pos)
                exact Nat.find_min hex hlt
              have hprev_lt : δn * (2 : ℝ) ^ (j0 - 1) < norm (F i) := by
                exact not_le.mp hprev_not
              have hr_le_normF : δn * (2 : ℝ) ^ j0 ≤ 2 * norm (F i) := by
                have hj0_eq : j0 = (j0 - 1) + 1 := by omega
                have hpow :
                    (2 : ℝ) ^ j0 = (2 : ℝ) ^ (j0 - 1) * 2 := by
                  conv_lhs => rw [hj0_eq, pow_succ]
                rw [hpow]
                nlinarith
              have hr_le_L : δn * (2 : ℝ) ^ j0 ≤ 2 * L * ‖θs.val - S.θ₀‖ := by
                nlinarith [hr_le_normF, hnormF_le_L]
              nlinarith [mul_le_mul_of_nonneg_right hr_le_L (by nlinarith : 0 ≤ 5 * δn),
                hδn_nonneg, sq_nonneg δn]
          rcases hShell_select with ⟨k₀, hk₀_radius, hk₀_rate⟩
          have hEk_bound := (hEk_per_shell k₀).choose_spec.2.2
          have hY_in_Ek : Y ω ∈ (hEk_per_shell k₀).choose :=
            hEtot_subset k₀ hω
          have hdev := hEk_bound (Y ω) hY_in_Ek i hk₀_radius
          have hsum_reindex :
              (Finset.univ.sum fun j : Fin m => F i (Y ω j)) =
                ∑ i ∈ split.foldB n,
                  (S.ℓ (S_iid.Z i ω) θs.val g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
            have hsum_subtype :
                (Finset.univ.sum fun j : Fin m => F i (Y ω j)) =
                  ∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θs.val g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g) :=
              Fintype.sum_equiv e.toEquiv (fun j => F i (Y ω j))
                (fun i : split.foldB n =>
                  S.ℓ (S_iid.Z i.val ω) θs.val g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)
                (by intro j; rfl)
            have hsum_attach :
                (∑ i : split.foldB n,
                    (S.ℓ (S_iid.Z i.val ω) θs.val g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)) =
                  ∑ i ∈ split.foldB n,
                    (S.ℓ (S_iid.Z i ω) θs.val g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
              simpa using Finset.sum_attach (s := split.foldB n)
                (f := fun i =>
                  S.ℓ (S_iid.Z i ω) θs.val g - S.ℓ (S_iid.Z i ω) S.θ₀ g)
            exact hsum_subtype.trans hsum_attach
          have hmean_eq :
              (∫ z, F i z ∂P_Z) = S.L θs.val g - S.L S.θ₀ g := by
            change (∫ z, S.ℓ z θs.val g - S.ℓ z S.θ₀ g ∂P_Z) =
              S.L θs.val g - S.L S.θ₀ g
            change (∫ z, S.ℓ z θs.val g - S.ℓ z S.θ₀ g ∂P_Z) =
              (∫ z, S.ℓ z θs.val g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
            exact integral_sub (hℓ_int θs.val θs.property) (hℓ_int S.θ₀ S.θ₀_mem)
          have hcenter_abs :
              |(empRiskFoldB S S_iid split n ω θs.val g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
                - (S.L θs.val g - S.L S.θ₀ g)|
                ≤ 5 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn := by
            have hdev' :
                |(m : ℝ)⁻¹ *
                    (∑ i ∈ split.foldB n,
                      (S.ℓ (S_iid.Z i ω) θs.val g - S.ℓ (S_iid.Z i ω) S.θ₀ g))
                    - (S.L θs.val g - S.L S.θ₀ g)|
                  ≤ 5 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn := by
              simpa [hmean_eq, hsum_reindex] using hdev
            convert hdev' using 1
            simp [empRiskFoldB, m]
            ring_nf
          have hmain :
              (S.L θs.val g - S.L S.θ₀ g)
                - (empRiskFoldB S S_iid split n ω θs.val g
                    - empRiskFoldB S S_iid split n ω S.θ₀ g)
                ≤ 5 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn := by
            have := neg_le_abs ((empRiskFoldB S S_iid split n ω θs.val g
                  - empRiskFoldB S S_iid split n ω S.θ₀ g)
                - (S.L θs.val g - S.L S.θ₀ g))
            linarith
          have hrate :
              5 * (δn * (2 : ℝ) ^ (k₀ : ℕ)) * δn
                ≤ 10 * L * δn * ‖θs.val - S.θ₀‖ + 5 * δn ^ 2 := hk₀_rate
          exact hmain.trans hrate
      rcases hfoldB_peeling_bridge with ⟨E, hE_meas, hE_prob, hE_bound⟩
      refine ⟨E, hE_meas, hE_prob, ?_⟩
      intro ω hω i
      have hdev := hE_bound ω hω i
      have hpackaging :
          10 * L * δn * ‖(idx i).val - S.θ₀‖ + 5 * δn ^ 2
            ≤ ((10 * L + 3) * δn) * ‖(idx i).val - S.θ₀‖
                + ((10 * L + 3) * δn) ^ 2 := by
        have hδn_pos : 0 < δn := hcrit_pos m
        have hδn_nn : 0 ≤ δn := le_of_lt hδn_pos
        have hL_nn : 0 ≤ L := hL_nonneg
        have hnorm_nn : 0 ≤ ‖(idx i).val - S.θ₀‖ := norm_nonneg _
        nlinarith [sq_nonneg ((10 * L + 3) * δn),
          mul_nonneg hL_nn hnorm_nn, mul_nonneg hδn_nn hnorm_nn,
          mul_nonneg (mul_nonneg hL_nn hδn_nn) hnorm_nn,
          sq_nonneg L, sq_nonneg δn, mul_self_nonneg δn]
      exact hdev.trans hpackaging
    rcases hnonempty_modulus with ⟨E, hE_meas, hE_prob, hE_bound⟩
    refine ⟨E, hE_meas, hE_prob, ?_⟩
    intro ω hω θ hθ
    let A : S.Θ_set → ℝ := fun ϑ =>
      (∫ z, S.ℓ z ϑ.val g - S.ℓ z S.θ₀ g ∂P_Z)
        - (empRiskFoldB S S_iid split n ω ϑ.val g
            - empRiskFoldB S S_iid split n ω S.θ₀ g)
    let B : S.Θ_set → ℝ := fun ϑ =>
      ((10 * L + 3) * δn) * ‖ϑ.val - S.θ₀‖ + ((10 * L + 3) * δn) ^ 2
    have hcenter_cont : Continuous fun ϑ : S.Θ_set =>
        ∫ z, S.ℓ z ϑ.val g - S.ℓ z S.θ₀ g ∂P_Z := by
      apply MeasureTheory.continuous_of_dominated
      · intro ϑ
        exact ((hℓ_meas ϑ.val ϑ.property).sub
          (hℓ_meas S.θ₀ S.θ₀_mem)).aestronglyMeasurable
      · intro ϑ
        filter_upwards [] with z
        simpa [Real.norm_eq_abs] using hbound z ϑ.val ϑ.property
      · exact integrable_const b
      · filter_upwards [] with z
        exact (hg_cont z).sub continuous_const
    have hemp_cont : Continuous fun ϑ : S.Θ_set =>
        empRiskFoldB S S_iid split n ω ϑ.val g := by
      unfold empRiskFoldB
      exact continuous_const.mul
        (continuous_finset_sum (split.foldB n) fun i _ => hg_cont (S_iid.Z i ω))
    have hA_cont : Continuous A := by
      exact hcenter_cont.sub (hemp_cont.sub continuous_const)
    have hB_cont : Continuous B := by
      have hdist : Continuous fun ϑ : S.Θ_set => ‖ϑ.val - S.θ₀‖ := by fun_prop
      exact continuous_const.mul hdist |>.add continuous_const
    have hclosed : IsClosed {ϑ | A ϑ ≤ B ϑ} := isClosed_le hA_cont hB_cont
    have hrange : Set.range idx ⊆ {ϑ | A ϑ ≤ B ϑ} := by
      rintro _ ⟨i, rfl⟩
      have hmean_eq :
          (∫ z, S.ℓ z (idx i).val g - S.ℓ z S.θ₀ g ∂P_Z) =
            S.L (idx i).val g - S.L S.θ₀ g := by
        change (∫ z, S.ℓ z (idx i).val g - S.ℓ z S.θ₀ g ∂P_Z) =
          (∫ z, S.ℓ z (idx i).val g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
        exact integral_sub (hℓ_int (idx i).val (idx i).property)
          (hℓ_int S.θ₀ S.θ₀_mem)
      simpa [A, B, hmean_eq] using hE_bound ω hω i
    have hall : ∀ ϑ : S.Θ_set, A ϑ ≤ B ϑ := by
      intro ϑ
      exact (closure_minimal hrange hclosed) (by
        rw [idx_dense.closure_range]
        trivial)
    let ϑ : S.Θ_set := ⟨θ, hθ⟩
    have hmean_eq :
        (∫ z, S.ℓ z ϑ.val g - S.ℓ z S.θ₀ g ∂P_Z) =
          S.L θ g - S.L S.θ₀ g := by
      change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
        (∫ z, S.ℓ z θ g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
      exact integral_sub (hℓ_int θ hθ) (hℓ_int S.θ₀ S.θ₀_mem)
    simpa [A, B, ϑ, hmean_eq, hm0, m, δn] using hall ϑ

end OrthogonalLearning
end Estimation
end Causalean
