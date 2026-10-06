/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized regime bridge, Part 3: almost-everywhere and singleton results

This third part proves the almost-everywhere sharp critical-radius bridge and the singleton-class
result. Parts 1 and 2 supply the definitions, fallback bounds, and everywhere-bounded sharp bridge.

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
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Localized_Part2

/-! # Localized Rademacher Moduli

This third part proves the almost-everywhere sharp critical-radius bridge
`localEmpProcessModulus_of_localized_sharp_ae` and the singleton-class result
`localEmpProcessModulus_of_localized_singleton`, building on Parts 1 and 2.
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
/-- **Almost-everywhere separable localized bridge.** Fix a separable,
densely-indexed target class on which [the loss is continuous in the parameter for every
observation](hyp:hg_cont) and [the chosen function-space norm is invariant under
`P_Z`-a.e. equality of its argument](hyp:hnorm_ae). Assume [an almost-everywhere localized
Rademacher regime holds — a uniform centred-loss bound and a sub-root Rademacher-complexity
envelope ψ](hyp:hreg), that [the Lipschitz constant `L` is nonnegative](hyp:hL_nonneg), that
[the norm of the centred loss difference at each parameter is bounded by
`L · ‖θ − θ₀‖`](hyp:hF_lip), that [the localization norm is nonnegative and controls
variance](hyp:hnorm_nonneg,hvariance), that [the loss at each parameter is measurable](hyp:hℓ_meas)
and [integrable under `P_Z`](hyp:hℓ_int), and that [the same centred loss difference has
diameter at most `Rmax` in that norm](hyp:hF_diam). Assume the critical radius of ψ at
every fold-B sample size satisfies [`criticalRadius (ψ m) > 0`](hyp:hcrit_pos), and that
[ψ upper-bounds the population Rademacher
complexity of the star-hulled centred loss class on a fold-B-sized sample](hyp:hψ_ub); the
technical regularity conditions that [the empirical Rademacher supremum is bounded
above](hyp:hrad_bdd) and [the upper empirical Rademacher complexity process is
integrable](hyp:hrad_int); and that [the population-optimal parameter minimizes the
auxiliary population risk with the centred excess loss clamped to
`[-b, b]`](hyp:hclamp_minimizes). For any confidence level [`0 < δ ≤ 1`](hyp:hδ,hδ'), assume the
Foster–Syrgkanis peeling-absorption condition that [at one dyadic shell count covering
`Rmax`, the normalized Bousquet slack at the union-bound-adjusted confidence is at most the
critical radius](hyp:hδ_dom). Then [the local empirical-process
modulus condition holds, with envelope `ρ n := (10 · L + 3) · criticalRadius (ψ |foldB n|)`
(falling back to `√(2 · b)` when the fold-B sample is empty)](goal).

This is the a.e. analogue of `localEmpProcessModulus_of_localized_sharp`.
The centred envelope is assumed only under `P_Z`, the target class is
required to have a countable dense indexing sequence, and the function-space
norm is assumed invariant under `P_Z`-a.e. equality. The proof applies the
pointwise theorem to the auxiliary system whose centred loss is clamped to
`[-b, b]`, then transfers the resulting fold-B event back to the original
system on the conull sample event where the clamp is inactive. -/
theorem localEmpProcessModulus_of_localized_sharp_ae
    (S : LearningSystem Ω μ Z P_Z Θ G) [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z) (split : OneShotSplit S_iid)
    [Nonempty S.Θ_set]
    (g : G)
    (hg_cont : ∀ z, Continuous fun (θ : S.Θ_set) => S.ℓ z θ.val g)
    (idx : ℕ → S.Θ_set)
    (idx_dense : DenseRange idx)
    {norm : (Z → ℝ) → ℝ}
    (hnorm_ae : ∀ F F' : Z → ℝ, F =ᵐ[P_Z] F' → norm F = norm F')
    {ψ : ℕ → ℝ → ℝ} {b L Rmax : ℝ}
    (hreg : LocalizedRademacherRegimeAE S S_iid split g idx norm ψ b)
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
    (hcrit_pos : ∀ m : ℕ, 0 < criticalRadius (ψ m))
    (hψ_ub : ∀ m : ℕ,
      RademacherUpperBound
        (fun k (z : Z) => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
        norm P_Z (id : Z → Z) m (ψ m))
    (hrad_bdd : ∀ m r, ∀ S_fin : Fin m → Z, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam ℕ =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut
            (fun i (z : Z) => S.ℓ z (idx i).val g - S.ℓ z S.θ₀ g)
            norm r p (S_fin k)|))
    (hrad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              (fun i (z : Z) => S.ℓ z (idx i).val g - S.ℓ z S.θ₀ g)
              norm r) ((id : Z → Z) ∘ ω))
        (Measure.pi (fun _ => P_Z)))
    (hclamp_minimizes : CenteredClampedThetaMinimizes S b)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
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
  classical
  obtain ⟨hb, hbound_ae, hsub, hub_idx⟩ := hreg
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  let clamp : ℝ → ℝ := fun t => max (-b) (min b t)
  let Sc : LearningSystem Ω μ Z P_Z Θ G :=
    { S with
      ℓ := fun z θ g' =>
        S.ℓ z S.θ₀ g' + clamp (S.ℓ z θ g' - S.ℓ z S.θ₀ g')
      ℓ_meas := fun θ g' => by
        dsimp [clamp]
        exact (S.ℓ_meas S.θ₀ g').add
          (measurable_const.max
            (measurable_const.min ((S.ℓ_meas θ g').sub (S.ℓ_meas S.θ₀ g'))))
      θ₀_minimizes := by
        intro θ hθ
        simpa [CenteredClampedThetaMinimizes, clamp] using hclamp_minimizes θ hθ }
  have hclamp_abs : ∀ t : ℝ, |clamp t| ≤ b := by
    intro t
    rw [abs_le]
    constructor
    · dsimp [clamp]
      exact le_max_left (-b) (min b t)
    · dsimp [clamp]
      exact max_le (by linarith) (min_le_left b t)
  have hclamp_zero : clamp 0 = 0 := by
    dsimp [clamp]
    rw [min_eq_right hb, max_eq_right]
    linarith
  have hclamp_eq_of_abs_le : ∀ {t : ℝ}, |t| ≤ b → clamp t = t := by
    intro t ht
    have ht_low : -b ≤ t := (abs_le.mp ht).1
    have ht_high : t ≤ b := (abs_le.mp ht).2
    dsimp [clamp]
    rw [min_eq_right ht_high, max_eq_right ht_low]
  have hSc_center :
      ∀ z θ, θ ∈ S.Θ_set →
        Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g =
          clamp (S.ℓ z θ g - S.ℓ z S.θ₀ g) := by
    intro z θ _hθ
    dsimp [Sc]
    have hzero_arg : S.ℓ z S.θ₀ g - S.ℓ z S.θ₀ g = 0 := by ring
    rw [hzero_arg]
    rw [hclamp_zero]
    ring
  have hSc_bound :
      ∀ z, ∀ θ ∈ Sc.Θ_set, |Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g| ≤ b := by
    intro z θ hθ
    rw [hSc_center z θ (by simpa [Sc] using hθ)]
    exact hclamp_abs _
  let Fs : S.Θ_set → Z → ℝ :=
    fun θ z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g
  let Fc : S.Θ_set → Z → ℝ :=
    fun θ z => Sc.ℓ z θ.val g - Sc.ℓ z Sc.θ₀ g
  have hcenter_all_ae :
      ∀ᵐ z ∂P_Z, ∀ θ : S.Θ_set, Fs θ z = Fc θ z := by
    filter_upwards [hbound_ae] with z hz θ
    have hc := hclamp_eq_of_abs_le (hz θ.val θ.property)
    calc
      Fs θ z = S.ℓ z θ.val g - S.ℓ z S.θ₀ g := rfl
      _ = clamp (S.ℓ z θ.val g - S.ℓ z S.θ₀ g) := hc.symm
      _ = Fc θ z := by
        dsimp [Fc]
        rw [hSc_center z θ.val θ.property]
  have hstar_all_ae :
      ∀ r : ℝ, ∀ᵐ z ∂P_Z, ∀ p : starHullParam S.Θ_set,
        starHullZeroOut Fs norm r p z = starHullZeroOut Fc norm r p z := by
    intro r
    filter_upwards [hcenter_all_ae] with z hz p
    have hstar_ae : starHullEval Fs p =ᵐ[P_Z] starHullEval Fc p := by
      filter_upwards [hcenter_all_ae] with z' hz'
      dsimp [starHullEval]
      rw [hz' p.2]
    have hnorm_eq : norm (starHullEval Fs p) = norm (starHullEval Fc p) :=
      hnorm_ae _ _ hstar_ae
    have hpval : starHullEval Fs p z = starHullEval Fc p z := by
      dsimp [starHullEval]
      rw [hz p.2]
    by_cases hp : norm (starHullEval Fs p) ≤ r
    · have hpc : norm (starHullEval Fc p) ≤ r := hnorm_eq ▸ hp
      change
        (if norm (starHullEval Fs p) ≤ r then starHullEval Fs p z else 0) =
          (if norm (starHullEval Fc p) ≤ r then starHullEval Fc p z else 0)
      rw [if_pos hp, if_pos hpc]
      exact hpval
    · have hpc : ¬ norm (starHullEval Fc p) ≤ r := by
        intro hc
        exact hp (hnorm_eq.symm ▸ hc)
      change
        (if norm (starHullEval Fs p) ≤ r then starHullEval Fs p z else 0) =
          (if norm (starHullEval Fc p) ≤ r then starHullEval Fc p z else 0)
      rw [if_neg hp, if_neg hpc]
  have hℓ_all_ae :
      ∀ᵐ z ∂P_Z, ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
    filter_upwards [hbound_ae] with z hz θ hθ
    have hc := hclamp_eq_of_abs_le (hz θ hθ)
    dsimp [Sc]
    rw [hc]
    ring
  have hL_eq : ∀ θ, θ ∈ S.Θ_set → S.L θ g = Sc.L θ g := by
    intro θ hθ
    dsimp [LearningSystem.L]
    apply integral_congr_ae
    filter_upwards [hℓ_all_ae] with z hz
    exact hz θ hθ
  have hSc_lip : ∀ θ ∈ Sc.Θ_set,
      norm (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) ≤ L * ‖θ - Sc.θ₀‖ := by
    intro θ hθ
    have hθS : θ ∈ S.Θ_set := by simpa [Sc] using hθ
    have hae : (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) =ᵐ[P_Z]
        fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g := by
      filter_upwards [hcenter_all_ae] with z hz
      exact (hz ⟨θ, hθS⟩).symm
    rw [hnorm_ae _ _ hae]
    simpa [Sc] using hF_lip θ hθS
  have hSc_norm_nonneg : ∀ θ ∈ Sc.Θ_set,
      0 ≤ norm (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) := by
    intro θ hθ
    have hθS : θ ∈ S.Θ_set := by simpa [Sc] using hθ
    have hae : (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) =ᵐ[P_Z]
        fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g := by
      filter_upwards [hcenter_all_ae] with z hz
      exact (hz ⟨θ, hθS⟩).symm
    rw [hnorm_ae _ _ hae]
    exact hnorm_nonneg θ hθS
  have hSc_variance : ∀ θ ∈ Sc.Θ_set,
      variance (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) P_Z ≤
        norm (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) ^ 2 := by
    intro θ hθ
    have hθS : θ ∈ S.Θ_set := by simpa [Sc] using hθ
    have hae : (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) =ᵐ[P_Z]
        fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g := by
      filter_upwards [hcenter_all_ae] with z hz
      exact (hz ⟨θ, hθS⟩).symm
    rw [variance_congr hae, hnorm_ae _ _ hae]
    exact hvariance θ hθS
  have hSc_diam : ∀ θ ∈ Sc.Θ_set,
      norm (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) ≤ Rmax := by
    intro θ hθ
    have hθS : θ ∈ S.Θ_set := by simpa [Sc] using hθ
    have hae : (fun z => Sc.ℓ z θ g - Sc.ℓ z Sc.θ₀ g) =ᵐ[P_Z]
        fun z => S.ℓ z θ g - S.ℓ z S.θ₀ g := by
      filter_upwards [hcenter_all_ae] with z hz
      exact (hz ⟨θ, hθS⟩).symm
    rw [hnorm_ae _ _ hae]
    simpa [Sc] using hF_diam θ hθS
  let Fsi : ℕ → Z → ℝ :=
    fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g
  let Fci : ℕ → Z → ℝ :=
    fun k z => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g
  have hidx_all_ae : ∀ r : ℝ, ∀ᵐ z ∂P_Z, ∀ p : starHullParam ℕ,
      starHullZeroOut Fsi norm r p z = starHullZeroOut Fci norm r p z := by
    intro r
    filter_upwards [hstar_all_ae r] with z hz p
    change starHullZeroOut Fs norm r (p.1, idx p.2) z =
      starHullZeroOut Fc norm r (p.1, idx p.2) z
    exact hz (p.1, idx p.2)
  have hSc_ψ_ub : ∀ m : ℕ,
      RademacherUpperBound Fci norm P_Z (id : Z → Z) m (ψ m) := by
    intro m r hr
    have hcongr :
        rademacherComplexity m (starHullZeroOut Fsi norm r) P_Z (id : Z → Z) =
          rademacherComplexity m (starHullZeroOut Fci norm r) P_Z (id : Z → Z) :=
      rademacherComplexity_congr_ae_all m
        (starHullZeroOut Fsi norm r) (starHullZeroOut Fci norm r)
        P_Z (id : Z → Z) (hidx_all_ae r)
    calc
      rademacherComplexity m (starHullZeroOut Fci norm r) P_Z (id : Z → Z)
          = rademacherComplexity m (starHullZeroOut Fsi norm r) P_Z (id : Z → Z) :=
              hcongr.symm
      _ ≤ ψ m r := by
              simpa [Fsi] using hψ_ub m r hr
  let idxc : ℕ → Sc.Θ_set := fun k => ⟨(idx k).val, by
    simp [Sc, (idx k).property]⟩
  have idxc_dense : DenseRange idxc := by
    simpa [idxc, Sc] using idx_dense
  have hSc_reg : LocalizedRademacherRegime Sc S_iid split g idxc norm ψ b := by
    refine ⟨hb, hSc_bound, hsub, ?_⟩
    intro n r hr
    have hcongr :
        rademacherComplexity (split.foldB n).card (starHullZeroOut Fsi norm r)
            P_Z (id : Z → Z) =
          rademacherComplexity (split.foldB n).card (starHullZeroOut Fci norm r)
            P_Z (id : Z → Z) :=
      rademacherComplexity_congr_ae_all (split.foldB n).card
        (starHullZeroOut Fsi norm r) (starHullZeroOut Fci norm r)
        P_Z (id : Z → Z) (hidx_all_ae r)
    calc
      rademacherComplexity (split.foldB n).card (starHullZeroOut Fci norm r)
          P_Z (id : Z → Z) =
        rademacherComplexity (split.foldB n).card (starHullZeroOut Fsi norm r)
          P_Z (id : Z → Z) := hcongr.symm
      _ ≤ ψ (split.foldB n).card r := hub_idx n r hr
  have hSc_cont :
      ∀ z, Continuous fun (θ : Sc.Θ_set) => Sc.ℓ z θ.val g := by
    intro z
    dsimp [Sc, clamp]
    exact continuous_const.add
      (continuous_const.max
        (continuous_const.min ((hg_cont z).sub continuous_const)))
  have hSc_ℓ_meas : ∀ θ ∈ Sc.Θ_set, Measurable (fun z => Sc.ℓ z θ g) := by
    intro θ _hθ
    exact Sc.ℓ_meas θ g
  have hSc_ℓ_int : ∀ θ ∈ Sc.Θ_set, Integrable (fun z => Sc.ℓ z θ g) P_Z := by
    intro θ hθ
    have hcenter_meas :
        Measurable fun z => clamp (S.ℓ z θ g - S.ℓ z S.θ₀ g) := by
      dsimp [clamp]
      exact measurable_const.max
        (measurable_const.min ((hℓ_meas θ hθ).sub (hℓ_meas S.θ₀ S.θ₀_mem)))
    have hcenter_int :
        Integrable (fun z => clamp (S.ℓ z θ g - S.ℓ z S.θ₀ g)) P_Z :=
      Integrable.of_bound hcenter_meas.aestronglyMeasurable b
        (by
          filter_upwards with z
          simpa [Real.norm_eq_abs] using hclamp_abs (S.ℓ z θ g - S.ℓ z S.θ₀ g))
    simpa [Sc] using (hℓ_int S.θ₀ S.θ₀_mem).fun_add hcenter_int
  have hSc_rad_bdd : ∀ m r, ∀ S_fin : Fin m → Z, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam ℕ =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut Fci norm r p (S_fin k)|) := by
    intro m r S_fin σ
    have hboundFci : ∀ i z, |Fci i z| ≤ b := by
      intro i z
      change |Sc.ℓ z (idx i).val g - Sc.ℓ z Sc.θ₀ g| ≤ b
      exact hSc_bound z (idx i).val (by simpa [Sc] using (idx i).property)
    exact starHullZeroOut_bddAbove_of_bound
      Fci norm hb m r S_fin (fun i k => hboundFci i (S_fin k)) σ
  have hSc_rad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              Fci norm r) ((id : Z → Z) ∘ ω))
        (Measure.pi (fun _ => P_Z)) := by
    intro m r
    have hprod : ∀ᵐ s : Fin m → Z ∂Measure.pi (fun _ : Fin m => P_Z),
        ∀ p : starHullParam ℕ, ∀ k : Fin m,
          starHullZeroOut Fsi norm r p ((id : Z → Z) (s k)) =
            starHullZeroOut Fci norm r p ((id : Z → Z) (s k)) := by
      filter_upwards [Filter.eventually_all.2 fun k : Fin m =>
        Measure.tendsto_eval_ae_ae.eventually (hidx_all_ae r)] with s hs p k
      exact hs k p
    have hemp :
        (fun ω : Fin m → Z =>
          empiricalRademacherComplexity m (starHullZeroOut Fsi norm r) ((id : Z → Z) ∘ ω))
          =ᵐ[Measure.pi (fun _ => P_Z)]
        fun ω : Fin m → Z =>
          empiricalRademacherComplexity m (starHullZeroOut Fci norm r) ((id : Z → Z) ∘ ω) := by
      filter_upwards [hprod] with s hs
      exact empiricalRademacherComplexity_congr_sample m
        (starHullZeroOut Fsi norm r) (starHullZeroOut Fci norm r) ((id : Z → Z) ∘ s)
        (fun p k => hs p k)
    have hbase := hrad_int m r
    exact (by
      simpa [Fsi, Fci] using hbase.congr hemp)
  have hmod_c := localEmpProcessModulus_of_localized_sharp
    (S := Sc) (S_iid := S_iid) (split := split)
    (g := g) (hg_cont := hSc_cont) (idx := idxc) (idx_dense := idxc_dense)
    (norm := norm) (ψ := ψ) (L := L)
    (b := b) (Rmax := Rmax)
    (hreg := hSc_reg) (hL_nonneg := hL_nonneg) (hF_lip := hSc_lip)
    (hnorm_nonneg := hSc_norm_nonneg) (hvariance := hSc_variance)
    (hℓ_meas := hSc_ℓ_meas) (hℓ_int := hSc_ℓ_int)
    (hF_diam := hSc_diam) (hcrit_pos := hcrit_pos)
    (hψ_ub := hSc_ψ_ub) hSc_rad_bdd
    (hrad_int := hSc_rad_int)
    (hδ := hδ) (hδ' := hδ') (hδ_dom := hδ_dom)
  intro n
  rcases hmod_c n with ⟨Ec, hEc_meas, hEc_prob, hEc_bound⟩
  let Gs : Set Ω :=
    {ω | ∀ i ∈ split.foldB n, ∀ θ ∈ S.Θ_set,
      S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g}
  have hsample_all_ae : ∀ i : ℕ, ∀ᵐ ω ∂μ,
      ∀ θ ∈ S.Θ_set,
        S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g := by
    intro i
    have hlaw_i : μ.map (S_iid.Z i) = P_Z := by
      rw [← (S_iid.identDist i).map_eq, S_iid.law]
    have hmap : ∀ᵐ z ∂μ.map (S_iid.Z i),
        ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
      simpa [hlaw_i] using hℓ_all_ae
    exact ae_of_ae_map (S_iid.meas i).aemeasurable hmap
  have hGs_ae : ∀ᵐ ω ∂μ, ω ∈ Gs := by
    have hfin : ∀ᵐ ω ∂μ, ∀ i ∈ split.foldB n,
        ∀ θ ∈ S.Θ_set,
          S.ℓ (S_iid.Z i ω) θ g = Sc.ℓ (S_iid.Z i ω) θ g := by
      simpa using (Finset.eventually_all (split.foldB n)).2
        (fun i _hi => hsample_all_ae i)
    simpa [Gs] using hfin
  have hGs_null : μ Gsᶜ = 0 := ae_iff.mp hGs_ae
  rcases exists_measurable_superset_of_null hGs_null with
    ⟨N, hGs_compl_subset_N, hN_meas, hN_null⟩
  refine ⟨Ec \ N, hEc_meas.diff hN_meas, ?_, ?_⟩
  · rw [measure_diff_null hN_null]
    exact hEc_prob
  · intro ω hω θ hθ
    have hωEc : ω ∈ Ec := hω.1
    have hωG : ω ∈ Gs := by
      by_contra hnot
      exact hω.2 (hGs_compl_subset_N hnot)
    have hLθ : S.L θ g = Sc.L θ g := hL_eq θ hθ
    have hL0 : S.L S.θ₀ g = Sc.L Sc.θ₀ g := by
      simpa [Sc] using hL_eq S.θ₀ S.θ₀_mem
    have hempθ :
        empRiskFoldB S S_iid split n ω θ g =
          empRiskFoldB Sc S_iid split n ω θ g := by
      dsimp [empRiskFoldB]
      congr 1
      exact Finset.sum_congr rfl fun i hi => hωG i hi θ hθ
    have hemp0 :
        empRiskFoldB S S_iid split n ω S.θ₀ g =
          empRiskFoldB Sc S_iid split n ω Sc.θ₀ g := by
      dsimp [empRiskFoldB]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by
        simpa [Sc] using hωG i hi S.θ₀ S.θ₀_mem
    calc
      (S.L θ g - S.L S.θ₀ g)
          - (empRiskFoldB S S_iid split n ω θ g
              - empRiskFoldB S S_iid split n ω S.θ₀ g)
          = (Sc.L θ g - Sc.L Sc.θ₀ g)
              - (empRiskFoldB Sc S_iid split n ω θ g
                  - empRiskFoldB Sc S_iid split n ω Sc.θ₀ g) := by
            rw [hLθ, hL0, hempθ, hemp0]
      _ ≤
          (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
           else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) *
            ‖θ - S.θ₀‖
            +
          (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
           else (10 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2 := by
            simpa [Sc] using hEc_bound ω hωEc θ (by simpa [Sc] using hθ)

/-- **Trivial finite class.**  When `Θ_set = {θ₀}` the
modulus inequality holds with `ρ n := 0` (the centred excess risk is
identically zero). Mirrors `localEmpProcessModulus_singleton` in the
global-Rademacher bridge. -/
theorem localEmpProcessModulus_of_localized_singleton
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    [IsProbabilityMeasure μ]
    (g : G)
    (hsing : S.Θ_set = {S.θ₀})
    {δ : ℝ} (_hδ : 0 < δ) :
    LocalEmpProcessModulus S S_iid split (fun _ => 0) δ g := by
  intro n
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · rw [measure_univ]
    exact tsub_le_self
  · intro ω _ θ hθ
    have hθ' : θ ∈ ({S.θ₀} : Set Θ) := by
      simpa [hsing] using hθ
    rcases hθ' with rfl
    simp

end OrthogonalLearning
end Estimation
end Causalean
