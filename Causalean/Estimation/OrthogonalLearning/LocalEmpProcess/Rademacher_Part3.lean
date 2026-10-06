/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Global Rademacher modulus: almost-everywhere and singleton bridges

This third part proves the almost-everywhere bounded-loss bridge and the degenerate
singleton-class modulus. The everywhere-bounded bridge is proved in Part 2.
-/

module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Rademacher_Part2

/-! # Global Rademacher Modulus

This third part proves the almost-everywhere bounded-loss bridge
`localEmpProcessModulus_of_bounded_rademacher_ae` and the degenerate singleton-class result
`localEmpProcessModulus_singleton`. It builds on the definitions and everywhere-bounded bridge
from Parts 1 and 2.
-/

public section

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Causalean.Stat
  Causalean.Stat.Concentration

/-! ## Imported helpers

Part 1 supplies the public fold-B joint-law alias and the predicates used below. -/
variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]
/-- **Almost-everywhere bounded-loss bridge.** Assume [`b` is nonnegative](hyp:hb), that
[the loss magnitude is bounded by `b` at `P_Z`-almost-every observation, over the
parameter set](hyp:hg_bdd_ae), and that [the loss is continuous in the parameter on the
parameter set](hyp:hg_cont). Given [a sequence `R n` that is nonnegative and upper-bounds
the population Rademacher complexity of the centred loss class on the fold-B sample at
every sample size](hyp:hR), and that [the target parameter minimizes, over the parameter
set, the population risk of the loss — evaluated at the model's baseline nuisance and
clamped to `[-b, b]`](hyp:hclamp_minimizes), then for any confidence level
[`0 < δ ≤ 1`](hyp:hδ,hδ') [the local empirical-process modulus condition holds, with rate
`ρ n := √(2 · b)` when the fold-B sample is empty and
`ρ n := √(2 · R n + 2 · b · √(2 · log(1/δ) / |foldB n|))` otherwise](goal).

The same empirical-process modulus bridge as
`localEmpProcessModulus_of_bounded_rademacher`, but with the loss envelope
assumed only under the population law and with a local minimizer witness for
the auxiliary clamped loss used in the proof. The empty-fold branch uses only
population-risk bounds and is therefore identical after replacing the helper
lemma by its a.e. analogue. In the nonempty branch, the proof applies the
McDiarmid tail bound to the class clamped to `[-b, b]` and transfers the
resulting product-space event back to the original class on the conull sample
event where the clamp is inactive. -/
theorem localEmpProcessModulus_of_bounded_rademacher_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb : 0 ≤ b) (g : G)
    (hg_bdd_ae : UniformlyBoundedLossAE S g b)
    (hg_cont : LossContinuousOnΘset S g)
    (idx : ℕ → S.Θ_set)
    (idx_dense : DenseRange idx)
    (R : ℕ → ℝ)
    (hR : RademacherBound S S_iid split g idx R)
    (hclamp_minimizes : ∀ θ ∈ S.Θ_set,
      ∫ z, max (-b) (min b (S.ℓ z S.θ₀ S.g₀)) ∂P_Z
        ≤ ∫ z, max (-b) (min b (S.ℓ z θ S.g₀)) ∂P_Z)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    LocalEmpProcessModulus S S_iid split
      (fun n => Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) δ g := by
  intro n
  classical
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  by_cases hm0 : (split.foldB n).card = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ θ hθ
      have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
      have hpop : S.L θ g - S.L S.θ₀ g ≤ 2 * b :=
        populationRisk_sub_le_two_mul_bound_ae S hb hg_bdd_ae hθ
      have hρsq :
          (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
            = 2 * b := by
        rw [Real.sq_sqrt]
        · simp [hm0]
        · have : 0 ≤ 2 * b := by nlinarith
          simpa [hm0] using this
      have hρ_nonneg :
          0 ≤ Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
        Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
      calc
        (S.L θ g - S.L S.θ₀ g)
            - (empRiskFoldB S S_iid split n ω θ g
                - empRiskFoldB S S_iid split n ω S.θ₀ g)
            = S.L θ g - S.L S.θ₀ g := by
                simp [empRiskFoldB, hfold_empty]
        _ ≤ 2 * b := hpop
        _ = (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq.symm
        _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]
  · let clamp : ℝ → ℝ := fun t => max (-b) (min b t)
    let Sc : LearningSystem Ω μ Z P_Z Θ G :=
      { S with
        ℓ := fun z θ g' => clamp (S.ℓ z θ g')
        ℓ_meas := fun θ g' => by
          dsimp [clamp]
          exact measurable_const.max (measurable_const.min (S.ℓ_meas θ g'))
        θ₀_minimizes := by
          intro θ hθ
          simpa [clamp] using hclamp_minimizes θ hθ }
    have hclamp_abs : ∀ t : ℝ, |clamp t| ≤ b := by
      intro t
      rw [abs_le]
      constructor
      · dsimp [clamp]
        exact le_max_left (-b) (min b t)
      · dsimp [clamp]
        exact max_le (by linarith) (min_le_left b t)
    have hclamp_eq_of_abs_le : ∀ {t : ℝ}, |t| ≤ b → clamp t = t := by
      intro t ht
      have ht_low : -b ≤ t := (abs_le.mp ht).1
      have ht_high : t ≤ b := (abs_le.mp ht).2
      dsimp [clamp]
      rw [min_eq_right ht_high, max_eq_right ht_low]
    have hSc_bdd : UniformlyBoundedLoss Sc g b := by
      intro z θ hθ
      simpa [Sc] using hclamp_abs (S.ℓ z θ g)
    have hSc_cont : LossContinuousOnΘset Sc g := by
      intro z
      dsimp [Sc, clamp]
      exact continuous_const.max (continuous_const.min (hg_cont z))
    have hℓ_ae : ∀ θ, θ ∈ S.Θ_set →
        (fun z => S.ℓ z θ g) =ᵐ[P_Z] fun z => Sc.ℓ z θ g := by
      intro θ hθ
      filter_upwards [hg_bdd_ae] with z hz
      simpa [Sc] using (hclamp_eq_of_abs_le (hz θ hθ)).symm
    have hℓ_all_ae : ∀ᵐ z ∂P_Z,
        ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
      filter_upwards [hg_bdd_ae] with z hz θ hθ
      simpa [Sc] using (hclamp_eq_of_abs_le (hz θ hθ)).symm
    have hL_eq : ∀ θ, θ ∈ S.Θ_set → S.L θ g = Sc.L θ g := by
      intro θ hθ
      dsimp [LearningSystem.L]
      exact integral_congr_ae (hℓ_ae θ hθ)
    let idxc : ℕ → Sc.Θ_set := fun k => ⟨(idx k).val, by
      simp [Sc, (idx k).property]⟩
    have idxc_dense : DenseRange idxc := by
      simpa [idxc, Sc] using idx_dense
    have hRc : RademacherBound Sc S_iid split g idxc R := by
      intro m
      refine ⟨(hR m).1, ?_⟩
      have hcenter_ae : ∀ k : ℕ,
          (fun ω => S.ℓ (S_iid.Z 0 ω) (idx k).val g
              - S.ℓ (S_iid.Z 0 ω) S.θ₀ g) =ᵐ[μ]
            fun ω => Sc.ℓ (S_iid.Z 0 ω) (idx k).val g
              - Sc.ℓ (S_iid.Z 0 ω) Sc.θ₀ g := by
        intro k
        have hidx_base : (fun z => S.ℓ z (idx k).val g) =ᵐ[P_Z]
            fun z => Sc.ℓ z (idx k).val g :=
          hℓ_ae (idx k).val (idx k).property
        have hzero_base : (fun z => S.ℓ z S.θ₀ g) =ᵐ[P_Z]
            fun z => Sc.ℓ z S.θ₀ g :=
          hℓ_ae S.θ₀ S.θ₀_mem
        have hidx' : (fun ω => S.ℓ (S_iid.Z 0 ω) (idx k).val g) =ᵐ[μ]
            fun ω => Sc.ℓ (S_iid.Z 0 ω) (idx k).val g := by
          have hmap : ∀ᵐ z ∂μ.map (S_iid.Z 0),
              S.ℓ z (idx k).val g = Sc.ℓ z (idx k).val g := by
            rw [S_iid.law]
            exact hidx_base
          exact ae_of_ae_map (S_iid.meas 0).aemeasurable hmap
        have hzero' : (fun ω => S.ℓ (S_iid.Z 0 ω) S.θ₀ g) =ᵐ[μ]
            fun ω => Sc.ℓ (S_iid.Z 0 ω) Sc.θ₀ g := by
          have hmap : ∀ᵐ z ∂μ.map (S_iid.Z 0),
              S.ℓ z S.θ₀ g = Sc.ℓ z S.θ₀ g := by
            rw [S_iid.law]
            exact hzero_base
          exact ae_of_ae_map (S_iid.meas 0).aemeasurable hmap
        exact hidx'.sub hzero'
      have hcongr :
          rademacherComplexity (split.foldB m).card
              (fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
              μ (S_iid.Z 0) =
            rademacherComplexity (split.foldB m).card
          (fun k z => Sc.ℓ z (idxc k).val g - Sc.ℓ z Sc.θ₀ g)
          μ (S_iid.Z 0) :=
        by
          simpa [idxc] using
            rademacherComplexity_congr_ae (split.foldB m).card
              (fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
              (fun k z => Sc.ℓ z (idx k).val g - Sc.ℓ z Sc.θ₀ g)
              μ (S_iid.Z 0) hcenter_ae
      calc
        rademacherComplexity (split.foldB m).card
            (fun k z => Sc.ℓ z (idxc k).val g - Sc.ℓ z Sc.θ₀ g)
            μ (S_iid.Z 0)
            = rademacherComplexity (split.foldB m).card
                (fun k z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
                μ (S_iid.Z 0) := hcongr.symm
        _ ≤ R m := (hR m).2
    have hmod_c := localEmpProcessModulus_of_bounded_rademacher
      Sc S_iid split hb g hSc_bdd hSc_cont idxc idxc_dense R hRc hδ hδ'
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
      have hbase : ∀ᵐ z ∂P_Z,
          ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := hℓ_all_ae
      have hmap : ∀ᵐ z ∂μ.map (S_iid.Z i),
          ∀ θ ∈ S.Θ_set, S.ℓ z θ g = Sc.ℓ z θ g := by
        simpa [hlaw_i] using hbase
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
        _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            simpa [Sc] using hEc_bound ω hωEc θ (by simpa [Sc] using hθ)

/-- **Trivial finite class.**  When `Θ_set = {θ₀}` (the
class collapses to the truth), the modulus inequality holds with
`ρ n := 0`. -/
theorem localEmpProcessModulus_singleton
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
