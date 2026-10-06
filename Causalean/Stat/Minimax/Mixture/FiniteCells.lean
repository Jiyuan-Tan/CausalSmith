module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Finite-cell likelihood assembly

This module turns finite observed-cell masses into likelihood representations
of measures.  It covers a finite latent choice assembled by `Measure.bind` and
an exact event-mass interface suitable for other finite-cell experiments.
-/
@[expose] public section
namespace Causalean.Stat.Minimax.Mixture.FiniteCells
open MeasureTheory
open scoped ENNReal BigOperators
/-- Given [a covariate sample space](hyp:X), [a finite observed-cell space](hyp:C),
[a covariate law](hyp:ν), [nonnegative masses for every cell](hyp:m), and
[an observed event](hyp:A), the [finite-cell event mass](goal) is given by
[integrating the masses of event cells](step:1). -/
noncomputable def cellSetMass {X C : Type*} [MeasurableSpace X] [Fintype C]
    (ν : Measure X) (m : X → C → ℝ≥0∞) (A : Set (X × C)) : ℝ≥0∞ := by
  classical
  exact ∫⁻ x, ∑ c : C, if (x, c) ∈ A then m x c else 0 ∂ν
/-- Given [a covariate sample space](hyp:X), [a finite observed-cell space](hyp:C),
[a probability covariate law](hyp:ν), [an observed law](hyp:Q), [cell masses](hyp:q),
[an exact finite-cell event-mass representation](hyp:hQ), and
[cell masses that sum to one at every covariate value](hyp:hsum),
[the observed law is a probability measure](goal). -/
theorem isProbability_of_cellSetMass {X C : Type*} [MeasurableSpace X] [MeasurableSpace C] [Fintype C] (ν : Measure X)
    [IsProbabilityMeasure ν] (Q : Measure (X × C)) (q : X → C → ℝ≥0∞) (hQ : ∀ A, MeasurableSet A → Q A = cellSetMass ν q
    A) (hsum : ∀ x, ∑ c : C, q x c = 1) : IsProbabilityMeasure Q := by
  apply isProbabilityMeasure_iff.mpr
  rw [hQ Set.univ MeasurableSet.univ]
  simp [cellSetMass, hsum]
/-- Given [a covariate sample space](hyp:X), [a finite observed-cell space](hyp:C),
[a finite latent-state space](hyp:Z), [a covariate law](hyp:ν),
[latent-state weights](hyp:w), [an observed-cell reporting map](hyp:obs),
[measurable weights](hyp:hw), and [a measurable reporting map](hyp:hobs),
[the bound latent law has the stated finite-cell event masses](goal). -/
theorem bind_latent_map_cellSetMass {X C Z : Type*} [MeasurableSpace X] [MeasurableSpace C] [Fintype C] [DecidableEq C]
    [Fintype Z] (ν : Measure X) (w : X → Z → ℝ≥0∞) (obs : X → Z → C) (hw : ∀ z, Measurable fun x => w x z) (hobs : ∀ z,
    Measurable fun x => obs x z) : ∀ A, MeasurableSet A → (ν.bind (fun x => ∑ z : Z, w x z • Measure.dirac (x, obs x
    z))) A = cellSetMass ν (fun x c => ∑ z : Z, if obs x z = c then w x z else 0) A := by
  intro A hA
  have hk : Measurable (fun x => ∑ z : Z, w x z • Measure.dirac (x, obs x z)) := by
    classical
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply]
    apply Finset.measurable_fun_sum
    intro z hz
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    exact (hw z).mul (measurable_one.indicator (hs.preimage (measurable_id.prodMk (hobs z))))
  rw [Measure.bind_apply hA hk.aemeasurable]
  unfold cellSetMass
  apply lintegral_congr
  intro x
  classical
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hA]
  calc
    (∑ z : Z, w x z * A.indicator 1 (x, obs x z)) =
        ∑ z : Z, if (x, obs x z) ∈ A then w x z else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          simp [Set.indicator, mul_ite]
    _ = ∑ z : Z, ∑ c : C,
        if (x, c) ∈ A then (if obs x z = c then w x z else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          calc
            (if (x, obs x z) ∈ A then w x z else 0) =
                ∑ c : C, if obs x z = c then
                  (if (x, c) ∈ A then w x z else 0) else 0 := by simp
            _ = ∑ c : C, if (x, c) ∈ A then
                  (if obs x z = c then w x z else 0) else 0 := by
                    apply Finset.sum_congr rfl
                    intro c hc
                    split_ifs <;> simp_all
    _ = ∑ c : C, ∑ z : Z,
        if (x, c) ∈ A then (if obs x z = c then w x z else 0) else 0 :=
          Finset.sum_comm
    _ = ∑ c : C, if (x, c) ∈ A then
        (∑ z : Z, if obs x z = c then w x z else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          split_ifs <;> simp
/-- Given [a covariate sample space](hyp:X), [a finite observed-cell space](hyp:C),
[a covariate law](hyp:ν), [reference and alternative observed laws](hyp:μ,Q),
[reference and alternative cell masses](hyp:p,q), [a likelihood](hyp:L),
[measurable reference and alternative masses](hyp:hp,hq), [a measurable
nonnegative likelihood](hyp:hL,hL0), [finite-cell event-mass representations](hyp:hμ,hQ),
and [the cellwise likelihood ratio identity](hyp:hratio), [the alternative law
is the reference law tilted by that likelihood](goal). -/
theorem eq_withDensity_of_cellSetMass {X C : Type*} [MeasurableSpace X] [MeasurableSpace C] [Fintype C] (ν : Measure X)
    (μ Q : Measure (X × C)) (p q : X → C → ℝ≥0∞) (L : X × C → ℝ) (hp : ∀ c, Measurable fun x => p x c) (hq : ∀ c,
    Measurable fun x => q x c) (hL : Measurable L) (hL0 : ∀ z, 0 ≤ L z) (hμ : ∀ A, MeasurableSet A → μ A = cellSetMass ν
    p A) (hQ : ∀ A, MeasurableSet A → Q A = cellSetMass ν q A) (hratio : ∀ x c, q x c = p x c * ENNReal.ofReal (L (x,
    c))) : Q = μ.withDensity (fun z => ENNReal.ofReal (L z)) := by
  classical
  let k : X → Measure (X × C) :=
    fun x => ∑ c : C, p x c • Measure.dirac (x, c)
  have hk : Measurable k := by
    unfold k
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply]
    apply Finset.measurable_fun_sum
    intro c hc
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    exact (hp c).mul (measurable_one.indicator
      (hs.preimage (measurable_id.prodMk measurable_const)))
  have hμbind : μ = ν.bind k := by
    ext A hA
    rw [hμ A hA]
    have hb := bind_latent_map_cellSetMass ν p (fun _ c => c) hp
      (fun _ => measurable_const) A hA
    rw [hb]
    unfold cellSetMass
    apply lintegral_congr
    intro x
    apply Finset.sum_congr rfl
    intro c hc
    simp
  let f : X × C → ℝ≥0∞ := fun z => ENNReal.ofReal (L z)
  have hf : Measurable f := hL.ennreal_ofReal
  ext A hA
  have hg : Measurable (A.indicator f) := hf.indicator hA
  calc
    Q A = ∫⁻ x, ∑ c : C, if (x, c) ∈ A then q x c else 0 ∂ν := hQ A hA
    _ = ∫⁻ x, ∑ c : C, if (x, c) ∈ A then p x c * f (x, c) else 0 ∂ν := by
      apply lintegral_congr
      intro x
      apply Finset.sum_congr rfl
      intro c hc
      simp only [hratio]
      rfl
    _ = (μ.withDensity f) A := by
      rw [withDensity_apply _ hA, ← lintegral_indicator hA, hμbind]
      rw [Measure.lintegral_bind hk.aemeasurable hg.aemeasurable]
      apply lintegral_congr
      intro x
      change (∑ c : C, if (x, c) ∈ A then p x c * f (x, c) else 0) =
        ∫⁻ z, A.indicator f z ∂k x
      unfold k
      rw [lintegral_finsetSum_measure]
      simp_rw [lintegral_smul_measure, lintegral_dirac' _ hg]
      apply Finset.sum_congr rfl
      intro c hc
      simp [Set.indicator, smul_eq_mul]
/-- Given [a covariate sample space](hyp:X), [a finite observed-cell space](hyp:C),
[a covariate law](hyp:ν), [reference and alternative cell masses](hyp:p,q),
[a likelihood](hyp:L), [measurable masses](hyp:hp,hq), [a measurable nonnegative
likelihood](hyp:hL,hL0), and [the cellwise likelihood ratio identity](hyp:hratio),
[the alternative finite-cell bound law is the likelihood tilt of the reference
bound law](goal). -/
theorem bind_cells_eq_withDensity {X C : Type*} [MeasurableSpace X] [MeasurableSpace C] [Fintype C] (ν : Measure X) (p q
    : X → C → ℝ≥0∞) (L : X × C → ℝ) (hp : ∀ c, Measurable fun x => p x c) (hq : ∀ c, Measurable fun x => q x c) (hL :
    Measurable L) (hL0 : ∀ z, 0 ≤ L z) (hratio : ∀ x c, q x c = p x c * ENNReal.ofReal (L (x, c))) : ν.bind (fun x => ∑
    c : C, q x c • Measure.dirac (x, c)) = (ν.bind (fun x => ∑ c : C, p x c • Measure.dirac (x, c))).withDensity (fun z
    => ENNReal.ofReal (L z)) := by
  classical
  apply eq_withDensity_of_cellSetMass ν _ _ p q L hp hq hL hL0
  · intro A hA
    rw [bind_latent_map_cellSetMass ν p (fun _ c => c) hp
      (fun _ => measurable_const) A hA]
    unfold cellSetMass
    apply lintegral_congr
    intro x
    apply Finset.sum_congr rfl
    intro c hc
    simp
  · intro A hA
    rw [bind_latent_map_cellSetMass ν q (fun _ c => c) hq
      (fun _ => measurable_const) A hA]
    unfold cellSetMass
    apply lintegral_congr
    intro x
    apply Finset.sum_congr rfl
    intro c hc
    simp
  · exact hratio
end Causalean.Stat.Minimax.Mixture.FiniteCells
