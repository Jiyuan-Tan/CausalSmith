/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Global Rademacher modulus: definitions and helper lemmas

This first part defines the global Rademacher and bounded-loss conditions and proves the
sample-law, dense-range, invariance, and population-risk lemmas needed by the bridge theorems in
Parts 2 and 3.
-/

module
public import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Local
public import Causalean.Stat.Concentration.Rademacher.Rademacher
public import Causalean.Stat.Concentration.TailBounds.McDiarmid
public import Causalean.Stat.Concentration.Rademacher.Symmetrization
public import Causalean.Stat.Concentration.Covering.Separable
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
public import Mathlib.Topology.Bases
public import FoML.Main

/-! # Global Rademacher Modulus

This first part provides the Rademacher-bound and bounded-loss predicates,
dense-range and map invariance lemmas, and population-risk bounds used by the subsequent
bridge theorems. The main everywhere-bounded bridge is in `Rademacher_Part2.lean`; the
almost-everywhere and singleton forms are in `Rademacher_Part3.lean`.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Causalean.Stat
  Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Given [an orthogonal statistical-learning system](hyp:S), [an independent and identically
distributed sample with the system's population law](hyp:S_iid), [a one-shot sample split](hyp:split),
[a nuisance function](hyp:g), [a sequence of targets in the target class](hyp:idx), and [a real
sequence](hyp:R), the [Rademacher-complexity bound](goal) holds exactly when, for every sample
size, [the proposed bound is nonnegative](step:1) and [the Rademacher complexity of the centred
loss class indexed by that target sequence on fold B, computed under the ambient sample measure
using the zeroth observation coordinate, is at most the proposed bound](step:2).

For a fixed nuisance `g`, the population Rademacher complexity of the
*countable* centred class
`{z ↦ ℓ z (denseSeq S.Θ_set k) g − ℓ z S.θ₀ g : k ∈ ℕ}`, evaluated on a
sample of size `(split.foldB n).card` drawn from the population law
`P_Z`, is at most `R n`.

Stated over the countable index `ℕ` (rather than the full `S.Θ_set`)
because FoML's `expectation_le_rademacher` and `mcdiarmid_inequality_pos'`
require a countable index — and `S.Θ_set` itself is not countable in
general.  The bridge theorem
`localEmpProcessModulus_of_bounded_rademacher` lifts the FoML conclusion
on `ℕ` to a uniform bound over `↥S.Θ_set` via
`separableSpaceSup_eq_real`, using continuity of the loss in `θ` and
separability of `S.Θ_set`.

The countable index `idx` is required because FoML's
`expectation_le_rademacher` consumes a countable index. Equivalence with the
un-lifted full-set Rademacher complexity holds only when `idx` has dense
range and, for each `z`, `S.ℓ z · g` is continuous in `θ` on `S.Θ_set`
with the subspace topology inherited from the normed structure on `Θ`.
Thus `idx_dense` is the user's explicit separability witness. See
`rademacherComplexity_eq_denseRange` for the dense-range helper used in this
file.

Independence of the fold-B block under `μ` ensures the value of
`rademacherComplexity` over `Z 0` equals the population Rademacher
complexity of the actual fold-B sample. -/
def RademacherBound
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (g : G) (idx : ℕ → S.Θ_set) (R : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ R n ∧
    rademacherComplexity (split.foldB n).card
      (fun (k : ℕ) z => S.ℓ z (idx k).val g - S.ℓ z S.θ₀ g)
      μ (S_iid.Z 0) ≤ R n

/-- Given [an orthogonal statistical-learning system](hyp:S), [a nuisance function](hyp:g), and
[a real bound](hyp:b), the [uniform bounded-loss condition](goal) holds exactly when, for every
observation and every target in the target class, the absolute loss at that nuisance function is at
most the bound. -/
def UniformlyBoundedLoss
    (S : LearningSystem Ω μ Z P_Z Θ G) (g : G) (b : ℝ) : Prop :=
  ∀ z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g| ≤ b

/-- Given [an orthogonal statistical-learning system](hyp:S), [a nuisance function](hyp:g), and
[a real bound](hyp:b), the [almost-everywhere uniform bounded-loss condition](goal) holds exactly
when, outside a set of population probability zero, every target in the target class has absolute
loss at that nuisance function at most the bound.

This is the satisfiable bounded-loss hypothesis for real-valued outcomes with
unbounded support: the bound only has to hold under the population law. -/
def UniformlyBoundedLossAE
    (S : LearningSystem Ω μ Z P_Z Θ G) (g : G) (b : ℝ) : Prop :=
  ∀ᵐ z ∂P_Z, ∀ θ ∈ S.Θ_set, |S.ℓ z θ g| ≤ b

/-- Given [an orthogonal statistical-learning system](hyp:S) and [a nuisance function](hyp:g),
the [target-continuity condition for the loss](goal) holds exactly when, for every observation, the
loss as a function of the target is continuous on the system's target class at that fixed nuisance
function.

Used by the bridge theorem for the countable-dense lifting via
`separableSpaceSup_eq_real`.  The subtype `↥S.Θ_set` carries the
subspace topology inherited from `Θ`'s normed structure. -/
def LossContinuousOnΘset
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (g : G) : Prop :=
  ∀ z, Continuous (fun (θ : S.Θ_set) => S.ℓ z θ.val g)

private lemma separableSup_via_denseRange
    {X : Type*} [TopologicalSpace X] [Nonempty X]
    {idx : ℕ → X} (h_dense : DenseRange idx)
    {f : X → ℝ} (hf : Continuous f) :
    ⨆ x : X, f x = ⨆ k : ℕ, f (idx k) := by
  have hclosure :
      closure (Set.range f) = closure (Set.range (f ∘ idx)) := by
    rw [Set.range_comp f idx]
    apply Set.Subset.antisymm
    · have hsub : Set.range f ⊆ closure (f '' Set.range idx) :=
        hf.range_subset_closure_image_dense h_dense
      exact closure_minimal hsub isClosed_closure
    · apply closure_mono
      exact Set.image_subset_range f (Set.range idx)
  by_cases hbdd : BddAbove (Set.range f)
  · calc
      ⨆ x : X, f x = sSup (closure (Set.range f)) := by
        exact sSup_eq_closure_sSup (Set.range_nonempty f) hbdd
      _ = sSup (closure (Set.range (f ∘ idx))) := by
        rw [hclosure]
      _ = ⨆ k : ℕ, f (idx k) := by
        have hbdd_idx : BddAbove (Set.range (f ∘ idx)) := by
          rw [Set.range_comp f idx]
          exact BddAbove.mono (Set.image_subset_range f (Set.range idx)) hbdd
        exact (sSup_eq_closure_sSup (Set.range_nonempty (f ∘ idx)) hbdd_idx).symm
  · have hbdd_idx : ¬ BddAbove (Set.range (f ∘ idx)) := by
      intro h
      have hclosure_bdd : BddAbove (closure (Set.range (f ∘ idx))) :=
        bddAbove_closure.mpr h
      rw [← hclosure] at hclosure_bdd
      exact hbdd (bddAbove_closure.mp hclosure_bdd)
    calc
      ⨆ x : X, f x = 0 := Real.iSup_of_not_bddAbove hbdd
      _ = ⨆ k : ℕ, f (idx k) := (Real.iSup_of_not_bddAbove hbdd_idx).symm

private lemma empiricalRademacherComplexity_eq_denseRange
    {X 𝒳 : Type*} [TopologicalSpace X] [Nonempty X]
    {idx : ℕ → X} (h_dense : DenseRange idx)
    (n : ℕ) (f : X → 𝒳 → ℝ)
    (hf : ∀ z : 𝒳, Continuous fun x : X => f x z)
    (sample : Fin n → 𝒳) :
    empiricalRademacherComplexity n f sample =
      empiricalRademacherComplexity n (f ∘ idx) sample := by
  dsimp [empiricalRademacherComplexity]
  congr
  ext σ
  exact separableSup_via_denseRange h_dense (by
    apply Continuous.abs
    apply Continuous.const_mul
    exact continuous_finset_sum Finset.univ fun k _ =>
      continuous_const.mul (hf (sample k)))

/-- Given [a function class indexed by a topological space and a countable indexing map](hyp:Ω,𝒳,X,idx,n,f,μ,sample),
if [the indexing map has dense range](hyp:h_dense) and [each pointwise function varies continuously
with the index](hyp:hf), then [the class and its countable dense subfamily have the same Rademacher
complexity](goal). -/
lemma rademacherComplexity_eq_denseRange
    {Ω 𝒳 X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [Nonempty X]
    {idx : ℕ → X} (h_dense : DenseRange idx)
    (n : ℕ) (f : X → 𝒳 → ℝ)
    (hf : ∀ z : 𝒳, Continuous fun x : X => f x z)
    (μ : MeasureTheory.Measure Ω) (sample : Ω → 𝒳) :
    rademacherComplexity n f μ sample =
      rademacherComplexity n (f ∘ idx) μ sample := by
  dsimp [rademacherComplexity]
  congr
  ext ω
  exact empiricalRademacherComplexity_eq_denseRange h_dense n f hf (sample ∘ ω)

/-- Given [a countable measurable function class, sample size, source measure, and sample map](hyp:Ω,𝒳,ι,n,f,μ,sample),
if [every class member is measurable](hyp:hf) and [the sample map is measurable](hyp:hsample), then
[the Rademacher complexity under the pushed-forward law with the identity sample equals that under
the source law with the original sample](goal). -/
lemma rademacherComplexity_map_id
    {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [Countable ι]
    (n : ℕ) (f : ι → 𝒳 → ℝ)
    (hf : ∀ i, Measurable (f i))
    (μ : MeasureTheory.Measure Ω) [SigmaFinite μ] (sample : Ω → 𝒳)
    [SigmaFinite (μ.map sample)]
    (hsample : Measurable sample) :
    rademacherComplexity n f (μ.map sample) id =
      rademacherComplexity n f μ sample := by
  dsimp [rademacherComplexity]
  let Φ : (Fin n → Ω) → (Fin n → 𝒳) := fun ω i => sample (ω i)
  have hmap :
      Measure.map Φ (Measure.pi fun _ : Fin n => μ) =
        Measure.pi fun _ : Fin n => μ.map sample := by
    dsimp [Φ]
    rw [Measure.pi_map_pi]
    intro _
    exact hsample.aemeasurable
  rw [← hmap]
  rw [integral_map]
  · rfl
  · exact (measurable_pi_lambda Φ
        (fun i => hsample.comp (measurable_pi_apply i))).aemeasurable
  · apply Measurable.aestronglyMeasurable
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro σ _
    apply Measurable.iSup
    intro i
    apply Measurable.abs
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro k _
    apply measurable_const.mul
    exact (hf i).comp (measurable_pi_apply k)

/-- Given [a sample size, two countable real-valued function families, a measure, and a sample map](hyp:Ω,𝒳,n,f,f',μ,sample),
if [corresponding sampled functions agree almost everywhere](hyp:h), then [the two Rademacher
complexities are equal](goal). -/
lemma rademacherComplexity_congr_ae
    {Ω 𝒳 : Type*} [MeasurableSpace Ω]
    (n : ℕ) (f f' : ℕ → 𝒳 → ℝ) (μ : MeasureTheory.Measure Ω)
    [SigmaFinite μ]
    (sample : Ω → 𝒳)
    (h : ∀ i, (fun ω => f i (sample ω)) =ᵐ[μ]
      fun ω => f' i (sample ω)) :
    rademacherComplexity n f μ sample =
      rademacherComplexity n f' μ sample := by
  exact Causalean.Stat.Concentration.rademacherComplexity_congr_ae n f f' μ sample h

/-- Given [an orthogonal learning system and a nonnegative bound](hyp:Ω,μ,Z,P_Z,Θ,G,S,b,_hb),
if [a nuisance value gives uniformly bounded losses](hyp:g,hg_bdd), then for [any admissible target
parameter](hyp:θ,hθ), [the absolute population risk is at most the bound](goal). -/
lemma populationRisk_abs_le_of_uniform
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (_hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLoss S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |S.L θ g| ≤ b := by
  calc
    |S.L θ g| = |∫ z, S.ℓ z θ g ∂P_Z| := rfl
    _ ≤ ∫ z, |S.ℓ z θ g| ∂P_Z := abs_integral_le_integral_abs
    _ ≤ ∫ _z, b ∂P_Z := by
      apply integral_mono
      · exact Integrable.of_bound (S.ℓ_meas θ g).abs.aestronglyMeasurable b
          (by
            filter_upwards with z
            simpa [Real.norm_eq_abs] using hg_bdd z θ hθ)
      · exact integrable_const b
      · intro z
        exact hg_bdd z θ hθ
    _ = b := by simp

/-- Given [an orthogonal learning system and a nonnegative bound](hyp:Ω,μ,Z,P_Z,Θ,G,S,b,hb),
if [a nuisance value gives uniformly bounded losses](hyp:g,hg_bdd), then for [any admissible target
parameter](hyp:θ,hθ), [its population risk exceeds the baseline risk by at most twice the bound](goal). -/
lemma populationRisk_sub_le_two_mul_bound
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLoss S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    S.L θ g - S.L S.θ₀ g ≤ 2 * b := by
  have hθ_abs := populationRisk_abs_le_of_uniform S hb hg_bdd hθ
  have hθ₀_abs := populationRisk_abs_le_of_uniform S hb hg_bdd S.θ₀_mem
  have hθ_le : S.L θ g ≤ b := le_abs_self (S.L θ g) |>.trans hθ_abs
  have hθ₀_ge : -b ≤ S.L S.θ₀ g := (abs_le.mp hθ₀_abs).1
  linarith

private lemma populationRisk_abs_le_of_uniform_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (_hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLossAE S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    |S.L θ g| ≤ b := by
  calc
    |S.L θ g| = |∫ z, S.ℓ z θ g ∂P_Z| := rfl
    _ ≤ ∫ z, |S.ℓ z θ g| ∂P_Z := abs_integral_le_integral_abs
    _ ≤ ∫ _z, b ∂P_Z := by
      apply integral_mono_ae
      · exact Integrable.of_bound (S.ℓ_meas θ g).abs.aestronglyMeasurable b
          (by
            filter_upwards [hg_bdd] with z hz
            simpa [Real.norm_eq_abs] using hz θ hθ)
      · exact integrable_const b
      · filter_upwards [hg_bdd] with z hz
        exact hz θ hθ
    _ = b := by simp

/-- Given [an orthogonal learning system and a nonnegative bound](hyp:Ω,μ,Z,P_Z,Θ,G,S,b,hb),
if [a nuisance value gives almost-everywhere uniformly bounded losses](hyp:g,hg_bdd), then for [any
admissible target parameter](hyp:θ,hθ), [its population risk exceeds the baseline risk by at most
twice the bound](goal). -/
lemma populationRisk_sub_le_two_mul_bound_ae
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure P_Z]
    {b : ℝ} (hb : 0 ≤ b) {g : G}
    (hg_bdd : UniformlyBoundedLossAE S g b)
    {θ : Θ} (hθ : θ ∈ S.Θ_set) :
    S.L θ g - S.L S.θ₀ g ≤ 2 * b := by
  have hθ_abs := populationRisk_abs_le_of_uniform_ae S hb hg_bdd hθ
  have hθ₀_abs := populationRisk_abs_le_of_uniform_ae S hb hg_bdd S.θ₀_mem
  have hθ_le : S.L θ g ≤ b := le_abs_self (S.L θ g) |>.trans hθ_abs
  have hθ₀_ge : -b ≤ S.L S.θ₀ g := (abs_le.mp hθ₀_abs).1
  linarith

end OrthogonalLearning
end Estimation
end Causalean
