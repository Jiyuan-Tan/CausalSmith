module

public import Causalean.Mathlib.Probability.Kernel.FiniteSequence
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite-horizon sequential likelihood scores

This module packages a dominated adaptive finite-horizon experiment with supplied
stage scores. It derives score centering, orthogonality, Fisher-information
additivity, and a uniform per-stage information bound for arbitrary measurable
stage spaces, using the finite sequential-kernel law API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.Minimax.SequentialScore

open Causalean.Mathlib.Probability.Kernel.FiniteSequence

variable {n : ℕ} {Z : Fin n → Type*} [∀ i, MeasurableSpace (Z i)]

/-- A [parameter-indexed family of sequential kernels](hyp:Q) and [a parameter value](hyp:u)
determine [the finite transcript law](goal), [given by the sequential law with the unit input at
every stage](step:1). -/
noncomputable def law (Q : ℝ → KernelFamily Unit Z) (u : ℝ) :
    Measure (Transcript Z) := transcriptLaw (Q u) (fun _ => ())

/-- [Stage-score functions indexed by the stage and parameter](hyp:D), [a stage](hyp:i),
[a parameter value](hyp:u), and [a complete transcript](hyp:z) determine [that stage's score
increment](goal), [given by evaluating the score on the transcript through that stage](step:1). -/
def increment (D : (i : Fin n) → ℝ →
    History Z (i.val + 1) (Nat.succ_le_of_lt i.isLt) → ℝ)
    (i : Fin n) (u : ℝ) (z : Transcript Z) : ℝ :=
  D i u (take (Nat.succ_le_of_lt i.isLt) z)

/-- A [finite horizon](hyp:n) and [measurable stage-output spaces](hyp:Z) determine the
assumption bundle for a finite-horizon sequential score model: an open parameter domain; a
parameter-indexed family of stage kernels that are Markov on the domain; a finite reference
measure on transcripts together with a jointly measurable, strictly positive transcript
density of the transcript law and its pointwise parameter derivative; and supplied
measurable stage scores that are conditionally integrable, have square-integrable increments
under the transcript law, give the parameter derivative of every stage-kernel event
probability, and, as an assumption rather than a derived fact, satisfy the score bridge:
the density derivative equals the density times the sum of the stage score increments,
almost everywhere under the reference measure. -/
structure Model (n : ℕ) (Z : Fin n → Type*) [∀ i, MeasurableSpace (Z i)] where
  domain : Set ℝ
  domain_open : IsOpen domain
  Q : ℝ → KernelFamily Unit Z
  markov : ∀ u ∈ domain, ∀ i, IsMarkovKernel (Q u i)
  reference : Measure (Transcript Z)
  reference_finite : IsFiniteMeasure reference
  q : ℝ → Transcript Z → ℝ
  qdot : ℝ → Transcript Z → ℝ
  q_joint_measurable : Measurable (fun p : ℝ × Transcript Z => q p.1 p.2)
  qdot_joint_measurable : Measurable (fun p : ℝ × Transcript Z => qdot p.1 p.2)
  q_positive : ∀ u ∈ domain, ∀ z, 0 < q u z
  law_eq_density : ∀ u ∈ domain,
    law Q u = reference.withDensity (fun z => ENNReal.ofReal (q u z))
  q_hasDerivAt : ∀ u ∈ domain, ∀ z,
    HasDerivAt (fun t => q t z) (qdot u z) u
  D : (i : Fin n) → ℝ →
    History Z (i.val + 1) (Nat.succ_le_of_lt i.isLt) → ℝ
  D_measurable : ∀ u ∈ domain, ∀ i, Measurable (D i u)
  D_stage_integrable : ∀ u ∈ domain, ∀ i h,
    Integrable (fun z => D i u (snoc (Nat.succ_le_of_lt i.isLt) h z))
      (Q u i ((), h))
  D_sq_integrable : ∀ u ∈ domain, ∀ i,
    Integrable (fun z => (increment D i u z) ^ 2) (law Q u)
  kernel_event_hasDerivAt : ∀ u ∈ domain, ∀ i h
    (A : Set (Z i)), MeasurableSet A →
    HasDerivAt (fun t => (Q t i ((), h) A).toReal)
      (∫ z in A, D i u (snoc (Nat.succ_le_of_lt i.isLt) h z)
        ∂Q u i ((), h)) u
  score_bridge : ∀ u ∈ domain, ∀ᵐ z ∂reference,
    qdot u z = q u z * ∑ i : Fin n, increment D i u z

/-- A [sequential score model](hyp:M) at [a parameter in its domain](hyp:hu) has [a transcript
law that is a probability measure](goal). -/
theorem Model.law_probability (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) : IsProbabilityMeasure (law M.Q u) := by
  exact isProbabilityMeasure_transcriptLaw (M.Q u) (M.markov u hu) (fun _ => ())

/-- A [sequential score model](hyp:M) at [a parameter in its domain](hyp:hu) has [a positive
transcript density that integrates to one against its common reference measure](goal). -/
theorem Model.q_normalized (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) :
    (∫ z, M.q u z ∂M.reference) = 1 := by
  have hmeas : Measurable (fun z => ENNReal.ofReal (M.q u z)) :=
    ((M.q_joint_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)
  have hmass : (∫ z, (1 : ℝ) ∂law M.Q u) = 1 := by
    letI := M.law_probability hu
    simp
  calc
    (∫ z, M.q u z ∂M.reference) =
        ∫ z, (1 : ℝ) ∂M.reference.withDensity
          (fun z => ENNReal.ofReal (M.q u z)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hmeas (by simp)]
      congr 1
      funext z
      simp [ENNReal.toReal_ofReal (le_of_lt (M.q_positive u hu z))]
    _ = ∫ z, (1 : ℝ) ∂law M.Q u := by rw [M.law_eq_density u hu]
    _ = 1 := hmass

/-- A [sequential score model](hyp:M), [a parameter in its domain](hyp:hu), [a stage](hyp:i),
and [a preceding transcript history](hyp:h) have [a next-output score with conditional mean
zero](goal). -/
theorem Model.stage_score_centered (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) (i : Fin n)
    (h : History Z i.val (Nat.le_of_lt i.isLt)) :
    (∫ z, M.D i u (snoc (Nat.succ_le_of_lt i.isLt) h z)
      ∂M.Q u i ((), h)) = 0 := by
  have hderiv := M.kernel_event_hasDerivAt u hu i h Set.univ MeasurableSet.univ
  have hevent : (fun t => (M.Q t i ((), h) Set.univ).toReal) =ᶠ[nhds u]
      fun _ => (1 : ℝ) := by
    filter_upwards [M.domain_open.mem_nhds hu] with t ht
    haveI := (M.markov t ht i).isProbabilityMeasure ((), h)
    simp
  have hzero : HasDerivAt
      (fun t => (M.Q t i ((), h) Set.univ).toReal) 0 u :=
    (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq hevent
  simpa using hderiv.unique hzero

/-- A [sequential score model](hyp:M) at [a parameter in its domain](hyp:hu) has [a transcript
score, the density derivative divided by the density, equal almost everywhere under the
reference measure to the sum of its stage score increments](goal). This is the model's
assumed score bridge divided by the positive density. -/
theorem Model.score_ae_eq_sum (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) :
    (fun z => M.qdot u z / M.q u z) =ᵐ[M.reference]
      (fun z => ∑ i : Fin n, increment M.D i u z) := by
  filter_upwards [M.score_bridge u hu] with z hz
  rw [hz]
  exact mul_div_cancel_left₀ _ (ne_of_gt (M.q_positive u hu z))

private theorem measurable_take_local {k : ℕ} (hk : k ≤ n) :
    Measurable (take hk : Transcript Z → History Z k hk) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pi_apply (Fin.castLE hk j)

private theorem take_succ_eq_snoc_local (i : Fin n) (t : Transcript Z) :
    take (Nat.succ_le_of_lt i.isLt) t =
      snoc (Nat.succ_le_of_lt i.isLt) (take (Nat.le_of_lt i.isLt) t)
        (t (nextIndex (Nat.succ_le_of_lt i.isLt))) := by
  funext j
  refine Fin.lastCases ?_ (fun a => ?_) j
  · simp [take, snoc, nextIndex, Fin.snoc, Fin.castLE]
  · simp [take, snoc, Fin.snoc, Fin.castLE]

private theorem integral_next_local (M : Model n Z) {u : ℝ}
    (hu : u ∈ M.domain) (k : ℕ) (hk : k + 1 ≤ n)
    (f : History Z k (Nat.le_of_succ_le hk) × Z (nextIndex hk) → ℝ)
    (hf : Measurable f)
    (hfi : Integrable (fun t : Transcript Z =>
      f (take (Nat.le_of_succ_le hk) t, t (nextIndex hk))) (law M.Q u)) :
    (∫ t, f (take (Nat.le_of_succ_le hk) t,
      t (nextIndex hk)) ∂law M.Q u) =
      ∫ h, ∫ z, f (h, z) ∂M.Q u (nextIndex hk) ((), h)
        ∂prefixLaw (M.Q u) (fun _ => ()) k (Nat.le_of_succ_le hk) := by
  letI : IsProbabilityMeasure
      (prefixLaw (M.Q u) (fun _ => ()) k (Nat.le_of_succ_le hk)) :=
    isProbabilityMeasure_prefixLaw (M.Q u) (M.markov u hu) (fun _ => ())
      k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel (M.Q u (nextIndex hk)) := M.markov u hu _
  have hp : Measurable (fun t : Transcript Z =>
      (take (Nat.le_of_succ_le hk) t, t (nextIndex hk))) :=
    (measurable_take_local (Nat.le_of_succ_le hk)).prodMk
      (measurable_pi_apply _)
  have hm := transcriptLaw_map_take_next (M.Q u) (M.markov u hu)
    (fun _ => ()) k hk
  have hfm : Integrable f
      ((prefixLaw (M.Q u) (fun _ => ()) k (Nat.le_of_succ_le hk)) ⊗ₘ
        (M.Q u (nextIndex hk)).comap (fun h => ((), h)) (by fun_prop)) := by
    rw [← hm]
    exact (integrable_map_measure hf.aestronglyMeasurable hp.aemeasurable).2 hfi
  calc
    _ = ∫ p, f p ∂((prefixLaw (M.Q u) (fun _ => ()) k
        (Nat.le_of_succ_le hk)) ⊗ₘ
        (M.Q u (nextIndex hk)).comap (fun h => ((), h)) (by fun_prop)) := by
      rw [← hm]
      exact (integral_map hp.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [Measure.integral_compProd hfm]
      rfl

/-- A [sequential score model](hyp:M), [a parameter in its domain](hyp:hu), [a stage](hyp:i),
and [a measurable event of the preceding history](hyp:A,hA) have [a stage increment whose
integral over that event is zero](goal). -/
theorem Model.increment_prefix_centered (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) (i : Fin n)
    (A : Set (History Z i.val (Nat.le_of_lt i.isLt))) (hA : MeasurableSet A) :
    (∫ z in (take (Nat.le_of_lt i.isLt)) ⁻¹' A,
      increment M.D i u z ∂law M.Q u) = 0 := by
  rcases i with ⟨k, hk⟩
  let hk' : k + 1 ≤ n := Nat.succ_le_of_lt hk
  let f : History Z k (Nat.le_of_succ_le hk') × Z (nextIndex hk') → ℝ :=
    fun p => (Prod.fst ⁻¹' A).indicator
      (fun p => M.D ⟨k, hk⟩ u (snoc hk' p.1 p.2)) p
  have hf : Measurable f := by
    exact ((M.D_measurable u hu ⟨k, hk⟩).comp (measurable_snoc hk')).indicator
      (hA.preimage measurable_fst)
  have hDmeas : Measurable (increment M.D ⟨k, hk⟩ u) :=
    (M.D_measurable u hu ⟨k, hk⟩).comp
      (measurable_take_local (Nat.succ_le_of_lt hk))
  letI : IsProbabilityMeasure (law M.Q u) := M.law_probability hu
  have hDint : Integrable (increment M.D ⟨k, hk⟩ u) (law M.Q u) :=
    ((memLp_two_iff_integrable_sq hDmeas.aestronglyMeasurable).2
      (M.D_sq_integrable u hu ⟨k, hk⟩)).integrable (by norm_num)
  have hfi : Integrable (fun t : Transcript Z =>
      f (take (Nat.le_of_succ_le hk') t, t (nextIndex hk'))) (law M.Q u) := by
    have heq : (fun t : Transcript Z =>
        f (take (Nat.le_of_succ_le hk') t, t (nextIndex hk'))) =
        ((take (Nat.le_of_succ_le hk')) ⁻¹' A).indicator
          (increment M.D ⟨k, hk⟩ u) := by
      funext t
      have ht := take_succ_eq_snoc_local ⟨k, hk⟩ t
      simp only [f, Set.indicator, Set.mem_preimage, increment]
      rw [← ht]
      rfl
    rw [heq]
    exact hDint.indicator (hA.preimage (measurable_take_local _))
  have hdis := integral_next_local M hu k hk' f hf hfi
  have hzero (h : History Z k (Nat.le_of_succ_le hk')) :
      (∫ z, f (h, z) ∂M.Q u (nextIndex hk') ((), h)) = 0 := by
    by_cases hh : h ∈ A
    · have heq : (fun z => f (h, z)) =
          (fun z => M.D ⟨k, hk⟩ u (snoc hk' h z)) := by
        funext z
        simp [f, hh]
      rw [heq]
      exact M.stage_score_centered hu ⟨k, hk⟩ h
    · have heq : (fun z => f (h, z)) = (fun _ => (0 : ℝ)) := by
        funext z
        simp [f, hh]
      simp [heq]
  calc
    _ = ∫ t, f (take (Nat.le_of_succ_le hk') t, t (nextIndex hk'))
        ∂law M.Q u := by
      rw [← integral_indicator (hA.preimage (measurable_take_local _))]
      congr 1
      funext t
      have ht := take_succ_eq_snoc_local ⟨k, hk⟩ t
      simp only [f, Set.indicator, Set.mem_preimage, increment]
      rw [← ht]
      rfl
    _ = ∫ h, ∫ z, f (h, z) ∂M.Q u (nextIndex hk') ((), h)
        ∂prefixLaw (M.Q u) (fun _ => ()) k (Nat.le_of_succ_le hk') := by
      exact hdis
    _ = 0 := by simp [hzero]

/-- A [sequential score model](hyp:M), [a parameter in its domain](hyp:hu), [two stages](hyp:i,j),
and [the first stage preceding the second](hyp:hij) have [orthogonal score increments under the
transcript law](goal). -/
theorem Model.increment_orthogonal (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) (i j : Fin n) (hij : i < j) :
    (∫ z, increment M.D i u z * increment M.D j u z
      ∂law M.Q u) = 0 := by
  rcases j with ⟨k, hk⟩
  let hk' : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have hik : i.val + 1 ≤ k := hij
  let g : History Z k (Nat.le_of_succ_le hk') → ℝ :=
    fun h => M.D i u (restrictHistory (Nat.succ_le_of_lt i.isLt)
      (Nat.le_of_succ_le hk') hik h)
  have hg : Measurable g :=
    (M.D_measurable u hu i).comp
      (measurable_restrictHistory (Nat.succ_le_of_lt i.isLt)
        (Nat.le_of_succ_le hk') hik)
  let f : History Z k (Nat.le_of_succ_le hk') × Z (nextIndex hk') → ℝ :=
    fun p => g p.1 * M.D (nextIndex hk') u (snoc hk' p.1 p.2)
  have hf : Measurable f :=
    (hg.comp measurable_fst).mul
      ((M.D_measurable u hu (nextIndex hk')).comp (measurable_snoc hk'))
  have himeas : Measurable (increment M.D i u) :=
    (M.D_measurable u hu i).comp
      (measurable_take_local (Nat.succ_le_of_lt i.isLt))
  have hjmeas : Measurable (increment M.D ⟨k, hk⟩ u) :=
    (M.D_measurable u hu ⟨k, hk⟩).comp
      (measurable_take_local (Nat.succ_le_of_lt hk))
  have hli : MemLp (increment M.D i u) 2 (law M.Q u) :=
    (memLp_two_iff_integrable_sq himeas.aestronglyMeasurable).2
      (M.D_sq_integrable u hu i)
  have hlj : MemLp (increment M.D ⟨k, hk⟩ u) 2 (law M.Q u) :=
    (memLp_two_iff_integrable_sq hjmeas.aestronglyMeasurable).2
      (M.D_sq_integrable u hu ⟨k, hk⟩)
  have hprod : Integrable (fun t => increment M.D i u t *
      increment M.D ⟨k, hk⟩ u t) (law M.Q u) := hli.integrable_mul hlj
  have hpre (t : Transcript Z) :
      restrictHistory (Nat.succ_le_of_lt i.isLt)
        (Nat.le_of_succ_le hk') hik (take (Nat.le_of_succ_le hk') t) =
      take (Nat.succ_le_of_lt i.isLt) t := by
    funext a
    rfl
  have heq (t : Transcript Z) :
      f (take (Nat.le_of_succ_le hk') t, t (nextIndex hk')) =
      increment M.D i u t * increment M.D ⟨k, hk⟩ u t := by
    dsimp [f, g, increment]
    rw [hpre t, take_succ_eq_snoc_local ⟨k, hk⟩ t]
    dsimp [hk', nextIndex]
  have hfi : Integrable (fun t : Transcript Z =>
      f (take (Nat.le_of_succ_le hk') t, t (nextIndex hk'))) (law M.Q u) := by
    convert hprod using 1
    funext t
    exact heq t
  have hdis := integral_next_local M hu k hk' f hf hfi
  have hzero (h : History Z k (Nat.le_of_succ_le hk')) :
      (∫ z, f (h, z) ∂M.Q u (nextIndex hk') ((), h)) = 0 := by
    have heq' : (fun z => f (h, z)) =
        (fun z => g h * M.D (nextIndex hk') u (snoc hk' h z)) := rfl
    rw [heq', integral_const_mul]
    have hc : (∫ z, M.D (nextIndex hk') u (snoc hk' h z)
        ∂M.Q u (nextIndex hk') ((), h)) = 0 := by
      convert M.stage_score_centered hu (nextIndex hk') h using 1
      congr 1
    rw [hc, mul_zero]
  calc
    _ = ∫ t, f (take (Nat.le_of_succ_le hk') t, t (nextIndex hk'))
        ∂law M.Q u := by
      congr 1
      funext t
      exact (heq t).symm
    _ = ∫ h, ∫ z, f (h, z) ∂M.Q u (nextIndex hk') ((), h)
        ∂prefixLaw (M.Q u) (fun _ => ()) k (Nat.le_of_succ_le hk') := hdis
    _ = 0 := by simp [hzero]

/-- A [sequential score model](hyp:M), [a parameter in its domain](hyp:hu), and [a stage](hyp:i)
have [a score-increment second moment equal to the prefix average of its conditional
next-output second moment](goal). -/
theorem Model.increment_second_moment_eq_prefix (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) (i : Fin n) :
    (∫ z, (increment M.D i u z) ^ 2 ∂law M.Q u) =
      ∫ h, (∫ z, (M.D i u
        (snoc (Nat.succ_le_of_lt i.isLt) h z)) ^ 2
        ∂M.Q u i ((), h))
        ∂prefixLaw (M.Q u) (fun _ => ()) i.val (Nat.le_of_lt i.isLt) := by
  rcases i with ⟨k, hk⟩
  let hk' : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have hf : Measurable (fun p : History Z k (Nat.le_of_succ_le hk') ×
      Z (nextIndex hk') => (M.D ⟨k, hk⟩ u (snoc hk' p.1 p.2)) ^ 2) := by
    exact ((M.D_measurable u hu ⟨k, hk⟩).comp (measurable_snoc hk')).pow_const 2
  have hfi : Integrable (fun t : Transcript Z =>
      (M.D ⟨k, hk⟩ u (snoc hk' (take (Nat.le_of_succ_le hk') t)
        (t (nextIndex hk')))) ^ 2) (law M.Q u) := by
    convert (M.D_sq_integrable u hu ⟨k, hk⟩) using 1
    funext t
    rw [increment, take_succ_eq_snoc_local]
  convert
    (integral_next_local M hu k hk'
      (fun p => (M.D ⟨k, hk⟩ u (snoc hk' p.1 p.2)) ^ 2) hf hfi) using 1
  · congr 1
    funext t
    rw [increment, take_succ_eq_snoc_local]
  · rfl

/-- A [sequential score model](hyp:M) and [a parameter value](hyp:u) determine [the scalar
Fisher information of its transcript](goal), [given by the integral, against the model's common
reference measure, of the transcript density times the squared guarded likelihood score (the
density derivative divided by the density where the density is positive, zero
otherwise)](step:1). -/
noncomputable def Model.fisherInformation (M : Model n Z) (u : ℝ) : ℝ :=
  Causalean.Stat.Minimax.ObservationDependentVanTrees.fisherInformation
    M.reference M.q M.qdot u

/-- A [sequential score model](hyp:M) at [a parameter in its domain](hyp:hu) has [Fisher
information equal to the transcript-law second moment of its unguarded score](goal). -/
theorem Model.fisher_eq_law_score_sq (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) :
    M.fisherInformation u =
      ∫ z, (M.qdot u z / M.q u z) ^ 2 ∂law M.Q u := by
  have hmeas : Measurable (fun z => ENNReal.ofReal (M.q u z)) :=
    ((M.q_joint_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)
  rw [Model.fisherInformation,
    Causalean.Stat.Minimax.ObservationDependentVanTrees.fisherInformation,
    M.law_eq_density u hu,
    integral_withDensity_eq_integral_toReal_smul hmeas (by simp)]
  congr 1
  funext z
  simp [Causalean.Stat.Minimax.ObservationDependentVanTrees.likelihoodScore,
    M.q_positive u hu z, ENNReal.toReal_ofReal (le_of_lt (M.q_positive u hu z))]

/-- A [sequential score model](hyp:M) at [a parameter in its domain](hyp:hu) has [transcript
Fisher information equal to the sum over stages of the second moment of the stage score
increment under the transcript law](goal). -/
theorem Model.fisher_eq_sum_increment (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) :
    M.fisherInformation u =
      ∑ i : Fin n, ∫ z, (increment M.D i u z) ^ 2 ∂law M.Q u := by
  let μ := law M.Q u
  let f : Fin n → Transcript Z → ℝ := fun i z => increment M.D i u z
  have hmeas (i : Fin n) : Measurable (f i) := by
    exact (M.D_measurable u hu i).comp (by
      apply measurable_pi_iff.mpr
      intro j
      exact measurable_pi_apply (Fin.castLE (Nat.succ_le_of_lt i.isLt) j))
  have hLp (i : Fin n) : MemLp (f i) 2 μ :=
    (memLp_two_iff_integrable_sq (hmeas i).aestronglyMeasurable).2
      (M.D_sq_integrable u hu i)
  have hprod (i j : Fin n) : Integrable (fun z => f i z * f j z) μ :=
    (hLp i).integrable_mul (hLp j)
  have hcross (i j : Fin n) (hij : i ≠ j) :
      (∫ z, f i z * f j z ∂μ) = 0 := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact M.increment_orthogonal hu i j hlt
    · exact (hij heq).elim
    · have h := M.increment_orthogonal hu j i hgt
      convert h using 1
      congr 1
      funext z
      exact mul_comm _ _
  have hscore : (fun z => M.qdot u z / M.q u z) =ᵐ[μ]
      (fun z => ∑ i : Fin n, f i z) := by
    rw [show μ = M.reference.withDensity
      (fun z => ENNReal.ofReal (M.q u z)) from M.law_eq_density u hu]
    exact (withDensity_absolutelyContinuous M.reference _).ae_le
      (M.score_ae_eq_sum hu)
  rw [M.fisher_eq_law_score_sq hu]
  calc
    (∫ z, (M.qdot u z / M.q u z) ^ 2 ∂μ) =
        ∫ z, (∑ i : Fin n, f i z) ^ 2 ∂μ :=
      integral_congr_ae (hscore.fun_comp (fun x => x ^ 2))
    _ = ∫ z, ∑ i : Fin n, ∑ j : Fin n, f i z * f j z ∂μ := by
      congr 1
      funext z
      simp only [pow_two, Finset.sum_mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ z, f i z * f j z ∂μ := by
      rw [integral_finsetSum]
      · congr 1
        funext i
        rw [integral_finsetSum]
        exact fun j _ => hprod i j
      · intro i _
        exact integrable_finsetSum _ (fun j _ => hprod i j)
    _ = ∑ i : Fin n, ∫ z, (increment M.D i u z) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · congr 1
        funext z
        simp [f, pow_two]
      · intro j _ hji
        exact hcross i j (Ne.symm hji)
      · simp

/-- A [sequential score model](hyp:M), [a parameter in its domain](hyp:hu), and [a bound,
uniform over stages and preceding histories, on the conditional second moment of the next
stage score](hyp:B,hB) have [transcript Fisher information at most the
horizon times that bound](goal). -/
theorem Model.fisher_le_horizon_mul_bound (M : Model n Z)
    {u : ℝ} (hu : u ∈ M.domain) (B : ℝ)
    (hB : ∀ (i : Fin n) (h : History Z i.val (Nat.le_of_lt i.isLt)),
      (∫ z, (M.D i u (snoc (Nat.succ_le_of_lt i.isLt) h z)) ^ 2
        ∂M.Q u i ((), h)) ≤ B) :
    M.fisherInformation u ≤ (n : ℝ) * B := by
  rw [M.fisher_eq_sum_increment hu]
  have hstage (i : Fin n) :
      (∫ z, (increment M.D i u z) ^ 2 ∂law M.Q u) ≤ B := by
    rw [M.increment_second_moment_eq_prefix hu i]
    haveI : IsProbabilityMeasure
        (prefixLaw (M.Q u) (fun _ => ()) i.val (Nat.le_of_lt i.isLt)) :=
      isProbabilityMeasure_prefixLaw (M.Q u) (M.markov u hu)
        (fun _ => ()) i.val (Nat.le_of_lt i.isLt)
    have hnonneg : 0 ≤ᵐ[prefixLaw (M.Q u) (fun _ => ()) i.val
        (Nat.le_of_lt i.isLt)] (fun h => ∫ z, (M.D i u
          (snoc (Nat.succ_le_of_lt i.isLt) h z)) ^ 2
          ∂M.Q u i ((), h)) := by
      filter_upwards [] with h
      exact integral_nonneg (fun z => sq_nonneg _)
    have hle : (fun h => ∫ z, (M.D i u
        (snoc (Nat.succ_le_of_lt i.isLt) h z)) ^ 2
        ∂M.Q u i ((), h)) ≤ᵐ[prefixLaw (M.Q u) (fun _ => ()) i.val
          (Nat.le_of_lt i.isLt)] (fun _ => B) :=
      Filter.Eventually.of_forall (hB i)
    simpa using integral_mono_of_nonneg hnonneg (integrable_const B) hle
  calc
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ => hstage i)
    _ = (n : ℝ) * B := by simp

end Causalean.Stat.Minimax.SequentialScore
