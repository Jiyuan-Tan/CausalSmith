module
public import Causalean.Stat.Concentration.Covering.VCCovering
public import Causalean.Stat.Concentration.Covering.HausslerPacking
public import Causalean.Stat.Concentration.Covering.DudleyEntropy
public import Causalean.Stat.Concentration.Localization.CriticalRadius
public import Causalean.Stat.Concentration.Rademacher.Symmetrization
public import Causalean.Stat.Concentration.Localization.UniformDeviation
public import FoML.ExpectationInequalities
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Samplewise finite-VC localization data

This file defines the binary factored VC-class certificate and a two-field
samplewise localization certificate. The finite-pattern bounds use its
empirical-radius field; its total-boundedness field is retained in the public
structure but is not used by that branch. The file also defines the finite-VC
slope and its linear envelope.
-/

@[expose] public section

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory

universe u v

section Definitions

variable {ι : Type u} {𝒳 : Type v}

/-- A binary factorization of a real-valued function class through
[a Boolean labeling `π`](hyp:π), such that
[on every finite sample each function's values factor through the Boolean labels](hyp:factor),
and whose realized Boolean patterns have
[VC dimension at most `d` on every finite sample](hyp:vcDim_le). -/
structure BinaryFactoredVCClass (F : ι → 𝒳 → ℝ) (d : ℕ) where
  /-- The Boolean class through which `F` factors on samples. -/
  π : ι → 𝒳 → Bool
  /-- Samplewise factorization through the Boolean labels. -/
  factor : ∀ {n : ℕ} (S : Fin n → 𝒳), ∃ φ : Fin n → Bool → ℝ,
    ∀ i j, F i (S j) = φ j (π i (S j))
  /-- Uniform VC dimension bound for the realized growth family. -/
  vcDim_le : ∀ {n : ℕ} (S : Fin n → 𝒳), (growthFamily π S).vcDim ≤ d

/-- The samplewise localization certificate records [an empirical L² radius
bound for every localized star-hull member on every deterministic
sample](hyp:empirical_radius) and [total boundedness of each empirical
class](hyp:totallyBounded).

The universal `empirical_radius` field is substantially stronger than the standard
population-$L^2(P)$ localization in Bartlett--Bousquet--Mendelson (2005, Theorem 3.3) and
Wainwright (2019, Chapter 14): it amounts to samplewise, hence essentially sup-norm,
localization. Replacing it by the standard assumption requires a separate high-probability
event that controls the empirical radius uniformly over localized star-hull parameters,
radii, and peeling shells, with its failure probability folded into the final deviation
event. That event lemma is not currently available, so users should treat this
structure as the stronger deterministic variant rather than as a formalization
of population-$L^2(P)$ localization. The current finite-pattern Massart bounds
use only `empirical_radius`; `totallyBounded` is not consumed by that branch. -/
structure SamplewiseLocalizedVCDudleyHypotheses
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) where
  empirical_radius : ∀ {n : ℕ} (S : Fin n → 𝒳) {r : ℝ}, 0 ≤ r →
    ∀ p : starHullParam ι, empiricalNorm S (starHullZeroOut F norm r p) ≤ r
  totallyBounded : ∀ {n : ℕ} (S : Fin n → 𝒳) {r : ℝ}, 0 < r →
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S))

/-- If every function in a class is pointwise bounded in absolute value by a common
constant, then every zeroed localized star-hull function has the same bound at every point. -/
lemma abs_starHullZeroOut_le_of_bound
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ} {B r : ℝ}
    (hbound : ∀ i x, |F i x| ≤ B) (p : starHullParam ι) (x : 𝒳) :
    |starHullZeroOut F norm r p x| ≤ B := by
  rcases p with ⟨a, i⟩
  by_cases hactive : norm (starHullEval F (a, i)) ≤ r
  · calc
      |starHullZeroOut F norm r (a, i) x|
          = |(a : ℝ) * F i x| := by
            simp [starHullZeroOut, hactive, starHullEval]
      _ = (a : ℝ) * |F i x| := by
            rw [abs_mul, abs_of_nonneg a.property.1]
      _ ≤ 1 * |F i x| :=
            mul_le_mul_of_nonneg_right a.property.2 (abs_nonneg _)
      _ ≤ B := by simpa using hbound i x
  · have hB : 0 ≤ B := (abs_nonneg (F i x)).trans (hbound i x)
    simpa [starHullZeroOut, hactive] using hB

/-- A function whose absolute value is bounded at every point of a finite
sample has empirical root-mean-square norm no larger than that bound. -/
lemma empiricalNorm_le_of_forall_abs_le
    {n : ℕ} (S : Fin n → 𝒳) {f : 𝒳 → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hf : ∀ j : Fin n, |f (S j)| ≤ η) :
    empiricalNorm S f ≤ η := by
  classical
  by_cases hn : n = 0
  · simp [empiricalNorm, hn, hη]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hsum :
        (∑ j : Fin n, (f (S j)) ^ 2) ≤ ∑ _j : Fin n, η ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro j _
      calc
        (f (S j)) ^ 2 = |f (S j)| ^ 2 := by rw [sq_abs]
        _ ≤ η ^ 2 :=
            sq_le_sq.mpr (by simpa [abs_of_nonneg hη] using hf j)
    have harg :
        (1 / (n : ℝ)) * ∑ j : Fin n, (f (S j)) ^ 2 ≤ η ^ 2 := by
      calc
        (1 / (n : ℝ)) * ∑ j : Fin n, (f (S j)) ^ 2
            ≤ (1 / (n : ℝ)) * ∑ _j : Fin n, η ^ 2 :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (1 / (n : ℝ)) * ((n : ℝ) * η ^ 2) := by
              simp
        _ = η ^ 2 := by
              field_simp [Finset.card_fin, hnR.ne']
    calc
      empiricalNorm S f
          = Real.sqrt ((1 / (n : ℝ)) * ∑ j : Fin n, (f (S j)) ^ 2) := rfl
      _ ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt harg
      _ = η := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hη]

/-- If two functions differ by at most a nonnegative amount at every observation
in a finite sample, then their empirical distance is at most that amount. -/
lemma empiricalFunctionSpace_dist_le_of_forall_abs_sub_le
    {G : starHullParam ι → 𝒳 → ℝ} {n : ℕ} {S : Fin n → 𝒳}
    (q q' : EmpiricalFunctionSpace G S) {η : ℝ} (hη : 0 ≤ η)
    (hcoord : ∀ j : Fin n, |G q.index (S j) - G q'.index (S j)| ≤ η) :
    dist q q' ≤ η := by
  have hnorm :
      empiricalNorm S ((q : 𝒳 → ℝ) - (q' : 𝒳 → ℝ)) ≤ η :=
    empiricalNorm_le_of_forall_abs_le S hη (by
      intro j
      simpa [Pi.sub_apply] using hcoord j)
  simpa [instDistEmpiricalFunctionSpace, empiricalDist] using hnorm

/-- A uniformly bounded function class has a totally bounded empirical image on
every finite sample after taking its zeroed star hull. -/
lemma starHullZeroOut_totallyBounded_of_bounded
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ} {B : ℝ}
    (hbound : ∀ i x, |F i x| ≤ B)
    {n : ℕ} (S : Fin n → 𝒳) {r : ℝ} :
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S)) := by
  classical
  let sampleVector :
      EmpiricalFunctionSpace (starHullZeroOut F norm r) S → Fin n → ℝ :=
    fun q j => starHullZeroOut F norm r q.index (S j)
  have hcube :
      TotallyBounded
        (Set.Icc (fun _ : Fin n => -B) (fun _ : Fin n => B) :
          Set (Fin n → ℝ)) :=
    isCompact_Icc.totallyBounded
  refine Metric.totallyBounded_of_finite_discretization
    (s := (Set.univ :
      Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S))) ?_
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  rcases Metric.finite_approx_of_totallyBounded hcube δ hδ with
    ⟨t, ht_subset, ht_finite, ht_cover⟩
  have hmem_cube :
      ∀ q : (Set.univ :
          Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S)),
        sampleVector q.1 ∈
          (Set.Icc (fun _ : Fin n => -B) (fun _ : Fin n => B) :
            Set (Fin n → ℝ)) := by
    intro q
    constructor
    · intro j
      exact neg_le_of_abs_le
        (abs_starHullZeroOut_le_of_bound hbound q.1.index (S j))
    · intro j
      exact le_of_abs_le
        (abs_starHullZeroOut_le_of_bound hbound q.1.index (S j))
  have hnear :
      ∀ q : (Set.univ :
          Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S)),
        ∃ y : (t : Set (Fin n → ℝ)), dist (sampleVector q.1) y.1 < δ := by
    intro q
    have hq := ht_cover (hmem_cube q)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hq
    rcases hq with ⟨y, hy_t, hy_dist⟩
    exact ⟨⟨y, hy_t⟩, hy_dist⟩
  let domain : Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S) :=
    Set.univ
  let center0 : domain → (t : Set (Fin n → ℝ)) :=
    fun q => Classical.choose (hnear q)
  let center : domain → ULift.{u} (t : Set (Fin n → ℝ)) :=
    fun q => ULift.up (center0 q)
  haveI : Fintype (t : Set (Fin n → ℝ)) := ht_finite.fintype
  refine ⟨ULift.{u} (t : Set (Fin n → ℝ)), inferInstance, center, ?_⟩
  intro q q' hcenter
  have hcenter0 : center0 q = center0 q' := by
    simpa [center] using congrArg ULift.down hcenter
  have hq_near : dist (sampleVector q.1) (center0 q).1 < δ :=
    Classical.choose_spec (hnear q)
  have hq'_near : dist (sampleVector q'.1) (center0 q').1 < δ :=
    Classical.choose_spec (hnear q')
  have hcoord : ∀ j : Fin n,
      |starHullZeroOut F norm r q.1.index (S j) -
        starHullZeroOut F norm r q'.1.index (S j)| ≤ ε / 2 := by
    intro j
    have hjq : dist (sampleVector q.1 j) ((center0 q).1 j) < δ :=
      (dist_le_pi_dist (sampleVector q.1) (center0 q).1 j).trans_lt hq_near
    have hjq' : dist ((center0 q).1 j) (sampleVector q'.1 j) < δ := by
      rw [← hcenter0] at hq'_near
      simpa [dist_comm] using
        (dist_le_pi_dist (sampleVector q'.1) (center0 q).1 j).trans_lt hq'_near
    have hsum :
        dist (sampleVector q.1 j) (sampleVector q'.1 j) < ε / 2 := by
      calc
        dist (sampleVector q.1 j) (sampleVector q'.1 j)
            ≤ dist (sampleVector q.1 j) ((center0 q).1 j) +
                dist ((center0 q).1 j) (sampleVector q'.1 j) :=
              dist_triangle _ _ _
        _ < δ + δ := add_lt_add hjq hjq'
        _ = ε / 2 := by ring
    simpa [Real.dist_eq] using le_of_lt hsum
  have hdist_le :
      dist q.1 q'.1 ≤ ε / 2 :=
    empiricalFunctionSpace_dist_le_of_forall_abs_sub_le q.1 q'.1
      (by positivity) hcoord
  exact lt_of_le_of_lt hdist_le (by linarith)

/-- For [a function class on an observation space, a localization norm, and a common
envelope](hyp:ι,𝒳,F,norm,B), if [every function is pointwise bounded by the
envelope](hyp:hbound) and [every localized zeroed star-hull function has empirical
radius at most its localization radius on every sample](hyp:empirical_radius),
then [the class has the samplewise localization certificate](goal).

The bound supplies total boundedness, while the empirical-radius premise
supplies the field used by the finite-pattern Rademacher bounds.

For a population `L²(μ)` localization norm, the `empirical_radius` argument is
the genuine extra bridge: boundedness alone does not imply that every function
with population radius at most `r` has empirical radius at most `r` on every
sample. -/
theorem samplewiseLocalizedVCDudleyHypotheses_of_empiricalRadius
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ} {B : ℝ}
    (hbound : ∀ i x, |F i x| ≤ B)
    (empirical_radius : ∀ {n : ℕ} (S : Fin n → 𝒳) {r : ℝ}, 0 ≤ r →
      ∀ p : starHullParam ι, empiricalNorm S (starHullZeroOut F norm r p) ≤ r) :
    SamplewiseLocalizedVCDudleyHypotheses F norm where
  empirical_radius := empirical_radius
  totallyBounded := fun {_} S {_} _ =>
    starHullZeroOut_totallyBounded_of_bounded hbound S

/-- Given [a tuning constant](hyp:K), [a VC-dimension bound](hyp:d), and [a sample size](hyp:n), [the finite-VC localized slope](goal) is $6\sqrt{(K d\log(n+1)+1)/n}$.

The finite-VC localized slope is the sample-size dependent coefficient in
the linear localized Rademacher envelope.

It has the displayed order given by the VC dimension, logarithmic sample-size
term, and tuning constant. -/
noncomputable def vcLocalizedSlope (K : ℝ) (d n : ℕ) : ℝ :=
  6 * Real.sqrt ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ))

/-- Given [a tuning constant](hyp:K), [a VC-dimension bound](hyp:d), and [a sample size](hyp:n), [the finite-VC localized envelope](goal) maps every radius $r$ to the finite-VC localized slope times $r$.

The finite-VC localized envelope maps a radius to the slope times that
radius. -/
noncomputable def vcLocalizedPsi (K : ℝ) (d n : ℕ) : ℝ → ℝ :=
  fun r => vcLocalizedSlope K d n * r

end Definitions


end Concentration
end Stat
end Causalean
