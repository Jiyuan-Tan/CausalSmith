module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.PalmSplit
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product

/-!
# Finite products of label-gated marked-Poisson mixtures

The one-coordinate experiment is tensorized over finitely many independent
coordinates, and the reusable total-variation product inequality transfers
the geometric one-coordinate estimate with the expected factor `k`.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

namespace NormalizedFiniteSignedMomentCertificate

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- The [product marked-Poisson predictive law](goal) [independently repeats the one-coordinate
predictive law across a fixed number of coordinates](step:1). Its inputs are [a finite signed
certificate](hyp:C), [the coordinate count](hyp:k), [overlap](hyp:ε), [shift](hyp:a), [labeled
and auxiliary intensities](hyp:u,v), and [an outcome-mark branch](hyp:branch).

The four real parameters are unrestricted here; the results that need them positive, or need the
overlap below one half, take those as explicit hypotheses. -/
noncomputable def markedPoissonProductPredictive
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (k : ℕ) (ε a u v : ℝ) (branch : Bool) :
    Measure (Fin k → MarkedPoissonObservation) :=
  Measure.pi fun _ : Fin k => C.markedPoissonPredictive ε a u v branch

/-- The independent product of the marked-Poisson predictive law is a probability measure,
provided the scalar prior's support conditions hold: for [a certificate, coordinate count,
overlap, shift, intensities, support ratio, support bound and branch](hyp:C,k,ε,a,u,v,κ,B,branch),
if [the shift is positive](hyp:ha), [the support ratio is positive](hyp:hκ), and [the certificate's
variation is almost surely supported in the interval from the shift-to-ratio quotient up to the
bound](hyp:hsupp), then [the product law is a probability measure](goal). -/
theorem markedPoissonProductPredictive_isProbabilityMeasure
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (k : ℕ) (ε a u v κ B : ℝ) (branch : Bool)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    IsProbabilityMeasure
      (C.markedPoissonProductPredictive k ε a u v branch) := by
  letI : IsProbabilityMeasure (C.markedPoissonPredictive ε a u v branch) :=
    C.markedPoissonPredictive_isProbabilityMeasure ε a u v κ B branch ha hκ hsupp
  change IsProbabilityMeasure
    (Measure.pi fun _ : Fin k => C.markedPoissonPredictive ε a u v branch)
  exact inferInstance

/-- A [one-coordinate total-variation bound](hyp:hone) by [a distance
threshold](hyp:δ) [tensorizes to the same bound times the number of independent
coordinates](goal) for [a certificate](hyp:C), [coordinate count](hyp:k), and [overlap, shift,
intensity, and support parameters](hyp:ε,a,u,v,κ,B), provided [the shift is
positive](hyp:ha), [the support ratio is positive](hyp:hκ), and [the certificate variation has
the stated compact support](hyp:hsupp). -/
theorem tvDist_markedPoissonProductPredictive_le
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (k : ℕ) (ε a u v κ B δ : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (hone : Causalean.Stat.tvDist
        (C.markedPoissonPredictive ε a u v false)
        (C.markedPoissonPredictive ε a u v true) ≤ δ) :
    Causalean.Stat.tvDist
        (C.markedPoissonProductPredictive k ε a u v false)
        (C.markedPoissonProductPredictive k ε a u v true) ≤ k * δ := by
  letI : IsProbabilityMeasure (C.markedPoissonPredictive ε a u v false) :=
    C.markedPoissonPredictive_isProbabilityMeasure ε a u v κ B false ha hκ hsupp
  letI : IsProbabilityMeasure (C.markedPoissonPredictive ε a u v true) :=
    C.markedPoissonPredictive_isProbabilityMeasure ε a u v κ B true ha hκ hsupp
  unfold markedPoissonProductPredictive
  calc
    Causalean.Stat.tvDist
        (Measure.pi fun _ : Fin k => C.markedPoissonPredictive ε a u v false)
        (Measure.pi fun _ : Fin k => C.markedPoissonPredictive ε a u v true) ≤
      k * Causalean.Stat.tvDist
        (C.markedPoissonPredictive ε a u v false)
        (C.markedPoissonPredictive ε a u v true) :=
      Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_pi_iid_le k _ _
    _ ≤ k * δ := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg k)

/-- Given [a finite signed certificate](hyp:C), [a number of coordinates](hyp:k), [an overlap
parameter](hyp:ε), [a shift parameter](hyp:a), [a labeled intensity](hyp:u), [an auxiliary
intensity](hyp:v), [a support ratio](hyp:κ), [a support bound](hyp:B), [a coefficient](hyp:C₀),
and [a power base](hyp:ρ), if [the shift is positive](hyp:ha), [the support ratio is
positive](hyp:hκ), [the certificate variation has the stated support](hyp:hsupp), and [the
one-coordinate geometric total-variation bound is assumed](hyp:hone), then [that assumed bound
tensorizes over the coordinates with an extra factor `k`](goal).

This conditional tensorization result does not establish the one-coordinate estimate. -/
theorem markedPoissonProductPredictive_geometric_tv_le_of_one_coordinate_bound
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (k : ℕ) (ε a u v κ B C₀ ρ : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (hone : Causalean.Stat.tvDist
        (C.markedPoissonPredictive ε a u v false)
        (C.markedPoissonPredictive ε a u v true) ≤ C₀ * u * a * ρ ^ L) :
    Causalean.Stat.tvDist
        (C.markedPoissonProductPredictive k ε a u v false)
        (C.markedPoissonProductPredictive k ε a u v true) ≤
      C₀ * u * k * a * ρ ^ L := by
  calc
    Causalean.Stat.tvDist
        (C.markedPoissonProductPredictive k ε a u v false)
        (C.markedPoissonProductPredictive k ε a u v true) ≤
      k * (C₀ * u * a * ρ ^ L) :=
      C.tvDist_markedPoissonProductPredictive_le k ε a u v κ B
        (C₀ * u * a * ρ ^ L) ha hκ hsupp hone
    _ = C₀ * u * k * a * ρ ^ L := by ring

end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
