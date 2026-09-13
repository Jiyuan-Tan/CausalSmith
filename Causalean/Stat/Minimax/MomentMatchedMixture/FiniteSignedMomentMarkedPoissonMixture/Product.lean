import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.MarkedPoisson
import Causalean.Stat.Minimax.MomentMatchedMixture.Product

/-!
# Finite products of label-gated marked-Poisson mixtures

The one-coordinate experiment is tensorized over finitely many independent
coordinates, and the reusable total-variation product inequality transfers
the geometric one-coordinate estimate with the expected factor `k`.
-/

open MeasureTheory

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

namespace NormalizedFiniteSignedMomentCertificate

variable {ι : Type*} [Fintype ι] {L : ℕ}

/-- The [defined object](goal) is determined by [the finite signed certificate](hyp:C), [the number of independent coordinates](hyp:k), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the outcome-mark branch](hyp:branch) and is given by [the following defining expression](step:1).  The `k`-fold i.i.d. product of a one-coordinate marked-Poisson predictive
law. -/
noncomputable def markedPoissonProductPredictive
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (k : ℕ) (ε a u v : ℝ) (branch : Bool) :
    Measure (Fin k → MarkedPoissonObservation) :=
  Measure.pi fun _ : Fin k => C.markedPoissonPredictive ε a u v branch

/-- The [stated conclusion](goal) follows from [the finite signed certificate](hyp:C), [the number of independent coordinates](hyp:k), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [the outcome-mark branch](hyp:branch), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp).  The i.i.d. product marked-Poisson predictive law is a probability measure
under the scalar prior's support assumptions. -/
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

/-- The [stated conclusion](goal) follows from [the finite signed certificate](hyp:C), [the number of independent coordinates](hyp:k), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [the one-coordinate distance bound](hyp:δ), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp), [the one-coordinate TV bound](hyp:hone).  A one-coordinate TV estimate tensorizes to `k` independent coordinates
by `tvDist_pi_iid_le`. -/
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

/-- The [stated conclusion](goal) follows from [the finite signed certificate](hyp:C), [the number of independent coordinates](hyp:k), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [the geometric-bound constant](hyp:C₀), [the geometric decay factor](hyp:ρ), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp), [the one-coordinate TV bound](hyp:hone).  The geometric one-coordinate estimate composes with finite i.i.d.
products, giving `k` times the one-coordinate bound. -/
theorem markedPoissonProductPredictive_geometric_tv_le
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
