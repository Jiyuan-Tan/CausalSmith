/- Row-indexed adaptive experiments for the Saco AIPW comparison. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Basic
import Causalean.Experimentation.Sequential.AdaptiveDesign

/-! # Saco triangular-array world -/

open Filter MeasureTheory ProbabilityTheory

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

-- @env: S2
/-- A triangular array whose design layer is one reused `AdaptiveExperiment`
per row.  The extra fields are precisely the potential-outcome, nuisance, and
scored-set data absent from the single-row library carrier. -/
structure SacoArrayWorld (Ω 𝒳 : Type*) [MeasurableSpace Ω] [MeasurableSpace 𝒳] where
  row : ℕ → Causalean.Experimentation.Sequential.AdaptiveExperiment Ω ‹MeasurableSpace Ω›
    -- @realizes \mathcal F_t((row n).F is the row filtration)
    -- @realizes \pi_t((row n).propensity is the logged row propensity)
  law : ℕ → Measure Ω -- @realizes P(row-indexed probability law)
  law_univ : ∀ n, law n Set.univ = 1
  horizon : ℕ → ℕ
  horizon_pos : ∀ n, 0 < horizon n
  context : ℕ → ℕ → Ω → 𝒳 -- @realizes X_t(row-indexed current covariate)
  potential0 : ℕ → ℕ → Ω → ℝ -- @realizes Y_t(a)(binary potential outcome under arm zero)
  potential1 : ℕ → ℕ → Ω → ℝ -- @realizes Y_t(a)(binary potential outcome under arm one)
  action : ℕ → ℕ → Ω → Bool -- @realizes A_t(binary row-indexed assignment)
  outcome : ℕ → ℕ → Ω → ℝ -- @realizes Y_t(observed row-indexed outcome)
  nuisance : ℕ → ℕ → Fin 2 → 𝒳 → Ω → ℝ
  preTreatment : ℕ → ℕ → MeasurableSpace Ω
  scoredSet : ℕ → Finset ℕ
  scoredSet_domain : ∀ n, scoredSet n ⊆ Finset.Icc 1 (horizon n)
  scoredTime : ℕ → ℕ → ℕ
  scoredTime_mem : ∀ n s, s < (scoredSet n).card → scoredTime n s ∈ scoredSet n
  scoredFiltration : ℕ → Filtration ℕ ‹MeasurableSpace Ω›
  scoredFiltration_before : ∀ n s, 1 ≤ s → s ≤ (scoredSet n).card →
    scoredFiltration n (s - 1) = (row n).ℱ (scoredTime n (s - 1) - 1)
  scoredFiltration_after : ∀ n s, 1 ≤ s → s ≤ (scoredSet n).card →
    (row n).ℱ (scoredTime n (s - 1)) ≤ scoredFiltration n s
  scoredFiltration_terminal : ∀ n, 0 < (scoredSet n).card →
    scoredFiltration n (scoredSet n).card =
      (row n).ℱ (scoredTime n ((scoredSet n).card - 1))

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

/-- Uniform two-sided overlap, almost surely and only at the deterministic
scored indices of each row. -/
def RowOverlapAE (W : SacoArrayWorld Ω 𝒳) (eps : ℝ) : Prop :=
  0 < eps ∧ -- @realizes \varepsilon(positive uniform Saco overlap constant)
  eps < 1 / 2 ∧ -- @realizes \varepsilon(range below one half)
  ∀ n, ∀ t ∈ W.scoredSet n, ∀ᵐ ω ∂W.law n,
    eps ≤ (W.row n).propensity t ω ∧
      (W.row n).propensity t ω ≤ 1 - eps
      -- @realizes \pi_t(a.e. two-sided overlap at scored indices)

/-- Pointwise all-index overlap implies the source-faithful a.e. overlap
condition at scored indices.  No converse is asserted. -/
lemma rowOverlapAE_of_hasOverlap {W : SacoArrayWorld Ω 𝒳} {eps : ℝ}
    (heps : eps < 1 / 2)
    (h : ∀ n,
      Causalean.Experimentation.Sequential.AdaptiveExperiment.HasOverlap (W.row n) eps) :
    RowOverlapAE W eps := by
  refine ⟨(h 0).1, heps, ?_⟩
  intro n t _ht
  exact Filter.Eventually.of_forall fun ω => (h n).2 t ω

def SacoArrayWorld.N (W : SacoArrayWorld Ω 𝒳) (n : ℕ) : ℕ := (W.scoredSet n).card

def SacoArrayWorld.theta0 (W : SacoArrayWorld Ω 𝒳) (n : ℕ) : ℝ :=
  ∫ ω, W.potential1 n 1 ω - W.potential0 n 1 ω ∂W.law n

def SacoArrayWorld.phiHat (W : SacoArrayWorld Ω 𝒳) (n t : ℕ) (ω : Ω) : ℝ :=
  let p := (W.row n).propensity t ω
  let a : ℝ := if W.action n t ω then 1 else 0
  let m1 := W.nuisance n (t - 1) 1 (W.context n t ω) ω
  let m0 := W.nuisance n (t - 1) 0 (W.context n t ω) ω
  a / p * (W.outcome n t ω - m1) -
    (1 - a) / (1 - p) * (W.outcome n t ω - m0) + m1 - m0

def SacoArrayWorld.increment (W : SacoArrayWorld Ω 𝒳) (n s : ℕ) : Ω → ℝ :=
  fun ω => W.phiHat n (W.scoredTime n (s - 1)) ω - W.theta0 n
  -- @realizes \xi_t(centered AIPW score in scored order)

def SacoArrayWorld.scoreSum (W : SacoArrayWorld Ω 𝒳) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ s ∈ Finset.Icc 1 (W.N n), W.increment n s ω
  -- @realizes S_T(row AIPW score sum)

def SacoArrayWorld.realizedQV (W : SacoArrayWorld Ω 𝒳) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ s ∈ Finset.Icc 1 (W.N n), (W.increment n s ω) ^ 2
  -- @realizes [S]_T(row realized score QV)

def SacoArrayWorld.predictableQV (W : SacoArrayWorld Ω 𝒳) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ s ∈ Finset.Icc 1 (W.N n),
    (W.law n)[(fun ω' => (W.increment n s ω') ^ 2) |
      W.scoredFiltration n (s - 1)] ω
  -- @realizes \langle S\rangle_T(row predictable score QV)

def SacoArrayWorld.thetaHat (W : SacoArrayWorld Ω 𝒳) (n : ℕ) : Ω → ℝ :=
  fun ω => (W.N n : ℝ)⁻¹ * ∑ s ∈ Finset.Icc 1 (W.N n),
    W.phiHat n (W.scoredTime n (s - 1)) ω

def SacoArrayWorld.sampleVariance (W : SacoArrayWorld Ω 𝒳) (n : ℕ) : Ω → ℝ :=
  fun ω => ((W.N n : ℝ) - 1)⁻¹ * ∑ s ∈ Finset.Icc 1 (W.N n),
    (W.phiHat n (W.scoredTime n (s - 1)) ω - W.thetaHat n ω) ^ 2

end

end CausalSmith.Experimentation.BanditRandomQV
