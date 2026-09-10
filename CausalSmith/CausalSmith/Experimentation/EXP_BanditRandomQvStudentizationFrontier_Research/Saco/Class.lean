/- Source conditions and early-QV stabilization for the Saco comparison. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Saco.World
import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.SelfNormalizedCLT

/-! # Saco source and repaired classes -/

open Filter MeasureTheory ProbabilityTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

variable {Ω 𝒳 I : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

/-- The ten numbered source conditions retained from Saco, written against
the row-indexed design carrier. -/
structure SacoSourceConditions (W : SacoArrayWorld Ω 𝒳)
    (epsilon CY CM vmin : ℝ) : Prop where
  consistency : ∀ n t, t ∈ Finset.Icc 1 (W.horizon n) →
    W.outcome n t =ᵐ[W.law n] fun ω =>
    if W.action n t ω then W.potential1 n t ω else W.potential0 n t ω
  iid_full_data : ∀ n,
    iIndepFun (fun t : {t // t ∈ Finset.Icc 1 (W.horizon n)} => fun ω =>
      (W.context n t.1 ω, W.potential0 n t.1 ω, W.potential1 n t.1 ω)) (W.law n) ∧
    ∀ t, t ∈ Finset.Icc 1 (W.horizon n) → IdentDistrib
      (fun ω => (W.context n t ω, W.potential0 n t ω, W.potential1 n t ω))
      (fun ω => (W.context n 1 ω, W.potential0 n 1 ω, W.potential1 n 1 ω))
      (W.law n) (W.law n)
  pretreatment_contains : ∀ n t, t ∈ Finset.Icc 1 (W.horizon n) →
    W.preTreatment n t ≤ (inferInstance : MeasurableSpace Ω) ∧
      (W.row n).ℱ (t - 1) ≤ W.preTreatment n t ∧
      Measurable[W.preTreatment n t] (W.context n t)
  logged_integrity : ∀ n t, t ∈ Finset.Icc 1 (W.horizon n) →
    Measurable[W.preTreatment n t] ((W.row n).propensity t) ∧
    (∀ᵐ ω ∂W.law n, 0 < (W.row n).propensity t ω ∧
      (W.row n).propensity t ω < 1) ∧
    (W.law n)[indicator (W.action n t) {true} | W.preTreatment n t] =ᵐ[W.law n]
      (W.row n).propensity t
  treatment_independence : ∀ n t, t ∈ Finset.Icc 1 (W.horizon n) →
    ConditionallyIndependent (W.law n) (W.preTreatment n t) (W.action n t)
    (fun ω => (W.potential0 n t ω, W.potential1 n t ω))
  overlap : RowOverlapAE W epsilon
  nuisance_measurable : ∀ n t, t ∈ W.scoredSet n → ∀ a x,
    Measurable[(W.row n).ℱ (t - 1)] (W.nuisance n (t - 1) a x)
  scored_times_ordered : ∀ n s, s + 1 < W.N n →
    W.scoredTime n s < W.scoredTime n (s + 1)
  increment_measurable : ∀ n s, 1 ≤ s → s ≤ W.N n →
    Measurable[(W.scoredFiltration n s)] (W.increment n s)
  terminal_scored_filtration : ∀ n, 0 < W.N n →
    W.scoredFiltration n (W.N n) = (W.row n).ℱ (W.scoredTime n (W.N n - 1))
  outcome_fourth_integrable : ∀ n t, t ∈ Finset.Icc 1 (W.horizon n) →
    Integrable (fun ω => |W.potential0 n t ω| ^ 4) (W.law n) ∧
    Integrable (fun ω => |W.potential1 n t ω| ^ 4) (W.law n)
  outcome_fourth : ∀ n t, t ∈ Finset.Icc 1 (W.horizon n) →
    (∫ ω, |W.potential0 n t ω| ^ 4 ∂W.law n) ≤ CY ∧
    (∫ ω, |W.potential1 n t ω| ^ 4 ∂W.law n) ≤ CY
  nuisance_fourth : ∀ n t, t ∈ W.scoredSet n → ∀ a,
    ∫ ω, |W.nuisance n (t - 1) a (W.context n t ω) ω| ^ 4 ∂W.law n ≤ CM
  nuisance_fourth_integrable : ∀ n t, t ∈ W.scoredSet n → ∀ a,
    Integrable (fun ω =>
      |W.nuisance n (t - 1) a (W.context n t ω) ω| ^ 4) (W.law n)
  effective_size : Tendsto W.N atTop atTop
  variance_growth : 0 < vmin ∧ ∀ δ > 0, ∀ᶠ n in atTop,
    (W.law n {ω | W.predictableQV n ω < vmin * W.N n}).toReal ≤ δ

-- @node: def:saco-early-stabilized-aipw-class
structure SacoEarlyStabilizedAIPWClass (W : I → SacoArrayWorld Ω 𝒳)
    (epsilon CY CM vmin lambdaMin : ℝ) (k : ℕ → ℕ)
    (Lambda : ℕ → I → Ω → ℝ) [Nonempty I] : Prop where
  source : ∀ i, SacoSourceConditions (W i) epsilon CY CM vmin
  common_scored_set : ∀ i j, (W i).scoredSet = (W j).scoredSet
  source_variance_growth : ∀ delta > 0, ∀ᶠ n in atTop, ∀ i,
    ((W i).law n {ω | (W i).predictableQV n ω < vmin * (W i).N n}).toReal ≤ delta
  cutoff : ∀ n i, k n < (W i).N n
  cutoff_negligible : Tendsto (fun n => (k n : ℝ) / (W (Classical.choice inferInstance)).N n)
    atTop (𝓝 0)
  lambda_pos : 0 < lambdaMin
  lambda_measurable : ∀ n i, Measurable[(W i).scoredFiltration n (k n)] (Lambda n i)
  lambda_floor : ∀ n i, ∀ᵐ ω ∂(W i).law n, lambdaMin ≤ Lambda n i ω
  suffix_stabilizes : UniformInProbability (fun n i => (W i).law n)
    (fun n i ω => (∑ s ∈ Finset.Icc (k n + 1) ((W i).N n),
      ((W i).law n)[(fun ω' => ((W i).increment n s ω') ^ 2) |
        (W i).scoredFiltration n (s - 1)] ω) /
          (((W i).N n : ℝ) * Lambda n i ω))
    (fun _ _ _ => 1)
  -- @realizes \Lambda_T(positive early-filtration-measurable Saco scale)
  -- @realizes k_T(o(N_n) deterministic early cutoff)

end

end CausalSmith.Experimentation.BanditRandomQV
