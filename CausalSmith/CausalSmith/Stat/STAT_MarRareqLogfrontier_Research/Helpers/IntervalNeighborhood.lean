module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Tactic.IntegralLinearity

/-! Neighborhood coverage transfer and expected length for the many-prior interval argument. -/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:I,t,w,hw), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_neighborhood_iff
lemma connectedInterval_neighborhood_iff (I : ConnectedInterval) (t w : ℝ)
    (hw : 0 ≤ w) :
    (∃ x : ℝ, I.lo ≤ x ∧ x ≤ I.hi ∧ |x - t| ≤ w) ↔
      t ∈ Set.Icc (I.lo - w) (I.hi + w) := by
  constructor
  · rintro ⟨x, hxlo, hxhi, hx⟩
    rcases abs_le.mp hx with ⟨hx0, hx1⟩
    constructor <;> linarith
  · rintro ⟨ht0, ht1⟩
    refine ⟨max I.lo (t - w), le_max_left _ _, ?_, ?_⟩
    · exact max_le I.ordered (by linarith)
    · rw [abs_le]
      constructor
      · have := le_max_right I.lo (t - w)
        linarith
      · have : max I.lo (t - w) ≤ t + w := max_le (by linarith) (by linarith)
        linarith

/-- Given [the specified inputs and assumptions](hyp:θ,w,hw), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_measurableSet_neighborhood
lemma connectedInterval_measurableSet_neighborhood (θ w : ℝ) (hw : 0 ≤ w) :
    MeasurableSet {I : ConnectedInterval | ∃ x : ℝ,
      I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w} := by
  have hF : Measurable (fun I : ConnectedInterval =>
      (I.lo, I.hi, I.closedLeft, I.closedRight)) := by
    exact (measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_const.prodMk measurable_const))
  have hlo : Measurable (fun I : ConnectedInterval => I.lo - w) := by
    first | fun_prop | exact (measurable_connectedInterval_lo).sub_const w
  have hhi : Measurable (fun I : ConnectedInterval => I.hi + w) := by
    first | fun_prop | exact (measurable_connectedInterval_hi).add_const w
  have heq : {I : ConnectedInterval | ∃ x : ℝ,
      I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w} =
      {I | I.lo - w ≤ θ} ∩ {I | θ ≤ I.hi + w} := by
    ext I
    exact connectedInterval_neighborhood_iff I θ w hw
  rw [heq]
  exact (measurableSet_le hlo measurable_const).inter
    (measurableSet_le measurable_const hhi)

/-- Given [the specified inputs and assumptions](hyp:μ,θ,w,u,ε,hcoverage,hconcentration), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_joint_neighborhood_coverage
lemma connectedInterval_joint_neighborhood_coverage
    (μ : Measure (ℝ × ConnectedInterval)) [IsProbabilityMeasure μ]
    (θ w u ε : ℝ)
    (hcoverage : u ≤ μ.real {z | intervalContains z.2 z.1})
    (hconcentration : μ.real {z | w < |z.1 - θ|} ≤ ε) :
    u - ε ≤ μ.real {z | ∃ x : ℝ,
      z.2.lo ≤ x ∧ x ≤ z.2.hi ∧ |x - θ| ≤ w} := by
  have hsubset : {z : ℝ × ConnectedInterval | intervalContains z.2 z.1} ⊆
      {z | ∃ x : ℝ, z.2.lo ≤ x ∧ x ≤ z.2.hi ∧ |x - θ| ≤ w} ∪
        {z | w < |z.1 - θ|} := by
    intro z hz
    by_cases hnear : |z.1 - θ| ≤ w
    · left
      have hlo : z.2.lo ≤ z.1 := by
        have h := hz.1
        change (if z.2.closedLeft then z.2.lo ≤ z.1 else z.2.lo < z.1) at h
        split at h
        · exact h
        · exact h.le
      have hhi : z.1 ≤ z.2.hi := by
        have h := hz.2
        change (if z.2.closedRight then z.1 ≤ z.2.hi else z.1 < z.2.hi) at h
        split at h
        · exact h
        · exact h.le
      exact ⟨z.1, hlo, hhi, hnear⟩
    · exact Or.inr (lt_of_not_ge hnear)
  have hmono := measureReal_mono (μ := μ) hsubset
  have hunion := measureReal_union_le (μ := μ)
    {z | ∃ x : ℝ, z.2.lo ≤ x ∧ x ≤ z.2.hi ∧ |x - θ| ≤ w}
    {z | w < |z.1 - θ|}
  linarith

/-- Given [the specified inputs and assumptions](hyp:μ,θ,w,u,ε,hw,hcoverage,hconcentration), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_prior_neighborhood_coverage
lemma connectedInterval_prior_neighborhood_coverage
    (μ : Measure (ℝ × ConnectedInterval)) [IsProbabilityMeasure μ]
    (θ w u ε : ℝ) (hw : 0 ≤ w)
    (hcoverage : u ≤ μ.real {z | intervalContains z.2 z.1})
    (hconcentration : μ.real {z | w < |z.1 - θ|} ≤ ε) :
    u - ε ≤ (μ.map Prod.snd).real {I | ∃ x : ℝ,
      I.lo ≤ x ∧ x ≤ I.hi ∧ |x - θ| ≤ w} := by
  rw [map_measureReal_apply measurable_snd
    (connectedInterval_measurableSet_neighborhood θ w hw)]
  exact connectedInterval_joint_neighborhood_coverage μ θ w u ε
    hcoverage hconcentration

/-- Given [the specified inputs and assumptions](hyp:ν₀,M,ν,θ,δ,w,p,ε,hδ,hw,hhit,htv), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_expected_neighborhood_length_of_tv
lemma connectedInterval_expected_neighborhood_length_of_tv
    (ν₀ : Measure ConnectedInterval) [IsProbabilityMeasure ν₀]
    (M : ℕ) (ν : Fin (M + 1) → Measure ConnectedInterval)
    [∀ j, IsProbabilityMeasure (ν j)] (θ δ w p ε : ℝ)
    (hδ : 0 < δ) (hw : 0 ≤ w)
    (hhit : ∀ j : Fin (M + 1), p ≤ (ν j).real
      {I | ∃ x : ℝ, I.lo ≤ x ∧ x ≤ I.hi ∧
        |x - (θ + (j : ℝ) * δ)| ≤ w})
    (htv : ∀ j, Causalean.Stat.tvDist ν₀ (ν j) ≤ ε) :
    δ * (((M + 1 : ℕ) : ℝ) * (p - ε) - 1) - 2 * w ≤
      ∫ I : ConnectedInterval, I.hi - I.lo ∂ν₀ := by
  have hF : Measurable (fun I : ConnectedInterval =>
      (I.lo, I.hi, I.closedLeft, I.closedRight)) := by
    exact (measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).prodMk
        (measurable_const.prodMk measurable_const))
  have hlo : Measurable (fun I : ConnectedInterval => I.lo - w) := by
    first | fun_prop | exact (measurable_connectedInterval_lo).sub_const w
  have hhi : Measurable (fun I : ConnectedInterval => I.hi + w) := by
    first | fun_prop | exact (measurable_connectedInterval_hi).add_const w
  let L : ConnectedInterval → ℝ := fun I => I.lo - w
  let U : ConnectedInterval → ℝ := fun I => I.hi + w
  have hcoverage : ∀ j : Fin (M + 1), p - ε ≤ ν₀.real
      (Causalean.Stat.coverageEvent L U
        (Causalean.Stat.gridPoint θ δ j)) := by
    intro j
    have heq : {I : ConnectedInterval | ∃ x : ℝ,
        I.lo ≤ x ∧ x ≤ I.hi ∧ |x - (θ + (j : ℝ) * δ)| ≤ w} =
        Causalean.Stat.coverageEvent L U
          (Causalean.Stat.gridPoint θ δ j) := by
      ext I
      exact connectedInterval_neighborhood_iff I _ w hw
    have hh := hhit j
    rw [heq] at hh
    have hgap := Causalean.Stat.measureReal_sub_le_tvDist (μ := ν₀) (ν := ν j)
      (A := Causalean.Stat.coverageEvent L U
        (Causalean.Stat.gridPoint θ δ j))
      (Causalean.Stat.measurableSet_coverageEvent
        hlo hhi)
    linarith [htv j]
  have hbound :=
    Causalean.Stat.expected_interval_length_lower_of_grid
    ν₀ M θ δ (p - ε) hlo hhi hδ hcoverage
  have hlen : Integrable (fun I : ConnectedInterval => I.hi - I.lo) ν₀ :=
    Integrable.of_bound
      ((measurable_connectedInterval_hi).sub
        (measurable_connectedInterval_lo)).aestronglyMeasurable 2
      (Filter.Eventually.of_forall (fun I => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr I.ordered)]
        linarith [I.lower, I.upper]))
  have hexpand : ∀ I : ConnectedInterval,
      Causalean.Stat.intervalLength (I.lo - w) (I.hi + w) =
        (I.hi - I.lo) + 2 * w := by
    intro I
    dsimp [Causalean.Stat.intervalLength, L, U]
    rw [max_eq_right (by have h := I.2.2.1; linarith)]
    ring
  simp_rw [hexpand] at hbound
  have hlenw : Integrable (fun I : ConnectedInterval => (I.hi - I.lo) + 2 * w) ν₀ :=
    hlen.add (integrable_const (2 * w))
  rw [← ofReal_integral_eq_lintegral_ofReal hlenw
    (Filter.Eventually.of_forall (fun I => by
      change 0 ≤ I.hi - I.lo + 2 * w
      linarith [I.ordered]))] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg (fun I => by
      change 0 ≤ I.hi - I.lo + 2 * w
      linarith [I.ordered]))).mp hbound
  have heq : (∫ I : ConnectedInterval, (I.hi - I.lo) + 2 * w ∂ν₀) =
      (∫ I : ConnectedInterval, I.hi - I.lo ∂ν₀) + 2 * w := by
    integral_linearity
    simp
  rw [heq] at hreal
  linarith

/-- Given [the specified inputs and assumptions](hyp:ν₀,M,ν,θ,Δ,u,hΔ,hu,hM,hhit,htv), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_many_prior_length_floor
lemma connectedInterval_many_prior_length_floor
    (ν₀ : Measure ConnectedInterval) [IsProbabilityMeasure ν₀]
    (M : ℕ) (ν : Fin (M + 1) → Measure ConnectedInterval)
    [∀ j, IsProbabilityMeasure (ν j)] (θ Δ u : ℝ)
    (hΔ : 0 < Δ) (hu : 0 < u) (hM : 8 / u ≤ (M : ℝ))
    (hhit : ∀ j : Fin (M + 1), 7 * u / 8 ≤ (ν j).real
      {I | ∃ x : ℝ, I.lo ≤ x ∧ x ≤ I.hi ∧
        |x - (θ + (j : ℝ) * (Δ / M))| ≤ Δ / (8 * M)})
    (htv : ∀ j, Causalean.Stat.tvDist ν₀ (ν j) ≤ u / 16) :
    (21 * u / 32) * Δ ≤ ∫ I : ConnectedInterval, I.hi - I.lo ∂ν₀ := by
  have hMr : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hM
  have hMu : 8 ≤ (M : ℝ) * u := (div_le_iff₀ hu).mp hM
  have hbound := connectedInterval_expected_neighborhood_length_of_tv
    ν₀ M ν θ (Δ / M) (Δ / (8 * M)) (7 * u / 8) (u / 16)
    (by positivity) (by positivity) hhit htv
  apply le_trans ?_ hbound
  push_cast
  rw [show Δ / (M : ℝ) * (((M : ℝ) + 1) * (7 * u / 8 - u / 16) - 1) -
      2 * (Δ / (8 * M)) =
      (Δ * (((M : ℝ) + 1) * (7 * u / 8 - u / 16) - 1) - Δ / 4) / M by ring]
  apply (le_div_iff₀ hMr).mpr
  have harith : (21 * u / 32) * Δ * M ≤
      Δ * (((M : ℝ) + 1) * (7 * u / 8 - u / 16) - 1) - Δ / 4 := by
    nlinarith [mul_nonneg hΔ.le hu.le]
  exact harith

/-- Given [the specified inputs and assumptions](hyp:M,μ,θ,Δ,u,hΔ,hu,hM,hcoverage,hconcentration,htv), [the stated mathematical conclusion holds](goal). -/
-- @node: connectedInterval_many_prior_length_of_joint_coverage
lemma connectedInterval_many_prior_length_of_joint_coverage
    (M : ℕ) (μ : Fin (M + 1) → Measure (ℝ × ConnectedInterval))
    [∀ j, IsProbabilityMeasure (μ j)] (θ Δ u : ℝ)
    (hΔ : 0 < Δ) (hu : 0 < u) (hM : 8 / u ≤ (M : ℝ))
    (hcoverage : ∀ j, u ≤ (μ j).real {z | intervalContains z.2 z.1})
    (hconcentration : ∀ j : Fin (M + 1),
      (μ j).real {z | Δ / (8 * M) < |z.1 - (θ + (j : ℝ) * (Δ / M))|} ≤ u / 8)
    (htv : ∀ j, Causalean.Stat.tvDist
      ((μ 0).map Prod.snd) ((μ j).map Prod.snd) ≤ u / 16) :
    (21 * u / 32) * Δ ≤
      ∫ I : ConnectedInterval, I.hi - I.lo ∂((μ 0).map Prod.snd) := by
  have hMr : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hM
  let ν : Fin (M + 1) → Measure ConnectedInterval := fun j => (μ j).map Prod.snd
  have (j : Fin (M + 1)) : IsProbabilityMeasure (ν j) := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  apply connectedInterval_many_prior_length_floor (ν 0) M ν θ Δ u hΔ hu hM
  · intro j
    have h := connectedInterval_prior_neighborhood_coverage (μ j)
      (θ + (j : ℝ) * (Δ / M)) (Δ / (8 * M)) u (u / 8)
      (by positivity) (hcoverage j) (hconcentration j)
    convert h using 1; ring
  · exact htv

end CausalSmith.Stat.MarRareqLogfrontier
