module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerIntervalDecision
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoPrior

/-! Finite-moment point-CATE frontier: TInteractionObstruction. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- A finite probability prior on original laws, represented by its support and weights. -/
abbrev FiniteLawPrior := Σ m : ℕ, (Fin m → ObservedLaw) ×
  {w : Fin m → ℝ≥0∞ // (∀ j, w j ≠ 0) ∧ ∑ j, w j = 1}
/-- The original n-record mixture of a finite law prior. -/
def FiniteLawPrior.sampleLaw (π : FiniteLawPrior) (n : ℕ) : Measure (Dataset n) :=
  ∑ j, π.2.2.1 j • Measure.pi (fun _ : Fin n => (π.2.1 j).P)
/-- The uniform sign prior, reindexed by a finite ordinal without changing its laws. -/
-- @node: uniformSignPrior
def uniformSignPrior (κ : Params) (n : ℕ) (ε : Bool) : FiniteLawPrior :=
  ⟨Fintype.card (Signs κ n),
    (fun j => lowerPriorLaw κ n ε ((Fintype.equivFin (Signs κ n)).symm j)),
    ⟨fun _ => (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹, by
      constructor
      · intro j
        simp
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        change (Fintype.card (Signs κ n) : ℝ≥0∞) *
          (Fintype.card (Signs κ n) : ℝ≥0∞)⁻¹ = 1
        exact ENNReal.mul_inv_cancel
          (by exact_mod_cast (Fintype.card_ne_zero (α := Signs κ n))) (by simp)⟩⟩

/-- Reindexing the uniform sign prior retains the original-record mixture exactly. -/
-- @node: uniformSignPrior_sampleLaw
lemma uniformSignPrior_sampleLaw (κ : Params) (n : ℕ) (ε : Bool) :
    (uniformSignPrior κ n ε).sampleLaw n = lowerMixture κ n ε := by
  classical
  unfold FiniteLawPrior.sampleLaw uniformSignPrior lowerMixture
  dsimp only
  rw [← Finset.smul_sum]
  congr 1
  exact (Equiv.sum_comp (Fintype.equivFin (Signs κ n)).symm
    (fun v => Measure.pi (fun _ : Fin n => (lowerPriorLaw κ n ε v).P)))

/-- Concrete constructions and numerical certificates used as existential proof witnesses. -/
-- @node: interaction_obstruction_concrete
lemma interaction_obstruction_concrete (κ : Params) (hκ : κ.Valid) (hb : boundary κ ≤ 1)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  0 < cInter κ ∧
  (∀ n : ℕ, 2 ≤ n → cInter κ*(n : ℝ)^(-rInter κ) ≤ minimaxRisk κ n ∧
    cInter κ*(n : ℝ)^(-rInter κ) ≤ honestLength κ n ∧
    (∀ ε v, InModel κ (lowerPriorLaw κ n ε v) ∧
      UniformDesign (lowerPriorLaw κ n ε v) ∧
      (lowerPriorLaw κ n ε v).tau = lowerEffect κ n ε ∧
      holderBall κ.γ (lowerPriorLaw κ n ε v).tau) ∧
    (∀ ε v w, (lowerPriorLaw κ n ε v).theta = (lowerPriorLaw κ n ε w).theta) ∧
    (∀ v w, cInter κ*(n : ℝ)^(-rInter κ) ≤
      |(lowerPriorLaw κ n true v).theta-(lowerPriorLaw κ n false w).theta|) ∧
    Causalean.Stat.tvDist (lowerMixture κ n true) (lowerMixture κ n false) ≤ 1/4) ∧
  (∀ K : Set Params, IsCompact K → K ⊆ {κ | κ.Valid ∧ boundary κ ≤ 1} →
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ κ' ∈ K, c0 ≤ cInter κ') := by
  refine ⟨cInter_pos κ, ?_, cInter_compact_lower_bound⟩
  intro n hn
  refine ⟨lower_interaction_minimax_risk κ n hκ hb hn,
    lower_interaction_honest_length κ n hκ hb hn,
    lower_prior_member_properties κ n hκ hb hn, ?_, ?_,
    lower_mixture_tv κ n hκ hb hn⟩
  · intro ε v w
    rw [lower_prior_target κ n hκ hb hn ε v, lower_prior_target κ n hκ hb hn ε w]
  · intro v w
    rw [lower_prior_target κ n hκ hb hn true v, lower_prior_target κ n hκ hb hn false w,
      cInter_separation_identity κ n hn]
    have hg := abs_nonneg (lowerEffect κ n true xstar-lowerEffect κ n false xstar)
    linarith

-- @node: thm:interaction-obstruction
/-- One existential parameter-indexed lower constant family is positive uniformly on compact
interaction regions. For every sample size, finite priors have constant support targets,
exact uniform design, deterministic smooth effects and close original-record mixtures. -/
theorem interaction_obstruction (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  ∃ c : Params → ℝ,
    (∀ κ, κ.Valid → boundary κ ≤ 1 → 0 < c κ ∧
      ∀ n : ℕ, 2 ≤ n →
        c κ*(n : ℝ)^(-rInter κ) ≤ minimaxRisk κ n ∧
        c κ*(n : ℝ)^(-rInter κ) ≤ honestLength κ n ∧
        ∃ π0 π1 : FiniteLawPrior, ∃ target0 target1 : ℝ,
        ∃ effect0 effect1 : unitInterval → ℝ,
          holderBall κ.γ effect0 ∧ holderBall κ.γ effect1 ∧
          (∀ j, InModel κ (π0.2.1 j) ∧ UniformDesign (π0.2.1 j) ∧
            (π0.2.1 j).theta = target0 ∧ (π0.2.1 j).tau = effect0) ∧
          (∀ j, InModel κ (π1.2.1 j) ∧ UniformDesign (π1.2.1 j) ∧
            (π1.2.1 j).theta = target1 ∧ (π1.2.1 j).tau = effect1) ∧
          c κ*(n : ℝ)^(-rInter κ) ≤ |target1-target0| ∧
          Causalean.Stat.tvDist (π0.sampleLaw n) (π1.sampleLaw n) ≤ 1/4) ∧
    (∀ K : Set Params, IsCompact K → K ⊆ {κ | κ.Valid ∧ boundary κ ≤ 1} →
      ∃ c0 : ℝ, 0 < c0 ∧ ∀ κ ∈ K, c0 ≤ c κ) := by
  classical
  refine ⟨cInter, ?_, ?_⟩
  · intro κ hκ hb
    have hc := interaction_obstruction_concrete κ hκ hb expLaw hiid
    refine ⟨hc.1, ?_⟩
    intro n hn
    rcases hc.2.1 n hn with ⟨hR, hL, hmem, htarget, hsep, htv⟩
    let v0 : Signs κ n := fun _ => false
    refine ⟨hR, hL, uniformSignPrior κ n true, uniformSignPrior κ n false,
      (lowerPriorLaw κ n true v0).theta, (lowerPriorLaw κ n false v0).theta,
      lowerEffect κ n true, lowerEffect κ n false, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← (hmem true v0).2.2.1]
      exact (hmem true v0).2.2.2
    · rw [← (hmem false v0).2.2.1]
      exact (hmem false v0).2.2.2
    · intro j
      let v := (Fintype.equivFin (Signs κ n)).symm j
      exact ⟨(hmem true v).1, (hmem true v).2.1,
        htarget true v v0, (hmem true v).2.2.1⟩
    · intro j
      let v := (Fintype.equivFin (Signs κ n)).symm j
      exact ⟨(hmem false v).1, (hmem false v).2.1,
        htarget false v v0, (hmem false v).2.2.1⟩
    · rw [abs_sub_comm]
      exact hsep v0 v0
    · rw [uniformSignPrior_sampleLaw, uniformSignPrior_sampleLaw]
      exact htv
  · intro K hK hsub
    by_cases hne : K.Nonempty
    · obtain ⟨κ, hκK⟩ := hne
      obtain ⟨hκ, hb⟩ := hsub hκK
      exact (interaction_obstruction_concrete κ hκ hb expLaw hiid).2.2 K hK hsub
    · refine ⟨1, by norm_num, ?_⟩
      intro κ hκK
      exact (hne ⟨κ, hκK⟩).elim

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
