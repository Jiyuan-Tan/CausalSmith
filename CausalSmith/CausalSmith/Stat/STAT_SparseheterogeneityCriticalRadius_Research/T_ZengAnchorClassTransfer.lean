module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Anchor.LowerBound

/-! Centering the binary radius class inside the real-outcome known-radius
class and transferring the matching minimax rate. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped ENNReal

-- @node: AnchorPriorSupport
def AnchorPriorSupport (n : ℕ) (rho : ℝ) (hn : 3 ≤ n)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) : Prop :=
  ∀ h : Bool,
    (sharedDesignPrior n 1 rho (1 / 4096) 1 h hn (by norm_num) hrho
      (by norm_num) (by norm_num)).1
      {theta | ∃ P : ZengAnchorClass n rho,
        (centerLaw P).fullLaw = (latentToLaw n 1 rho (1 / 4096) 1
          (dualDegree n rho) theta
          (by omega)
          (by unfold dualDegree; exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by norm_num) hrho (by norm_num) (by norm_num)).fullLaw}ᶜ = 0

/-- Every latent parameter, including parameters routed through the fallback,
has an anchor representative. Hence the prior gives zero mass to the complement. -/
-- @node: anchorPriorSupport
lemma anchorPriorSupport (n : ℕ) (rho : ℝ) (hn : 3 ≤ n)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) : AnchorPriorSupport n rho hn hrho := by
  intro h
  have hfull : {theta | ∃ P : ZengAnchorClass n rho,
      (centerLaw P).fullLaw = (latentToLaw n 1 rho (1 / 4096) 1
        (dualDegree n rho) theta
        (by omega)
        (by unfold dualDegree; exact lt_of_lt_of_le (by decide) (le_max_left _ _))
        (by norm_num) hrho (by norm_num) (by norm_num)).fullLaw} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro theta
    exact latentToLaw_anchor_embedding n rho (1 / 4096) 1 (dualDegree n rho) theta hn
      (by unfold dualDegree; exact lt_of_lt_of_le (by decide) (le_max_left _ _))
      hrho (by norm_num) (by norm_num)
  rw [hfull, Set.compl_univ, measure_empty]

-- @node: prop:zeng-anchor-class-transfer
theorem zeng_anchor_class_transfer :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      -- @realizes c(universal lower constant) @realizes C(universal upper constant)
      ∀ n rho, (hn : 3 ≤ n) → (hr0 : 0 ≤ rho) → (hr2 : rho ≤ 2) →
        c * rate n rho ≤ anchorMinimaxRisk n rho ∧
        anchorMinimaxRisk n rho ≤ anchorWorstRisk n rho ∧
        anchorWorstRisk n rho ≤ C * rate n rho ∧
        (∀ P : ZengAnchorClass n rho,
          ∃ Q : KnownRadiusClass n 1 rho,
            Q.law.fullLaw = (centerLaw P).fullLaw) ∧
        (∀ Q : KnownRadiusClass n 1 rho,
          CenteredBinary Q.law →
            ∃ P : ZengAnchorClass n rho,
              (centerLaw P).fullLaw = Q.law.fullLaw) ∧
        AnchorPriorSupport n rho hn ⟨hr0, hr2⟩ := by
  obtain ⟨C₀, hC₀, hupper⟩ := anchorWorstRisk_bound
  have hremaining : ∃ c : ℝ, 0 < c ∧
      ∀ n rho, (hn : 3 ≤ n) → (hr0 : 0 ≤ rho) → (hr2 : rho ≤ 2) →
        c * rate n rho ≤ anchorMinimaxRisk n rho := by
    exact anchor_minimax_lower_bound
  obtain ⟨c, hc, hrest⟩ := hremaining
  let C := C₀ + c + 1
  have hcC : c < C := by dsimp [C]; linarith
  have hC : C₀ ≤ C := by dsimp [C]; linarith
  refine ⟨c, C, hc, hcC, ?_⟩
  intro n rho hn hr0 hr2
  have hlower := hrest n rho hn hr0 hr2
  have hu : anchorWorstRisk n rho ≤ C * rate n rho :=
    (hupper n rho hn hr0 hr2).trans
      (mul_le_mul_of_nonneg_right hC (by unfold rate; positivity))
  refine ⟨hlower, anchorMinimaxRisk_le_anchorWorstRisk n rho,
    hu, ?_, centerLaw_inverse_embedding, anchorPriorSupport n rho hn ⟨hr0, hr2⟩⟩
  intro P
  obtain ⟨Q, hQ⟩ := centerLaw_class_embedding P
  exact ⟨Q, congrArg (fun R : Law n => R.fullLaw) hQ⟩

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
