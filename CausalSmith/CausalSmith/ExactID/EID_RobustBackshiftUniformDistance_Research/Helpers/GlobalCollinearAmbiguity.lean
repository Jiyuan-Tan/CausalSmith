import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.SharpThreshold
import Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity.Main

/-!
# Globally admissible collinear ambiguity

Bridges the reusable two-coordinate deformation to the paper's global cycle-product
normalization.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open scoped Matrix Topology
open Filter Set Metric
open Causalean.Discovery.LinearDisentanglement.CollinearAmbiguity

noncomputable section

-- @node: continuousAt_deformedDiagonalizer
/-- The normalized two-row deformation converges to its reference diagonalizer at zero. [This is the asserted conclusion](goal). -/
lemma continuousAt_deformedDiagonalizer {p : ℕ} (B : RealMatrix p)
    (i j : Fin p) (u v : ℝ) :
    ContinuousAt (fun t : ℝ ↦ deformedDiagonalizer B i j u v t) 0 := by
  have hR : ContinuousAt (fun t : ℝ ↦ pairRowNormalizer B i j u v t) 0 := by
    apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro l
    by_cases hkl : k = l
    · subst l
      simp only [pairRowNormalizer, Matrix.diagonal_apply, if_pos]
      by_cases hki : k = i
      · simp [hki, firstNormalizationDenom]
        fun_prop (disch := norm_num)
      · by_cases hkj : k = j
        · have hji : j ≠ i := by
            intro h
            exact hki (hkj.trans h)
          simp [hkj, hji, secondNormalizationDenom]
          fun_prop (disch := norm_num)
        · simpa [hki, hkj] using
            (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) 0)
    · simpa [pairRowNormalizer, hkl] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0)
  have hS : ContinuousAt (fun t : ℝ ↦ pairShear i j u v t) 0 := by
    apply continuousAt_pi.mpr
    intro k
    apply continuousAt_pi.mpr
    intro l
    simp only [pairShear, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  unfold deformedDiagonalizer normalizedPairDeformation
  exact (hR.mul hS).mul continuousAt_const

-- @node: exists_deformedDiagonalizer_cycleProduct_radius
/-- Strict global cycle-product admissibility persists under a sufficiently small normalized
two-row deformation. [Under the stated hypotheses](hyp:hB) [this conclusion](goal) applies. -/
lemma exists_deformedDiagonalizer_cycleProduct_radius {p : ℕ} (B : RealMatrix p)
    (hB : cycleProduct (1 - B) < 1) (i j : Fin p) (u v : ℝ) :
    ∃ r > 0, ∀ t : ℝ, |t| < r →
      cycleProduct (1 - deformedDiagonalizer B i j u v t) < 1 := by
  have hc : ContinuousAt
      (fun t : ℝ ↦ cycleProduct (1 - deformedDiagonalizer B i j u v t)) 0 := by
    apply continuous_cycleProduct.continuousAt.comp
    exact continuousAt_const.sub (continuousAt_deformedDiagonalizer B i j u v)
  have heventually : ∀ᶠ t in nhds 0,
      cycleProduct (1 - deformedDiagonalizer B i j u v t) < 1 := by
    apply hc.eventually_lt_const
    simpa using hB
  rcases Metric.mem_nhds_iff.mp heventually with ⟨r, hr, hball⟩
  refine ⟨r, hr, fun t ht ↦ hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht

-- @node: pairCycleAdmissible_of_cycleProduct_lt_one
/-- The global strict cycle-product bound excludes equality on every selected two-cycle. [Under the stated hypotheses](hyp:hij,hB) [this conclusion](goal) applies. -/
lemma pairCycleAdmissible_of_cycleProduct_lt_one {p : ℕ} (B : RealMatrix p)
    {i j : Fin p} (hij : i ≠ j) (hB : cycleProduct (1 - B) < 1) :
    PairCycleAdmissible B i j := by
  intro heq
  let σ : Equiv.Perm (Fin p) := Equiv.swap i j
  have hσcyc : σ.IsCycle := Equiv.Perm.isCycle_swap hij
  have hσsupport : σ.support = {i, j} := Equiv.Perm.support_swap hij
  have hweight : simpleCycleWeight (1 - B) σ = 1 := by
    simp only [simpleCycleWeight, hσcyc, true_and, hσsupport, Finset.card_pair hij,
      le_refl, if_pos, Finset.prod_insert, Finset.mem_singleton, hij, not_false_eq_true,
      Finset.prod_singleton, Matrix.sub_apply, Matrix.one_apply]
    simp only [σ, Equiv.swap_apply_left, Equiv.swap_apply_right]
    simp only [if_neg hij, if_neg hij.symm, zero_sub, abs_neg]
    rw [← abs_mul, heq, abs_one]
  have hle : simpleCycleWeight (1 - B) σ ≤ cycleProduct (1 - B) := by
    unfold cycleProduct
    rw [Finset.le_fold_max]
    exact Or.inr ⟨σ, Finset.mem_univ σ, le_rfl⟩
  rw [hweight] at hle
  linarith

-- @node: affineLineCertificate_of_collinearPairs
/-- A nonempty finite cloud satisfying the affine-minor collinearity predicate has an
explicit affine-line certificate on its subtype of indices. -/
noncomputable def affineLineCertificate_of_collinearPairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (s : ι → Fin p → ℝ) (k l : Fin p) (S : Finset ι)
    (hS : S.Nonempty) (hcol : CollinearPairs s k l S) :
    AffineLineCertificate (fun e : {x // x ∈ S} ↦ s e.1) k l := by
  let e0 : {x // x ∈ S} := ⟨hS.choose, hS.choose_spec⟩
  by_cases hvary : ∃ e : {x // x ∈ S}, s e.1 l ≠ s e0.1 l
  · choose e1 he1 using hvary
    let u := s e1.1 l - s e0.1 l
    let v := -(s e1.1 k - s e0.1 k)
    let d := u * s e0.1 k + v * s e0.1 l
    refine ⟨u, v, d, Or.inl (sub_ne_zero.mpr he1), ?_⟩
    intro e
    have hminor := hcol e0.1 e0.2 e1.1 e1.2 e.1 e.2
    dsimp [u, v, d]
    unfold affineMinor at hminor
    linarith
  · push_neg at hvary
    refine ⟨0, 1, s e0.1 l, Or.inr one_ne_zero, ?_⟩
    intro e
    simpa using hvary e

-- @node: exists_globally_admissible_collinear_ambiguity
/-- A collinear shift pair yields a distinct covariance representation that remains in the
paper's full BACKSHIFT admissible set. [Under the stated hypotheses](hyp:hij,hB,hΩ,hs) [this conclusion](goal) applies. -/
theorem exists_globally_admissible_collinear_ambiguity
    {p : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (B Ω : RealMatrix p) (s : E → Fin p → ℝ) {i j : Fin p}
    (hij : i ≠ j) (hB : B ∈ admissibleSet p) (hΩ : Ω.PosDef)
    (hs : ∀ e k, 0 ≤ s e k) (cert : AffineLineCertificate s i j) :
    ∃ (B' Ω' : RealMatrix p) (s' : E → Fin p → ℝ),
      B' ∈ admissibleSet p ∧ B' ≠ B ∧ Ω'.PosDef ∧
      (∀ e k, 0 ≤ s' e k) ∧
      (∀ e, (representedCovariance B Ω (s e)).PosDef) ∧
      ∀ e, representedCovariance B' Ω' (s' e) =
        representedCovariance B Ω (s e) := by
  rcases exists_deformedDiagonalizer_cycleProduct_radius B hB.2.2 i j cert.u cert.v with
    ⟨r, hr, hglobal⟩
  have hpair : PairCycleAdmissible B i j :=
    pairCycleAdmissible_of_cycleProduct_lt_one B hij hB.2.2
  rcases exists_collinear_simultaneous_congruence_ambiguity B Ω s hij hB.2.1 hB.1
      hpair hΩ hs cert hr with
    ⟨t, B', Ω', s', _ht0, htr, hB'eq, _hΩ'eq, _hs'eq,
      hdiag, hunit, _hpair', hne, _hsymm, hpos, hs', hcovpos, hcov⟩
  have hcp : cycleProduct (1 - B') < 1 := by
    rw [hB'eq]
    exact hglobal t htr
  exact ⟨B', Ω', s', ⟨hunit, hdiag, hcp⟩, hne, hpos, hs', hcovpos, hcov⟩

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance
