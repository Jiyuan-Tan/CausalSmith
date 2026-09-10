import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.Perturbation
import Causalean.PO.ID.Partial.Basic

set_option linter.unusedDecidableInType false

/-! Positive full-observed-law perturbation converse. -/

open Matrix
open scoped BigOperators

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]

-- @node: thm:positive-full-law-converse
/-- Given [nonemptiness of the compatible fiber, compatibility with the observed and target laws, source-law factorization, target-law factorization, the required strict positivity condition, injectivity of the reference proxy channel, existence of a comparison outcome, the positive off-diagonal proxy condition, failure of the target-span condition](hyp:hne,hMdl,hfactor,htarget,hpos,hinj,hy,hoff,hh), [failure of the target-span condition produces two positive compatible models with the same full observed laws but separated causal probabilities](goal). -/
theorem positive_full_law_converse (PO : E → W → X → Y → ℝ) (bvec : W → ℝ)
    (hne : (compatibleFiber (U := U) PO bvec).Nonempty)
    (Mdl : LatentShiftSCM E U W X Y) (hMdl : Mdl ∈ compatibleFiber PO bvec)
    (hfactor : LatentShiftFactorization Mdl)
    (htarget : TargetMechanismInvariance Mdl)
    (hpos : StrictPrimitivePositivity Mdl)
    (hinj : ProxyChannelInjectivity Mdl)
    (x : X) (y ycirc : Y) (hy : ycirc ≠ y) (wstar : W)
    (hoff : ∀ lam, (condProxyMatrix Mdl x).mulVec lam ≠ bvec)
    (h : W → ℝ) (hh : h ∈ failureSeparator (condProxyMatrix Mdl x) bvec) :
    ∃ ε : ℝ, 0 < ε ∧ -- @realizes \varepsilon(positive path radius)
      (∀ t : ℝ, |t| < ε →
        ∃ hf_nonneg : ∀ x' y' u w,
            0 ≤ outcomeNullPerturbation Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
              x y ⟨ycirc, hy⟩ wstar t x' y' u w,
          ∃ hf_col : ∀ x' u w,
            ∑ y', outcomeNullPerturbation Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
              x y ⟨ycirc, hy⟩ wstar t x' y' u w = 1,
            let Mt := perturbedModel Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
              x y ⟨ycirc, hy⟩ wstar t hf_nonneg hf_col
            Mt ∈ compatibleFiber PO bvec ∧
              interventionalProb Mt x y - interventionalProb Mdl x y =
                t * dotProduct h bvec) ∧
      Set.Ioo (interventionalProb Mdl x y - ε * |dotProduct h bvec|)
          (interventionalProb Mdl x y + ε * |dotProduct h bvec|) ⊆
        Causalean.PartialID.IdentifiedInterval
          (fun M : LatentShiftSCM E U W X Y => interventionalProb M x y)
          (fun M => M ∈ compatibleFiber PO bvec) := by
  have hM : PositiveLatentShiftClass Mdl := hMdl.1
  obtain ⟨ε, hε, hpositive⟩ := perturbation_positive_radius Mdl hM
    (condProxyMatrix Mdl x) bvec ⟨h, hh⟩ x y ⟨ycirc, hy⟩ wstar hpos
  have hslope : dotProduct h bvec ≠ 0 := hh.2
  have hall : ∀ t : ℝ, |t| < ε →
      ∃ hf_nonneg : ∀ x' y' u w,
          0 ≤ outcomeNullPerturbation Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
            x y ⟨ycirc, hy⟩ wstar t x' y' u w,
        ∃ hf_col : ∀ x' u w,
          ∑ y', outcomeNullPerturbation Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
            x y ⟨ycirc, hy⟩ wstar t x' y' u w = 1,
          let Mt := perturbedModel Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
            x y ⟨ycirc, hy⟩ wstar t hf_nonneg hf_col
          Mt ∈ compatibleFiber PO bvec ∧
            interventionalProb Mt x y - interventionalProb Mdl x y =
              t * dotProduct h bvec := by
    intro t ht
    have hf_pos := hpositive t ht
    let hf_nonneg : ∀ x' y' u w,
        0 ≤ outcomeNullPerturbation Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
          x y ⟨ycirc, hy⟩ wstar t x' y' u w :=
      fun x' y' u w => (hf_pos x' y' u w).le
    let hf_col : ∀ x' u w,
        ∑ y', outcomeNullPerturbation Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
          x y ⟨ycirc, hy⟩ wstar t x' y' u w = 1 :=
      outcomeNullPerturbation_sum Mdl hM (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
        x y ⟨ycirc, hy⟩ wstar t
    refine ⟨hf_nonneg, hf_col, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · exact ⟨by simp [LatentShiftFactorization, perturbedModel],
          by simp [TargetMechanismInvariance, perturbedModel],
          ⟨hpos.1, hpos.2.1, hpos.2.2.1, hpos.2.2.2.1, hf_pos, hpos.2.2.2.2.2⟩,
          hinj⟩
      · exact (perturbedModel_preserves_observedLaw Mdl hM bvec x ⟨h, hh⟩
          y ⟨ycirc, hy⟩ wstar t hf_nonneg hf_col).trans hMdl.2.1
      · change targetProxyVector Mdl = bvec
        exact hMdl.2.2
    · exact perturbedModel_interventionalProb_sub Mdl hM bvec x ⟨h, hh⟩
        y ⟨ycirc, hy⟩ wstar t hf_nonneg hf_col hpos hMdl.2.2
  refine ⟨ε, hε, hall, ?_⟩
  intro z hz
  let s := dotProduct h bvec
  let t := (z - interventionalProb Mdl x y) / s
  have hs : s ≠ 0 := by simpa [s] using hslope
  have hnum : |z - interventionalProb Mdl x y| < ε * |s| := by
    change interventionalProb Mdl x y - ε * |s| < z ∧
      z < interventionalProb Mdl x y + ε * |s| at hz
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have ht : |t| < ε := by
    rw [show |t| = |z - interventionalProb Mdl x y| / |s| by
      simp [t, abs_div]]
    exact (div_lt_iff₀ (abs_pos.mpr hs)).2 hnum
  obtain ⟨hf_nonneg, hf_col, hMt, hdiff⟩ := hall t ht
  have htprod : t * s = z - interventionalProb Mdl x y := by
    exact div_mul_cancel₀ _ hs
  dsimp [s] at hdiff htprod
  have heq : interventionalProb
      (perturbedModel Mdl hMdl.1 (condProxyMatrix Mdl x) bvec ⟨h, hh⟩
        x y ⟨ycirc, hy⟩ wstar t hf_nonneg hf_col) x y = z := by
    linarith
  rw [← heq]
  exact Causalean.PartialID.mem_identifiedInterval hMt

end CausalSmith.SCM.ProxyTargetspanTransport
