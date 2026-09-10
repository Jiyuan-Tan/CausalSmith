import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_k3_lp_certificate
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_rational_contrast_grid_certificate_sandwich

/-! Three-arm specialization of the exact rational certificate sandwich. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Filter

-- @node: thm:k3-grid-certificate-sandwich
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the three-arm specialization inherits the exact rational lower-and-upper grid certificate sandwich](goal). -/
theorem k3_grid_certificate_sandwich (n M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    ∃ (pi : GridPi 3 n) (w : GridWeight 3 n M) (u : ℚ)
      (nu : CountVec 3 n → ℚ)
      (delta : ∀ r : AllocVec 3 n, ObsVec r → ℝ),
      ExactGridPrimalDualCertificate cDaggerQ pi w u nu ∧
      IsGridBarycenter cDaggerQ pi w delta ∧
      (u : ℝ) = gridLPValueK3 n M hM ∧
      lowerCertificate cDaggerQ nu ≤ rhoNDagger n ∧
      rhoNDagger n ≤ upperCertificate cDaggerQ pi delta ∧
      upperCertificate cDaggerQ pi delta ≤ gridLPValueK3 n M hM ∧
      gridLPValueK3 n M hM ≤ lowerCertificate cDaggerQ nu + 1 / (4 * (M : ℝ) ^ 2) ∧
      (∀ (a : PositiveSequence) (Mseq : ℕ → ℕ),
        (∀ k, 0 < Mseq k) →
        Tendsto (fun k => a k / (Mseq k : ℝ) ^ 2) atTop (nhds 0) →
        Tendsto (fun k => a k * (1 / (4 * (Mseq k : ℝ) ^ 2))) atTop (nhds 0)) ∧
      (∀ (a : PositiveSequence) (Mseq : ℕ → ℕ) (lower upper : ℕ → ℝ) C,
        (∀ k, 0 < k → 0 < Mseq k ∧
          lower k ≤ rhoNDagger k ∧ rhoNDagger k ≤ upper k ∧
          upper k - lower k ≤ 1 / (4 * (Mseq k : ℝ) ^ 2)) →
        Tendsto (fun k => a k / (Mseq k : ℝ) ^ 2) atTop (nhds 0) →
        Tendsto (fun k => a k * dN 3 cDagger k) atTop (nhds C) →
        Tendsto (fun k => a k * (C0 cDagger / k - lower k)) atTop (nhds C) ∧
        Tendsto (fun k => a k * (C0 cDagger / k - upper k)) atTop (nhds C)) := by
  obtain ⟨pi, w, u, nu, delta, hcert, hbary, hu, hlow, hrho, hupp, hlp,
      _hcount, _halloc, _hobs, hscale⟩ :=
    rational_contrast_grid_certificate_sandwich 3 n M cDaggerQ hn hM
  have hC0 : C0 cDagger = 1 := by
    norm_num [C0, Lc, cDagger, ratContrastToReal, cDaggerQ, Fin.sum_univ_succ]
  have hC0q : C0 (ratContrastToReal cDaggerQ) = 1 := by
    simpa [cDagger] using hC0
  refine ⟨pi, w, u, nu, delta, hcert, hbary, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [gridLPValueK3, gridLPValue] using hu
  · simpa [rhoNDagger, cDagger] using hlow
  · simpa [rhoNDagger, cDagger] using hrho
  · simpa [gridLPValueK3, gridLPValue] using hupp
  · simpa [gridLPValueK3, gridLPValue, hC0q] using hlp
  · intro a Mseq hMseq hlim
    simpa [hC0q] using hscale.1 a Mseq hMseq hlim
  · intro a Mseq lower upper C hbounds hmesh htarget
    have hmesh4 : Tendsto (fun k => a k * (1 / (4 * (Mseq k : ℝ) ^ 2)))
        atTop (nhds 0) := by
      convert (hmesh.const_mul (1 / 4 : ℝ)) using 1 <;> ring
    have hkpos : ∀ᶠ k : ℕ in atTop, 0 < k := by
      exact eventually_atTop.2 ⟨1, fun k hk => by omega⟩
    have hlerr : Tendsto (fun k => a k * (rhoNDagger k - lower k))
        atTop (nhds 0) := by
      apply squeeze_zero' (g := fun k => a k * (1 / (4 * (Mseq k : ℝ) ^ 2)))
      · filter_upwards [hkpos] with k hk
        exact mul_nonneg (le_of_lt (a.2 k)) (sub_nonneg.mpr (hbounds k hk).2.1)
      · filter_upwards [hkpos] with k hk
        have hb := hbounds k hk
        have ha : 0 ≤ a k := le_of_lt (a.2 k)
        exact mul_le_mul_of_nonneg_left (by linarith [hb.2.1, hb.2.2.2]) ha
      · exact hmesh4
    have huerr : Tendsto (fun k => a k * (upper k - rhoNDagger k))
        atTop (nhds 0) := by
      apply squeeze_zero' (g := fun k => a k * (1 / (4 * (Mseq k : ℝ) ^ 2)))
      · filter_upwards [hkpos] with k hk
        exact mul_nonneg (le_of_lt (a.2 k)) (sub_nonneg.mpr (hbounds k hk).2.2.1)
      · filter_upwards [hkpos] with k hk
        have hb := hbounds k hk
        have ha : 0 ≤ a k := le_of_lt (a.2 k)
        exact mul_le_mul_of_nonneg_left (by linarith [hb.2.1, hb.2.2.2]) ha
      · exact hmesh4
    constructor
    · convert htarget.add hlerr using 1 <;> simp [dN, rhoNDagger]
      funext k
      ring
    · convert htarget.sub huerr using 1 <;> simp [dN, rhoNDagger]
      funext k
      ring

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
