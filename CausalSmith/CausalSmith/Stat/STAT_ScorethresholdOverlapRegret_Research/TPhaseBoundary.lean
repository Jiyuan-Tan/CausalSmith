module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.TMatchedFrontier
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.JointTail

/-! # Score-threshold overlap regret — phase equality and branch assignment

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- Local risk exponent, expressed through the information denominator. -/
noncomputable def rLoc (α γ θ : ℝ) : ℝ := (α+1)/DExp α γ θ
/-- High-effect risk exponent. -/
noncomputable def rHi (θ : ℝ) : ℝ := θ/(θ+1)

-- @node: rExp_eq_min_branches
/-- The risk exponent is the minimum of the two branch exponents. -/
lemma rExp_eq_min_branches (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    rExp α γ θ = min (rLoc α γ θ) (rHi θ) := by
  have hd : 0 < α + θ * γ := by positivity
  have hb : 0 ≤ betaExp α γ θ := by
    unfold betaExp
    positivity
  have hs : 0 < sLoc α γ θ := by
    unfold sLoc
    positivity
  have hlocal : sLoc α γ θ / (sLoc α γ θ + 1) = rLoc α γ θ := by
    unfold sLoc rLoc DExp
    dsimp [betaExp]
    field_simp
    ring
  have hhigh : sHi θ / (sHi θ + 1) = rHi θ := by rfl
  rcases le_total (sLoc α γ θ) (sHi θ) with h | h
  · have hr : rLoc α γ θ ≤ rHi θ := by
      rw [← hlocal, ← hhigh]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith [h])
    simp [rExp, sExp, min_eq_left h, hlocal, min_eq_left hr]
  · have hr : rHi θ ≤ rLoc α γ θ := by
      rw [← hlocal, ← hhigh]
      exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith [h])
    simp [rExp, sExp, min_eq_right h, hhigh, min_eq_right hr]

-- @node: phase_eq_iff
/-- Equality of the two branch exponents is the phase equation. -/
lemma phase_eq_iff (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    (rLoc α γ θ = rHi θ ↔ θ*(1+α*γ/(α+θ*γ)) = α+1) := by
  have hd : 0 < α + θ*γ := by positivity
  have hb : 0 ≤ α*γ/(α+θ*γ) := by positivity
  have hD : 0 < α+2+α*γ/(α+θ*γ) := by positivity
  have ht : 0 < θ+1 := by positivity
  unfold rLoc rHi DExp betaExp
  rw [div_eq_div_iff (ne_of_gt hD) (ne_of_gt ht)]
  constructor <;> intro h <;> nlinarith [h]

-- @node: phase_hi_le_loc_iff
/-- The sign of the exponent difference after clearing positive denominators. -/
lemma phase_hi_le_loc_iff (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    (rHi θ ≤ rLoc α γ θ ↔
      θ*(θ-1)*γ ≤ α*(α+1-θ)) := by
  have hd : 0 < α + θ*γ := by positivity
  have hb : 0 ≤ α*γ/(α+θ*γ) := by positivity
  have hD : 0 < α+2+α*γ/(α+θ*γ) := by positivity
  have ht : 0 < θ+1 := by positivity
  have hscale : θ*(α*γ/(α+θ*γ)) = (θ*α*γ)/(α+θ*γ) := by ring
  have hcross :
      (θ*α*γ)/(α+θ*γ) ≤ α+1-θ ↔
        θ*(θ-1)*γ ≤ α*(α+1-θ) := by
    rw [div_le_iff₀ hd]
    constructor <;> intro h <;> nlinarith [h]
  unfold rHi rLoc DExp betaExp
  rw [div_le_div_iff₀ ht hD]
  rw [← hscale] at hcross
  constructor
  · intro h
    apply hcross.mp
    nlinarith [h]
  · intro h
    have := hcross.mpr h
    nlinarith

-- @node: phase_loc_le_hi_iff
/-- The reverse branch comparison uses the reverse sign. -/
lemma phase_loc_le_hi_iff (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hθ : 0 < θ) :
    (rLoc α γ θ ≤ rHi θ ↔
      α*(α+1-θ) ≤ θ*(θ-1)*γ) := by
  have hd : 0 < α + θ*γ := by positivity
  have hb : 0 ≤ α*γ/(α+θ*γ) := by positivity
  have hD : 0 < α+2+α*γ/(α+θ*γ) := by positivity
  have ht : 0 < θ+1 := by positivity
  have hscale : θ*(α*γ/(α+θ*γ)) = (θ*α*γ)/(α+θ*γ) := by ring
  have hcross :
      α+1-θ ≤ (θ*α*γ)/(α+θ*γ) ↔
        α*(α+1-θ) ≤ θ*(θ-1)*γ := by
    rw [le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith [h]
  unfold rLoc rHi DExp betaExp
  rw [div_le_div_iff₀ hD ht]
  rw [← hscale] at hcross
  constructor
  · intro h
    apply hcross.mp
    nlinarith [h]
  · intro h
    have := hcross.mpr h
    nlinarith

-- @node: phase_zero_wedge_gamma
/-- A positive finite crossing lies in the open wedge and has the stated location. -/
lemma phase_zero_wedge_gamma (α γ θ : ℝ) (hα : 0 < α) (hγ : 0 < γ)
    (hθ : 0 < θ) (heq : rLoc α γ θ = rHi θ) :
    1 < θ ∧ θ < α+1 ∧ γ = gammaC α θ := by
  have hpoly : θ*(θ-1)*γ = α*(α+1-θ) := by
    apply le_antisymm
    · exact (phase_hi_le_loc_iff α γ θ hα hγ hθ).mp (le_of_eq heq.symm)
    · exact (phase_loc_le_hi_iff α γ θ hα hγ hθ).mp (le_of_eq heq)
  have hθ1 : 1 < θ := by
    by_contra h
    have hθle : θ ≤ 1 := le_of_not_gt h
    have hnon : θ*(θ-1)*γ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hθ) (by linarith))
        (le_of_lt hγ)
    have hpos : 0 < α*(α+1-θ) := mul_pos hα (by linarith)
    linarith
  have hθupper : θ < α+1 := by
    have hpos : 0 < θ*(θ-1)*γ := by positivity
    nlinarith [hpoly]
  have hden : θ*(θ-1) ≠ 0 := ne_of_gt (by positivity)
  refine ⟨hθ1, hθupper, ?_⟩
  unfold gammaC
  apply (eq_div_iff hden).2
  nlinarith [hpoly]

-- @node: prop:phase-boundary
/-- Exact equality surface, its finite-positive wedge, branch assignment, and slice. -/
theorem phase_boundary :
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → 0 < θ →
      (rLoc α γ θ = rHi θ ↔
        θ*(1+α*γ/(α+θ*γ)) = α+1)) ∧
    (∀ α θ : ℝ, 0 < α → 0 < θ →
      ((∃ γ : ℝ, 0 < γ ∧ rLoc α γ θ = rHi θ) ↔
        1 < θ ∧ θ < α+1)) ∧
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → 0 < θ →
      rLoc α γ θ = rHi θ → γ = gammaC α θ) ∧
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → 0 < θ → θ ≤ 1 →
      rExp α γ θ = rHi θ) ∧
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → 1 < θ → θ < α+1 →
      γ < gammaC α θ → rExp α γ θ = rHi θ) ∧
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → 1 < θ → θ < α+1 →
      gammaC α θ < γ → rExp α γ θ = rLoc α γ θ) ∧
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → α+1 ≤ θ →
      rExp α γ θ = rLoc α γ θ) ∧
    (∀ α γ : ℝ, 0 < α → 0 < γ →
      (rLoc α γ (1/γ) = rHi (1/γ) ↔
        γ = (α+1)/(α^2+α+1))) ∧
    (∀ α γ θ : ℝ, 0 < α → 0 < γ → 0 < θ →
      rLoc α γ θ = rHi θ →
      ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
        ∀ n ≥ N,
          selectorWorstRisk α γ θ n ≤ C*(n:ℝ)^(-rExp α γ θ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α γ θ hα hγ hθ
    exact phase_eq_iff α γ θ hα hγ hθ
  · intro α θ hα hθ
    constructor
    · rintro ⟨γ, hγ, heq⟩
      obtain ⟨hθ1, hθupper, _⟩ := phase_zero_wedge_gamma α γ θ hα hγ hθ heq
      exact ⟨hθ1, hθupper⟩
    · rintro ⟨hθ1, hθupper⟩
      let γ := gammaC α θ
      have hγ : 0 < γ := by dsimp [γ, gammaC]; positivity
      have hpoly : θ*(θ-1)*γ = α*(α+1-θ) := by
        dsimp [γ, gammaC]
        field_simp [ne_of_gt hθ, ne_of_gt (sub_pos.mpr hθ1)]
      refine ⟨γ, hγ, ?_⟩
      apply le_antisymm
      · exact (phase_loc_le_hi_iff α γ θ hα hγ hθ).2 (le_of_eq hpoly.symm)
      · exact (phase_hi_le_loc_iff α γ θ hα hγ hθ).2 (le_of_eq hpoly)
  · intro α γ θ hα hγ hθ heq
    exact (phase_zero_wedge_gamma α γ θ hα hγ hθ heq).2.2
  · intro α γ θ hα hγ hθ hθ1
    rw [rExp_eq_min_branches α γ θ hα hγ hθ]
    have hnon : θ*(θ-1)*γ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hθ) (by linarith))
        (le_of_lt hγ)
    have hpos : 0 < α*(α+1-θ) := mul_pos hα (by linarith)
    exact min_eq_right ((phase_hi_le_loc_iff α γ θ hα hγ hθ).2 (by linarith))
  · intro α γ θ hα hγ hθ1 hθupper hγbelow
    have hθ : 0 < θ := by linarith
    rw [rExp_eq_min_branches α γ θ hα hγ hθ]
    have hden : 0 < θ*(θ-1) := by positivity
    have hpoly : θ*(θ-1)*γ < α*(α+1-θ) := by
      unfold gammaC at hγbelow
      simpa only [mul_comm, mul_left_comm, mul_assoc] using (lt_div_iff₀ hden).mp hγbelow
    exact min_eq_right ((phase_hi_le_loc_iff α γ θ hα hγ hθ).2 (le_of_lt hpoly))
  · intro α γ θ hα hγ hθ1 hθupper hγabove
    have hθ : 0 < θ := by linarith
    rw [rExp_eq_min_branches α γ θ hα hγ hθ]
    have hden : 0 < θ*(θ-1) := by positivity
    have hpoly : α*(α+1-θ) < θ*(θ-1)*γ := by
      unfold gammaC at hγabove
      simpa only [mul_comm, mul_left_comm, mul_assoc] using (div_lt_iff₀ hden).mp hγabove
    exact min_eq_left ((phase_loc_le_hi_iff α γ θ hα hγ hθ).2 (le_of_lt hpoly))
  · intro α γ θ hα hγ hθlarge
    have hθ : 0 < θ := by linarith
    have hθ1 : 1 < θ := by linarith
    rw [rExp_eq_min_branches α γ θ hα hγ hθ]
    have hpos : 0 < θ*(θ-1)*γ := by positivity
    have hnon : α*(α+1-θ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hα) (by linarith)
    exact min_eq_left ((phase_loc_le_hi_iff α γ θ hα hγ hθ).2 (by linarith))
  · intro α γ hα hγ
    have hθ : 0 < (1/γ:ℝ) := by positivity
    rw [phase_eq_iff α γ (1/γ) hα hγ hθ]
    have hγ0 : γ ≠ 0 := ne_of_gt hγ
    have hα1 : α+1 ≠ 0 := ne_of_gt (by linarith)
    constructor
    · intro h
      apply (eq_div_iff (by positivity : α^2+α+1 ≠ 0)).2
      field_simp [hγ0, hα1] at h
      nlinarith [h]
    · intro h
      have hh := (eq_div_iff (by positivity : α^2+α+1 ≠ 0)).mp h
      field_simp [hγ0, hα1]
      nlinarith [hh]
  · intro α γ θ hα hγ hθ _
    obtain ⟨C, N, hC, hbound⟩ := upper_bound α γ θ hα hγ hθ
    refine ⟨C, N, hC, ?_⟩
    intro n hn
    unfold selectorWorstRisk
    classical
    by_cases hne : Nonempty {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2}
    · letI := hne
      apply ciSup_le
      intro Pe
      exact hbound n hn Pe.1.1 Pe.1.2 Pe.2
    · haveI : IsEmpty {Pe : RowLaw × (ℝ → ℝ) // LawClass α γ θ n Pe.1 Pe.2} :=
        not_nonempty_iff.mp hne
      simp
      positivity

end CausalSmith.Stat.ScorethresholdOverlapRegret
