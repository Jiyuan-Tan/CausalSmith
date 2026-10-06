module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairPrognosisEnvelope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Fair prognosis oscillation at the calibrated amplitude scale

The logit is Lipschitz on the fixed interior risk interval. Quadratic root
centering and the bounded sign field give an exponent-uniform oscillation bound
for the actual random law and deterministic comparator.
-/
public section
set_option linter.style.whitespace false
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The logarithm has Lipschitz constant three on the interior interval used
for a risk and its complement. [the documented result](goal) Under [the stated assumptions](hyp:hp,hq). -/
-- @node: calibrated_log_difference_le
lemma calibrated_log_difference_le (p q : ℝ)
    (hp : p ∈ Set.Icc (1/3 : ℝ) 1) (hq : q ∈ Set.Icc (1/3 : ℝ) 1) :
    |Real.log p - Real.log q| ≤ 3 * |p-q| := by
  have hd : ∀ x ∈ Set.Icc (1/3 : ℝ) 1,
      HasDerivWithinAt Real.log x⁻¹ (Set.Icc (1/3 : ℝ) 1) x := by
    intro x hx
    exact (Real.hasDerivAt_log (by linarith [hx.1])).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Icc (1/3 : ℝ) 1, ‖x⁻¹‖ ≤ (3 : ℝ) := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    rw [← one_div]
    apply (div_le_iff₀ hxpos).mpr
    linarith [hx.1]
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (1/3 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hq hp

/-- Positive floors for a risk and its complement bound logit differences
by six times the risk difference. [the documented result](goal) Under [the stated assumptions](hyp:hp,hq). -/
-- @node: calibrated_logit_difference_le
lemma calibrated_logit_difference_le (p q : ℝ)
    (hp : p ∈ Set.Icc (1/3 : ℝ) (2/3))
    (hq : q ∈ Set.Icc (1/3 : ℝ) (2/3)) :
    |logit p-logit q| ≤ 6*|p-q| := by
  have hp0 : p ≠ 0 := by linarith [hp.1]
  have hq0 : q ≠ 0 := by linarith [hq.1]
  have hpc : 1-p ≠ 0 := by linarith [hp.2]
  have hqc : 1-q ≠ 0 := by linarith [hq.2]
  have h1 := calibrated_log_difference_le p q
    ⟨hp.1, by linarith [hp.2]⟩ ⟨hq.1, by linarith [hq.2]⟩
  have h2 := calibrated_log_difference_le (1-p) (1-q)
    ⟨by linarith [hp.2], by linarith [hp.1]⟩
    ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hc : |(1-p)-(1-q)| = |p-q| := by
    rw [show (1-p)-(1-q) = -(p-q) by ring, abs_neg]
  rw [hc] at h2
  simp only [logit, Real.log_div hp0 hpc, Real.log_div hq0 hqc]
  calc
    _ = |(Real.log p-Real.log q)-(Real.log (1-p)-Real.log (1-q))| := by congr 1; ring
    _ ≤ |Real.log p-Real.log q| + |Real.log (1-p)-Real.log (1-q)| := abs_sub _ _
    _ ≤ 6*|p-q| := by linarith

/-- The actual fair native control logit stays near the fixed center with
linear sign-field displacement and quadratic root displacement. [the documented result](goal) Under [the stated assumptions](hyp:hδ,hp,hB,hv,x). -/
-- @node: fairCells_prognosis_displacement
lemma fairCells_prognosis_displacement (b : Bool) (k : ℕ)
    (σ : Fin (k+1) → Bool) (t δ B : ℝ) (hδ : |δ| ≤ 1/100)
    (hp : ∀ x : Covariate, |fairRoot t δ (cellCoord k x)-2/5| ≤ 1/100)
    (hB : ∀ x : Covariate, |fairRoot t δ (cellCoord k x)-2/5| ≤ B*δ^2)
    (hv : ValidCells (fairCells b k σ t δ)) (x : Covariate) :
    |prognosisLogit (totalCellLaw (fairCells b k σ t δ)) x-logit (2/5)| ≤
      6*(B*δ^2+2*|δ|) := by
  change |logit (armRisk (totalCellLaw (fairCells b k σ t δ)) false x)-logit (2/5)| ≤ _
  rw [fairCells_armRisk_control b k σ t δ hv x]
  have hi := fair_control_risk_bounds_of_centering b k σ t δ x hδ (hp x)
  have hl := calibrated_logit_difference_le _ (2/5) hi (by norm_num)
  have hs : |δ*signFieldZ k σ x| ≤ 2*|δ| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (signFieldZ_abs_le_two k σ x) (abs_nonneg δ)]
  have hr : |(if b then fairRoot t δ (cellCoord k x)+δ*signFieldZ k σ x
      else fairRoot t δ (cellCoord k x))-2/5| ≤ B*δ^2+2*|δ| := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · linarith [hB x, abs_nonneg δ]
    · calc
        _ = |(fairRoot t δ (cellCoord k x)-2/5)+δ*signFieldZ k σ x| := by congr 1; ring
        _ ≤ |fairRoot t δ (cellCoord k x)-2/5|+|δ*signFieldZ k σ x| := abs_add_le _ _
        _ ≤ _ := add_le_add (hB x) hs
  exact hl.trans (mul_le_mul_of_nonneg_left hr (by norm_num))

/-- [Two displacements from the same fixed center give the actual fair
prognosis oscillation; fallback laws have constant zero prognosis. [the documented result](goal) Under [the stated assumptions](hyp:hBnonneg,hδ,hp,hB,x). -/
-- @node: fairCells_prognosis_oscillation_of_centering
lemma fairCells_prognosis_oscillation_of_centering (b : Bool) (k : ℕ)
    (σ : Fin (k+1) → Bool) (t δ B : ℝ) (hBnonneg : 0 ≤ B)
    (hδ : |δ| ≤ 1/100)
    (hp : ∀ x : Covariate, |fairRoot t δ (cellCoord k x)-2/5| ≤ 1/100)
    (hB : ∀ x : Covariate, |fairRoot t δ (cellCoord k x)-2/5| ≤ B*δ^2)
    (x z : Covariate) :
    |prognosisLogit (totalCellLaw (fairCells b k σ t δ)) x-
      prognosisLogit (totalCellLaw (fairCells b k σ t δ)) z| ≤
      12*B*δ^2+24*|δ| := by
  classical
  by_cases hv : ValidCells (fairCells b k σ t δ)
  · have hx := fairCells_prognosis_displacement b k σ t δ B hδ hp hB hv x
    have hz := fairCells_prognosis_displacement b k σ t δ B hδ hp hB hv z
    have ht := abs_sub_le
      (prognosisLogit (totalCellLaw (fairCells b k σ t δ)) x)
      (logit (2/5)) (prognosisLogit (totalCellLaw (fairCells b k σ t δ)) z)
    rw [abs_sub_comm (logit (2/5))] at ht
    linarith
  · have hz : ∀ w, prognosisLogit (totalCellLaw (fairCells b k σ t δ)) w = 0 := by
      intro w
      norm_num [prognosisLogit, armRisk, totalCellLaw, hv, lawFromCells, logit]
    rw [hz x, hz z, sub_self, abs_zero]
    positivity

/-- One absolute positive amplitude radius gives the prescribed fair
prognosis oscillation at every nonnegative exponent and every rank. [the documented result](goal) -/
-- @node: fairCells_uniform_prognosis_oscillation
lemma fairCells_uniform_prognosis_oscillation : ∃ r : ℝ, 0 < r ∧ r ≤ 1/100 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ β : ℝ, 0 ≤ β → ∀ k : ℕ, 1 ≤ k →
      ∀ σ : Fin (k+1) → Bool, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → ∀ b,
        ∀ x z, |prognosisLogit (totalCellLaw (fairCells b k σ t (ε*(k : ℝ)^(-β)))) x-
          prognosisLogit (totalCellLaw (fairCells b k σ t (ε*(k : ℝ)^(-β)))) z| ≤
          2*(k : ℝ)^(-β) := by
  obtain ⟨a, B, ha, hB, _, _, _, _, hf⟩ := exact_calibrations
  let r := min a (min (1/100) (1/(100*(B+1))))
  have hr : 0 < r := lt_min ha (lt_min (by norm_num) (by positivity))
  have hra : r ≤ a := min_le_left _ _
  have hrs : r ≤ 1/100 := (min_le_right _ _).trans (min_le_left _ _)
  have hrB : r ≤ 1/(100*(B+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hBr : B*r ≤ 1/100 := by
    have hh := (le_div_iff₀ (show 0 < 100*(B+1) by positivity)).mp hrB
    nlinarith
  refine ⟨r, hr, hrs, ?_⟩
  intro ε hε hεr β hβ k hk σ t ht b x z
  let δ := ε*(k : ℝ)^(-β)
  have hd : |δ| ≤ ε := calibrated_amplitude_abs_le ε β hε.le hβ k hk
  have hdr : |δ| ≤ r := hd.trans hεr
  have hb : ∀ w : Covariate, |fairRoot t δ (cellCoord k w)-2/5| ≤ B*δ^2 := by
    intro w
    have hh := (hf t δ (cellCoord k w) ht (hdr.trans hra)
      (cellCoord_mem_unit k hk w)).2.2.2.2.2.2.2.2.1
    linarith [abs_nonneg (deriv (fairRoot t δ) (cellCoord k w))]
  have hp : ∀ w : Covariate, |fairRoot t δ (cellCoord k w)-2/5| ≤ 1/100 := by
    intro w
    have hs : δ^2 ≤ r^2 := by nlinarith [sq_abs δ, abs_nonneg δ]
    have hh := mul_le_mul_of_nonneg_left hs hB.le
    nlinarith [hb w]
  have ho := fairCells_prognosis_oscillation_of_centering b k σ t δ B hB.le
    (hdr.trans hrs) hp hb x z
  have hds : δ^2 ≤ r*|δ| := by nlinarith [sq_abs δ, abs_nonneg δ]
  have hsmall : 12*B*r+24 ≤ 26 := by linarith
  have hosc : 12*B*δ^2+24*|δ| ≤ 26*|δ| := by
    nlinarith [mul_le_mul_of_nonneg_left hds hB.le]
  have heps : 26*ε ≤ 2 := by linarith [hεr.trans hrs]
  calc
    _ ≤ 12*B*δ^2+24*|δ| := ho
    _ ≤ 26*|δ| := hosc
    _ ≤ 2*(k : ℝ)^(-β) := by
      have hδpos : 0 ≤ δ := by dsimp [δ]; positivity
      have hrate : |δ| = ε*(k : ℝ)^(-β) := abs_of_nonneg hδpos
      have hh := mul_le_mul_of_nonneg_right heps (Real.rpow_nonneg (Nat.cast_nonneg k) (-β))
      rw [hrate]
      nlinarith [hh]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
