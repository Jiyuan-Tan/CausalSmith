module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.Normalization
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.OneCellComparison

/-! Deterministic normalization and orientation identities for the shared-design converse. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped BigOperators

/-- The signed score whose raw-mass average determines the normalized ATE. -/
def latentSignedScore (z : LatentCell) : ℝ :=
  latentIntensity z * latentSignValue z * latentScore z

/-- Common raw-mass scale of each rare cell. -/
noncomputable def rareScale (n J : ℕ) (kappa : ℝ) : ℝ :=
  kappa * (J : ℝ) / (2 * (n : ℝ))

/-- Unnormalized signed-score total over the rare cells. -/
noncomputable def rawSignedScoreTotal (n J : ℕ) (kappa : ℝ)
    (theta : Fin (n - 1) → LatentCell) : ℝ :=
  rareScale n J kappa * ∑ k, latentSignedScore (theta k)

/-- The reservoir contributes exactly one and every rare mass has the common scale. -/
lemma rawMassTotal_eq_one_add_sum (n J : ℕ) (kappa : ℝ)
    (theta : Fin (n - 1) → LatentCell) (hn : 0 < n) :
    rawMassTotal n J kappa theta =
      1 + rareScale n J kappa * ∑ k, latentIntensity (theta k) := by
  cases n with
  | zero => omega
  | succ m =>
      simp only [Nat.succ_sub_one] at theta ⊢
      rw [rawMassTotal, Fin.sum_univ_castSucc]
      simp [rawRareMass, rareScale]
      rw [Finset.mul_sum]
      ring

/-- The selected law's target is the normalized signed-score ratio. -/
lemma latentLawSpec_ateTarget_eq_ratio {n J : ℕ} {M rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell} {P : Law n} (hn : 0 < n)
    (hs : LatentLawSpec n M rho kappa gamma J theta P) :
    ateTarget P = M * rho * gamma / 4 *
      (rawSignedScoreTotal n J kappa theta / rawMassTotal n J kappa theta) := by
  rw [latentLawSpec_ateTarget_eq hs]
  cases n with
  | zero => omega
  | succ m =>
      simp only [Nat.succ_sub_one] at theta hs ⊢
      rw [Fin.sum_univ_castSucc]
      simp [rawRareMass, rawSignedScoreTotal, rareScale, latentSignedScore]
      rw [Finset.mul_sum]
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold latentSignValue
      split_ifs <;> ring

/-- Signed dual separation before orienting the two hypotheses. -/
noncomputable def dualTargetGap (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) : ℝ :=
  ∑ i, D.weights i * rationalTarget a (D.nodes i)

lemma abs_dualTargetGap (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) :
    |dualTargetGap a J D| =
      bestUniformApproxError (rationalTarget a) a 1 (3 * J) := by
  exact D.target_abs_eq

/-- Sign used to align the unsigned approximation-dual gap with the hypothesis label. -/
noncomputable def dualOrientationValue (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) : ℝ :=
  if 0 ≤ dualTargetGap a J D then 1 else -1

-- keep: certifies that orientation converts the signed dual gap to its absolute value
lemma dualOrientationValue_mul_gap (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) :
    dualOrientationValue a J D * dualTargetGap a J D = |dualTargetGap a J D| := by
  unfold dualOrientationValue
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]

/-- Relabel the two priors when the selected dual certificate has negative orientation. -/
noncomputable def orientedHypothesis (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool) : Bool :=
  if 0 ≤ dualTargetGap a J D then h else !h

/-- A ratio perturbation identity used after the two Bernstein bounds. -/
lemma ratio_sub_calibrated_center {S V ES EV gamma c H : ℝ}
    (hS : S ≠ 0) (hES : ES ≠ 0) (hEV : EV ≠ 0) (hH : H ≠ 0)
    (hgamma : gamma = 4 * c * ES / (H * EV)) :
    gamma * V / S - 4 * c / H =
      (gamma * (V - EV)) / S +
        (4 * c / H) * ((ES - S) / S) := by
  rw [hgamma]
  field_simp
  ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
