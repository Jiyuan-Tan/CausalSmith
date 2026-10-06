module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.PoissonReciprocal

/-! Scalar rate algebra behind the heavy-correction noise bound (40). -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

/-- One cross-arm term produced by expanding the guarded heavy-count kernel. -/
lemma poisson_cross_inverse_rate_le {a b s : ℝ}
    (hs : 0 ≤ s) (ha : s / 4 ≤ a) (hb : b ≤ 3 * s / 4)
    (hb0 : 0 ≤ b) :
    (b ^ 2 + b) * min a (2 / a) ≤ 12 * s := by
  by_cases hs0 : s = 0
  · subst s
    have hbz : b = 0 := by nlinarith
    simp [hbz]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hapos : 0 < a := by nlinarith
  have hratio : b / a ≤ 3 := by
    apply (div_le_iff₀ hapos).mpr
    nlinarith
  by_cases hsone : s ≤ 1
  · have hb1 : b ≤ 1 := by nlinarith
    by_cases ha1 : a ≤ 1
    · have hmin := min_le_left a (2 / a)
      have hnonneg : 0 ≤ b ^ 2 + b := by positivity
      calc
        _ ≤ (b ^ 2 + b) * a := mul_le_mul_of_nonneg_left hmin hnonneg
        _ ≤ 2 * s := by
          have hba : b * a ≤ b :=
            mul_le_of_le_one_right hb0 ha1
          have hbba : b ^ 2 * a ≤ b * a := by
            nlinarith [mul_nonneg (mul_nonneg hb0 (sub_nonneg.mpr hb1)) hapos.le]
          nlinarith
        _ ≤ 12 * s := by nlinarith
    · have ha1' : 1 < a := lt_of_not_ge ha1
      have hratioB : b / a ≤ b := by
        apply (div_le_iff₀ hapos).mpr
        nlinarith
      have hmin := min_le_right a (2 / a)
      have hnonneg : 0 ≤ b ^ 2 + b := by positivity
      calc
        _ ≤ (b ^ 2 + b) * (2 / a) :=
          mul_le_mul_of_nonneg_left hmin hnonneg
        _ = 2 * b * (b / a) + 2 * (b / a) := by field_simp
        _ ≤ 2 * b ^ 2 + 2 * b := by
          nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hratioB)]
        _ ≤ 4 * s := by nlinarith [sq_nonneg (b - 1)]
        _ ≤ 12 * s := by nlinarith
  · have hs1 : 1 < s := lt_of_not_ge hsone
    have hmin := min_le_right a (2 / a)
    have hnonneg : 0 ≤ b ^ 2 + b := by positivity
    calc
      _ ≤ (b ^ 2 + b) * (2 / a) :=
        mul_le_mul_of_nonneg_left hmin hnonneg
      _ = 2 * b * (b / a) + 2 * (b / a) := by field_simp
      _ ≤ 6 * b + 6 := by nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hratio)]
      _ ≤ 12 * s := by nlinarith

/-- Rate form of (40): after exact product-Poisson factorization, the expanded
count kernel is at most a universal multiple of the total mean. -/
lemma heavy_noise_rate_envelope {a b s : ℝ}
    (hs : 0 ≤ s) (hsum : a + b = s)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (haL : s / 4 ≤ a) (hbL : s / 4 ≤ b)
    (haU : a ≤ 3 * s / 4) (hbU : b ≤ 3 * s / 4) :
    3 * (a + b) +
        (b ^ 2 + b) * min a (2 / a) +
        (a ^ 2 + a) * min b (2 / b) ≤
      27 * s := by
  have hba := poisson_cross_inverse_rate_le hs haL hbU hb0
  have hab := poisson_cross_inverse_rate_le hs hbL haU ha0
  rw [hsum]
  linarith

/-- Equation (40) after the exact Poisson product-moment calculation, specialized
to the two audit arm rates. -/
lemma heavy_noise_arm_rate_envelope {n : ℕ} (P : Law n) (k : Fin n)
    (hn : 0 < n) (hoverlap : FixedOverlap P) :
    let a := blockMean n * armMass P false k
    let b := blockMean n * armMass P true k
    let s := blockMean n * P.cellMass k
    3 * (a + b) + (b ^ 2 + b) * min a (2 / a) +
        (a ^ 2 + a) * min b (2 / b) ≤ 27 * s := by
  dsimp only
  have hm : 0 < blockMean n := blockMean_pos n hn
  have hp0 := (P.cellMass_range k).1
  have hpi := (P.propensity_range k)
  have ha0 : 0 ≤ blockMean n * armMass P false k := by
    simp only [armMass, Bool.false_eq_true, ↓reduceIte]
    exact mul_nonneg hm.le (mul_nonneg hp0 (sub_nonneg.mpr hpi.2))
  have hb0 : 0 ≤ blockMean n * armMass P true k := by
    simp only [armMass, ↓reduceIte]
    exact mul_nonneg hm.le (mul_nonneg hp0 hpi.1)
  have hsum : blockMean n * armMass P false k +
      blockMean n * armMass P true k = blockMean n * P.cellMass k := by
    simp only [armMass, Bool.false_eq_true, ↓reduceIte]
    ring
  by_cases hp : P.cellMass k = 0
  · simp [armMass, hp]
  · have hp' : 0 < P.cellMass k := lt_of_le_of_ne hp0 (Ne.symm hp)
    obtain ⟨hpiL, hpiU⟩ := hoverlap k hp'
    have haL : blockMean n * P.cellMass k / 4 ≤
        blockMean n * armMass P false k := by
      simp only [armMass, Bool.false_eq_true, ↓reduceIte]
      nlinarith
    have hbL : blockMean n * P.cellMass k / 4 ≤
        blockMean n * armMass P true k := by
      simp only [armMass, ↓reduceIte]
      nlinarith
    have haU : blockMean n * armMass P false k ≤
        3 * (blockMean n * P.cellMass k) / 4 := by
      simp only [armMass, Bool.false_eq_true, ↓reduceIte]
      nlinarith
    have hbU : blockMean n * armMass P true k ≤
        3 * (blockMean n * P.cellMass k) / 4 := by
      simp only [armMass, ↓reduceIte]
      nlinarith
    exact heavy_noise_rate_envelope (mul_nonneg hm.le hp0) hsum ha0 hb0
      haL hbL haU hbU

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
