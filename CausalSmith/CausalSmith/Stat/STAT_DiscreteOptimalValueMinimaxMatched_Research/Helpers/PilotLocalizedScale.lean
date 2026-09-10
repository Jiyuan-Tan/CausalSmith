import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.PilotControl

/-! Localized geometry of the canonical pilot rectangle. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open scoped BigOperators

-- @node: canonicalPilotGoodSqrtWidth_le
/-- On a good pilot, the Jackson endpoint weight vanishes at a null coordinate
and otherwise has the local square-root scale. This uses [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the pilot sample lies in the good event](hyp:hgood). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilotGoodSqrtWidth_le
    (m : ℝ) (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d)
    (pilot : Cell → ℕ) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hgood : pilotGoodEvent canonicalJacksonTuning m d pilot q) (j : Cell) :
    Real.sqrt ((q j - (pilotRectangle canonicalJacksonTuning m d pilot).1 j) *
        ((pilotRectangle canonicalJacksonTuning m d pilot).2 j - q j)) ≤
      10000000 * Real.sqrt (q j * (logAlphabet d / m)) := by
  let tau := logAlphabet d / m
  let c := pilotCenter m pilot j
  let s := Real.sqrt (c * tau)
  let h := pilotRadius canonicalJacksonTuning m d pilot j
  change Real.sqrt ((q j - (pilotRectangle canonicalJacksonTuning m d pilot).1 j) *
      ((pilotRectangle canonicalJacksonTuning m d pilot).2 j - q j)) ≤
    10000000 * Real.sqrt (q j * tau)
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet]
    apply Real.log_pos
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hdR (Real.exp_nonneg 1)]
  have htau : 0 < tau := div_pos hL hm
  have hc : 0 ≤ c := by dsimp [c, pilotCenter]; positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = c * tau := by
    dsimp [s]
    rw [Real.sq_sqrt] <;> positivity
  have hh : h = 1024 * (s + tau) := by
    simp [h, pilotRadius, canonicalJacksonTuning,
      Causalean.Stat.Concentration.PoissonSelfNormalized.universalH, s, tau, c]
    congr 2
    ring
  have hmem := pilotGoodEvent_mem_pilotRectangle
    canonicalJacksonTuning m d pilot q hq hgood j
  have hqclose : |pilotCenter m pilot j - q j| ≤ h / 4 := by
    simpa [pilotGoodEvent, h] using hgood j
  change |c - q j| ≤ h / 4 at hqclose
  by_cases hlo : c - h ≤ 0
  · have hyoung : s ≤ c / 2048 + 512 * tau := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [show c * tau = s ^ 2 by exact hs2.symm]
        nlinarith [sq_nonneg (c / 2048 - 512 * tau)]
    have hcle : c ≤ 1100000 * tau := by
      change c - h ≤ 0 at hlo
      rw [hh] at hlo
      nlinarith
    have hhle : h ≤ 1200000000 * tau := by
      rw [hh]
      nlinarith
    have hprod :
        (q j - (pilotRectangle canonicalJacksonTuning m d pilot).1 j) *
            ((pilotRectangle canonicalJacksonTuning m d pilot).2 j - q j) ≤
          q j * (c + h) := by
      simp only [pilotRectangle]
      rw [max_eq_left hlo]
      dsimp only [c, h]
      nlinarith [hmem.1, hmem.2, sq_nonneg (q j)]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (mul_nonneg (hq j) (le_of_lt htau))]
      have hct : c + h ≤ 1201100000 * tau := by linarith
      have := mul_le_mul_of_nonneg_left hct (hq j)
      nlinarith
  · have hlo' : 0 < c - h := lt_of_not_ge hlo
    have hqge : 3 * c / 4 ≤ q j := by
      have := (abs_le.mp hqclose).2
      nlinarith
    have htauc : tau ≤ c := by
      rw [hh] at hlo'
      nlinarith
    have htaus : tau ≤ s := by
      apply (sq_le_sq₀ (le_of_lt htau) hs).mp
      rw [hs2]
      nlinarith
    have hsqcomp : s ≤ 2 * Real.sqrt (q j * tau) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · rw [show c * tau = s ^ 2 by exact hs2.symm, mul_pow,
          Real.sq_sqrt (mul_nonneg (hq j) (le_of_lt htau))]
        nlinarith [mul_le_mul_of_nonneg_right hqge (le_of_lt htau)]
    have hhle : h ≤ 4096 * Real.sqrt (q j * tau) := by
      rw [hh]
      nlinarith
    have hr : rectangleRadius
        (pilotRectangle canonicalJacksonTuning m d pilot) j = h := by
      change ((c + h) - max 0 (c - h)) / 2 = h
      rw [max_eq_right (le_of_lt hlo')]
      ring
    have hsqrt : Real.sqrt
        ((q j - (pilotRectangle canonicalJacksonTuning m d pilot).1 j) *
          ((pilotRectangle canonicalJacksonTuning m d pilot).2 j - q j)) ≤
        rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j := by
      have hrpos := pilotRectangle_radius_pos
        canonicalJacksonTuning m d pilot hm hd j
      rw [Real.sqrt_le_iff]
      refine ⟨le_of_lt hrpos, ?_⟩
      let a := (pilotRectangle canonicalJacksonTuning m d pilot).1 j
      let b := (pilotRectangle canonicalJacksonTuning m d pilot).2 j
      change (q j - a) * (b - q j) ≤ ((b - a) / 2) ^ 2
      nlinarith [hmem.1, hmem.2,
        sq_nonneg (q j - ((pilotRectangle canonicalJacksonTuning m d pilot).1 j +
          (pilotRectangle canonicalJacksonTuning m d pilot).2 j) / 2)]
    exact hsqrt.trans (hr ▸ hhle) |>.trans (by gcongr <;> norm_num)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
