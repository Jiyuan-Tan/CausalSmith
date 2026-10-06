module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.IntervalScales

/-! Uniform effective-size thresholds for equations (9)--(10) of the
connected-interval proof. These are numerical estimates, preceding the
activated likelihood and model-mixture transfer. -/

public section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:η,D,n,q,hη,hN,hell,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_capacity_of_large_size
lemma interval_capacity_of_large_size (η : ℝ) (D n : ℕ) (q : ℝ)
    (hη : 0 < η) (hN : 0 < effectiveSize n q)
    (hell : 1 ≤ logScale n q) (hlarge : 2 * η * D ≤ effectiveSize n q) :
    (D : ℝ) ≤ (2 * rareMass η n q)⁻¹ := by
  have hb : 0 < 2 * rareMass η n q := by unfold rareMass; positivity
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hb).mpr
  rw [show (D : ℝ) * (2 * rareMass η n q) =
    (2 * η * D) / (effectiveSize n q * logScale n q) by unfold rareMass; ring]
  apply (div_le_iff₀ (by positivity : 0 < effectiveSize n q * logScale n q)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hell hN.le]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hN,hell), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_activation_tail_le_exp
lemma interval_activation_tail_le_exp (n d : ℕ) (q : ℝ)
    (hN : 0 < effectiveSize n q) (hell : 1 ≤ logScale n q) :
    (rareCount (Real.exp (-32)) n d q : ℝ) *
      (Real.exp 1 * Real.exp (-32)) ^ (lowerDegree n q + 1) ≤
        Real.exp (32 - 29 * logScale n q) := by
  let N := effectiveSize n q
  let L := logScale n q
  have hNL : 0 < N * L := by dsimp [N, L]; positivity
  have hcap : (rareCount (Real.exp (-32)) n d q : ℝ) ≤
      N * L / (2 * Real.exp (-32)) := by
    have h := rareCount_mass_le_half (Real.exp (-32)) n d q
      (show 0 < rareMass (Real.exp (-32)) n q by unfold rareMass; positivity)
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.exp (-32))).mpr
    dsimp [rareMass] at h
    have h' := (div_le_iff₀ hNL).mp (show
      (rareCount (Real.exp (-32)) n d q : ℝ) * Real.exp (-32) / (N * L) ≤ 1 / 2 by
        simpa [N, L, mul_div_assoc] using h)
    nlinarith
  have hexpL : Real.exp L = Real.exp 1 + N := by
    dsimp [L, N, logScale]
    rw [Real.exp_log (by positivity)]
  have hNexp : N ≤ Real.exp L := by rw [hexpL]; linarith [Real.exp_pos (1 : ℝ)]
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hprod : N * L ≤ Real.exp (2 * L) := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
    exact mul_le_mul hNexp hLexp (by dsimp [L]; linarith) (Real.exp_nonneg _)
  have hdegree : L ≤ (lowerDegree n q + 1 : ℕ) := by
    have h := Nat.le_ceil (logScale n q)
    dsimp [L]
    unfold lowerDegree
    push_cast
    linarith
  have hpow : (Real.exp 1 * Real.exp (-32)) ^ (lowerDegree n q + 1) ≤
      Real.exp (-31 * L) := by
    rw [← Real.exp_add, show (1 : ℝ) + -32 = -31 by norm_num,
      ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ (N * L / (2 * Real.exp (-32))) * Real.exp (-31 * L) :=
      mul_le_mul hcap hpow (by positivity) (by positivity)
    _ ≤ (Real.exp (2 * L) / Real.exp (-32)) * Real.exp (-31 * L) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact (div_le_div_of_nonneg_left hNL.le (Real.exp_pos (-32)) (by
        linarith [Real.exp_pos (-32)])).trans
        (div_le_div_of_nonneg_right hprod (Real.exp_nonneg (-32)))
    _ = Real.exp (32 - 29 * logScale n q) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      dsimp [L]
      ring

/-- Given [the specified inputs and assumptions](hyp:u,n,d,q,hu,hN,hell,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_activation_tail_budget
lemma interval_activation_tail_budget (u : ℝ) (n d : ℕ) (q : ℝ)
    (hu : 0 < u) (hN : 0 < effectiveSize n q) (hell : 1 ≤ logScale n q)
    (hlarge : Real.exp ((32 - Real.log (u / 16)) / 29) ≤ effectiveSize n q) :
    (rareCount (Real.exp (-32)) n d q : ℝ) *
      (Real.exp 1 * Real.exp (-32)) ^ (lowerDegree n q + 1) ≤ u / 16 := by
  have hlog := Real.log_le_log (Real.exp_pos ((32 - Real.log (u / 16)) / 29))
    (hlarge.trans (show effectiveSize n q ≤ Real.exp 1 + effectiveSize n q by
      linarith [Real.exp_pos (1 : ℝ)]))
  rw [Real.log_exp] at hlog
  change (32 - Real.log (u / 16)) / 29 ≤ logScale n q at hlog
  apply (interval_activation_tail_le_exp n d q hN hell).trans
  calc
    Real.exp (32 - 29 * logScale n q) ≤ Real.exp (Real.log (u / 16)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = u / 16 := Real.exp_log (by positivity)

/-- Given [the specified inputs and assumptions](hyp:u,D,hu), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_activation_thresholds
lemma interval_activation_thresholds (u : ℝ) (D : ℕ) (hu : 0 < u) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (n d : ℕ) (q : ℝ), 0 < effectiveSize n q →
      T ≤ effectiveSize n q →
        (D : ℝ) ≤ (2 * rareMass (Real.exp (-32)) n q)⁻¹ ∧
        (rareCount (Real.exp (-32)) n d q : ℝ) *
          (Real.exp 1 * Real.exp (-32)) ^ (lowerDegree n q + 1) ≤ u / 16 := by
  let T := max 1 (max (2 * Real.exp (-32) * D)
    (Real.exp ((32 - Real.log (u / 16)) / 29)))
  refine ⟨T, le_max_left _ _, ?_⟩
  intro n d q hN hlarge
  have hell : 1 ≤ logScale n q := by
    unfold logScale
    have h := Real.log_le_log (Real.exp_pos (1 : ℝ))
      (show Real.exp 1 ≤ Real.exp 1 + effectiveSize n q by linarith)
    simpa using h
  have hcap : 2 * Real.exp (-32) * D ≤ effectiveSize n q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have htail : Real.exp ((32 - Real.log (u / 16)) / 29) ≤ effectiveSize n q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  exact ⟨interval_capacity_of_large_size _ D n q (Real.exp_pos _) hN hell hcap,
    interval_activation_tail_budget u n d q hu hN hell htail⟩

/-- Given [the specified inputs and assumptions](hyp:u,hu), [the stated mathematical conclusion holds](goal). -/
-- @node: interval_activation_grid_thresholds
lemma interval_activation_grid_thresholds (u : ℝ) (hu : 0 < u) :
    let M := Nat.ceil (8 / u) + 1
    let D := Nat.ceil (18432 * (M : ℝ) ^ 2 / u) + 1
    1 ≤ M ∧ (M : ℝ)⁻¹ ≤ u / 8 ∧ 1 ≤ D ∧
      18432 * (M : ℝ) ^ 2 / u ≤ (D : ℝ) := by
  dsimp only
  have hM : 1 ≤ Nat.ceil (8 / u) + 1 := by omega
  have hMr : 0 < ((Nat.ceil (8 / u) + 1 : ℕ) : ℝ) := by exact_mod_cast hM
  have hceil := Nat.le_ceil (8 / u)
  have hgrid : 8 ≤ u * ((Nat.ceil (8 / u) + 1 : ℕ) : ℝ) := by
    have h := (div_le_iff₀ hu).mp hceil
    push_cast
    nlinarith
  refine ⟨hM, ?_, by omega, ?_⟩
  · rw [inv_eq_one_div]
    apply (div_le_iff₀ hMr).mpr
    nlinarith
  · have h := Nat.le_ceil (18432 * (((Nat.ceil (8 / u) + 1 : ℕ) : ℝ)) ^ 2 / u)
    push_cast at *
    linarith

end CausalSmith.Stat.MarRareqLogfrontier
