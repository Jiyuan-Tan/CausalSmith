import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Basic
import Causalean.Experimentation.DesignBased.ProductMeasure
import Mathlib.Probability.Moments.SubGaussian

/-! Contrast-score moments and the explicit clipped-shrinkage procedure. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ}

/-- Minimum nonzero normalized response-type score spacing. -/
noncomputable def lambdaC (c : Contrast ℝ K) : ℝ :=
  sInf {v : ℝ | ∃ t : RespType K,
    (∑ a, c a * if t a then 1 else 0) ≠ 0 ∧
    v = |∑ a, c a * if t a then 1 else 0| / (Lc c / 2)}

/-- The contrast spacing constant is the smallest nonzero absolute normalized response-type score. -/
noncomputable def kappaC (c : Contrast ℝ K) : ℝ :=
  let A := Real.sqrt (lambdaC c) / 2 - lambdaC c / 16
  let B := 7 * lambdaC c / 16
  min A B / 2

/-- Explicit clipped shrinkage applied to the normalized contrast score. -/
noncomputable def shrinkageProcedure (K n : ℕ) (c : Contrast ℝ K) : Procedure K n c :=
  let base := contrastWeightedProcedure K n c
  (base.1, fun A y =>
    let raw := centeredContrastScore c A y
    let h := Lc c / 2
    let X := raw / h
    let b := (n : ℝ) ^ (-(1 / 3 : ℝ))
    let eps := Real.sqrt (lambdaC c) / 4 * b
    ⟨clip c (h * (X - eps * max (-b) (min X b))), clip_mem c _⟩)

/-- [the lambda c is positive is at most one](goal). -/
lemma lambdaC_pos_le_one (c : Contrast ℝ K) : 0 < lambdaC c ∧ lambdaC c ≤ 1 := by
  classical
  let score : RespType K → ℝ := fun t =>
    (∑ a, c a * if t a then 1 else 0)
  let values : Set ℝ := {v | ∃ t : RespType K,
    score t ≠ 0 ∧ v = |score t| / (Lc c / 2)}
  have hfinite : values.Finite := by
    apply Set.Finite.subset (Set.finite_range fun t : RespType K =>
      |score t| / (Lc c / 2))
    rintro v ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
    by_contra h
    apply c.nonzero
    funext a
    by_contra ha
    exact h ⟨a, ha⟩
  let t : RespType K := fun b => b = a
  have hscore : score t = c a := by
    simp [score, t]
  have hmem : |c a| / (Lc c / 2) ∈ values := by
    refine ⟨t, ?_, ?_⟩
    · simpa [hscore] using ha
    · simp [hscore]
  have hnonempty : values.Nonempty := ⟨_, hmem⟩
  have hinf : sInf values ∈ values := hnonempty.csInf_mem hfinite
  have hallpos : ∀ v ∈ values, 0 < v := by
    rintro v ⟨tv, htv, rfl⟩
    exact div_pos (abs_pos.mpr htv) (by positivity [Lc_pos c])
  have hcoeff : |c a| ≤ Lc c / 2 := by
    have hsum : (∑ b ∈ Finset.univ.erase a, c b) = -c a := by
      have hzero := c.sum_zero
      rw [← Finset.add_sum_erase Finset.univ c (Finset.mem_univ a)] at hzero
      linarith
    have habs := Finset.abs_sum_le_sum_abs (s := Finset.univ.erase a) (f := c)
    rw [hsum, abs_neg] at habs
    have hLc : Lc c = |c a| + ∑ b ∈ Finset.univ.erase a, |c b| := by
      exact (Finset.add_sum_erase Finset.univ (fun b => |c b|)
        (Finset.mem_univ a)).symm
    rw [hLc]
    linarith
  have hresult : 0 < sInf values ∧ sInf values ≤ 1 := by
    constructor
    · exact hallpos _ hinf
    · calc
        sInf values ≤ |c a| / (Lc c / 2) :=
          csInf_le ⟨0, fun v hv => le_of_lt (hallpos v hv)⟩ hmem
        _ ≤ 1 := (div_le_one (by positivity [Lc_pos c])).2 hcoeff
  simpa only [lambdaC, values, score] using hresult
/-- [the kappa c is positive](goal). -/
lemma kappaC_pos (c : Contrast ℝ K) : 0 < kappaC c := by
  rcases lambdaC_pos_le_one c with ⟨hlambda, hlambda_one⟩
  have hsqrt_pos : 0 < Real.sqrt (lambdaC c) := Real.sqrt_pos.2 hlambda
  have hsqrt_sq : (Real.sqrt (lambdaC c)) ^ 2 = lambdaC c := by
    exact Real.sq_sqrt (le_of_lt hlambda)
  have hA : 0 < Real.sqrt (lambdaC c) / 2 - lambdaC c / 16 := by
    nlinarith [Real.sqrt_nonneg (lambdaC c)]
  have hB : 0 < 7 * lambdaC c / 16 := by positivity
  simp only [kappaC]
  exact div_pos (lt_min hA hB) (by norm_num)

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
