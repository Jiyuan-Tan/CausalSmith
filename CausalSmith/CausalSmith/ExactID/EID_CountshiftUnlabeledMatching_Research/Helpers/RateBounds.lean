module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Defs.Estimator

/-! Uniform logarithmic bounds for the finite sample deviation radius. -/

public section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: log_ratio_bounds
lemma log_ratio_bounds (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ, 2 ≤ p →
      Real.log p ≤ Real.log (4 * p * (p + 1) / δ) ∧
      Real.log (4 * p * (p + 1) / δ) ≤ K * Real.log p := by
  let K := 2 + Real.log (8 / δ) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 1 ≤ 8 / δ := by
    apply (le_div_iff₀ hδ).2
    linarith
  have hlogD : 0 ≤ Real.log (8 / δ) := Real.log_nonneg hD
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro p hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hppos : (0 : ℝ) < p := by positivity
  have hlogp : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) hpR
  have hlow : (p : ℝ) ≤ 4 * p * (p + 1) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith
  have hhigh : 4 * (p : ℝ) * (p + 1) / δ ≤ (8 / δ) * p ^ 2 := by
    apply (div_le_iff₀ hδ).2
    field_simp
    nlinarith
  have hmul : Real.log ((8 / δ) * (p : ℝ) ^ 2) =
      Real.log (8 / δ) + 2 * Real.log p := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  constructor
  · exact Real.log_le_log hppos hlow
  · calc
      Real.log (4 * p * (p + 1) / δ) ≤ Real.log ((8 / δ) * p ^ 2) :=
        Real.log_le_log (by positivity) hhigh
      _ = Real.log (8 / δ) + 2 * Real.log p := hmul
      _ ≤ K * Real.log p := by
        dsimp [K]
        have h : Real.log (8 / δ) ≤
            (Real.log (8 / δ) / Real.log 2) * Real.log p := by
          have hratio : 1 ≤ Real.log p / Real.log 2 :=
            (le_div_iff₀ hlog2).2 (by simpa using hlogp)
          calc
            Real.log (8 / δ) ≤ Real.log (8 / δ) *
                (Real.log p / Real.log 2) := le_mul_of_one_le_right hlogD hratio
            _ = (Real.log (8 / δ) / Real.log 2) * Real.log p := by ring
        nlinarith

-- @node: epsN_bounds
lemma epsN_bounds (C ℓ v δ : ℝ) (hC : 0 < C) (hℓ : 0 < ℓ)
    (hv : 0 < v) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (p n : ℕ), 2 ≤ p → 0 < n →
        c₁ * Real.sqrt (Real.log p / n) ≤ epsN C p n v ℓ δ ∧
        epsN C p n v ℓ δ ≤ c₂ * Real.sqrt (Real.log p / n) := by
  obtain ⟨K, hK, hlogs⟩ := log_ratio_bounds δ hδ hδ'
  let L := ℓ⁻¹ + ℓ⁻¹ ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  let c₁ := C * Real.sqrt v * L
  let c₂ := C * Real.sqrt (v * K) * L
  refine ⟨c₁, c₂, by dsimp [c₁]; positivity,
    by dsimp [c₂]; positivity, ?_⟩
  intro p n hp hn
  obtain ⟨hloglo, hloghi⟩ := hlogs p hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hlogratio : 0 ≤ Real.log (4 * p * (p + 1) / δ) :=
    hlogp.trans hloglo
  have hleft : v * (Real.log p / n) ≤
      v * (Real.log (4 * p * (p + 1) / δ) / n) := by
    apply mul_le_mul_of_nonneg_left _ hv.le
    exact div_le_div_of_nonneg_right hloglo hnR.le
  have hright : v * (Real.log (4 * p * (p + 1) / δ) / n) ≤
      (v * K) * (Real.log p / n) := by
    calc
      v * (Real.log (4 * p * (p + 1) / δ) / n) ≤
          v * ((K * Real.log p) / n) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hloghi hnR.le) hv.le
      _ = (v * K) * (Real.log p / n) := by ring
  have hsqrtleft := Real.sqrt_le_sqrt hleft
  have hsqtright := Real.sqrt_le_sqrt hright
  rw [Real.sqrt_mul hv.le, Real.sqrt_mul hv.le] at hsqrtleft
  rw [Real.sqrt_mul (by positivity : 0 ≤ v * K),
      Real.sqrt_mul hv.le] at hsqtright
  have hrewrite : epsN C p n v ℓ δ =
      C * Real.sqrt v * Real.sqrt (Real.log (4 * p * (p + 1) / δ) / n) * L := by
    unfold epsN
    rw [show v * Real.log (4 * p * (p + 1) / δ) / (n : ℝ) =
      v * (Real.log (4 * p * (p + 1) / δ) / n) by ring,
      Real.sqrt_mul (le_of_lt hv)]
    ring
  constructor
  · rw [hrewrite]
    dsimp [c₁]
    calc
      C * Real.sqrt v * L * Real.sqrt (Real.log p / n) =
          (C * L) * (Real.sqrt v * Real.sqrt (Real.log p / n)) := by ring
      _ ≤ (C * L) *
          (Real.sqrt v * Real.sqrt (Real.log (4 * p * (p + 1) / δ) / n)) :=
        mul_le_mul_of_nonneg_left hsqrtleft (by positivity)
      _ = C * Real.sqrt v *
          Real.sqrt (Real.log (4 * p * (p + 1) / δ) / n) * L := by ring
  · rw [hrewrite]
    dsimp [c₂]
    calc
      C * Real.sqrt v *
          Real.sqrt (Real.log (4 * p * (p + 1) / δ) / n) * L =
            (C * L) *
              (Real.sqrt v * Real.sqrt (Real.log (4 * p * (p + 1) / δ) / n)) := by ring
      _ ≤ (C * L) * (Real.sqrt (v * K) * Real.sqrt (Real.log p / n)) :=
        mul_le_mul_of_nonneg_left hsqtright (by positivity)
      _ = C * Real.sqrt (v * K) * L * Real.sqrt (Real.log p / n) := by ring

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
