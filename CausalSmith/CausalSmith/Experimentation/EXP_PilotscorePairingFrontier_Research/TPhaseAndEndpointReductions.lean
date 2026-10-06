module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.TJointMinimaxFrontier

/-! # Regime reductions and the one-dimensional endpoint -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

-- @node: phase_rate_comparison
lemma phase_rate_comparison (G H B t : ℝ)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (ht : 1 ≤ t) (hBG : B ≤ G) :
    (G ≤ t * H → G / t ≤ min G (B + H) ∧ min G (B + H) ≤ G) ∧
    (H ≤ t * G → B ≤ t * H →
      H / t ≤ min G (B + H) ∧ min G (B + H) ≤ (t + 1) * H) ∧
    (H ≤ t * B → B ≤ min G (B + H) ∧ min G (B + H) ≤ (t + 1) * B) := by
  have htpos : 0 < t := by linarith
  constructor
  · intro h
    constructor
    · apply le_min
      · exact (div_le_iff₀ htpos).2 (by nlinarith)
      · exact (div_le_iff₀ htpos).2 (by nlinarith)
    · exact min_le_left _ _
  constructor
  · intro hHG hBH
    constructor
    · apply le_min
      · exact (div_le_iff₀ htpos).2 (by nlinarith)
      · exact (div_le_iff₀ htpos).2 (by nlinarith)
    · exact (min_le_right _ _).trans (by nlinarith)
  · intro hHB
    constructor
    · exact le_min hBG (by linarith)
    · exact (min_le_right _ _).trans (by nlinarith)

-- @node: prop:phase-and-endpoint-reductions
theorem phase_and_endpoint_reductions (d : ℕ) (β L cX CX cg Cg : ℝ)
    (hpars : ValidClassParameters d β L cX CX cg Cg) (hL : 1 / 2 < L) :
    ∀ κ : ℝ, 1 ≤ κ → ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ m N : ℕ, 1 ≤ m → Even N → 2 ≤ N →
        (m ≤ κ * (N : ℝ) ^ ((2 * β + d) / d) →
          c * (N : ℝ) ^ (-2 * β / d) ≤
            minimaxRisk d m N L β cX CX cg Cg ∧
          minimaxRisk d m N L β cX CX cg Cg ≤
            C * (N : ℝ) ^ (-2 * β / d)) ∧
        ((N : ℝ) ^ ((2 * β + d) / d) ≤ κ * m ∧
          m ≤ κ * (N : ℝ) ^ ((2 * β + d) / β) →
          c * (m : ℝ) ^ (-2 * β / (2 * β + d)) ≤
            minimaxRisk d m N L β cX CX cg Cg ∧
          minimaxRisk d m N L β cX CX cg Cg ≤
            C * (m : ℝ) ^ (-2 * β / (2 * β + d))) ∧
        ((N : ℝ) ^ ((2 * β + d) / β) ≤ κ * m →
          c * (N : ℝ) ^ (-2 : ℝ) ≤
            minimaxRisk d m N L β cX CX cg Cg ∧
          minimaxRisk d m N L β cX CX cg Cg ≤
            C * (N : ℝ) ^ (-2 : ℝ)) ∧
        (d = 1 → β = 1 →
          jointFrontier d m N β = (N : ℝ) ^ (-2 : ℝ) ∧
          c * (N : ℝ) ^ (-2 : ℝ) ≤
            minimaxRisk d m N L β cX CX cg Cg ∧
          minimaxRisk d m N L β cX CX cg Cg ≤
            C * (N : ℝ) ^ (-2 : ℝ)) := by
  obtain ⟨c₀, C₀, hc₀, hcC₀, hfrontier⟩ :=
    joint_minimax_frontier d β L cX CX cg Cg hpars hL
  have hd : (0 : ℝ) < d := by exact_mod_cast hpars.1
  have hβ : 0 < β := hpars.2.1
  have hβ1 : β ≤ 1 := hpars.2.2.1
  have hden : 0 < 2 * β + d := by positivity
  intro κ hκ
  let a : ℝ := 2 * β / (2 * β + d)
  let t : ℝ := κ ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : 1 ≤ t := by
    dsimp [t]
    calc (1 : ℝ) = (1 : ℝ) ^ a := by simp
      _ ≤ κ ^ a := Real.rpow_le_rpow (by norm_num) hκ (le_of_lt ha)
  have htpos : 0 < t := by linarith
  refine ⟨c₀ / t, C₀ * (t + 1), div_pos hc₀ htpos, ?_, ?_⟩
  · have hc₀le : c₀ / t ≤ c₀ := (div_le_iff₀ htpos).2 (by nlinarith)
    have hC₀le : C₀ ≤ C₀ * (t + 1) := by nlinarith
    linarith
  · intro m N hm hN hN2
    let G : ℝ := (N : ℝ) ^ (-2 * β / d)
    let H : ℝ := (m : ℝ) ^ (-2 * β / (2 * β + d))
    let B : ℝ := (N : ℝ) ^ (-2 : ℝ)
    let A : ℝ := (N : ℝ) ^ ((2 * β + d) / d)
    let E : ℝ := (N : ℝ) ^ ((2 * β + d) / β)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hκpos : 0 < κ := by linarith
    have hNnonneg : (0 : ℝ) ≤ N := le_of_lt hNpos
    have hκnonneg : 0 ≤ κ := le_of_lt hκpos
    have hApos : 0 < A := Real.rpow_pos_of_pos hNpos _
    have hEpos : 0 < E := Real.rpow_pos_of_pos hNpos _
    have hGpos : 0 < G := Real.rpow_pos_of_pos hNpos _
    have hHpos : 0 < H := Real.rpow_pos_of_pos hmpos _
    have hBpos : 0 < B := Real.rpow_pos_of_pos hNpos _
    have hA : A ^ (-a) = G := by
      dsimp [A, G]
      rw [← Real.rpow_mul hNnonneg]
      congr 1
      dsimp [a]
      field_simp
    have hE : E ^ (-a) = B := by
      dsimp [E, B]
      rw [← Real.rpow_mul hNnonneg]
      congr 1
      dsimp [a]
      field_simp
    have hscale (x : ℝ) (hx : 0 < x) : (κ * x) ^ (-a) = x ^ (-a) / t := by
      rw [Real.mul_rpow hκnonneg (le_of_lt hx), show -a = -(a) by rfl,
        Real.rpow_neg hκnonneg]
      simp [t, div_eq_mul_inv, mul_comm]
    have hHa : (m : ℝ) ^ (-a) = H := by
      dsimp [H, a]
      congr 1
      ring
    have hBG : B ≤ G := by
      dsimp [B, G]
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      have hβd : β ≤ (d : ℝ) := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hpars.1
        linarith
      apply (le_div_iff₀ hd).2
      nlinarith
    have hphi : jointFrontier d m N β = min G (B + H) := rfl
    have hcomparison := phase_rate_comparison G H B t
      (le_of_lt hGpos) (le_of_lt hHpos) (le_of_lt hBpos) ht hBG
    have hfront := hfrontier m N hm hN hN2
    have hbounds (R : ℝ) (X : ℝ)
        (hXL : X / t ≤ min G (B + H))
        (hXU : min G (B + H) ≤ (t + 1) * X)
        (hRlo : c₀ * min G (B + H) ≤ R)
        (hRhi : R ≤ C₀ * min G (B + H)) :
        c₀ / t * X ≤ R ∧ R ≤ C₀ * (t + 1) * X := by
      constructor
      · calc c₀ / t * X = c₀ * (X / t) := by ring
          _ ≤ c₀ * min G (B + H) := mul_le_mul_of_nonneg_left hXL (le_of_lt hc₀)
          _ ≤ R := hRlo
      · calc R ≤ C₀ * min G (B + H) := hRhi
          _ ≤ C₀ * ((t + 1) * X) := mul_le_mul_of_nonneg_left hXU (by linarith)
          _ = C₀ * (t + 1) * X := by ring
    have hRlo : c₀ * min G (B + H) ≤ minimaxRisk d m N L β cX CX cg Cg := by
      simpa [hphi] using hfront.1
    have hRhi : minimaxRisk d m N L β cX CX cg Cg ≤ C₀ * min G (B + H) := by
      simpa [hphi] using hfront.2.1
    have hfirst (hmA : (m : ℝ) ≤ κ * A) : G ≤ t * H := by
      have hp := Real.rpow_le_rpow_of_nonpos hmpos hmA (by linarith : -a ≤ 0)
      rw [hscale A hApos, hA, hHa] at hp
      simpa only [mul_comm] using (div_le_iff₀ htpos).1 hp
    have hsecond (hAm : A ≤ κ * m) : H ≤ t * G := by
      have hp := Real.rpow_le_rpow_of_nonpos hApos hAm (by linarith : -a ≤ 0)
      rw [hscale (m : ℝ) hmpos, hHa, hA] at hp
      simpa only [mul_comm] using (div_le_iff₀ htpos).1 hp
    have hthird (hmE : (m : ℝ) ≤ κ * E) : B ≤ t * H := by
      have hp := Real.rpow_le_rpow_of_nonpos hmpos hmE (by linarith : -a ≤ 0)
      rw [hscale E hEpos, hE, hHa] at hp
      simpa only [mul_comm] using (div_le_iff₀ htpos).1 hp
    have hfourth (hEm : E ≤ κ * m) : H ≤ t * B := by
      have hp := Real.rpow_le_rpow_of_nonpos hEpos hEm (by linarith : -a ≤ 0)
      rw [hscale (m : ℝ) hmpos, hHa, hE] at hp
      simpa only [mul_comm] using (div_le_iff₀ htpos).1 hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hmA
      have ⟨hlow, hupp⟩ := hcomparison.1 (hfirst hmA)
      have hupp' : min G (B + H) ≤ (t + 1) * G :=
        hupp.trans (by nlinarith [hGpos])
      exact hbounds _ G hlow hupp' hRlo hRhi
    · rintro ⟨hAm, hmE⟩
      have ⟨hlow, hupp⟩ := hcomparison.2.1 (hsecond hAm) (hthird hmE)
      exact hbounds _ H hlow hupp hRlo hRhi
    · intro hEm
      have ⟨hlow, hupp⟩ := hcomparison.2.2 (hfourth hEm)
      have hlow' : B / t ≤ min G (B + H) :=
        (div_le_iff₀ htpos).2 (by nlinarith [hBpos]) |>.trans hlow
      exact hbounds _ B hlow' hupp hRlo hRhi
    · intro hd1 hβ1'
      have hGB : G = B := by
        subst d
        subst β
        dsimp [G, B]
        norm_num
      have hPhiB : min G (B + H) = B := by
        rw [hGB]
        exact min_eq_left (by linarith [hHpos])
      have hlow : B / t ≤ min G (B + H) := by
        rw [hPhiB]
        exact (div_le_iff₀ htpos).2 (by nlinarith [hBpos])
      have hupp : min G (B + H) ≤ (t + 1) * B := by
        rw [hPhiB]
        nlinarith [hBpos]
      refine ⟨?_, hbounds _ B hlow hupp hRlo hRhi⟩
      change jointFrontier d m N β = B
      rw [hphi]
      exact hPhiB

end CausalSmith.Experimentation.PilotscorePairingFrontier
