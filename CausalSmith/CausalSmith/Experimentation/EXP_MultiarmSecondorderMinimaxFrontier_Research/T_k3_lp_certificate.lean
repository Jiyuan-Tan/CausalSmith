import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.GridApprox
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_exact_response_type_game
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_rational_contrast_grid_certificate_sandwich

/-! Finite exact-rational three-arm LP certificate. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Filter
open Finset

-- @node: k3TauCountRat_sq_le_one
/-- [the population size is positive](hyp:hn), [the three-arm tau count rat squared is at most one](goal). -/
lemma k3TauCountRat_sq_le_one {n : ℕ} (hn : 0 < n) (m : CountVec 3 n) :
    (tauCountRat cDaggerQ m) ^ 2 ≤ 1 := by
  let s : RespType 3 → ℚ := fun t =>
    ∑ a, cDaggerQ a * if t a then 1 else 0
  have hs : ∀ t, -1 ≤ s t ∧ s t ≤ 1 := by
    intro t
    cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;>
      norm_num [s, cDaggerQ, Fin.sum_univ_succ, h0, h1, h2]
  have hsum : (∑ t, (m.1 t : ℚ)) = n := by
    exact_mod_cast m.2
  have hlo : -(n : ℚ) ≤ ∑ t, (m.1 t : ℚ) * s t := by
    calc
      -(n : ℚ) = ∑ t, (m.1 t : ℚ) * (-1) := by rw [← hsum]; simp
      _ ≤ ∑ t, (m.1 t : ℚ) * s t := sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (hs t).1 (by positivity)
  have hhi : ∑ t, (m.1 t : ℚ) * s t ≤ n := by
    rw [← hsum]
    simpa only [mul_one] using sum_le_sum (fun t _ =>
      mul_le_mul_of_nonneg_left (hs t).2 (by positivity))
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have htau : tauCountRat cDaggerQ m = (n : ℚ)⁻¹ * ∑ t, (m.1 t : ℚ) * s t := by
    rfl
  rw [htau]
  have hinv : (0 : ℚ) < (n : ℚ)⁻¹ := inv_pos.mpr hnQ
  have hl : -(1 : ℚ) ≤ (n : ℚ)⁻¹ * ∑ t, (m.1 t : ℚ) * s t := by
    have := mul_le_mul_of_nonneg_left hlo (le_of_lt hinv)
    field_simp at this ⊢
    exact this
  have hu : (n : ℚ)⁻¹ * ∑ t, (m.1 t : ℚ) * s t ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hhi (le_of_lt hinv)
    field_simp at this ⊢
    exact this
  nlinarith

-- @node: gridLPValueK3_le_one
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the grid lpvalue three-arm is at most one](goal). -/
lemma gridLPValueK3_le_one (n M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    gridLPValueK3 n M hM ≤ 1 := by
  classical
  let r₀ : AllocVec 3 n := assignmentCounts (fun _ => 0)
  let g₀ : Fin (2 * M + 1) := ⟨M, by omega⟩
  let pi : GridPi 3 n := fun r => if r = r₀ then 1 else 0
  let w : RationalGridWeight 3 n M := fun r _ g =>
    if r = r₀ ∧ g = g₀ then 1 else 0
  have hg : gammaMC M cDaggerQ g₀ = 0 := by
    dsimp [g₀, gammaMC, hRat, LcRat, cDaggerQ]
    norm_num [Fin.sum_univ_succ]
    field_simp
    ring
  have hfeas : GridLPFeasible 3 n M cDaggerQ pi w 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [pi]
    · intro r x
      by_cases hr : r = r₀
      · subst r
        simp [pi, w]
      · simp [pi, w, hr]
    · intro r
      dsimp [pi]
      split <;> norm_num
    · intro r x g
      dsimp [w]
      split <;> norm_num
    · intro m
      simp only [w]
      rw [sum_eq_single r₀]
      · calc
          ∑ x : ObsVec r₀, ∑ g,
              orbitLik m r₀ x * (if r₀ = r₀ ∧ g = g₀ then 1 else 0) *
                (gammaMC M cDaggerQ g - tauCountRat cDaggerQ m) ^ 2 =
              ∑ x : ObsVec r₀, orbitLik m r₀ x * tauCountRat cDaggerQ m ^ 2 := by
                apply sum_congr rfl
                intro x hx
                rw [sum_eq_single g₀]
                · simp [hg]
                · intro g _ hgne
                  simp [hgne]
                · simp
          _ ≤ ∑ x : ObsVec r₀, orbitLik m r₀ x * 1 := by
                apply sum_le_sum
                intro x hx
                exact mul_le_mul_of_nonneg_left
                  (k3TauCountRat_sq_le_one hn m) (orbitLik_nonneg m r₀ x)
          _ = 1 := by simpa using orbitLik_sum_obs m r₀
      · intro r _ hr
        simp [hr]
      · simp
  unfold gridLPValueK3 gridLPValueRaw
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨pi', w', u', hu', rfl⟩
    exact_mod_cast gridLP_u_nonneg hu'
  · exact ⟨pi, w, 1, hfeas, by norm_num⟩

-- @node: prop:k3-lp-certificate
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [the exact three-arm linear program has the stated certified value and primal–dual witness](goal). -/
theorem k3_lp_certificate (n M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    rhoNDagger n ≤ gridLPValueK3 n M hM ∧
    gridLPValueK3 n M hM ≤ rhoNDagger n + 2 / (M : ℝ) + 1 / (M : ℝ) ^ 2 ∧
    0 ≤ gridLPValueK3 n M hM ∧ gridLPValueK3 n M hM ≤ 1 ∧
    (∃ (pi : GridPi 3 n) (w : GridWeight 3 n (n ^ 2)) (u : ℚ),
      ∃ nu : CountVec 3 n → ℚ,
        ExactGridPrimalDualCertificate cDaggerQ pi w u nu ∧
        (u : ℝ) = gridLPValueK3 n (n ^ 2) (Nat.pow_pos hn)) ∧
    (∀ t : RespType 3, ∃ m : CountVec 3 n, 0 < (m.1 t : ℕ)) ∧
    Tendsto (fun k : ℕ => secondOrderScale k *
      (2 / (k : ℝ) ^ 2 + 1 / (k : ℝ) ^ 4)) atTop (nhds 0) := by
  obtain ⟨pi, w, u, nu, delta, hcert, _hbary, hu, hlow, hrho, hupp, hlp,
      _hcount, _halloc, _hobs, _hscale⟩ :=
    rational_contrast_grid_certificate_sandwich 3 n M cDaggerQ hn hM
  have hC0 : C0 (ratContrastToReal cDaggerQ) = 1 := by
    norm_num [C0, Lc, ratContrastToReal, cDaggerQ, Fin.sum_univ_succ]
  have hrhoGrid : rhoNDagger n ≤ gridLPValueK3 n M hM := by
    simpa [rhoNDagger, cDagger, gridLPValueK3, gridLPValue] using hrho.trans hupp
  have hgridRho : gridLPValueK3 n M hM ≤
      rhoNDagger n + 2 / (M : ℝ) + 1 / (M : ℝ) ^ 2 := by
    have hmesh : gridLPValue 3 n M cDaggerQ hn hM ≤
        rhoN 3 n (ratContrastToReal cDaggerQ) + 2 / (M : ℝ) + 1 / (M : ℝ) ^ 2 := by
      calc
        gridLPValue 3 n M cDaggerQ hn hM ≤
            lowerCertificate cDaggerQ nu + 1 / (4 * (M : ℝ) ^ 2) := by
              simpa [hC0] using hlp
        _ ≤ rhoN 3 n (ratContrastToReal cDaggerQ) + 1 / (4 * (M : ℝ) ^ 2) := by
              gcongr
        _ ≤ rhoN 3 n (ratContrastToReal cDaggerQ) +
            2 / (M : ℝ) + 1 / (M : ℝ) ^ 2 := by
              have hMR : (0 : ℝ) < M := by exact_mod_cast hM
              field_simp
              nlinarith
    simpa [rhoNDagger, cDagger, gridLPValueK3, gridLPValue] using hmesh
  have hrhoNonneg : 0 ≤ rhoNDagger n := by
    unfold rhoNDagger rhoN
    exact Causalean.Stat.minimaxValue_nonneg fun p z => p.1.mse_nonneg _ _
  have hgridNonneg : 0 ≤ gridLPValueK3 n M hM := hrhoNonneg.trans hrhoGrid
  obtain ⟨pi2, w2, u2, nu2, delta2, hcert2, _hbary2, hu2, _hlow2,
      _hrho2, _hupp2, _hlp2, _hcount2, _halloc2, _hobs2, _hscale2⟩ :=
    rational_contrast_grid_certificate_sandwich 3 n (n ^ 2) cDaggerQ hn
      (Nat.pow_pos hn)
  refine ⟨hrhoGrid, hgridRho, hgridNonneg, gridLPValueK3_le_one n M hn hM, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨pi2, w2, u2, nu2, hcert2, by
      simpa [gridLPValueK3, gridLPValue] using hu2⟩
  · intro t
    let z : Schedule 3 n := fun _ => t
    refine ⟨scheduleCounts z, ?_⟩
    simp [scheduleCounts, rawScheduleCount, z, hn]
  · have h2 : Tendsto (fun x : ℝ => 2 * x ^ (-(2 / 3 : ℝ))) atTop (nhds 0) := by
      simpa using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul 2
    have h8 : Tendsto (fun x : ℝ => x ^ (-(8 / 3 : ℝ))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8 / 3)
    have h := (h2.add h8).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, zero_add] using h.congr' (by
      filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
      rw [secondOrderScale]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hfirst : (k : ℝ) ^ (4 / 3 : ℝ) * (2 / (k : ℝ) ^ 2) =
          2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [div_eq_mul_inv]
        calc
          (k : ℝ) ^ (4 / 3 : ℝ) * (2 * ((k : ℝ) ^ 2)⁻¹) =
              2 * ((k : ℝ) ^ (4 / 3 : ℝ) * ((k : ℝ) ^ 2)⁻¹) := by ring
          _ = 2 * ((k : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(2 : ℝ))) := by
            rw [Real.rpow_neg (le_of_lt hkR)]
            norm_num
          _ = 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
            rw [← Real.rpow_add hkR]
            norm_num
      have hsecond : (k : ℝ) ^ (4 / 3 : ℝ) * (1 / (k : ℝ) ^ 4) =
          (k : ℝ) ^ (-(8 / 3 : ℝ)) := by
        rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (le_of_lt hkR),
          ← Real.rpow_add hkR]
        norm_num
      change 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) + (k : ℝ) ^ (-(8 / 3 : ℝ)) = _
      rw [mul_add, hfirst, hsecond])

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
