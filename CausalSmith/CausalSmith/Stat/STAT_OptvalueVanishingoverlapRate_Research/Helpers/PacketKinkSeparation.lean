module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketCompletion

/-! # Separation of the two packet kinks

Roadmap (26)--(27): the circular distance between the kinks stays at least
four times the inverse square root of M. Jackson antiderivative localization
therefore suppresses the opposite atomic contribution even when M = K².
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

-- @node: packetKink_distance_eq
/-- The shortest arc between the two kinks passes through the endpoint π. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetKink_distance_eq {M : ℝ} (hM : 2 ≤ M) :
    torusDistance (2 * Real.arccos (2 / M - 1)) =
      2 * (Real.pi - Real.arccos (2 / M - 1)) := by
  let θ := Real.arccos (2 / M - 1)
  have hM0 : 0 < M := by linarith
  have hr : 2 / M ≤ 1 := (div_le_one hM0).2 hM
  have hlo : Real.pi / 2 ≤ θ := by
    have h := Real.arccos_le_arccos (show 2 / M - 1 ≤ 0 by linarith)
    simpa only [Real.arccos_zero] using h
  have hhi : θ ≤ Real.pi := Real.arccos_le_pi _
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  change sInf {r : ℝ | ∃ j : ℤ, r = |2 * θ - 2 * Real.pi * j|} = _
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, by rintro r ⟨j, rfl⟩; exact abs_nonneg _⟩
    · refine ⟨1, ?_⟩
      simp only [Int.cast_one, mul_one, abs_of_nonpos (show 2 * θ - 2 * Real.pi ≤ 0 by linarith)]
      dsimp [θ]
      ring
  · have hne : Set.Nonempty {r : ℝ | ∃ j : ℤ, r = |2 * θ - 2 * Real.pi * j|} :=
      ⟨|2 * θ|, 0, by simp⟩
    apply le_csInf hne
    rintro r ⟨j, rfl⟩
    by_cases hj : j ≤ 0
    · have hjR : (j : ℝ) ≤ 0 := by exact_mod_cast hj
      have hshift : 0 ≤ 2 * θ - 2 * Real.pi * j := by
        nlinarith [Real.pi_pos]
      rw [abs_of_nonneg hshift]
      change 2 * (Real.pi - θ) ≤ _
      nlinarith [Real.pi_pos]
    · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      have hshift : 2 * θ - 2 * Real.pi * j ≤ 0 := by
        nlinarith [Real.pi_pos]
      rw [abs_of_nonpos hshift]
      change 2 * (Real.pi - θ) ≤ _
      nlinarith [Real.pi_pos]

-- @node: packetKink_distance_lower
/-- The opposite kink remains at circular distance at least 4/√M, including at the dense endpoint. This is the lower bound in roadmap (26). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetKink_distance_lower {M : ℝ} (hM : 2 ≤ M) :
    4 / Real.sqrt M ≤ torusDistance (2 * Real.arccos (2 / M - 1)) := by
  rw [packetKink_distance_eq hM]
  let α := Real.pi - Real.arccos (2 / M - 1)
  have hM0 : 0 < M := by linarith
  have hα : 0 ≤ α := sub_nonneg.mpr (Real.arccos_le_pi _)
  have hr : 2 / M ≤ 1 := (div_le_one hM0).2 hM
  have hc : Real.cos α = 1 - 2 / M := by
    dsimp [α]
    rw [Real.cos_pi_sub, Real.cos_arccos
      (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hM0]) (by linarith)]
    ring
  have ht := Real.one_sub_sq_div_two_le_cos (x := α)
  rw [hc] at ht
  have hs : 4 / M ≤ α ^ 2 := by
    rw [show 4 / M = 2 * (2 / M) by ring]
    linarith
  have hroot : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
  have hsq : (2 / Real.sqrt M) ^ 2 = 4 / M := by
    rw [div_pow, Real.sq_sqrt hM0.le]
    norm_num
  have hq : 0 ≤ 2 / Real.sqrt M := by positivity
  have ha : 2 / Real.sqrt M ≤ α := by
    nlinarith [hsq]
  change 4 / Real.sqrt M ≤ 2 * α
  convert mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> first | rfl | ring

-- @node: packetKink_antideriv_bound
/-- Localization and kink separation give the opposite-center response bound `C M/N³`. This is the antiderivative estimate used in roadmap (27). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetKink_antideriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (M : ℝ), 2 ≤ N → 2 ≤ M →
      |packetAntideriv N (2 * Real.arccos (2 / M - 1))| ≤
        C * M / (N : ℝ) ^ 3 := by
  obtain ⟨c, C, hc, hcC, hpacket⟩ := jackson_packet_localization
  refine ⟨C / 16, by linarith, ?_⟩
  intro N M hN hM
  have hC : 0 < C := hc.trans_le hcC
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : 0 < M := by linarith
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hm
  have hd := packetKink_distance_lower hM
  have hloc := (hpacket N hN).2.2.2.2.2.2.2.2.2.2.1
  let d := torusDistance (2 * Real.arccos (2 / M - 1))
  have hd0 : 0 ≤ d := le_trans (by positivity) hd
  have hbase : 4 * (N : ℝ) / Real.sqrt M ≤ 1 + (N : ℝ) * d := by
    have hh := mul_le_mul_of_nonneg_left hd hn.le
    dsimp [d]
    calc
      _ = (N : ℝ) * (4 / Real.sqrt M) := by ring
      _ ≤ (N : ℝ) * torusDistance (2 * Real.arccos (2 / M - 1)) := hh
      _ ≤ _ := by linarith
  calc
    _ ≤ C / ((N : ℝ) * (1 + (N : ℝ) * d) ^ 2) := hloc _
    _ ≤ C / ((N : ℝ) * (4 * (N : ℝ) / Real.sqrt M) ^ 2) := by
      apply div_le_div_of_nonneg_left hC.le (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase 2) hn.le
    _ = (C / 16) * M / (N : ℝ) ^ 3 := by
      rw [div_pow, Real.sq_sqrt hm.le]
      field_simp
      ring

-- @node: packetKink_opposite_atom_bound
/-- The opposite atomic contribution has order `M^(3/2)/N³`, uniformly in M. Its coefficient is the actual derivative jump `√(M-1)/2` of roadmap (24). In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetKink_opposite_atom_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (M : ℝ), 2 ≤ N → 2 ≤ M →
      (Real.sqrt (M - 1) / 2) *
        |packetAntideriv N (2 * Real.arccos (2 / M - 1))| ≤
          C * M * Real.sqrt M / (N : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := packetKink_antideriv_bound
  refine ⟨C / 2, by positivity, ?_⟩
  intro N M hN hM
  calc
    _ ≤ (Real.sqrt M / 2) * (C * M / (N : ℝ) ^ 3) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (by norm_num))
        (hbound N M hN hM) (abs_nonneg _) (by positivity)
    _ = _ := by ring

-- @node: packetKink_atomic_response_lower
/-- A universal packet scale prevents the opposite kink from canceling even half of the center response, uniformly over the full range M ≤ K². In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetKink_atomic_response_lower :
    ∃ (c : ℝ) (A₀ : ℕ), 0 < c ∧ 1 ≤ A₀ ∧
      ∀ (K : ℕ) (M : ℝ), 2 ≤ K → 2 ≤ M → M ≤ (K : ℝ) ^ 2 →
        c * Real.sqrt M / K ≤
          (Real.sqrt (M - 1) / 2) *
            |packetAntideriv (A₀ * K) 0 +
              packetAntideriv (A₀ * K) (2 * Real.arccos (2 / M - 1))| := by
  obtain ⟨c, Ccenter, hc, _, hpacket⟩ := jackson_packet_localization
  obtain ⟨C, hC, hopposite⟩ := packetKink_antideriv_bound
  obtain ⟨A, hA⟩ := exists_nat_gt (max 1 (2 * C / c))
  have hA1R : (1 : ℝ) ≤ A := (le_max_left _ _).trans hA.le
  have hA1 : 1 ≤ A := by exact_mod_cast hA1R
  have hAR : (0 : ℝ) < A := by linarith
  have hdom : 2 * C ≤ c * (A : ℝ) ^ 2 := by
    have hratio : 2 * C / c ≤ (A : ℝ) := (le_max_right _ _).trans hA.le
    have hh := (div_le_iff₀ hc).mp hratio
    have hsq : (A : ℝ) ≤ (A : ℝ) ^ 2 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith
  refine ⟨c / (8 * A), A, by positivity, hA1, ?_⟩
  intro K M hK hM hMhi
  let N := A * K
  have hN : 2 ≤ N := by dsimp [N]; nlinarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hNcast : (N : ℝ) = (A : ℝ) * K := by simp [N]
  have hcenter : c / (N : ℝ) ≤ |packetAntideriv N 0| :=
    (hpacket N hN).2.2.2.2.2.2.2.2.1
  have hsmall : |packetAntideriv N (2 * Real.arccos (2 / M - 1))| ≤
      c / (2 * N) := by
    apply (hopposite N M hN hM).trans
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 3)
      (by positivity : (0 : ℝ) < 2 * N)).mpr
    have hh : 2 * C * M ≤ c * (N : ℝ) ^ 2 := by
      calc
        _ ≤ 2 * C * (K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hMhi (by positivity)
        _ ≤ (c * (A : ℝ) ^ 2) * (K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hdom (sq_nonneg _)
        _ = _ := by rw [hNcast]; ring
    have hh' := mul_le_mul_of_nonneg_right hh hn.le
    nlinarith only [hh']
  have hsum : c / (2 * N) ≤
      |packetAntideriv N 0 + packetAntideriv N (2 * Real.arccos (2 / M - 1))| := by
    have hh := abs_add_le
      (packetAntideriv N 0 + packetAntideriv N (2 * Real.arccos (2 / M - 1)))
      (-packetAntideriv N (2 * Real.arccos (2 / M - 1)))
    simp only [add_neg_cancel_right, abs_neg] at hh
    have he : c / (N : ℝ) = 2 * (c / (2 * N)) := by ring
    rw [he] at hcenter
    linarith
  have hroot : Real.sqrt M / 2 ≤ Real.sqrt (M - 1) := by
    have hm : 0 ≤ M := by linarith
    have hm1 : 0 ≤ M - 1 := by linarith
    have hs := Real.sq_sqrt hm
    have hs1 := Real.sq_sqrt hm1
    have hp := Real.sqrt_nonneg M
    have hp1 := Real.sqrt_nonneg (M - 1)
    nlinarith
  calc
    (c / (8 * A)) * Real.sqrt M / K =
        (Real.sqrt M / 4) * (c / (2 * N)) := by
      rw [hNcast]
      field_simp
      ring
    _ ≤ _ := mul_le_mul
      (by linarith : Real.sqrt M / 4 ≤ Real.sqrt (M - 1) / 2)
      hsum (by positivity) (by positivity)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
