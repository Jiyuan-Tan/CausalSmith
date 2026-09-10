import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.ScoreDesign
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.ShrinkageRisk
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_embedded_two_arm_converse
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! Universal `n^{-4/3}` second-order improvement. -/

open Filter

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- A positive sequence is regularly varying with exponent beta when its value at every fixed positive rescaling is asymptotic to the rescaling factor raised to beta times its original value. -/
def RegularlyVarying (a : ℕ → ℝ) (β : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x →
    Tendsto (fun n : ℕ => a ⌊ x * (n : ℝ) ⌋₊ / a n) atTop (nhds (x ^ β))

/-- [the comparison sequence is eventually positive](hyp:hbpos), [the ratio sequence is positive](hyp:hrpos), [the stated dyadic bounds hold](hyp:hbounds), [the dyadic ratio converges to one](hyp:hratio), [A positive sequence bounded above and away from zero cannot have a non-unit doubling-ratio limit.](goal) -/
-- @node: dyadic_ratio_limit_eq_one
lemma dyadic_ratio_limit_eq_one (b : ℕ → ℝ) (r : ℝ)
    (hbpos : ∀ n, 0 < b n) (hrpos : 0 < r)
    (hbounds : ∃ l u : ℝ, 0 < l ∧ ∀ᶠ n in atTop, l ≤ b n ∧ b n ≤ u)
    (hratio : Tendsto (fun n => b (2 * n) / b n) atTop (nhds r)) : r = 1 := by
  let u : ℕ → ℝ := fun k => Real.log (b (2 ^ k))
  have hpow : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hratio' : Tendsto (fun k => b (2 * 2 ^ k) / b (2 ^ k)) atTop (nhds r) :=
    hratio.comp hpow
  have hdiff : Tendsto (fun k => u (k + 1) - u k) atTop (nhds (Real.log r)) := by
    have hlog := hratio'.log hrpos.ne'
    convert hlog using 1
    · funext k
      simp only [u, pow_succ']
      rw [Real.log_div (hbpos _).ne' (hbpos _).ne']
  have hces := hdiff.cesaro
  rcases hbounds with ⟨l, v, hl, hbds⟩
  have hbds' : ∀ᶠ k in atTop, l ≤ b (2 ^ k) ∧ b (2 ^ k) ≤ v := hpow.eventually hbds
  have hulow : ∀ᶠ k in atTop, Real.log l ≤ u k := by
    filter_upwards [hbds'] with k hk
    exact Real.log_le_log hl hk.1
  have huhi : ∀ᶠ k in atTop, u k ≤ Real.log v := by
    filter_upwards [hbds'] with k hk
    exact Real.log_le_log (hbpos _) hk.2
  have havg0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      (u (i + 1) - u i)) atTop (nhds 0) := by
    have hlow' : ∀ᶠ k in atTop, Real.log l - u 0 ≤ u k - u 0 :=
      hulow.mono (fun _ hk => sub_le_sub_right hk _)
    have hhi' : ∀ᶠ k in atTop, u k - u 0 ≤ Real.log v - u 0 :=
      huhi.mono (fun _ hk => sub_le_sub_right hk _)
    have hquot : Tendsto (fun n : ℕ => (u n - u 0) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_bdd_div_atTop_nhds_zero hlow' hhi' tendsto_natCast_atTop_atTop
    convert hquot using 1
    funext n
    rw [Finset.sum_range_sub]
    simp [div_eq_mul_inv, mul_comm]
  have : Real.log r = 0 := tendsto_nhds_unique hces havg0
  exact Real.eq_one_of_pos_of_log_eq_zero hrpos this

/-- [The polynomial prefactor in the local shrinkage tail error is dominated by the stretched-exponential decay.](goal) -/
-- @node: shrinkage_tail_prefactor_tendsto_zero
lemma shrinkage_tail_prefactor_tendsto_zero : Tendsto (fun n : ℕ => (n : ℝ) *
    Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8)) atTop (nhds 0) := by
  let t : ℕ → ℝ := fun n => (n : ℝ) ^ (1 / 3 : ℝ)
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℝ) (1 / 8 : ℝ)
    (by norm_num)).comp ht
  apply h.congr'
  filter_upwards [Ici_mem_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [t]
  rw [← Real.rpow_mul hnR.le]
  congr 1
  · norm_num
  · ring

/-- [the population size is positive](hyp:hn), [The second-order scale exactly cancels its reciprocal power at positive sample sizes.](goal) -/
-- @node: secondOrderScale_mul_inverse
lemma secondOrderScale_mul_inverse (n : ℕ) (hn : 0 < n) :
    secondOrderScale n * (n : ℝ) ^ (-(4 / 3 : ℝ)) = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold secondOrderScale
  rw [← Real.rpow_add hnR]
  norm_num

-- @node: minimaxEnvelopeBound_of_contrastWeightedProcedure
/-- [The contrast-weighted procedure supplies the minimax envelope, including the degenerate zero-unit experiment.](goal) -/
lemma minimaxEnvelopeBound_of_contrastWeightedProcedure (K : ℕ)
    (c : Contrast ℝ K) : MinimaxEnvelopeBound K c := by
  intro n
  by_cases hn : n = 0
  · subst n
    have hLc : 0 ≤ Lc c := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hclip : clip c 0 = 0 := by
      unfold clip
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    have hzero : labeledRisk c (contrastWeightedProcedure K 0 c)
        (fun i => Fin.elim0 i) = 0 := by
      simp [labeledRisk, Causalean.Experimentation.DesignBased.FiniteDesign.mse,
        tauC, contrastWeightedProcedure, centeredContrastScore, hclip]
    calc
      rhoN K 0 c ≤ Causalean.Stat.worstCaseRisk
          (fun (p : Procedure K 0 c) (z : Schedule K 0) => labeledRisk c p z)
          (contrastWeightedProcedure K 0 c) :=
        Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
          (fun p z => p.1.mse_nonneg _ _) _
      _ ≤ 0 := by
        apply Causalean.Stat.worstCaseRisk_le
        intro z
        have hz : z = fun i => Fin.elim0 i := by
          funext i
          exact Fin.elim0 i
        simpa [hz] using hzero.le
      _ = C0 c / ((0 : ℕ) : ℝ) := by simp
  · exact (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (fun p z => p.1.mse_nonneg _ _) (contrastWeightedProcedure K n c)).trans
        (contrastWeightedProcedure_upperRisk K n c (Nat.pos_of_ne_zero hn))

-- @node: thm:universal-second-order-rate
/-- [there are at least two treatment arms](hyp:hK), [the contrast-score shrinkage procedure improves on the first-order risk by order $n^{-4/3}$ uniformly over response schedules](goal). -/
theorem universal_second_order_rate (K : ℕ) (c : Contrast ℝ K)
    (hK : AdmissibleArmCount K) :
    0 < lambdaC c ∧ lambdaC c ≤ 1 ∧ 0 < kappaC c ∧
    MinimaxEnvelopeBound K c ∧
    (∃ N : ℕ,
      (∀ m : ℕ, N ≤ m →
        4 * Real.sqrt (lambdaC c) * (m : ℝ) *
          Real.exp (-(m : ℝ) ^ (1 / 3 : ℝ) / 8) ≤
            Real.sqrt (lambdaC c) / 2 - lambdaC c / 16) ∧
      ∀ n ≥ N,
        Causalean.Stat.worstCaseRisk
          (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
          (shrinkageProcedure K n c) ≤
            C0 c * ((n : ℝ)⁻¹ - kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ)))) ∧
    C0 c * kappaC c ≤
      liminf (fun n => secondOrderScale n * dN K c n) atTop ∧
    liminf (fun n => secondOrderScale n * dN K c n) atTop ≤
      limsup (fun n => secondOrderScale n * dN K c n) atTop ∧
    limsup (fun n => secondOrderScale n * dN K c n) atTop ≤ 43 * C0 c ∧
    (∀ (a : PositiveSequence) β C,
      RegularlyVarying a β → 0 < C →
      Tendsto (fun n => a n * dN K c n) atTop (nhds C) → β = 4 / 3) := by
  rcases lambdaC_pos_le_one c with ⟨hlambda, hlambda1⟩
  have hkappa := kappaC_pos c
  have hA : 0 < Real.sqrt (lambdaC c) / 2 - lambdaC c / 16 := by
    have hs := Real.sq_sqrt hlambda.le
    nlinarith [Real.sqrt_nonneg (lambdaC c)]
  have htail0 : Tendsto (fun n : ℕ => 4 * Real.sqrt (lambdaC c) *
      ((n : ℝ) * Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8))) atTop (nhds 0) := by
    simpa using (shrinkage_tail_prefactor_tendsto_zero.const_mul
      (4 * Real.sqrt (lambdaC c)))
  have htailEv : ∀ᶠ n : ℕ in atTop, 4 * Real.sqrt (lambdaC c) * (n : ℝ) *
      Real.exp (-(n : ℝ) ^ (1 / 3 : ℝ) / 8) ≤
        Real.sqrt (lambdaC c) / 2 - lambdaC c / 16 := by
    have hev := (tendsto_order.1 htail0).2 _ hA
    filter_upwards [hev] with n hn
    simpa [mul_assoc] using hn.le
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 htailEv
  let N := max N0 1
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hrisk : ∀ n ≥ N,
      Causalean.Stat.worstCaseRisk
        (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
        (shrinkageProcedure K n c) ≤
          C0 c * ((n : ℝ)⁻¹ - kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
    intro n hn
    apply shrinkageProcedure_risk_bound_of_tail K n c (hNpos.trans_le hn)
    exact hN0 n ((le_max_left _ _).trans hn)
  have hthresholdWitness : ∃ N : ℕ,
      (∀ m : ℕ, N ≤ m →
        4 * Real.sqrt (lambdaC c) * (m : ℝ) *
          Real.exp (-(m : ℝ) ^ (1 / 3 : ℝ) / 8) ≤
            Real.sqrt (lambdaC c) / 2 - lambdaC c / 16) ∧
      ∀ n ≥ N,
        Causalean.Stat.worstCaseRisk
          (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
          (shrinkageProcedure K n c) ≤
            C0 c * ((n : ℝ)⁻¹ - kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
    exact ⟨N, fun m hm => hN0 m ((le_max_left N0 1).trans hm), hrisk⟩
  let f : ℕ → ℝ := fun n => secondOrderScale n * dN K c n
  have hflower : ∀ᶠ n in atTop, C0 c * kappaC c ≤ f n := by
    filter_upwards [Ici_mem_atTop N] with n hn
    have hnpos := hNpos.trans_le hn
    have hrho : rhoN K n c ≤ C0 c * ((n : ℝ)⁻¹ - kappaC c *
        (n : ℝ) ^ (-(4 / 3 : ℝ))) := by
      exact (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        (fun p z => p.1.mse_nonneg _ _) (shrinkageProcedure K n c)).trans (hrisk n hn)
    have hd : C0 c * kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ dN K c n := by
      have hsub := sub_le_sub_left hrho (C0 c / (n : ℝ))
      unfold dN
      convert hsub using 1 <;> ring
    have hs0 : 0 ≤ secondOrderScale n := by
      unfold secondOrderScale
      positivity
    have hm := mul_le_mul_of_nonneg_left hd hs0
    dsimp [f]
    calc
      C0 c * kappaC c = (secondOrderScale n *
          (n : ℝ) ^ (-(4 / 3 : ℝ))) * (C0 c * kappaC c) := by
            rw [secondOrderScale_mul_inverse n hnpos, one_mul]
      _ = secondOrderScale n * (C0 c * kappaC c *
          (n : ℝ) ^ (-(4 / 3 : ℝ))) := by ring
      _ ≤ secondOrderScale n * dN K c n := hm
  have hfupper : ∀ᶠ n in atTop, f n ≤ 43 * C0 c := by
    filter_upwards [Ici_mem_atTop 8] with n hn
    have hn8 : 8 ≤ n := hn
    have hnpos : 0 < n := by omega
    have hc := (embedded_two_arm_converse K n c hK hnpos).2.2.1 hn8
    have hd := hc.2.2
    have hs0 : 0 ≤ secondOrderScale n := by unfold secondOrderScale; positivity
    have hm := mul_le_mul_of_nonneg_left hd hs0
    dsimp [f]
    calc
      secondOrderScale n * dN K c n ≤ secondOrderScale n *
          (43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ))) := hm
      _ = 43 * C0 c := by rw [show secondOrderScale n *
          (43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ))) =
            (43 * C0 c) * (secondOrderScale n *
              (n : ℝ) ^ (-(4 / 3 : ℝ))) by ring,
          secondOrderScale_mul_inverse n hnpos, mul_one]
  have hf_bdd_above : IsBoundedUnder (· ≤ ·) atTop f :=
    isBoundedUnder_of_eventually_le hfupper
  have hf_bdd_below : IsBoundedUnder (· ≥ ·) atTop f :=
    isBoundedUnder_of_eventually_ge hflower
  have hli : C0 c * kappaC c ≤ liminf f atTop :=
    le_liminf_of_le (hf_bdd_above.isCoboundedUnder_ge) hflower
  have hls : limsup f atTop ≤ 43 * C0 c :=
    limsup_le_of_le (hf_bdd_below.isCoboundedUnder_le) hfupper
  have hil : liminf f atTop ≤ limsup f atTop :=
    liminf_le_limsup hf_bdd_above hf_bdd_below
  refine ⟨hlambda, hlambda1, hkappa, minimaxEnvelopeBound_of_contrastWeightedProcedure K c,
    hthresholdWitness, hli, hil, hls, ?_⟩
  intro a β C hreg hC hconv
  have hC0 : 0 < C0 c := by
    unfold C0
    positivity [Lc_pos c]
  let b : ℕ → ℝ := fun n => if n = 0 then 1 else
    a n * (n : ℝ) ^ (-(4 / 3 : ℝ))
  have hbpos : ∀ n, 0 < b n := by
    intro n
    by_cases hn : n = 0
    · simp [b, hn]
    · simp only [b, hn, ↓reduceIte]
      exact mul_pos (a.2 n) (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _)
  have hprod : ∀ᶠ n in atTop, b n * f n = a n * dN K c n := by
    filter_upwards [Ici_mem_atTop 1] with n hn
    have hnpos : 0 < n := hn
    simp only [b, ne_of_gt hnpos, ↓reduceIte, f]
    rw [show (a : ℕ → ℝ) n * (n : ℝ) ^ (-(4 / 3 : ℝ)) *
        (secondOrderScale n * dN K c n) = a n * dN K c n *
          (secondOrderScale n * (n : ℝ) ^ (-(4 / 3 : ℝ))) by ring,
      secondOrderScale_mul_inverse n hnpos, mul_one]
  have hqbounds : ∀ᶠ n in atTop, C / 2 ≤ a n * dN K c n ∧
      a n * dN K c n ≤ 2 * C := by
    have hl := (tendsto_order.1 hconv).1 (C / 2) (by linarith)
    have hu := (tendsto_order.1 hconv).2 (2 * C) (by linarith)
    exact hl.and hu |>.mono (fun _ h => ⟨h.1.le, h.2.le⟩)
  have hbbounds : ∀ᶠ n in atTop,
      C / (2 * (43 * C0 c)) ≤ b n ∧
      b n ≤ (2 * C) / (C0 c * kappaC c) := by
    filter_upwards [hflower, hfupper, hqbounds, hprod] with n hfl hfu hq hp
    have hb := (hbpos n).le
    have hlowden : 0 < C0 c * kappaC c := mul_pos hC0 hkappa
    have hupden : 0 < 2 * (43 * C0 c) := by positivity
    constructor
    · rw [← hp] at hq
      apply (div_le_iff₀ hupden).2
      nlinarith
    · rw [← hp] at hq
      apply (le_div_iff₀ hlowden).2
      nlinarith
  have haRatio := hreg 2 (by norm_num)
  have haRatio' : Tendsto (fun n : ℕ => a (2 * n) / a n) atTop
      (nhds ((2 : ℝ) ^ β)) := by
    convert haRatio using 1
    funext n
    congr 2
    have hcast : (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) := by norm_num
    rw [hcast, Nat.floor_natCast]
  have hbratio : Tendsto (fun n => b (2 * n) / b n) atTop
      (nhds ((2 : ℝ) ^ (β - 4 / 3))) := by
    have hmul := haRatio'.mul_const ((2 : ℝ) ^ (-(4 / 3 : ℝ)))
    have hmul' : Tendsto (fun n => b (2 * n) / b n) atTop
        (nhds ((2 : ℝ) ^ β * (2 : ℝ) ^ (-(4 / 3 : ℝ)))) := by
      apply hmul.congr'
      filter_upwards [Ici_mem_atTop 1] with n hn
      have hnpos : 0 < n := hn
      have h2npos : 0 < 2 * n := by omega
      simp only [b, ne_of_gt hnpos, ne_of_gt h2npos, ↓reduceIte]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      rw [show ((2 * n : ℕ) : ℝ) = (2 : ℝ) * n by norm_num,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnR.le]
      field_simp [ne_of_gt (a.2 n), ne_of_gt (Real.rpow_pos_of_pos hnR _)]
    convert hmul' using 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
  have hrpos : 0 < (2 : ℝ) ^ (β - 4 / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have hbindex := dyadic_ratio_limit_eq_one b ((2 : ℝ) ^ (β - 4 / 3)) hbpos hrpos
    ⟨C / (2 * (43 * C0 c)), (2 * C) / (C0 c * kappaC c), by positivity, hbbounds⟩
    hbratio
  have hexp : β - 4 / 3 = 0 := by
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
    simpa using hbindex
  linarith

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
