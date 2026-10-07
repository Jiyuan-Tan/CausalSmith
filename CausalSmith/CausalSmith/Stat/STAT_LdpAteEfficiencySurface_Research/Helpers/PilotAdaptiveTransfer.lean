module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveAveraging

/-! # Finite pilot transfer lemmas for local limits and risks -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter
open scoped Topology BigOperators

/-- [the finite pilot conditional cdf tendsto assertion](goal) holds. For [the displayed quantities and conditions](hyp:w,F,L,hw,hsum,hF0,hF1,hL0,hL1,hbad), these specify the stated inputs. -/
lemma finitePilot_conditionalCDF_tendsto
    {P : ℕ → Type*} [∀ n, Fintype (P n)]
    (w : (n : ℕ) → P n → ℝ) (F : (n : ℕ) → P n → ℝ) (L : ℝ)
    (hw : ∀ n a, 0 ≤ w n a) (hsum : ∀ n, ∑ a, w n a = 1)
    (hF0 : ∀ n a, 0 ≤ F n a) (hF1 : ∀ n a, F n a ≤ 1)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hbad : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      ∑ a, w n a * if δ ≤ |F n a - L| then 1 else 0) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ a, w n a * F n a) atTop (𝓝 L) := by
  apply finitePilot_average_tendsto_of_badMass w F L hw hsum
  · intro n a
    rw [abs_le]
    exact ⟨by linarith [hF0 n a], hF1 n a⟩
  · rw [abs_le]
    exact ⟨by linarith, hL1⟩
  · exact hbad

/-- the finite pilot good bad average error le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hw,hsum,hL,hδ,hgood), [the finite Pilot good bad average error le](goal).

Under the stated assumptions, the finite Pilot good bad average error le. -/
lemma finitePilot_good_bad_average_error_le {P : Type*} [Fintype P]
    (w g : P → ℝ) (good : P → Prop) [DecidablePred good]
    (L δ : ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hgood : ∀ a, good a → |g a - L| ≤ δ) :
    |∑ a, w a * g a - L| ≤
      δ + ∑ a, w a * if good a then 0 else |g a - L| := by
  have hpoint (a : P) :
      w a * |g a - L| ≤
        w a * (δ + if good a then 0 else |g a - L|) := by
    apply mul_le_mul_of_nonneg_left _ (hw a)
    split_ifs with ha
    · simpa using hgood a ha
    · linarith [abs_nonneg (g a - L)]
  calc
    |∑ a, w a * g a - L| = |∑ a, w a * (g a - L)| := by
      congr 1
      calc
        ∑ a, w a * g a - L = ∑ a, w a * g a - L * ∑ a, w a := by
          rw [hsum]
          ring
        _ = ∑ a, w a * (g a - L) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ ≤ ∑ a, |w a * (g a - L)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w a * |g a - L| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (hw a)]
    _ ≤ ∑ a, w a * (δ + if good a then 0 else |g a - L|) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = δ + ∑ a, w a * if good a then 0 else |g a - L| := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
      ring

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- [the finite pilot good bad average tendsto assertion](goal) holds. For [the displayed quantities and conditions](hyp:w,g,good,L,hw,hsum,hL,hgood,hbad), these specify the stated inputs. -/
lemma finitePilot_good_bad_average_tendsto
    {P : ℕ → Type*} [∀ n, Fintype (P n)]
    (w g : (n : ℕ) → P n → ℝ) (good : (n : ℕ) → P n → Prop)
    [∀ n, DecidablePred (good n)] (L : ℝ)
    (hw : ∀ n a, 0 ≤ w n a) (hsum : ∀ n, ∑ a, w n a = 1)
    (hL : 0 ≤ L)
    (hgood : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ a, good n a → |g n a - L| ≤ δ)
    (hbad : Tendsto (fun n =>
      ∑ a, w n a * if good n a then 0 else |g n a - L|) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ a, w n a * g n a) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hgoodη := hgood (η / 2) (half_pos hη)
  have hbadη : ∀ᶠ n in atTop,
      (∑ a, w n a * if good n a then 0 else |g n a - L|) < η / 2 :=
    (tendsto_order.1 hbad).2 _ (half_pos hη)
  have hevent := hgoodη.and hbadη
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq]
    have hpair := hN n hn
    have hbound := finitePilot_good_bad_average_error_le
      (w n) (g n) (good n) L (η / 2) (hw n) (hsum n) hL
      (by positivity) hpair.1
    exact lt_of_le_of_lt hbound (by linarith [hpair.2])⟩

/-- Under [the supplied quantities and conditions](hyp:m), [the adaptive main scale tendsto one assertion](goal) holds. For [the displayed quantities and conditions](hyp:hsub), these specify the stated inputs. -/
lemma adaptive_mainScale_tendsto_one (m : ℕ → ℕ)
    (hsub : PilotSublinear m) :
    Tendsto (fun n : ℕ => (n : ℝ) / (adaptiveMainSize m n : ℝ))
      atTop (𝓝 1) := by
  have hratio := adaptiveMainSize_ratio_tendsto_one m hsub
  simpa only [inv_div, inv_one] using hratio.inv₀ one_ne_zero

/-- [the adaptive main scale mul tendsto assertion](goal) holds. For [the displayed quantities and conditions](hyp:hsub,ha), these specify the stated inputs. -/
lemma adaptive_mainScale_mul_tendsto {m : ℕ → ℕ}
    (hsub : PilotSublinear m) {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ((n : ℝ) / (adaptiveMainSize m n : ℝ)) * a n)
      atTop (𝓝 L) := by
  simpa using (adaptive_mainScale_tendsto_one m hsub).mul ha

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- [the adaptive sqrt scale mul tendsto assertion](goal) holds. For [the displayed quantities and conditions](hyp:hsub,ha), these specify the stated inputs. -/
lemma adaptive_sqrtScale_mul_tendsto {m : ℕ → ℕ}
    (hsub : PilotSublinear m) {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun n : ℕ =>
      Real.sqrt ((n : ℝ) / (adaptiveMainSize m n : ℝ)) * a n)
      atTop (𝓝 L) := by
  simpa using (adaptive_row_main_sqrt_ratio_tendsto_one m hsub).mul ha

end CausalSmith.Stat.LdpAteEfficiencySurface
