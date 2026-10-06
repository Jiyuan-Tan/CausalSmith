module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveModelFields

/-! # Finite pilot averaging and main-row scale transfer -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter
open scoped Topology BigOperators

/-- the finite pilot average error le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hw,hsum,hf,hL,hδ), [the finite Pilot average error le](goal).

Under the stated assumptions, the finite Pilot average error le. -/
lemma finitePilot_average_error_le {P : Type*} [Fintype P]
    (w f : P → ℝ) (L δ : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (hf : ∀ a, |f a| ≤ 1) (hL : |L| ≤ 1) (hδ : 0 ≤ δ) :
    |∑ a, w a * f a - L| ≤
      δ + 2 * ∑ a, w a * if δ ≤ |f a - L| then 1 else 0 := by
  have hpoint (a : P) :
      w a * |f a - L| ≤ w a *
        (δ + 2 * if δ ≤ |f a - L| then 1 else 0) := by
    apply mul_le_mul_of_nonneg_left _ (hw a)
    split_ifs with hbad
    · have hdiff : |f a - L| ≤ 2 := by
        calc
          |f a - L| ≤ |f a| + |L| := abs_sub _ _
          _ ≤ 2 := by linarith [hf a, hL]
      linarith
    · simpa [hbad] using (le_of_lt (lt_of_not_ge hbad))
  calc
    |∑ a, w a * f a - L| = |∑ a, w a * (f a - L)| := by
      congr 1
      calc
        ∑ a, w a * f a - L = ∑ a, w a * f a - L * ∑ a, w a := by rw [hsum]; ring
        _ = ∑ a, w a * (f a - L) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ ≤ ∑ a, |w a * (f a - L)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w a * |f a - L| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (hw a)]
    _ ≤ ∑ a, w a *
        (δ + 2 * if δ ≤ |f a - L| then 1 else 0) :=
      Finset.sum_le_sum fun a _ => hpoint a
    _ = δ + 2 * ∑ a, w a *
        if δ ≤ |f a - L| then 1 else 0 := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp_rw [show ∀ a : P, w a * (2 * if δ ≤ |f a - L| then 1 else 0) =
        2 * (w a * if δ ≤ |f a - L| then 1 else 0) by intro a; ring]
      rw [← Finset.mul_sum, hsum]
      ring

/-- [the finite pilot average tendsto of bad mass assertion](goal) holds. For [the displayed quantities and conditions](hyp:w,f,L,hw,hsum,hf,hL,hbad), these specify the stated inputs. -/
lemma finitePilot_average_tendsto_of_badMass
    {P : ℕ → Type*} [∀ n, Fintype (P n)]
    (w : (n : ℕ) → P n → ℝ) (f : (n : ℕ) → P n → ℝ) (L : ℝ)
    (hw : ∀ n a, 0 ≤ w n a) (hsum : ∀ n, ∑ a, w n a = 1)
    (hf : ∀ n a, |f n a| ≤ 1) (hL : |L| ≤ 1)
    (hbad : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      ∑ a, w n a * if δ ≤ |f n a - L| then 1 else 0) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ a, w n a * f n a) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hbadη := hbad (η / 2) (half_pos hη)
  have hevent : ∀ᶠ n in atTop,
      (∑ a, w n a * if η / 2 ≤ |f n a - L| then 1 else 0) < η / 4 :=
    (tendsto_order.1 hbadη).2 _ (by linarith)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq]
    have hbound := finitePilot_average_error_le (w n) (f n) L (η / 2)
      (hw n) (hsum n) (hf n) hL (by positivity)
    exact lt_of_le_of_lt hbound (by linarith [hN n hn])⟩

/-- For [the supplied quantities and conditions](hyp:m,n), the [adaptive main size](goal) is the mathematical object specified below. -/
def adaptiveMainSize (m : ℕ → ℕ) (n : ℕ) : ℕ :=
  n - adaptivePilotSize m n

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under [the supplied quantities and conditions](hyp:m,n), [the adaptive main size add pilot assertion](goal) holds. -/
lemma adaptiveMainSize_add_pilot (m : ℕ → ℕ) (n : ℕ) :
    adaptiveMainSize m n + adaptivePilotSize m n = n := by
  exact Nat.sub_add_cancel (adaptivePilotSize_le m n)

/-- Under [the supplied quantities and conditions](hyp:m), [the adaptive main size ratio tendsto one assertion](goal) holds. For [the displayed quantities and conditions](hyp:hsub), these specify the stated inputs. -/
lemma adaptiveMainSize_ratio_tendsto_one (m : ℕ → ℕ)
    (hsub : PilotSublinear m) :
    Tendsto (fun n => (adaptiveMainSize m n : ℝ) / n) atTop (𝓝 1) := by
  have hpilot := adaptivePilotSize_sublinear m hsub
  have ht : Tendsto (fun n => (1 : ℝ) - (adaptivePilotSize m n : ℝ) / n)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hpilot
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [adaptiveMainSize, Nat.cast_sub (adaptivePilotSize_le m n)]
  field_simp

/-- Under [the supplied quantities and conditions](hyp:m), [the adaptive main size tendsto at top assertion](goal) holds. For [the displayed quantities and conditions](hyp:hsub), these specify the stated inputs. -/
lemma adaptiveMainSize_tendsto_atTop (m : ℕ → ℕ)
    (hsub : PilotSublinear m) :
    Tendsto (adaptiveMainSize m) atTop atTop := by
  have hratio := adaptiveMainSize_ratio_tendsto_one m hsub
  have hreal : Tendsto (fun n => (adaptiveMainSize m n : ℝ)) atTop atTop := by
    have hprod := hratio.pos_mul_atTop zero_lt_one tendsto_natCast_atTop_atTop
    apply hprod.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    change (adaptiveMainSize m n : ℝ) / n * n = adaptiveMainSize m n
    rw [div_mul_cancel₀]
    exact_mod_cast hn
  exact tendsto_natCast_atTop_iff.mp hreal

/-- Under [the supplied quantities and conditions](hyp:m), [the adaptive row main sqrt ratio tendsto one assertion](goal) holds. For [the displayed quantities and conditions](hyp:hsub), these specify the stated inputs. -/
lemma adaptive_row_main_sqrt_ratio_tendsto_one (m : ℕ → ℕ)
    (hsub : PilotSublinear m) :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / (adaptiveMainSize m n : ℝ)))
      atTop (𝓝 1) := by
  have hratio := adaptiveMainSize_ratio_tendsto_one m hsub
  have hinv : Tendsto (fun n : ℕ => ((adaptiveMainSize m n : ℝ) / n)⁻¹)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using hratio.inv₀ one_ne_zero
  have hinv' : Tendsto
      (fun n : ℕ => (n : ℝ) / (adaptiveMainSize m n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_div] using hinv
  convert (Real.continuous_sqrt.tendsto 1).comp hinv' using 1 <;>
    simp [Function.comp_def]

end CausalSmith.Stat.LdpAteEfficiencySurface
