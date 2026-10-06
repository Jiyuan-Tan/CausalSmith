module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Procedure
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


-- @env: S5
variable (β σ : ℝ) (n : ℕ)
/-- Piecewise continuous endpoint noise cost. Given [the displayed inputs and assumptions](hyp:h,σ), [this definition specifies the stated object](goal). -/
def noiseCost (h σ : ℝ) : ℝ := -- @realizes Noisecost(piecewise endpoint cost)
  if σ ≤ h then 0 else if σ ^ 4 ≤ h then (σ / h) ^ (2 / 3 : ℝ) - 1
  else h ^ (-1 / 2 : ℝ) * (1 + Real.log (σ ^ 2 / Real.sqrt h)) - 1
/-- Noiseless endpoint resolution. Given [the displayed inputs and assumptions](hyp:β,n), [this definition specifies the stated object](goal). -/
def directResolution (β : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-1 / (2 * β + 1))
/-- A supremum construction of the root, whose existence and uniqueness are proof obligations. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def rateResolution (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ := -- @realizes Rateresolution(root construction)
  sSup {h ∈ Icc (directResolution β n) 1 |
    Real.log n + (2 * β + 1) * Real.log h - noiseCost h σ ≤ 0}
/-- Endpoint frontier rate. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
def frontierRate (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ := -- @realizes Frontier(root to Holder power)
  rateResolution β n σ ^ β
/-- Rate and selected observable procedures. Given [the displayed inputs and assumptions](hyp:β,n,σ), [this definition specifies the stated object](goal). -/
-- @node: def:uniform-rate
def uniformRate (β : ℝ) (n : ℕ) (σ : ℝ) : ℝ × Estimator n × IntervalProc n :=
  (frontierRate β n σ, attainer β n σ, honestAttainer β n σ)
/-- Each branch of the public noise cost is nonnegative on its stated domain. Given [the displayed inputs and assumptions](hyp:h,σ,hh,hσ), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_nonneg (h σ : ℝ) (hh : h ∈ Ioc (0 : ℝ) 1)
    (hσ : σ ∈ Icc (0 : ℝ) 1) : 0 ≤ noiseCost h σ := by
  unfold noiseCost
  split_ifs with hdirect hpower
  · exact le_rfl
  · have hratio : 1 ≤ σ / h := (le_div_iff₀ hh.1).2 (by linarith)
    have hpow := Real.one_le_rpow hratio (by norm_num : (0 : ℝ) ≤ 2/3)
    linarith
  · have hsqrt : Real.sqrt h ≤ σ ^ 2 := by
      have hsq := Real.sq_sqrt hh.1.le
      have hroot := Real.sqrt_nonneg h
      have hfour : h < (σ ^ 2)^2 := by
        calc h < σ ^ 4 := lt_of_not_ge hpower
             _ = (σ ^ 2)^2 := by ring
      nlinarith [sq_nonneg σ]
    have hlog : 0 ≤ Real.log (σ ^ 2 / Real.sqrt h) :=
      Real.log_nonneg ((le_div_iff₀ (Real.sqrt_pos.2 hh.1)).2 (by simpa using hsqrt))
    have hfactor : 1 ≤ h ^ (-1 / 2 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh.1 hh.2 (by norm_num)
    have hproduct : 1 ≤ h ^ (-1 / 2 : ℝ) * (1 + Real.log (σ ^ 2 / Real.sqrt h)) := by
      calc 1 = 1 * 1 := by norm_num
           _ ≤ _ := mul_le_mul hfactor (by linarith) (by norm_num) (by linarith)
    linarith

/-- The two nonzero cost branches agree at the compact-support interface. Given [the displayed inputs and assumptions](hyp:σ,hσ), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_compact_interface (σ : ℝ) (hσ : 0 < σ) :
    (σ / σ^4) ^ (2/3 : ℝ) - 1 =
      (σ^4) ^ (-1/2 : ℝ) * (1 + Real.log (σ^2 / Real.sqrt (σ^4))) - 1 := by
  have hsqrt : Real.sqrt (σ^4) = σ^2 := by
    rw [show σ^4 = (σ^2)^2 by ring, Real.sqrt_sq (sq_nonneg σ)]
  rw [hsqrt, div_self (pow_ne_zero 2 hσ.ne'), Real.log_one]
  simp only [add_zero, mul_one]
  congr 1
  rw [Real.div_rpow hσ.le (pow_nonneg hσ.le 4),
    ← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ.le,
    ← Real.rpow_sub hσ, ← Real.rpow_mul hσ.le]
  congr 1 <;> norm_num

/-- Gluing the explicit branches gives continuity on the positive resolution domain. Given [the displayed inputs and assumptions](hyp:σ,hσ), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_continuousOn (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun h => noiseCost h σ) (Ioc 0 1) := by
  by_cases hz : σ = 0
  · subst σ
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioc 0 1)).congr
      (fun h hh => by simp [noiseCost, hh.1.le])
  have hpos : 0 < σ := lt_of_le_of_ne hσ.1 (Ne.symm hz)
  have hc : Continuous (fun h : Ioi (0 : ℝ) => noiseCost h σ) := by
    unfold noiseCost
    apply continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop)
    · apply Continuous.continuousOn
      apply continuous_if_le (by fun_prop) (by fun_prop)
      · have : Continuous (fun h : Ioi (0 : ℝ) => (σ / (h : ℝ)) ^ (2/3 : ℝ) - 1) := by
          exact ((continuous_const.div continuous_subtype_val
            (fun h => h.property.ne')).rpow_const (fun _ => Or.inr (by norm_num))).sub
            continuous_const
        exact this.continuousOn
      · have : Continuous (fun h : Ioi (0 : ℝ) =>
            (h : ℝ) ^ (-1/2 : ℝ) * (1 + Real.log (σ^2 / Real.sqrt (h : ℝ))) - 1) := by
          have hne : ∀ h : Ioi (0 : ℝ), (h : ℝ) ≠ 0 := fun h => h.property.ne'
          have hsqrt : ∀ h : Ioi (0 : ℝ), Real.sqrt (h : ℝ) ≠ 0 :=
            fun h => (Real.sqrt_pos.2 h.property).ne'
          have hp : Continuous (fun h : Ioi (0 : ℝ) => (h : ℝ) ^ (-1/2 : ℝ)) :=
            continuous_subtype_val.rpow_const (fun h => Or.inl (hne h))
          have hl : Continuous (fun h : Ioi (0 : ℝ) => Real.log (σ^2 / Real.sqrt (h : ℝ))) :=
            (continuous_const.div (Real.continuous_sqrt.comp continuous_subtype_val) hsqrt).log
              (fun h => div_ne_zero (pow_ne_zero 2 hpos.ne') (hsqrt h))
          exact (hp.mul (continuous_const.add hl)).sub continuous_const
        exact this.continuousOn
      · intro h heq
        simpa only [← heq] using noiseCost_compact_interface σ hpos
    · intro h heq
      have hfour : σ^4 ≤ σ := by
        calc σ^4 ≤ σ^1 := pow_le_pow_of_le_one hσ.1 hσ.2 (by omega)
             _ = σ := pow_one _
      simp [← heq, hfour, div_self hpos.ne']
  exact (continuousOn_iff_continuous_restrict.mpr hc).mono (fun h hh => hh.1)

/-- The compact branch decreases as resolution increases below its interface. Given [the displayed inputs and assumptions](hyp:h,t,σ,hh,hht,ht,hσ), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_compact_antitone (h t σ : ℝ) (hh : 0 < h) (hht : h ≤ t)
    (ht : t ≤ σ^4) (hσ : 0 < σ) :
    t ^ (-1/2 : ℝ) * (1 + Real.log (σ^2 / Real.sqrt t)) - 1 ≤
      h ^ (-1/2 : ℝ) * (1 + Real.log (σ^2 / Real.sqrt h)) - 1 := by
  have htpos : 0 < t := lt_of_lt_of_le hh hht
  have hsqrt : Real.sqrt t ≤ σ^2 := by
    have hsq := Real.sq_sqrt htpos.le
    have hroot := Real.sqrt_nonneg t
    have ht' : t ≤ (σ^2)^2 := by nlinarith [ht]
    nlinarith [sq_nonneg σ]
  have hlogt : 0 ≤ Real.log (σ^2 / Real.sqrt t) :=
    Real.log_nonneg ((le_div_iff₀ (Real.sqrt_pos.2 htpos)).2 (by simpa using hsqrt))
  have hlog : Real.log (σ^2 / Real.sqrt t) ≤ Real.log (σ^2 / Real.sqrt h) :=
    Real.log_le_log (div_pos (sq_pos_of_pos hσ) (Real.sqrt_pos.2 htpos))
      (div_le_div_of_nonneg_left (sq_nonneg σ) (Real.sqrt_pos.2 hh)
        (Real.sqrt_le_sqrt hht))
  have hp := Real.rpow_le_rpow_of_nonpos hh hht (by norm_num : (-1/2 : ℝ) ≤ 0)
  have hm := mul_le_mul hp (show 1 + Real.log (σ^2 / Real.sqrt t) ≤
    1 + Real.log (σ^2 / Real.sqrt h) by linarith) (by linarith :
    0 ≤ 1 + Real.log (σ^2 / Real.sqrt t)) (Real.rpow_nonneg hh.le _)
  linarith

/-- The power branch decreases on positive resolutions. Given [the displayed inputs and assumptions](hyp:h,t,σ,hh,hht,hσ), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_power_antitone (h t σ : ℝ) (hh : 0 < h) (hht : h ≤ t)
    (hσ : 0 ≤ σ) :
    (σ/t) ^ (2/3 : ℝ) - 1 ≤ (σ/h) ^ (2/3 : ℝ) - 1 := by
  apply sub_le_sub_right
  exact Real.rpow_le_rpow (div_nonneg hσ (lt_of_lt_of_le hh hht).le)
    (div_le_div_of_nonneg_left hσ hh hht) (by norm_num)

/-- Branchwise comparisons and interface agreement give global monotonicity. Given [the displayed inputs and assumptions](hyp:σ,hσ), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_antitoneOn (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (fun h => noiseCost h σ) (Ioc 0 1) := by
  intro h hh t ht hht
  by_cases hd : σ ≤ h
  · simp [noiseCost, hd, hd.trans hht]
  by_cases td : σ ≤ t
  · simpa [noiseCost, td] using noiseCost_nonneg h σ hh hσ
  have hpos : 0 < σ := lt_trans hh.1 (lt_of_not_ge hd)
  by_cases hp : σ^4 ≤ h
  · simp only [noiseCost, if_neg hd, if_neg td, if_pos hp, if_pos (hp.trans hht)]
    exact noiseCost_power_antitone h t σ hh.1 hht hσ.1
  by_cases tp : σ^4 ≤ t
  · simp only [noiseCost, if_neg hd, if_neg td, if_neg hp, if_pos tp]
    calc
      (σ/t) ^ (2/3 : ℝ) - 1 ≤ (σ/σ^4) ^ (2/3 : ℝ) - 1 :=
        noiseCost_power_antitone (σ^4) t σ (pow_pos hpos 4) tp hσ.1
      _ = (σ^4) ^ (-1/2 : ℝ) * (1 + Real.log (σ^2 / Real.sqrt (σ^4))) - 1 :=
        noiseCost_compact_interface σ hpos
      _ ≤ _ := noiseCost_compact_antitone h (σ^4) σ hh.1 (le_of_not_ge hp) le_rfl hpos
  · simp only [noiseCost, if_neg hd, if_neg td, if_neg hp, if_neg tp]
    exact noiseCost_compact_antitone h t σ hh.1 hht (le_of_not_ge tp) hpos

/-- The power expression also holds at the direct-branch endpoint. Given [the displayed inputs and assumptions](hyp:h,σ,hh,hp,ht), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_one_power (h σ : ℝ) (hh : 0 < h) (hp : σ^4 ≤ h)
    (ht : h ≤ σ) : 1 + noiseCost h σ = (σ/h) ^ (2/3 : ℝ) := by
  by_cases hd : σ ≤ h
  · have heq : σ = h := le_antisymm hd ht
    subst σ
    simp [noiseCost, div_self hh.ne']
  · simp [noiseCost, hd, hp]

/-- The compact expression agrees with the power expression at their interface. Given [the displayed inputs and assumptions](hyp:h,σ,hh,hp,hσ,hspos), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_one_compact (h σ : ℝ) (hh : 0 < h) (hp : h ≤ σ^4)
    (hσ : σ ≤ 1) (hspos : 0 < σ) :
    1 + noiseCost h σ = h ^ (-1/2 : ℝ) * (1 + Real.log (σ^2 / Real.sqrt h)) := by
  have hfour : σ^4 ≤ σ := by
    calc σ^4 ≤ σ^1 := pow_le_pow_of_le_one hspos.le hσ (by omega)
         _ = σ := pow_one _
  by_cases heq : h = σ^4
  · rw [heq, noiseCost_one_power _ _ (pow_pos hspos 4) le_rfl hfour]
    have hi := noiseCost_compact_interface σ hspos
    linarith
  · have hp' : h < σ^4 := lt_of_le_of_ne hp heq
    simp [noiseCost, not_le.mpr (hp'.trans_le hfour), not_le.mpr hp']

/-- On the power branch the multiplicative cost ratio is a two-thirds power. Given [the displayed inputs and assumptions](hyp:h,t,σ,hh,hht,hp,ht), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_power_comparison (h t σ : ℝ) (hh : 0 < h) (hht : h ≤ t)
    (hp : σ^4 ≤ h) (ht : t ≤ σ) :
    (t/h) ^ (1/2 : ℝ) * (1 + noiseCost t σ) ≤ 1 + noiseCost h σ ∧
    1 + noiseCost h σ ≤ (t/h) * (1 + noiseCost t σ) := by
  have htpos := lt_of_lt_of_le hh hht
  have hspos := lt_of_lt_of_le htpos ht
  rw [noiseCost_one_power h σ hh hp (hht.trans ht),
    noiseCost_one_power t σ htpos (hp.trans hht) ht]
  have heq : (σ/h) ^ (2/3 : ℝ) = (t/h) ^ (2/3 : ℝ) * (σ/t) ^ (2/3 : ℝ) := by
    rw [← Real.mul_rpow (div_nonneg htpos.le hh.le) (div_nonneg hspos.le htpos.le)]
    congr 1
    field_simp
  rw [heq]
  have hr : 1 ≤ t/h := (le_div_iff₀ hh).2 (by simpa using hht)
  constructor
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hr (by norm_num)) (Real.rpow_nonneg (by positivity) _)
  · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    simpa using Real.rpow_le_rpow_of_exponent_le hr (show (2/3 : ℝ) ≤ 1 by norm_num)

/-- On the compact branch the logarithmic factor grows between zero and the square-root ratio.
The bound log r ≤ r - 1 is the integrated upper derivative bound in the roadmap. Given [the displayed inputs and assumptions](hyp:h,t,σ,hh,hht,ht,hσ,hspos), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_compact_comparison (h t σ : ℝ) (hh : 0 < h) (hht : h ≤ t)
    (ht : t ≤ σ^4) (hσ : σ ≤ 1) (hspos : 0 < σ) :
    (t/h) ^ (1/2 : ℝ) * (1 + noiseCost t σ) ≤ 1 + noiseCost h σ ∧
    1 + noiseCost h σ ≤ (t/h) * (1 + noiseCost t σ) := by
  have htpos := lt_of_lt_of_le hh hht
  rw [noiseCost_one_compact h σ hh (hht.trans ht) hσ hspos,
    noiseCost_one_compact t σ htpos ht hσ hspos]
  let r : ℝ := Real.sqrt t / Real.sqrt h
  have sh := Real.sqrt_pos.2 hh
  have st := Real.sqrt_pos.2 htpos
  have hrpos : 0 < r := div_pos st sh
  have hr : 1 ≤ r := (le_div_iff₀ sh).2 (by simpa [r] using Real.sqrt_le_sqrt hht)
  have hroot : Real.sqrt t ≤ σ^2 := by
    have := Real.sq_sqrt htpos.le
    have : t ≤ (σ^2)^2 := by nlinarith [ht]
    nlinarith [Real.sqrt_nonneg t, sq_nonneg σ]
  have hl : 0 ≤ Real.log (σ^2 / Real.sqrt t) :=
    Real.log_nonneg ((le_div_iff₀ st).2 (by simpa using hroot))
  have hlog : Real.log (σ^2 / Real.sqrt h) =
      Real.log (σ^2 / Real.sqrt t) + Real.log r := by
    rw [← Real.log_mul (div_ne_zero (pow_ne_zero 2 hspos.ne') st.ne') hrpos.ne']
    congr 1
    dsimp [r]
    field_simp
  have hlow : 1 + Real.log (σ^2 / Real.sqrt t) ≤ 1 + Real.log (σ^2 / Real.sqrt h) := by
    rw [hlog]
    linarith [Real.log_nonneg hr]
  have hupp : 1 + Real.log (σ^2 / Real.sqrt h) ≤ r * (1 + Real.log (σ^2 / Real.sqrt t)) := by
    rw [hlog]
    have := Real.log_le_sub_one_of_pos hrpos
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hl]
  have hp (x : ℝ) (hx : 0 < x) : x ^ (-1/2 : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by norm_num, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  have hratio : (t/h) ^ (1/2 : ℝ) = r := by
    rw [Real.div_rpow htpos.le hh.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rw [hp h hh, hp t htpos, hratio]
  constructor
  · have := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr sh.le)
    dsimp [r]
    convert! this using 1
    field_simp [sh.ne', st.ne']
  · have := mul_le_mul_of_nonneg_left hupp (inv_nonneg.mpr sh.le)
    dsimp [r] at this
    convert! this using 1
    field_simp [sh.ne', st.ne', hh.ne']
    nlinarith [Real.sq_sqrt hh.le, Real.sq_sqrt htpos.le]

/-- Multiplicative branch comparisons compose across an intermediate resolution. Given [the displayed inputs and assumptions](hyp:h,u,t,σ,hh,hu,ht,hhu,hut), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_comparison_trans (h u t σ : ℝ) (hh : 0 < h) (hu : 0 < u) (ht : 0 < t)
    (hhu : (u/h) ^ (1/2 : ℝ) * (1 + noiseCost u σ) ≤ 1 + noiseCost h σ ∧
      1 + noiseCost h σ ≤ (u/h) * (1 + noiseCost u σ))
    (hut : (t/u) ^ (1/2 : ℝ) * (1 + noiseCost t σ) ≤ 1 + noiseCost u σ ∧
      1 + noiseCost u σ ≤ (t/u) * (1 + noiseCost t σ)) :
    (t/h) ^ (1/2 : ℝ) * (1 + noiseCost t σ) ≤ 1 + noiseCost h σ ∧
    1 + noiseCost h σ ≤ (t/h) * (1 + noiseCost t σ) := by
  have heq : t/h = (u/h) * (t/u) := by field_simp
  constructor
  · calc
      _ = (u/h) ^ (1/2 : ℝ) * ((t/u) ^ (1/2 : ℝ) * (1 + noiseCost t σ)) := by
        rw [heq, Real.mul_rpow (by positivity) (by positivity), mul_assoc]
      _ ≤ (u/h) ^ (1/2 : ℝ) * (1 + noiseCost u σ) :=
        mul_le_mul_of_nonneg_left hut.1 (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := hhu.1
  · calc
      _ ≤ (u/h) * (1 + noiseCost u σ) := hhu.2
      _ ≤ (u/h) * ((t/u) * (1 + noiseCost t σ)) :=
        mul_le_mul_of_nonneg_left hut.2 (by positivity)
      _ = _ := by rw [heq, mul_assoc]

/-- Joining the two explicit branch estimates yields the full ratio bounds. Given [the displayed inputs and assumptions](hyp:h,t,σ,hh,hht,htσ,hσ), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_ratio_bounds (h t σ : ℝ) (hh : 0 < h) (hht : h ≤ t)
    (htσ : t ≤ σ) (hσ : σ ≤ 1) :
    (t/h) ^ (1/2 : ℝ) ≤ (1 + noiseCost h σ) / (1 + noiseCost t σ) ∧
    (1 + noiseCost h σ) / (1 + noiseCost t σ) ≤ t/h := by
  have htpos := lt_of_lt_of_le hh hht
  have hspos := lt_of_lt_of_le htpos htσ
  have hFpos : 0 < 1 + noiseCost t σ := by
    have := noiseCost_nonneg t σ ⟨htpos, htσ.trans hσ⟩ ⟨hspos.le, hσ⟩
    linarith
  have hcomp : (t/h) ^ (1/2 : ℝ) * (1 + noiseCost t σ) ≤ 1 + noiseCost h σ ∧
      1 + noiseCost h σ ≤ (t/h) * (1 + noiseCost t σ) := by
    by_cases hp : σ^4 ≤ h
    · exact noiseCost_power_comparison h t σ hh hht hp htσ
    by_cases tp : t ≤ σ^4
    · exact noiseCost_compact_comparison h t σ hh hht tp hσ hspos
    · exact noiseCost_comparison_trans h (σ^4) t σ hh (pow_pos hspos 4) htpos
        (noiseCost_compact_comparison h (σ^4) σ hh (le_of_not_ge hp) le_rfl hσ hspos)
        (noiseCost_power_comparison (σ^4) t σ (pow_pos hspos 4) (le_of_not_ge tp) le_rfl htσ)
  exact ⟨(le_div_iff₀ hFpos).2 hcomp.1, (div_le_iff₀ hFpos).2 hcomp.2⟩

/-- The lower ratio estimate gives dilation decay until the direct branch is reached. Given [the displayed inputs and assumptions](hyp:hratio,h,σ,a,hh,hσ,ha,hah), [the stated mathematical conclusion holds](goal). -/
lemma noiseCost_dilation_of_lower_ratio
    (hratio : ∀ h t σ : ℝ, 0 < h → h ≤ t → t ≤ σ → σ ≤ 1 →
      (t/h) ^ (1/2 : ℝ) ≤ (1 + noiseCost h σ) / (1 + noiseCost t σ))
    (h σ a : ℝ) (hh : h ∈ Ioc (0 : ℝ) 1) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (ha : 1 ≤ a) (hah : a*h ≤ 1) :
    1 + noiseCost (a*h) σ ≤ max 1 (a ^ (-1/2 : ℝ) * (1 + noiseCost h σ)) := by
  by_cases hdirect : σ ≤ a*h
  · simpa [noiseCost, hdirect] using
      (le_max_left (1 : ℝ) (a ^ (-1/2 : ℝ) * (1 + noiseCost h σ)))
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hahpos : 0 < a*h := mul_pos hapos hh.1
  have hht : h ≤ a*h := by nlinarith [hh.1]
  have hFpos : 0 < 1 + noiseCost (a*h) σ := by
    have := noiseCost_nonneg (a*h) σ ⟨hahpos, hah⟩ hσ
    linarith
  have hr := hratio h (a*h) σ hh.1 hht (le_of_not_ge hdirect) hσ.2
  rw [mul_div_cancel_right₀ a hh.1.ne'] at hr
  have hprod : a ^ (1/2 : ℝ) * (1 + noiseCost (a*h) σ) ≤ 1 + noiseCost h σ :=
    (le_div_iff₀ hFpos).mp hr
  have hinv : a ^ (-1/2 : ℝ) * a ^ (1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hapos]
    norm_num
  apply le_trans _ (le_max_right _ _)
  calc
    1 + noiseCost (a*h) σ =
        (a ^ (-1/2 : ℝ) * a ^ (1/2 : ℝ)) * (1 + noiseCost (a*h) σ) := by rw [hinv, one_mul]
    _ = a ^ (-1/2 : ℝ) * (a ^ (1/2 : ℝ) * (1 + noiseCost (a*h) σ)) := by ring
    _ ≤ a ^ (-1/2 : ℝ) * (1 + noiseCost h σ) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hapos.le _)

/-- Continuity, monotonicity and both scalar scaling inequalities. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
-- @node: lem:noise-cost-scaling
lemma noise_cost_scaling :
    (∀ σ ∈ Icc (0 : ℝ) 1, ContinuousOn (fun h => noiseCost h σ) (Ioc 0 1) ∧
      (∀ h ∈ Ioc (0 : ℝ) 1, 0 ≤ noiseCost h σ) ∧
      AntitoneOn (fun h => noiseCost h σ) (Ioc 0 1)) ∧
    (∀ h t σ : ℝ, 0 < h → h ≤ t → t ≤ σ → σ ≤ 1 →
      (t/h) ^ (1/2 : ℝ) ≤ (1 + noiseCost h σ) / (1 + noiseCost t σ) ∧
      (1 + noiseCost h σ) / (1 + noiseCost t σ) ≤ t/h) ∧
    (∀ h σ a : ℝ, h ∈ Ioc (0 : ℝ) 1 → σ ∈ Icc (0 : ℝ) 1 →
      1 ≤ a → a*h ≤ 1 →
      1 + noiseCost (a*h) σ ≤ max 1 (a ^ (-1/2 : ℝ) * (1 + noiseCost h σ))) := by
  refine ⟨?_, ?_⟩
  · intro σ hσ
    refine ⟨?_, fun h hh => noiseCost_nonneg h σ hh hσ, ?_⟩
    · exact noiseCost_continuousOn σ hσ
    · exact noiseCost_antitoneOn σ hσ
  · have hratio : ∀ h t σ : ℝ, 0 < h → h ≤ t → t ≤ σ → σ ≤ 1 →
        (t/h) ^ (1/2 : ℝ) ≤ (1 + noiseCost h σ) / (1 + noiseCost t σ) ∧
        (1 + noiseCost h σ) / (1 + noiseCost t σ) ≤ t/h := by
      exact noiseCost_ratio_bounds
    refine ⟨hratio, ?_⟩
    exact noiseCost_dilation_of_lower_ratio
      (fun h t σ hh hht htσ hσ => (hratio h t σ hh hht htσ hσ).1)

end CausalSmith.Stat.RdTruesideNoiseFrontier
