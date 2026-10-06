module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PhaseAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Limits of the matched scales and the strict finite-moment scale comparison. -/
public section

open Filter
open scoped Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Both matched scales are positive at every positive sample size. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: matched_scales_pos
lemma matched_scales_pos (n : ℕ) (hn : 0 < n) (v : Params) :
    0 < rho n v ∧ 0 < rhoBounded n v.toSmooth3 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact ⟨Real.rpow_pos_of_pos hn' _, Real.rpow_pos_of_pos hn' _⟩

/-- The finite-moment matched scale tends to zero because its exponent is positive. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: rho_tendsto_zero
lemma rho_tendsto_zero (v : Params) (hv : v.Valid) :
    Tendsto (fun n : ℕ => rho n v) atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop (exponent_phase_algebra v hv).2.2.1).comp
    tendsto_natCast_atTop_atTop

/-- The bounded matched scale tends to zero, including every phase boundary. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: rhoBounded_tendsto_zero
lemma rhoBounded_tendsto_zero (v : Params) (hv : v.Valid) :
    Tendsto (fun n : ℕ => rhoBounded n v.toSmooth3) atTop (nhds 0) := by
  apply rho_tendsto_zero
  exact ⟨by norm_num [Params.ofBounded], hv.2⟩

/-- Dividing the matched scales gives exactly the power of the exponent gap. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: matched_scale_ratio_eq
lemma matched_scale_ratio_eq (n : ℕ) (hn : 0 < n) (v : Params) :
    rho n v / rhoBounded n v.toSmooth3 =
      (n : ℝ) ^ (Eexp (Params.ofBounded v.toSmooth3) - Eexp v) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rhoBounded, rho, rho, ← Real.rpow_sub hn']
  congr 1
  ring

/-- Every strict finite-moment exponent gives a scale asymptotically larger than the bounded one. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: matched_scale_ratio_tendsto
lemma matched_scale_ratio_tendsto (v : Params) (hv : v.Valid) (hp : v.p < 2) :
    Tendsto (fun n : ℕ => rho n v / rhoBounded n v.toSmooth3) atTop atTop := by
  have hgap : 0 < Eexp (Params.ofBounded v.toSmooth3) - Eexp v :=
    sub_pos.mpr ((exponent_phase_algebra v hv).2.2.2.2.2.2.2.2.2 hp)
  have h := (tendsto_rpow_atTop hgap).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (matched_scale_ratio_eq n hn v).symm

/-- The lower multiplier remains strictly positive on both branches. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: cLower_pos
lemma cLower_pos (v : Params) (hv : v.Valid) : 0 < cLower v := by
  have hN : (0 : ℝ) < Nlow v := by
    have hb : (2 : ℝ) ≤ Nlow v := (le_max_left _ _).trans (Nat.le_ceil _)
    linarith
  unfold cLower kLow cOracle Hfine
  split <;> positivity

/-- The diverging ratio eventually places the finite-moment lower separation above any fixed bounded multiplier. This statement assumes [the hv condition](hyp:hv), [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: finite_scale_eventually_dominates_bounded
lemma finite_scale_eventually_dominates_bounded (v : Params) (hv : v.Valid)
    (hp : v.p < 2) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * rhoBounded n v.toSmooth3 ≤ cLower v * rho n v := by
  have hc := cLower_pos v hv
  have he := (matched_scale_ratio_tendsto v hv hp).eventually
    (eventually_ge_atTop (C / cLower v))
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hb := (matched_scales_pos n hn0 v).2
  have h := (le_div_iff₀ hb).mp hn
  have hC := mul_le_mul_of_nonneg_left h hc.le
  have hid : cLower v * (C / cLower v * rhoBounded n v.toSmooth3) =
      C * rhoBounded n v.toSmooth3 := by field_simp
  rw [hid] at hC
  exact hC

end CausalSmith.Stat.FinitepHomogeneityDensegamma
