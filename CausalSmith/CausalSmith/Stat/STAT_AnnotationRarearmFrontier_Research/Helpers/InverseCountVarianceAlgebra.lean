module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Numerical cell envelopes for the inverse-count Poisson variance calculation.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

/-- [Under the stated inputs and conditions](hyp:hs,hv,heps,hoverlap,s,v,eps), Overlap controls the squared opposite-arm mass divided by the current-arm mass.  This gives [the stated result](goal).-/
-- @node: inverse_count_overlap_ratio_bound
lemma inverse_count_overlap_ratio_bound (s v eps : Real)
    (hs : 0 < s) (hv : 0 ≤ v) (heps : 0 < eps)
    (hoverlap : eps * (s + v) ≤ s) :
    v ^ 2 / s ≤ (s + v) / eps := by
  apply (div_le_div_iff₀ hs heps).2
  have hvs : eps * v ≤ s := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hvs hv
  nlinarith [sq_nonneg s]

/-- [Under the stated inputs and conditions](hyp:hs,hv,ht,s,v,t), The four rational factors in the Poisson second-moment and variance bounds.  This gives [the stated result](goal).-/
-- @node: inverse_count_rational_factors
lemma inverse_count_rational_factors (s v t : Real)
    (hs : 0 < s) (hv : 0 ≤ v) (ht : 0 < t) :
    s * (t * v) ^ 2 / (1 + t * s) ^ 2 ≤ v ^ 2 / s ∧
    s * (t * v) / (1 + t * s) ^ 2 ≤ v ∧
    s ^ 2 * (t * v) / (1 + t * s) ^ 2 ≤ v / t ∧
    s ^ 2 * (t * v) ^ 2 * (t * s) / (1 + t * s) ^ 4 ≤ v ^ 2 / (t * s) := by
  have hd : 0 < 1 + t * s := by positivity
  have hr0 : 0 ≤ t * s / (1 + t * s) := by positivity
  have hr1 : t * s / (1 + t * s) ≤ 1 := (div_le_one hd).2 (by linarith)
  have hr2 : (t * s / (1 + t * s)) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hr0 hr1 2
  have hr4 : (t * s / (1 + t * s)) ^ 4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hr0 hr1 4
  have hsquare : t * s ≤ (1 + t * s) ^ 2 := by nlinarith [sq_nonneg (t * s)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = (v ^ 2 / s) * (t * s / (1 + t * s)) ^ 2 := by field_simp
      _ ≤ (v ^ 2 / s) * 1 := mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = _ := mul_one _
  · apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    nlinarith [mul_le_mul_of_nonneg_right hsquare hv]
  · calc
      _ = (v / t) * (t * s / (1 + t * s)) ^ 2 := by field_simp
      _ ≤ (v / t) * 1 := mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = _ := mul_one _
  · calc
      _ = (v ^ 2 / (t * s)) * (t * s / (1 + t * s)) ^ 4 := by field_simp
      _ ≤ (v ^ 2 / (t * s)) * 1 := mul_le_mul_of_nonneg_left hr4 (by positivity)
      _ = _ := mul_one _

/-- [Under the stated inputs and conditions](hyp:hs,hv,hq,hqs,hu,ht,heps,hC,hoverlap,s,v,q,u,t,eps,C0), The cell second-moment and variance envelopes are uniform even when the arm mass is zero.  This gives [the stated result](goal).-/
-- @node: inverse_count_cell_variance_envelope
lemma inverse_count_cell_variance_envelope (s v q u t eps C0 : Real)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hq : 0 ≤ q) (hqs : q ≤ s)
    (hu : 0 < u) (ht : 0 < t) (heps : 0 < eps)
    (hC : 0 ≤ C0) (hoverlap : eps * (s + v) ≤ s) :
    q / u * (2 + 2 * C0 * ((t * v) ^ 2 + t * v) / (1 + t * s) ^ 2) +
      q ^ 2 * C0 * (t * v / (1 + t * s) ^ 2 +
        (t * v) ^ 2 * (t * s) / (1 + t * s) ^ 4) ≤
      (2 + 4 * C0) * (s + v) * (1 / (u * eps) + 1 / (t * eps)) := by
  by_cases hz : s = 0
  · have hq0 : q = 0 := by linarith
    have hv0 : v = 0 := by rw [hz] at hoverlap; nlinarith
    simp [hz, hq0, hv0]
  have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
  have hp : 0 ≤ s + v := by positivity
  have hd : 0 < 1 + t * s := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := inverse_count_rational_factors s v t hs0 hv ht
  have hr := inverse_count_overlap_ratio_bound s v eps hs0 hv heps hoverlap
  have hpE : s + v ≤ (s + v) / eps := (le_div_iff₀ heps).2 (by nlinarith)
  have hvE : v ≤ (s + v) / eps := (by linarith : v ≤ s + v).trans hpE
  have hqE : q ≤ (s + v) / eps := hqs.trans ((by linarith : s ≤ s + v).trans hpE)
  have hsecond : q * (((t * v) ^ 2 + t * v) / (1 + t * s) ^ 2) ≤
      2 * ((s + v) / eps) := by
    calc
      _ ≤ s * (((t * v) ^ 2 + t * v) / (1 + t * s) ^ 2) :=
        mul_le_mul_of_nonneg_right hqs (by positivity)
      _ = s * (t * v) ^ 2 / (1 + t * s) ^ 2 +
          s * (t * v) / (1 + t * s) ^ 2 := by ring
      _ ≤ v ^ 2 / s + v := add_le_add h1 h2
      _ ≤ _ := by linarith
  have hvar : q ^ 2 * (t * v / (1 + t * s) ^ 2 +
      (t * v) ^ 2 * (t * s) / (1 + t * s) ^ 4) ≤
      2 * ((s + v) / (t * eps)) := by
    have hsq : q ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hq hqs 2
    have hfirst : v / t ≤ (s + v) / (t * eps) := by
      simpa only [div_div, mul_comm eps t] using div_le_div_of_nonneg_right hvE ht.le
    have hlast : v ^ 2 / (t * s) ≤ (s + v) / (t * eps) := by
      simpa only [div_div, mul_comm s t, mul_comm eps t] using
        div_le_div_of_nonneg_right hr ht.le
    calc
      _ ≤ s ^ 2 * (t * v / (1 + t * s) ^ 2 +
          (t * v) ^ 2 * (t * s) / (1 + t * s) ^ 4) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = s ^ 2 * (t * v) / (1 + t * s) ^ 2 +
          s ^ 2 * (t * v) ^ 2 * (t * s) / (1 + t * s) ^ 4 := by ring
      _ ≤ v / t + v ^ 2 / (t * s) := add_le_add h3 h4
      _ ≤ _ := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hqE (show 0 ≤ 2 / u by positivity)
  have hsecond' := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 2 * C0 / u by positivity)
  have hvar' := mul_le_mul_of_nonneg_left hvar hC
  have hslack : 0 ≤ (2 + 2 * C0) * ((s + v) / (t * eps)) := by positivity
  have hid :
      (2 + 4 * C0) * (s + v) * (1 / (u * eps) + 1 / (t * eps)) =
        2 / u * ((s + v) / eps) + 2 * C0 / u * (2 * ((s + v) / eps)) +
        C0 * (2 * ((s + v) / (t * eps))) +
        (2 + 2 * C0) * ((s + v) / (t * eps)) := by ring
  rw [hid]
  calc
    _ = (2 / u * q + 2 * C0 / u *
        (q * (((t * v) ^ 2 + t * v) / (1 + t * s) ^ 2))) +
        C0 * (q ^ 2 * (t * v / (1 + t * s) ^ 2 +
          (t * v) ^ 2 * (t * s) / (1 + t * s) ^ 4)) := by ring
    _ ≤ (2 / u * ((s + v) / eps) +
        2 * C0 / u * (2 * ((s + v) / eps))) +
        C0 * (2 * ((s + v) / (t * eps))) :=
      add_le_add (add_le_add hfirst hsecond') hvar'
    _ ≤ _ := by linarith only [hslack]

end CausalSmith.Stat.AnnotationRarearmFrontier
