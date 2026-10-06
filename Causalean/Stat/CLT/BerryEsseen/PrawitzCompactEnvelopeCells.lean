module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzBudgetCutoffs
public import Mathlib.Analysis.Complex.Exponential

/-! # Cutoff geometry and cubic envelope enclosures on parameter cells

These deterministic helpers split the complementary Prawitz certificates into
parameter geometry, endpoint exponent bounds, and later finite-sum arithmetic.
They assert no budget or Gaussian approximation as a hypothesis. For rational
negative exponent endpoints, reuse Real.sum_le_exp_of_nonneg followed by
Real.exp_neg to obtain rational reciprocal-polynomial upper bounds. For the
logarithmic cutoff, certify endpoint exponentials and use Real.log_le_iff_le_exp.
Mathlib's sum_integral_adjacent_intervals provides partition integration; it
must be combined with the existing low/high interval-integrability results.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- On [a positive parameter cell](hyp:ρ,r,s,hr,hrρ,hρs),
[the inner logarithmic cutoff lies between the cutoffs at the cell endpoints,
and the outer cutoff lies between the reciprocal endpoints](goal). -/
theorem prawitz_compact_cutoff_cell_bounds
    (ρ r s : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s) :
    max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / s))) ≤
      max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ))) ∧
    max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ))) ≤
      max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / r))) ∧
    12 / (5 * s) ≤ 12 / (5 * ρ) ∧ 12 / (5 * ρ) ≤ 12 / (5 * r) := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hs : 0 < s := hρ.trans_le hρs
  have hleft : 1 / s ≤ 1 / ρ :=
    div_le_div_of_nonneg_left (by norm_num) hρ hρs
  have hright : 1 / ρ ≤ 1 / r :=
    div_le_div_of_nonneg_left (by norm_num) hr hrρ
  have hl : Real.log (1 / s) ≤ Real.log (1 / ρ) :=
    Real.log_le_log (by positivity) hleft
  have hu : Real.log (1 / ρ) ≤ Real.log (1 / r) :=
    Real.log_le_log (by positivity) hright
  refine ⟨?_, ?_, ?_, ?_⟩
  · gcongr
  · gcongr
  · gcongr
  · gcongr

/-- Throughout [a nonnegative frequency cell](hyp:t,a,b,ha,hat,htb) and
[a nonnegative parameter cell](hyp:ρ,s,hρ,hρs), [the cubic Gaussian exponent
is bounded by its two endpoint values at the upper parameter](goal). -/
theorem prawitz_cubic_exponent_cell_bound
    (ρ s t a b : ℝ) (hρ : 0 ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    -(t ^ 2 / 2) + ρ * t ^ 3 / 5 ≤
      max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
        (-(b ^ 2 / 2) + s * b ^ 3 / 5) := by
  /- Smallest open exponent obligation; do not dispatch a compact budget.
  First replace ρ by s using t≥0. At s=0 the exponent is decreasing.
  At s>0 its derivative is t*(-1+3*s*t/5), so the exponent decreases
  up to 5/(3*s) and increases afterwards. Split according to which side
  contains t, and compare to a or b on the corresponding interval using
  monotoneOn/antitoneOn_of_deriv_nonneg/nonpos. The critical point is a
  minimum, so endpoint maxima enclose every cell including cells crossing it.
  This preserves the cubic damping; -a²/2+s*b³/5 is an unnecessarily loose
  independent-term bound. The Taylor discrepancy exponent is exactly half
  this exponent and can use the same enclosure. Certify later endpoint
  exponentials with Mathlib's finite Taylor bounds, never floating-point scans.
  The eventual normalized totals remain ≤1/4 and ≤3/20 for low/high
  contributions (equivalently raw integrals ≤3/10 and ≤9/50); this lemma
  supplies no such total as an assumption. -/
  have hs : 0 ≤ s := hρ.trans hρs
  have ht : 0 ≤ t := ha.trans hat
  have hparam : -(t ^ 2 / 2) + ρ * t ^ 3 / 5 ≤
      -(t ^ 2 / 2) + s * t ^ 3 / 5 := by
    gcongr
  have hd (x : ℝ) :
      deriv (fun x : ℝ => -(x ^ 2 / 2) + s * x ^ 3 / 5) x =
        x * (-1 + 3 * s * x / 5) := by
    simp (disch := fun_prop)
    ring
  -- The sign test includes s = 0, when the decreasing branch always applies.
  by_cases hturn : 3 * s * t ≤ 5
  · have hm : AntitoneOn
        (fun x : ℝ => -(x ^ 2 / 2) + s * x ^ 3 / 5) (Set.Icc a t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc a t)
        (by fun_prop) (by fun_prop)
      intro x hx
      have hxcell : x ∈ Set.Icc a t := interior_subset hx
      have hx : 0 ≤ x := ha.trans hxcell.1
      have hxt : 3 * s * x ≤ 3 * s * t :=
        mul_le_mul_of_nonneg_left hxcell.2 (by positivity)
      rw [hd]
      exact mul_nonpos_of_nonneg_of_nonpos hx (by linarith)
    exact hparam.trans ((hm ⟨le_rfl, hat⟩ ⟨hat, le_rfl⟩ hat).trans
      (le_max_left _ _))
  · have hm : MonotoneOn
        (fun x : ℝ => -(x ^ 2 / 2) + s * x ^ 3 / 5) (Set.Icc t b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc t b)
        (by fun_prop) (by fun_prop)
      intro x hx
      have hxcell : x ∈ Set.Icc t b := interior_subset hx
      have hx : 0 ≤ x := ht.trans hxcell.1
      have htx : 3 * s * t ≤ 3 * s * x :=
        mul_le_mul_of_nonneg_left hxcell.1 (by positivity)
      rw [hd]
      exact mul_nonneg hx (by linarith)
    exact hparam.trans ((hm ⟨le_rfl, htb⟩ ⟨htb, le_rfl⟩ htb).trans
      (le_max_right _ _))

/-- For [a frequency t in a nonnegative cell [a, b]](hyp:t,a,b,ha,hat,htb) and
[a nonnegative ratio ρ at most s](hyp:ρ,s,hρ,hρs), with E the larger of the
endpoint exponents −a²/2 + s·a³/5 and −b²/2 + s·b³/5,
[the moment envelope at ratio ρ and frequency t is at most min(1, exp E), and
the Taylor exponential exp(−t²/4 + ρ|t|³/10) is at most exp(E/2)](goal). -/
theorem prawitz_envelope_cell_bounds
    (ρ s t a b : ℝ) (hρ : 0 ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
      (-(b ^ 2 / 2) + s * b ^ 3 / 5)
    prawitzMomentEnvelope ρ t ≤ min 1 (Real.exp E) ∧
    Real.exp (-(t ^ 2 / 4) + ρ * |t| ^ 3 / 10) ≤ Real.exp (E / 2) := by
  dsimp only
  have ht : 0 ≤ t := ha.trans hat
  have he := prawitz_cubic_exponent_cell_bound ρ s t a b hρ hρs ha hat htb
  constructor
  · unfold prawitzMomentEnvelope
    rw [abs_of_nonneg ht]
    exact min_le_min_left 1 (Real.exp_le_exp.mpr he)
  · rw [abs_of_nonneg ht]
    apply Real.exp_le_exp.mpr
    linarith only [he]

end Causalean.Stat.CLT.BerryEsseen
