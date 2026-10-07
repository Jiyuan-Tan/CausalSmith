module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCutoffRationalCertificate

/-! # Analytic adapters for the rational low-frequency cells

These inequalities compare the proved analytic integral majorants with the
unchanged rational table terms. They are independent of the real cutoff
adapter, the finite low sum certificate, and both integral budgets. The
positive grid cells stay inside the band by the rational cutoff certificate,
so their cubic endpoint damping is nonnegative before reciprocal Taylor
bounds are used. No numerical integral allocation is a premise.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

/-- On [each certified parameter cell](hyp:j), [the analytic polynomial
enclosure of the singular initial low interval is bounded by its rational
table entry](goal). -/
theorem prawitz_low_real_initial_enclosure (j : Fin 270) :
    let s := (prawitzCompactRight j.val : ℝ)
    let a := (1 / 200 : ℝ)
    (1 / Real.pi + 5 * s * a / 12) *
      (1 / 6 + s * a / 8) * a ^ 3 / 3 ≤
        (prawitzRationalLowInitial j.val : ℝ) := by
  /- Use positive s from the CLOSED cutoff certificate. Replace only
  1/pi by 1/(314159/100000), using prawitz_rational_pi_bounds.
  All other nonnegative factors are identical after push_cast. This
  corresponds exactly to prawitz_low_compact_initial_integral_bound
  in PrawitzBudgetLowCompact; no integral proof needs to be copied. -/
  dsimp only
  have hc := prawitz_compact_cutoff_rational_certificate j
  dsimp only at hc
  have hs : 0 ≤ (prawitzCompactRight j.val : ℝ) := by
    exact_mod_cast (hc.1.trans hc.2.1).le
  have hp := prawitz_rational_pi_bounds
  unfold prawitzRationalLowInitial
  push_cast
  gcongr
  exact hp.1

/-- On [the j-th certified parameter cell, with rational endpoints r < s, and
the i-th positive low grid cell [a, b] = [i/200, (i+1)/200] below the cell's
low cutoff index](hyp:j,i,hi), [the analytic cell majorant
(b − a)·(1/(πa) + 5s/12)·min((b³/6 + s·b⁴/8)·exp(E/2),
(min(1, exp E) + exp(−a²/2))/r), where E is the larger of the two endpoint
exponents −a²/2 + s·a³/5 and −b²/2 + s·b³/5, is at most the cell's rational
table entry](goal).

The table entry is the same expression with π replaced by 314159/100000,
each exponential replaced by the reciprocal of a sixteen-term Taylor
polynomial, and the factor min(1, exp E) replaced by that reciprocal bound
on exp E. -/
theorem prawitz_low_real_cell_enclosure
    (j : Fin 270) (i : ℕ)
    (hi : i ∈ Ico 1 (prawitzLowCutoffIndex j.val)) :
    let r := (prawitzCompactLeft j.val : ℝ)
    let s := (prawitzCompactRight j.val : ℝ)
    let a := (i : ℝ) / 200
    let b := ((i + 1 : ℕ) : ℝ) / 200
    let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
      (-(b ^ 2 / 2) + s * b ^ 3 / 5)
    (b - a) * (1 / (Real.pi * a) + 5 * s / 12) *
      min ((b ^ 3 / 6 + s * b ^ 4 / 8) * Real.exp (E / 2))
        ((min 1 (Real.exp E) + Real.exp (-(a ^ 2 / 2))) / r) ≤
          (prawitzRationalLowCell j.val i : ℝ) := by
  /- Round 8 lowest analytic layer. From hi obtain 1<=i and i+1<=K.
  The CLOSED cutoff certificate gives 0<r<s<=1 and K/200<=12/(5*s).
  Thus 0<a<=b and s*b<=12/5<5/2, so both a²/2-s*a³/5 and
  b²/2-s*b³/5 are nonnegative. Their rational minimum e casts to -E.
  Use prawitz_exp_neg_le_reciprocal_taylor16 at e/2, e, and a²/2.
  Dropping min 1 in the second branch is an upper bound, not a new
  approximation premise. Replace 1/(pi*a) by 1/(p*a), p=314159/100000;
  all factors are nonnegative. Show b-a=1/200 and push_cast to match
  prawitzRationalLowCell exactly. This retains the SHARP endpoint
  maximum in PrawitzCompactCellIntegrals, not the looser independent
  endpoint majorant. Do not replace the minimum by one chosen branch,
  alter grid endpoints, or import either compact budget. -/
  dsimp only
  let r := prawitzCompactLeft j.val
  let s := prawitzCompactRight j.val
  let a : ℚ := i / 200
  let b : ℚ := (i + 1 : ℕ) / 200
  let e := min (a ^ 2 / 2 - s * a ^ 3 / 5) (b ^ 2 / 2 - s * b ^ 3 / 5)
  have hc := prawitz_compact_cutoff_rational_certificate j
  dsimp only at hc
  have hr : 0 < r := hc.1
  have hs : 0 < s := hr.trans hc.2.1
  have hia := (mem_Ico.mp hi).1
  have hib : i + 1 ≤ prawitzLowCutoffIndex j.val := by
    have := (mem_Ico.mp hi).2
    omega
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : i ≤ i + 1)) (by norm_num)
  have hb : b ≤ (prawitzLowCutoffIndex j.val : ℚ) / 200 := by
    dsimp [b]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hib) (by norm_num)
  have hsb : s * b ≤ 12 / 5 := by
    have hcut := hc.2.2.2.2.2.2.2.1
    have h := (le_div_iff₀ (by positivity : 0 < 5 * s)).mp hcut
    nlinarith only [h, mul_le_mul_of_nonneg_left hb hs.le]
  have hsa : s * a ≤ 12 / 5 :=
    (mul_le_mul_of_nonneg_left hab hs.le).trans hsb
  have hda : 0 ≤ a ^ 2 / 2 - s * a ^ 3 / 5 := by
    have h : 0 ≤ a ^ 2 * (1 / 2 - s * a / 5) :=
      mul_nonneg (sq_nonneg a) (by linarith only [hsa])
    nlinarith only [h]
  have hdb : 0 ≤ b ^ 2 / 2 - s * b ^ 3 / 5 := by
    have h : 0 ≤ b ^ 2 * (1 / 2 - s * b / 5) :=
      mul_nonneg (sq_nonneg b) (by linarith only [hsb])
    nlinarith only [h]
  have he : 0 ≤ e := le_min hda hdb
  have hE : max (-(((a : ℝ) ^ 2) / 2) + (s : ℝ) * (a : ℝ) ^ 3 / 5)
      (-(((b : ℝ) ^ 2) / 2) + (s : ℝ) * (b : ℝ) ^ 3 / 5) = -(e : ℝ) := by
    dsimp [e]
    push_cast
    rcases le_total ((a : ℝ) ^ 2 / 2 - (s : ℝ) * (a : ℝ) ^ 3 / 5)
      ((b : ℝ) ^ 2 / 2 - (s : ℝ) * (b : ℝ) ^ 3 / 5) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith only [h])]
      ring
    · rw [min_eq_right h, max_eq_right (by linarith only [h])]
      ring
  have hhalf := prawitz_exp_neg_le_reciprocal_taylor16 (e / 2) (by positivity)
  have hfull := prawitz_exp_neg_le_reciprocal_taylor16 e he
  have hgauss := prawitz_exp_neg_le_reciprocal_taylor16 (a ^ 2 / 2) (by positivity)
  push_cast at hhalf hfull hgauss
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 0 < (b : ℝ) := by exact_mod_cast (ha.trans_le hab)
  have hwidth : (b : ℝ) - (a : ℝ) = 1 / 200 := by
    dsimp [a, b]
    push_cast
    ring
  have hp : 1 / (Real.pi * (a : ℝ)) ≤
      1 / ((314159 / 100000 : ℝ) * (a : ℝ)) := by
    gcongr
    exact prawitz_rational_pi_bounds.1
  have hbranches :
      min (((b : ℝ) ^ 3 / 6 + (s : ℝ) * (b : ℝ) ^ 4 / 8) * Real.exp (-(e : ℝ) / 2))
        ((min 1 (Real.exp (-(e : ℝ))) + Real.exp (-((a : ℝ) ^ 2 / 2))) / (r : ℝ)) ≤
      min (((b : ℝ) ^ 3 / 6 + (s : ℝ) * (b : ℝ) ^ 4 / 8) / (prawitzTaylor16 (e / 2) : ℝ))
        ((1 / (prawitzTaylor16 e : ℝ) + 1 / (prawitzTaylor16 (a ^ 2 / 2) : ℝ)) / (r : ℝ)) := by
    apply min_le_min
    · simpa only [div_eq_mul_inv, one_mul, neg_mul] using
        mul_le_mul_of_nonneg_left hhalf
          (by positivity : 0 ≤ (b : ℝ) ^ 3 / 6 + (s : ℝ) * (b : ℝ) ^ 4 / 8)
    · exact div_le_div_of_nonneg_right
        (add_le_add ((min_le_right _ _).trans hfull) hgauss) hr'.le
  have hac : (i : ℝ) / 200 = (a : ℝ) := by simp [a]
  have hbc : ((i + 1 : ℕ) : ℝ) / 200 = (b : ℝ) := by simp [b]
  rw [hac, hbc]
  change ((b : ℝ) - (a : ℝ)) * (1 / (Real.pi * (a : ℝ)) + 5 * (s : ℝ) / 12) *
    min (((b : ℝ) ^ 3 / 6 + (s : ℝ) * (b : ℝ) ^ 4 / 8) * Real.exp
      (max (-((a : ℝ) ^ 2 / 2) + (s : ℝ) * (a : ℝ) ^ 3 / 5)
        (-((b : ℝ) ^ 2 / 2) + (s : ℝ) * (b : ℝ) ^ 3 / 5) / 2))
      ((min 1 (Real.exp (max (-((a : ℝ) ^ 2 / 2) + (s : ℝ) * (a : ℝ) ^ 3 / 5)
        (-((b : ℝ) ^ 2 / 2) + (s : ℝ) * (b : ℝ) ^ 3 / 5))) +
        Real.exp (-((a : ℝ) ^ 2 / 2))) / (r : ℝ)) ≤ _
  rw [hE, hwidth]
  unfold prawitzRationalLowCell
  change _ ≤ (((1 / 200 : ℚ) * (1 / ((314159 / 100000 : ℚ) * a) + 5 * s / 12) *
    min ((b ^ 3 / 6 + s * b ^ 4 / 8) / prawitzTaylor16 (e / 2))
      ((1 / prawitzTaylor16 e + 1 / prawitzTaylor16 (a ^ 2 / 2)) / r) : ℚ) : ℝ)
  push_cast
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) (by norm_num)
  · exact hbranches
  · positivity
  · positivity

end Causalean.Stat.CLT.BerryEsseen
