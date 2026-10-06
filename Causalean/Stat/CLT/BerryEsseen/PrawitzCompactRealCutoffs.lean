module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactEnvelopeCells
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCutoffRationalCertificate
public import Mathlib.Order.Interval.Set.Union

/-! # Real cutoff adapters for the certified compact parameter grid

The finite rational cutoff certificate is already proved. This module bridges
its Taylor inequalities to the original logarithmic cutoffs over entire real
parameter cells. It also locates every compact ratio in the explicit grid.
Neither integral budget is imported or assumed.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

/-- [Every real ratio in the closed compact range](hyp:ρ,hρ0,hρ1)
[belongs to one of the 270 adjacent rational parameter cells](goal). -/
theorem prawitz_compact_parameter_cell_exists
    (ρ : ℝ) (hρ0 : 1 / 100 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ j : Fin 270, (prawitzCompactLeft j.val : ℝ) ≤ ρ ∧
      ρ ≤ (prawitzCompactRight j.val : ℝ) := by
  by_cases heq : ρ = 1
  · refine ⟨269, ?_, ?_⟩ <;>
      norm_num [heq, prawitzCompactLeft, prawitzCompactRight]
  · have hlast : (prawitzCompactLeft 270 : ℝ) = 1 := by
      norm_num [prawitzCompactLeft]
    have hfirst : (prawitzCompactLeft 0 : ℝ) = 1 / 100 := by
      norm_num [prawitzCompactLeft]
    have hmem : ρ ∈ Set.Ico (prawitzCompactLeft 0 : ℝ)
        (prawitzCompactLeft 270 : ℝ) := by
      rw [hfirst, hlast]
      exact ⟨hρ0, lt_of_le_of_ne hρ1 heq⟩
    have hcover := Ico_subset_biUnion_Ico 270
      (fun i => (prawitzCompactLeft i : ℝ)) hmem
    rcases Set.mem_iUnion.mp hcover with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hi, hcell⟩
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, hcell.1, hcell.2.le⟩

/-- Throughout [the j-th certified parameter cell, for every ratio ρ between the
cell's left and right endpoints](hyp:j,ρ,hrρ,hρs), with B the cell's low grid
endpoint (its low cutoff index over 200), A its high grid endpoint (its high
cutoff index over 1000), inner cutoff U0 = max(3/2, √(4 log(1/ρ))) and outer
cutoff U = 12/(5ρ), [the inner cutoff U0 is at most B, B is at most the outer
cutoff U, and the rescaled high endpoint U·A is at most U0](goal). -/
theorem prawitz_compact_real_cutoff_enclosures
    (j : Fin 270) (ρ : ℝ)
    (hrρ : (prawitzCompactLeft j.val : ℝ) ≤ ρ)
    (hρs : ρ ≤ (prawitzCompactRight j.val : ℝ)) :
    let B := (prawitzLowCutoffIndex j.val : ℝ) / 200
    let A := (prawitzHighCutoffIndex j.val : ℝ) / 1000
    let U0 := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
    let U := 12 / (5 * ρ)
    U0 ≤ B ∧ B ≤ U ∧ U * A ≤ U0 := by
  /- Round 8 lowest analytic layer. Destructure the CLOSED rational cutoff
  certificate, cast its inequalities, and use the proved monotone cutoff
  geometry. For low B, B>=3/2 and 1<=r*Taylor16(B²/4) imply
  1/r<=exp(B²/4). Apply log and sqrt_le_left to enclose U0(r).
  B<=12/(5*s)<=U follows directly from the certificate and geometry.
  For high A set C=12*A/(5*r)>=0. If C<=3/2 the max suffices.
  Otherwise exp(C²/4)<=ExpUpper8(C²/4)<=1/s; apply log and sqrt
  to obtain C<=U0(s)<=U0(rho), and U*A<=C. All exp comparisons
  are in PrawitzRationalArithmetic. Do not prove a sampled cutoff or
  assume the real cutoff bounds as new premises. The interval includes
  rho=1; use non-strict log/sqrt bounds at that endpoint. -/
  let r := prawitzCompactLeft j.val
  let s := prawitzCompactRight j.val
  let b : ℚ := (prawitzLowCutoffIndex j.val : ℚ) / 200
  let a : ℚ := (prawitzHighCutoffIndex j.val : ℚ) / 1000
  let c : ℚ := 12 * a / (5 * r)
  rcases prawitz_compact_cutoff_rational_certificate j with
    ⟨hr, hrs, hs, hb, _, ha, _, hband, htaylor, hhigh⟩
  change c ≤ 3 / 2 ∨ (0 ≤ c ^ 2 / 4 ∧ c ^ 2 / 4 ≤ 8 ∧
    s * prawitzExpUpper8 (c ^ 2 / 4) ≤ 1) at hhigh
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrs' : (r : ℝ) < s := by exact_mod_cast hrs
  have hb' : (3 / 2 : ℝ) ≤ b := by
    dsimp only [b]
    push_cast
    have : (300 : ℝ) ≤ prawitzLowCutoffIndex j.val := by exact_mod_cast hb
    linarith
  have ha' : (0 : ℝ) ≤ a := by
    dsimp only [a]
    push_cast
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hband' : (b : ℝ) ≤ 12 / (5 * (s : ℝ)) := by
    exact_mod_cast hband
  have htaylor' : (1 : ℝ) ≤ (r : ℝ) * (prawitzTaylor16 (b ^ 2 / 4) : ℝ) := by
    exact_mod_cast htaylor
  have hcastb : (b : ℝ) = (prawitzLowCutoffIndex j.val : ℝ) / 200 := by
    simp only [b, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  have hcasta : (a : ℝ) = (prawitzHighCutoffIndex j.val : ℝ) / 1000 := by
    simp only [a, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  have hcastc : (c : ℝ) = 12 * (a : ℝ) / (5 * (r : ℝ)) := by
    simp only [c, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  have hgeometry := prawitz_compact_cutoff_cell_bounds ρ (r : ℝ) (s : ℝ)
    hr' hrρ hρs
  have hlow : max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / (r : ℝ)))) ≤ b := by
    apply max_le hb'
    apply (Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ b)).2
    have he := (prawitz_taylor16_pos_le_exp ((b : ℝ) ^ 2 / 4)
      (by positivity)).2
    have hpoly : (prawitzTaylor16 (b ^ 2 / 4) : ℝ) ≤
        Real.exp ((b : ℝ) ^ 2 / 4) := by
      simpa only [prawitzTaylor16_cast, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using he
    have hexp : 1 / (r : ℝ) ≤ Real.exp ((b : ℝ) ^ 2 / 4) := by
      apply (div_le_iff₀ hr').2
      have hm := mul_le_mul_of_nonneg_left hpoly hr'.le
      linarith only [htaylor', hm]
    have hlog := (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 1 / (r : ℝ))).2 hexp
    linarith
  have hupper : (c : ℝ) ≤ max (3 / 2 : ℝ)
      (Real.sqrt (4 * Real.log (1 / (s : ℝ)))) := by
    rcases hhigh with hsmall | ⟨hx, hx8, hu⟩
    · have hsmall' : (c : ℝ) ≤ 3 / 2 := by
        have hh : (c : ℝ) ≤ ((3 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hsmall
        simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
      exact hsmall'.trans (le_max_left _ _)
    · have he := prawitz_exp_le_upper8 (c ^ 2 / 4) hx hx8
      have hu' : (s : ℝ) * (prawitzExpUpper8 (c ^ 2 / 4) : ℝ) ≤ 1 := by
        exact_mod_cast hu
      have hs' : (0 : ℝ) < s := hr'.trans hrs'
      have hexp : Real.exp ((c : ℝ) ^ 2 / 4) ≤ 1 / (s : ℝ) := by
        apply (le_div_iff₀ hs').2
        simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at he
        have hm := mul_le_mul_of_nonneg_left he hs'.le
        linarith only [hu', hm]
      have hlog := (Real.le_log_iff_exp_le
        (by positivity : (0 : ℝ) < 1 / (s : ℝ))).2 hexp
      apply le_trans (Real.le_sqrt_of_sq_le (by linarith :
        (c : ℝ) ^ 2 ≤ 4 * Real.log (1 / (s : ℝ)))) (le_max_right _ _)
  have hscaled : 12 / (5 * ρ) * (a : ℝ) ≤ c := by
    rw [hcastc]
    calc
      12 / (5 * ρ) * (a : ℝ) ≤ 12 / (5 * (r : ℝ)) * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hgeometry.2.2.2 ha'
      _ = 12 * (a : ℝ) / (5 * (r : ℝ)) := by ring
  dsimp only
  rw [← hcastb, ← hcasta]
  exact ⟨hgeometry.2.1.trans hlow, hband'.trans hgeometry.2.2.1,
    hscaled.trans (hupper.trans hgeometry.1)⟩

end Causalean.Stat.CLT.BerryEsseen
