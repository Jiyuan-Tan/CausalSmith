module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactRationalData
public import Mathlib.Tactic.IntervalCases

/-! # Finite rational certificates for the moving Prawitz cutoffs

This is a finite arithmetic obligation, independent of either integral
budget. The low table certifies exp(B²/4) ≥ 1/r using a lower Taylor
polynomial. The high table certifies C ≤ 3/2 or exp(C²/4) ≤ 1/s using
the proved eighth-power exponential enclosure. Thus B bounds the actual
inner cutoff from above, and the rescaled high index bounds it from below
on the WHOLE parameter cell [r,s]. No sampled log/sqrt value is a premise.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

set_option maxHeartbeats 4000000 in
-- The 270 exact arithmetic branches exceed the default elaboration limit;
-- the kernel still checks every certificate.
set_option maxRecDepth 10000 in
/-- At [every cell j of the explicit 270-cell compact parameter grid](hyp:j),
[the rational cutoff tables have endpoints 0 < r < s ≤ 1, a low cutoff index
between 300 and 859 and a high cutoff index between 1 and 999, a low grid
endpoint B inside the band 12/(5s), and rational certificates for both
logarithmic cutoff enclosures](goal). -/
theorem prawitz_compact_cutoff_rational_certificate (j : Fin 270) :
    let r := prawitzCompactLeft j.val
    let s := prawitzCompactRight j.val
    let B := (prawitzLowCutoffIndex j.val : ℚ) / 200
    let A := (prawitzHighCutoffIndex j.val : ℚ) / 1000
    let C := 12 * A / (5 * r)
    0 < r ∧ r < s ∧ s ≤ 1 ∧
      300 ≤ prawitzLowCutoffIndex j.val ∧
      prawitzLowCutoffIndex j.val ≤ 859 ∧
      1 ≤ prawitzHighCutoffIndex j.val ∧
      prawitzHighCutoffIndex j.val < 1000 ∧
      B ≤ 12 / (5 * s) ∧ 1 ≤ r * prawitzTaylor16 (B ^ 2 / 4) ∧
      (C ≤ 3 / 2 ∨
        (0 ≤ C ^ 2 / 4 ∧ C ^ 2 / 4 ≤ 8 ∧
          s * prawitzExpUpper8 (C ^ 2 / 4) ≤ 1)) := by
  /- Lowest open layer: only finite rational arithmetic. Use interval_cases
  on j.val (retaining j.isLt), unfold the explicit arrays/getD and the
  degree-16 series, and close with kernel-checked norm_num/decide proofs.
  Split into helper certificates by index blocks if proof reduction is
  expensive; do not use native_decide, unsafe elaboration, or new axioms.
  All 270 cases were independently evaluated with Python Fraction as a
  scaffold sanity check, including every displayed inequality. That check
  is NOT a Lean proof and supplies no hypothesis here.

  Later analytic adapters: positive r,s and the Taylor lower comparison
  give 1/r <= exp(B²/4), hence sqrt(4*log(1/r)) <= B. For the high index,
  C<=3/2 is already below U0(s); otherwise the upper comparison yields
  exp(C²/4)<=1/s and C<=sqrt(4*log(1/s)). Multiply by 5*r/12 and use the
  proved monotonic cutoff lemma to cover all rho in [r,s]. The original
  low/high integrals and constants are unchanged. -/
  -- Each branch is a closed decidable proposition; kernel reduction checks
  -- the exact rational arithmetic, including the Taylor sum and eighth power.
  have hj := j.isLt
  generalize hjval : j.val = i at *
  interval_cases i <;>
    (dsimp only
     unfold prawitzCompactRight prawitzCompactLeft prawitzLowCutoffIndex
       prawitzHighCutoffIndex prawitzExpUpper8 prawitzTaylor16
     decide +kernel)

end Causalean.Stat.CLT.BerryEsseen
