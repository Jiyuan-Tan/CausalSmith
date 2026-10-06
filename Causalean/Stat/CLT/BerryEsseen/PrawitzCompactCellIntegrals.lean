module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactEnvelopeCells
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactIntegrability
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactKernelCells

/-! # Endpoint integral enclosures for compact Prawitz certificates

These cell inequalities retain the cubic exponent's endpoint maximum and
the quartic/reflected kernel bounds. Their imports are proved, including
integrability at zero and at the assigned upper endpoint. They do not assert
either compact allocation. Subsequent certificates must choose explicit
parameter and frequency partitions and certify finite sums of these bounds.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- On [positive parameter and frequency cells inside the original kernel
band](hyp:ρ,r,s,a,b,hr,hrρ,hρs,ha,hab,hbU), [the normalized low-frequency
integral is enclosed by the better branch using the sharp endpoint
cubic exponent](goal). -/
theorem prawitz_low_compact_endpoint_cell_integral_bound
    (ρ r s a b : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 < a) (hab : a ≤ b) (hbU : b ≤ 12 / (5 * ρ)) :
    let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
      (-(b ^ 2 / 2) + s * b ^ 3 / 5)
    (5 / 6 : ℝ) * (∫ t in a..b,
      ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * prawitzDiscrepancyEnvelope ρ t) ≤
      (b - a) * (1 / (Real.pi * a) + 5 * s / 12) *
        min ((b ^ 3 / 6 + s * b ^ 4 / 8) * Real.exp (E / 2))
          ((min 1 (Real.exp E) + Real.exp (-(a ^ 2 / 2))) / r) := by
  /- Reproduce the normalized algebra of the proved, older low cell bound,
  but use prawitz_envelope_cell_bounds instead of independent exponent
  endpoints. The two polynomial factors are monotone on positive cells.
  Bound the discrepancy divided by rho by each branch; combine with the
  triangle kernel estimate. Integrate using extracted low integrability.
  This leaf imports neither compact budget and changes neither headline.
  It is a cell enclosure, not the still-missing total <=3/10 certificate. -/
  dsimp only
  let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
    (-(b ^ 2 / 2) + s * b ^ 3 / 5)
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hU : 0 < 12 / (5 * ρ) := by positivity
  have hib := prawitz_low_compact_intervalIntegrable ρ (12 / (5 * ρ)) b
    hρ.le hU (ha.le.trans hab) hbU
  have hia := prawitz_low_compact_intervalIntegrable ρ (12 / (5 * ρ)) a
    hρ.le hU ha.le (hab.trans hbU)
  have hi := hia.symm.trans hib
  rw [← intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∫ _t in a..b,
        (1 / (Real.pi * a) + 5 * s / 12) *
          min ((b ^ 3 / 6 + s * b ^ 4 / 8) * Real.exp (E / 2))
            ((min 1 (Real.exp E) + Real.exp (-(a ^ 2 / 2))) / r) := by
      apply intervalIntegral.integral_mono_on hab (hi.const_mul _)
        intervalIntegrable_const
      intro t htcell
      have hat := htcell.1
      have htb := htcell.2
      have htU := htb.trans hbU
      change (5 / 6 : ℝ) * (_ * _) ≤ _
      rw [← mul_assoc]
      have hρ : 0 < ρ := hr.trans_le hrρ
      have hs : 0 < s := hρ.trans_le hρs
      have ht : 0 < t := ha.trans_le hat
      have hb : 0 < b := ht.trans_le htb
      have hU : 0 < 12 / (5 * ρ) := by positivity
      have hfreq : 0 < t / (12 / (5 * ρ)) := div_pos ht hU
      have hfreq1 : t / (12 / (5 * ρ)) ≤ 1 := (div_le_one hU).2 htU
      have hk := prawitzKernel_norm_le (t / (12 / (5 * ρ)))
        (by simpa only [abs_of_pos hfreq] using hfreq)
        (by simpa only [abs_of_pos hfreq] using hfreq1)
      rw [abs_of_pos hfreq] at hk
      have hk' : (5 / 6 : ℝ) * ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * ρ ≤
          1 / (Real.pi * a) + 5 * s / 12 := by
        calc
          _ ≤ (5 / 6 : ℝ) * (1 / (2 * Real.pi * (t / (12 / (5 * ρ)))) +
              1 / 2) * ρ := by gcongr
          _ = 1 / (Real.pi * t) + 5 * ρ / 12 := by field_simp; norm_num
          _ ≤ _ := by gcongr
      have he := prawitz_envelope_cell_bounds ρ s t a b hρ.le hρs ha.le hat htb
      let T := (b ^ 3 / 6 + s * b ^ 4 / 8) *
        Real.exp (E / 2)
      let S := (min 1 (Real.exp E) +
        Real.exp (-(a ^ 2 / 2))) / r
      have hT : (t ^ 3 / 6 + ρ * t ^ 4 / 8) *
          Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10) ≤ T := by
        dsimp [T]
        exact mul_le_mul (by gcongr) (by simpa only [abs_of_pos ht] using he.2)
          (by positivity) (by positivity)
      have hM : prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2)) ≤
          min 1 (Real.exp E) +
            Real.exp (-(a ^ 2 / 2)) := by
        exact add_le_add he.1 (Real.exp_le_exp.mpr (by
          have hsq := pow_le_pow_left₀ ha.le hat 2
          linarith))
      have hd : prawitzDiscrepancyEnvelope ρ t / ρ ≤ min T S := by
        apply le_min
        · apply (div_le_iff₀ hρ).2
          calc
            _ ≤ (ρ * t ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
                Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10) := by
              unfold prawitzDiscrepancyEnvelope
              rw [abs_of_pos ht]
              exact min_le_left _ _
            _ = ((t ^ 3 / 6 + ρ * t ^ 4 / 8) *
                Real.exp (-(t ^ 2 / 4) + ρ * t ^ 3 / 10)) * ρ := by ring
            _ ≤ T * ρ := mul_le_mul_of_nonneg_right hT hρ.le
        · calc
            _ ≤ (prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2))) / ρ :=
              div_le_div_of_nonneg_right (min_le_right _ _) hρ.le
            _ ≤ S := by dsimp [S]; gcongr
      have hd0 : 0 ≤ prawitzDiscrepancyEnvelope ρ t / ρ := by
        unfold prawitzDiscrepancyEnvelope prawitzMomentEnvelope
        positivity
      calc
        _ = ((5 / 6 : ℝ) * ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * ρ) *
            (prawitzDiscrepancyEnvelope ρ t / ρ) := by field_simp
        _ ≤ (1 / (Real.pi * a) + 5 * s / 12) * min T S :=
          mul_le_mul hk' hd hd0 (by positivity)
    _ = _ := by rw [intervalIntegral.integral_const]; ring

/-- On [positive parameter and frequency cells](hyp:ρ,r,s,a,b,hr,hrρ,hρs,ha,hab)
[inside the lower half of every kernel band](hyp:hbU,hhalf), [the
high-frequency cell integral is bounded by the quartic kernel enclosure
times the cubic moment envelope](goal). -/
theorem prawitz_high_compact_lower_cell_integral_bound
    (ρ r s a b : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 < a) (hab : a ≤ b) (hbU : b ≤ 12 / (5 * ρ))
    (hhalf : 5 * s * b / 12 ≤ 1 / 2) :
    let α := 5 * r * a / 12
    let β := 5 * s * b / 12
    let Q := (1 - α) ^ 2 / 4 +
      (((1 - α) * (1 - (Real.pi * α) ^ 2 / 2 + (Real.pi * β) ^ 4 / 24) /
        (Real.pi * α * (1 - (Real.pi * β) ^ 2 / 6)) + 1 / Real.pi) / 2) ^ 2
    let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
      (-(b ^ 2 / 2) + s * b ^ 3 / 5)
    (∫ t in a..b,
      ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * prawitzMomentEnvelope ρ t) ≤
      (b - a) * Real.sqrt Q * min 1 (Real.exp E) := by
  /- For t in [a,b], t/U=5*rho*t/12 lies in [alpha,beta]. Apply the
  proved lower-cell Taylor squared norm bound, then
  Real.le_sqrt_of_sq_le. Apply prawitz_envelope_cell_bounds and integrate
  the constant majorant using prawitz_high_compact_intervalIntegrable.
  The resulting finite integral sums still require certified arithmetic;
  no allocation is assumed by this lemma. -/
  dsimp only
  let α := 5 * r * a / 12
  let β := 5 * s * b / 12
  let Q := (1 - α) ^ 2 / 4 +
    (((1 - α) * (1 - (Real.pi * α) ^ 2 / 2 + (Real.pi * β) ^ 4 / 24) /
      (Real.pi * α * (1 - (Real.pi * β) ^ 2 / 6)) + 1 / Real.pi) / 2) ^ 2
  let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
    (-(b ^ 2 / 2) + s * b ^ 3 / 5)
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hs : 0 < s := hρ.trans_le hρs
  have hU : 0 < 12 / (5 * ρ) := by positivity
  have hi := prawitz_high_compact_intervalIntegrable ρ (12 / (5 * ρ)) a b
    hU ha hab hbU
  calc
    _ ≤ ∫ _t in a..b, Real.sqrt Q * min 1 (Real.exp E) := by
      apply intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      intro t ht
      have ht0 : 0 < t := ha.trans_le ht.1
      have heq : t / (12 / (5 * ρ)) = 5 * ρ * t / 12 := by field_simp
      have hα : α ≤ t / (12 / (5 * ρ)) := by
        rw [heq]
        dsimp [α]
        gcongr
        exact ht.1
      have hβ : t / (12 / (5 * ρ)) ≤ β := by
        rw [heq]
        dsimp [β]
        gcongr
        exact ht.2
      have hk : ‖prawitzKernel (t / (12 / (5 * ρ)))‖ ≤ Real.sqrt Q :=
        Real.le_sqrt_of_sq_le (prawitzKernel_lower_cell_taylor_sq_bound
          _ α β (by dsimp [α]; positivity) hα hβ hhalf)
      have he := (prawitz_envelope_cell_bounds ρ s t a b hρ.le hρs ha.le ht.1 ht.2).1
      exact mul_le_mul hk he (by unfold prawitzMomentEnvelope; positivity)
        (Real.sqrt_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const]; ring

/-- On [a positive parameter cell r ≤ ρ ≤ s](hyp:ρ,r,s,hr,hrρ,hρs) and
[a positive frequency cell a ≤ b](hyp:a,b,ha,hab)
[inside the outer band b ≤ 12/(5ρ) whose rescaled lower endpoint
α = 5ra/12 is at least one half](hyp:hbU,hhalf), [the integral over [a, b]
of the Prawitz filter magnitude at t/(12/(5ρ)) times the moment envelope is
at most (b − a)·√Q·min(1, exp E)](goal), where
Q = (1 − α)²/4 + π²(1 − α)⁴/16 is a reflected quartic bound on the filter and
E is the larger endpoint value of −t²/2 + s·t³/5, so the bound decays at the
outer endpoint. -/
theorem prawitz_high_compact_upper_cell_integral_bound
    (ρ r s a b : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 < a) (hab : a ≤ b) (hbU : b ≤ 12 / (5 * ρ))
    (hhalf : 1 / 2 ≤ 5 * r * a / 12) :
    let α := 5 * r * a / 12
    let Q := (1 - α) ^ 2 / 4 + Real.pi ^ 2 * (1 - α) ^ 4 / 16
    let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
      (-(b ^ 2 / 2) + s * b ^ 3 / 5)
    (∫ t in a..b,
      ‖prawitzKernel (t / (12 / (5 * ρ)))‖ * prawitzMomentEnvelope ρ t) ≤
      (b - a) * Real.sqrt Q * min 1 (Real.exp E) := by
  /- Use integral_mono_on_of_le_Ioo so t<b<=U gives t/U<1. The
  assigned value at t=U has not been replaced and does not satisfy the
  vanishing reflected bound; it is a null endpoint. Apply the proved
  upper-half squared estimate and monotonically bound 1-t/U by 1-alpha,
  then use the same endpoint moment estimate and constant integration.
  Imports have no admissions. This is the smallest upper-band integral
  step; the unchanged high budget awaits a finite-sum certificate. -/
  dsimp only
  let α := 5 * r * a / 12
  let Q := (1 - α) ^ 2 / 4 + Real.pi ^ 2 * (1 - α) ^ 4 / 16
  let E := max (-(a ^ 2 / 2) + s * a ^ 3 / 5)
    (-(b ^ 2 / 2) + s * b ^ 3 / 5)
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hU : 0 < 12 / (5 * ρ) := by positivity
  have hi := prawitz_high_compact_intervalIntegrable ρ (12 / (5 * ρ)) a b
    hU ha hab hbU
  calc
    _ ≤ ∫ _t in a..b, Real.sqrt Q * min 1 (Real.exp E) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hab hi intervalIntegrable_const
      intro t ht
      have ht0 : 0 < t := ha.trans ht.1
      have heq : t / (12 / (5 * ρ)) = 5 * ρ * t / 12 := by field_simp
      have hα : α ≤ t / (12 / (5 * ρ)) := by
        rw [heq]
        dsimp [α]
        gcongr
        exact ht.1.le
      have hu : t / (12 / (5 * ρ)) < 1 :=
        (div_lt_one hU).2 (ht.2.trans_le hbU)
      have hk : ‖prawitzKernel (t / (12 / (5 * ρ)))‖ ≤ Real.sqrt Q := by
        apply Real.le_sqrt_of_sq_le
        apply (prawitz_high_compact_kernel_sq_upper _
          (hhalf.trans hα) hu).trans
        dsimp [Q]
        gcongr
      have he := (prawitz_envelope_cell_bounds ρ s t a b hρ.le hρs ha.le
        ht.1.le ht.2.le).1
      exact mul_le_mul hk he (by unfold prawitzMomentEnvelope; positivity)
        (Real.sqrt_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const]; ring

end Causalean.Stat.CLT.BerryEsseen
