module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactEnvelopeCells
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactIntegrability
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactKernelCells

/-! # High-frequency certificates with cells proportional to the bandwidth

The frequency endpoints in these enclosures are fixed fractions of the
actual outer cutoff. This avoids extending a frequency cell beyond that
cutoff as the moment ratio varies. On such cells the cubic exponent is a
negative polynomial divided by the squared moment ratio. Its upper bound
uses only the upper parameter endpoint, while the interval length uses the
lower endpoint. These are analytic cell bounds, not numerical budgets.

The file proves three bounds: the moment envelope at a rescaled frequency
is dominated by the two endpoint cubic exponents at the upper parameter
(`prawitz_rescaled_moment_cell_bound`), and the lower-half and upper-half
cell integrals of the high-frequency integrand are bounded by the cell
length times an explicit polynomial bound on the filter times the endpoint
exponential envelope (`prawitz_high_rescaled_lower_cell_integral_bound`,
`prawitz_high_rescaled_upper_cell_integral_bound`). Summing these cell
bounds over a rational grid into the numerical high-frequency budget is
done downstream in `PrawitzBudgetHighCompact`, not here.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- Within [a positive parameter cell](hyp:ρ,s,hρ,hρs) and
[a nonnegative cell of the kernel band](hyp:u,a,b,ha,hau,hub,hb),
the [moment envelope at the rescaled frequency is bounded by the two
endpoint cubic exponents at the upper parameter](goal). -/
theorem prawitz_rescaled_moment_cell_bound
    (ρ s u a b : ℝ) (hρ : 0 < ρ) (hρs : ρ ≤ s)
    (ha : 0 ≤ a) (hau : a ≤ u) (hub : u ≤ b) (hb : b ≤ 1) :
    prawitzMomentEnvelope ρ ((12 / (5 * ρ)) * u) ≤
      min 1 (Real.exp (max
        ((-72 * a ^ 2 / 25 + 1728 * a ^ 3 / 625) / s ^ 2)
        ((-72 * b ^ 2 / 25 + 1728 * b ^ 3 / 625) / s ^ 2))) := by
  have hs : 0 < s := hρ.trans_le hρs
  have hu : 0 ≤ u := ha.trans hau
  have hu1 : u ≤ 1 := hub.trans hb
  let C : ℝ := -72 * u ^ 2 / 25 + 1728 * u ^ 3 / 625
  have hC : C ≤ 0 := by
    have h := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)
    dsimp [C]
    nlinarith [sq_nonneg u]
  have hsq : ρ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hρ.le hρs 2
  have hdiv : C / ρ ^ 2 ≤ C / s ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hρ) (sq_pos_of_pos hs)).mpr
    have h := mul_nonpos_of_nonpos_of_nonneg hC (sub_nonneg.mpr hsq)
    nlinarith
  have he := prawitz_cubic_exponent_cell_bound s s
    ((12 / (5 * s)) * u) ((12 / (5 * s)) * a) ((12 / (5 * s)) * b)
    hs.le le_rfl (by positivity)
    (mul_le_mul_of_nonneg_left hau (by positivity))
    (mul_le_mul_of_nonneg_left hub (by positivity))
  have heq (z : ℝ) :
      -(((12 / (5 * s)) * z) ^ 2 / 2) +
        s * ((12 / (5 * s)) * z) ^ 3 / 5 =
      (-72 * z ^ 2 / 25 + 1728 * z ^ 3 / 625) / s ^ 2 := by
    field_simp
    ring
  rw [heq u, heq a, heq b] at he
  unfold prawitzMomentEnvelope
  apply min_le_min_left 1
  apply Real.exp_le_exp.mpr
  have hfreq : 0 ≤ (12 / (5 * ρ)) * u := by positivity
  rw [abs_of_nonneg hfreq]
  have hreal : -(((12 / (5 * ρ)) * u) ^ 2 / 2) +
      ρ * ((12 / (5 * ρ)) * u) ^ 3 / 5 = C / ρ ^ 2 := by
    dsimp [C]
    field_simp
    ring
  rw [hreal]
  exact hdiv.trans he

/-- On [a positive parameter cell](hyp:ρ,r,s,hr,hrρ,hρs) and
[a positive lower-half kernel cell](hyp:a,b,ha,hab,hb), the
[high-frequency integral over the corresponding moving frequency cell
has an explicit endpoint enclosure](goal). -/
theorem prawitz_high_rescaled_lower_cell_integral_bound
    (ρ r s a b : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    let U := 12 / (5 * ρ)
    let Q := (1 - a) ^ 2 / 4 +
      (((1 - a) * (1 - (Real.pi * a) ^ 2 / 2 + (Real.pi * b) ^ 4 / 24) /
        (Real.pi * a * (1 - (Real.pi * b) ^ 2 / 6)) + 1 / Real.pi) / 2) ^ 2
    let E := max ((-72 * a ^ 2 / 25 + 1728 * a ^ 3 / 625) / s ^ 2)
      ((-72 * b ^ 2 / 25 + 1728 * b ^ 3 / 625) / s ^ 2)
    (∫ t in (U * a)..(U * b),
      ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) ≤
      (12 / (5 * r)) * (b - a) * Real.sqrt Q * min 1 (Real.exp E) := by
  /- Apply the proved high interval-integrability helper on [U*a,U*b].
  For interior t set u=t/U in [a,b]. The proved Taylor squared norm
  enclosure uses these FIXED kernel endpoints, independent of rho.
  Apply prawitz_rescaled_moment_cell_bound and U*(t/U)=t, then integrate
  the constant bound. Finally U<=12/(5*r) and all factors are nonnegative.
  No substitution theorem or cutoff/log certificate is needed for this leaf. -/
  dsimp only
  let U := 12 / (5 * ρ)
  let Q := (1 - a) ^ 2 / 4 +
    (((1 - a) * (1 - (Real.pi * a) ^ 2 / 2 + (Real.pi * b) ^ 4 / 24) /
      (Real.pi * a * (1 - (Real.pi * b) ^ 2 / 6)) + 1 / Real.pi) / 2) ^ 2
  let E := max ((-72 * a ^ 2 / 25 + 1728 * a ^ 3 / 625) / s ^ 2)
    ((-72 * b ^ 2 / 25 + 1728 * b ^ 3 / 625) / s ^ 2)
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hU : 0 < U := by dsimp [U]; positivity
  have ha0 : 0 < a := ha
  have hb1 : b ≤ 1 := by linarith
  have hcell : U * a ≤ U * b := mul_le_mul_of_nonneg_left hab hU.le
  have hbU : U * b ≤ U := by simpa using mul_le_mul_of_nonneg_left hb1 hU.le
  have hi := prawitz_high_compact_intervalIntegrable ρ U (U * a) (U * b)
    hU (mul_pos hU ha0) hcell hbU
  have hUr : U ≤ 12 / (5 * r) := by
    dsimp [U]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hrρ (by norm_num))
  calc
    _ ≤ ∫ _t in (U * a)..(U * b), Real.sqrt Q * min 1 (Real.exp E) := by
      apply intervalIntegral.integral_mono_on hcell hi intervalIntegrable_const
      intro t ht
      have hau : a ≤ t / U := (le_div_iff₀ hU).2 (by simpa [mul_comm] using ht.1)
      have hub : t / U ≤ b := (div_le_iff₀ hU).2 (by simpa [mul_comm] using ht.2)
      have hk : ‖prawitzKernel (t / U)‖ ≤ Real.sqrt Q :=
        Real.le_sqrt_of_sq_le
          (prawitzKernel_lower_cell_taylor_sq_bound _ a b ha hau hub hb)
      have heq : U * (t / U) = t := by field_simp
      have he := prawitz_rescaled_moment_cell_bound ρ s (t / U) a b
        hρ hρs ha0.le hau hub hb1
      change prawitzMomentEnvelope ρ (U * (t / U)) ≤ min 1 (Real.exp E) at he
      rw [heq] at he
      exact mul_le_mul hk he (by unfold prawitzMomentEnvelope; positivity)
        (Real.sqrt_nonneg _)
    _ = U * (b - a) * Real.sqrt Q * min 1 (Real.exp E) := by
      rw [intervalIntegral.integral_const]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right hUr (sub_nonneg.mpr hab)

/-- On [a positive parameter cell r ≤ ρ ≤ s](hyp:ρ,r,s,hr,hrρ,hρs) and
[an upper-half kernel cell 1/2 ≤ a ≤ b ≤ 1](hyp:a,b,ha,hab,hb), with outer
cutoff U = 12/(5ρ), [the integral over the moving frequency cell [Ua, Ub] of
the Prawitz filter magnitude at t/U times the moment envelope is at most
(12/(5r))·(b − a)·√Q·min(1, exp E)](goal), where
Q = (1 − a)²/4 + π²(1 − a)⁴/16 is a reflected polynomial bound on the filter
and E is the larger of the two rescaled endpoint exponents
(−72c²/25 + 1728c³/625)/s² at c = a and c = b; this includes cells ending at
the outer cutoff. -/
theorem prawitz_high_rescaled_upper_cell_integral_bound
    (ρ r s a b : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (hρs : ρ ≤ s)
    (ha : 1 / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    let U := 12 / (5 * ρ)
    let Q := (1 - a) ^ 2 / 4 + Real.pi ^ 2 * (1 - a) ^ 4 / 16
    let E := max ((-72 * a ^ 2 / 25 + 1728 * a ^ 3 / 625) / s ^ 2)
      ((-72 * b ^ 2 / 25 + 1728 * b ^ 3 / 625) / s ^ 2)
    (∫ t in (U * a)..(U * b),
      ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) ≤
      (12 / (5 * r)) * (b - a) * Real.sqrt Q * min 1 (Real.exp E) := by
  /- As in the lower cell but compare only on Ioo: t<U*b<=U excludes
  the assigned outer endpoint. Use prawitz_high_compact_kernel_sq_upper
  and 1-t/U<=1-a, then the proved rescaled moment cell bound. The original
  kernel value at t=U is unchanged and excluded ONLY almost everywhere.
  This imports no numerical budget and assumes no such allocation. -/
  dsimp only
  let U := 12 / (5 * ρ)
  let Q := (1 - a) ^ 2 / 4 + Real.pi ^ 2 * (1 - a) ^ 4 / 16
  let E := max ((-72 * a ^ 2 / 25 + 1728 * a ^ 3 / 625) / s ^ 2)
    ((-72 * b ^ 2 / 25 + 1728 * b ^ 3 / 625) / s ^ 2)
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hU : 0 < U := by dsimp [U]; positivity
  have ha0 : 0 < a := by linarith
  have hb1 : b ≤ 1 := hb
  have hcell : U * a ≤ U * b := mul_le_mul_of_nonneg_left hab hU.le
  have hbU : U * b ≤ U := by simpa using mul_le_mul_of_nonneg_left hb1 hU.le
  have hi := prawitz_high_compact_intervalIntegrable ρ U (U * a) (U * b)
    hU (mul_pos hU ha0) hcell hbU
  have hUr : U ≤ 12 / (5 * r) := by
    dsimp [U]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hrρ (by norm_num))
  calc
    _ ≤ ∫ _t in (U * a)..(U * b), Real.sqrt Q * min 1 (Real.exp E) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hcell hi intervalIntegrable_const
      intro t ht
      have hau : a ≤ t / U := (le_div_iff₀ hU).2 (by simpa [mul_comm] using ht.1.le)
      have hub : t / U ≤ b := (div_le_iff₀ hU).2 (by simpa [mul_comm] using ht.2.le)
      have hu1 : t / U < 1 := (div_lt_one hU).2 (ht.2.trans_le hbU)
      have hk : ‖prawitzKernel (t / U)‖ ≤ Real.sqrt Q := by
        apply Real.le_sqrt_of_sq_le
        apply (prawitz_high_compact_kernel_sq_upper _ (ha.trans hau) hu1).trans
        dsimp [Q]
        gcongr
      have heq : U * (t / U) = t := by field_simp
      have he := prawitz_rescaled_moment_cell_bound ρ s (t / U) a b
        hρ hρs ha0.le hau hub hb1
      change prawitzMomentEnvelope ρ (U * (t / U)) ≤ min 1 (Real.exp E) at he
      rw [heq] at he
      exact mul_le_mul hk he (by unfold prawitzMomentEnvelope; positivity)
        (Real.sqrt_nonneg _)
    _ = U * (b - a) * Real.sqrt Q * min 1 (Real.exp E) := by
      rw [intervalIntegral.integral_const]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right hUr (sub_nonneg.mpr hab)

end Causalean.Stat.CLT.BerryEsseen
