module
public import Causalean.Stat.CLT.BerryEsseen.SincBoxFourier
public import Causalean.Stat.CLT.BerryEsseen.SincSquaredPrereqs

/-! # Self-convolution of the sinc interval density

The interval density whose Fourier transform is sinc has a triangular
self-convolution. This spatial calculation is the next step toward the
Fourier transform of squared sinc.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- At [every real argument t](hyp:t), [the self-convolution of the interval
density equal to π on `(−1/(2π), 1/(2π)]`, whose Fourier transform is sinc,
equals the triangular function π·max(1 − π|t|, 0)](goal). -/
theorem sincBox_self_convolution (t : ℝ) :
    ∫ u : ℝ, sincBox (t - u) * sincBox u =
      ((Real.pi * max (1 - Real.pi * |t|) 0 : ℝ) : ℂ) := by
  let a : ℝ := (2 * Real.pi)⁻¹
  let s : Set ℝ := Set.Icc (-a) a ∩ Set.Icc (t - a) (t + a)
  have hae (x : ℝ) : ∀ᵐ u : ℝ ∂volume, u ≠ x := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton x : volume {x} = 0)
  have hfun : (fun u : ℝ => sincBox (t - u) * sincBox u) =ᵐ[volume]
      (fun u => s.indicator (fun _ => ((Real.pi ^ 2 : ℝ) : ℂ)) u) := by
    filter_upwards [hae (-a), hae a, hae (t - a), hae (t + a)] with u h₁ h₂ h₃ h₄
    have hleft : t - u ∈ Set.Ioc (-a) a ↔ u ∈ Set.Icc (t - a) (t + a) := by
      simp only [Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨hlo, hhi⟩
        constructor <;> linarith
      · rintro ⟨hlo, hhi⟩
        constructor
        · linarith [lt_of_le_of_ne hhi h₄]
        · linarith
    have hright : u ∈ Set.Ioc (-a) a ↔ u ∈ Set.Icc (-a) a := by
      simp only [Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨hlo, hhi⟩
        exact ⟨hlo.le, hhi⟩
      · rintro ⟨hlo, hhi⟩
        exact ⟨lt_of_le_of_ne hlo (Ne.symm h₁), hhi⟩
    change (Set.Ioc (-a) a).indicator (fun _ => (Real.pi : ℂ)) (t - u) *
      (Set.Ioc (-a) a).indicator (fun _ => (Real.pi : ℂ)) u =
      s.indicator (fun _ => ((Real.pi ^ 2 : ℝ) : ℂ)) u
    have hs : u ∈ s ↔ u ∈ Set.Ioc (-a) a ∧ t - u ∈ Set.Ioc (-a) a := by
      change (u ∈ Set.Icc (-a) a ∧ u ∈ Set.Icc (t - a) (t + a)) ↔ _
      exact and_congr hright.symm hleft.symm
    by_cases hp : t - u ∈ Set.Ioc (-a) a <;>
      by_cases hq : u ∈ Set.Ioc (-a) a <;>
      simp [Set.indicator, hp, hq, hs, pow_two]
  rw [integral_congr_ae hfun,
    integral_indicator_const _ (measurableSet_Icc.inter measurableSet_Icc)]
  have hoverlap : volume.real s = max (2 * a - |t|) 0 := by
    dsimp [s]
    rw [Set.Icc_inter_Icc, Real.volume_real_Icc]
    change max (min a (t + a) - max (-a) (t - a)) 0 = max (2 * a - |t|) 0
    rcases le_total t 0 with ht | ht
    · rw [max_eq_left (by linarith : t - a ≤ -a),
        min_eq_right (by linarith : t + a ≤ a), abs_of_nonpos ht]
      congr 1
      ring
    · rw [max_eq_right (by linarith : -a ≤ t - a),
        min_eq_left (by linarith : a ≤ t + a), abs_of_nonneg ht]
      congr 1
      ring
  rw [hoverlap]
  have hpi : 0 < Real.pi := Real.pi_pos
  have haπ : Real.pi * (2 * a) = 1 := by
    dsimp [a]
    field_simp [Real.pi_ne_zero]
  rw [Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  by_cases h : 0 ≤ 2 * a - |t|
  · rw [max_eq_left h, max_eq_left (by nlinarith [mul_nonneg hpi.le h] :
        0 ≤ 1 - Real.pi * |t|)]
    nlinarith
  · rw [max_eq_right (le_of_lt (lt_of_not_ge h)),
        max_eq_right (by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hpi.le
            (le_of_lt (lt_of_not_ge h))] : 1 - Real.pi * |t| ≤ 0)]
    simp

end Causalean.Stat.CLT.BerryEsseen
