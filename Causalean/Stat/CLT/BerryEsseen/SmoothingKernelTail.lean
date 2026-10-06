module
public import Causalean.Stat.CLT.BerryEsseen.SmoothingKernel

/-! # Tail control for the compact-frequency smoothing kernel

The sinc fourth-power kernel has a quantitative concentration bound at the
inverse-bandwidth scale. This is the kernel estimate used when a smoothed CDF
is compared with its original CDF.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory
open scoped Pointwise

/-- For [a positive bandwidth T](hyp:hT), [at most one quarter of the
fourth-power sinc kernel's mass lies at distance at least 6/T from
zero](goal). -/
theorem sinc4Kernel_tail_le_quarter (T : ℝ) (hT : 0 < T) :
    ∫ x in {x : ℝ | 6 / T ≤ |x|}, sinc4Kernel T x ≤ 1 / 4 := by
  let a : ℝ := T / 4
  let s : Set ℝ := {y | (3 : ℝ) / 2 ≤ |y|}
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_le measurable_const measurable_abs
  have hset : a • {x : ℝ | 6 / T ≤ |x|} = s := by
    dsimp [s]
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    simp only [Set.mem_ofPred_eq, smul_eq_mul, abs_mul, abs_inv, abs_of_pos ha]
    dsimp [a]
    rw [div_le_iff₀ hT]
    have hfactor : (T / 4)⁻¹ * |y| * T = 4 * |y| := by
      field_simp
    rw [hfactor]
    constructor <;> intro h <;> linarith
  have htailset : s = Set.Iic (-(3/2 : ℝ)) ∪ Set.Ici (3/2 : ℝ) := by
    dsimp [s]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      constructor <;> intro h
      · exact Or.inr h
      · rcases h with h | h
        · linarith
        · exact h
    · rw [abs_of_nonpos hy]
      constructor <;> intro h
      · exact Or.inl (by linarith)
      · rcases h with h | h <;> linarith
  have hpos : IntegrableOn (fun y : ℝ => y ^ (-4 : ℝ)) (Set.Ici (3/2 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hneg : IntegrableOn (fun y : ℝ => |y| ^ (-4 : ℝ))
      (Set.Iic (-(3/2 : ℝ))) := by
    have hn : IntegrableOn (fun y : ℝ => (-y) ^ (-4 : ℝ))
        (Set.Iic (-(3/2 : ℝ))) := by
      simpa only [Set.neg_Ici] using hpos.comp_neg
    apply hn.congr_fun
    · intro y hy
      exact congrArg (fun z : ℝ => z ^ (-4 : ℝ))
        (abs_of_nonpos (le_trans (Set.mem_Iic.mp hy) (by norm_num))).symm
    · exact measurableSet_Iic
  have hposabs : IntegrableOn (fun y : ℝ => |y| ^ (-4 : ℝ))
      (Set.Ici (3/2 : ℝ)) := by
    apply hpos.congr_fun
    · intro y hy
      exact congrArg (fun z : ℝ => z ^ (-4 : ℝ))
        (abs_of_nonneg (le_trans (by norm_num) (Set.mem_Ici.mp hy))).symm
    · exact measurableSet_Ici
  have hmajor : IntegrableOn (fun y : ℝ => |y| ^ (-4 : ℝ)) s := by
    rw [htailset, integrableOn_union]
    exact ⟨hneg, hposabs⟩
  have hpower : (∫ y : ℝ in Set.Ioi (3/2 : ℝ), y ^ (-4 : ℝ)) = 8/81 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num [Real.rpow_neg_natCast]
  have htail : (∫ y in s, |y| ^ (-4 : ℝ)) = 16/81 := by
    rw [htailset]
    have hdisj : Disjoint (Set.Iic (-(3/2 : ℝ))) (Set.Ici (3/2 : ℝ)) := by
      rw [Set.Iic_disjoint_Ici]
      norm_num
    rw [setIntegral_union hdisj measurableSet_Ici hneg hposabs]
    have hn : (∫ y in Set.Iic (-(3/2 : ℝ)), |y| ^ (-4 : ℝ)) =
        ∫ y in Set.Ioi (3/2 : ℝ), y ^ (-4 : ℝ) := by
      calc
        (∫ y in Set.Iic (-(3/2 : ℝ)), |y| ^ (-4 : ℝ)) =
            ∫ y in Set.Iic (-(3/2 : ℝ)), (-y) ^ (-4 : ℝ) := by
              apply setIntegral_congr_fun measurableSet_Iic
              intro y hy
              exact congrArg (fun z : ℝ => z ^ (-4 : ℝ))
                (abs_of_nonpos (le_trans (Set.mem_Iic.mp hy) (by norm_num)))
        _ = ∫ y in Set.Ioi (-(-(3/2 : ℝ))), y ^ (-4 : ℝ) :=
          by simpa using (integral_comp_neg_Iic (-(3/2 : ℝ))
            (fun y : ℝ => y ^ (-4 : ℝ)))
        _ = _ := by norm_num
    have hp : (∫ y in Set.Ici (3/2 : ℝ), |y| ^ (-4 : ℝ)) =
        ∫ y in Set.Ioi (3/2 : ℝ), y ^ (-4 : ℝ) := by
      rw [integral_Ici_eq_integral_Ioi]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact congrArg (fun z : ℝ => z ^ (-4 : ℝ))
        (abs_of_pos (lt_trans (by norm_num) (Set.mem_Ioi.mp hy)))
    rw [hn, hp, hpower]
    norm_num
  have hpoint (y : ℝ) (hy : y ∈ s) :
      Real.sinc y ^ 4 ≤ |y| ^ (-4 : ℝ) := by
    have hy' : (3 : ℝ) / 2 ≤ |y| := hy
    have hy0 : y ≠ 0 := by
      intro h
      subst y
      norm_num at hy'
    have hsin := Real.abs_sin_le_one y
    have hs2 : Real.sin y ^ 2 ≤ 1 := by
      nlinarith [neg_abs_le (Real.sin y), le_abs_self (Real.sin y)]
    have hs4 : Real.sin y ^ 4 ≤ 1 := by
      nlinarith [mul_self_le_mul_self (sq_nonneg (Real.sin y)) hs2]
    rw [Real.sinc_of_ne_zero hy0, div_pow]
    have hpow : y ^ 4 = |y| ^ 4 := by
      rw [← abs_pow]
      exact (abs_of_nonneg (by positivity : 0 ≤ y ^ 4)).symm
    rw [hpow]
    simpa [div_eq_mul_inv, Real.rpow_neg (abs_nonneg y), Real.rpow_natCast] using
      mul_le_mul_of_nonneg_right hs4
        (inv_nonneg.mpr (by positivity : 0 ≤ |y| ^ 4))
  have hsinc : IntegrableOn (fun y : ℝ => Real.sinc y ^ 4) s := by
    apply hmajor.mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem hs] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.sinc y ^ 4)]
      exact hpoint y hy
  have hbound : (∫ y in s, Real.sinc y ^ 4) ≤ 16/81 := by
    rw [← htail]
    exact setIntegral_mono_on hsinc hmajor hs hpoint
  have hscale : (∫ x in {x : ℝ | 6 / T ≤ |x|}, Real.sinc (a * x) ^ 4) =
      a⁻¹ * ∫ y in s, Real.sinc y ^ 4 := by
    have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure ℝ)
      (fun y : ℝ => Real.sinc y ^ 4) {x : ℝ | 6 / T ≤ |x|} ha
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, hset] using h
  unfold sinc4Kernel
  rw [integral_const_mul]
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  calc
    (3 * T / (8 * Real.pi)) *
        (∫ x in {x : ℝ | 6 / T ≤ |x|}, Real.sinc (T * x / 4) ^ 4)
        = (3 / (2 * Real.pi)) * (∫ y in s, Real.sinc y ^ 4) := by
          have hfun : (fun x : ℝ => Real.sinc (T * x / 4) ^ 4) =
              (fun x : ℝ => Real.sinc (a * x) ^ 4) := by
            funext x
            apply congrArg (fun z : ℝ => Real.sinc z ^ 4)
            dsimp [a]
            ring
          rw [hfun, hscale]
          dsimp [a]
          field_simp
          ring
    _ ≤ (3 / (2 * Real.pi)) * (16/81) := by
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ 1/4 := by
      apply (le_div_iff₀ (by positivity : 0 < (4 : ℝ))).2
      have hpi0 : 0 < Real.pi := Real.pi_pos
      field_simp
      nlinarith

end Causalean.Stat.CLT.BerryEsseen
