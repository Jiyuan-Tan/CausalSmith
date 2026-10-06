module
public import Causalean.Stat.CLT.BerryEsseen.EsseenSinc4FirstMoment
public import Causalean.Stat.CLT.BerryEsseen.SmoothingKernel

/-! # The signed sinc-fourth comparison kernel

This reflected and shifted kernel is the explicit witness used in the
unit-bandwidth one-sided Esseen comparison. Its elementary regularity is
separated from its Fourier support and comparison properties.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- At a real argument `y`, the signed comparison kernel is `-y/8` times
the unit sinc-fourth density evaluated at `-y-4`. -/
noncomputable def esseenSignedSinc4Kernel (y : ℝ) : ℝ :=
  (-y) / 8 * sinc4Kernel 1 (-y - 4)

/-- [The signed sinc-fourth comparison kernel (the reflected, shifted, linearly
weighted sinc-fourth kernel) is integrable and continuous on the real
line](goal). -/
theorem esseenSignedSinc4Kernel_integrable_continuous :
    Integrable esseenSignedSinc4Kernel volume ∧
      Continuous esseenSignedSinc4Kernel := by
  have hweighted : Integrable (fun x : ℝ => (x + 4) * sinc4Kernel 1 x) volume := by
    have h := sinc4Kernel_unit_first_moment.1.add
      ((sinc4Kernel_integrable 1 (by norm_num)).const_mul 4)
    apply h.congr
    filter_upwards with x
    simp only [Pi.add_apply, add_mul]
  have hshift : Integrable (fun x : ℝ => x * sinc4Kernel 1 (x - 4)) volume := by
    convert hweighted.comp_add_left (-4) using 1
    ext x
    congr 1 <;> ring
  constructor
  · convert (hshift.comp_neg.const_mul (1 / 8 : ℝ)) using 1
    ext x
    simp only [esseenSignedSinc4Kernel]
    ring
  · unfold esseenSignedSinc4Kernel sinc4Kernel
    fun_prop

end Causalean.Stat.CLT.BerryEsseen
