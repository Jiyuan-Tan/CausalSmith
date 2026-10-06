module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.ProjectionFieldGeometry
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.ProjectionFieldMoments

/-! The sharp moment-only bound for the observable multiscale projection field. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The projection field has the sharp normalized energy bound even when each scale uses
an arbitrary Borel clipped conditional mean. Only the common-threshold prefix is telescoped. -/
-- @node: projectionField_energy_bound
lemma projectionField_energy_bound (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j)
    (j0 : ℕ) (hj0 : j0 ≤ J) (hcap : ∀ j, j.val ≤ j0 → T j = T 0) :
    h⁻¹ * (∫ x in window h, (projectionField law h J T x)^2 ∂design) ≤
      3*(10 : ℝ)^(2/κ.p) + 200*(∑ j : Fin J,
        if j0 < j.val+1 then T j.succ^(-2*(κ.p-1)) else 0) := by
  let B : ℝ := (10 : ℝ)^(1/κ.p)
  let idx : ℕ → Fin (J+1) := fun j => ⟨min j J, by omega⟩
  let F : ℕ → unitInterval → ℝ := fun j => truncatedMean law (T (idx j))
  have hi (j : ℕ) (hj : j ≤ J) : (idx j).val = j := min_eq_left hj
  have hzero : idx 0 = 0 := Fin.ext (by simp [idx])
  have hs (j : Fin J) : idx (j.val+1) = j.succ := Fin.ext (hi _ (by omega))
  have hmom (j) := marginal_mean_truncation_bounds κ hκ law hm (T j) (hT j)
  have hgM : Measurable law.g := by
    have h0 := hm.baselineHolder.1.measurable
    have ht := hm.effectHolder.1.measurable
    have he := law.e_measurable
    unfold ObservedLaw.g
    fun_prop
  have hg := window_energy_of_abs_bound h hh law.g hgM B ((hmom 0).mono fun x hx => hx.1)
  have hf (j : Fin (J+1)) := window_energy_of_abs_bound h hh (truncatedMean law (T j))
    (measurable_truncatedMean law _) B ((hmom j).mono fun x hx => hx.2.1)
  have herr (j : Fin (J+1)) := window_energy_of_abs_bound h hh
    (fun x => truncatedMean law (T j) x-law.g x)
    ((measurable_truncatedMean law _).sub hgM) (10*T j^(1-κ.p))
    ((hmom j).mono fun x hx => hx.2.2)
  have hF (j) : MemLp (F j) 2 (design.restrict (window h)) := (hf (idx j)).1
  have hcapF (j) (hj : j ≤ j0) : F j = F 0 := by
    dsimp [F]
    rw [hcap (idx j) (by rw [hi j (by omega)]; exact hj), hzero]
  have he := projection_energy_error_bound h hh F hF law.g hg.1 j0 J hj0 hcapF
  rw [Finset.sum_range, Finset.sum_range] at he
  simp only [F, hzero, hs] at he
  rw [← projectionField_energy law h hh J T (fun j => (hf j).1)] at he
  have herrors : (∑ j : Fin J, if j0 < j.val+1 then
      (∫ x in window h, (truncatedMean law (T j.succ) x-law.g x)^2 ∂design) else 0) ≤
      ∑ j : Fin J, if j0 < j.val+1 then h*(10*T j.succ^(1-κ.p))^2 else 0 := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact (herr j.succ).2
    · exact le_rfl
  have hraw : (∫ x in window h, (projectionField law h J T x)^2 ∂design) ≤
      h*B^2+2*(h*B^2)+2*(∑ j : Fin J, if j0 < j.val+1 then h*(10*T j.succ^(1-κ.p))^2 else 0) := by
    have hf0 := (hf 0).2
    have hgg := hg.2
    linarith
  have hB : B^2 = (10 : ℝ)^(2/κ.p) := by
    dsimp [B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    congr 1
    ring
  have hsq (j : Fin J) : (10*T j.succ^(1-κ.p))^2 = 100*T j.succ^(-2*(κ.p-1)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by linarith [hT j.succ] : 0 ≤ T j.succ)]
    norm_num
    congr 1
    ring
  simp_rw [hsq] at hraw
  have hsum : (∑ j : Fin J, if j0 < j.val+1 then h*(100*T j.succ^(-2*(κ.p-1))) else 0) =
      100*h*(∑ j : Fin J, if j0 < j.val+1 then T j.succ^(-2*(κ.p-1)) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hsum, hB] at hraw
  have hnorm := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hh.1.le)
  calc
    _ ≤ h⁻¹*(h*(10 : ℝ)^(2/κ.p)+2*(h*(10 : ℝ)^(2/κ.p))+
        2*(100*h*(∑ j : Fin J, if j0 < j.val+1 then T j.succ^(-2*(κ.p-1)) else 0))) := hnorm
    _ = _ := by field_simp [hh.1.ne']; ring

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
