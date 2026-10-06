module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.CellPolynomial

/-! # Propensity times coarse-polynomial residual
The cell-center propensity approximant retains the entire coarse polynomial.
Hölder continuity and orthogonal best approximation give the fine-scale bound
for every coarse basis entry.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Multiplication by a coarse entry preserves the cell-center approximation rate.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input K](hyp:K), [the specified input s](hyp:s), [the specified input hK](hyp:hK), [the specified input hs](hyp:hs), [the specified input hB](hyp:hB), [the specified input hmod](hyp:hmod), [the specified input u](hyp:u), [the holder propensity projection residual conclusion](goal) holds. -/
lemma holder_propensity_projection_residual (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : Measurable f) (B K s : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hB : ∀ x ∈ locCube d h, |f x| ≤ B)
    (hmod : ∀ x ∈ locCube d h, ∀ y ∈ locCube d h,
      |f x-f y| ≤ K*dist x y^s) (u : PolyIdx d) :
    Real.sqrt (∫ x, (f x*coarseBasis h x u-
      projOp d h J (fun y => f y*coarseBasis h y u) x)^2 ∂locLaw d h) ≤
      (K*(Real.sqrt (d:ℝ))^s*(4:ℝ)^d)*(h/J)^s := by
  classical
  letI := localization_probability d h hh hh'
  have hae : ∀ᵐ x ∂locLaw d h, x ∈ locCube d h := by
    unfold locLaw
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (isClosed_locCube d h).measurableSet
  let F := fun x => f x*coarseBasis h x u
  have hF2 : MemLp F 2 (locLaw d h) := by
    apply (memLp_top_of_bound (by fun_prop) (B*(4:ℝ)^d) ?_).mono_exponent (by simp)
    filter_upwards [hae] with x hx
    simp only [F, Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |f x| *(4:ℝ)^d := mul_le_mul_of_nonneg_left
        (coarseBasis_abs_bound d h hh x hx u) (abs_nonneg _)
      _ ≤ B*(4:ℝ)^d := mul_le_mul_of_nonneg_right (hB x hx) (by positivity)
  let center := fun z : Fin d → Fin J =>
    (WithLp.toLp 2 (fun i => 1/2-h/2+((z i:ℝ)+1/2)*(h/J)) : Cov d)
  obtain ⟨v, hv⟩ := cellwise_coarse_expansion h J hh hJ u (fun z => f (center z))
  let g := fun x => ∑ i, fineBasis h J x i*v i
  have hg : MemLp g 2 (locLaw d h) := memLp_finsetSum _
    (fun i _ => (fineBasis_memLp d h J hh hh' hJ i).mul_const (v i))
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  let E := (K*(Real.sqrt (d:ℝ))^s*(4:ℝ)^d)*(h/J)^s
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have herr : ∀ᵐ x ∂locLaw d h, |F x-g x| ≤ E := by
    filter_upwards [hae] with x hx
    obtain ⟨z, hz⟩ := localization_cell_cover h J hh hJ x hx
    have hc : center z ∈ cell h J z := cell_center_mem h J hh hJ z
    change |f x*coarseBasis h x u-g x| ≤ E
    rw [show g x = f (center z)*coarseBasis h x u from hv z x hz, ← sub_mul, abs_mul]
    calc
      _ ≤ (K*dist x (center z)^s)*(4:ℝ)^d :=
        mul_le_mul (hmod x hx _ (cell_subset_locCube h J hh hJ z hc))
          (coarseBasis_abs_bound d h hh x hx u) (abs_nonneg _) (by positivity)
      _ ≤ (K*(Real.sqrt (d:ℝ)*(h/J))^s)*(4:ℝ)^d := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg (cell_distance_bound h J hh hJ z x _ hz hc) hs) hK
      _ = E := by rw [Real.mul_rpow (Real.sqrt_nonneg _) ht.le]; dsimp [E]; ring
  have henergy : (∫ x, (F x-g x)^2 ∂locLaw d h) ≤ E^2 := by
    calc
      _ ≤ ∫ _x : Cov d, E^2 ∂locLaw d h := by
        apply integral_mono_ae (hF2.sub hg).integrable_sq (integrable_const _)
        filter_upwards [herr] with x hx
        change (F x-g x)^2 ≤ E^2
        nlinarith [sq_abs (F x-g x), abs_nonneg (F x-g x)]
      _ = E^2 := by simp
  calc
    _ ≤ Real.sqrt (∫ x, (F x-g x)^2 ∂locLaw d h) := Real.sqrt_le_sqrt
      (projection_best_approximation d h J hh hh' hJ F hF2 v)
    _ ≤ Real.sqrt (E^2) := Real.sqrt_le_sqrt henergy
    _ = _ := Real.sqrt_sq hE

/-- Class membership supplies the propensity residual bound uniformly in the coarse entry.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the propensity projection bounds conclusion](goal) holds. -/
lemma propensity_projection_bounds (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ h J, 0 < h → h ≤ 1/2 → 1 ≤ J → ∀ u : PolyIdx d,
        Real.sqrt (∫ x, (designatedPropensity P hP x*coarseBasis h x u-
          projOp d h J (fun y => designatedPropensity P hP y*coarseBasis h y u) x)^2
          ∂locLaw d h) ≤ C*(h/J)^alpha := by
  have hL : 0 ≤ L := by linarith [hdom.2.2.2.2.2.2.2.1]
  let C := L*(Real.sqrt (d:ℝ))^alpha*(4:ℝ)^d+1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP h J hh hh' hJ u
  have he : PropensityHolder alpha L (canonicalLaw P hP) := (canonicalLaw_spec P hP).2.2.2.2.1
  have hbound : ∀ x ∈ locCube d h, |designatedPropensity P hP x| ≤ L := by
    intro x hx
    have hxc := locCube_subset_cube d h hh' hx
    have hp : Nat.ceil alpha-1 = 0 := by
      have hc : Nat.ceil alpha ≤ 1 := Nat.ceil_le.mpr (by simpa using hdom.2.2.1)
      omega
    have hs := ((holderNorm_le_iff _ alpha L hL).mp he).2.1
      (fun _ => 0) (by simp [multiOrder, hp]) x hxc
    simpa only [coordinatePartial_zero_index, designatedPropensity, if_pos hxc] using hs
  have hmod : ∀ x ∈ locCube d h, ∀ y ∈ locCube d h,
      |designatedPropensity P hP x-designatedPropensity P hP y| ≤ L*dist x y^alpha := by
    intro x hx y hy
    have hxc := locCube_subset_cube d h hh' hx
    have hyc := locCube_subset_cube d h hh' hy
    simpa only [designatedPropensity, if_pos hxc, if_pos hyc] using
      holderNorm_low_order_modulus _ alpha L hdom.2.1 hdom.2.2.1 hL he x y hxc hyc
  have hr := holder_propensity_projection_residual d h J hh hh' hJ _
    (measurable_designatedPropensity P hP) L L alpha hL hdom.2.1.le hbound hmod u
  exact hr.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (Real.rpow_nonneg (div_nonneg hh.le (Nat.cast_nonneg J)) _))

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
