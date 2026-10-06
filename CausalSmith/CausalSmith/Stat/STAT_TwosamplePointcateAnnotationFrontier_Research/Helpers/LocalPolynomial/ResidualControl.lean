module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationGram
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.LocalPolynomial.Taylor

/-! # Cellwise control-regression approximation
Cell coverage, cell geometry, and the orthogonal best-approximation inequality
used for the control-regression residual in the local polynomial roadmap.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 800000
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The prescribed face assignments cover every point of the localization box.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the localization cell cover conclusion](goal) holds. -/
lemma localization_cell_cover {d : ℕ} (h : ℝ) (J : ℕ) (hh : 0 < h)
    (hJ : 1 ≤ J) (x : Cov d) (hx : x ∈ locCube d h) :
    ∃ z : Fin d → Fin J, x ∈ cell h J z := by
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  have hex (i : Fin d) : ∃ j : Fin J,
      1/2-h/2+(j:ℝ)*(h/J) ≤ x i ∧
      (if j.val+1 = J then x i ≤ 1/2+h/2
       else x i < 1/2-h/2+((j:ℝ)+1)*(h/J)) := by
    let t := (x i-(1/2-h/2))/(h/J)
    have ht0 : 0 ≤ t := div_nonneg (by linarith [(hx i).1]) ht.le
    have htJ : t ≤ J := by
      apply (div_le_iff₀ ht).2
      have he : (J:ℝ)*(h/J) = h := by field_simp
      dsimp [t]
      rw [he]
      linarith [(hx i).2]
    by_cases he : t = J
    · let j : Fin J := ⟨J-1, by omega⟩
      have hjlast : j.val+1 = J := by dsimp [j]; omega
      have hjcast : (j:ℝ)+1 = J := by exact_mod_cast hjlast
      refine ⟨j, ?_, ?_⟩
      · have hmul : (J:ℝ)*(h/J) = x i-(1/2-h/2) := by
          exact ((div_eq_iff ht.ne').mp he).symm
        have hle := mul_le_mul_of_nonneg_right (by linarith : (j:ℝ) ≤ J) ht.le
        linarith
      · simpa only [if_pos hjlast] using (hx i).2
    · have hlt : t < J := lt_of_le_of_ne htJ he
      let j : Fin J := ⟨⌊t⌋₊, (Nat.floor_lt ht0).mpr hlt⟩
      refine ⟨j, ?_, ?_⟩
      · have hle := (le_div_iff₀ ht).mp (Nat.floor_le ht0)
        change (j:ℝ)*(h/J) ≤ x i-(1/2-h/2) at hle
        linarith
      · split_ifs with hjlast
        · exact (hx i).2
        · have hle := (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one t)
          change x i-(1/2-h/2) < ((j:ℝ)+1)*(h/J) at hle
          linarith
  choose z hz using hex
  exact ⟨z, hz⟩

/-- Points in the same cell are separated by at most its side times √d.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input z](hyp:z), [the specified input x](hyp:x), [the specified input y](hyp:y), [the specified input hx](hyp:hx), [the specified input hy](hyp:hy), [the cell distance bound conclusion](goal) holds. -/
lemma cell_distance_bound {d : ℕ} (h : ℝ) (J : ℕ) (hh : 0 < h)
    (hJ : 1 ≤ J) (z : Fin d → Fin J) (x y : Cov d)
    (hx : x ∈ cell h J z) (hy : y ∈ cell h J z) :
    dist x y ≤ Real.sqrt (d:ℝ)*(h/J) := by
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  have upper (w : Cov d) (hw : w ∈ cell h J z) (i : Fin d) :
      w i ≤ 1/2-h/2+((z i:ℝ)+1)*(h/J) := by
    have hi := (hw i).2
    split_ifs at hi with he
    · have hc : (z i:ℝ)+1 = J := by exact_mod_cast he
      rw [hc]
      have hm : (J:ℝ)*(h/J) = h := by field_simp
      rw [hm]
      linarith
    · exact hi.le
  have hcoord (i : Fin d) : |x i-y i| ≤ h/J := by
    rw [abs_le]
    constructor <;> linarith [(hx i).1, (hy i).1, upper x hx i, upper y hy i]
  rw [EuclideanSpace.dist_eq]
  calc
    _ ≤ Real.sqrt ((d:ℝ)*(h/J)^2) := by
      apply Real.sqrt_le_sqrt
      calc
        _ ≤ ∑ _i : Fin d, (h/J)^2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.dist_eq]
          nlinarith [hcoord i, sq_abs (x i-y i), abs_nonneg (x i-y i)]
        _ = _ := by simp
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq ht.le]

/-- Subtracting any fine-basis expansion leaves the same orthogonal residual.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input v](hyp:v), [the projection best approximation conclusion](goal) holds. -/
lemma projection_best_approximation (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h))
    (v : FineIdx d J → ℝ) :
    (∫ x, (f x-projOp d h J f x)^2 ∂locLaw d h) ≤
      ∫ x, (f x-∑ i, fineBasis h J x i*v i)^2 ∂locLaw d h := by
  let g := fun x => ∑ i, fineBasis h J x i*v i
  have hb := fineBasis_memLp d h J hh hh' hJ
  have hg : MemLp g 2 (locLaw d h) := memLp_finsetSum _ (fun i _ => (hb i).mul_const (v i))
  have hcoef (i : FineIdx d J) : (∫ x, fineBasis h J x i*g x ∂locLaw d h) = v i := by
    simp only [g, Finset.mul_sum]
    simp_rw [← mul_assoc]
    rw [integral_finsetSum (f := fun j x => fineBasis h J x i*fineBasis h J x j*v j)
      Finset.univ (fun j _ => ((hb i).integrable_mul (hb j)).mul_const (v j))]
    simp_rw [integral_mul_const, fine_orthonormal d h J hh hh' hJ]
    simp
  have hproj (x : Cov d) : projOp d h J (fun y => f y-g y) x = projOp d h J f x-g x := by
    rw [projection_finite_expansion d h J hh hh' hJ (fun y => f y-g y) (hf.sub hg),
      projection_finite_expansion d h J hh hh' hJ _ hf]
    have hsub (i : FineIdx d J) :
        (∫ y, fineBasis h J y i*(f y-g y) ∂locLaw d h) =
          (∫ y, fineBasis h J y i*f y ∂locLaw d h)-v i := by
      simp_rw [mul_sub]
      rw [integral_sub
        (show Integrable (fun y => fineBasis h J y i*f y) (locLaw d h) from (hb i).integrable_mul hf)
        (show Integrable (fun y => fineBasis h J y i*g y) (locLaw d h) from (hb i).integrable_mul hg), hcoef]
    simp_rw [hsub, mul_sub, Finset.sum_sub_distrib]
    rfl
  have he := projection_pythagoras d h J hh hh' hJ (fun x => f x-g x) (hf.sub hg)
  simp_rw [hproj, show ∀ x, f x-g x-(projOp d h J f x-g x) = f x-projOp d h J f x by intro x; ring] at he
  have hn : 0 ≤ ∫ x, (projOp d h J (fun y => f y-g y) x)^2 ∂locLaw d h :=
    integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [hproj] at hn
  change (∫ x, (f x-projOp d h J f x)^2 ∂locLaw d h) ≤ ∫ x, (f x-g x)^2 ∂locLaw d h
  linarith

/-- Coarse constant orthonormality normalizes the localization measure.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the localization probability conclusion](goal) holds. -/
lemma localization_probability (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) :
    IsProbabilityMeasure (locLaw d h) := by
  let z : PolyIdx d := ⟨fun _ => 0, by simp⟩
  have ho := coarse_orthonormal d h hh hh' z z
  simp only [z, coarseBasis, legendre, ite_true, Finset.prod_const_one, one_mul] at ho
  apply isProbabilityMeasure_iff_real.mpr
  simpa only [integral_const, smul_eq_mul, mul_one] using ho

/-- Every cell centre belongs to its assigned cell.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input z](hyp:z), [the cell center mem conclusion](goal) holds. -/
lemma cell_center_mem {d : ℕ} (h : ℝ) (J : ℕ) (hh : 0 < h) (hJ : 1 ≤ J)
    (z : Fin d → Fin J) :
    (WithLp.toLp 2 (fun i => 1/2-h/2+((z i:ℝ)+1/2)*(h/J)) : Cov d) ∈ cell h J z := by
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  intro i
  simp only [WithLp.ofLp_toLp]
  constructor
  · nlinarith
  · split_ifs with he
    · have hz : (z i:ℝ)+1 = J := by exact_mod_cast he
      have hm : (J:ℝ)*(h/J) = h := by field_simp
      nlinarith
    · nlinarith

/-- A bounded measurable Hölder function is approximated by cellwise constants
with the precise fine-scale exponent in the paper's roadmap.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input K](hyp:K), [the specified input s](hyp:s), [the specified input hK](hyp:hK), [the specified input hs](hyp:hs), [the specified input hB](hyp:hB), [the specified input hmod](hyp:hmod), [the holder control projection residual conclusion](goal) holds. -/
lemma holder_control_projection_residual (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : Measurable f) (B K s : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hB : ∀ x ∈ locCube d h, |f x| ≤ B)
    (hmod : ∀ x ∈ locCube d h, ∀ y ∈ locCube d h,
      |f x-f y| ≤ K*dist x y^s) :
    Real.sqrt (∫ x, (f x-projOp d h J f x)^2 ∂locLaw d h) ≤
      K*(Real.sqrt (d:ℝ))^s*(h/J)^s := by
  classical
  letI := localization_probability d h hh hh'
  have hae : ∀ᵐ x ∂locLaw d h, x ∈ locCube d h := by
    unfold locLaw
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (isClosed_locCube d h).measurableSet
  have hf2 : MemLp f 2 (locLaw d h) := by
    exact (memLp_top_of_bound hf.aestronglyMeasurable B (hae.mono fun x hx => by
      simpa only [Real.norm_eq_abs] using hB x hx)).mono_exponent (by simp)
  let center := fun z : Fin d → Fin J =>
    (WithLp.toLp 2 (fun i => 1/2-h/2+((z i:ℝ)+1/2)*(h/J)) : Cov d)
  let z0 : PolyIdx d := ⟨fun _ => 0, by simp⟩
  let v : FineIdx d J → ℝ := fun i => if i.2 = z0 then
    f (center i.1)/Real.sqrt ((J:ℝ)^d) else 0
  let g := fun x => ∑ i, fineBasis h J x i*v i
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  have hroot : 0 < Real.sqrt ((J:ℝ)^d) := Real.sqrt_pos.mpr (by positivity)
  have hg : MemLp g 2 (locLaw d h) := memLp_finsetSum _
    (fun i _ => (fineBasis_memLp d h J hh hh' hJ i).mul_const (v i))
  have hcell (x : Cov d) (z : Fin d → Fin J) (hx : x ∈ cell h J z) :
      g x = f (center z) := by
    dsimp only [g]
    rw [Fintype.sum_prod_type]
    have hinner (w : Fin d → Fin J) :
        (∑ u : PolyIdx d, fineBasis h J x (w,u)*v (w,u)) =
          if x ∈ cell h J w then f (center w) else 0 := by
      simp [v, fineBasis, z0, legendre]
      split_ifs <;> simp [mul_div_cancel₀ _ hroot.ne']
    simp_rw [hinner]
    rw [Finset.sum_eq_single z]
    · simp only [if_pos hx]
    · intro w _ hw
      have hn : x ∉ cell h J w := fun hw' => hw (cell_index_unique d h J hh hJ x w z hw' hx)
      simp only [if_neg hn]
    · simp
  let E := K*(Real.sqrt (d:ℝ))^s*(h/J)^s
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have herr : ∀ᵐ x ∂locLaw d h, |f x-g x| ≤ E := by
    filter_upwards [hae] with x hx
    obtain ⟨z, hz⟩ := localization_cell_cover h J hh hJ x hx
    have hc : center z ∈ cell h J z := cell_center_mem h J hh hJ z
    rw [hcell x z hz]
    calc
      _ ≤ K*dist x (center z)^s := hmod x hx _ (cell_subset_locCube h J hh hJ z hc)
      _ ≤ K*(Real.sqrt (d:ℝ)*(h/J))^s := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (dist_nonneg) (cell_distance_bound h J hh hJ z x _ hz hc) hs) hK
      _ = E := by rw [Real.mul_rpow (Real.sqrt_nonneg _) ht.le]; dsimp [E]; ring
  have henergy : (∫ x, (f x-g x)^2 ∂locLaw d h) ≤ E^2 := by
    calc
      _ ≤ ∫ _x : Cov d, E^2 ∂locLaw d h := by
        apply integral_mono_ae (hf2.sub hg).integrable_sq (integrable_const _)
        filter_upwards [herr] with x hx
        change (f x-g x)^2 ≤ E^2
        nlinarith [sq_abs (f x-g x), abs_nonneg (f x-g x)]
      _ = E^2 := by simp
  calc
    _ ≤ Real.sqrt (∫ x, (f x-g x)^2 ∂locLaw d h) := Real.sqrt_le_sqrt
      (projection_best_approximation d h J hh hh' hJ f hf2 v)
    _ ≤ Real.sqrt (E^2) := Real.sqrt_le_sqrt henergy
    _ = _ := Real.sqrt_sq hE

/-- For [a primitive law P](hyp:P) [in the model class](hyp:hP) at [overlap level eps](hyp:eps), [the designated control regression is globally Borel](goal). -/
@[fun_prop] lemma measurable_designatedControl {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P) :
    Measurable (designatedControl P hP) := by
  unfold designatedControl
  have hc : MeasurableSet (cube d) := by
    unfold cube
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_Icc.preimage (by fun_prop)
  exact Measurable.ite hc (canonicalLaw P hP).measurable_mu0 measurable_const

/-- At exponents at most one, the frozen Hölder norm gives the function's modulus.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input s](hyp:s), [the specified input L](hyp:L), [the specified input hs](hyp:hs), [the specified input hs'](hyp:hs'), [the specified input hL](hyp:hL), [the specified input hf](hyp:hf), [the specified input x](hyp:x), [the specified input y](hyp:y), [the specified input hx](hyp:hx), [the specified input hy](hyp:hy), [the holder norm low order modulus conclusion](goal) holds. -/
lemma holderNorm_low_order_modulus {d : ℕ} (f : Cov d → ℝ) (s L : ℝ)
    (hs : 0 < s) (hs' : s ≤ 1) (hL : 0 ≤ L)
    (hf : holderNorm f s ≤ ENNReal.ofReal L)
    (x y : Cov d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |f x-f y| ≤ L*dist x y^s := by
  have hp : Nat.ceil s-1 = 0 := by
    have hc : Nat.ceil s ≤ 1 := Nat.ceil_le.mpr (by simpa using hs')
    omega
  have hm := (holderNorm_le_iff f s L hL).mp hf
  by_cases he : x = y
  · subst y
    simp only [sub_self, abs_zero]
    positivity
  · have hh := hm.2.2 (fun _ => 0) (by simp [multiOrder, hp]) x hx y hy he
    simpa only [coordinatePartial_zero_index, hp, Nat.cast_zero, sub_zero] using hh

/-- The control-regression half of the residual estimates is fully derived from
class membership and the prescribed cellwise constant construction.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the control projection bounds conclusion](goal) holds. -/
lemma control_projection_bounds (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P),
      ∀ h J, 0 < h → h ≤ 1/2 → 1 ≤ J →
        Real.sqrt (∫ x, (designatedControl P hP x-
          projOp d h J (designatedControl P hP) x)^2 ∂locLaw d h) ≤ C*(h/J)^beta := by
  have hL : 0 ≤ L := by linarith [hdom.2.2.2.2.2.2.2.1]
  let C := L*(Real.sqrt (d:ℝ))^beta+1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP h J hh hh' hJ
  have hmu : ControlHolder beta L (canonicalLaw P hP) := (canonicalLaw_spec P hP).2.2.2.2.2.1
  have hbound : ∀ x ∈ locCube d h, |designatedControl P hP x| ≤ L := by
    intro x hx
    have hxc := locCube_subset_cube d h hh' hx
    have hp : Nat.ceil beta-1 = 0 := by
      have hc : Nat.ceil beta ≤ 1 := Nat.ceil_le.mpr (by simpa using hdom.2.2.2.2.1)
      omega
    have hs := ((holderNorm_le_iff _ beta L hL).mp hmu).2.1
      (fun _ => 0) (by simp [multiOrder, hp]) x hxc
    simpa only [coordinatePartial_zero_index, designatedControl, if_pos hxc] using hs
  have hmod : ∀ x ∈ locCube d h, ∀ y ∈ locCube d h,
      |designatedControl P hP x-designatedControl P hP y| ≤ L*dist x y^beta := by
    intro x hx y hy
    have hxc := locCube_subset_cube d h hh' hx
    have hyc := locCube_subset_cube d h hh' hy
    simpa only [designatedControl, if_pos hxc, if_pos hyc] using
      holderNorm_low_order_modulus _ beta L hdom.2.2.2.1 hdom.2.2.2.2.1 hL hmu x y hxc hyc
  have hr := holder_control_projection_residual d h J hh hh' hJ _
    (measurable_designatedControl P hP) L L beta hL hdom.2.2.2.1.le hbound hmod
  exact hr.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (Real.rpow_nonneg (div_nonneg hh.le (Nat.cast_nonneg J)) _))

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
