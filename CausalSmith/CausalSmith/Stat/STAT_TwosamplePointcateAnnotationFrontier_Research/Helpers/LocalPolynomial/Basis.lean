module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Projection
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Helpers/LocalPolynomial/Basis

Two-channel point-CATE annotation frontier: Helpers/LocalPolynomial/Basis
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Each of the three prescribed Legendre formulas is uniformly bounded on the reference interval.  Given [the specified input k](hyp:k), [the specified input u](hyp:u), [the specified input hu](hyp:hu), [the legendre abs le four conclusion](goal) holds. -/
lemma legendre_abs_le_four (k : ℕ) (u : ℝ) (hu : |u| ≤ 1/2) :
    |legendre k u| ≤ 4 := by
  have hu2 : u^2 ≤ 1/4 := by
    nlinarith [sq_abs u, mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ (1/2:ℝ)+|u| by positivity)]
  have hs12 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12)
  have hs5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h12 : Real.sqrt 12 ≤ 4 := by nlinarith [Real.sqrt_nonneg 12]
  have h5 : Real.sqrt 5 ≤ 3 := by nlinarith [Real.sqrt_nonneg 5]
  unfold legendre
  split_ifs
  · norm_num
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sqrt_nonneg 12, abs_nonneg u]
  · have hp : |6*u^2-1/2| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg u]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sqrt_nonneg 5, abs_nonneg (6*u^2-1/2)]

/-- Scaling an admissible coarse window preserves the reference-interval bound.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the specified input u](hyp:u), [the coarse basis abs bound conclusion](goal) holds. -/
lemma coarseBasis_abs_bound (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Cov d) (hx : x ∈ locCube d h) (u : PolyIdx d) :
    |coarseBasis h x u| ≤ (4:ℝ)^d := by
  unfold coarseBasis
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i : Fin d, (4:ℝ) := by
      apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
      intro i _
      apply legendre_abs_le_four
      rw [abs_le]
      constructor
      · apply (le_div_iff₀ hh).2
        have hi := (hx i).1
        linarith
      · apply (div_le_iff₀ hh).2
        have hi := (hx i).2
        linarith
    _ = _ := by simp

/-- The finite coarse vector has a bound depending only on the public dimension.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the coarse basis vector bound conclusion](goal) holds. -/
lemma coarseBasis_vector_bound (d : ℕ) (h : ℝ) (hh : 0 < h)
    (x : Cov d) (hx : x ∈ locCube d h) :
    Real.sqrt (∑ u : PolyIdx d, (coarseBasis h x u)^2) ≤
      Real.sqrt (Fintype.card (PolyIdx d):ℝ) * (4:ℝ)^d := by
  have hs : (∑ u : PolyIdx d, (coarseBasis h x u)^2) ≤
      (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2 := by
    calc
      _ ≤ ∑ _u : PolyIdx d, ((4:ℝ)^d)^2 := by
        apply Finset.sum_le_sum
        intro u _
        have hb := coarseBasis_abs_bound d h hh x hx u
        nlinarith [sq_abs (coarseBasis h x u), abs_nonneg (coarseBasis h x u),
          show 0 ≤ (4:ℝ)^d by positivity]
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2) := Real.sqrt_le_sqrt hs
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]

/-- Expanding a finite orthonormal kernel gives its rank as the squared product-space norm.  Given [the specified input b](hyp:b), [the specified input hb](hyp:hb), [the specified input ho](hyp:ho), [the finite orthonormal kernel square conclusion](goal) holds. -/
lemma finite_orthonormal_kernel_square {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [SFinite μ] (b : ι → Ω → ℝ) (hb : ∀ i, MemLp (b i) 2 μ)
    (ho : ∀ i j, (∫ x, b i x * b j x ∂μ) = if i = j then 1 else 0) :
    (∫ p, (∑ i, b i p.1 * b i p.2)^2 ∂μ.prod μ) = Fintype.card ι := by
  classical
  have hexpand (p : Ω × Ω) : (∑ i, b i p.1 * b i p.2)^2 =
      ∑ i, ∑ j, (b i p.1 * b j p.1) * (b i p.2 * b j p.2) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : ι) : Integrable
      (fun p : Ω × Ω => (b i p.1 * b j p.1) * (b i p.2 * b j p.2)) (μ.prod μ) :=
    ((hb i).integrable_mul (hb j)).mul_prod ((hb i).integrable_mul (hb j))
  simp_rw [hexpand]
  rw [integral_finsetSum (f := fun i (p : Ω × Ω) => ∑ j, (b i p.1 * b j p.1) * (b i p.2 * b j p.2))
    Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  have hinner (i : ι) :
      (∫ p : Ω × Ω, ∑ j, (b i p.1 * b j p.1) * (b i p.2 * b j p.2) ∂μ.prod μ) = 1 := by
    rw [integral_finsetSum (f := fun j (p : Ω × Ω) =>
      (b i p.1 * b j p.1) * (b i p.2 * b j p.2)) Finset.univ (fun j _ => hi i j)]
    have hp (j : ι) : (∫ p : Ω × Ω,
        (b i p.1 * b j p.1) * (b i p.2 * b j p.2) ∂μ.prod μ) =
        (if i = j then (1:ℝ) else 0) := by
      rw [integral_prod_mul (fun x => b i x * b j x) (fun x => b i x * b j x), ho]
      split_ifs <;> norm_num
    simp_rw [hp]
    simp
  simp_rw [hinner]
  simp

/-- The prescribed fine kernel has squared integral equal to its finite rank.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the fine kernel square integral conclusion](goal) holds. -/
lemma fineKernel_square_integral (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) :
    (∫ p, (fineKernel d h J p.1 p.2)^2 ∂(locLaw d h).prod (locLaw d h)) =
      (Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d := by
  let : SFinite (locLaw d h) := by unfold locLaw; infer_instance
  unfold fineKernel
  rw [finite_orthonormal_kernel_square (locLaw d h)
    (fun i x => fineBasis h J x i) (fineBasis_memLp d h J hh hh' hJ)
    (fun i j => by
      have ho := fine_orthonormal d h J hh hh' hJ i j
      by_cases hij : i = j
      · simp only [if_pos hij] at ho ⊢; exact ho
      · simp only [if_neg hij] at ho ⊢; exact ho)]
  rw [fineIdx_card]
  push_cast
  rfl

/-- The assigned half-open cells are disjoint, including their last closed face.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input x](hyp:x), [the specified input z](hyp:z), [the specified input w](hyp:w), [the specified input hz](hyp:hz), [the specified input hw](hyp:hw), [the cell index unique conclusion](goal) holds. -/
lemma cell_index_unique (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h)
    (hJ : 1 ≤ J) (x : Cov d) (z w : Fin d → Fin J)
    (hz : x ∈ cell h J z) (hw : x ∈ cell h J w) : z = w := by
  have hJp : 0 < (J:ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hd : 0 < h/J := div_pos hh hJp
  funext i
  apply Fin.ext
  have hzi := hz i
  have hwi := hw i
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : ¬ (z i).val + 1 = J := by have := (w i).isLt; omega
    have hzw : (z i:ℝ)+1 ≤ (w i:ℝ) := by exact_mod_cast hlt
    simp only [if_neg hn] at hzi
    have hm := mul_le_mul_of_nonneg_right hzw hd.le
    linarith [hwi.1, hzi.2]
  · have hn : ¬ (w i).val + 1 = J := by have := (z i).isLt; omega
    have hwz : (w i:ℝ)+1 ≤ (z i:ℝ) := by exact_mod_cast hgt
    simp only [if_neg hn] at hwi
    have hm := mul_le_mul_of_nonneg_right hwz hd.le
    linarith [hzi.1, hwi.2]

/-- Fine coordinates lie in the same reference interval after centering in their cell.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input x](hyp:x), [the specified input u](hyp:u), [the fine basis abs bound conclusion](goal) holds. -/
lemma fineBasis_abs_bound (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h)
    (hJ : 1 ≤ J) (x : Cov d) (u : FineIdx d J) :
    |fineBasis h J x u| ≤ Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d := by
  have hJp : 0 < (J:ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hd : 0 < h/J := div_pos hh hJp
  unfold fineBasis
  split_ifs with hx
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Finset.abs_prod]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    calc
      _ ≤ ∏ i : Fin d, (4:ℝ) := by
        apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
        intro i _
        apply legendre_abs_le_four
        have hi := hx i
        have hu : x i ≤ 1/2-h/2+((u.1 i:ℝ)+1)*(h/J) := by
          split_ifs at hi with hn
          · have he : (u.1 i:ℝ)+1 = J := by exact_mod_cast hn
            rw [he]
            have he' : (J:ℝ)*(h/J) = h := by field_simp
            linarith [hi.2]
          · exact hi.2.le
        rw [abs_le]
        constructor
        · apply (le_div_iff₀ hd).2
          linarith [hi.1]
        · apply (div_le_iff₀ hd).2
          linarith
      _ = _ := by simp
  · simp only [abs_zero]
    positivity

/-- Orthonormality of the cell's constant entry normalizes the absolute basis integral.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the fine basis abs integral bound conclusion](goal) holds. -/
lemma fineBasis_abs_integral_bound (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) (u : FineIdx d J) :
    Integrable (fun x => |fineBasis h J x u|) (locLaw d h) ∧
    (∫ x, |fineBasis h J x u| ∂locLaw d h) ≤
      (4:ℝ)^d / Real.sqrt ((J:ℝ)^d) := by
  let z0 : PolyIdx d := ⟨fun _ => 0, by simp⟩
  let b0 := fun x : Cov d => fineBasis h J x (u.1,z0)
  have hJp : 0 < (J:ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hs : 0 < Real.sqrt ((J:ℝ)^d) := Real.sqrt_pos.2 (by positivity)
  have hb0 : Integrable (fun x => (b0 x)^2) (locLaw d h) :=
    (fineBasis_memLp d h J hh hh' hJ (u.1,z0)).integrable_sq
  have hb0norm : (∫ x, (b0 x)^2 ∂locLaw d h) = 1 := by
    have ho := fine_orthonormal d h J hh hh' hJ (u.1,z0) (u.1,z0)
    simpa only [b0, pow_two, ite_true] using ho
  have hpoint (x : Cov d) : |fineBasis h J x u| ≤
      ((4:ℝ)^d / Real.sqrt ((J:ℝ)^d)) * (b0 x)^2 := by
    by_cases hx : x ∈ cell h J u.1
    · have he : b0 x = Real.sqrt ((J:ℝ)^d) := by
        simp [b0, fineBasis, hx, z0, legendre]
      rw [he]
      have hc : ((4:ℝ)^d / Real.sqrt ((J:ℝ)^d)) * (Real.sqrt ((J:ℝ)^d))^2 =
          Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d := by field_simp
      rw [hc]
      exact fineBasis_abs_bound d h J hh hJ x u
    · simp [fineBasis, hx, b0]
  have hmajor := hb0.const_mul ((4:ℝ)^d / Real.sqrt ((J:ℝ)^d))
  have hint : Integrable (fun x => |fineBasis h J x u|) (locLaw d h) := by
    apply hmajor.mono'
    · fun_prop
    · exact Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs, abs_abs] using hpoint x)
  refine ⟨hint, ?_⟩
  have hm := integral_mono hint hmajor hpoint
  rwa [integral_const_mul, hb0norm, mul_one] at hm

/-- Only one cell contributes to a kernel row; its normalization cancels the grid scale.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input x](hyp:x), [the fine kernel abs row bound conclusion](goal) holds. -/
lemma fineKernel_abs_row_bound (d : ℕ) (h : ℝ) (J : ℕ)
    (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) (x : Cov d) :
    (∫ y, |fineKernel d h J x y| ∂locLaw d h) ≤
      (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2 := by
  classical
  by_cases hex : ∃ z : Fin d → Fin J, x ∈ cell h J z
  · obtain ⟨z, hz⟩ := hex
    have hk (y : Cov d) : fineKernel d h J x y =
        ∑ u : PolyIdx d, fineBasis h J x (z,u) * fineBasis h J y (z,u) := by
      unfold fineKernel
      rw [Fintype.sum_prod_type]
      have hzero (w : Fin d → Fin J) (hw : w ≠ z) :
          (∑ u : PolyIdx d, fineBasis h J x (w,u) * fineBasis h J y (w,u)) = 0 := by
        have hn : x ∉ cell h J w := fun hw' => hw (cell_index_unique d h J hh hJ x w z hw' hz)
        simp [fineBasis, hn]
      exact Finset.sum_eq_single z (fun w _ hw => hzero w hw) (by simp)
    let F := fun y : Cov d => ∑ u : PolyIdx d,
      |fineBasis h J x (z,u)| * |fineBasis h J y (z,u)|
    have hF : Integrable F (locLaw d h) := integrable_finsetSum _
      (fun u _ => (fineBasis_abs_integral_bound d h J hh hh' hJ (z,u)).1.const_mul _)
    have hpoint (y : Cov d) : |fineKernel d h J x y| ≤ F y := by
      rw [hk]
      simpa only [F, abs_mul] using Finset.abs_sum_le_sum_abs
        (fun u : PolyIdx d => fineBasis h J x (z,u) * fineBasis h J y (z,u)) Finset.univ
    have hint : Integrable (fun y => |fineKernel d h J x y|) (locLaw d h) := by
      apply hF.mono'
      · fun_prop
      · exact Filter.Eventually.of_forall (fun y => by
          simpa only [Real.norm_eq_abs, abs_abs] using hpoint y)
    calc
      _ ≤ ∫ y, F y ∂locLaw d h := integral_mono hint hF hpoint
      _ = ∑ u : PolyIdx d, |fineBasis h J x (z,u)| *
          (∫ y, |fineBasis h J y (z,u)| ∂locLaw d h) := by
        dsimp only [F]
        rw [integral_finsetSum (f := fun u y => |fineBasis h J x (z,u)| * |fineBasis h J y (z,u)|)
          Finset.univ (fun u _ => (fineBasis_abs_integral_bound d h J hh hh' hJ (z,u)).1.const_mul _)]
        simp_rw [integral_const_mul]
      _ ≤ ∑ _u : PolyIdx d, ((4:ℝ)^d)^2 := by
        apply Finset.sum_le_sum
        intro u _
        have hu := fineBasis_abs_integral_bound d h J hh hh' hJ (z,u)
        have hb := fineBasis_abs_bound d h J hh hJ x (z,u)
        have hs : 0 < Real.sqrt ((J:ℝ)^d) := Real.sqrt_pos.2
          (pow_pos (by exact_mod_cast (show 0 < J by omega)) _)
        calc
          _ ≤ (Real.sqrt ((J:ℝ)^d) * (4:ℝ)^d) * ((4:ℝ)^d / Real.sqrt ((J:ℝ)^d)) :=
            mul_le_mul hb hu.2 (integral_nonneg (fun y => abs_nonneg _)) (by positivity)
          _ = _ := by field_simp
      _ = _ := by simp
  · have hk (y : Cov d) : fineKernel d h J x y = 0 := by
      unfold fineKernel
      apply Finset.sum_eq_zero
      intro u _
      have hn : x ∉ cell h J u.1 := fun hx => hex ⟨u.1,hx⟩
      simp [fineBasis, hn]
    simp_rw [hk, abs_zero, integral_zero]
    positivity

/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the kernel basis bounds conclusion](goal) holds. -/
lemma kernel_basis_bounds (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ h J, 0 < h → h ≤ 1/2 → 1 ≤ J →
      (∀ x ∈ locCube d h, Real.sqrt (∑ u : PolyIdx d, (coarseBasis h x u)^2) ≤ C) ∧
      (∀ x ∈ locCube d h, (∫ xp, |fineKernel d h J x xp| ∂locLaw d h) ≤ C) ∧
      (∫ p, (fineKernel d h J p.1 p.2)^2 ∂(locLaw d h).prod (locLaw d h)) =
        (Fintype.card (PolyIdx d):ℝ)*(J:ℝ)^d := by
  let B := Real.sqrt (Fintype.card (PolyIdx d):ℝ) * (4:ℝ)^d
  let C := (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max (B+1) C, lt_of_lt_of_le hC (le_max_right _ _), ?_⟩
  intro h J hh hh' hJ
  refine ⟨?_, ?_, fineKernel_square_integral d h J hh hh' hJ⟩
  · intro x hx
    exact (coarseBasis_vector_bound d h hh x hx).trans
      ((by dsimp only [B]; linarith : B ≤ B+1).trans (le_max_left _ _))
  · intro x hx
    exact (fineKernel_abs_row_bound d h J hh hh' hJ x).trans
      ((by dsimp only [C]; linarith : (Fintype.card (PolyIdx d):ℝ) * ((4:ℝ)^d)^2 ≤ C).trans (le_max_right _ _))

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
