module
public import Causalean.Mathlib.MeasureTheory.Integral.FiniteOrthonormal
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Projection

Two-channel point-CATE annotation frontier: Projection
constructions and obligations.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


-- @env: S3
variable {d : ℕ}
/-- Multi-indices of total degree at most two.  Given [the specified input d](hyp:d), [poly idx](goal) is the corresponding construction. -/
abbrev PolyIdx (d : ℕ) := {κ : Fin d → ℕ // (∑ i, κ i) ≤ 2}
/-- Given [the specified input d](hyp:d), [the poly idx finite conclusion](goal) holds. -/
lemma polyIdx_finite (d : ℕ) : Finite (PolyIdx d) := by
  let encode : PolyIdx d → (Fin d → Fin 3) := fun κ i =>
    ⟨κ.1 i, Nat.lt_succ_of_le ((Finset.single_le_sum
      (fun j _ => Nat.zero_le (κ.1 j)) (Finset.mem_univ i)).trans κ.2)⟩
  apply Finite.of_injective encode
  intro κ κ' h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)
/-- For [dimension d](hyp:d), [the degree-at-most-two multi-indices form a finite type](goal). -/
instance (d : ℕ) : Fintype (PolyIdx d) := @Fintype.ofFinite _ (polyIdx_finite d)
/-- Given [the specified input d](hyp:d), [the specified input J](hyp:J), [fine idx](goal) is the corresponding construction. -/
abbrev FineIdx (d J : ℕ) := (Fin d → Fin J) × PolyIdx d
/-- Given [the specified input d](hyp:d), [the poly idx card conclusion](goal) holds. -/
lemma polyIdx_card (d : ℕ) : Fintype.card (PolyIdx d) = Nat.choose (d+2) 2 := by
  -- Add a slack coordinate to turn the degree bound into total degree exactly two.
  let slack : PolyIdx d ≃ {f : Fin (d+1) → ℕ // ∑ i, f i = 2} :=
    { toFun := fun κ => ⟨Fin.cons (2 - ∑ i, κ.1 i) κ.1, by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact Nat.sub_add_cancel κ.2⟩
      invFun := fun f => ⟨fun i => f.1 i.succ, by
        change (∑ i : Fin d, f.1 i.succ) ≤ 2
        have hf := f.2
        rw [Fin.sum_univ_succ] at hf
        omega⟩
      left_inv := fun κ => by
        apply Subtype.ext
        funext i
        rfl
      right_inv := fun f => by
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          have hf := f.2
          rw [Fin.sum_univ_succ] at hf
          omega
        · rfl }
  calc
    Fintype.card (PolyIdx d) = Fintype.card (Sym (Fin (d+1)) 2) :=
      Fintype.card_congr (slack.trans (Sym.equivNatSumOfFintype (Fin (d+1)) 2).symm)
    _ = Nat.choose (d+2) 2 := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      congr 1
/-- Given [the specified input d](hyp:d), [the specified input J](hyp:J), [the fine idx card conclusion](goal) holds. -/
lemma fineIdx_card (d J : ℕ) : Fintype.card (FineIdx d J) = Fintype.card (PolyIdx d) * J^d := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  exact Nat.mul_comm _ _
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [loc cube](goal) is the corresponding construction. -/
def locCube (d : ℕ) (h : ℝ) : Set (Cov d) :=
  {x | ∀ i, x i ∈ Icc (1/2-h/2) (1/2+h/2)} -- @realizes Ch(local cube) @realizes h(localization input)
/-- Given [the specified input h](hyp:h), [the specified input x](hyp:x), [loc weight](goal) is the corresponding construction. -/
def locWeight (h : ℝ) (x : Cov d) : ℝ := if x ∈ locCube d h then h^(-(d:ℝ)) else 0 -- @realizes wh(localization weight)
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [loc law](goal) is the corresponding construction. -/
def locLaw (d : ℕ) (h : ℝ) : Measure (Cov d) :=
  ENNReal.ofReal (h^(-(d:ℝ))) • volume.restrict (locCube d h) -- @realizes nuh(known localization law)
/-- Given [the specified input k](hyp:k), [the specified input u](hyp:u), [legendre](goal) is the corresponding construction. -/
def legendre (k : ℕ) (u : ℝ) : ℝ :=
  if k = 0 then 1 else if k = 1 then Real.sqrt 12 * u else Real.sqrt 5 * (6*u^2-1/2)
/-- Given [the specified input h](hyp:h), [the specified input x](hyp:x), [coarse basis](goal) is the corresponding construction. -/
def coarseBasis (h : ℝ) (x : Cov d) (κ : PolyIdx d) : ℝ :=
  ∏ i, legendre (κ.1 i) ((x i-1/2)/h) -- @realizes r(scaled Legendre vector)
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [r0](goal) is the corresponding construction. -/
def r0 (d : ℕ) (h : ℝ) : PolyIdx d → ℝ := coarseBasis h (x0 d) -- @realizes r0(basis at target)
/-- Given [the specified input h](hyp:h), [the specified input v](hyp:v), [the specified input x](hyp:x), [pv](goal) is the corresponding construction. -/
def pv (h : ℝ) (v : PolyIdx d → ℝ) (x : Cov d) : ℝ := ∑ κ, coarseBasis h x κ * v κ -- @realizes pv(polynomial formula) @realizes v(coefficient vector)
/-- Given [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input z](hyp:z), [cell](goal) is the corresponding construction. -/
def cell (h : ℝ) (J : ℕ) (z : Fin d → Fin J) : Set (Cov d) :=
  {x | ∀ i, 1/2-h/2 + (z i:ℝ)*(h/J) ≤ x i ∧
    (if (z i).val + 1 = J then x i ≤ 1/2+h/2 else x i < 1/2-h/2 + ((z i:ℝ)+1)*(h/J))}
/-- Given [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input x](hyp:x), [the specified input z](hyp:z), [fine basis](goal) is the corresponding construction. -/
def fineBasis (h : ℝ) (J : ℕ) (x : Cov d) (zκ : FineIdx d J) : ℝ :=
  if x ∈ cell h J zκ.1 then Real.sqrt ((J:ℝ)^d) *
    ∏ i, legendre (zκ.2.1 i) ((x i-(1/2-h/2+((zκ.1 i:ℝ)+1/2)*(h/J)))/(h/J))
  else 0 -- @realizes bvec(cellwise Legendre basis)
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input x](hyp:x), [the specified input xp](hyp:xp), [fine kernel](goal) is the corresponding construction. -/
def fineKernel (d : ℕ) (h : ℝ) (J : ℕ) (x xp : Cov d) : ℝ :=
  ∑ z : FineIdx d J, fineBasis h J x z * fineBasis h J xp z -- @realizes K(projection kernel)
-- @node: def:projection
/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input f](hyp:f), [the specified input x](hyp:x), [proj op](goal) is the corresponding construction. -/
def projOp (d : ℕ) (h : ℝ) (J : ℕ) (f : Cov d → ℝ) (x : Cov d) : ℝ :=
  ∫ xp, fineKernel d h J x xp * f xp ∂locLaw d h -- @realizes Proj(kernel integral)
/-- Localization windows are closed boxes.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the is closed loc cube conclusion](goal) holds. -/
lemma isClosed_locCube (d : ℕ) (h : ℝ) : IsClosed (locCube d h) := by
  unfold locCube
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_Icc.preimage (by fun_prop)

/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input z](hyp:z), [the measurable set cell conclusion](goal) holds. -/
lemma measurableSet_cell (d : ℕ) (h : ℝ) (J : ℕ) (z : Fin d → Fin J) :
    MeasurableSet (cell h J z) := by
  unfold cell
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : (z i).val + 1 = J
  · simp only [if_pos hi]
    exact (measurableSet_le measurable_const (show Measurable (fun x : Cov d => x i) by fun_prop)).inter
      (measurableSet_le (show Measurable (fun x : Cov d => x i) by fun_prop) measurable_const)
  · simp only [if_neg hi]
    exact (measurableSet_le measurable_const (show Measurable (fun x : Cov d => x i) by fun_prop)).inter
      (measurableSet_lt (show Measurable (fun x : Cov d => x i) by fun_prop) measurable_const)

/-- Given [the specified input k](hyp:k), [the measurable legendre conclusion](goal) holds. -/
@[fun_prop] lemma measurable_legendre (k : ℕ) : Measurable (legendre k) := by
  unfold legendre
  split_ifs <;> fun_prop

/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input u](hyp:u), [the measurable coarse basis conclusion](goal) holds. -/
@[fun_prop] lemma measurable_coarseBasis (d : ℕ) (h : ℝ) (u : PolyIdx d) :
    Measurable (fun x : Cov d => coarseBasis h x u) := by
  unfold coarseBasis
  fun_prop

/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the measurable loc weight conclusion](goal) holds. -/
@[fun_prop] lemma measurable_locWeight (d : ℕ) (h : ℝ) :
    Measurable (locWeight (d:=d) h) := by
  unfold locWeight
  exact Measurable.ite (isClosed_locCube d h).measurableSet measurable_const measurable_const

/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input z](hyp:z), [the measurable fine basis conclusion](goal) holds. -/
@[fun_prop] lemma measurable_fineBasis (d : ℕ) (h : ℝ) (J : ℕ) (z : FineIdx d J) :
    Measurable (fun x : Cov d => fineBasis h J x z) := by
  unfold fineBasis
  apply Measurable.ite (measurableSet_cell d h J z.1) <;> fun_prop

/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the measurable fine kernel conclusion](goal) holds. -/
@[fun_prop] lemma measurable_fineKernel (d : ℕ) (h : ℝ) (J : ℕ) :
    Measurable (fun p : Cov d × Cov d => fineKernel d h J p.1 p.2) := by
  unfold fineKernel
  fun_prop

/-- Direct integration gives orthogonality for degrees zero, one and two on the reference interval.  Given [the specified input k](hyp:k), [the specified input l](hyp:l), [the specified input hk](hyp:hk), [the specified input hl](hyp:hl), [the legendre interval orthogonality conclusion](goal) holds. -/
lemma legendre_interval_orthogonality (k l : ℕ) (hk : k ≤ 2) (hl : l ≤ 2) :
    (∫ x in (-1/2:ℝ)..(1/2:ℝ), legendre k x * legendre l x) =
      if k = l then 1 else 0 := by
  interval_cases k <;> interval_cases l <;>
    norm_num [legendre] <;>
    (conv_lhs => arg 1; ext x; ring_nf) <;>
    simp (disch := apply Continuous.intervalIntegrable; fun_prop)
      [intervalIntegral.integral_add, intervalIntegral.integral_sub,
       intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
       integral_pow, integral_id,
       Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),
       Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12)] <;> norm_num <;>
    (rw [intervalIntegral.integral_const_mul, integral_id]; norm_num)
/-- For [degree k](hyp:k), [the corresponding Legendre polynomial is continuous on the real line](goal). -/
@[fun_prop] lemma continuous_legendre (k : ℕ) : Continuous (legendre k) := by
  unfold legendre
  split_ifs <;> fun_prop

/-- Affine rescaling multiplies each one-dimensional orthogonality integral by the side length.  Given [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input k](hyp:k), [the specified input l](hyp:l), [the specified input hk](hyp:hk), [the specified input hl](hyp:hl), [the scaled legendre orthogonality conclusion](goal) holds. -/
lemma scaled_legendre_orthogonality (h : ℝ) (hh : 0 < h)
    (k l : ℕ) (hk : k ≤ 2) (hl : l ≤ 2) :
    (∫ x in Icc (1/2-h/2) (1/2+h/2),
      legendre k ((x-1/2)/h) * legendre l ((x-1/2)/h)) =
      h * (if k = l then 1 else 0) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (1/2-h/2:ℝ) ≤ 1/2+h/2)]
  simp_rw [sub_div]
  rw [intervalIntegral.integral_comp_div_sub
    (fun x => legendre k x * legendre l x) hh.ne' ((1/2)/h)]
  have ha : (1/2-h/2)/h - (1/2)/h = (-1/2:ℝ) := by field_simp; ring
  have hb : (1/2+h/2)/h - (1/2)/h = (1/2:ℝ) := by field_simp; ring
  rw [ha, hb, legendre_interval_orthogonality k l hk hl]
  rfl

/-- Integration of a coordinate product over a Euclidean box factors into one-dimensional integrals.  Given [the specified input d](hyp:d), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input f](hyp:f), [the euclidean box product integral conclusion](goal) holds. -/
lemma euclidean_box_product_integral (d : ℕ) (a b : ℝ) (f : Fin d → ℝ → ℝ) :
    (∫ x : Cov d in {x | ∀ i, x i ∈ Icc a b}, ∏ i, f i (x i)) =
      ∏ i, ∫ x in Icc a b, f i x := by
  have ht := (PiLp.volume_preserving_ofLp (Fin d)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
    (fun x : Fin d → ℝ => ∏ i, f i (x i)) (Set.pi Set.univ (fun _ => Icc a b))
  change (∫ x : Cov d in WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ => Icc a b),
    ∏ i, f i (x i)) = _ at ht
  rw [show {x : Cov d | ∀ i, x i ∈ Icc a b} =
      WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ => Icc a b) by ext x; simp [Pi.le_def, forall_and]]
  rw [ht]
  change (∫ y : Fin d → ℝ, ∏ i, f i (y i) ∂(Measure.pi (fun _ => volume)).restrict _) = _
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod _

/-- Euclidean product-set integrals factor across arbitrary coordinate sets.  Given [the specified input d](hyp:d), [the specified input s](hyp:s), [the specified input f](hyp:f), [the euclidean product set integral conclusion](goal) holds. -/
lemma euclidean_product_set_integral (d : ℕ) (s : Fin d → Set ℝ)
    (f : Fin d → ℝ → ℝ) :
    (∫ x : Cov d in {x | ∀ i, x i ∈ s i}, ∏ i, f i (x i)) =
      ∏ i, ∫ x in s i, f i x := by
  have ht := (PiLp.volume_preserving_ofLp (Fin d)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
    (fun x : Fin d → ℝ => ∏ i, f i (x i)) (Set.pi Set.univ s)
  change (∫ x : Cov d in WithLp.ofLp ⁻¹' Set.pi Set.univ s,
    ∏ i, f i (x i)) = _ at ht
  rw [show {x : Cov d | ∀ i, x i ∈ s i} =
      WithLp.ofLp ⁻¹' Set.pi Set.univ s by ext x; simp only
        [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]]
  rw [ht]
  change (∫ y : Fin d → ℝ, ∏ i, f i (y i) ∂(Measure.pi (fun _ => volume)).restrict _) = _
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod _

/-- A centered cell of any positive side length has the same Legendre orthogonality.  Given [the specified input c](hyp:c), [the specified input t](hyp:t), [the specified input ht](hyp:ht), [the specified input k](hyp:k), [the specified input l](hyp:l), [the specified input hk](hyp:hk), [the specified input hl](hyp:hl), [the centered legendre orthogonality conclusion](goal) holds. -/
lemma centered_legendre_orthogonality (c t : ℝ) (ht : 0 < t)
    (k l : ℕ) (hk : k ≤ 2) (hl : l ≤ 2) :
    (∫ x in Icc (c-t/2) (c+t/2),
      legendre k ((x-c)/t) * legendre l ((x-c)/t)) =
      t * (if k = l then 1 else 0) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : c-t/2 ≤ c+t/2)]
  simp_rw [sub_div]
  rw [intervalIntegral.integral_comp_div_sub
    (fun x => legendre k x * legendre l x) ht.ne' (c/t)]
  have ha : (c-t/2)/t - c/t = (-1/2:ℝ) := by field_simp; ring
  have hb : (c+t/2)/t - c/t = (1/2:ℝ) := by field_simp; ring
  rw [ha, hb, legendre_interval_orthogonality k l hk hl]
  rfl

/-- Every cell stays inside the localization box, including its assigned upper face.  Given [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input z](hyp:z), [the cell subset loc cube conclusion](goal) holds. -/
lemma cell_subset_locCube (h : ℝ) (J : ℕ) (hh : 0 < h) (hJ : 1 ≤ J)
    (z : Fin d → Fin J) : cell h J z ⊆ locCube d h := by
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  intro x hx i
  have hi := hx i
  have hz : (z i:ℝ) + 1 ≤ J := by exact_mod_cast (z i).isLt
  constructor
  · have hn : 0 ≤ (z i:ℝ)*(h/J) := mul_nonneg (Nat.cast_nonneg _) ht.le
    linarith [hi.1]
  · by_cases hf : (z i).val + 1 = J
    · simpa only [if_pos hf] using hi.2
    · have hu : ((z i:ℝ)+1)*(h/J) ≤ h := by
        calc
          _ ≤ (J:ℝ)*(h/J) := mul_le_mul_of_nonneg_right hz ht.le
          _ = h := by field_simp
      have hi' := hi.2
      rw [if_neg hf] at hi'
      linarith

/-- Distinct half-open grid cells are disjoint.  Given [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input z](hyp:z), [the specified input w](hyp:w), [the specified input hzw](hyp:hzw), [the cells disjoint conclusion](goal) holds. -/
lemma cells_disjoint (h : ℝ) (J : ℕ) (hh : 0 < h) (hJ : 1 ≤ J)
    (z w : Fin d → Fin J) (hzw : z ≠ w) : Disjoint (cell h J z) (cell h J w) := by
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  have hne : ∃ i, z i ≠ w i := by
    by_contra hn
    apply hzw
    funext i
    exact not_ne_iff.mp (not_exists.mp hn i)
  obtain ⟨i, hi⟩ := hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  have horder (z w : Fin J) (hlt : z < w)
      (hz : 1/2-h/2+(z:ℝ)*(h/J) ≤ x i ∧
        (if z.val+1 = J then x i ≤ 1/2+h/2 else x i < 1/2-h/2+((z:ℝ)+1)*(h/J)))
      (hw : 1/2-h/2+(w:ℝ)*(h/J) ≤ x i) : False := by
    have hfinal : z.val+1 ≠ J := by have := w.isLt; change z.val < w.val at hlt; omega
    rw [if_neg hfinal] at hz
    have hle : (z:ℝ)+1 ≤ w := by exact_mod_cast hlt
    have hm := mul_le_mul_of_nonneg_right hle ht.le
    linarith [hz.2]
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · exact horder (z i) (w i) hlt (hx i) (hy i).1
  · exact horder (w i) (z i) hlt (hy i) (hx i).1
/-- Cell face assignments do not change the product Legendre integrals.  Given [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hJ](hyp:hJ), [the specified input z](hyp:z), [the specified input u](hyp:u), [the specified input v](hyp:v), [the cell legendre product integral conclusion](goal) holds. -/
lemma cell_legendre_product_integral (h : ℝ) (J : ℕ) (hh : 0 < h) (hJ : 1 ≤ J)
    (z : Fin d → Fin J) (u v : PolyIdx d) :
    (∫ x in cell h J z, ∏ i,
      legendre (u.1 i) ((x i-(1/2-h/2+((z i:ℝ)+1/2)*(h/J)))/(h/J)) *
      legendre (v.1 i) ((x i-(1/2-h/2+((z i:ℝ)+1/2)*(h/J)))/(h/J))) =
      (h/(J:ℝ))^d * (if u = v then 1 else 0) := by
  classical
  have hj : (0:ℝ) < J := by exact_mod_cast hJ
  have ht : 0 < h/(J:ℝ) := div_pos hh hj
  let c : Fin d → ℝ := fun i => 1/2-h/2+((z i:ℝ)+1/2)*(h/J)
  let s : Fin d → Set ℝ := fun i => if (z i).val+1 = J then
    Icc (c i-(h/J)/2) (c i+(h/J)/2) else Ico (c i-(h/J)/2) (c i+(h/J)/2)
  have hlo (i : Fin d) : c i-(h/J)/2 = 1/2-h/2+(z i:ℝ)*(h/J) := by dsimp [c]; ring
  have hup (i : Fin d) : c i+(h/J)/2 = 1/2-h/2+((z i:ℝ)+1)*(h/J) := by dsimp [c]; ring
  have hfinal (i : Fin d) (hi : (z i).val+1 = J) : c i+(h/J)/2 = 1/2+h/2 := by
    rw [hup]
    have hz : (z i:ℝ)+1 = J := by exact_mod_cast hi
    rw [hz]
    field_simp
    ring
  have hs : cell h J z = {x : Cov d | ∀ i, x i ∈ s i} := by
    ext x
    simp only [cell, Set.mem_setOf_eq]
    apply forall_congr'
    intro i
    by_cases hi : (z i).val+1 = J
    · simp only [s, if_pos hi, Set.mem_Icc, hlo, hfinal i hi]
    · simp only [s, if_neg hi, Set.mem_Ico, hlo, hup]
  rw [hs, euclidean_product_set_integral d s
    (fun i x => legendre (u.1 i) ((x-c i)/(h/J)) * legendre (v.1 i) ((x-c i)/(h/J)))]
  have hk (w : PolyIdx d) (i : Fin d) : w.1 i ≤ 2 :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (w.1 j)) (Finset.mem_univ i)).trans w.2
  have hint (i : Fin d) : (∫ x in s i,
      legendre (u.1 i) ((x-c i)/(h/J)) * legendre (v.1 i) ((x-c i)/(h/J))) =
      (h/J) * (if u.1 i = v.1 i then 1 else 0) := by
    by_cases hi : (z i).val+1 = J
    · simp only [s, if_pos hi]
      exact centered_legendre_orthogonality (c i) (h/J) ht _ _ (hk u i) (hk v i)
    · simp only [s, if_neg hi]
      rw [restrict_Ico_eq_restrict_Icc]
      exact centered_legendre_orthogonality (c i) (h/J) ht _ _ (hk u i) (hk v i)
  simp_rw [hint]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  by_cases huv : u = v
  · subst v; simp
  · rw [if_neg huv]
    have hne : ∃ i, u.1 i ≠ v.1 i := by
      by_contra hn
      apply huv
      apply Subtype.ext
      funext i
      exact not_ne_iff.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)


/-- The scaled coarse Legendre basis is orthonormal under localization measure.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input u](hyp:u), [the specified input v](hyp:v), [the coarse orthonormal conclusion](goal) holds. -/
lemma coarse_orthonormal (d : ℕ) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2) (u v : PolyIdx d) :
    (∫ x, coarseBasis h x u * coarseBasis h x v ∂locLaw d h) = if u = v then 1 else 0 := by
  classical
  rw [locLaw, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  simp only [coarseBasis, ← Finset.prod_mul_distrib]
  rw [locCube]
  rw [euclidean_box_product_integral d (1/2-h/2) (1/2+h/2)
    (fun i x => legendre (u.1 i) ((x-1/2)/h) * legendre (v.1 i) ((x-1/2)/h))]
  simp only [smul_eq_mul]
  have hk (w : PolyIdx d) (i : Fin d) : w.1 i ≤ 2 :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (w.1 j)) (Finset.mem_univ i)).trans w.2
  simp_rw [scaled_legendre_orthogonality h hh _ _ (hk u _) (hk v _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnorm : h ^ (-(d:ℝ)) * h^d = 1 := by
    rw [Real.rpow_neg hh.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hh.ne')]
  rw [← mul_assoc, hnorm, one_mul]
  by_cases huv : u = v
  · subst v
    simp
  · rw [if_neg huv]
    have hne : ∃ i, u.1 i ≠ v.1 i := by
      by_contra hn
      apply huv
      apply Subtype.ext
      funext i
      exact not_ne_iff.mp (not_exists.mp hn i)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
/-- The cellwise Legendre basis is orthonormal, including the assigned grid faces.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the specified input v](hyp:v), [the fine orthonormal conclusion](goal) holds. -/
lemma fine_orthonormal (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J) (u v : FineIdx d J) :
    (∫ x, fineBasis h J x u * fineBasis h J x v ∂locLaw d h) = if u = v then 1 else 0 := by
  classical
  by_cases hz : u.1 = v.1
  · rcases u with ⟨z, u⟩
    rcases v with ⟨w, v⟩
    dsimp only at hz
    subst w
    have heq (x : Cov d) : fineBasis h J x (z,u) * fineBasis h J x (z,v) =
        (cell h J z).indicator (fun x => (J:ℝ)^d * ∏ i,
          legendre (u.1 i) ((x i-(1/2-h/2+((z i:ℝ)+1/2)*(h/J)))/(h/J)) *
          legendre (v.1 i) ((x i-(1/2-h/2+((z i:ℝ)+1/2)*(h/J)))/(h/J))) x := by
      by_cases hx : x ∈ cell h J z
      · simp only [fineBasis, hx, if_true, Set.indicator_of_mem hx]
        rw [Finset.prod_mul_distrib]
        rw [mul_mul_mul_comm, ← pow_two,
          Real.sq_sqrt (show (0:ℝ) ≤ (J:ℝ)^d by positivity)]
      · simp [fineBasis, hx]
    simp_rw [heq]
    rw [locLaw, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      integral_indicator (measurableSet_cell d h J z),
      Measure.restrict_restrict (measurableSet_cell d h J z),
      Set.inter_eq_left.mpr (cell_subset_locCube h J hh hJ z), integral_const_mul,
      cell_legendre_product_integral h J hh hJ z u v]
    simp only [smul_eq_mul, Prod.mk.injEq, true_and]
    have hj : (J:ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
    have hnorm : h ^ (-(d:ℝ)) * (J:ℝ)^d * (h/(J:ℝ))^d = 1 := by
      rw [Real.rpow_neg hh.le, Real.rpow_natCast, div_pow]
      field_simp
    simp only [← mul_assoc]
    rw [hnorm, one_mul]
  · rw [if_neg (fun huv => hz (congrArg Prod.fst huv))]
    have hzero (x : Cov d) : fineBasis h J x u * fineBasis h J x v = 0 := by
      by_cases hu : x ∈ cell h J u.1
      · have hv : x ∉ cell h J v.1 :=
          fun hv => Set.disjoint_left.mp (cells_disjoint h J hh hJ u.1 v.1 hz) hu hv
        simp [fineBasis, hv]
      · simp [fineBasis, hu]
    simp_rw [hzero]
    exact integral_zero _ _
/-- The diagonal orthonormality integral supplies square integrability of each fine basis entry.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the fine basis mem lp conclusion](goal) holds. -/
lemma fineBasis_memLp (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (hJ : 1 ≤ J) (u : FineIdx d J) :
    MemLp (fun x => fineBasis h J x u) 2 (locLaw d h) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  by_contra hi
  have hz := integral_undef hi
  have ho := fine_orthonormal d h J hh hh' hJ u u
  simp only [ite_true, ← pow_two] at ho
  rw [hz] at ho
  norm_num at ho

/-- Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input J](hyp:J), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input hJ](hyp:hJ), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the projection pythagoras conclusion](goal) holds. -/
lemma projection_pythagoras (d : ℕ) (h : ℝ) (J : ℕ) (hh : 0 < h) (hh' : h ≤ 1/2) (hJ : 1 ≤ J)
    (f : Cov d → ℝ) (hf : MemLp f 2 (locLaw d h)) :
    (∫ x, f x^2 ∂locLaw d h) = (∫ x, (projOp d h J f x)^2 ∂locLaw d h) +
      (∫ x, (f x - projOp d h J f x)^2 ∂locLaw d h) := by
  have hb := fineBasis_memLp d h J hh hh' hJ
  have hexpand (x : Cov d) : projOp d h J f x =
      ∑ i : FineIdx d J, fineBasis h J x i * (∫ y, fineBasis h J y i * f y ∂locLaw d h) := by
    unfold projOp fineKernel
    simp_rw [Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum (f := fun i y => fineBasis h J x i * (fineBasis h J y i * f y))
      Finset.univ (fun i _ => ((hb i).integrable_mul hf).const_mul (fineBasis h J x i))]
    simp_rw [integral_const_mul]
  simp_rw [hexpand]
  exact Causalean.Mathlib.MeasureTheory.finite_orthonormal_pythagoras
    (locLaw d h) (fun i x => fineBasis h J x i)
    hb (fun i j => by
      have ho := fine_orthonormal d h J hh hh' hJ i j
      by_cases hij : i = j
      · simp only [if_pos hij] at ho ⊢; exact ho
      · simp only [if_neg hij] at ho ⊢; exact ho) f hf

/-- Given [the specified input f](hyp:f), [the specified input p](hyp:p), [the specified input x](hyp:x), [taylor poly](goal) is the corresponding construction. -/
def taylorPoly (f : Cov d → ℝ) (p : ℕ) (x : Cov d) : ℝ :=
  ∑ κ ∈ Finset.univ.filter (fun κ : PolyIdx d => multiOrder κ.1 ≤ p),
    coordinatePartial f κ.1 (x0 d) / (∏ i, (Nat.factorial (κ.1 i) : ℝ)) *
      ∏ i, (x i - 1/2)^(κ.1 i)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
