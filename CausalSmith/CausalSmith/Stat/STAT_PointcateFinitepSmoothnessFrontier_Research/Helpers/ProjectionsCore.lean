module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Basic
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! Finite-moment point-CATE frontier: Helpers/ProjectionsCore. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


-- @env: S4
variable (h : ℝ) (J : ℕ) -- @realizes h(real bandwidth; 0<h≤1 in consumers) @realizes J(natural resolution)
/-- The closed localization window within the unit interval. -/
def window : Set unitInterval := {x | (x : ℝ) ∈ Icc (1/2 - h/2) (1/2 + h/2)} -- @realizes W(closed centered window)
/-- Dyadic cell length. -/
def cellLen (j : ℕ) : ℝ := h / (2 : ℝ)^j -- @realizes delta(h*2^(-j))
/-- Half-open dyadic cell labels, with the right endpoint assigned to the last cell. -/
def cellIndex (j : ℕ) (x : unitInterval) : ℕ :=
  min (2^j - 1) (Int.toNat ⌊((x : ℝ) - (1/2 - h/2)) / cellLen h j⌋)
/-- Public dyadic labels are Borel, including the endpoint convention. -/
-- @node: measurable_cellIndex
@[fun_prop] lemma measurable_cellIndex (j : ℕ) : Measurable (cellIndex h j) := by
  unfold cellIndex
  fun_prop
/-- A dyadic cell as a measurable subset of the localization window. -/
def cell (j l : ℕ) : Set unitInterval := {x | x ∈ window h ∧ cellIndex h j x = l}
-- @node: def:projections
/-- The explicit dyadic histogram projection kernel. -/
def projKernel (j : ℕ) (x z : unitInterval) : ℝ :=
  if x ∈ window h ∧ z ∈ window h ∧ cellIndex h j x = cellIndex h j z
    then (cellLen h j)⁻¹ else 0 -- @realizes Proj(inverse-cell-length histogram kernel)
/-- The histogram kernel is jointly Borel in its two covariates. -/
-- @node: measurable_projKernel
@[fun_prop] lemma measurable_projKernel (j : ℕ) :
    Measurable (fun xz : unitInterval × unitInterval => projKernel h j xz.1 xz.2) := by
  unfold projKernel
  apply Measurable.ite _ measurable_const measurable_const
  have hw : MeasurableSet (window h) := by
    exact measurable_subtype_coe (measurableSet_Icc)
  exact (hw.preimage measurable_fst).inter
    ((hw.preimage measurable_snd).inter
      (measurableSet_eq_fun ((measurable_cellIndex h j).comp measurable_fst)
        ((measurable_cellIndex h j).comp measurable_snd)))
/-- The integral operator of the dyadic histogram kernel. -/
def projOp (j : ℕ) (f : unitInterval → ℝ) (x : unitInterval) : ℝ :=
  ∫ z, projKernel h j x z * f z ∂design -- @realizes Proj(histogram integral operator)
/-- The difference of adjacent histogram kernels. -/
def bandKernel (j : ℕ) (x z : unitInterval) : ℝ :=
  projKernel h j x z - projKernel h (j-1) x z -- @realizes Band(P_j−P_(j−1); j≥1)
/-- Adjacent histogram differences remain jointly Borel. -/
-- @node: measurable_bandKernel
@[fun_prop] lemma measurable_bandKernel (j : ℕ) :
    Measurable (fun xz : unitInterval × unitInterval => bandKernel h j xz.1 xz.2) := by
  unfold bandKernel
  fun_prop
/-- The operator of an adjacent-level difference. -/
def bandOp (j : ℕ) (f : unitInterval → ℝ) (x : unitInterval) : ℝ :=
  ∫ z, bandKernel h j x z * f z ∂design -- @realizes Band(adjacent-level difference operator)
/-- An L2 window function has integrable histogram-kernel sections on the original design. -/
-- @node: integrable_projKernel_mul
lemma integrable_projKernel_mul (j : ℕ) (f : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h))) (x : unitInterval) :
    Integrable (fun z => projKernel h j x z * f z) design := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hw : MeasurableSet (window h) :=
    measurable_subtype_coe measurableSet_Icc
  have hl1 : IntegrableOn f (window h) design := hf.integrable (by norm_num)
  have hi : Integrable ((window h).indicator f) design :=
    hl1.integrable_indicator hw
  have hm : AEStronglyMeasurable (fun z => projKernel h j x z) design := by
    fun_prop
  have hb : ∀ᵐ z ∂design, ‖projKernel h j x z‖ ≤ |(cellLen h j)⁻¹| := by
    apply Filter.Eventually.of_forall
    intro z
    simp only [projKernel]
    split_ifs <;> simp
  have hp := hi.bdd_mul hm hb
  convert hp using 1
  funext z
  by_cases hz : z ∈ window h
  · simp [hz]
  · simp [projKernel, hz]

/-- Adjacent-level integration is the difference of the two histogram averages. -/
-- @node: bandOp_eq_sub
lemma bandOp_eq_sub (j : ℕ) (f : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h))) (x : unitInterval) :
    bandOp h j f x = projOp h j f x - projOp h (j-1) f x := by
  simp only [bandOp, bandKernel, sub_mul, projOp]
  exact integral_sub (integrable_projKernel_mul h j f hf x)
    (integrable_projKernel_mul h (j-1) f hf x)

/-- The adjacent histogram differences telescope to the finest-level average. -/
-- @node: projOp_telescope
lemma projOp_telescope (f : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h))) (x : unitInterval) :
    projOp h 0 f x + ∑ j ∈ Finset.range J, bandOp h (j+1) f x = projOp h J f x := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, bandOp_eq_sub h (J+1) f hf x]
    simp only [Nat.add_sub_cancel]
    linarith

/-- The histogram operator integrates only over its localization window. -/
-- @node: projOp_eq_window_integral
lemma projOp_eq_window_integral (j : ℕ) (f : unitInterval → ℝ) (x : unitInterval) :
    projOp h j f x = ∫ z in window h, projKernel h j x z * f z ∂design := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  rw [← integral_indicator hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ window h
  · simp [projOp, hz]
  · simp [projKernel, hz]

/-- Histogram cell membership is symmetric in the two kernel arguments. -/
-- @node: projKernel_symm
lemma projKernel_symm (j : ℕ) (x z : unitInterval) :
    projKernel h j x z = projKernel h j z x := by
  unfold projKernel
  congr 1
  exact propext (by constructor <;> rintro ⟨hx, hz, he⟩ <;> exact ⟨hz, hx, he.symm⟩)

/-- On its cell, the histogram average is the inverse cell length times the cell integral. -/
-- @node: projOp_eq_cell_average
lemma projOp_eq_cell_average (j : ℕ) (f : unitInterval → ℝ)
    (x : unitInterval) (hx : x ∈ window h) :
    projOp h j f x = (cellLen h j)⁻¹ * ∫ z in cell h j (cellIndex h j x), f z ∂design := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hc : MeasurableSet (cell h j (cellIndex h j x)) :=
    hw.inter ((measurable_cellIndex h j) (measurableSet_singleton _))
  rw [← integral_indicator hc, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ window h
  · by_cases he : cellIndex h j z = cellIndex h j x
    · simp [projKernel, cell, hx, hz, he]
    · have he' : cellIndex h j x ≠ cellIndex h j z := Ne.symm he
      simp [projKernel, cell, hx, hz, he, he']
  · simp [projKernel, cell, hz]

/-- Integrating the symmetric cell kernel in either order gives the same L² pairing. -/
-- @node: projOp_self_adjoint
lemma projOp_self_adjoint (j : ℕ) (f g : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h)))
    (hg : MemLp g 2 (design.restrict (window h))) :
    (∫ x in window h, projOp h j f x * g x ∂design) =
      ∫ x in window h, f x * projOp h j g x ∂design := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hi := (hg.integrable (by norm_num)).mul_prod (hf.integrable (by norm_num))
  have hm : AEStronglyMeasurable
      (fun z : unitInterval × unitInterval => projKernel h j z.1 z.2)
      ((design.restrict (window h)).prod (design.restrict (window h))) := by fun_prop
  have hb : ∀ᵐ z ∂((design.restrict (window h)).prod (design.restrict (window h))),
      ‖projKernel h j z.1 z.2‖ ≤ |(cellLen h j)⁻¹| := by
    apply Filter.Eventually.of_forall
    intro z
    simp only [projKernel]
    split_ifs <;> simp
  have hp := hi.bdd_mul hm hb
  have hp' : Integrable (Function.uncurry
      (fun x z => projKernel h j x z * f z * g x))
      ((design.restrict (window h)).prod (design.restrict (window h))) := by
    convert hp using 1
    funext z
    dsimp [Function.uncurry]
    ring
  calc
    _ = ∫ x in window h, ∫ z in window h,
        projKernel h j x z * f z * g x ∂design ∂design := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [projOp_eq_window_integral, integral_mul_const])
    _ = ∫ z in window h, ∫ x in window h,
        projKernel h j x z * f z * g x ∂design ∂design := integral_integral_swap hp'
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      rw [projOp_eq_window_integral, ← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [projKernel_symm h j x z]
      ring

/-- The localization window has its prescribed Lebesgue length. -/
-- @node: design_window
lemma design_window (hh : 0 < h ∧ h ≤ 1) :
    design (window h) = ENNReal.ofReal h := by
  let a : unitInterval := ⟨1/2 - h/2, by constructor <;> linarith [hh.1, hh.2]⟩
  let b : unitInterval := ⟨1/2 + h/2, by constructor <;> linarith [hh.1, hh.2]⟩
  have hw : window h = Icc a b := by
    ext x
    rfl
  rw [hw, design, unitInterval.volume_Icc]
  congr 1
  dsimp [a, b]
  ring

/-- The level-zero histogram kernel is constant on the window square. -/
-- @node: projKernel_zero_on_window
lemma projKernel_zero_on_window (x z : unitInterval)
    (hx : x ∈ window h) (hz : z ∈ window h) :
    projKernel h 0 x z = h⁻¹ := by
  simp [projKernel, cellIndex, cellLen, hx, hz]

/-- A coarse histogram-kernel section has squared norm equal to inverse bandwidth. -/
-- @node: projKernel_zero_sq_integral
lemma projKernel_zero_sq_integral (hh : 0 < h ∧ h ≤ 1)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, (projKernel h 0 x z)^2 ∂design) = h⁻¹ := by
  have hw : MeasurableSet (window h) := by
    exact measurable_subtype_coe measurableSet_Icc
  calc
    _ = ∫ x in window h, (h⁻¹)^2 ∂design := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hw] with x hx
      rw [projKernel_zero_on_window h x z hx hz]
    _ = h * (h⁻¹)^2 := by
      simp [integral_const, Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
    _ = h⁻¹ := by
      field_simp

/-- Away from the right window endpoint, the capped dyadic label is the usual floor. -/
-- @node: cellIndex_eq_floor_interior
lemma cellIndex_eq_floor_interior (hh : 0 < h) (j : ℕ) (x : unitInterval)
    (hx : x ∈ window h) (hr : (x : ℝ) < 1/2+h/2) :
    cellIndex h j x = ⌊((x : ℝ)-(1/2-h/2))/cellLen h j⌋₊ := by
  have hd : 0 < cellLen h j := by unfold cellLen; positivity
  have ht : ((x : ℝ)-(1/2-h/2))/cellLen h j < (2^j : ℕ) := by
    rw [div_lt_iff₀ hd]
    have he : (2^j : ℕ) * cellLen h j = h := by
      simp only [cellLen, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    rw [he]
    linarith
  have hf : ⌊((x : ℝ)-(1/2-h/2))/cellLen h j⌋₊ < 2^j :=
    (Nat.floor_lt (div_nonneg (sub_nonneg.mpr hx.1) hd.le)).mpr ht
  unfold cellIndex
  rw [Int.floor_toNat, min_eq_right (by omega)]

/-- Interior cell membership is exactly the half-open interval between its grid endpoints. -/
-- @node: cell_mem_iff_interior
lemma cell_mem_iff_interior (hh : 0 < h) (j l : ℕ) (hl : l < 2^j)
    (x : unitInterval) (hr : (x : ℝ) ≠ 1/2+h/2) :
    x ∈ cell h j l ↔
      1/2-h/2+(l : ℝ)*cellLen h j ≤ (x : ℝ) ∧
      (x : ℝ) < 1/2-h/2+((l : ℝ)+1)*cellLen h j := by
  have hd : 0 < cellLen h j := by unfold cellLen; positivity
  have he : (2^j : ℕ) * cellLen h j = h := by
    simp only [cellLen, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hle : (l : ℝ)+1 ≤ (2^j : ℕ) := by exact_mod_cast hl
  constructor
  · rintro ⟨hx, hi⟩
    have hx' : 1/2-h/2 ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1/2+h/2 := hx
    have ht : 0 ≤ ((x : ℝ)-(1/2-h/2))/cellLen h j := div_nonneg (sub_nonneg.mpr hx'.1) hd.le
    rw [cellIndex_eq_floor_interior h hh j x hx (lt_of_le_of_ne hx'.2 hr)] at hi
    obtain ⟨hlo, hup⟩ := (Nat.floor_eq_iff ht).mp hi
    rw [le_div_iff₀ hd] at hlo
    rw [div_lt_iff₀ hd] at hup
    constructor <;> linarith
  · rintro ⟨hlo, hup⟩
    have hb : ((l : ℝ)+1)*cellLen h j ≤ h := by
      calc
        _ ≤ (2^j : ℕ)*cellLen h j := mul_le_mul_of_nonneg_right hle hd.le
        _ = h := he
    have hx : x ∈ window h := by
      constructor
      · nlinarith [Nat.cast_nonneg (α := ℝ) l]
      · linarith
    refine ⟨hx, ?_⟩
    rw [cellIndex_eq_floor_interior h hh j x hx (by linarith)]
    apply (Nat.floor_eq_iff (by
      apply div_nonneg _ hd.le
      nlinarith [Nat.cast_nonneg (α := ℝ) l])).mpr
    constructor
    · rw [le_div_iff₀ hd]; linarith
    · rw [div_lt_iff₀ hd]; linarith

/-- Every dyadic cell has its prescribed length; the last-cell endpoint is null. -/
-- @node: design_cell
lemma design_cell (hh : 0 < h ∧ h ≤ 1) (j l : ℕ) (hl : l < 2^j) :
    design (cell h j l) = ENNReal.ofReal (cellLen h j) := by
  have hd : 0 < cellLen h j := by unfold cellLen; exact div_pos hh.1 (by positivity)
  have he : (2^j : ℕ)*cellLen h j = h := by
    simp only [cellLen, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hle : (l : ℝ)+1 ≤ (2^j : ℕ) := by exact_mod_cast hl
  have hb : ((l : ℝ)+1)*cellLen h j ≤ h := by
    calc
      _ ≤ (2^j : ℕ)*cellLen h j := mul_le_mul_of_nonneg_right hle hd.le
      _ = h := he
  have hn : 0 ≤ (l : ℝ)*cellLen h j := by positivity
  let a : unitInterval := ⟨1/2-h/2+(l : ℝ)*cellLen h j,
    by constructor <;> linarith [hh.2]⟩
  let b : unitInterval := ⟨1/2-h/2+((l : ℝ)+1)*cellLen h j,
    by constructor <;> linarith [hh.2]⟩
  let r : unitInterval := ⟨1/2+h/2, by constructor <;> linarith [hh.2]⟩
  have hae : cell h j l =ᵐ[design] Ico a b := by
    have hr : ∀ᵐ x ∂design, x ≠ r := by
      unfold design
      exact Measure.ae_ne _ r
    filter_upwards [hr] with x hx
    have hxr : (x : ℝ) ≠ 1/2+h/2 := by
      intro heq
      apply hx
      exact Subtype.ext heq
    exact propext (cell_mem_iff_interior h hh.1 j l hl x hxr)
  rw [measure_congr hae, design, unitInterval.volume_Ico]
  congr 1
  dsimp [a, b]
  ring

/-- Averaging over a cell preserves its integral exactly. -/
-- @node: projOp_cell_integral
lemma projOp_cell_integral (hh : 0 < h ∧ h ≤ 1) (j l : ℕ)
    (hl : l < 2^j) (f : unitInterval → ℝ) :
    (∫ x in cell h j l, projOp h j f x ∂design) =
      ∫ x in cell h j l, f x ∂design := by
  have hc : MeasurableSet (cell h j l) :=
    (measurable_subtype_coe measurableSet_Icc).inter
      ((measurable_cellIndex h j) (measurableSet_singleton l))
  have hd : 0 < cellLen h j := by unfold cellLen; exact div_pos hh.1 (by positivity)
  calc
    _ = ∫ _x in cell h j l, (cellLen h j)⁻¹ *
        (∫ z in cell h j l, f z ∂design) ∂design := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hc] with x hx
      rw [projOp_eq_cell_average h j f x hx.1, hx.2]
    _ = _ := by
      simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, design_cell h hh j l hl,
        ENNReal.toReal_ofReal hd.le]
      rw [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]

/-- Capping sends every dyadic label into the finite partition range. -/
-- @node: cellIndex_lt
lemma cellIndex_lt (j : ℕ) (x : unitInterval) : cellIndex h j x < 2^j := by
  have hp : 0 < 2^j := by positivity
  have hm := min_le_left (2^j-1) (Int.toNat ⌊((x : ℝ)-(1/2-h/2))/cellLen h j⌋)
  change min _ _ < _
  omega

/-- Reaveraging the same cell does not change its histogram average. -/
-- @node: projOp_idempotent
lemma projOp_idempotent (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (x : unitInterval) (hx : x ∈ window h) :
    projOp h j (projOp h j f) x = projOp h j f x := by
  rw [projOp_eq_cell_average h j (projOp h j f) x hx,
    projOp_cell_integral h hh j _ (cellIndex_lt h j x) f,
    ← projOp_eq_cell_average h j f x hx]

/-- Histogram averages are Borel functions, even for an arbitrary input function. -/
-- @node: measurable_projOp
@[fun_prop] lemma measurable_projOp (j : ℕ) (f : unitInterval → ℝ) :
    Measurable (projOp h j f) := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have he : projOp h j f = fun x => if x ∈ window h then
      (cellLen h j)⁻¹ * ∫ z in cell h j (cellIndex h j x), f z ∂design else 0 := by
    funext x
    by_cases hx : x ∈ window h
    · simp only [if_pos hx]
      exact projOp_eq_cell_average h j f x hx
    · simp [projOp, projKernel, hx]
  rw [he]
  apply Measurable.ite hw _ measurable_const
  exact (measurable_of_countable (fun l : ℕ =>
    (cellLen h j)⁻¹ * ∫ z in cell h j l, f z ∂design)).comp (measurable_cellIndex h j)

/-- A finite histogram average is bounded and therefore belongs to window L². -/
-- @node: projOp_memLp
lemma projOp_memLp (j : ℕ) (f : unitInterval → ℝ) :
    MemLp (projOp h j f) 2 (design.restrict (window h)) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let C := ∑ l ∈ Finset.range (2^j),
    ‖(cellLen h j)⁻¹ * ∫ z in cell h j l, f z ∂design‖
  apply MemLp.of_bound (by fun_prop) C
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  filter_upwards [ae_restrict_mem hw] with x hx
  rw [projOp_eq_cell_average h j f x hx]
  dsimp only [C]
  exact Finset.single_le_sum (fun l _ => norm_nonneg ((cellLen h j)⁻¹ * ∫ z in cell h j l, f z ∂design))
    (Finset.mem_range.mpr (cellIndex_lt h j x))

/-- Idempotence and self-adjointness identify the projection energy with its input pairing. -/
-- @node: projOp_energy_pairing
lemma projOp_energy_pairing (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∫ x in window h, (projOp h j f x)^2 ∂design) =
      ∫ x in window h, f x * projOp h j f x ∂design := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  calc
    _ = ∫ x in window h, projOp h j (projOp h j f) x * f x ∂design := by
      rw [projOp_self_adjoint h j (projOp h j f) f (projOp_memLp h j f) hf]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; ring)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hw] with x hx
      rw [projOp_idempotent h hh j f x hx, mul_comm]

/-- Nonnegative residual energy proves that a histogram projection contracts L². -/
-- @node: projOp_energy_contraction
lemma projOp_energy_contraction (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∫ x in window h, (projOp h j f x)^2 ∂design) ≤
      ∫ x in window h, (f x)^2 ∂design := by
  have hp := projOp_memLp h j f
  have hcross : Integrable (fun x => f x * projOp h j f x)
      (design.restrict (window h)) := hf.integrable_mul hp
  have hf2 := hf.integrable_sq
  have hp2 := hp.integrable_sq
  have hc2 := hcross.const_mul 2
  have hd := hf2.sub hc2
  have henergy := projOp_energy_pairing h hh j f hf
  have hres : 0 ≤ ∫ x in window h, (f x - projOp h j f x)^2 ∂design :=
    integral_nonneg (fun x => sq_nonneg _)
  have hexp : (∫ x in window h, (f x - projOp h j f x)^2 ∂design) =
      (∫ x in window h, (f x)^2 ∂design) -
      2 * (∫ x in window h, f x * projOp h j f x ∂design) +
      (∫ x in window h, (projOp h j f x)^2 ∂design) := by
    have he : (fun x => (f x - projOp h j f x)^2) =
        (fun x => (f x)^2 - 2 * (f x * projOp h j f x) + (projOp h j f x)^2) := by
      funext x; ring
    rw [he]
    integral_linearity
  rw [hexp, ← henergy] at hres
  linarith

/-- Every histogram projection fixes the constant function on its window. -/
-- @node: projOp_one_on_window
lemma projOp_one_on_window (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (x : unitInterval) (hx : x ∈ window h) :
    projOp h j (fun _ => (1 : ℝ)) x = 1 := by
  have hd : 0 < cellLen h j := by unfold cellLen; exact div_pos hh.1 (by positivity)
  rw [projOp_eq_cell_average h j _ x hx]
  simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
    design_cell h hh j _ (cellIndex_lt h j x), ENNReal.toReal_ofReal hd.le, mul_one]
  exact inv_mul_cancel₀ hd.ne'

/-- Self-adjointness and preservation of constants give preservation of the window integral. -/
-- @node: projOp_window_integral
lemma projOp_window_integral (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∫ x in window h, projOp h j f x ∂design) = ∫ x in window h, f x ∂design := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hone : MemLp (fun _ : unitInterval => (1 : ℝ)) 2
      (design.restrict (window h)) := memLp_const 1
  have he := projOp_self_adjoint h j f (fun _ => (1 : ℝ)) hf hone
  simp only [mul_one] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_subtype_coe measurableSet_Icc :
    MeasurableSet (window h))] with x hx
  rw [projOp_one_on_window h hh j x hx, mul_one]

/-- Adjacent histogram differences have zero window integral. -/
-- @node: bandOp_window_integral_zero
lemma bandOp_window_integral_zero (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∫ x in window h, bandOp h j f x ∂design) = 0 := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  simp_rw [bandOp_eq_sub h j f hf]
  rw [integral_sub ((projOp_memLp h j f).integrable (by norm_num))
    ((projOp_memLp h (j-1) f).integrable (by norm_num)),
    projOp_window_integral h hh j f hf, projOp_window_integral h hh (j-1) f hf, sub_self]

/-- The level-zero projection is the normalized window mean. -/
-- @node: projOp_zero_eq_window_average
lemma projOp_zero_eq_window_average (f : unitInterval → ℝ)
    (x : unitInterval) (hx : x ∈ window h) :
    projOp h 0 f x = h⁻¹ * ∫ z in window h, f z ∂design := by
  rw [projOp_eq_window_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_subtype_coe measurableSet_Icc :
    MeasurableSet (window h))] with z hz
  rw [projKernel_zero_on_window h x z hx hz]

/-- The coarsest projection annihilates every adjacent-level difference. -/
-- @node: projOp_zero_bandOp
lemma projOp_zero_bandOp (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h)))
    (x : unitInterval) (hx : x ∈ window h) :
    projOp h 0 (bandOp h j f) x = 0 := by
  rw [projOp_zero_eq_window_average h _ x hx, bandOp_window_integral_zero h hh j f hf,
    mul_zero]

/-- Constant coarse averages are orthogonal to every zero-mean histogram band. -/
-- @node: projOp_zero_bandOp_orthogonal
lemma projOp_zero_bandOp_orthogonal (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f g : unitInterval → ℝ) (hg : MemLp g 2 (design.restrict (window h))) :
    (∫ x in window h, projOp h 0 f x * bandOp h j g x ∂design) = 0 := by
  calc
    _ = ∫ x in window h, (h⁻¹ * ∫ z in window h, f z ∂design) *
        bandOp h j g x ∂design := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurable_subtype_coe measurableSet_Icc :
        MeasurableSet (window h))] with x hx
      rw [projOp_zero_eq_window_average h f x hx]
    _ = _ := by
      rw [integral_const_mul, bandOp_window_integral_zero h hh j g hg, mul_zero]

/-- Every histogram-kernel section has unit integral over the window. -/
-- @node: projKernel_window_integral
lemma projKernel_window_integral (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, projKernel h j x z ∂design) = 1 := by
  calc
    _ = ∫ x in window h, projKernel h j z x * 1 ∂design := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [projKernel_symm h j x z, mul_one])
    _ = projOp h j (fun _ => (1 : ℝ)) z :=
      (projOp_eq_window_integral h j (fun _ => (1 : ℝ)) z).symm
    _ = 1 := projOp_one_on_window h hh j z hz

/-- Subtracting the unit integrals of adjacent histogram sections gives a zero-mean band. -/
-- @node: bandKernel_window_integral_zero
lemma bandKernel_window_integral_zero (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, bandKernel h j x z ∂design) = 0 := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hone : MemLp (fun _ : unitInterval => (1 : ℝ)) 2
      (design.restrict (window h)) := memLp_const 1
  have hi (k : ℕ) : Integrable (fun x => projKernel h k x z)
      (design.restrict (window h)) := by
    have hi := (integrable_projKernel_mul h k (fun _ => (1 : ℝ)) hone z).restrict (s := window h)
    simpa only [mul_one, projKernel_symm h k z] using hi
  simp only [bandKernel]
  rw [integral_sub (hi j) (hi (j-1)), projKernel_window_integral h hh j z hz,
    projKernel_window_integral h hh (j-1) z hz, sub_self]

/-- The constant coarse kernel section is orthogonal to every zero-mean band section. -/
-- @node: projKernel_zero_bandKernel_orthogonal
lemma projKernel_zero_bandKernel_orthogonal (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, projKernel h 0 x z * bandKernel h j x z ∂design) = 0 := by
  calc
    _ = ∫ x in window h, h⁻¹ * bandKernel h j x z ∂design := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurable_subtype_coe measurableSet_Icc :
        MeasurableSet (window h))] with x hx
      rw [projKernel_zero_on_window h x z hx hz]
    _ = 0 := by
      rw [integral_const_mul, bandKernel_window_integral_zero h hh j z hz, mul_zero]

/-- Every section of a histogram kernel has the inverse-cell-length squared norm. -/
-- @node: projKernel_sq_integral
lemma projKernel_sq_integral (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, (projKernel h j x z)^2 ∂design) = (cellLen h j)⁻¹ := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hc : MeasurableSet (cell h j (cellIndex h j z)) :=
    hw.inter ((measurable_cellIndex h j) (measurableSet_singleton _))
  have hl := cellIndex_lt h j z
  have hd : 0 < cellLen h j := by unfold cellLen; exact div_pos hh.1 (by positivity)
  calc
    _ = ∫ _x in cell h j (cellIndex h j z), ((cellLen h j)⁻¹)^2 ∂design := by
      rw [← integral_indicator hw, ← integral_indicator hc]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ window h
      · by_cases hi : cellIndex h j x = cellIndex h j z
        · simp [projKernel, cell, hz, hx, hi]
        · simp [projKernel, cell, hz, hx, hi]
      · simp [projKernel, cell, hx]
    _ = cellLen h j * ((cellLen h j)⁻¹)^2 := by
      simp [integral_const, Measure.real, design_cell h hh j _ hl,
        ENNReal.toReal_ofReal hd.le]
    _ = _ := by field_simp

/-- Summing equal section energies over the window gives the dyadic dimension. -/
-- @node: projKernel_product_sq_integral
lemma projKernel_product_sq_integral (hh : 0 < h ∧ h ≤ 1) (j : ℕ) :
    (∫ z in window h, ∫ x in window h, (projKernel h j x z)^2 ∂design ∂design) =
      (2 : ℝ)^j := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  calc
    _ = ∫ _z in window h, (cellLen h j)⁻¹ ∂design := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hw] with z hz
      exact projKernel_sq_integral h hh j z hz
    _ = h * (cellLen h j)⁻¹ := by
      simp [integral_const, Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
    _ = _ := by
      unfold cellLen
      field_simp [hh.1.ne']

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
