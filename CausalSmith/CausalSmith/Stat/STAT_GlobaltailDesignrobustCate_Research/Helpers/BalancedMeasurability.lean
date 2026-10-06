module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountAdmissibility
public import Causalean.Mathlib.MeasureTheory.Matrix
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Measurability of balanced fits and their sup-norm losses

The finite-dimensional balanced coefficients are measurable, including at
singular matrices. On each deterministic half-open cell the fitted curve is
continuous. Separability of these cells makes the supremum loss measurable
without requiring the fitted curve to be continuous across cell boundaries.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped BigOperators ENNReal Matrix

/-- Each tensor monomial is continuous on the ambient coordinate space. -/
-- @node: monomial_continuous
@[fun_prop] lemma monomial_continuous (d m : ℕ) (a : MultiIndex d m) :
    Continuous (fun u => monomial d m u a) := by
  unfold monomial
  fun_prop

/-- Each tensor monomial is a measurable coordinate function. -/
-- @node: monomial_measurable
@[fun_prop] lemma monomial_measurable (d m : ℕ) (a : MultiIndex d m) :
    Measurable (fun u => monomial d m u a) := by
  fun_prop

/-- The arm membership and subcell membership event is measurable in the sample. -/
-- @node: sampledSubcell_measurableSet
lemma sampledSubcell_measurableSet {d n : ℕ} (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (ℓ : MultiIndex d m) (i : Fin n) :
    MeasurableSet {sample : Fin n → Obs d | (sample i).2.1 = arm ∧
      (sample i).1 ∈ scaledSubcell d j m ε Q ℓ} := by
  exact ((measurableSet_singleton arm).preimage (by fun_prop)).inter
    ((scaledSubcell_measurableSet d j m ε Q ℓ).preimage (by fun_prop))

/-- Every entry of the empirical balanced Gram matrix is measurable. -/
-- @node: balancedGram_measurable
@[fun_prop] lemma balancedGram_measurable {d n : ℕ} (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (a b : MultiIndex d m) :
    Measurable (fun sample : Fin n → Obs d => balancedGram sample arm j m ε Q a b) := by
  classical
  unfold balancedGram
  apply measurable_const.mul
  apply Finset.measurable_fun_sum
  intro ℓ _
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_fun_sum
    intro i _
    apply Measurable.ite (sampledSubcell_measurableSet arm j m ε Q ℓ i)
    · fun_prop
    · exact measurable_const

/-- Every coordinate of the balanced outcome moment is measurable. -/
-- @node: balancedMoment_measurable
@[fun_prop] lemma balancedMoment_measurable {d n : ℕ} (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (a : MultiIndex d m) :
    Measurable (fun sample : Fin n → Obs d => balancedMoment sample arm j m ε Q a) := by
  classical
  unfold balancedMoment
  apply measurable_const.mul
  apply Finset.measurable_fun_sum
  intro ℓ _
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_fun_sum
    intro i _
    apply Measurable.ite (sampledSubcell_measurableSet arm j m ε Q ℓ i)
    · fun_prop
    · exact measurable_const

/-- Balanced normal-equation coefficients are measurable with the total matrix inverse. -/
-- @node: balancedCoefficient_measurable
@[fun_prop] lemma balancedCoefficient_measurable {d n : ℕ} (arm : Bool) (j m : ℕ) (ε : ℝ)
    (Q : Fin d → Fin (2 ^ j)) (a : MultiIndex d m) :
    Measurable (fun sample : Fin n → Obs d =>
      ((balancedGram sample arm j m ε Q)⁻¹ *ᵥ balancedMoment sample arm j m ε Q) a) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.measurable_fun_sum
  intro b _
  apply Measurable.mul
  · exact Causalean.Mathlib.MeasureTheory.measurable_matrix_inv_apply _
      (fun i k => balancedGram_measurable arm j m ε Q i k) a b
  · exact balancedMoment_measurable arm j m ε Q b

/-- Each point evaluation of the total clipped arm fit is measurable, including empty cells. -/
-- @node: armBalancedEstimator_measurable
@[fun_prop] lemma armBalancedEstimator_measurable {d n : ℕ} (arm : Bool) (j : ℕ)
    (β M : ℝ) (x : Fin d → ℝ) :
    Measurable (fun sample : Fin n → Obs d => armBalancedEstimator sample arm j β M x) := by
  classical
  unfold armBalancedEstimator
  dsimp only
  apply Measurable.ite
  · exact (measurableSet_singleton 0).preimage (by fun_prop)
  · exact measurable_const
  · fun_prop

/-- A Hölder-class target is continuous on the cube, using its ambient extension. -/
-- @node: holderOnCube_continuousOn
lemma holderOnCube_continuousOn {d : ℕ} {β L : ℝ} {g : (Fin d → ℝ) → ℝ}
    (hβ : 0 < β) (hg : holderOnCube g β L) : ContinuousOn g (cube d) := by
  obtain ⟨A, _, hext⟩ := holderOnCube_std_extension d β hβ
  obtain ⟨f, hf, heq⟩ := hext g L hg
  exact (hf.1.continuousOn.mono (Set.subset_univ _)).congr (fun x hx => heq x hx)

/-- Within one ownership cell the arm fit is a clipped polynomial or the constant zero curve. -/
-- @node: armBalancedEstimator_continuous_cell
lemma armBalancedEstimator_continuous_cell {d n : ℕ} (sample : Fin n → Obs d)
    (arm : Bool) (j : ℕ) (β M : ℝ) (Q : Fin d → Fin (2 ^ j)) :
    Continuous (fun x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q} =>
      armBalancedEstimator sample arm j β M x) := by
  classical
  have heq : (fun x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q} =>
      armBalancedEstimator sample arm j β M x) =
      (fun x => if minimumCellCount sample arm j (polynomialOrder β)
          (normingSubcells d β).radius Q = 0 then 0 else
        max (-M) (min M (∑ a : MultiIndex d (polynomialOrder β),
          monomial d (polynomialOrder β)
            (fun k => (x.val k - cellOrigin d j Q k) / dyadicWidth j) a *
          ((balancedGram sample arm j (polynomialOrder β) (normingSubcells d β).radius Q)⁻¹ *ᵥ
            balancedMoment sample arm j (polynomialOrder β) (normingSubcells d β).radius Q) a))) := by
    funext x
    simp only [armBalancedEstimator, x.property.2]
  rw [heq]
  split_ifs
  · fun_prop
  · apply continuous_const.max
    apply continuous_const.min
    apply continuous_finset_sum
    intro a _
    apply Continuous.mul
    · exact (monomial_continuous d (polynomialOrder β) a).comp
        (continuous_pi (fun k => (((continuous_apply k).comp continuous_subtype_val).sub
          continuous_const).div_const _))
    · exact continuous_const

/-- The cube supremum is a finite supremum of suprema over its ownership cells. -/
-- @node: supLoss_eq_cellSup
lemma supLoss_eq_cellSup {d : ℕ} (f g : (Fin d → ℝ) → ℝ) (j : ℕ) :
    supLoss f g = ⨆ Q : Fin d → Fin (2 ^ j),
      ⨆ x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q},
        ENNReal.ofReal |f x - g x| := by
  apply le_antisymm
  · apply iSup_le
    intro x
    exact le_iSup_of_le (cellIndex d j x) (le_iSup_of_le ⟨x, x.property, rfl⟩ le_rfl)
  · apply iSup_le
    intro Q
    apply iSup_le
    intro x
    exact le_iSup_of_le (⟨x, x.property.1⟩ : cube d) le_rfl

/-- The loss supremum restricted to one ownership cell is measurable. -/
-- @node: armBalancedEstimator_cellSup_measurable
@[fun_prop] lemma armBalancedEstimator_cellSup_measurable {d n : ℕ}
    (arm : Bool) (j : ℕ) (β M : ℝ) (g : (Fin d → ℝ) → ℝ)
    (hg : ContinuousOn g (cube d)) (Q : Fin d → Fin (2 ^ j)) :
    Measurable (fun sample : Fin n → Obs d =>
      ⨆ x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q},
        ENNReal.ofReal |armBalancedEstimator sample arm j β M x - g x|) := by
  have h : Measurable (⨆ x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q},
      fun sample : Fin n → Obs d =>
        ENNReal.ofReal |armBalancedEstimator sample arm j β M x - g x|) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro x
      fun_prop
    · intro sample
      have htarget : Continuous
          (fun x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q} => g x) :=
        (continuousOn_iff_continuous_domRestrict.mp hg).comp
          (continuous_subtype_val.subtype_mk (fun x => x.property.1))
      exact (ENNReal.continuous_ofReal.comp
        ((armBalancedEstimator_continuous_cell sample arm j β M Q).sub htarget).abs).lowerSemicontinuous
  convert h using 1
  funext sample
  exact (iSup_apply (f := fun x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q} =>
    fun sample : Fin n → Obs d => ENNReal.ofReal |armBalancedEstimator sample arm j β M x - g x|)
    (a := sample)).symm

/-- A strict cell-loss exceedance is a measurable event, including zero fits. -/
-- @node: balancedEstimator_cellEvent_measurableSet
lemma balancedEstimator_cellEvent_measurableSet {d n : ℕ} (j : ℕ) (β M b : ℝ)
    (hb : 0 ≤ b) (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g (cube d))
    (Q : Fin d → Fin (2 ^ j)) :
    MeasurableSet {sample : Fin n → Obs d | ∃ x ∈ cube d,
      cellIndex d j x = Q ∧ b < |balancedEstimator sample j β M x - g x|} := by
  have heq : {sample : Fin n → Obs d | ∃ x ∈ cube d,
      cellIndex d j x = Q ∧ b < |balancedEstimator sample j β M x - g x|} =
      {sample | ENNReal.ofReal b <
        ⨆ x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q},
          ENNReal.ofReal |armBalancedEstimator sample true j β M x - g x|} := by
    ext sample
    simp only [Set.mem_setOf_eq, lt_iSup_iff,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb]
    constructor
    · rintro ⟨x, hx, hQ, hlt⟩
      exact ⟨⟨x, hx, hQ⟩, hlt⟩
    · rintro ⟨x, hlt⟩
      exact ⟨x, x.property.1, x.property.2, hlt⟩
  rw [heq]
  exact measurableSet_lt measurable_const
    (armBalancedEstimator_cellSup_measurable true j β M g hg Q)

/-- Sup-norm loss of either arm fit is measurable whenever the target is continuous on the cube.
Separability is used on each cell, so cell boundaries and zero fallback cause no exception. -/
-- @node: armBalancedEstimator_supLoss_measurable
@[fun_prop] lemma armBalancedEstimator_supLoss_measurable {d n : ℕ}
    (arm : Bool) (j : ℕ) (β M : ℝ) (g : (Fin d → ℝ) → ℝ)
    (hg : ContinuousOn g (cube d)) :
    Measurable (fun sample : Fin n → Obs d => supLoss (armBalancedEstimator sample arm j β M) g) := by
  simp_rw [supLoss_eq_cellSup _ _ j]
  apply Measurable.iSup
  intro Q
  have h : Measurable (⨆ x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q},
      fun sample : Fin n → Obs d => ENNReal.ofReal |armBalancedEstimator sample arm j β M x - g x|) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro x
      fun_prop
    · intro sample
      have htarget : Continuous
          (fun x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q} => g x) :=
        (continuousOn_iff_continuous_domRestrict.mp hg).comp
          (continuous_subtype_val.subtype_mk (fun x => x.property.1))
      exact (ENNReal.continuous_ofReal.comp
        ((armBalancedEstimator_continuous_cell sample arm j β M Q).sub htarget).abs).lowerSemicontinuous
  convert h using 1
  funext sample
  exact (iSup_apply (f := fun x : {x : Fin d → ℝ | x ∈ cube d ∧ cellIndex d j x = Q} =>
    fun sample : Fin n → Obs d => ENNReal.ofReal |armBalancedEstimator sample arm j β M x - g x|)
    (a := sample)).symm

/-- The treated estimator's loss has the measurability required for layer-cake integration. -/
-- @node: balancedEstimator_supLoss_measurable
@[fun_prop] lemma balancedEstimator_supLoss_measurable {d n : ℕ} (j : ℕ)
    (β M : ℝ) (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g (cube d)) :
    Measurable (fun sample : Fin n → Obs d => supLoss (balancedEstimator sample j β M) g) := by
  exact armBalancedEstimator_supLoss_measurable true j β M g hg

/-- Selecting a scale by a measurable finite set preserves measurability of any measurable statistic. -/
-- @node: selectedStatistic_measurable
lemma selectedStatistic_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (levels : Ω → Finset ℕ) (hlevels : Measurable levels)
    (f : ℕ → Ω → E) (hf : ∀ j, Measurable (f j)) (fallback : E) :
    Measurable (fun ω => if h : (levels ω).Nonempty then
      f ((levels ω).max' h) ω else fallback) := by
  classical
  have hF : Measurable (fun p : Finset ℕ × Ω =>
      if h : p.1.Nonempty then f (p.1.max' h) p.2 else fallback) := by
    apply measurable_from_prod_countable_right
    intro s
    by_cases hs : s.Nonempty
    · simpa only [hs, dite_true] using hf (s.max' hs)
    · simp only [hs, dite_false]
      exact measurable_const
  exact hF.comp (hlevels.prodMk measurable_id)

/-- Each point evaluation of the count-selected estimator is measurable. -/
-- @node: selectorHandle_measurable
@[fun_prop] lemma selectorHandle_measurable {d n : ℕ} (β M : ℝ) (x : Fin d → ℝ) :
    Measurable (fun sample : Fin n → Obs d => selectorHandle sample β M x) := by
  unfold selectorHandle
  exact selectedStatistic_measurable _ (admissibleLevels_measurable d n β)
    _ (fun j => armBalancedEstimator_measurable true j β M x) 0

/-- Adaptive sup loss is measurable, including the empty-grid zero fallback. -/
-- @node: selectorHandle_supLoss_measurable
@[fun_prop] lemma selectorHandle_supLoss_measurable {d n : ℕ} (β M : ℝ)
    (g : (Fin d → ℝ) → ℝ) (hg : ContinuousOn g (cube d)) :
    Measurable (fun sample : Fin n → Obs d => supLoss (selectorHandle sample β M) g) := by
  classical
  have heq : (fun sample : Fin n → Obs d => supLoss (selectorHandle sample β M) g) =
      (fun sample => if h : (admissibleLevels sample β).Nonempty then
        supLoss (balancedEstimator sample ((admissibleLevels sample β).max' h) β M) g
      else supLoss (fun _ => 0) g) := by
    funext sample
    unfold selectorHandle
    split_ifs <;> rfl
  rw [heq]
  exact selectedStatistic_measurable _ (admissibleLevels_measurable d n β)
    _ (fun j => balancedEstimator_supLoss_measurable j β M g hg) _

end CausalSmith.Stat.GlobalTailDesignRobustCate
