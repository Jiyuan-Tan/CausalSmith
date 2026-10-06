module
public import Causalean.Mathlib.MeasureTheory.Matrix
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Bias

/-! # Measurability of the selected equal-cell estimator -/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- For [a sample size, smoothness exponent, outcome bound, regression function, and realized sample](hyp:d,n,β,B,μ,ω),
[the real-valued equal-cell cube loss](goal) is the supremum, over cube points, of the estimator's absolute error. -/
noncomputable def equalCellCubeLossReal {d n : ℕ} (β B : ℝ)
    (μ : (Fin d → ℝ) → ℝ) (ω : Fin n → Obs d) : ℝ :=
  (⨆ y : Fin d → ℝ, ⨆ (_ : y ∈ cube d),
    ENNReal.ofReal |equalCellEstimator β B ω y - μ y|).toReal

/-- Feasibility of a fixed mesh index is a measurable sample event. [For the stated inputs and conditions](hyp:d,n,m,β,j), [the asserted conclusion holds](goal). -/
lemma meshFeasible_measurableSet {d n : ℕ} (m : ℕ) (β : ℝ) (j : ℕ) :
    MeasurableSet {ω : Fin n → Obs d | meshFeasible m β ω j} := by
  classical
  unfold meshFeasible
  by_cases hj : j ∈ meshIndices d n β
  · simp only [hj, true_and]
    rw [show {ω : Fin n → Obs d |
          ∀ (k : Fin d → Fin (2 ^ j)) (l : Fin d → Fin (m + 1)),
            meshWidth j ^ (-2 * β) ≤ (treatedCount m j ω k l : ℝ)} =
        ⋂ k, ⋂ l, {ω | meshWidth j ^ (-2 * β) ≤
          (treatedCount m j ω k l : ℝ)} by
      ext ω
      simp]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun l =>
      measurableSet_le measurable_const (treatedCount_measurable m j k l)
  · simp [hj]

/-- Membership of a fixed index in the data-selected feasible set is measurable. [For the stated inputs and conditions](hyp:d,n,m,β,j), [the asserted conclusion holds](goal). -/
lemma feasibleIndices_mem_measurableSet {d n : ℕ} (m : ℕ) (β : ℝ) (j : ℕ) :
    MeasurableSet {ω : Fin n → Obs d | j ∈ feasibleIndices m β ω} := by
  classical
  simp only [feasibleIndices, Finset.mem_filter]
  by_cases hj : j ∈ meshIndices d n β
  · simpa [hj] using meshFeasible_measurableSet (d := d) (n := n) m β j
  · simp [hj]

/-- The finite feasible-index set is a measurable function of the sample. [For the stated inputs and conditions](hyp:d,n,m,β), [the asserted conclusion holds](goal). -/
lemma feasibleIndices_measurable {d n : ℕ} (m : ℕ) (β : ℝ) :
    Measurable (fun ω : Fin n → Obs d => feasibleIndices m β ω) := by
  classical
  apply measurable_to_countable'
  intro T
  rw [show (fun ω : Fin n → Obs d => feasibleIndices m β ω) ⁻¹' {T} =
      ⋂ j : ℕ, {ω | (j ∈ feasibleIndices m β ω) ↔ j ∈ T} by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
    exact Finset.ext_iff]
  exact MeasurableSet.iInter fun j => by
    by_cases hj : j ∈ T
    · simpa [hj] using feasibleIndices_mem_measurableSet (d := d) (n := n) m β j
    · rw [show {ω : Fin n → Obs d |
          (j ∈ feasibleIndices m β ω) ↔ j ∈ T} =
          {ω | j ∈ feasibleIndices m β ω}ᶜ by
        ext ω
        simp [hj]]
      exact (feasibleIndices_mem_measurableSet (d := d) (n := n) m β j).compl

/-- The selected mesh width is a measurable function of the finite sample. [For the stated inputs and conditions](hyp:d,n,m,β), [the asserted conclusion holds](goal). -/
lemma countSelectedMesh_measurable {d n : ℕ} (m : ℕ) (β : ℝ) :
    Measurable (countSelectedMesh (d := d) (n := n) m β) := by
  unfold countSelectedMesh
  exact (measurable_of_countable (fun S : Finset ℕ =>
    if S.Nonempty then meshWidth (S.sup id) else 0)).comp
      (feasibleIndices_measurable m β)

/-- A fixed sample coordinate falling in a fixed treated microcell is measurable. [For the stated inputs and conditions](hyp:d,n,m,j,k,l,i), [the asserted conclusion holds](goal). -/
lemma treatedSampleMicrocell_measurableSet {d n : ℕ} (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (l : Fin d → Fin (m + 1)) (i : Fin n) :
    MeasurableSet {ω : Fin n → Obs d | (ω i).2.1 = true ∧
      (ω i).1 ∈ scaledMicroCell d m j k l} := by
  exact ((measurableSet_singleton true).preimage
    ((measurable_fst.comp measurable_snd).comp (measurable_pi_apply i))).inter
    ((orderedMass_scaledMicroCell_measurable d m j k l).preimage
      (measurable_fst.comp (measurable_pi_apply i)))

/-- Every coordinate of the equal-cell response moment is sample measurable. [For the stated inputs and conditions](hyp:d,n,m,j,k,α), [the asserted conclusion holds](goal). -/
lemma responseMoment_coordinate_measurable {d n : ℕ} (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) :
    Measurable (fun ω : Fin n → Obs d => responseMoment m j ω k α) := by
  classical
  unfold responseMoment
  apply measurable_const.mul
  apply Finset.measurable_fun_sum
  intro l _
  apply (treatedCount_measurable m j k l).inv.mul
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.ite (treatedSampleMicrocell_measurableSet m j k l i)
  · unfold monoVec
    fun_prop
  · exact measurable_const

/-- Every coordinate of the equal-cell Gram matrix is sample measurable. [For the stated inputs and conditions](hyp:d,n,m,j,k,α,δ), [the asserted conclusion holds](goal). -/
lemma gramHat_coordinate_measurable {d n : ℕ} (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (α δ : MonoIndex d m) :
    Measurable (fun ω : Fin n → Obs d => gramHat m j ω k α δ) := by
  classical
  unfold gramHat
  apply measurable_const.mul
  apply Finset.measurable_fun_sum
  intro l _
  apply (treatedCount_measurable m j k l).inv.mul
  apply Finset.measurable_fun_sum
  intro i _
  apply Measurable.ite (treatedSampleMicrocell_measurableSet m j k l i)
  · unfold monoVec
    fun_prop
  · exact measurable_const

/-- A finite real matrix with measurable entries has measurable determinant. [For the stated inputs and conditions](hyp:Omega,I,A,hA), [the asserted conclusion holds](goal). -/
lemma finiteMatrix_det_measurable {Omega I : Type*} [MeasurableSpace Omega]
    [Fintype I] [DecidableEq I] (A : Omega → Matrix I I ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) :
    Measurable (fun ω => (A ω).det) :=
  Causalean.Mathlib.MeasureTheory.measurable_matrix_det A hA

/-- Every entry of the inverse of a finite measurable real matrix is measurable. [For the stated inputs and conditions](hyp:Omega,I,A,hA,i,j), [the asserted conclusion holds](goal). -/
lemma finiteMatrix_inv_coordinate_measurable {Omega I : Type*}
    [MeasurableSpace Omega] [Fintype I] [DecidableEq I]
    (A : Omega → Matrix I I ℝ)
    (hA : ∀ i j, Measurable (fun ω => A ω i j)) (i j : I) :
    Measurable (fun ω => (A ω)⁻¹ i j) :=
  Causalean.Mathlib.MeasureTheory.measurable_matrix_inv_apply A hA i j

/-- Every coordinate of the equal-cell fitted coefficient vector is measurable. [For the stated inputs and conditions](hyp:d,n,m,j,k,α), [the asserted conclusion holds](goal). -/
lemma coefHat_coordinate_measurable {d n : ℕ} (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) :
    Measurable (fun ω : Fin n → Obs d => coefHat m j ω k α) := by
  classical
  unfold coefHat Matrix.mulVec dotProduct
  apply Finset.measurable_fun_sum
  intro b _
  exact (finiteMatrix_inv_coordinate_measurable
      (fun ω => gramHat m j ω k)
      (fun a b => gramHat_coordinate_measurable m j k a b) α b).mul
    (responseMoment_coordinate_measurable m j k b)

/-- With the dyadic index fixed, the clipped equal-cell estimate is measurable in the sample. [For the stated inputs and conditions](hyp:d,n,β,B,x,j), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_fixedIndex_measurable {d n : ℕ} (β B : ℝ)
    (x : Fin d → ℝ) (j : ℕ) :
    Measurable (fun ω : Fin n → Obs d =>
      let m := polynomialDegree β
      let h := countSelectedMesh m β ω
      if h = 0 then 0 else
        let k := cubeIndex d j x
        max (-B) (min B (∑ α, monoVec d m
          (fun a => (x a - cubeCorner d j k a) / h) α *
            coefHat m j ω k α))) := by
  let m := polynomialDegree β
  let k := cubeIndex d j x
  have hh : Measurable (fun ω : Fin n → Obs d => countSelectedMesh m β ω) :=
    countSelectedMesh_measurable m β
  apply Measurable.ite (measurableSet_eq_fun hh measurable_const)
  · exact measurable_const
  · apply Measurable.max measurable_const
    apply Measurable.min measurable_const
    apply Finset.measurable_fun_sum
    intro α _
    apply Measurable.mul
    · unfold monoVec
      fun_prop
    · exact coefHat_coordinate_measurable m j k α

/-- At every fixed covariate point, the selected equal-cell estimate is measurable in the sample. [For the stated inputs and conditions](hyp:d,n,β,B,x), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_fixedPoint_measurable {d n : ℕ} (β B : ℝ)
    (x : Fin d → ℝ) :
    Measurable (fun ω : Fin n → Obs d => equalCellEstimator β B ω x) := by
  let m := polynomialDegree β
  let J : (Fin n → Obs d) → ℕ :=
    fun ω => (feasibleIndices m β ω).sup id
  let F : ((Fin n → Obs d) × ℕ) → ℝ := fun p =>
    let ω := p.1
    let j := p.2
    let h := countSelectedMesh m β ω
    if h = 0 then 0 else
      let k := cubeIndex d j x
      max (-B) (min B (∑ α, monoVec d m
        (fun a => (x a - cubeCorner d j k a) / h) α *
          coefHat m j ω k α))
  have hF : Measurable F := measurable_from_prod_countable_left fun j => by
    simpa [F, m] using equalCellEstimator_fixedIndex_measurable β B x j
  have hJ : Measurable J := by
    exact (measurable_of_countable (fun S : Finset ℕ => S.sup id)).comp
      (feasibleIndices_measurable m β)
  have hc := hF.comp (measurable_id.prodMk hJ)
  convert hc using 1 <;> simp [F, J, m, equalCellEstimator, Function.comp_def]

/-- The supremum of pointwise measurable continuous ENNReal sections over a
second-countable space is measurable. [For the stated inputs and conditions](hyp:Omega,X,f,hm,hc), [the asserted conclusion holds](goal). -/
lemma measurable_iSup_of_continuous_sections {Omega X : Type*}
    [MeasurableSpace Omega] [TopologicalSpace X] [SecondCountableTopology X]
    (f : Omega → X → ℝ≥0∞) (hm : ∀ x, Measurable (fun ω => f ω x))
    (hc : ∀ ω, Continuous (f ω)) :
    Measurable (fun ω => ⨆ x, f ω x) := by
  cases isEmpty_or_nonempty X with
  | inl _ => simp
  | inr _ =>
      have heq : (fun ω => ⨆ x, f ω x) =
          fun ω => ⨆ r : ℕ, f ω (TopologicalSpace.denseSeq X r) := by
        funext ω
        have hd := (TopologicalSpace.denseRange_denseSeq X).ciSup' (hc ω)
        rw [← hd]
        apply le_antisymm
        · apply iSup_le
          intro s
          rcases s.property with ⟨r, hr⟩
          rw [← hr]
          exact le_iSup (fun r : ℕ => f ω (TopologicalSpace.denseSeq X r)) r
        · apply iSup_le
          intro r
          exact le_iSup_of_le
            ⟨TopologicalSpace.denseSeq X r, ⟨r, rfl⟩⟩ le_rfl
      rw [heq]
      exact Measurable.iSup fun r => hm _

/-- Polynomial estimator formula with its dyadic index and cube fixed. For [the stated inputs and conditions](hyp:β,B,ω,j,k,x), [the `equalCellEstimatorAtCell` object being defined](goal). -/
noncomputable def equalCellEstimatorAtCell {d n : ℕ} (β B : ℝ)
    (ω : Fin n → Obs d) (j : ℕ) (k : Fin d → Fin (2 ^ j))
    (x : Fin d → ℝ) : ℝ :=
  let m := polynomialDegree β
  let h := countSelectedMesh m β ω
  if h = 0 then 0 else
    max (-B) (min B (∑ α, monoVec d m
      (fun a => (x a - cubeCorner d j k a) / h) α *
        coefHat m j ω k α))

/-- At a fixed point and cell, the polynomial estimator formula is sample measurable. [For the stated inputs and conditions](hyp:d,n,β,B,j,k,x), [the asserted conclusion holds](goal). -/
lemma equalCellEstimatorAtCell_measurable {d n : ℕ} (β B : ℝ)
    (j : ℕ) (k : Fin d → Fin (2 ^ j)) (x : Fin d → ℝ) :
    Measurable (fun ω : Fin n → Obs d =>
      equalCellEstimatorAtCell β B ω j k x) := by
  let m := polynomialDegree β
  have hh : Measurable (fun ω : Fin n → Obs d => countSelectedMesh m β ω) :=
    countSelectedMesh_measurable m β
  unfold equalCellEstimatorAtCell
  apply Measurable.ite (measurableSet_eq_fun hh measurable_const)
  · exact measurable_const
  · apply Measurable.max measurable_const
    apply Measurable.min measurable_const
    apply Finset.measurable_fun_sum
    intro α _
    apply Measurable.mul
    · unfold monoVec
      fun_prop
    · exact coefHat_coordinate_measurable m j k α

/-- For a fixed sample and cell, the polynomial estimator formula is continuous in x. [For the stated inputs and conditions](hyp:d,n,β,B,ω,j,k), [the asserted conclusion holds](goal). -/
lemma equalCellEstimatorAtCell_continuous {d n : ℕ} (β B : ℝ)
    (ω : Fin n → Obs d) (j : ℕ) (k : Fin d → Fin (2 ^ j)) :
    Continuous (equalCellEstimatorAtCell β B ω j k) := by
  unfold equalCellEstimatorAtCell
  dsimp only
  by_cases hzero : countSelectedMesh (polynomialDegree β) β ω = 0
  · simp only [hzero, if_true]
    exact continuous_const
  · simp only [hzero, if_false]
    apply Continuous.max continuous_const
    apply Continuous.min continuous_const
    apply continuous_finset_sum
    intro α _
    unfold monoVec
    fun_prop

/-- Against a continuous target on the cube, the cube-supremum loss of the
selected equal-cell estimator is sample measurable. [For the stated inputs and conditions](hyp:d,n,β,B,μ,hμ), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_cubeSup_measurable {d n : ℕ} (β B : ℝ)
    (μ : (Fin d → ℝ) → ℝ) (hμ : ContinuousOn μ (cube d)) :
    Measurable (fun ω : Fin n → Obs d =>
      ⨆ y : Fin d → ℝ, ⨆ (_ : y ∈ cube d),
        ENNReal.ofReal |equalCellEstimator β B ω y - μ y|) := by
  let m := polynomialDegree β
  let J : (Fin n → Obs d) → ℕ :=
    fun ω => (feasibleIndices m β ω).sup id
  let cell : (j : ℕ) → (Fin d → Fin (2 ^ j)) → Set (Fin d → ℝ) :=
    fun j k => {x | x ∈ cube d ∧ cubeIndex d j x = k}
  let G : ((Fin n → Obs d) × ℕ) → ℝ≥0∞ := fun p =>
    ⨆ k : Fin d → Fin (2 ^ p.2),
      ⨆ x : cell p.2 k,
        ENNReal.ofReal
          |equalCellEstimatorAtCell β B p.1 p.2 k x - μ x|
  have hG : Measurable G := measurable_from_prod_countable_left fun j => by
    change Measurable (fun ω : Fin n → Obs d =>
      ⨆ k : Fin d → Fin (2 ^ j),
        ⨆ x : cell j k,
          ENNReal.ofReal
            |equalCellEstimatorAtCell β B ω j k x - μ x|)
    apply Measurable.iSup
    intro k
    apply measurable_iSup_of_continuous_sections
    · intro x
      exact ENNReal.measurable_ofReal.comp
        ((equalCellEstimatorAtCell_measurable β B j k x).sub measurable_const).abs
    · intro ω
      apply ENNReal.continuous_ofReal.comp
      apply Continuous.abs
      apply Continuous.sub
      · exact (equalCellEstimatorAtCell_continuous β B ω j k).comp
          continuous_subtype_val
      · exact hμ.comp_continuous continuous_subtype_val fun x => x.property.1
  have hJ : Measurable J := by
    exact (measurable_of_countable (fun S : Finset ℕ => S.sup id)).comp
      (feasibleIndices_measurable m β)
  have hcomp := hG.comp (measurable_id.prodMk hJ)
  convert hcomp using 1
  funext ω
  dsimp only [Function.comp_apply]
  change (⨆ y : Fin d → ℝ, ⨆ (_ : y ∈ cube d),
      ENNReal.ofReal |equalCellEstimator β B ω y - μ y|) =
    G (ω, J ω)
  unfold G
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    let k := cubeIndex d (J ω) y
    have heq : equalCellEstimator β B ω y =
        equalCellEstimatorAtCell β B ω (J ω) k y := by
      simp [equalCellEstimator, equalCellEstimatorAtCell, J, m, k]
    rw [heq]
    exact le_iSup_of_le k
      (le_iSup_of_le ⟨y, hy, rfl⟩ le_rfl)
  · apply iSup_le
    intro k
    apply iSup_le
    intro x
    have heq : equalCellEstimator β B ω x =
        equalCellEstimatorAtCell β B ω (J ω) k x := by
      simp [equalCellEstimator, equalCellEstimatorAtCell, J, m, x.property.2]
    rw [← heq]
    exact le_iSup_of_le x.1 (le_iSup_of_le x.property.1 le_rfl)

/-- A Holder representative supplies the continuity premise required by the
sample-measurability theorem for the cube-supremum loss. [For the stated inputs and conditions](hyp:d,n,β,B,L,μ,hμ), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_cubeSup_measurable_of_holderBall {d n : ℕ}
    (β B L : ℝ) (μ : (Fin d → ℝ) → ℝ) (hμ : HolderBall β L μ) :
    Measurable (fun ω : Fin n → Obs d =>
      ⨆ y : Fin d → ℝ, ⨆ (_ : y ∈ cube d),
        ENNReal.ofReal |equalCellEstimator β B ω y - μ y|) :=
  equalCellEstimator_cubeSup_measurable β B μ hμ.regularity.continuousOn

/-- [For the stated inputs and conditions](hyp:d,n,β,B,μ,hμ), [the asserted conclusion holds](goal). -/

lemma equalCellCubeLossReal_measurable {d n : ℕ} (β B : ℝ)
    (μ : (Fin d → ℝ) → ℝ) (hμ : ContinuousOn μ (cube d)) :
    Measurable (equalCellCubeLossReal (n := n) β B μ) := by
  unfold equalCellCubeLossReal
  exact ENNReal.measurable_toReal.comp
    (equalCellEstimator_cubeSup_measurable β B μ hμ)

/-- [For the stated inputs and conditions](hyp:d,n,β,B,μ,hB,hμ,ω), [the asserted conclusion holds](goal). -/

lemma equalCellCubeLossReal_le_two_mul {d n : ℕ} (β B : ℝ)
    (μ : (Fin d → ℝ) → ℝ) (hB : 0 ≤ B)
    (hμ : ∀ x ∈ cube d, |μ x| ≤ B) (ω : Fin n → Obs d) :
    equalCellCubeLossReal β B μ ω ≤ 2 * B := by
  have hsup := cube_iSup_ofReal_loss_le
    (fun x => equalCellEstimator β B ω x - μ x) (2 * B) (by positivity)
    (fun x hx => equalCellEstimator_error_le_two_mul β B ω x (μ x) hB (hμ x hx))
  unfold equalCellCubeLossReal
  calc
    _ ≤ (ENNReal.ofReal (2 * B)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
    _ = 2 * B := ENNReal.toReal_ofReal (by positivity)

/-- [For the stated inputs and conditions](hyp:d,n,β,B,μ,hB,hμcont,hμ,Q), [the asserted conclusion holds](goal). -/

lemma equalCellCubeLoss_lintegral_eq_ofReal_integral {d n : ℕ} (β B : ℝ)
    (μ : (Fin d → ℝ) → ℝ) (hB : 0 ≤ B)
    (hμcont : ContinuousOn μ (cube d))
    (hμ : ∀ x ∈ cube d, |μ x| ≤ B)
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q] :
    (∫⁻ ω, ⨆ x, ⨆ (_hx : x ∈ cube d),
        ENNReal.ofReal |equalCellEstimator β B ω x - μ x| ∂Q) =
      ENNReal.ofReal (∫ ω, equalCellCubeLossReal β B μ ω ∂Q) := by
  have hmeas := equalCellCubeLossReal_measurable (n := n) β B μ hμcont
  have hint : Integrable (equalCellCubeLossReal (n := n) β B μ) Q :=
    Integrable.of_bound hmeas.aestronglyMeasurable (2 * B) <|
      ae_of_all Q fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact equalCellCubeLossReal_le_two_mul β B μ hB hμ ω
        · exact ENNReal.toReal_nonneg
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all Q fun ω => ENNReal.toReal_nonneg)]
  refine lintegral_congr fun ω => ?_
  unfold equalCellCubeLossReal
  symm
  apply ENNReal.ofReal_toReal
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (cube_iSup_ofReal_loss_le
      (fun x => equalCellEstimator β B ω x - μ x) (2 * B) (by positivity)
      (fun x hx => equalCellEstimator_error_le_two_mul β B ω x (μ x) hB (hμ x hx)))

/-- The selected-estimator cube loss against a model Holder response is
almost-everywhere measurable under any sample law. [For the stated inputs and conditions](hyp:d,n,β,B,L,Pc,μ,hμ,Q), [the asserted conclusion holds](goal). -/
lemma equalCellEstimator_cubeSup_aemeasurable_of_holderResponse {d n : ℕ}
    (β B L : ℝ) (Pc : Measure (Completion d))
    (μ : (Fin d → ℝ) → ℝ) (hμ : HolderResponse Pc μ β L)
    (Q : Measure (Fin n → Obs d)) :
    AEMeasurable (fun ω : Fin n → Obs d =>
      ⨆ y : Fin d → ℝ, ⨆ (_ : y ∈ cube d),
        ENNReal.ofReal |equalCellEstimator β B ω y - μ y|) Q :=
  (equalCellEstimator_cubeSup_measurable_of_holderBall β B L μ hμ.1).aemeasurable

/-- Integrate fibrewise good-event and global bounds without changing the
event used for conditioning. [For the stated inputs and conditions](hyp:Ω,S,Q,X,hX,Z,hZm,hZ,E,hE,R,M,δ,hR,hM,hδ,hgood,hall,hbad), [the asserted conclusion holds](goal). -/
lemma integral_le_of_condDistrib_event_bounds
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [StandardBorelSpace Ω] [Nonempty Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (X : Ω → S) (hX : Measurable X) (Z : Ω → ℝ)
    (hZm : StronglyMeasurable Z) (hZ : Integrable Z Q)
    (E : Set Ω) (hE : MeasurableSet E) (R M δ : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hgood : ∀ᵐ ω ∂Q, ω ∈ E →
      ∫ ξ, Z ξ ∂condDistrib id X Q (X ω) ≤ R)
    (hall : ∀ᵐ ω ∂Q,
      ∫ ξ, Z ξ ∂condDistrib id X Q (X ω) ≤ M)
    (hbad : Q.real Eᶜ ≤ δ) :
    ∫ ω, Z ω ∂Q ≤ R + M * δ := by
  classical
  let F : Ω → ℝ := fun ω => ∫ ξ, Z ξ ∂condDistrib id X Q (X ω)
  have htower : Q[Z | ‹MeasurableSpace S›.comap X] =ᵐ[Q] F := by
    simpa [F] using ProbabilityTheory.condExp_ae_eq_integral_condDistrib
      (Y := id) hX measurable_id.aemeasurable hZm hZ
  have hFint : Integrable F Q := integrable_condExp.congr htower
  let G : Ω → ℝ := E.indicator (fun _ => R) + Eᶜ.indicator (fun _ => M)
  have hGint : Integrable G Q :=
    ((integrable_const R).indicator hE).add ((integrable_const M).indicator hE.compl)
  have hFG : F ≤ᵐ[Q] G := by
    filter_upwards [hgood, hall] with ω hgoodω hallω
    by_cases hω : ω ∈ E
    · simpa [G, hω] using hgoodω hω
    · simpa [G, hω] using hallω
  calc
    ∫ ω, Z ω ∂Q = ∫ ω, F ω ∂Q := by
      rw [← integral_condExp (μ := Q) (f := Z) hX.comap_le]
      exact integral_congr_ae htower
    _ ≤ ∫ ω, G ω ∂Q := integral_mono_ae hFint hGint hFG
    _ = R * Q.real E + M * Q.real Eᶜ := by
      dsimp [G]
      rw [integral_add ((integrable_const R).indicator hE)
        ((integrable_const M).indicator hE.compl),
        integral_indicator_const R hE, integral_indicator_const M hE.compl]
      simp only [smul_eq_mul]
      ring
    _ ≤ R + M * δ := by
      have hprob : Q.real E ≤ 1 := measureReal_le_one
      have hfirst : R * Q.real E ≤ R := by
        simpa using mul_le_mul_of_nonneg_left hprob hR
      have hsecond : M * Q.real Eᶜ ≤ M * δ :=
        mul_le_mul_of_nonneg_left hbad hM
      linarith


end CausalSmith.Stat.WeakOverlap
