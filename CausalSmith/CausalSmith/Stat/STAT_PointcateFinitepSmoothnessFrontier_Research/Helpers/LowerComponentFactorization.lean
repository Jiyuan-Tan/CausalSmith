module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerComponentBounds
public import Causalean.Experimentation.DesignBased.ProductBlock
public import Causalean.Stat.RandomGraph.Expectation

/-! Finite-moment point-CATE frontier: Helpers/LowerComponentFactorization. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


variable (κ : Params) (n : ℕ)
/-- Macro-window edge events connect records sharing a frame sign. -/
def sharedEdge (i j : Fin n) : Set (unitInterval × unitInterval) :=
  {z | |(z.1 : ℝ)-1/2| ≤ lowerH κ n ∧ |(z.2 : ℝ)-1/2| ≤ lowerH κ n ∧
    |(z.1 : ℝ)-(z.2 : ℝ)| ≤ 2*lowerEll κ n}
/-- The coordinate edge events are Borel. -/
-- @node: measurable_sharedEdge
lemma measurable_sharedEdge (i j : Fin n) : MeasurableSet (sharedEdge κ n i j) := by
  have h1 : Measurable (fun z : unitInterval × unitInterval => |(z.1 : ℝ)-1/2|) := by
    apply Continuous.measurable
    fun_prop
  have h2 : Measurable (fun z : unitInterval × unitInterval => |(z.2 : ℝ)-1/2|) := by
    apply Continuous.measurable
    fun_prop
  have h3 : Measurable (fun z : unitInterval × unitInterval => |(z.1 : ℝ)-(z.2 : ℝ)|) := by
    apply Continuous.measurable
    fun_prop
  exact (measurableSet_le h1 measurable_const).inter
    ((measurableSet_le h2 measurable_const).inter (measurableSet_le h3 measurable_const))
/-- The coordinate edge events are symmetric. -/
-- @node: symmetric_sharedEdge
lemma symmetric_sharedEdge (i j : Fin n) (x y : unitInterval) :
  (x,y) ∈ sharedEdge κ n i j ↔ (y,x) ∈ sharedEdge κ n j i := by
  simp only [sharedEdge, mem_setOf_eq, abs_sub_comm]
  tauto
/-- The substrate coordinate graph encodes all shared-sign components. -/
def sharedGraph : Causalean.Stat.RandomGraph.CoordinateGraph (fun _ : Fin n => unitInterval) where
  edgeEvent := sharedEdge κ n
  measurable_edgeEvent := measurable_sharedEdge κ n
  symmetric := symmetric_sharedEdge κ n
/-- Size-m components are counted once by their vertex subsets. -/
def componentCount (m : ℕ) (x : Fin n → unitInterval) : ℝ :=
  ((Finset.univ.powersetCard m).filter (fun S =>
    Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S ∧
      ∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n)).card
/-- A real interval cuts out at most its length from the uniform design. -/
-- @node: design_absolute_ball_le
lemma design_absolute_ball_le (c r : ℝ) :
    design {x : unitInterval | |(x : ℝ)-c| ≤ r} ≤ ENNReal.ofReal (2*r) := by
  unfold design
  rw [unitInterval.volume_apply]
  calc
    volume (Subtype.val '' {x : unitInterval | |(x : ℝ)-c| ≤ r})
        ≤ volume (Icc (c-r) (c+r)) := by
      apply measure_mono
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨hlo, hhi⟩ := abs_le.mp (show |(x : ℝ)-c| ≤ r from hx)
      constructor <;> linarith
    _ = ENNReal.ofReal (2*r) := by rw [Real.volume_Icc]; congr 1; ring

/-- Every vertex of a non-singleton shared-sign component lies in the macro window. -/
-- @node: shared_component_vertex_in_window
lemma shared_component_vertex_in_window (S : Finset (Fin n)) (r : Fin n) (hr : r ∈ S)
    (hsize : 2 ≤ S.card) (x : Fin n → unitInterval)
    (hcomp : Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S) :
    |(x r : ℝ)-1/2| ≤ lowerH κ n := by
  obtain ⟨w, hw, hwr⟩ := S.exists_mem_ne (by omega) r
  have hne : (⟨r, hr⟩ : S) ≠ ⟨w, hw⟩ := by
    intro h
    exact hwr (congrArg Subtype.val h).symm
  obtain ⟨v, hv⟩ := (hcomp.1.preconnected (⟨r, hr⟩ : S) ⟨w, hw⟩).nonempty_neighborSet_left hne
  exact hv.2.1

/-- The root qualification in the component count is a measurable finite event. -/
-- @node: measurable_shared_component_event
lemma measurable_shared_component_event (S : Finset (Fin n)) :
    MeasurableSet {x : Fin n → unitInterval |
      Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S ∧
        ∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n} := by
  have hm : MeasurableSet {y : unitInterval | |(y : ℝ)-1/2| ≤ lowerH κ n} := by
    apply measurableSet_le _ measurable_const
    fun_prop
  simpa [Causalean.Stat.RandomGraph.componentEvent] using
    Causalean.Stat.RandomGraph.measurableSet_componentEvent (sharedGraph κ n) Finset.univ
      (fun _ => {y : unitInterval | |(y : ℝ)-1/2| ≤ lowerH κ n}) S (fun _ => hm)

/-- A fixed vertex subset uses one prescribed root and the parent-array tree envelope. -/
-- @node: integral_shared_component_indicator_le
lemma integral_shared_component_indicator_le (hn : 0 < n) (S : Finset (Fin n))
    (r : Fin n) (hr : r ∈ S) (hsize : 2 ≤ S.card) :
    (∫ x, (if Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S ∧
      (∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n) then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin n => design)) ≤
    (S.card : ℝ)^(S.card-1)*(2*lowerH κ n)*(4*lowerEll κ n)^(S.card-1) := by
  classical
  let : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let M := sharedGraph κ n
  let rootEvent := fun _ : Fin n => {y : unitInterval | |(y : ℝ)-1/2| ≤ lowerH κ n}
  have hm : ∀ i, MeasurableSet (rootEvent i) := by
    intro i
    apply measurableSet_le _ measurable_const
    fun_prop
  have hInt : Integrable (fun x => if
      Causalean.Stat.RandomGraph.IsComponent (M.graph x) S ∧
        (∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n) then (1 : ℝ) else 0)
      (Measure.pi (fun _ : Fin n => design)) := by
    exact (integrable_const (1 : ℝ)).mono_nonneg
      ((Measurable.ite (measurable_shared_component_event κ n S)
        measurable_const measurable_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num))
      (Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num))
  have hcover (x : Fin n → unitInterval) :
      (if Causalean.Stat.RandomGraph.IsComponent (M.graph x) S ∧
        (∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n) then (1 : ℝ) else 0) ≤
      Causalean.Stat.RandomGraph.rootTreeWitnessCount M rootEvent r (S.erase r) x := by
    by_cases hc : Causalean.Stat.RandomGraph.IsComponent (M.graph x) S ∧
        (∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n)
    · rw [if_pos hc]
      have hroot := shared_component_vertex_in_window κ n S r hr hsize x hc.1
      have hevent : x ∈ Causalean.Stat.RandomGraph.componentEvent M {r} rootEvent S :=
        ⟨hc.1, r, by simp, hr, hroot⟩
      obtain ⟨r', hr', hrS, P, hP⟩ :=
        Causalean.Stat.RandomGraph.component_event_parent_cover M {r} rootEvent S x hevent
      have hrr : r' = r := by simpa using hr'
      subst r'
      have hex (s : Finset (Fin n)) (hs : s = S) : ∃ hr : r ∈ s,
          ∃ P : Causalean.Stat.RandomGraph.ParentEncoding s (⟨r, hr⟩ : s),
            P.Valid ∧ x ∈ Causalean.Stat.RandomGraph.partialTreeEvent
              (Causalean.Stat.RandomGraph.selectedEmbedding s) P (rootEvent r)
              M.edgeEvent Finset.univ := by
        subst s
        exact ⟨hrS, P, hP⟩
      obtain ⟨hrI, Q, hQ⟩ := hex _ (Finset.insert_erase hr)
      unfold Causalean.Stat.RandomGraph.rootTreeWitnessCount
      dsimp only
      have hterm : (if Q.Valid ∧ x ∈ Causalean.Stat.RandomGraph.partialTreeEvent
          (Causalean.Stat.RandomGraph.selectedEmbedding (insert r (S.erase r))) Q
          (rootEvent r) M.edgeEvent Finset.univ then (1 : ℝ) else 0) = 1 := if_pos hQ
      conv_lhs => rw [← hterm]
      exact Finset.single_le_sum
        (f := fun P : Causalean.Stat.RandomGraph.ParentEncoding
          ↥(insert r (S.erase r)) ⟨r, hrI⟩ =>
          if P.Valid ∧ x ∈ Causalean.Stat.RandomGraph.partialTreeEvent
            (Causalean.Stat.RandomGraph.selectedEmbedding (insert r (S.erase r))) P
            (rootEvent r) M.edgeEvent Finset.univ then (1 : ℝ) else 0)
        (fun P _ => by split_ifs <;> norm_num) (Finset.mem_univ Q)
    · rw [if_neg hc]
      unfold Causalean.Stat.RandomGraph.rootTreeWitnessCount
      exact Finset.sum_nonneg (fun P _ => by split_ifs <;> norm_num)
  have he := (lowerEll_pos κ n hn).le
  have hh : 0 ≤ lowerH κ n := by unfold lowerH; positivity
  have hsection : ∀ (i j : Fin n), i ≠ j → ∀ y : unitInterval,
      design {z | (z,y) ∈ M.edgeEvent i j} ≤ ENNReal.ofReal (4*lowerEll κ n) := by
    intro i j hij y
    calc
      design {z | (z,y) ∈ M.edgeEvent i j}
          ≤ design {z : unitInterval | |(z : ℝ)-(y : ℝ)| ≤ 2*lowerEll κ n} :=
        measure_mono (fun z hz => hz.2.2)
      _ ≤ ENNReal.ofReal (4*lowerEll κ n) := by
        convert design_absolute_ball_le (y : ℝ) (2*lowerEll κ n) using 1 <;> congr 1 <;> ring
  have hb := Causalean.Stat.RandomGraph.integral_rootTreeWitnessCount_le
    (fun _ : Fin n => design) M rootEvent r (S.erase r) (2*lowerH κ n)
    (4*lowerEll κ n) (by positivity) (by positivity) (hm r)
    (design_absolute_ball_le (1/2) (lowerH κ n)) hsection
  rw [Finset.insert_erase hr] at hb
  convert (integral_mono hInt
    (Causalean.Stat.RandomGraph.integrable_rootTreeWitnessCount
      (fun _ : Fin n => design) M rootEvent r (S.erase r) (hm r)) hcover).trans hb using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp only [M]
  split_ifs <;> rfl

/-- Labeled trees bound every component size without independent-edge assumptions. -/
-- @node: expected_component_count
lemma expected_component_count (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (m : ℕ) (hm : 2 ≤ m) :
  (∫ x, componentCount κ n m x ∂Measure.pi (fun _ : Fin n => design)) ≤
    (Nat.choose n m : ℝ)*(m : ℝ)^(m-1)*(2*lowerH κ n)*(4*lowerEll κ n)^(m-1) := by
  classical
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hInt (S : Finset (Fin n)) : Integrable (fun x => if
      Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S ∧
        (∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n) then (1 : ℝ) else 0)
      (Measure.pi (fun _ : Fin n => design)) := by
    exact (integrable_const (1 : ℝ)).mono_nonneg
      ((Measurable.ite (measurable_shared_component_event κ n S)
        measurable_const measurable_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num))
      (Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num))
  have hcount (x : Fin n → unitInterval) : componentCount κ n m x =
      ∑ S ∈ Finset.univ.powersetCard m,
        if Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S ∧
          (∃ i ∈ S, |(x i : ℝ)-1/2| ≤ lowerH κ n) then (1 : ℝ) else 0 := by
    simp [componentCount, Finset.sum_boole]
  simp_rw [hcount]
  rw [integral_finsetSum _ (fun S _ => hInt S)]
  calc
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (m : ℝ)^(m-1)*(2*lowerH κ n)*(4*lowerEll κ n)^(m-1) := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard := (Finset.mem_powersetCard.mp hS).2
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨r, hr⟩ := hne
      simpa only [hcard] using integral_shared_component_indicator_le κ n (by omega) S r hr
        (by omega)
    _ = _ := by simp; ring

/-- A fair bit design provides the uniform finite sign prior. -/
-- @node: componentFairBitDesign
def componentFairBitDesign : Causalean.Experimentation.DesignBased.FiniteDesign Bool where
  p _ := 1 / 2
  p_nonneg _ := by norm_num
  p_sum := by simp [Fintype.sum_bool]

/-- Independent finite-coordinate expectations factor over any disjoint block family. -/
-- @node: component_disjoint_blocks_expectation
lemma component_disjoint_blocks_expectation
    {ι η : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq η]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (D : ∀ i, Causalean.Experimentation.DesignBased.FiniteDesign (α i))
    (S : Finset η) (A : η → Finset ι) (F : η → (∀ i, α i) → ℝ)
    (hd : Set.PairwiseDisjoint (S : Set η) A)
    (hf : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → F k v = F k w) :
    (Causalean.Experimentation.DesignBased.prodDesign D).E (fun v => ∏ k ∈ S, F k v) =
      ∏ k ∈ S, (Causalean.Experimentation.DesignBased.prodDesign D).E (F k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Causalean.Experimentation.DesignBased.FiniteDesign.E_const]
  | @insert k S hk ih =>
    simp only [Finset.prod_insert hk]
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_prod_block_mul
      D (A k) (F k) (fun v => ∏ l ∈ S, F l v)]
    · rw [ih]
      · intro i hi j hj hij
        exact hd (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
      · intro l hl
        exact hf l (Finset.mem_insert_of_mem hl)
    · exact hf k (Finset.mem_insert_self k S)
    · intro v w hagree
      apply Finset.prod_congr rfl
      intro l hl
      apply hf l (Finset.mem_insert_of_mem hl) v w
      intro i hi
      apply hagree i
      intro hik
      have hkl : k ≠ l := by intro heq; subst l; exact hk hl
      exact Finset.disjoint_left.mp
        (hd (Finset.mem_insert_self k S) (Finset.mem_insert_of_mem hl) hkl) hik hi

/-- Uniform sign averages inherit disjoint-block product factorization. -/
-- @node: component_fair_sign_average_factorization
lemma component_fair_sign_average_factorization
    {ι η : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq η]
    (S : Finset η) (A : η → Finset ι) (F : η → (ι → Bool) → ℝ)
    (hd : Set.PairwiseDisjoint (S : Set η) A)
    (hf : ∀ k ∈ S, ∀ v w, (∀ i ∈ A k, v i = w i) → F k v = F k w) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ * (∑ v, ∏ k ∈ S, F k v) =
      ∏ k ∈ S, ((Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v, F k v) := by
  have hav (G : (ι → Bool) → ℝ) :
      (Causalean.Experimentation.DesignBased.prodDesign
        (fun _ : ι => componentFairBitDesign)).E G =
        (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ v, G v := by
    simp only [Causalean.Experimentation.DesignBased.FiniteDesign.E,
      Causalean.Experimentation.DesignBased.prodDesign_p, componentFairBitDesign,
      Finset.prod_const, Finset.card_univ, ← Finset.mul_sum]
    simp [Fintype.card_fun, inv_pow, one_div]
  simpa only [hav] using component_disjoint_blocks_expectation
    (fun _ => componentFairBitDesign) S A F hd hf

/-- All connected components of the shared-sign graph, including isolated records. -/
-- @node: sharedComponents
def sharedComponents (x : Fin n → unitInterval) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter
    (fun S => Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S)

/-- Each record lies in a shared-sign graph component. -/
-- @node: shared_components_cover
lemma shared_components_cover (x : Fin n → unitInterval) (i : Fin n) :
    ∃ S ∈ sharedComponents κ n x, i ∈ S := by
  let G := (sharedGraph κ n).graph x
  let C := G.connectedComponentMk i
  let S := C.supp.toFinset
  have hS : (S : Set (Fin n)) = C.supp := Set.coe_toFinset _
  refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩, ?_⟩
  · exact (Causalean.Stat.RandomGraph.isComponent_iff_exists_connectedComponent G S).mpr
      ⟨C, hS.symm⟩
  · change i ∈ C.supp.toFinset
    simp [C, SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- Distinct shared-sign components have disjoint record sets. -/
-- @node: shared_components_disjoint
lemma shared_components_disjoint (x : Fin n → unitInterval) :
    Set.PairwiseDisjoint (sharedComponents κ n x : Set (Finset (Fin n))) id := by
  intro S hS T hT hne
  obtain ⟨C, hC⟩ := (Causalean.Stat.RandomGraph.isComponent_iff_exists_connectedComponent _ S).mp
    (Finset.mem_filter.mp hS).2
  obtain ⟨D, hD⟩ := (Causalean.Stat.RandomGraph.isComponent_iff_exists_connectedComponent _ T).mp
    (Finset.mem_filter.mp hT).2
  apply Finset.disjoint_left.mpr
  intro i hiS hiT
  have he : C = D := SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (by simpa [hC] using hiS) (by simpa [hD] using hiT)
  apply hne
  apply Finset.coe_injective
  exact hC.symm.trans ((congrArg SimpleGraph.ConnectedComponent.supp he).trans hD)

/-- A component's active latent sign coordinates. -/
-- @node: sharedSignBlock
def sharedSignBlock (x : Fin n → unitInterval) (S : Finset (Fin n)) :
    Finset (Fin (signCount κ n)) :=
  Finset.univ.filter (fun j => ∃ i ∈ S, lowerCutoff κ n (x i)*frame κ n j (x i) ≠ 0)

/-- Any nonzero localized frame coordinate lies in the macro window. -/
-- @node: active_cutoff_in_window
lemma active_cutoff_in_window (hn : 0 < n) (x : unitInterval)
    (hx : lowerCutoff κ n x ≠ 0) : |(x : ℝ)-1/2| ≤ lowerH κ n := by
  have hh : 0 < lowerH κ n := Real.rpow_pos_of_pos (lowerEll_pos κ n hn) _
  have hpos : 0 < lowerCutoff κ n x :=
    lt_of_le_of_ne (le_max_left _ _) (Ne.symm hx)
  have hdiv : |(x : ℝ)-1/2|/lowerH κ n < 1 := by
    unfold lowerCutoff at hpos
    rcases (lt_max_iff.mp hpos) with h | h
    · exact False.elim (lt_irrefl _ h)
    · linarith
  exact le_of_lt (by simpa using (div_lt_iff₀ hh).mp hdiv)

/-- Components cannot share a latent coordinate: common active support gives an edge. -/
-- @node: shared_sign_blocks_disjoint
lemma shared_sign_blocks_disjoint (hn : 0 < n) (x : Fin n → unitInterval) :
    Set.PairwiseDisjoint (sharedComponents κ n x : Set (Finset (Fin n)))
      (sharedSignBlock κ n x) := by
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro j hjS hjT
  obtain ⟨i, hi, hij⟩ := (Finset.mem_filter.mp hjS).2
  obtain ⟨l, hl, hlj⟩ := (Finset.mem_filter.mp hjT).2
  have hdis := Finset.disjoint_left.mp (shared_components_disjoint κ n x hS hT hne)
  have hil : i ≠ l := by intro he; subst l; exact hdis hi hl
  have hadj : ((sharedGraph κ n).graph x).Adj i l := by
    refine ⟨hil, ?_⟩
    exact ⟨active_cutoff_in_window κ n hn _ (left_ne_zero_of_mul hij),
      active_cutoff_in_window κ n hn _ (left_ne_zero_of_mul hlj),
      frame_support_diameter κ n hn j _ _ (right_ne_zero_of_mul hij)
        (right_ne_zero_of_mul hlj)⟩
  have hlS := (Finset.mem_filter.mp hS).2.2 i hi l hadj
  exact hdis hlS hl

/-- A record likelihood is invariant under changes to inactive latent signs. -/
-- @node: lower_density_depends_on_sign_block
lemma lower_density_depends_on_sign_block (x : Fin n → unitInterval)
    (S : Finset (Fin n)) (s t : ℝ) (z : Fin n → Bool × ℝ) (v w : Signs κ n)
    (hagree : ∀ j ∈ sharedSignBlock κ n x S, v j = w j) :
    (∏ i ∈ S, lowerDensity κ n s t v (x i) (z i)) =
      ∏ i ∈ S, lowerDensity κ n s t w (x i) (z i) := by
  apply Finset.prod_congr rfl
  intro i hi
  have he : lowerField κ n v (x i) = lowerField κ n w (x i) := by
    simp only [lowerField, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : lowerCutoff κ n (x i)*frame κ n j (x i) = 0
    · calc
        _ = sign (v j)*(lowerCutoff κ n (x i)*frame κ n j (x i)) := by ring
        _ = sign (w j)*(lowerCutoff κ n (x i)*frame κ n j (x i)) := by simp [hj]
        _ = _ := by ring
    · rw [hagree j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, hj⟩)]
  simp only [lowerDensity, he]

/-- The shared-sign graph components partition the conditional likelihood. -/
-- @node: conditional_component_factorization
lemma conditional_component_factorization (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (x : Fin n → unitInterval) (s t : ℝ) (hs : |s| ≤ lowerA κ n) (ht : |t| ≤ lowerB κ n)
    (z : Fin n → Bool × ℝ) :
  componentDensity κ n n x s t z =
    ∏ S ∈ Finset.univ.powerset.filter
      (fun S => Causalean.Stat.RandomGraph.IsComponent ((sharedGraph κ n).graph x) S),
      subsetDensity κ n S x s t z := by
  let C := sharedComponents κ n x
  have hcover : C.biUnion id = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
    exact shared_components_cover κ n x i
  have hprod (v : Signs κ n) :
      (∏ S ∈ C, ∏ i ∈ S, lowerDensity κ n s t v (x i) (z i)) =
        ∏ i, lowerDensity κ n s t v (x i) (z i) := by
    have hp := Finset.prod_biUnion
      (f := fun i => lowerDensity κ n s t v (x i) (z i))
      (shared_components_disjoint κ n x)
    rw [hcover] at hp
    simpa only [id_eq] using hp.symm
  have hf := component_fair_sign_average_factorization C (sharedSignBlock κ n x)
    (fun S v => ∏ i ∈ S, lowerDensity κ n s t v (x i) (z i))
    (shared_sign_blocks_disjoint κ n (by omega) x)
    (fun S _ v w ha => lower_density_depends_on_sign_block κ n x S s t z v w ha)
  simp_rw [hprod] at hf
  exact hf

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
