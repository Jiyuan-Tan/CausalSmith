module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TreeProbability
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.TreeSeries
/-! Component-count expectations as sums over fixed vertex sets, and ordered-tree
probability bounds on arbitrary distinct coordinates of the full sample. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Selecting distinct coordinates of an iid uniform sample preserves the uniform product law.  [the theorem's stated inputs and assumptions](hyp:he), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s,e). -/
-- @node: uniform_covariate_injection_map
lemma uniform_covariate_injection_map (n s : ℕ) (e : Fin s → Fin n)
    (he : Function.Injective e) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))).map
      (fun x i => x (e i)) =
        Measure.pi (fun _ : Fin s => (volume : Measure Covariate)) := by
  have hi : iIndepFun (fun i : Fin n => fun x : Fin n → Covariate => x i)
      (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  rw [(hi.precomp he).map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval
    (fun _ : Fin n => (volume : Measure Covariate)) (e i)).map_eq

/-- A Borel event on distinct selected sample coordinates has exactly its smaller product probability.  [the theorem's stated inputs and assumptions](hyp:he,A,hA), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s,e). -/
-- @node: uniform_covariate_injection_preimage
lemma uniform_covariate_injection_preimage (n s : ℕ) (e : Fin s → Fin n)
    (he : Function.Injective e) (A : Set (Fin s → Covariate)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      ((fun x i => x (e i)) ⁻¹' A) =
        (Measure.pi (fun _ : Fin s => (volume : Measure Covariate))) A := by
  rw [← uniform_covariate_injection_map n s e he, Measure.map_apply (by fun_prop) hA]

/-- The recursive shared-sign tree event is Borel, including its support-boundary conventions.  [the theorem's stated inputs and assumptions](hyp:p,m,m), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL). -/
-- @node: measurableSet_orderedSharedTreeEvent
lemma measurableSet_orderedSharedTreeEvent (hL : ℝ)
    (p : (m : ℕ) → Fin (m + 1)) (m : ℕ) :
    MeasurableSet (orderedSharedTreeEvent hL p m) := by
  induction m with
  | zero => exact MeasurableSet.univ
  | succ m ih =>
    exact (ih.preimage (by fun_prop)).inter
      (measurableSet_sharedAdj hL (m + 2) (Fin.last (m + 1)) (p m).castSucc)

/-- The specified-tree envelope holds for any distinct vertices in the original sample,
so discarding the unused sample coordinates costs no probability factor. The result uses [the stated assumptions](hyp:hL,hhL,hm,he) and establishes [the displayed conclusion](goal). -/
-- @node: selected_orderedSharedTreeEvent_volume_le
lemma selected_orderedSharedTreeEvent_volume_le (hL : ℝ)
    (hhL : 0 < hL ∧ hL ≤ 1 / 4) (n m : ℕ) (hm : 1 ≤ m)
    (e : Fin (m + 1) → Fin n) (he : Function.Injective e)
    (p : (k : ℕ) → Fin (k + 1)) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      {x | (fun i => x (e i)) ∈ orderedSharedTreeEvent hL p m} ≤
        ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ m) := by
  change (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
    ((fun x i => x (e i)) ⁻¹' orderedSharedTreeEvent hL p m) ≤ _
  rw [uniform_covariate_injection_preimage n (m + 1) e he _
    (measurableSet_orderedSharedTreeEvent hL p m)]
  exact orderedSharedTreeEvent_volume_le hL hhL p m hm

/-- The event that a fixed vertex set is one of the selected graph components is Borel. The result uses [the stated assumptions](hyp:hL) and establishes [the displayed conclusion](goal). -/
-- @node: measurableSet_fixed_component
lemma measurableSet_fixed_component (hL : ℝ) (n : ℕ) (C : Finset (Fin n)) :
    MeasurableSet {x : Fin n → Covariate | C ∈ orderedComponents hL n x} := by
  classical
  have he : {x : Fin n → Covariate | C ∈ orderedComponents hL n x} =
      ⋃ G : SimpleGraph (Fin n),
        (if C ∈ componentsOfGraph n G then {x | sharedGraph hL n x = G} else ∅) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨sharedGraph hL n x, ?_⟩
      have hc : C ∈ componentsOfGraph n (sharedGraph hL n x) := hx
      simp [hc]
    · rintro ⟨G, hx⟩
      split_ifs at hx with hc
      · have hg : sharedGraph hL n x = G := hx
        rw [orderedComponents_eq_of_sharedGraph_eq hL n x G hg]
        exact hc
      · exact False.elim hx
  rw [he]
  apply MeasurableSet.iUnion
  intro G
  split_ifs
  · exact measurableSet_sharedGraph_eq hL n G
  · exact MeasurableSet.empty

/-- Counting size-s components is exactly summing their indicators over all size-s vertex sets.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s). -/
-- @node: sizeComponentCount_eq_sum_indicators
lemma sizeComponentCount_eq_sum_indicators (hL : ℝ) (n s : ℕ)
    (x : Fin n → Covariate) :
    (sizeComponentCount hL n x s : ℝ≥0∞) =
      ∑ C ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        {x : Fin n → Covariate | C ∈ orderedComponents hL n x}.indicator
          (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  have he : ((orderedComponents hL n x).toFinset.filter (fun C => C.card = s)) =
      ((Finset.univ : Finset (Fin n)).powersetCard s).filter
        (fun C => C ∈ orderedComponents hL n x) := by
    ext C
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact and_comm
  rw [sizeComponentCount, he]
  simp [Set.indicator]

/-- Taking expectations of the exact indicator count gives a sum of fixed-component
probabilities.  [the theorem's stated inputs and assumptions](hyp:μ), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s). -/
-- @node: lintegral_sizeComponentCount_eq_sum
lemma lintegral_sizeComponentCount_eq_sum (hL : ℝ) (n s : ℕ)
    (μ : Measure (Fin n → Covariate)) :
    (∫⁻ x, (sizeComponentCount hL n x s : ℝ≥0∞) ∂μ) =
      ∑ C ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        μ {x | C ∈ orderedComponents hL n x} := by
  classical
  simp_rw [sizeComponentCount_eq_sum_indicators]
  rw [lintegral_finsetSum _ (fun C _ =>
    measurable_const.indicator (measurableSet_fixed_component hL n C))]
  apply Finset.sum_congr rfl
  intro C _
  rw [lintegral_indicator_const (measurableSet_fixed_component hL n C), one_mul]

/-- A common probability bound for fixed size-s components gives the binomial
component-count bound.  [the theorem's stated inputs and assumptions](hyp:μ,b,hb), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s). -/
-- @node: lintegral_sizeComponentCount_le_choose_mul
lemma lintegral_sizeComponentCount_le_choose_mul (hL : ℝ) (n s : ℕ)
    (μ : Measure (Fin n → Covariate)) (b : ℝ≥0∞)
    (hb : ∀ C : Finset (Fin n), C.card = s →
      μ {x | C ∈ orderedComponents hL n x} ≤ b) :
    (∫⁻ x, (sizeComponentCount hL n x s : ℝ≥0∞) ∂μ) ≤
      (n.choose s : ℝ≥0∞) * b := by
  classical
  rw [lintegral_sizeComponentCount_eq_sum]
  calc
    _ ≤ ∑ C ∈ (Finset.univ : Finset (Fin n)).powersetCard s, b := by
      apply Finset.sum_le_sum
      intro C hC
      exact hb C (Finset.mem_powersetCard.mp hC).2
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul]

/-- The two vertices of a two-element graph component share an edge.  [the theorem's stated inputs and assumptions](hyp:i,j,hij,hC), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: sharedAdj_of_pair_component
lemma sharedAdj_of_pair_component (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (i j : Fin n) (hij : i ≠ j)
    (hC : ({i, j} : Finset (Fin n)) ∈ orderedComponents hL n x) :
    sharedAdj hL n x i j := by
  classical
  obtain ⟨r, _, hr⟩ := (mem_orderedComponents hL n x {i, j}).mp hC
  have hri : (sharedGraph hL n x).Reachable r i :=
    (mem_componentVertices hL n x r i).mp (by rw [hr]; simp)
  have hrj : (sharedGraph hL n x).Reachable r j :=
    (mem_componentVertices hL n x r j).mp (by rw [hr]; simp)
  obtain ⟨w⟩ := hri.symm.trans hrj
  cases w with
  | nil => exact False.elim (hij rfl)
  | @cons u v w hedge tail =>
    have hrv := hri.trans hedge.reachable
    have hv : v = i ∨ v = j := by
      have hm := (mem_componentVertices hL n x r v).mpr hrv
      rw [hr] at hm
      simpa using hm
    rcases hv with hvi | hvj
    · exact False.elim (hedge.ne hvi.symm)
    · simpa [hvj, sharedGraph] using hedge

/-- A specified pair of distinct sampled vertices shares a sign with probability at most
its macro root length times its micro child length.  [the theorem's stated inputs and assumptions](hyp:n,i,j,hij), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: sharedAdj_uniform_volume_le
lemma sharedAdj_uniform_volume_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      {x | sharedAdj hL n x i j} ≤ ENNReal.ofReal (2 * hL * (4 * deltaL hL)) := by
  let e : Fin 2 → Fin n := ![j, i]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have ht := selected_orderedSharedTreeEvent_volume_le hL hhL n 1 (by omega)
    e he (fun _ => 0)
  have hsub : {x : Fin n → Covariate | sharedAdj hL n x i j} ⊆
      {x | (fun k => x (e k)) ∈ orderedSharedTreeEvent hL (fun _ => 0) 1} := by
    intro x hx
    simpa [orderedSharedTreeEvent, sharedAdj, e] using hx.2
  exact (measure_mono hsub).trans (by simpa using ht)

/-- The component event for any specified two-set is bounded by the corresponding
single-edge event.  [the theorem's stated inputs and assumptions](hyp:n,C,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: pair_component_uniform_volume_le
lemma pair_component_uniform_volume_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (C : Finset (Fin n)) (hc : C.card = 2) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      {x | C ∈ orderedComponents hL n x} ≤ ENNReal.ofReal (2 * hL * (4 * deltaL hL)) := by
  classical
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
  exact (measure_mono (fun x hx => sharedAdj_of_pair_component hL n x i j hij hx)).trans
    (sharedAdj_uniform_volume_le hL hhL n i j hij)

/-- The actual expected number of two-vertex components satisfies the roadmap's
binomial labeled-tree bound, with no assumed probability estimate.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: lintegral_sizeComponentCount_two_le
lemma lintegral_sizeComponentCount_two_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    (∫⁻ x, (sizeComponentCount hL n x 2 : ℝ≥0∞)
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))) ≤
      ENNReal.ofReal ((n.choose 2 : ℝ) * (2 * hL * (4 * deltaL hL))) := by
  have hb := lintegral_sizeComponentCount_le_choose_mul hL n 2
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))) _
    (pair_component_uniform_volume_le hL hhL n)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hb
  exact hb

/-- Every vertex in a component with another vertex has a neighbor in that component.
This uses the first step of a connecting walk, without assuming any graph geometry.  [the theorem's stated inputs and assumptions](hyp:C,hC,i,j,hi,hj,hij), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: component_vertex_has_neighbor
lemma component_vertex_has_neighbor (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hC : C ∈ orderedComponents hL n x)
    (i j : Fin n) (hi : i ∈ C) (hj : j ∈ C) (hij : i ≠ j) :
    ∃ v ∈ C, sharedAdj hL n x i v := by
  obtain ⟨r, _, hr⟩ := (mem_orderedComponents hL n x C).mp hC
  have hri : (sharedGraph hL n x).Reachable r i :=
    (mem_componentVertices hL n x r i).mp (by rw [hr]; exact hi)
  have hrj : (sharedGraph hL n x).Reachable r j :=
    (mem_componentVertices hL n x r j).mp (by rw [hr]; exact hj)
  obtain ⟨w⟩ := hri.symm.trans hrj
  cases w with
  | nil => exact False.elim (hij rfl)
  | @cons u v w hedge tail =>
    refine ⟨v, ?_, hedge⟩
    rw [← hr]
    exact (mem_componentVertices hL n x r v).mpr (hri.trans hedge.reachable)

/-- A three-vertex component contains one of the three labeled spanning trees.  [the theorem's stated inputs and assumptions](hyp:i,j,k,hij,hik,hjk,hC), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: triple_component_contains_tree
lemma triple_component_contains_tree (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hC : ({i, j, k} : Finset (Fin n)) ∈ orderedComponents hL n x) :
    (sharedAdj hL n x i j ∧ sharedAdj hL n x i k) ∨
    (sharedAdj hL n x j i ∧ sharedAdj hL n x j k) ∨
    (sharedAdj hL n x k i ∧ sharedAdj hL n x k j) := by
  classical
  have hn (a b : Fin n) (ha : a ∈ ({i, j, k} : Finset (Fin n)))
      (hb : b ∈ ({i, j, k} : Finset (Fin n))) (hab : a ≠ b) :=
    component_vertex_has_neighbor hL n x {i, j, k} hC a b ha hb hab
  obtain ⟨v, hv, hiv⟩ := hn i j (by simp) (by simp) hij
  have hv' : v = j ∨ v = k := by
    simpa [hiv.1.symm] using hv
  rcases hv' with hvj | hvk
  <;> subst v
  · obtain ⟨v, hv, hkv⟩ := hn k i (by simp) (by simp) hik.symm
    have hv' : v = i ∨ v = j := by simpa [hkv.1.symm] using hv
    rcases hv' with hvi | hvj
    <;> subst v
    · exact Or.inl ⟨hiv, SimpleGraph.Adj.symm (G := sharedGraph hL n x) hkv⟩
    · exact Or.inr (Or.inl ⟨SimpleGraph.Adj.symm (G := sharedGraph hL n x) hiv,
        SimpleGraph.Adj.symm (G := sharedGraph hL n x) hkv⟩)
  · obtain ⟨v, hv, hjv⟩ := hn j i (by simp) (by simp) hij.symm
    have hv' : v = i ∨ v = k := by simpa [hjv.1.symm] using hv
    rcases hv' with hvi | hvk
    <;> subst v
    · exact Or.inl ⟨SimpleGraph.Adj.symm (G := sharedGraph hL n x) hjv, hiv⟩
    · exact Or.inr (Or.inr ⟨SimpleGraph.Adj.symm (G := sharedGraph hL n x) hiv,
        SimpleGraph.Adj.symm (G := sharedGraph hL n x) hjv⟩)

/-- A specified two-edge star on three distinct records obeys the tree envelope.  [the theorem's stated inputs and assumptions](hyp:n,i,j,k,hij,hik,hjk), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: triple_star_uniform_volume_le
lemma triple_star_uniform_volume_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      {x | sharedAdj hL n x i j ∧ sharedAdj hL n x i k} ≤
        ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ 2) := by
  let e : Fin 3 → Fin n := ![i, j, k]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have ht := selected_orderedSharedTreeEvent_volume_le hL hhL n 2 (by omega)
    e he (fun _ => 0)
  have hsub : {x : Fin n → Covariate | sharedAdj hL n x i j ∧ sharedAdj hL n x i k} ⊆
      {x | (fun a => x (e a)) ∈ orderedSharedTreeEvent hL (fun _ => 0) 2} := by
    intro x hx
    have hj := SimpleGraph.Adj.symm (G := sharedGraph hL n x) hx.1
    have hk := SimpleGraph.Adj.symm (G := sharedGraph hL n x) hx.2
    simpa [orderedSharedTreeEvent, sharedAdj, e] using And.intro hj.2 hk.2
  exact (measure_mono hsub).trans ht

/-- The probability that a specified triple is a component is at most the sum
of its three labeled spanning-tree envelopes.  [the theorem's stated inputs and assumptions](hyp:n,i,j,k,hij,hik,hjk), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: triple_component_uniform_volume_le
lemma triple_component_uniform_volume_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      {x | ({i, j, k} : Finset (Fin n)) ∈ orderedComponents hL n x} ≤
        ENNReal.ofReal (3 * (2 * hL * (4 * deltaL hL) ^ 2)) := by
  classical
  let μ := Measure.pi (fun _ : Fin n => (volume : Measure Covariate))
  let A := {x | sharedAdj hL n x i j ∧ sharedAdj hL n x i k}
  let B := {x | sharedAdj hL n x j i ∧ sharedAdj hL n x j k}
  let D := {x | sharedAdj hL n x k i ∧ sharedAdj hL n x k j}
  have hs : {x | ({i, j, k} : Finset (Fin n)) ∈ orderedComponents hL n x} ⊆
      A ∪ (B ∪ D) := fun x hx =>
    triple_component_contains_tree hL n x i j k hij hik hjk hx
  have ha := triple_star_uniform_volume_le hL hhL n i j k hij hik hjk
  have hb := triple_star_uniform_volume_le hL hhL n j i k hij.symm hjk hik
  have hd := triple_star_uniform_volume_le hL hhL n k i j hik.symm hjk.symm hij
  calc
    _ ≤ μ (A ∪ (B ∪ D)) := measure_mono hs
    _ ≤ μ A + (μ B + μ D) :=
      (measure_union_le A (B ∪ D)).trans (add_le_add le_rfl (measure_union_le B D))
    _ ≤ ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ 2) +
        (ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ 2) +
         ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ 2)) :=
      add_le_add ha (add_le_add hb hd)
    _ = _ := by
      have hh : 0 < hL := hhL.1
      have hn : 0 ≤ 2 * hL * (4 * deltaL hL) ^ 2 := by positivity
      rw [← ENNReal.ofReal_add hn hn, ← ENNReal.ofReal_add hn (add_nonneg hn hn)]
      congr 1
      ring

/-- Every fixed size-three component obeys the Cayley envelope with three trees.  [the theorem's stated inputs and assumptions](hyp:n,C,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: card_three_component_uniform_volume_le
lemma card_three_component_uniform_volume_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (C : Finset (Fin n)) (hc : C.card = 3) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      {x | C ∈ orderedComponents hL n x} ≤
        ENNReal.ofReal (3 * (2 * hL * (4 * deltaL hL) ^ 2)) := by
  classical
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hc
  exact triple_component_uniform_volume_le hL hhL n i j k hij hik hjk

/-- The expected number of size-three components satisfies the roadmap's
binomial Cayley bound with no assumed component probability estimate.  [the theorem's stated inputs and assumptions](hyp:n), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hhL). -/
-- @node: lintegral_sizeComponentCount_three_le
lemma lintegral_sizeComponentCount_three_le (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) :
    (∫⁻ x, (sizeComponentCount hL n x 3 : ℝ≥0∞)
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))) ≤
      ENNReal.ofReal ((n.choose 3 : ℝ) * 2 * hL * 3 ^ (3 - 2 : ℕ) *
        (4 * deltaL hL) ^ (3 - 1 : ℕ)) := by
  have hb := lintegral_sizeComponentCount_le_choose_mul hL n 3
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate))) _
    (card_three_component_uniform_volume_le hL hhL n)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hb
  convert hb using 1 <;> congr 1 <;> norm_num <;> ring

end CausalSmith.Stat.PrivateCateRoughdesign
