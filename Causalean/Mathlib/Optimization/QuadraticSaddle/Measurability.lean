module
public import Causalean.Mathlib.Optimization.QuadraticSaddle.Basic

/-!
# Borel value and saddle relations for finite quadratics

This module proves that the finite-quadratic saddle relation and the attained max-min value are
Borel on a measurable parameter domain of pointwise saddle attainment.
-/

public section

namespace Causalean.Mathlib.Optimization.QuadraticSaddle

variable {Θ ι κ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
  [Fintype ι] [Fintype κ]

/-- A [fixed polytope](hyp:P) and [quadratic family](hyp:Q) have a [Borel saddle relation](goal)
in the parameter, finite weight vector, and scalar decision, including tied saddles and zero
quadratic coefficients. -/
theorem measurableSet_isSaddle (P : Polytope ι κ) (Q : Quadratics Θ ι) :
    MeasurableSet {x : Θ × (EuclideanSpace ℝ ι × ℝ) |
      IsSaddle P Q x.1 x.2.1 x.2.2} := by
  classical
  letI : Nonempty P.weights := Set.nonempty_coe_sort.mpr P.nonempty
  let d : ℕ → P.weights := TopologicalSpace.denseSeq P.weights
  have hd : Dense (Set.range d) := by
    simpa only [DenseRange, d] using TopologicalSpace.denseRange_denseSeq P.weights
  have hobj := Q.measurable_objective
  have hfeas : MeasurableSet {x : Θ × (EuclideanSpace ℝ ι × ℝ) |
      x.2.1 ∈ P.weights} :=
    P.measurableSet_weights.preimage (measurable_fst.comp measurable_snd)
  have hrat : ∀ q : ℚ, MeasurableSet {x : Θ × (EuclideanSpace ℝ ι × ℝ) |
      Q.objective x.1 x.2.1 x.2.2 ≤ Q.objective x.1 x.2.1 (q : ℝ)} := by
    intro q
    apply measurableSet_le hobj
    exact hobj.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk measurable_const))
  have hwt : ∀ n : ℕ, MeasurableSet {x : Θ × (EuclideanSpace ℝ ι × ℝ) |
      Q.objective x.1 (d n).1 x.2.2 ≤ Q.objective x.1 x.2.1 x.2.2} := by
    intro n
    apply measurableSet_le
    · exact hobj.comp (measurable_fst.prodMk
        (measurable_const.prodMk (measurable_snd.comp measurable_snd)))
    · exact hobj
  have heq : {x : Θ × (EuclideanSpace ℝ ι × ℝ) |
      IsSaddle P Q x.1 x.2.1 x.2.2} =
      {x | x.2.1 ∈ P.weights} ∩ (
      (⋂ q : ℚ, {x | Q.objective x.1 x.2.1 x.2.2 ≤
        Q.objective x.1 x.2.1 (q : ℝ)}) ∩
      (⋂ n : ℕ, {x | Q.objective x.1 (d n).1 x.2.2 ≤
        Q.objective x.1 x.2.1 x.2.2})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, IsSaddle]
    constructor
    · rintro ⟨ha, ht, hb⟩
      exact ⟨ha, fun q => ht q, fun n => hb (d n).1 (d n).2⟩
    · rintro ⟨ha, ht, hb⟩
      refine ⟨ha, ?_, ?_⟩
      · have hc : Continuous (fun u : ℝ => Q.objective x.1 x.2.1 u) := by
          unfold Quadratics.objective
          fun_prop
        have hden : Dense (Set.range (fun q : ℚ => (q : ℝ))) := Rat.denseRange_cast
        have hbound := hden.lowerBounds_image hc
        have hm : Q.objective x.1 x.2.1 x.2.2 ∈
            lowerBounds ((fun u : ℝ => Q.objective x.1 x.2.1 u) ''
              Set.range (fun q : ℚ => (q : ℝ))) := by
          rintro y ⟨u, ⟨q, rfl⟩, rfl⟩
          exact ht q
        rw [hbound] at hm
        exact fun u => hm (Set.mem_range_self u)
      · have hc : Continuous (fun β : P.weights => Q.objective x.1 β.1 x.2.2) := by
          unfold Quadratics.objective
          fun_prop
        have hbound := hd.upperBounds_image hc
        have hm : Q.objective x.1 x.2.1 x.2.2 ∈
            upperBounds ((fun β : P.weights => Q.objective x.1 β.1 x.2.2) ''
              Set.range d) := by
          rintro y ⟨β, ⟨n, rfl⟩, rfl⟩
          exact hb n
        rw [hbound] at hm
        intro β hβ
        exact hm ⟨⟨β, hβ⟩, rfl⟩
  rw [heq]
  exact hfeas.inter ((MeasurableSet.iInter hrat).inter (MeasurableSet.iInter hwt))

/-- A [fixed polytope](hyp:P), [quadratic family](hyp:Q), [Borel parameter domain](hyp:D,hD),
and [pointwise saddle-attainment certificate](hyp:hAttains) give a [Borel max-min value on that
domain](goal). -/
theorem measurable_value_on (P : Polytope ι κ) (Q : Quadratics Θ ι)
    (D : Set Θ) (hD : MeasurableSet D)
    (hAttains : ∀ θ ∈ D, ∃ α t, IsSaddle P Q θ α t) :
    Measurable (fun θ : D => value P Q θ.1) := by
  classical
  letI : Nonempty P.weights := Set.nonempty_coe_sort.mpr P.nonempty
  let d : ℕ → P.weights := TopologicalSpace.denseSeq P.weights
  have hd : Dense (Set.range d) := by
    simpa only [DenseRange, d] using TopologicalSpace.denseRange_denseSeq P.weights
  let M : Θ → ℝ → ℝ := fun θ t =>
    sSup ((fun β : EuclideanSpace ℝ ι => Q.objective θ β t) '' P.weights)
  have hM : Measurable (fun x : Θ × ℝ => M x.1 x.2) := by
    have hn : Measurable (fun x : Θ × ℝ =>
        ⨆ n : ℕ, Q.objective x.1 (d n).1 x.2) := by
      apply Measurable.iSup
      intro n
      exact Q.measurable_objective.comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    convert hn using 1
    ext x
    change sSup ((fun β : EuclideanSpace ℝ ι => Q.objective x.1 β x.2) ''
      P.weights) = ⨆ n : ℕ, Q.objective x.1 (d n).1 x.2
    rw [sSup_image']
    have hc : Continuous (fun β : P.weights => Q.objective x.1 β.1 x.2) := by
      unfold Quadratics.objective
      fun_prop
    rw [← hd.ciSup' hc]
    have he : Function.Surjective
        (fun n : ℕ => (⟨d n, Set.mem_range_self n⟩ : Set.range d)) := by
      rintro ⟨z, n, rfl⟩
      exact ⟨n, rfl⟩
    exact (he.iSup_comp (fun s : Set.range d =>
      Q.objective x.1 s.1.1 x.2)).symm
  have hMc : ∀ θ : Θ, Continuous (M θ) := by
    intro θ
    apply P.compact.continuous_sSup
    change Continuous (fun p : ℝ × EuclideanSpace ℝ ι =>
      Q.objective θ p.2 p.1)
    unfold Quadratics.objective
    fun_prop
  have hEq : ∀ θ : D, (⨅ q : ℚ, M θ.1 q) = value P Q θ.1 := by
    intro θ
    obtain ⟨α, t, hs⟩ := hAttains θ.1 θ.2
    have hc : Continuous (fun β : EuclideanSpace ℝ ι => Q.objective θ.1 β t) := by
      unfold Quadratics.objective
      fun_prop
    have hbdd : BddAbove ((fun β : EuclideanSpace ℝ ι =>
        Q.objective θ.1 β t) '' P.weights) := P.compact.bddAbove_image hc.continuousOn
    have hMt : M θ.1 t = Q.objective θ.1 α t := by
      apply le_antisymm
      · apply csSup_le (P.nonempty.image _)
        rintro y ⟨β, hβ, rfl⟩
        exact hs.2.2 β hβ
      · exact le_csSup hbdd ⟨α, hs.1, rfl⟩
    have hmin : IsMinOn (M θ.1) Set.univ t := by
      intro u hu
      have hcu : Continuous (fun β : EuclideanSpace ℝ ι => Q.objective θ.1 β u) := by
        unfold Quadratics.objective
        fun_prop
      have hbu : BddAbove ((fun β : EuclideanSpace ℝ ι =>
          Q.objective θ.1 β u) '' P.weights) := P.compact.bddAbove_image hcu.continuousOn
      rw [hMt]
      exact (hs.2.1 u).trans (le_csSup hbu ⟨α, hs.1, rfl⟩)
    have hr : Dense (Set.range (fun q : ℚ => (q : ℝ))) := Rat.denseRange_cast
    have hi := hr.ciInf' (hMc θ.1)
    have he : Function.Surjective
        (fun q : ℚ => (⟨(q : ℝ), Set.mem_range_self q⟩ :
          Set.range (fun q : ℚ => (q : ℝ)))) := by
      rintro ⟨z, q, rfl⟩
      exact ⟨q, rfl⟩
    rw [← he.iInf_comp (fun s : Set.range (fun q : ℚ => (q : ℝ)) => M θ.1 s.1)] at hi
    change (⨅ q : ℚ, M θ.1 (q : ℝ)) = ⨅ u : ℝ, M θ.1 u at hi
    rw [hi]
    have hlower : BddBelow (Set.range (M θ.1)) := by
      refine ⟨M θ.1 t, ?_⟩
      rintro y ⟨u, rfl⟩
      exact hmin (Set.mem_univ u)
    have hminEq : (⨅ u : ℝ, M θ.1 u) = M θ.1 t :=
      le_antisymm (ciInf_le hlower t) (le_ciInf fun u => hmin (Set.mem_univ u))
    rw [hminEq, hMt, value_eq_of_isSaddle P Q θ.1 α t hs]
  have hresult : Measurable (fun θ : D => ⨅ q : ℚ, M θ.1 q) := by
    apply Measurable.iInf
    intro q
    have hp : Measurable (fun θ : D => ((θ.1, (q : ℝ)) : Θ × ℝ)) :=
      measurable_subtype_coe.prodMk measurable_const
    simpa only [Function.comp_def] using hM.comp hp
  convert hresult using 1
  ext θ
  exact (hEq θ).symm

end Causalean.Mathlib.Optimization.QuadraticSaddle
