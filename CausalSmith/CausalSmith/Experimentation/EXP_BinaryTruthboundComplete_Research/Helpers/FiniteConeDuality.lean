import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.BooleanMobius
import Causalean.PO.ID.Partial.LP.ConicDuality
import Causalean.Mathlib.Optimization.KKT
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Finite observable-margin linear-program duality interfaces used by both full and truncated programs. -/

open scoped BigOperators
open Finset Set
open Filter Topology

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- Nonnegative schedule weights matching the observable moments through degree `r`. -/
-- @node: degreeDualMarginSet
def degreeDualMarginSet (E : Setup) (q : FullSupportObjective E) (r : WithTop ℕ) :
    Set (Theta E → ℝ) :=
  {μ | (∀ θ, 0 ≤ μ θ) ∧
    ∀ S ∈ observableComplex E, (S.card : WithTop ℕ) ≤ r →
      ∑ θ, μ θ * monomial E S θ = ∑ θ, q.1 θ * monomial E S θ}

/-- [A primal optimizer exists for every full-support objective](goal). -/
lemma observable_primal_attained (E : Setup) (q : FullSupportObjective E) (r : WithTop ℕ) :
    ∃ b ∈ conservativeCone E r, (∑ θ, q.1 θ * b θ) = optValue E q r := by
  classical
  let obj : (Theta E → ℝ) → ℝ := fun b => ∑ θ, q.1 θ * b θ
  let C : ℝ := ∑ θ, |trueVarianceFn E θ|
  let b₀ : Theta E → ℝ := fun _ => C
  have hf_nonneg : ∀ θ, 0 ≤ trueVarianceFn E θ := by
    intro θ
    rw [designVarianceFn_eq_Var]
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.Var
      Causalean.Experimentation.DesignBased.FiniteDesign.E
    exact Finset.sum_nonneg fun z _ => mul_nonneg (E.design.p_nonneg z) (sq_nonneg _)
  have hf_le_C : ∀ θ, trueVarianceFn E θ ≤ C := by
    intro θ
    calc
      trueVarianceFn E θ ≤ |trueVarianceFn E θ| := le_abs_self _
      _ ≤ ∑ η, |trueVarianceFn E η| :=
        Finset.single_le_sum (s := Finset.univ) (f := fun η => |trueVarianceFn E η|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ θ)
      _ = C := rfl
  have hb₀_span : b₀ ∈ observableSpan E r := by
    letI : Nonempty E.Omega := by
      classical
      by_contra h
      haveI : IsEmpty E.Omega := not_nonempty_iff.mp h
      simpa using E.design.p_sum
    have hgen : monomial E ∅ ∈ observableSpan E r := by
      apply Submodule.subset_span
      exact ⟨∅, by simp [observableComplex], by simp, rfl⟩
    have hsmul := (observableSpan E r).smul_mem C hgen
    convert hsmul using 1
    ext θ
    simp [b₀, monomial]
  have hb₀ : b₀ ∈ conservativeCone E r := ⟨hb₀_span, hf_le_C⟩
  let K : Set (Theta E → ℝ) := conservativeCone E r ∩ {b | obj b ≤ obj b₀}
  have hobj_cont : Continuous obj := by
    apply continuous_finset_sum
    intro θ _
    fun_prop
  have hcone_closed : IsClosed (conservativeCone E r) := by
    have hspan : IsClosed (observableSpan E r : Set (Theta E → ℝ)) :=
      (observableSpan E r).closed_of_finiteDimensional
    have hdom : IsClosed {b : Theta E → ℝ | ∀ θ, trueVarianceFn E θ ≤ b θ} := by
      rw [show {b : Theta E → ℝ | ∀ θ, trueVarianceFn E θ ≤ b θ} =
          ⋂ θ, {b : Theta E → ℝ | trueVarianceFn E θ ≤ b θ} by ext b; simp]
      exact isClosed_iInter fun θ => isClosed_le continuous_const (continuous_apply θ)
    exact hspan.inter hdom
  have hK_closed : IsClosed K :=
    hcone_closed.inter (isClosed_le hobj_cont continuous_const)
  have hK_nonempty : K.Nonempty := by
    refine ⟨b₀, ?_⟩
    change b₀ ∈ conservativeCone E r ∧ obj b₀ ≤ obj b₀
    exact ⟨hb₀, le_rfl⟩
  let box : Set (Theta E → ℝ) :=
    Set.univ.pi fun θ => Set.Icc 0 (obj b₀ / q.1 θ)
  have hK_box : K ⊆ box := by
    intro b hb
    rw [Set.mem_pi]
    intro θ _
    have hbθ_nonneg : 0 ≤ b θ := (hf_nonneg θ).trans ((hb.1.2) θ)
    have hterm_nonneg : ∀ η, 0 ≤ q.1 η * b η := by
      intro η
      exact mul_nonneg (q.2.1 η).le ((hf_nonneg η).trans ((hb.1.2) η))
    have hterm_le : q.1 θ * b θ ≤ obj b₀ := by
      calc
        q.1 θ * b θ ≤ ∑ η, q.1 η * b η :=
          Finset.single_le_sum (fun η _ => hterm_nonneg η) (Finset.mem_univ θ)
        _ = obj b := rfl
        _ ≤ obj b₀ := hb.2
    constructor
    · exact hbθ_nonneg
    · exact (le_div_iff₀ (q.2.1 θ)).2 (by simpa [mul_comm] using hterm_le)
  have hbox_compact : IsCompact box := by
    exact isCompact_univ_pi fun θ => isCompact_Icc
  have hK_compact : IsCompact K := hbox_compact.of_isClosed_subset hK_closed hK_box
  obtain ⟨b, hbK, hbmin⟩ := hK_compact.exists_isMinOn hK_nonempty hobj_cont.continuousOn
  refine ⟨b, hbK.1, ?_⟩
  change obj b = sInf (obj '' conservativeCone E r)
  apply le_antisymm
  · apply le_csInf
    · exact ⟨obj b₀, ⟨b₀, hb₀, rfl⟩⟩
    · rintro y ⟨b', hb', rfl⟩
      by_cases hsub : obj b' ≤ obj b₀
      · exact hbmin ⟨hb', hsub⟩
      · exact hbK.2.trans (le_of_lt (lt_of_not_ge hsub))
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨b', hb', rfl⟩
      exact Finset.sum_nonneg fun θ _ =>
        mul_nonneg (q.2.1 θ).le ((hf_nonneg θ).trans ((hb'.2) θ))
    · exact ⟨b, hbK.1, rfl⟩

/-- If [a bound is feasible in the degree-restricted conservative cone](hyp:hb) and [a nonnegative dual weight matches every observable margin](hyp:hμ), then [the dual variance objective does not exceed the primal objective](goal). -/
lemma observable_weak_duality (E : Setup) (q : FullSupportObjective E) (r : WithTop ℕ)
    {b μ : Theta E → ℝ} (hb : b ∈ conservativeCone E r)
    (hμ : μ ∈ dualMarginSet E q) :
    ∑ θ, μ θ * trueVarianceFn E θ ≤ ∑ θ, q.1 θ * b θ := by
  have hmargin : ∀ u ∈ observableSpan E r,
      (∑ θ, μ θ * u θ) = ∑ θ, q.1 θ * u θ := by
    intro u hu
    unfold observableSpan at hu
    refine Submodule.span_induction
      (p := fun u _ => (∑ θ, μ θ * u θ) = ∑ θ, q.1 θ * u θ) ?_ ?_ ?_ ?_ hu
    · intro u hu
      rcases hu with ⟨S, hS, _hdeg, rfl⟩
      exact hμ.2 S hS
    · simp
    · intro u v _hu _hv ihu ihv
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ihu, ihv]
    · intro c u _hu ihu
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        (∑ θ, μ θ * (c * u θ)) = c * ∑ θ, μ θ * u θ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
        _ = c * ∑ θ, q.1 θ * u θ := by rw [ihu]
        _ = ∑ θ, q.1 θ * (c * u θ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
  calc
    (∑ θ, μ θ * trueVarianceFn E θ) ≤ ∑ θ, μ θ * b θ := by
      apply Finset.sum_le_sum
      intro θ _
      exact mul_le_mul_of_nonneg_left (hb.2 θ) (hμ.1 θ)
    _ = ∑ θ, q.1 θ * b θ := hmargin b hb.1

/-- If [a bound is feasible through the chosen degree](hyp:hb) and [a nonnegative dual weight matches exactly those degree-restricted margins](hyp:hμ), then [the dual variance objective does not exceed the primal objective](goal). -/
-- @node: observable_degree_weak_duality
lemma observable_degree_weak_duality (E : Setup) (q : FullSupportObjective E)
    (r : WithTop ℕ) {b μ : Theta E → ℝ} (hb : b ∈ conservativeCone E r)
    (hμ : μ ∈ degreeDualMarginSet E q r) :
    ∑ θ, μ θ * trueVarianceFn E θ ≤ ∑ θ, q.1 θ * b θ := by
  have hmargin : ∀ u ∈ observableSpan E r,
      (∑ θ, μ θ * u θ) = ∑ θ, q.1 θ * u θ := by
    intro u hu
    unfold observableSpan at hu
    refine Submodule.span_induction
      (p := fun u _ => (∑ θ, μ θ * u θ) = ∑ θ, q.1 θ * u θ) ?_ ?_ ?_ ?_ hu
    · intro u hu
      rcases hu with ⟨S, hS, hdeg, rfl⟩
      exact hμ.2 S hS hdeg
    · simp
    · intro u v _hu _hv ihu ihv
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ihu, ihv]
    · intro c u _hu ihu
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        (∑ θ, μ θ * (c * u θ)) = c * ∑ θ, μ θ * u θ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
        _ = c * ∑ θ, q.1 θ * u θ := by rw [ihu]
        _ = ∑ θ, q.1 θ * (c * u θ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro θ _
          ring
  calc
    (∑ θ, μ θ * trueVarianceFn E θ) ≤ ∑ θ, μ θ * b θ := by
      apply Finset.sum_le_sum
      intro θ _
      exact mul_le_mul_of_nonneg_left (hb.2 θ) (hμ.1 θ)
    _ = ∑ θ, q.1 θ * b θ := hmargin b hb.1

/-- [The degree-restricted primal optimum equals the supremum of the dual objective, and a dual optimizer attains that value](goal). -/
-- @node: observable_degree_strong_duality
lemma observable_degree_strong_duality (E : Setup) (q : FullSupportObjective E)
    (r : WithTop ℕ) :
    optValue E q r = sSup ((fun μ => ∑ θ, μ θ * trueVarianceFn E θ) ''
      degreeDualMarginSet E q r) ∧
    ∃ μ ∈ degreeDualMarginSet E q r,
      (∑ θ, μ θ * trueVarianceFn E θ) = optValue E q r := by
  classical
  let Col := {S : Finset (Fin E.K) //
    S ∈ observableComplex E ∧ (S.card : WithTop ℕ) ≤ r}
  let D := Fintype.card Col
  let e : Fin D ≃ Col := Fintype.equivFin Col |>.symm
  let N := Fintype.card (Theta E)
  let et : Fin N ≃ Theta E := Fintype.equivFin (Theta E) |>.symm
  let row : ℕ → EuclideanSpace ℝ (Fin D) := fun i =>
    if hi : i < N then WithLp.toLp 2 (fun j => monomial E (e j).1 (et ⟨i, hi⟩)) else 0
  let c : EuclideanSpace ℝ (Fin D) := WithLp.toLp 2 (fun j =>
    ∑ θ, q.1 θ * monomial E (e j).1 θ)
  obtain ⟨b, hb, hbopt⟩ := observable_primal_attained E q r
  let active : Finset ℕ := (Finset.range N).filter fun i =>
    if hi : i < N then b (et ⟨i, hi⟩) = trueVarianceFn E (et ⟨i, hi⟩) else False
  let x : EuclideanSpace ℝ (Fin D) := WithLp.toLp 2 (fun j => beta E b (e j).1)
  have hrepr : ∀ θ, b θ = ∑ j, beta E b (e j).1 * monomial E (e j).1 θ := by
    intro θ
    rw [boolean_mobius_expansion E b θ]
    calc
      ∑ S, beta E b S * monomial E S θ =
          ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin E.K) =>
            S ∈ observableComplex E ∧ (S.card : WithTop ℕ) ≤ r),
              beta E b S * monomial E S θ := by
        symm
        apply Finset.sum_subset (by simp)
        intro S _ hS
        have hout : S ∉ observableComplex E ∨ ¬(S.card : WithTop ℕ) ≤ r := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          exact not_and_or.mp hS
        rw [(observableSpan_iff_beta_vanishes_degree E b r).mp hb.1 S hout, zero_mul]
      _ = ∑ S : Col, beta E b S.1 * monomial E S.1 θ := by
        change (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin E.K) =>
            S ∈ observableComplex E ∧ (S.card : WithTop ℕ) ≤ r),
              beta E b S * monomial E S θ) =
          ∑ S : {S : Finset (Fin E.K) //
            S ∈ observableComplex E ∧ (S.card : WithTop ℕ) ≤ r},
              beta E b S.1 * monomial E S.1 θ
        exact Finset.sum_subtype
          (Finset.univ.filter fun S : Finset (Fin E.K) =>
            S ∈ observableComplex E ∧ (S.card : WithTop ℕ) ≤ r)
          (by simp) (fun S => beta E b S * monomial E S θ)
      _ = _ := (Fintype.sum_equiv e
        (fun j => beta E b (e j).1 * monomial E (e j).1 θ)
        (fun S : Col => beta E b S.1 * monomial E S.1 θ) (fun j => rfl)).symm
  have hinner_row (i : Fin N) (z : EuclideanSpace ℝ (Fin D)) :
      inner ℝ (row i) z = ∑ j, monomial E (e j).1 (et i) * z j := by
    simp [row, i.isLt, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hinner_c (z : EuclideanSpace ℝ (Fin D)) :
      inner ℝ c z = ∑ j, (∑ θ, q.1 θ * monomial E (e j).1 θ) * z j := by
    simp [c, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hnodescent : ¬ ∃ z : EuclideanSpace ℝ (Fin D),
      (∀ i ∈ active, inner ℝ (row i) z ≥ 0) ∧ inner ℝ c z < 0 := by
    rintro ⟨z, hz, hcz⟩
    let d : Theta E → ℝ := fun θ => ∑ j, z j * monomial E (e j).1 θ
    have hdspan : d ∈ observableSpan E r := by
      change (fun θ => ∑ j, z j * monomial E (e j).1 θ) ∈ observableSpan E r
      have hs : (∑ j, z j • monomial E (e j).1) ∈ observableSpan E r := by
        exact Submodule.sum_mem _ fun j _ => (observableSpan E r).smul_mem (z j)
          (Submodule.subset_span ⟨(e j).1, (e j).2.1, (e j).2.2, rfl⟩)
      convert hs using 1
      ext θ
      simp [smul_eq_mul]
    have hdnonneg : ∀ θ, b θ = trueVarianceFn E θ → 0 ≤ d θ := by
      intro θ hact
      let i := et.symm θ
      have himem : i.1 ∈ active := by
        simp [active, i.isLt, show et i = θ from et.apply_symm_apply θ, hact]
      have hi := hz i himem
      rw [hinner_row] at hi
      simpa [d, show et i = θ from et.apply_symm_apply θ, mul_comm] using hi
    have hinactive : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ θ,
        b θ ≠ trueVarianceFn E θ → trueVarianceFn E θ < b θ + t * d θ := by
      have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ θ ∈ (Finset.univ : Finset (Theta E)),
          b θ ≠ trueVarianceFn E θ → trueVarianceFn E θ < b θ + t * d θ := by
        apply (Filter.eventually_all_finset (Finset.univ : Finset (Theta E))).2
        intro θ _
        by_cases hne : b θ ≠ trueVarianceFn E θ
        · have hlt : trueVarianceFn E θ < b θ := lt_of_le_of_ne (hb.2 θ) hne.symm
          filter_upwards [(continuousAt_const.eventually_lt
            (show ContinuousAt (fun t : ℝ => b θ + t * d θ) 0 by fun_prop) (by simpa using hlt))]
          intro t ht _
          exact ht
        · exact Filter.Eventually.of_forall fun _ h => (hne h).elim
      simpa only [Finset.mem_univ, forall_const] using hall
    have hmem : {t : ℝ | ∀ θ,
        b θ ≠ trueVarianceFn E θ → trueVarianceFn E θ < b θ + t * d θ} ∈
        𝓝 (0 : ℝ) := hinactive
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
    let t : ℝ := ε / 2
    have htpos : 0 < t := div_pos hε (by norm_num)
    have htmem := hball (show t ∈ Metric.ball (0 : ℝ) ε by
      rw [Metric.mem_ball, Real.dist_eq]
      simp [t, abs_of_pos htpos, hε])
    have hbd : b + t • d ∈ conservativeCone E r := by
      change b ∈ observableSpan E r ∧ (∀ θ, trueVarianceFn E θ ≤ b θ) at hb
      change b + t • d ∈ observableSpan E r ∧
        (∀ θ, trueVarianceFn E θ ≤ (b + t • d) θ)
      refine ⟨(observableSpan E r).add_mem hb.1 ((observableSpan E r).smul_mem t hdspan), ?_⟩
      intro θ
      by_cases hact : b θ = trueVarianceFn E θ
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [← hact]
        exact le_add_of_nonneg_right (mul_nonneg htpos.le (hdnonneg θ hact))
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (htmem θ hact).le
    have hobjd : (∑ θ, q.1 θ * d θ) = inner ℝ c z := by
      rw [hinner_c]
      simp only [d, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro θ _
      ring
    have hlower : optValue E q r ≤ ∑ θ, q.1 θ * (b + t • d) θ := by
      unfold optValue
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro y ⟨u, hu, rfl⟩
        have hf : ∀ θ, 0 ≤ trueVarianceFn E θ := by
          intro θ
          rw [designVarianceFn_eq_Var]
          unfold Causalean.Experimentation.DesignBased.FiniteDesign.Var
            Causalean.Experimentation.DesignBased.FiniteDesign.E
          exact Finset.sum_nonneg fun z _ => mul_nonneg (E.design.p_nonneg z) (sq_nonneg _)
        exact Finset.sum_nonneg fun θ _ => mul_nonneg (q.2.1 θ).le ((hf θ).trans (hu.2 θ))
      · exact ⟨b + t • d, hbd, rfl⟩
    rw [← hbopt] at hlower
    have hadd : (∑ θ, q.1 θ * (b + t • d) θ) =
        (∑ θ, q.1 θ * b θ) + t * ∑ θ, q.1 θ * d θ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro θ _
      ring
    rw [hadd, hobjd] at hlower
    have htneg : t * inner ℝ c z < 0 := mul_neg_of_pos_of_neg htpos hcz
    linarith
  have hfark := (Farkas (n := D) (a := fun _ => 0) (b := row) (c := c)
    (τ := ∅) (σ := active)).2 (by simpa using hnodescent)
  obtain ⟨lam, mu, hmu_nonneg, hc⟩ := hfark
  let muN : ℕ → ℝ := fun i => if hi : i ∈ active then mu ⟨i, hi⟩ else 0
  let μ : Theta E → ℝ := fun θ => muN (et.symm θ)
  let er : {i // i ∈ Finset.range N} ≃ Fin N :=
    { toFun := fun i => ⟨i, Finset.mem_range.mp i.2⟩
      invFun := fun i => ⟨i, Finset.mem_range.mpr i.isLt⟩
      left_inv := fun i => by ext; rfl
      right_inv := fun i => by ext; rfl }
  have hcmom : ∀ j, (∑ θ, q.1 θ * monomial E (e j).1 θ) =
      ∑ θ, μ θ * monomial E (e j).1 θ := by
    intro j
    have hj' : (∑ θ, q.1 θ * monomial E (e j).1 θ) =
        ∑ i : {i // i ∈ active}, mu i * (row i.1) j := by
      have hj := congrArg (fun v : EuclideanSpace ℝ (Fin D) => v j) hc
      have hj0 : c j = ∑ i : {i // i ∈ active}, (mu i • row i.1) j := by
        simpa using hj
      rw [show c j = ∑ θ, q.1 θ * monomial E (e j).1 θ by rfl] at hj0
      calc
        _ = ∑ i : {i // i ∈ active}, (mu i • row i.1) j := hj0
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          simp [smul_eq_mul]
    calc
      _ = ∑ i : {i // i ∈ active}, mu i * (row i.1) j := hj'
      _ = ∑ i ∈ active, muN i * (row i) j := by
        rw [← Finset.sum_attach active, Finset.attach_eq_univ]
        apply Finset.sum_congr rfl
        intro i _
        rw [show muN i.1 = mu i by simp only [muN, dif_pos i.2]]
      _ = ∑ i ∈ Finset.range N, muN i * (row i) j := by
        apply Finset.sum_subset
        · intro i hi
          have hi' : i ∈ Finset.range N ∧
              (if h : i < N then b (et ⟨i, h⟩) = trueVarianceFn E (et ⟨i, h⟩) else False) := by
            simpa only [active, Finset.mem_filter] using hi
          exact hi'.1
        · intro i hir hia
          rw [show muN i = 0 by simp only [muN, dif_neg hia], zero_mul]
      _ = ∑ i : {i // i ∈ Finset.range N}, muN i.1 * (row i.1) j := by
        rw [← Finset.sum_attach (Finset.range N), Finset.attach_eq_univ]
      _ = ∑ i : Fin N, muN i * monomial E (e j).1 (et i) := by
        apply Fintype.sum_equiv er
        intro i
        have hi : i.1 < N := Finset.mem_range.mp i.2
        change muN i.1 * (row i.1) j = muN (er i) * monomial E (e j).1 (et (er i))
        simp only [er]
        rw [show row i.1 = WithLp.toLp 2 (fun k => monomial E (e k).1
          (et ⟨i.1, hi⟩)) by simp only [row, dif_pos hi]]
        rfl
      _ = _ := Fintype.sum_equiv et _ _ (fun i => by simp [μ])
  have hμ : μ ∈ degreeDualMarginSet E q r := by
    refine ⟨?_, ?_⟩
    · intro θ
      by_cases hi : (et.symm θ).1 ∈ active
      · simpa [μ, muN, hi] using hmu_nonneg ⟨(et.symm θ).1, hi⟩
      · simp [μ, muN, hi]
    · intro S hS hdeg
      let j := e.symm ⟨S, hS, hdeg⟩
      have := hcmom j
      simpa [j] using this.symm
  have hdualval : (∑ θ, μ θ * trueVarianceFn E θ) = optValue E q r := by
    rw [← hbopt]
    have hgap : ∑ θ, μ θ * b θ = ∑ θ, q.1 θ * b θ := by
      simp_rw [hrepr]
      calc
        (∑ θ, μ θ * ∑ j, beta E b (e j).1 * monomial E (e j).1 θ) =
            ∑ j, beta E b (e j).1 * ∑ θ, μ θ * monomial E (e j).1 θ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro θ _
          ring
        _ = ∑ j, beta E b (e j).1 * ∑ θ, q.1 θ * monomial E (e j).1 θ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hcmom j]
        _ = ∑ θ, q.1 θ * ∑ j, beta E b (e j).1 * monomial E (e j).1 θ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro θ _
          apply Finset.sum_congr rfl
          intro j _
          ring
    calc
      (∑ θ, μ θ * trueVarianceFn E θ) = ∑ θ, μ θ * b θ := by
        apply Finset.sum_congr rfl
        intro θ _
        by_cases hi : (et.symm θ).1 ∈ active
        · have hact := hi
          simp only [active, Finset.mem_filter] at hact
          have hlt : (et.symm θ).1 < N := Finset.mem_range.mp hact.1
          have heq : b θ = trueVarianceFn E θ := by
            have := hact.2
            simp only [dif_pos hlt] at this
            simpa only [et.apply_symm_apply] using this
          rw [heq]
        · have hz : μ θ = 0 := by simp only [μ, muN, dif_neg hi]
          rw [hz, zero_mul, zero_mul]
      _ = _ := hgap
  refine ⟨?_, ⟨μ, hμ, hdualval⟩⟩
  apply le_antisymm
  · rw [← hdualval]
    apply le_csSup
    · refine ⟨∑ θ, q.1 θ * b θ, ?_⟩
      rintro y ⟨ν, hν, rfl⟩
      exact observable_degree_weak_duality E q r hb hν
    · exact ⟨μ, hμ, rfl⟩
  · apply csSup_le
    · exact ⟨_, μ, hμ, rfl⟩
    · rintro y ⟨ν, hν, rfl⟩
      exact (observable_degree_weak_duality E q r hb hν).trans_eq hbopt

/-- [The unrestricted primal optimum equals the supremum of the full dual objective, and a dual optimizer attains that value](goal). -/
-- @node: observable_strong_duality
lemma observable_strong_duality (E : Setup) (q : FullSupportObjective E) :
    optValue E q ⊤ = sSup ((fun μ => ∑ θ, μ θ * trueVarianceFn E θ) ''
      dualMarginSet E q) ∧
    ∃ μ ∈ dualMarginSet E q,
      (∑ θ, μ θ * trueVarianceFn E θ) = optValue E q ⊤ := by
  have hsets : degreeDualMarginSet E q ⊤ = dualMarginSet E q := by
    ext μ
    simp [degreeDualMarginSet, dualMarginSet]
  simpa only [hsets] using observable_degree_strong_duality E q ⊤

end CausalSmith.Experimentation.BinaryTruthbound
