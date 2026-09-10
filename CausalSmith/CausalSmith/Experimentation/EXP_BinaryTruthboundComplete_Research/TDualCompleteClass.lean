import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.FiniteConeDuality
import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TObservableMobius
import Mathlib.Analysis.LocallyConvex.Separation

/-! Strong duality, complementary slackness, and the Pareto complete class. -/

open scoped BigOperators
open Finset Set
open Filter Topology

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- Weighted objective of a Boolean bound. -/
def boundObjective (E : Setup) (q : FullSupportObjective E) (b : Theta E → ℝ) : ℝ :=
  ∑ θ, q.1 θ * b θ

/-- Dual objective. -/
def dualObjective (E : Setup) (μ : Theta E → ℝ) : ℝ :=
  ∑ θ, μ θ * trueVarianceFn E θ

/-- [A Pareto-admissible bound](hyp:hb) [is supported by a strictly positive schedule objective at the unrestricted optimum](goal). -/
-- @node: paretoAdmissible_supported_fullSupport
lemma paretoAdmissible_supported_fullSupport (E : Setup) {b : Theta E → ℝ}
    (hb : ParetoAdmissible E b) :
    ∃ q : FullSupportObjective E,
      boundObjective E q b = optValue E q ⊤ := by
  classical
  let active : Finset (Theta E) := Finset.univ.filter fun θ =>
    b θ = trueVarianceFn E θ
  let T : Set (Theta E → ℝ) :=
    {d | d ∈ observableSpan E ⊤ ∧ ∀ θ ∈ active, 0 ≤ d θ}
  let generators : Set (Theta E → ℝ) :=
    Set.range fun θ => Pi.single θ (-1 : ℝ)
  let N : Set (Theta E → ℝ) := convexHull ℝ generators
  let P : Set (Theta E → ℝ) :=
    {d | (∀ θ, d θ ≤ 0) ∧ ∑ θ, d θ = -1}
  have hPconvex : Convex ℝ P := by
    intro x hx y hy s t hs ht hst
    refine ⟨?_, ?_⟩
    · intro θ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs (hx.1 θ))
        (mul_nonpos_of_nonneg_of_nonpos ht (hy.1 θ))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
      linarith
  have hgenerators_P : generators ⊆ P := by
    rintro d ⟨θ, rfl⟩
    constructor
    · intro η
      by_cases h : η = θ
      · subst η
        simp
      · simp [Pi.single, h]
    · simp
  have hN_P : N ⊆ P := convexHull_min hgenerators_P hPconvex
  have hNconvex : Convex ℝ N := convex_convexHull ℝ generators
  have hNcompact : IsCompact N :=
    (Set.finite_range fun θ : Theta E =>
      (Pi.single θ (-1 : ℝ) : Theta E → ℝ)).isCompact_convexHull ℝ
  have hTclosed : IsClosed T := by
    have hspan : IsClosed (observableSpan E ⊤ : Set (Theta E → ℝ)) :=
      (observableSpan E ⊤).closed_of_finiteDimensional
    have hcoords : IsClosed {d : Theta E → ℝ | ∀ θ ∈ active, 0 ≤ d θ} := by
      rw [show {d : Theta E → ℝ | ∀ θ ∈ active, 0 ≤ d θ} =
          ⋂ θ, ⋂ (_h : θ ∈ active), {d : Theta E → ℝ | 0 ≤ d θ} by
        ext d
        simp]
      exact isClosed_iInter fun θ => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_apply θ)
    exact hspan.inter hcoords
  have hTconvex : Convex ℝ T := by
    intro x hx y hy s t hs ht hst
    refine ⟨(observableSpan E ⊤).convex hx.1 hy.1 hs ht hst, ?_⟩
    intro θ hθ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (hx.2 θ hθ)) (mul_nonneg ht (hy.2 θ hθ))
  have hTN : Disjoint T N := by
    rw [Set.disjoint_left]
    intro d hdT hdN
    have hdP := hN_P hdN
    have hinactive : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ θ,
        b θ ≠ trueVarianceFn E θ → trueVarianceFn E θ < b θ + t * d θ := by
      have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ θ ∈ (Finset.univ : Finset (Theta E)),
          b θ ≠ trueVarianceFn E θ → trueVarianceFn E θ < b θ + t * d θ := by
        apply (Filter.eventually_all_finset (Finset.univ : Finset (Theta E))).2
        intro θ _
        by_cases hne : b θ ≠ trueVarianceFn E θ
        · have hlt : trueVarianceFn E θ < b θ :=
            lt_of_le_of_ne (hb.1.2 θ) hne.symm
          filter_upwards [(continuousAt_const.eventually_lt
            (show ContinuousAt (fun t : ℝ => b θ + t * d θ) 0 by fun_prop)
              (by simpa using hlt))]
          intro t ht _
          exact ht
        · exact Filter.Eventually.of_forall fun _ h => (hne h).elim
      simpa only [Finset.mem_univ, forall_const] using hall
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hinactive
    let t : ℝ := ε / 2
    have htpos : 0 < t := div_pos hε (by norm_num)
    have htmem := hball (show t ∈ Metric.ball (0 : ℝ) ε by
      rw [Metric.mem_ball, Real.dist_eq]
      simp [t, abs_of_pos htpos, hε])
    let b' : Theta E → ℝ := b + t • d
    have hb' : b' ∈ unrestrictedConservativeCone E := by
      refine ⟨(observableSpan E ⊤).add_mem hb.1.1
          ((observableSpan E ⊤).smul_mem t hdT.1), ?_⟩
      intro θ
      by_cases hact : b θ = trueVarianceFn E θ
      · have hθmem : θ ∈ active := by simp [active, hact]
        change trueVarianceFn E θ ≤ b θ + t * d θ
        rw [← hact]
        exact le_add_of_nonneg_right (mul_nonneg htpos.le (hdT.2 θ hθmem))
      · change trueVarianceFn E θ ≤ b θ + t * d θ
        exact (htmem θ hact).le
    have hb'le : ∀ θ, b' θ ≤ b θ := by
      intro θ
      change b θ + t * d θ ≤ b θ
      have htd : t * d θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le (hdP.1 θ)
      linarith
    have hdneg : ∃ θ, d θ < 0 := by
      by_contra h
      push Not at h
      have hd0 : d = 0 := by
        funext θ
        exact le_antisymm (hdP.1 θ) (h θ)
      have hsum0 : (∑ θ, d θ) = 0 := by simp [hd0]
      linarith [hdP.2]
    have hb'strict : ∃ θ, b' θ < b θ := by
      obtain ⟨θ, hθ⟩ := hdneg
      exact ⟨θ, by
        change b θ + t * d θ < b θ
        have htd : t * d θ < 0 := mul_neg_of_pos_of_neg htpos hθ
        linarith⟩
    exact hb.2 ⟨b', hb', hb'le, hb'strict⟩
  obtain ⟨f, u, v, hfT, huv, hfN⟩ :=
    geometric_hahn_banach_closed_compact hTconvex hTclosed hNconvex hNcompact hTN
  have hzeroT : (0 : Theta E → ℝ) ∈ T := by
    refine ⟨(observableSpan E ⊤).zero_mem, ?_⟩
    simp
  have hu_pos : 0 < u := by simpa using hfT 0 hzeroT
  let w : Theta E → ℝ := fun θ => -f (Pi.single θ (1 : ℝ))
  have hw_pos : ∀ θ, 0 < w θ := by
    intro θ
    have hgen : Pi.single θ (-1 : ℝ) ∈ N :=
      subset_convexHull ℝ generators ⟨θ, rfl⟩
    have := lt_trans hu_pos (lt_trans huv (hfN _ hgen))
    have hsingle : (Pi.single θ (-1 : ℝ) : Theta E → ℝ) =
        -Pi.single θ (1 : ℝ) := by
      ext η
      by_cases h : η = θ <;> simp [Pi.single, h]
    rw [hsingle, map_neg] at this
    simpa [w] using this
  let W : ℝ := ∑ θ, w θ
  have hW_pos : 0 < W := Finset.sum_pos (fun θ _ => hw_pos θ) Finset.univ_nonempty
  let qfun : Theta E → ℝ := fun θ => w θ / W
  have hqweight : FullSupportWeight E qfun := by
    constructor
    · intro θ
      exact div_pos (hw_pos θ) hW_pos
    · simp only [qfun, ← Finset.sum_div, W]
      exact div_self hW_pos.ne'
  let q : FullSupportObjective E := ⟨qfun, hqweight⟩
  have hf_nonpos : ∀ d ∈ T, f d ≤ 0 := by
    intro d hd
    by_contra hfd
    have hfdpos : 0 < f d := lt_of_not_ge hfd
    let c : ℝ := (u + 1) / f d
    have hcpos : 0 < c := div_pos (by linarith) hfdpos
    have hcdT : c • d ∈ T := by
      refine ⟨(observableSpan E ⊤).smul_mem c hd.1, ?_⟩
      intro θ hθ
      simpa only [Pi.smul_apply, smul_eq_mul] using mul_nonneg hcpos.le (hd.2 θ hθ)
    have hlt := hfT (c • d) hcdT
    simp only [map_smul, smul_eq_mul, c] at hlt
    field_simp [hfdpos.ne'] at hlt
    linarith
  have hfrepr (d : Theta E → ℝ) : f d = -∑ θ, w θ * d θ := by
    have hdecomp : d = ∑ θ, Pi.single θ (d θ) := by
      funext η
      simp
    calc
      f d = f (∑ θ, Pi.single θ (d θ)) := congrArg f hdecomp
      _ = ∑ θ, f (Pi.single θ (d θ)) := by simp
      _ = ∑ θ, -(w θ * d θ) := by
        apply Finset.sum_congr rfl
        intro θ _
        rw [show Pi.single θ (d θ) = d θ • Pi.single θ (1 : ℝ) by
          ext η
          by_cases h : η = θ <;> simp [Pi.single, h]]
        simp only [map_smul, smul_eq_mul, w]
        ring
      _ = -∑ θ, w θ * d θ := by rw [← Finset.sum_neg_distrib]
  have hsupport : ∀ b' ∈ unrestrictedConservativeCone E,
      boundObjective E q b ≤ boundObjective E q b' := by
    intro b' hb'
    let d : Theta E → ℝ := b' - b
    have hdT : d ∈ T := by
      refine ⟨(observableSpan E ⊤).sub_mem hb'.1 hb.1.1, ?_⟩
      intro θ hθ
      have hactive : b θ = trueVarianceFn E θ := by simpa [active] using hθ
      change 0 ≤ b' θ - b θ
      rw [hactive]
      exact sub_nonneg.mpr (hb'.2 θ)
    have hfd := hf_nonpos d hdT
    rw [hfrepr] at hfd
    have hsum : 0 ≤ ∑ θ, w θ * (b' θ - b θ) := neg_nonpos.mp hfd
    have hraw : (∑ θ, w θ * b θ) ≤ ∑ θ, w θ * b' θ := by
      have hdiff : (∑ θ, w θ * (b' θ - b θ)) =
          (∑ θ, w θ * b' θ) - ∑ θ, w θ * b θ := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hdiff] at hsum
      exact sub_nonneg.mp hsum
    unfold boundObjective
    change (∑ θ, qfun θ * b θ) ≤ ∑ θ, qfun θ * b' θ
    have hWinv : 0 ≤ W⁻¹ := inv_nonneg.mpr hW_pos.le
    calc
      (∑ θ, qfun θ * b θ) = W⁻¹ * ∑ θ, w θ * b θ := by
        simp only [qfun, div_eq_mul_inv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro θ _
        ring
      _ ≤ W⁻¹ * ∑ θ, w θ * b' θ := mul_le_mul_of_nonneg_left hraw hWinv
      _ = ∑ θ, qfun θ * b' θ := by
        simp only [qfun, div_eq_mul_inv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro θ _
        ring
  refine ⟨q, ?_⟩
  apply le_antisymm
  · apply le_csInf
    · exact ⟨boundObjective E q b, ⟨b, hb.1, rfl⟩⟩
    · rintro y ⟨b', hb', rfl⟩
      exact hsupport b' hb'
  · unfold optValue
    apply csInf_le
    · exact ⟨boundObjective E q b, by
        rintro y ⟨b', hb', rfl⟩
        exact hsupport b' hb'⟩
    · exact ⟨b, hb.1, rfl⟩

/-- [A dual weight matching all observable margins](hyp:hμ) and [a function in the observable span](hyp:hu) [have the same expectation under the dual and objective weights](goal). -/
-- @node: dualMargin_expectation_eq
lemma dualMargin_expectation_eq (E : Setup) (q : FullSupportObjective E)
    (r : WithTop ℕ) {μ u : Theta E → ℝ} (hμ : μ ∈ dualMarginSet E q)
    (hu : u ∈ observableSpan E r) :
    (∑ θ, μ θ * u θ) = ∑ θ, q.1 θ * u θ := by
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

/-- For [an experiment](hyp:E), [every full-support objective has an attained unrestricted primal optimum equal to an attained dual optimum; complementary slackness characterizes simultaneous optimizers, every primal optimizer is Pareto admissible, and every Pareto-admissible bound is optimal for some full-support objective](goal). -/
-- @node: thm:dual-complete-class
theorem optValue_eq_dual_and_paretoCompleteClass (E : Setup) :
    ∀ q : FullSupportObjective E,
      (∃ b ∈ unrestrictedConservativeCone E, boundObjective E q b = optValue E q ⊤) ∧
      optValue E q ⊤ = sSup (dualObjective E '' dualMarginSet E q) ∧
      (∃ μ ∈ dualMarginSet E q, dualObjective E μ = optValue E q ⊤) ∧
      (∀ b μ,
        b ∈ unrestrictedConservativeCone E → μ ∈ dualMarginSet E q →
        (boundObjective E q b = optValue E q ⊤ ∧
          dualObjective E μ = optValue E q ⊤ ↔
          ∀ θ, 0 < μ θ → b θ = trueVarianceFn E θ)) ∧
      (∀ b, b ∈ unrestrictedConservativeCone E →
        boundObjective E q b = optValue E q ⊤ → ParetoAdmissible E b) ∧
      (∀ b, ParetoAdmissible E b →
        ∃ q' : FullSupportObjective E,
          boundObjective E q' b = optValue E q' ⊤) := by
  intro q
  obtain ⟨bopt, hbopt, hbopt_value⟩ := observable_primal_attained E q ⊤
  obtain ⟨hdual_value, μopt, hμopt, hμopt_value⟩ := observable_strong_duality E q
  refine ⟨⟨bopt, hbopt, hbopt_value⟩, hdual_value,
    ⟨μopt, hμopt, hμopt_value⟩, ?_, ?_, ?_⟩
  · intro b μ hb hμ
    have hmargin := dualMargin_expectation_eq E q ⊤ hμ hb.1
    constructor
    · rintro ⟨hbval, hμval⟩ θ hμθ
      have hgap : (∑ η, μ η * (b η - trueVarianceFn E η)) = 0 := by
        calc
          (∑ η, μ η * (b η - trueVarianceFn E η)) =
              (∑ η, μ η * b η) - ∑ η, μ η * trueVarianceFn E η := by
                simp only [mul_sub, Finset.sum_sub_distrib]
          _ = boundObjective E q b - dualObjective E μ := by
                rw [hmargin]
                rfl
          _ = 0 := by rw [hbval, hμval, sub_self]
      have hterm_nonneg : ∀ η, 0 ≤ μ η * (b η - trueVarianceFn E η) := by
        intro η
        exact mul_nonneg (hμ.1 η) (sub_nonneg.mpr (hb.2 η))
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Theta E)))
        (fun η _ => hterm_nonneg η)).mp hgap θ (Finset.mem_univ θ)
      have hslack : b θ - trueVarianceFn E θ = 0 :=
        (mul_eq_zero.mp hzero).resolve_left hμθ.ne'
      linarith
    · intro hcontact
      have hcontact_sum : dualObjective E μ = boundObjective E q b := by
        unfold dualObjective boundObjective
        rw [← hmargin]
        apply Finset.sum_congr rfl
        intro θ _
        by_cases hμzero : μ θ = 0
        · simp [hμzero]
        · have hμpos : 0 < μ θ := lt_of_le_of_ne (hμ.1 θ) (Ne.symm hμzero)
          rw [hcontact θ hμpos]
      have hopt_le_primal : optValue E q ⊤ ≤ boundObjective E q b := by
        rw [← hμopt_value]
        exact observable_weak_duality E q ⊤ hb hμopt
      have hdual_le_opt : dualObjective E μ ≤ optValue E q ⊤ := by
        rw [← hbopt_value]
        exact observable_weak_duality E q ⊤ hbopt hμ
      constructor <;> linarith
  · intro b hb hbval
    refine ⟨hb, ?_⟩
    rintro ⟨b', hb', hb'le, θ, hθlt⟩
    have hobjlt : boundObjective E q b' < boundObjective E q b := by
      unfold boundObjective
      apply Finset.sum_lt_sum
      · intro η _
        exact mul_le_mul_of_nonneg_left (hb'le η) (q.2.1 η).le
      · exact ⟨θ, Finset.mem_univ θ,
          mul_lt_mul_of_pos_left hθlt (q.2.1 θ)⟩
    have hopt_le : optValue E q ⊤ ≤ boundObjective E q b' := by
      rw [← hμopt_value]
      exact observable_weak_duality E q ⊤ hb' hμopt
    linarith
  · intro b hb
    exact paretoAdmissible_supported_fullSupport E hb

end CausalSmith.Experimentation.BinaryTruthbound
