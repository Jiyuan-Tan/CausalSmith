import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.TDualCompleteClass
import Causalean.Mathlib.Optimization.RationalLP

/-! Rational primal-dual and assignment-table certificates. -/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- A real number represented by a rational number. -/
def RationalReal (x : ℝ) : Prop := ∃ r : ℚ, (r : ℝ) = x

/-- Pointwise rational-valued function. -/
def RationalValued {A : Type*} (f : A → ℝ) : Prop := ∀ x, RationalReal (f x)

-- @node: prop:rational-certificates
set_option maxHeartbeats 2000000 in
/-- For [an experiment and objective weights](hyp:E,q) whose [assignment probabilities](hyp:hp), [scores](hyp:hv), and [objective weights](hyp:hq) are rational-valued and whose [objective has full support](hyp:hfull), [there exist rational primal coefficients, dual weights, and assignment tables that are feasible, have equal objectives, satisfy complementary slackness, and implement the primal bound](goal). -/
theorem rational_primal_dual_certificates (E : Setup) (q : Theta E → ℝ)
    (hp : ∀ z, RationalReal (E.design.p z))
    (hv : ∀ z i, RationalReal (E.v z i))
    (hq : RationalValued q) (hfull : FullSupportWeight E q) :
    ∃ (a : Finset (Fin E.K) → ℝ) (μ : Theta E → ℝ) (g : AssignmentRule E),
      RationalValued a ∧ RationalValued μ ∧ (∀ z, RationalValued (g z)) ∧
      (fun θ => ∑ S, a S * monomial E S θ) ∈ unrestrictedConservativeCone E ∧
      μ ∈ dualMarginSet E ⟨q, hfull⟩ ∧
      boundObjective E ⟨q, hfull⟩ (fun θ => ∑ S, a S * monomial E S θ) =
        dualObjective E μ ∧
      (∀ θ, 0 < μ θ →
        (∑ S, a S * monomial E S θ) = trueVarianceFn E θ) ∧
      expectedRule E g = fun θ => ∑ S, a S * monomial E S θ := by
  classical
  let pQ : E.Omega → ℚ := fun z => Classical.choose (hp z)
  let vQ : E.Omega → Fin E.K → ℚ := fun z i => Classical.choose (hv z i)
  let qQ : Theta E → ℚ := fun θ => Classical.choose (hq θ)
  have hpQ (z) : (pQ z : ℝ) = E.design.p z := Classical.choose_spec (hp z)
  have hvQ (z i) : (vQ z i : ℝ) = E.v z i := Classical.choose_spec (hv z i)
  have hqQ (θ) : (qQ θ : ℝ) = q θ := Classical.choose_spec (hq θ)
  let cQ : Fin E.K → ℚ := fun i => ∑ z, pQ z * vQ z i
  let AQ : Fin E.K → Fin E.K → ℚ := fun i k =>
    (∑ z, pQ z * (vQ z i * vQ z k)) - cQ i * cQ k
  let fQ : Theta E → ℚ := fun θ =>
    ∑ i, ∑ k, AQ i k * (θ i).val * (θ k).val
  have hcQ (i) : (cQ i : ℝ) = targetCoeff E i := by
    simp only [cQ, targetCoeff, Causalean.Experimentation.DesignBased.FiniteDesign.E,
      Rat.cast_sum, Rat.cast_mul, hpQ, hvQ]
  have hAQ (i k) : (AQ i k : ℝ) = varianceMatrix E i k := by
    simp only [AQ, varianceMatrix, Causalean.Experimentation.DesignBased.FiniteDesign.E,
      Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, hpQ, hvQ, hcQ]
  have hfQ (θ) : (fQ θ : ℝ) = trueVarianceFn E θ := by
    simp only [fQ, trueVarianceFn, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, hAQ]
  have hfQ_nonneg (θ) : 0 ≤ fQ θ := by
    apply (Rat.cast_nonneg (K := ℝ)).mp
    rw [hfQ, designVarianceFn_eq_Var]
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.Var
      Causalean.Experimentation.DesignBased.FiniteDesign.E
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (E.design.p_nonneg z) (sq_nonneg _)
  let Obs := {S : Finset (Fin E.K) // S ∈ observableComplex E}
  let e : Obs ≃ Fin (Fintype.card Obs) := Fintype.equivFin Obs
  let monoQ (S : Finset (Fin E.K)) (θ : Theta E) : ℚ :=
    ∏ i ∈ S, (θ i).val
  have hmonoQ (S) (θ) : (monoQ S θ : ℝ) = monomial E S θ := by
    simp only [monoQ, monomial, Rat.cast_prod, Rat.cast_natCast]
  let P : Causalean.Mathlib.Optimization.RationalLP.Program (Theta E)
      (Fintype.card Obs) := {
    A := fun θ j => -monoQ (e.symm j).1 θ
    b := fun θ => -fQ θ
    c := fun j => ∑ θ, qQ θ * monoQ (e.symm j).1 θ }
  let boundQ (x : Fin (Fintype.card Obs) → ℚ) (θ : Theta E) : ℚ :=
    ∑ j, x j * monoQ (e.symm j).1 θ
  have hfeas_iff (x) : P.PrimalFeasible x ↔ ∀ θ, fQ θ ≤ boundQ x θ := by
    constructor
    · intro hx θ
      have h := hx θ
      change (∑ j, (-monoQ (e.symm j).1 θ) * x j) ≤ -fQ θ at h
      have heq : (∑ j, (-monoQ (e.symm j).1 θ) * x j) = -boundQ x θ := by
        change (∑ j, (-monoQ (e.symm j).1 θ) * x j) =
          -(∑ j, x j * monoQ (e.symm j).1 θ)
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [heq] at h
      linarith
    · intro hx θ
      have h := hx θ
      change (∑ j, (-monoQ (e.symm j).1 θ) * x j) ≤ -fQ θ
      rw [show (∑ j, (-monoQ (e.symm j).1 θ) * x j) = -boundQ x θ by
        change (∑ j, (-monoQ (e.symm j).1 θ) * x j) =
          -(∑ j, x j * monoQ (e.symm j).1 θ)
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring]
      linarith
  have hobj (x) : P.objective x = ∑ θ, qQ θ * boundQ x θ := by
    unfold Causalean.Mathlib.Optimization.RationalLP.Program.objective
      Causalean.Mathlib.Optimization.RationalLP.dot
    simp only [P, boundQ, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro θ _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro η _
    ring
  have hqQ_nonneg (θ) : 0 ≤ qQ θ := by
    apply (Rat.cast_nonneg (K := ℝ)).mp
    rw [hqQ]
    exact (hfull.1 θ).le
  have hempty : (∅ : Finset (Fin E.K)) ∈ observableComplex E := by
    letI : Nonempty E.Omega := by
      by_contra hn
      haveI : IsEmpty E.Omega := not_nonempty_iff.mp hn
      simpa using E.design.p_sum
    simp [observableComplex]
  let C : ℚ := ∑ θ, |fQ θ|
  let x₀ : Fin (Fintype.card Obs) → ℚ := fun j =>
    if j = e ⟨∅, hempty⟩ then C else 0
  have hbound_x₀ (θ) : boundQ x₀ θ = C := by
    change (∑ j, x₀ j * monoQ (e.symm j).1 θ) = C
    rw [Finset.sum_eq_single (e ⟨∅, hempty⟩)]
    · simp [x₀, monoQ]
    · intro j _ hj
      simp [x₀, hj]
    · simp
  have hPne : ∃ x, P.PrimalFeasible x := by
    refine ⟨x₀, (hfeas_iff x₀).mpr fun θ => ?_⟩
    rw [hbound_x₀]
    exact (le_abs_self (fQ θ)).trans
      (Finset.single_le_sum (fun η _ => abs_nonneg (fQ η)) (Finset.mem_univ θ))
  have hPbdd : ∃ l : ℚ, ∀ x, P.PrimalFeasible x → l ≤ P.objective x := by
    refine ⟨0, fun x hx => ?_⟩
    rw [hobj]
    exact Finset.sum_nonneg fun θ _ =>
      mul_nonneg (hqQ_nonneg θ) ((hfQ_nonneg θ).trans (((hfeas_iff x).mp hx) θ))
  obtain ⟨xStar, yStar, hxStar, hyStar, hobjEq, _hxOptimal⟩ :=
    Causalean.Mathlib.Optimization.RationalLP.exists_rational_optimal_primal_dual P hPne hPbdd
  let aQ : Finset (Fin E.K) → ℚ := fun S =>
    if hS : S ∈ observableComplex E then xStar (e ⟨S, hS⟩) else 0
  let a : Finset (Fin E.K) → ℝ := fun S => (aQ S : ℝ)
  let μ : Theta E → ℝ := fun θ => (yStar θ : ℝ)
  let g : AssignmentRule E := mobiusImplementation E a
  have ha_rat : RationalValued a := by
    intro S
    by_cases hS : S ∈ observableComplex E
    · exact ⟨aQ S, rfl⟩
    · exact ⟨aQ S, rfl⟩
  have hμ_rat : RationalValued μ := fun θ => ⟨yStar θ, rfl⟩
  have ha_zero : ∀ S, S ∉ observableComplex E → a S = 0 := by
    intro S hS
    simp [a, aQ, hS]
  have hsum_a (θ) : (∑ S, a S * monomial E S θ) = (boundQ xStar θ : ℚ) := by
    have hfilter : (∑ S, aQ S * monoQ S θ) =
        (∑ S ∈ Finset.univ.filter (fun S => S ∈ observableComplex E),
          aQ S * monoQ S θ) := by
      exact (Finset.sum_subset (s₁ := Finset.univ.filter
        (fun S => S ∈ observableComplex E)) (s₂ := Finset.univ) (by simp) (by
          intro S _ hS
          have hn : S ∉ observableComplex E := by simpa using hS
          simp [aQ, hn])).symm
    have hsub : (∑ S ∈ Finset.univ.filter (fun S => S ∈ observableComplex E),
          aQ S * monoQ S θ) =
        ∑ S : Obs, aQ S.1 * monoQ S.1 θ := by
      exact Finset.sum_subtype _ (by simp) _
    have hsub' : (∑ S : Obs, aQ S.1 * monoQ S.1 θ) =
        ∑ S : Obs, xStar (e S) * monoQ S.1 θ := by
      apply Finset.sum_congr rfl
      intro S _
      simp [aQ, S.2]
    have hequiv : (∑ S : Obs, xStar (e S) * monoQ S.1 θ) =
        ∑ j, xStar j * monoQ (e.symm j).1 θ :=
      Fintype.sum_equiv e _ _ (fun S => by simp)
    calc
      (∑ S, a S * monomial E S θ) =
          ((∑ S, aQ S * monoQ S θ : ℚ) : ℝ) := by
            simp only [a, Rat.cast_sum, Rat.cast_mul, hmonoQ]
      _ = (boundQ xStar θ : ℚ) := by rw [hfilter, hsub, hsub', hequiv]
  have hb : (fun θ => ∑ S, a S * monomial E S θ) ∈
      unrestrictedConservativeCone E := by
    constructor
    · exact (observableSpan_iff_beta_vanishes E _).2 fun S hS => by
        rw [show beta E (fun θ => ∑ T, a T * monomial E T θ) S = a S by
          have hu := boolean_mobius_unique E
            (fun θ => ∑ T, a T * monomial E T θ) a (fun θ => rfl)
          exact (congrFun hu S).symm]
        exact ha_zero S hS
    · intro θ
      change trueVarianceFn E θ ≤ ∑ S, a S * monomial E S θ
      rw [hsum_a θ, ← hfQ θ]
      exact_mod_cast ((hfeas_iff xStar).mp hxStar θ)
  have hμ_nonneg : ∀ θ, 0 ≤ μ θ := by
    intro θ
    change (0 : ℝ) ≤ (yStar θ : ℝ)
    exact_mod_cast hyStar.1 θ
  have hmargin : ∀ S ∈ observableComplex E,
      ∑ θ, μ θ * monomial E S θ = ∑ θ, q θ * monomial E S θ := by
    intro S hS
    have hs := hyStar.2 (e ⟨S, hS⟩)
    simp only [P] at hs
    have hs' := congrArg (fun x : ℚ => (x : ℝ)) hs
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_neg, hqQ, hmonoQ] at hs'
    have hs'' : ∑ θ, (yStar θ : ℝ) * monomial E S θ =
        ∑ θ, q θ * monomial E S θ := by
      calc
        _ = -(∑ θ, (yStar θ : ℝ) * -monomial E S θ) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro θ _
          ring
        _ = -(-∑ θ, q θ * monomial E S θ) := by simpa using congrArg Neg.neg hs'
        _ = _ := by ring
    simpa [μ] using hs''
  have hμ : μ ∈ dualMarginSet E ⟨q, hfull⟩ := ⟨hμ_nonneg, hmargin⟩
  have hobjectives :
      boundObjective E ⟨q, hfull⟩ (fun θ => ∑ S, a S * monomial E S θ) =
        dualObjective E μ := by
    have heq := congrArg (fun x : ℚ => (x : ℝ)) hobjEq
    rw [hobj] at heq
    simp only [Causalean.Mathlib.Optimization.RationalLP.Program.dualObjective,
      P, Rat.cast_sum, Rat.cast_mul, Rat.cast_neg, hqQ, hfQ] at heq
    unfold boundObjective dualObjective
    simp_rw [hsum_a]
    calc
      (∑ θ, q θ * (boundQ xStar θ : ℝ)) =
          -(∑ θ, (yStar θ : ℝ) * -trueVarianceFn E θ) := heq
      _ = ∑ θ, μ θ * trueVarianceFn E θ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro θ _
        simp only [μ]
        ring
  have hslack : ∀ θ, 0 < μ θ →
      (∑ S, a S * monomial E S θ) = trueVarianceFn E θ := by
    intro θ hμpos
    have hgap : ∑ η, μ η *
        ((∑ S, a S * monomial E S η) - trueVarianceFn E η) = 0 := by
      have hμb : (∑ η, μ η * (∑ S, a S * monomial E S η)) =
          ∑ η, q η * (∑ S, a S * monomial E S η) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm, Finset.sum_comm (f := fun x x_1 => q x * (a x_1 * monomial E x_1 x))]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hS : S ∈ observableComplex E
        · rw [show (∑ x, μ x * (a S * monomial E S x)) =
                a S * ∑ x, μ x * monomial E S x by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring,
              show (∑ x, q x * (a S * monomial E S x)) =
                a S * ∑ x, q x * monomial E S x by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring,
              hmargin S hS]
        · simp [ha_zero S hS]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hμb]
      exact sub_eq_zero.mpr hobjectives
    have hterms : ∀ η, 0 ≤ μ η *
        ((∑ S, a S * monomial E S η) - trueVarianceFn E η) := by
      intro η
      exact mul_nonneg (hμ_nonneg η) (sub_nonneg.mpr (hb.2 η))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun η _ => hterms η).mp hgap θ
      (Finset.mem_univ θ)
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hμpos.ne' hzero)
    · exact sub_eq_zero.mp hzero
  have hg_rat : ∀ z, RationalValued (g z) := by
    intro z y
    unfold g mobiusImplementation
    let denQ : Finset (Fin E.K) → ℚ := fun S => ∑ w, if S ⊆ E.O w then pQ w else 0
    let localQ : Finset (Fin E.K) → ℚ := fun S =>
      ∏ i ∈ S, if h : i ∈ E.O z then (y ⟨i, h⟩).val else 0
    have hdenQ (S) : (denQ S : ℝ) = jointObsProb E S := by
      simp only [denQ, jointObsProb,
        Causalean.Experimentation.DesignBased.FiniteDesign.E, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hS : S ⊆ E.O w <;> simp [hS, hpQ]
    have hlocalQ (S) : (localQ S : ℝ) = localMonomial E z y S := by
      simp only [localQ, localMonomial, Rat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : i ∈ E.O z <;> simp [h]
    refine ⟨∑ S ∈ (E.O z).powerset,
      (if hS : S ∈ observableComplex E then xStar (e ⟨S, hS⟩) else 0) /
        denQ S * localQ S, ?_⟩
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div]
    simp_rw [hdenQ, hlocalQ]
    rfl
  refine ⟨a, μ, g, ha_rat, hμ_rat, hg_rat, hb, hμ, hobjectives, hslack, ?_⟩
  exact expectedRule_mobiusImplementation E a ha_zero

end CausalSmith.Experimentation.BinaryTruthbound
