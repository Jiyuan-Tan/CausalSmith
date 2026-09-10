import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Helpers.BooleanMobius

/-! Odd-degree collapse under outcome-complement symmetry. -/

namespace CausalSmith.Experimentation.BinaryTruthbound

open scoped BigOperators
open Finset Set

/-- For [an experiment and binary schedule](hyp:E,θ), [complementing twice returns the original schedule](goal). -/
-- @node: complement_involutive
lemma complement_involutive (E : Setup) (θ : Theta E) :
    complement E (complement E θ) = θ := by
  funext i
  apply Fin.ext
  simp only [complement]
  have hi : (θ i : ℕ) < 2 := (θ i).isLt
  omega

/-- For [an experiment](hyp:E), [the complement equivalence](goal) maps every binary schedule to its coordinatewise complement. -/
-- @node: complementEquiv
def complementEquiv (E : Setup) : Theta E ≃ Theta E where
  toFun := complement E
  invFun := complement E
  left_inv := complement_involutive E
  right_inv := complement_involutive E

/-- If [one degree bound is no larger than another](hyp:hrs), then [the smaller observable span is contained in the larger one](goal). -/
-- @node: observableSpan_mono_degree
lemma observableSpan_mono_degree (E : Setup) {r s : WithTop ℕ} (hrs : r ≤ s) :
    observableSpan E r ≤ observableSpan E s := by
  unfold observableSpan
  apply Submodule.span_mono
  rintro u ⟨S, hS, hSr, rfl⟩
  exact ⟨S, hS, hSr.trans hrs, rfl⟩

/-- If [a function is in the observable span](hyp:hb), then [composing it with schedule complementation remains in that span](goal). -/
-- @node: complement_preserves_observableSpan
lemma complement_preserves_observableSpan (E : Setup) (r : WithTop ℕ)
    {b : Theta E → ℝ} (hb : b ∈ observableSpan E r) :
    (fun θ => b (complement E θ)) ∈ observableSpan E r := by
  unfold observableSpan at hb
  refine Submodule.span_induction
    (p := fun b _ => (fun θ => b (complement E θ)) ∈ observableSpan E r) ?_ ?_ ?_ ?_ hb
  · intro u hu
    rcases hu with ⟨R, hR, hdeg, rfl⟩
    rw [observableSpan_iff_beta_vanishes_degree]
    intro T hT
    rw [beta_complement_monomial]
    by_cases hTR : T ⊆ R
    · rw [if_pos hTR]
      rcases hT with hnot | hnot
      · exact (hnot (observableComplex_downward_closed E hR hTR)).elim
      · exact (hnot (((WithTop.coe_le_coe).mpr
          (Finset.card_le_card hTR)).trans hdeg)).elim
    · simp [hTR]
  · change (0 : Theta E → ℝ) ∈ observableSpan E r
    exact (observableSpan E r).zero_mem
  · intro x y hx hy hcx hcy
    change ((fun θ => x (complement E θ)) +
      (fun θ => y (complement E θ))) ∈ observableSpan E r
    exact (observableSpan E r).add_mem hcx hcy
  · intro c x hx hcx
    change c • (fun θ => x (complement E θ)) ∈ observableSpan E r
    exact (observableSpan E r).smul_mem c hcx

/-- If [higher-degree Möbius coefficients vanish](hyp:hb), then [complementation changes the indicated coefficient only by its degree sign](goal). -/
-- @node: beta_complement_of_degree
lemma beta_complement_of_degree (E : Setup) (b : Theta E → ℝ)
    (T : Finset (Fin E.K)) (hb : ∀ R, T.card < R.card → beta E b R = 0) :
    beta E (fun θ => b (complement E θ)) T =
      (-1 : ℝ) ^ T.card * beta E b T := by
  classical
  have hexp : (fun θ => b (complement E θ)) =
      ∑ R, beta E b R • (fun θ => monomial E R (complement E θ)) := by
    funext θ
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      boolean_mobius_expansion E b (complement E θ)
  rw [hexp, beta_finset_sum]
  simp_rw [beta_smul, beta_complement_monomial]
  rw [Finset.sum_eq_single T]
  · rw [if_pos (Finset.Subset.rfl)]
    ring
  · intro R hR hRT
    by_cases hsub : T ⊆ R
    · have hcard : T.card < R.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hRT⟩)
      rw [if_pos hsub, hb R hcard, zero_mul]
    · rw [if_neg hsub, mul_zero]
  · simp

/-- Under [complement-invariant variance](hyp:hvar), [the true variance is unchanged by schedule complementation](goal). -/
-- @node: trueVarianceFn_complement
lemma trueVarianceFn_complement (E : Setup) (hvar : ComplementInvariantVariance E)
    (θ : Theta E) : trueVarianceFn E (complement E θ) = trueVarianceFn E θ := by
  have hsym : ∀ i k, varianceMatrix E i k = varianceMatrix E k i := by
    intro i k
    unfold varianceMatrix
    congr 1
    · apply Finset.sum_congr rfl
      intro z hz
      ring
    · ring
  have hcol : ∀ k, ∑ i, varianceMatrix E i k = 0 := by
    intro k
    calc
      ∑ i, varianceMatrix E i k = ∑ i, varianceMatrix E k i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsym i k
      _ = 0 := hvar k
  have hcomp : ∀ i, ((((complement E θ) i : Fin 2) : ℕ) : ℝ) =
      1 - (((θ i : Fin 2) : ℕ) : ℝ) := by
    intro i
    unfold complement
    rw [Nat.cast_sub]
    · norm_num
    · exact Nat.le_of_lt_succ (θ i).isLt
  unfold trueVarianceFn
  simp_rw [hcomp]
  have htotal : (∑ i, ∑ k, varianceMatrix E i k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hvar i
  have hrow : (∑ i, ∑ k, varianceMatrix E i k *
      (((θ i : Fin 2) : ℕ) : ℝ)) = 0 := by
    calc
      ∑ i, ∑ k, varianceMatrix E i k * (((θ i : Fin 2) : ℕ) : ℝ) =
          ∑ i, (∑ k, varianceMatrix E i k) * (((θ i : Fin 2) : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_mul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hvar i, zero_mul]
  have hcolumn : (∑ i, ∑ k, varianceMatrix E i k *
      (((θ k : Fin 2) : ℕ) : ℝ)) = 0 := by
    rw [Finset.sum_comm]
    calc
      ∑ k, ∑ i, varianceMatrix E i k * (((θ k : Fin 2) : ℕ) : ℝ) =
          ∑ k, (∑ i, varianceMatrix E i k) * (((θ k : Fin 2) : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.sum_mul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [hcol k, zero_mul]
  calc
    (∑ i, ∑ k, varianceMatrix E i k *
        (1 - (((θ i : Fin 2) : ℕ) : ℝ)) *
        (1 - (((θ k : Fin 2) : ℕ) : ℝ))) =
        (∑ i, ∑ k, varianceMatrix E i k) -
        (∑ i, ∑ k, varianceMatrix E i k * (((θ i : Fin 2) : ℕ) : ℝ)) -
        (∑ i, ∑ k, varianceMatrix E i k * (((θ k : Fin 2) : ℕ) : ℝ)) +
        ∑ i, ∑ k, varianceMatrix E i k * (((θ i : Fin 2) : ℕ) : ℝ) *
          (((θ k : Fin 2) : ℕ) : ℝ) := by
          simp_rw [mul_sub, sub_mul]
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          ring
    _ = ∑ i, ∑ k, varianceMatrix E i k * (((θ i : Fin 2) : ℕ) : ℝ) *
          (((θ k : Fin 2) : ℕ) : ℝ) := by rw [htotal, hrow, hcolumn]; ring

/-- In [an experiment](hyp:E), for [a complement-invariant objective](hyp:q,hq) and [a bound](hyp:b), [averaging the bound with its complement leaves the weighted objective unchanged](goal). -/
-- @node: complement_symmetrization_objective
lemma complement_symmetrization_objective (E : Setup) (q : Theta E → ℝ)
    (hq : ComplementInvariantObjective E q) (b : Theta E → ℝ) :
    (∑ θ, q θ * ((b θ + b (complement E θ)) / 2)) = ∑ θ, q θ * b θ := by
  have hchange : (∑ θ, q θ * b (complement E θ)) = ∑ θ, q θ * b θ := by
    calc
      ∑ θ, q θ * b (complement E θ) =
          ∑ θ, (q (complement E θ) * b (complement E θ)) := by
            apply Finset.sum_congr rfl
            intro θ hθ
            rw [← hq θ]
      _ = ∑ θ, q θ * b θ := (complementEquiv E).sum_comp (fun θ => q θ * b θ)
  calc
    (∑ θ, q θ * ((b θ + b (complement E θ)) / 2)) =
        ∑ θ, ((1 / 2) * (q θ * b θ) +
          (1 / 2) * (q θ * b (complement E θ))) := by
            apply Finset.sum_congr rfl
            intro θ hθ
            ring
    _ = (1 / 2) * (∑ θ, q θ * b θ) +
        (1 / 2) * ∑ θ, q θ * b (complement E θ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ θ, q θ * b θ := by rw [hchange]; ring

/-- In [an experiment](hyp:E) where [every observation set has at most three coordinates](hyp:hcard), [the unrestricted observable span equals the degree-three observable span](goal). -/
-- @node: observableSpan_top_eq_three_of_observation_card
lemma observableSpan_top_eq_three_of_observation_card (E : Setup)
    (hcard : ∀ z, (E.O z).card ≤ 3) : observableSpan E ⊤ = observableSpan E 3 := by
  apply le_antisymm
  · unfold observableSpan
    apply Submodule.span_mono
    rintro u ⟨S, hS, hdeg, rfl⟩
    have hS' := hS
    unfold observableComplex at hS'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS'
    rcases hS' with ⟨hSuniv, z, hsub⟩
    exact ⟨S, hS, by
      exact_mod_cast (Finset.card_le_card hsub).trans (hcard z), rfl⟩
  · exact observableSpan_mono_degree E le_top

/-- In [an experiment](hyp:E) with [objective weights](hyp:q), [complement-invariant true variance](hyp:hvar), [complement-invariant objective weights](hyp:hq), and [full support](hyp:hfull), [every odd-degree optimum equals the preceding even-degree optimum; in particular degrees three and two agree, and observation sets of size at most three make the unrestricted optimum equal the degree-two optimum](goal). -/
-- @node: thm:complement-degree-collapse
theorem optValue_odd_degree_collapse (E : Setup) (q : Theta E → ℝ)
    (hvar : ComplementInvariantVariance E)
    (hq : ComplementInvariantObjective E q)
    (hfull : FullSupportWeight E q) :
    (∀ d : ℕ, optValue E ⟨q, hfull⟩ (2 * d + 1) = optValue E ⟨q, hfull⟩ (2 * d)) ∧
    (optValue E ⟨q, hfull⟩ 3 = optValue E ⟨q, hfull⟩ 2) ∧
    ((∀ z, (E.O z).card ≤ 3) →
      optValue E ⟨q, hfull⟩ ⊤ = optValue E ⟨q, hfull⟩ 2) := by
  classical
  let q' : FullSupportObjective E := ⟨q, hfull⟩
  have hcollapse : ∀ d : ℕ,
      optValue E q' (2 * d + 1) = optValue E q' (2 * d) := by
    intro d
    unfold optValue
    congr 1
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      let bc : Theta E → ℝ := fun θ => b (complement E θ)
      let bs : Theta E → ℝ := fun θ => (b θ + bc θ) / 2
      have hbsform : bs = (2 : ℝ)⁻¹ • (b + bc) := by
        funext θ
        simp [bs]
        ring
      have hbc : bc ∈ observableSpan E (2 * d + 1) := by
        exact complement_preserves_observableSpan E _ hb.1
      have hbsHigh : bs ∈ observableSpan E (2 * d + 1) := by
        rw [hbsform]
        exact (observableSpan E (2 * d + 1)).smul_mem _
          ((observableSpan E (2 * d + 1)).add_mem hb.1 hbc)
      have hbs : bs ∈ observableSpan E (2 * d) := by
        rw [observableSpan_iff_beta_vanishes_degree]
        intro T hbad
        rcases hbad with hnotobs | hnotdeg
        · exact (observableSpan_iff_beta_vanishes_degree E bs (2 * d + 1)).mp
            hbsHigh T (Or.inl hnotobs)
        · have hcardLower : 2 * d < T.card := by exact_mod_cast (lt_of_not_ge hnotdeg)
          by_cases hlarge : 2 * d + 1 < T.card
          · exact (observableSpan_iff_beta_vanishes_degree E bs (2 * d + 1)).mp
              hbsHigh T (Or.inr (by exact_mod_cast (not_le.mpr hlarge)))
          · have hcardT : T.card = 2 * d + 1 := by omega
            have hbHigher : ∀ R, T.card < R.card → beta E b R = 0 := by
              intro R hTR
              exact (observableSpan_iff_beta_vanishes_degree E b (2 * d + 1)).mp
                hb.1 R (Or.inr (by
                  exact_mod_cast (not_le.mpr (by omega : 2 * d + 1 < R.card))))
            rw [hbsform]
            rw [beta_smul, beta_add]
            change (2 : ℝ)⁻¹ *
              (beta E b T + beta E (fun θ => b (complement E θ)) T) = 0
            rw [beta_complement_of_degree E b T hbHigher]
            rw [show (-1 : ℝ) ^ T.card = -1 by
              rw [hcardT, pow_add, pow_mul]
              norm_num]
            ring
      refine ⟨bs, ⟨hbs, ?_⟩, ?_⟩
      · intro θ
        change trueVarianceFn E θ ≤ (b θ + b (complement E θ)) / 2
        have h₁ := hb.2 θ
        have h₂ := hb.2 (complement E θ)
        rw [trueVarianceFn_complement E hvar] at h₂
        linarith
      · change (∑ θ, q θ * ((b θ + b (complement E θ)) / 2)) =
          ∑ θ, q θ * b θ
        exact complement_symmetrization_objective E q hq b
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b, ⟨observableSpan_mono_degree E ?_ hb.1, hb.2⟩, rfl⟩
      exact_mod_cast (by omega : 2 * d ≤ 2 * d + 1)
  refine ⟨hcollapse, ?_, ?_⟩
  · change optValue E q' 3 = optValue E q' 2
    convert hcollapse 1 using 1 <;> norm_num
  · intro hcard
    have hspan := observableSpan_top_eq_three_of_observation_card E hcard
    have hcone : conservativeCone E ⊤ = conservativeCone E 3 := by
      ext b
      simp only [conservativeCone, Set.mem_setOf_eq]
      rw [hspan]
    calc
      optValue E q' ⊤ = optValue E q' 3 := by unfold optValue; rw [hcone]
      _ = optValue E q' 2 := by convert hcollapse 1 using 1 <;> norm_num
  -- @realizes d(nonnegative half-degree index)

end CausalSmith.Experimentation.BinaryTruthbound
