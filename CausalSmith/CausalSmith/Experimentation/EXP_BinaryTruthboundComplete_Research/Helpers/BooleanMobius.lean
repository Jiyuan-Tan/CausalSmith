import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Basic
import Causalean.Panel.PO.Mobius
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Boolean-cube Mobius inversion and centered-coordinate helpers. -/

open scoped BigOperators
open Finset Set

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- Vertex schedule with ones exactly on `T`. -/
def vertex (E : Setup) (T : Finset (Fin E.K)) : Theta E := fun i => if i ∈ T then 1 else 0
  -- @realizes \mathbf 1_T(vertex schedule with support T)

/-- Inclusion-exclusion coefficient of a Boolean function. -/
def beta (E : Setup) (u : Theta E → ℝ) (S : Finset (Fin E.K)) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * u (vertex E T)
  -- @realizes \beta_S(inclusion-exclusion coefficient)

/-- Joint probability that every coordinate of `S` is observed. -/
def jointObsProb (E : Setup) (S : Finset (Fin E.K)) : ℝ :=
  E.design.E fun z => if S ⊆ E.O z then 1 else 0
  -- @realizes \pi_S(sum of assignment probabilities observing S)

/-- Centered binary coordinate. -/
def centeredCoord {E : Setup} (θ : Theta E) (i : Fin E.K) : ℝ :=
  2 * ((θ i : ℕ) : ℝ) - 1
  -- @realizes x_i(2 theta_i - 1)

/-- A monomial evaluated from an assignment-local observed schedule. -/
def localMonomial (E : Setup) (z : E.Omega) (y : E.O z → Fin 2)
    (S : Finset (Fin E.K)) : ℝ :=
  ∏ i ∈ S, if h : i ∈ E.O z then ((y ⟨i, h⟩ : ℕ) : ℝ) else 0

/-- Canonical inverse-observation-probability implementation of Boolean coefficients. -/
noncomputable def mobiusImplementation (E : Setup) (a : Finset (Fin E.K) → ℝ) :
    AssignmentRule E := fun z y =>
  ∑ S ∈ (E.O z).powerset, (a S / jointObsProb E S) * localMonomial E z y S

/-- If [a coordinate set is observable](hyp:hS), then [every subset of it](hyp:hTS) is [also observable](goal). -/
lemma observableComplex_downward_closed (E : Setup) {S T : Finset (Fin E.K)}
    (hS : S ∈ observableComplex E) (hTS : T ⊆ S) : T ∈ observableComplex E := by
  unfold observableComplex at *
  simp only [Finset.mem_filter, Finset.mem_powerset] at *
  rcases hS with ⟨hSuniv, z, hz⟩
  exact ⟨hTS.trans hSuniv, z, hTS.trans hz⟩

/-- For [a finite set](hyp:S), [the alternating subset sum is unchanged when its exponent uses complement size rather than subset size](goal). -/
-- @node: alternating_sum_card_sub
lemma alternating_sum_card_sub {iota : Type*} [DecidableEq iota] (S : Finset iota) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card := by
  refine Finset.sum_nbij' (fun T => S \ T) (fun T => S \ T) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro T hT
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro T hT
    ext i
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hiS, hnot⟩
      by_contra hiT
      exact hnot ⟨hiS, hiT⟩
    · intro hiT
      exact ⟨hTS hiT, fun h => h.2 hiT⟩
  · intro T hT
    ext i
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hiS, hnot⟩
      by_contra hiT
      exact hnot ⟨hiS, hiT⟩
    · intro hiT
      exact ⟨hTS hiT, fun h => h.2 hiT⟩
  · intro T hT
    rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hT)]

/-- For [an experiment and Boolean function](hyp:E,u), [the function equals the sum of its Boolean Möbius coefficients times the corresponding monomials](goal). -/
lemma boolean_mobius_expansion (E : Setup) (u : Theta E → ℝ) :
    ∀ θ, u θ = ∑ S, beta E u S * monomial E S θ := by
  classical
  intro θ
  let τ : Theta E → ℝ := fun h => u h - u (fun _ => 0)
  have hτ0 : τ (fun _ => 0) = 0 := by simp [τ]
  have hexp := Causalean.Panel.PO.Mobius.mobius_expansion τ hτ0 θ
  have hcoef : ∀ S, S.Nonempty →
      Causalean.Panel.PO.Mobius.delta τ S = beta E u S := by
    intro S hS
    simp only [Causalean.Panel.PO.Mobius.delta, τ]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    change (∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * u (vertex E T)) -
      (∑ T ∈ S.powerset,
        (-1 : ℝ) ^ (S.card - T.card) * u (fun _ => 0)) = beta E u S
    have hz : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) = 0 := by
      rw [alternating_sum_card_sub]
      exact_mod_cast Finset.sum_powerset_neg_one_pow_card_of_nonempty hS
    rw [← Finset.sum_mul, hz]
    simp [beta]
  rw [show u θ = u (fun _ => 0) + τ θ by simp [τ]]
  rw [hexp]
  rw [Finset.sum_congr rfl (fun S hS => by rw [hcoef S (Finset.mem_filter.mp hS).2])]
  simp only [monomial]
  have hzero : beta E u ∅ = u (fun _ => 0) := by
    simp only [beta, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty,
      Nat.zero_sub, pow_zero, one_mul]
    congr 1
  rw [← hzero]
  change beta E u ∅ +
      ∑ S ∈ (Finset.univ : Finset (Fin E.K)).powerset.filter (fun S => S.Nonempty),
        beta E u S * ∏ k ∈ S, ((θ k).val : ℝ) =
    ∑ S ∈ (Finset.univ : Finset (Fin E.K)).powerset,
      beta E u S * ∏ k ∈ S, ((θ k).val : ℝ)
  have herase :
      (Finset.univ : Finset (Fin E.K)).powerset.erase ∅ =
        (Finset.univ : Finset (Fin E.K)).powerset.filter (fun S => S.Nonempty) := by
    ext S
    simp [Finset.nonempty_iff_ne_empty]
  rw [← herase, add_comm]
  simpa only [Finset.prod_empty, mul_one] using
    (Finset.sum_erase_add
      (Finset.univ : Finset (Fin E.K)).powerset
      (fun S : Finset (Fin E.K) => beta E u S * ∏ k ∈ S, ((θ k).val : ℝ))
      (by simp : (∅ : Finset (Fin E.K)) ∈
        (Finset.univ : Finset (Fin E.K)).powerset))

/-- For [an experiment and two coordinate sets](hyp:E,S,T), [a monomial at a vertex is one exactly when its support is contained in the vertex support](goal). -/
-- @node: monomial_vertex
lemma monomial_vertex (E : Setup) (S T : Finset (Fin E.K)) :
    monomial E T (vertex E S) = if T ⊆ S then 1 else 0 := by
  apply Causalean.Panel.PO.Mobius.prod_indicator_eq (vertex E S) S
  intro i
  simp [vertex]

/-- For [a Boolean function and proposed monomial coefficients](hyp:u,a) satisfying [the displayed monomial expansion](hyp:h), [those coefficients equal the Boolean Möbius coefficients](goal). -/
lemma boolean_mobius_unique (E : Setup) (u : Theta E → ℝ) (a : Finset (Fin E.K) → ℝ)
    (h : ∀ θ, u θ = ∑ S, a S * monomial E S θ) : a = beta E u := by
  classical
  have heval : ∀ (c : Finset (Fin E.K) → ℝ)
      (hc : ∀ θ, u θ = ∑ T, c T * monomial E T θ) S,
      u (vertex E S) = ∑ T ∈ S.powerset, c T := by
    intro c hc S
    rw [hc]
    simp_rw [monomial_vertex]
    change (∑ T ∈ (Finset.univ : Finset (Fin E.K)).powerset,
      c T * if T ⊆ S then 1 else 0) = ∑ T ∈ S.powerset, c T
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext T
      simp
    · intro T hT
      rfl
  have hbeta := boolean_mobius_expansion E u
  have hsum : ∀ S : Finset (Fin E.K),
      ∑ T ∈ S.powerset, (a T - beta E u T) = 0 := by
    intro S
    rw [Finset.sum_sub_distrib, ← heval a h S, ← heval (beta E u) hbeta S]
    simp
  funext S
  refine Finset.strongInductionOn S ?_
  intro S ih
  have hs := hsum S
  rw [← Finset.sum_erase_add (S.powerset)
    (fun T => a T - beta E u T) (a := S) (by simp)] at hs
  have hproper : ∀ T ∈ S.powerset.erase S, a T - beta E u T = 0 := by
    intro T hT
    have hsub : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)
    have hne : T ≠ S := Finset.ne_of_mem_erase hT
    rw [ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)]
    simp
  rw [Finset.sum_eq_zero hproper, zero_add] at hs
  linarith

/-- For [an experiment and two coordinate sets](hyp:E,T,S), [the Möbius coefficient of a monomial is one at its own support and zero elsewhere](goal). -/
-- @node: beta_monomial
lemma beta_monomial (E : Setup) (T S : Finset (Fin E.K)) :
    beta E (monomial E T) S = if S = T then 1 else 0 := by
  classical
  let a : Finset (Fin E.K) → ℝ := fun R => if R = T then 1 else 0
  have hexp : ∀ θ, monomial E T θ = ∑ R, a R * monomial E R θ := by
    intro θ
    simp [a]
  have hu := boolean_mobius_unique E (monomial E T) a hexp
  have hS := congrFun hu S
  simpa [a] using hS.symm

/-- For [an experiment, scalar, function, and coordinate set](hyp:E,c,u,S), [scaling a function scales its Möbius coefficient](goal). -/
lemma beta_smul (E : Setup) (c : ℝ) (u : Theta E → ℝ) (S : Finset (Fin E.K)) :
    beta E (c • u) S = c * beta E u S := by
  simp only [beta, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  ring

/-- For [an experiment, two functions, and a coordinate set](hyp:E,u,v,S), [the Möbius coefficient of their sum is the sum of their coefficients](goal). -/
-- @node: beta_add
lemma beta_add (E : Setup) (u v : Theta E → ℝ) (S : Finset (Fin E.K)) :
    beta E (u + v) S = beta E u S + beta E v S := by
  unfold beta
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- For [an experiment, finite index set, function family, and coordinate set](hyp:E,A,u,S), [the Möbius coefficient of the finite sum is the finite sum of coefficients](goal). -/
-- @node: beta_finset_sum
lemma beta_finset_sum (E : Setup) {ι : Type*} (A : Finset ι)
    (u : ι → Theta E → ℝ) (S : Finset (Fin E.K)) :
    beta E (∑ i ∈ A, u i) S = ∑ i ∈ A, beta E (u i) S := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [beta]
  | @insert i A hi ih =>
      rw [Finset.sum_insert hi, beta_add, ih, Finset.sum_insert hi]

/-- For [an experiment, function, and degree limit](hyp:E,u,r), [membership in the degree-restricted observable span is equivalent to vanishing coefficients outside allowed observable supports](goal). -/
-- @node: observableSpan_iff_beta_vanishes_degree
lemma observableSpan_iff_beta_vanishes_degree (E : Setup) (u : Theta E → ℝ)
    (r : WithTop ℕ) :
    u ∈ observableSpan E r ↔
      ∀ S, S ∉ observableComplex E ∨ ¬(S.card : WithTop ℕ) ≤ r → beta E u S = 0 := by
  classical
  constructor
  · intro hu
    unfold observableSpan at hu
    refine Submodule.span_induction
      (p := fun x _ => ∀ S, S ∉ observableComplex E ∨
        ¬(S.card : WithTop ℕ) ≤ r → beta E x S = 0) ?_ ?_ ?_ ?_ hu
    · intro x hx S hS
      rcases hx with ⟨T, hT, hdeg, rfl⟩
      rw [beta_monomial]
      by_cases hST : S = T
      · subst S
        rcases hS with hnot | hnot
        · exact (hnot hT).elim
        · exact (hnot hdeg).elim
      · simp [hST]
    · intro S hS
      simp [beta]
    · intro x y hx hy hxp hyp S hS
      rw [beta_add, hxp S hS, hyp S hS, add_zero]
    · intro c x hx hxp S hS
      rw [beta_smul, hxp S hS, mul_zero]
  · intro hv
    have hexp : u = ∑ S, beta E u S • monomial E S := by
      funext θ
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        boolean_mobius_expansion E u θ
    rw [hexp]
    apply Submodule.sum_mem
    intro S hS
    by_cases hgen : S ∈ observableComplex E ∧ (S.card : WithTop ℕ) ≤ r
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, hgen.1, hgen.2, rfl⟩)
    · rw [hv S (not_and_or.mp hgen)]
      simpa using (observableSpan E r).zero_mem

/-- For [an experiment and two coordinate sets](hyp:E,R,T), [the complemented monomial has the stated signed Möbius coefficient](goal). -/
-- @node: beta_complement_monomial
lemma beta_complement_monomial (E : Setup) (R T : Finset (Fin E.K)) :
    beta E (fun θ => monomial E R (complement E θ)) T =
      if T ⊆ R then (-1 : ℝ) ^ T.card else 0 := by
  classical
  by_cases hTR : T ⊆ R
  · rw [if_pos hTR]
    unfold beta
    rw [Finset.sum_eq_single ∅]
    · simp [monomial, complement, vertex]
    · intro U hU hUne
      obtain ⟨i, hiU⟩ := Finset.nonempty_iff_ne_empty.mpr hUne
      have hiR : i ∈ R := hTR (Finset.mem_powerset.mp hU hiU)
      simp only [monomial, complement, vertex]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero hiR
      simp [hiU]
    · simp
  · rw [if_neg hTR]
    obtain ⟨i, hiT, hiR⟩ := Set.not_subset.mp hTR
    have hinv : ∀ U ∈ (T.erase i).powerset,
        monomial E R (complement E (vertex E (insert i U))) =
          monomial E R (complement E (vertex E U)) := by
      intro U hU
      unfold monomial
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := fun h => hiR (h ▸ hj)
      simp [complement, vertex, hji]
    rw [← Finset.insert_erase hiT]
    unfold beta
    rw [Finset.sum_powerset_insert (by simp)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro U hU
    have hUi : i ∉ U := by
      intro h
      have : i ∈ T.erase i := (Finset.mem_powerset.mp hU) h
      simp at this
    have hcardT : (insert i (T.erase i)).card = (T.erase i).card + 1 := by simp
    have hcardU : (insert i U).card = U.card + 1 := by simp [hUi]
    change (-1 : ℝ) ^ ((insert i (T.erase i)).card - U.card) *
          monomial E R (complement E (vertex E U)) +
        (-1 : ℝ) ^ ((insert i (T.erase i)).card - (insert i U).card) *
          monomial E R (complement E (vertex E (insert i U))) = 0
    rw [hinv U hU, hcardT, hcardU]
    have hle : U.card ≤ (T.erase i).card :=
      Finset.card_le_card (Finset.mem_powerset.mp hU)
    rw [show (T.erase i).card + 1 - U.card = ((T.erase i).card - U.card) + 1 by omega]
    rw [show (T.erase i).card + 1 - (U.card + 1) = (T.erase i).card - U.card by omega]
    ring

/-- For [an experiment and Boolean function](hyp:E,u), [membership in the unrestricted observable span is equivalent to vanishing Möbius coefficients on nonobservable supports](goal). -/
lemma observableSpan_iff_beta_vanishes (E : Setup) (u : Theta E → ℝ) :
    u ∈ observableSpan E ⊤ ↔ ∀ S, S ∉ observableComplex E → beta E u S = 0 := by
  classical
  constructor
  · intro hu
    unfold observableSpan at hu
    refine Submodule.span_induction
      (p := fun x _ => ∀ S, S ∉ observableComplex E → beta E x S = 0) ?_ ?_ ?_ ?_ hu
    · intro x hx S hS
      rcases hx with ⟨T, hT, _, rfl⟩
      rw [beta_monomial]
      simp only [ite_eq_right_iff]
      intro hST
      exact (hS (hST ▸ hT)).elim
    · intro S hS
      simp [beta]
    · intro x y hx hy hxp hyp S hS
      rw [show beta E (x + y) S = beta E x S + beta E y S by
        simp only [beta, Pi.add_apply, mul_add, Finset.sum_add_distrib]]
      rw [hxp S hS, hyp S hS, add_zero]
    · intro c x hx hxp S hS
      rw [show beta E (c • x) S = c * beta E x S by
        simp only [beta, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
              (c * x (vertex E T))) =
              ∑ T ∈ S.powerset,
                c * ((-1 : ℝ) ^ (S.card - T.card) * x (vertex E T)) := by
                apply Finset.sum_congr rfl
                intro T hT
                ring
          _ = c * ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ (S.card - T.card) * x (vertex E T) := by
                rw [Finset.mul_sum]]
      rw [hxp S hS, mul_zero]
  · intro hv
    have hexp : u = ∑ S, beta E u S • monomial E S := by
      funext θ
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        boolean_mobius_expansion E u θ
    rw [hexp]
    apply Submodule.sum_mem
    intro S hS
    by_cases hobs : S ∈ observableComplex E
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨S, hobs, by simp, rfl⟩
    · rw [hv S hobs]
      simpa only [zero_smul] using (observableSpan E ⊤).zero_mem

/-- If [the toggled coordinate belongs to the coefficient set](hyp:hi) and [a Boolean function is invariant under that vertex toggle](hyp:hinv), then [the indicated Möbius coefficient is zero](goal). -/
-- @node: beta_eq_zero_of_vertex_toggle
lemma beta_eq_zero_of_vertex_toggle (E : Setup) (u : Theta E → ℝ)
    (S : Finset (Fin E.K)) (i : Fin E.K) (hi : i ∈ S)
    (hinv : ∀ T ∈ (S.erase i).powerset,
      u (vertex E (insert i T)) = u (vertex E T)) :
    beta E u S = 0 := by
  classical
  rw [show S = insert i (S.erase i) by simp [hi], beta,
    Finset.sum_powerset_insert (by simp)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro T hT
  have hTi : i ∉ T := by
    intro h
    have : i ∈ S.erase i := (Finset.mem_powerset.mp hT) h
    simp at this
  have hcardS : (insert i (S.erase i)).card = (S.erase i).card + 1 := by simp
  have hcardT : (insert i T).card = T.card + 1 := by simp [hTi]
  rw [hinv T hT, hcardS, hcardT]
  have hle : T.card ≤ (S.erase i).card :=
    Finset.card_le_card (Finset.mem_powerset.mp hT)
  rw [show (S.erase i).card + 1 - T.card = ((S.erase i).card - T.card) + 1 by omega]
  rw [show (S.erase i).card + 1 - (T.card + 1) = (S.erase i).card - T.card by omega]
  ring

/-- For [an experiment and assignment atom](hyp:E,z), [functions pulled back from that atom's observed schedule belong to the observable span](goal). -/
-- @node: observed_pullback_mem_observableSpan
lemma observed_pullback_mem_observableSpan (E : Setup) (z : E.Omega)
    (g : (E.O z → Fin 2) → ℝ) :
    (fun θ => g (restrict E z θ)) ∈ observableSpan E ⊤ := by
  classical
  rw [observableSpan_iff_beta_vanishes]
  intro S hS
  have hnsub : ¬ S ⊆ E.O z := by
    intro hsub
    apply hS
    unfold observableComplex
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ S, z, hsub⟩
  obtain ⟨i, hiS, hiO⟩ := Finset.not_subset.mp hnsub
  apply beta_eq_zero_of_vertex_toggle E _ S i hiS
  intro T hT
  congr 1
  funext j
  simp only [restrict]
  have hji : (j : Fin E.K) ≠ i := by
    intro h
    subst i
    exact hiO j.property
  simp [vertex, hji]

/-- For [an experiment and assignment rule](hyp:E,g), [the expected rule belongs to the observable span](goal). -/
-- @node: expectedRule_mem_observableSpan
lemma expectedRule_mem_observableSpan (E : Setup) (g : AssignmentRule E) :
    expectedRule E g ∈ observableSpan E ⊤ := by
  classical
  have hz : ∀ z, (E.design.p z) • (fun θ => g z (restrict E z θ)) ∈
      observableSpan E ⊤ := by
    intro z
    exact Submodule.smul_mem _ _ (observed_pullback_mem_observableSpan E z (g z))
  have hsum : (∑ z, (E.design.p z) • (fun θ => g z (restrict E z θ))) ∈
      observableSpan E ⊤ :=
    (observableSpan E ⊤).sum_mem (fun z _ => hz z)
  unfold expectedRule Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [show (fun θ => ∑ z, E.design.p z * g z (restrict E z θ)) =
      ∑ z, (E.design.p z) • (fun θ => g z (restrict E z θ)) by
    funext θ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
  exact hsum

/-- If [a coordinate set is observable](hyp:hS), then [its joint observation probability is strictly positive](goal). -/
-- @node: jointObsProb_pos
lemma jointObsProb_pos (E : Setup) (S : Finset (Fin E.K))
    (hS : S ∈ observableComplex E) : 0 < jointObsProb E S := by
  classical
  unfold observableComplex at hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨_, z, hz⟩ := hS
  unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
  have hnonneg : ∀ w ∈ Finset.univ,
      0 ≤ E.design.p w * (if S ⊆ E.O w then 1 else 0) := by
    intro w hw
    by_cases h : S ⊆ E.O w <;> simp [h, E.design.p_nonneg w]
  have hterm : 0 < E.design.p z * (if S ⊆ E.O z then 1 else 0) := by
    simp [hz, E.support_pos z]
  exact lt_of_lt_of_le hterm (Finset.single_le_sum hnonneg (Finset.mem_univ z))

/-- If [a coordinate set is observed under an assignment](hyp:hS), then [its local monomial equals its full-schedule monomial](goal). -/
-- @node: localMonomial_restrict
lemma localMonomial_restrict (E : Setup) (z : E.Omega) (θ : Theta E)
    (S : Finset (Fin E.K)) (hS : S ⊆ E.O z) :
    localMonomial E z (restrict E z θ) S = monomial E S θ := by
  classical
  unfold localMonomial monomial restrict
  apply Finset.prod_congr rfl
  intro i hi
  simp [hS hi]

/-- If [coefficients vanish on nonobservable supports](hyp:ha), then [the inverse-observation-probability rule has the stated expected Möbius polynomial](goal). -/
-- @node: expectedRule_mobiusImplementation
lemma expectedRule_mobiusImplementation (E : Setup) (a : Finset (Fin E.K) → ℝ)
    (ha : ∀ S, S ∉ observableComplex E → a S = 0) :
    expectedRule E (mobiusImplementation E a) =
      fun θ => ∑ S, a S * monomial E S θ := by
  classical
  funext θ
  unfold expectedRule Causalean.Experimentation.DesignBased.FiniteDesign.E
  simp only [mobiusImplementation]
  let U : Finset (Finset (Fin E.K)) := (Finset.univ : Finset (Fin E.K)).powerset
  have hlocal : ∀ z,
      (∑ S ∈ (E.O z).powerset,
          E.design.p z * ((a S / jointObsProb E S) *
            localMonomial E z (restrict E z θ) S)) =
      ∑ S ∈ U, if S ⊆ E.O z then
          E.design.p z * ((a S / jointObsProb E S) * monomial E S θ) else 0 := by
    intro z
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext S
      simp [U]
    · intro S hS
      simp only [Finset.mem_filter] at hS
      rw [localMonomial_restrict E z θ S hS.2]
  simp_rw [Finset.mul_sum]
  simp_rw [hlocal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hSU
  by_cases hobs : S ∈ observableComplex E
  · have hpi : jointObsProb E S ≠ 0 := ne_of_gt (jointObsProb_pos E S hobs)
    calc
      (∑ z, if h : S ⊆ E.O z then
          E.design.p z * (a S / jointObsProb E S * monomial E S θ) else 0) =
          (a S / jointObsProb E S * monomial E S θ) * jointObsProb E S := by
            unfold jointObsProb Causalean.Experimentation.DesignBased.FiniteDesign.E
            simp_rw [mul_ite, mul_one, mul_zero]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            by_cases h : S ⊆ E.O z <;> simp [h]
            ring
      _ = a S * monomial E S θ := by field_simp
  · rw [ha S hobs]
    simp

end CausalSmith.Experimentation.BinaryTruthbound
