/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Sign polynomials for extremal residual sets

This module develops the ordered sign-block argument used in the necessity proof
of Chebyshev's alternation theorem.
-/

@[expose] public section

open Polynomial Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Sign polynomials and alternating extrema -/


private def boolSign (b : Bool) : ℝ := if b then 1 else -1

private lemma boolSign_sq (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> simp [boolSign]

private lemma boolSign_eq_neg_of_ne {a b : Bool} (h : a ≠ b) :
    boolSign a = -boolSign b := by
  cases a <;> cases b <;> simp_all [boolSign]

private def signChanges (color : ℝ → Bool) : List ℝ → ℕ
  | [] | [_] => 0
  | a :: b :: l => (if color a = color b then 0 else 1) + signChanges color (b :: l)

private noncomputable def listSignPolynomial (color : ℝ → Bool) : List ℝ → Polynomial ℝ
  | [] => 1
  | [a] => C (boolSign (color a))
  | a :: b :: l =>
      if color a = color b then listSignPolynomial color (b :: l)
      else (X - C ((a + b) / 2)) * listSignPolynomial color (b :: l)

private lemma listSignPolynomial_degree (color : ℝ → Bool) (l : List ℝ) :
    (listSignPolynomial color l).natDegree ≤ signChanges color l := by
  induction l with
  | nil => simp [listSignPolynomial, signChanges]
  | cons a l ih =>
      cases l with
      | nil => simp [listSignPolynomial, signChanges]
      | cons b l =>
          by_cases h : color a = color b
          · simpa [listSignPolynomial, signChanges, h] using ih
          · simp only [listSignPolynomial, signChanges, h, ↓reduceIte]
            calc
              ((X - C ((a + b) / 2)) * listSignPolynomial color (b :: l)).natDegree
                  ≤ (X - C ((a + b) / 2)).natDegree +
                    (listSignPolynomial color (b :: l)).natDegree := natDegree_mul_le
              _ ≤ 1 + signChanges color (b :: l) := by
                rw [natDegree_X_sub_C]
                omega

private lemma listSignPolynomial_sign (color : ℝ → Bool) (ε : ℝ) (l : List ℝ)
    (hε : 0 < ε) (hne : l ≠ []) (hsort : l.Pairwise (· < ·))
    (hsep : ∀ a ∈ l, ∀ b ∈ l, color a ≠ color b → 4 * ε < |a - b|) :
    (∀ x, x < l.head hne + ε →
      0 < boolSign (color (l.head hne)) * (listSignPolynomial color l).eval x) ∧
    ∀ c ∈ l, ∀ x, |x - c| < ε →
      0 < boolSign (color c) * (listSignPolynomial color l).eval x := by
  induction l with
  | nil => simp at hne
  | cons a l ih =>
      cases l with
      | nil =>
          constructor
          · intro x hx
            simp [listSignPolynomial, boolSign_sq]
          · intro c hc x hx
            simp only [List.mem_singleton] at hc
            subst c
            simp [listSignPolynomial, boolSign_sq]
      | cons b l =>
          have hab : a < b := (List.pairwise_cons.mp hsort).1 b (by simp)
          have hsort' : (b :: l).Pairwise (· < ·) := (List.pairwise_cons.mp hsort).2
          have hsep' : ∀ u ∈ b :: l, ∀ v ∈ b :: l,
              color u ≠ color v → 4 * ε < |u - v| := by
            intro u hu v hv huv
            exact hsep u (by simp [hu]) v (by simp [hv]) huv
          have ih' := ih (by simp) hsort' hsep'
          by_cases hc : color a = color b
          · constructor
            · intro x hx
              rw [listSignPolynomial, if_pos hc]
              simp only [List.head_cons] at hx ⊢
              simpa [hc] using ih'.1 x (by simp only [List.head_cons]; linarith)
            · intro c hc_mem x hx
              rw [listSignPolynomial, if_pos hc]
              rcases List.mem_cons.mp hc_mem with rfl | hc_tail
              · simpa [hc] using ih'.1 x (by
                  simp only [List.head_cons]
                  rw [abs_lt] at hx
                  linarith)
              · exact ih'.2 c hc_tail x hx
          · have hsign : boolSign (color a) = -boolSign (color b) :=
              boolSign_eq_neg_of_ne hc
            have hgap : 4 * ε < b - a := by
              have := hsep a (by simp) b (by simp) hc
              rw [abs_of_neg (sub_neg.mpr hab)] at this
              linarith
            constructor
            · intro x hx
              rw [listSignPolynomial, if_neg hc, eval_mul]
              simp only [eval_sub, eval_X, eval_C]
              simp only [List.head_cons] at hx ⊢
              have htail := ih'.1 x (by
                simp only [List.head_cons]
                linarith)
              simp only [List.head_cons] at htail
              have hfactor : (x - (a + b) / 2) < 0 := by
                linarith
              rw [hsign]
              have hp := mul_pos (neg_pos.mpr hfactor) htail
              rw [show -boolSign (color b) *
                ((x - (a + b) / 2) * (listSignPolynomial color (b :: l)).eval x) =
                (-(x - (a + b) / 2)) *
                  (boolSign (color b) * (listSignPolynomial color (b :: l)).eval x) by ring]
              exact hp
            · intro c hc_mem x hx
              rw [listSignPolynomial, if_neg hc, eval_mul]
              simp only [eval_sub, eval_X, eval_C]
              rcases List.mem_cons.mp hc_mem with hca | hc_tail
              · rw [hca] at hx ⊢
                have htail := ih'.1 x (by
                  simp only [List.head_cons]
                  rw [abs_lt] at hx
                  linarith)
                simp only [List.head_cons] at htail
                have hfactor : x - (a + b) / 2 < 0 := by
                  rw [abs_lt] at hx
                  linarith
                rw [hsign]
                have hp := mul_pos (neg_pos.mpr hfactor) htail
                rw [show -boolSign (color b) *
                  ((x - (a + b) / 2) * (listSignPolynomial color (b :: l)).eval x) =
                  (-(x - (a + b) / 2)) *
                    (boolSign (color b) * (listSignPolynomial color (b :: l)).eval x) by ring]
                exact hp
              · have hbc : b ≤ c := by
                  rcases List.mem_cons.mp hc_tail with rfl | hcl
                  · exact le_rfl
                  · exact (List.pairwise_cons.mp hsort').1 c hcl |>.le
                have hfactor : 0 < x - (a + b) / 2 := by
                  rw [abs_lt] at hx
                  linarith
                have htail := ih'.2 c hc_tail x hx
                nlinarith

private lemma exists_alternating_sublist_of_lt_signChanges
    (color : ℝ → Bool) {a : ℝ} {l : List ℝ} (hsort : (a :: l).Pairwise (· < ·))
    {n : ℕ} (hchange : n < signChanges color (a :: l)) :
    ∃ w : List ℝ, (a :: w).length = n + 2 ∧ (a :: w).Pairwise (· < ·) ∧
      (a :: w).IsChain (fun x y ↦ color x ≠ color y) ∧
      ∀ x ∈ a :: w, x ∈ a :: l := by
  induction l generalizing a n with
  | nil => simp [signChanges] at hchange
  | cons b l ih =>
      have hab : a < b := (List.pairwise_cons.mp hsort).1 b (by simp)
      have hsort' : (b :: l).Pairwise (· < ·) := (List.pairwise_cons.mp hsort).2
      by_cases hc : color a = color b
      · have hchange' : n < signChanges color (b :: l) := by
          simpa [signChanges, hc] using hchange
        obtain ⟨w, hwlen, hword, hwchain, hwmem⟩ := ih hsort' hchange'
        cases w with
        | nil => simp at hwlen
        | cons c w =>
          refine ⟨c :: w, ?_, ?_, ?_, ?_⟩
          · simpa using hwlen
          · rw [List.pairwise_cons]
            exact ⟨fun x hx ↦ hab.trans ((List.pairwise_cons.mp hword).1 x hx),
              (List.pairwise_cons.mp hword).2⟩
          · rw [List.isChain_cons_cons]
            have hfirst := (List.isChain_cons_cons.mp hwchain).1
            exact ⟨by simpa [hc] using hfirst, (List.isChain_cons_cons.mp hwchain).2⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · simp
            · exact List.mem_cons.mpr (Or.inr (hwmem x (List.mem_cons.mpr (Or.inr hx))))
      · cases n with
        | zero =>
            refine ⟨[b], by simp, ?_, by simp [hc], ?_⟩
            · simp [hab]
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · simp
              · have : x = b := by simpa using hx
                subst x
                simp
        | succ n =>
            have hchange' : n < signChanges color (b :: l) := by
              simp [signChanges, hc] at hchange
              omega
            obtain ⟨w, hwlen, hword, hwchain, hwmem⟩ := ih hsort' hchange'
            refine ⟨b :: w, ?_, ?_, ?_, ?_⟩
            · simp at hwlen ⊢
              omega
            · rw [List.pairwise_cons]
              refine ⟨?_, hword⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hab
              · exact hab.trans ((List.pairwise_cons.mp hword).1 x hx)
            · rw [List.isChain_cons_cons]
              exact ⟨hc, hwchain⟩
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · simp
              · exact List.mem_cons.mpr (Or.inr (hwmem x hx))

private lemma boolSign_get_eq_of_chain (color : ℝ → Bool) {a : ℝ} {l : List ℝ}
    (hchain : (a :: l).IsChain (fun x y ↦ color x ≠ color y)) :
    ∀ i : Fin (a :: l).length,
      boolSign (color ((a :: l).get i)) =
        boolSign (color a) * (-1 : ℝ) ^ (i : ℕ) := by
  induction l generalizing a with
  | nil =>
      intro i
      have hiLt : (i : ℕ) < 1 := by simpa using i.isLt
      have hi : (i : ℕ) = 0 := by omega
      have hi' : i = ⟨0, by simp⟩ := Fin.ext hi
      rw [hi']
      simp
  | cons b l ih =>
      rw [List.isChain_cons_cons] at hchain
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · change boolSign (color ((b :: l).get j)) =
          boolSign (color a) * (-1 : ℝ) ^ ((j : ℕ) + 1)
        rw [ih hchain.2 j, boolSign_eq_neg_of_ne hchain.1, pow_succ]
        ring

/-- A residual has `L+2` alternating uniform extrema when it attains its
supremum magnitude with alternating signs at that many strictly ordered
points of the interval. [the stated inputs](hyp:g,r,s,L,nodes,orientation) establish [the defined object](goal). -/
def IsAlternatingExtrema
    (g : ℝ → ℝ) (r s : ℝ) (L : ℕ)
    (nodes : Fin (L + 2) → ℝ) (orientation : ℝ) : Prop :=
  StrictMono nodes ∧
    (∀ i, nodes i ∈ Set.Icc r s) ∧
    (orientation = 1 ∨ orientation = -1) ∧
    ∀ i, g (nodes i) =
      orientation * (-1 : ℝ) ^ (i : ℕ) * intervalSupNorm g r s

/-- If a continuous residual on a nondegenerate interval has positive
supremum norm but no `L+2` alternating extrema, some polynomial of degree at
most `L` has the residual's strict sign at every norm-attaining point. [the stated inputs](hyp:g,r,s,hrs,hg,L,hE,hno) establish [the stated conclusion](goal). -/
theorem exists_signPolynomial_of_no_alternatingExtrema
    {g : ℝ → ℝ} {r s : ℝ} (hrs : r < s)
    (hg : ContinuousOn g (Set.Icc r s)) (L : ℕ)
    (hE : 0 < intervalSupNorm g r s)
    (hno : ¬ ∃ nodes orientation, IsAlternatingExtrema g r s L nodes orientation) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ L ∧
      ∀ x ∈ Set.Icc r s, |g x| = intervalSupNorm g r s →
        0 < g x * Q.eval x := by
  classical
  let E := intervalSupNorm g r s
  let K : Set ℝ := {x | x ∈ Set.Icc r s ∧ |g x| = E}
  let P : Set ℝ := {x | x ∈ K ∧ g x = E}
  let N : Set ℝ := {x | x ∈ K ∧ g x = -E}
  have hKsub : K ⊆ Set.Icc r s := fun _ hx ↦ hx.1
  have hKcompact : IsCompact K := by
    apply isCompact_Icc.of_isClosed_subset
    · exact isClosed_Icc.isClosed_eq hg.abs continuousOn_const
    · exact hKsub
  have hKne : K.Nonempty := by
    obtain ⟨x, hx, hmax, -⟩ :=
      isCompact_Icc.exists_sSup_image_eq_and_ge (nonempty_Icc.mpr hrs.le) hg.abs
    exact ⟨x, hx, by simpa [E, intervalSupNorm] using hmax.symm⟩
  have hPcompact : IsCompact P := by
    apply hKcompact.of_isClosed_subset
    · exact hKcompact.isClosed.isClosed_eq (hg.mono hKsub) continuousOn_const
    · intro x hx
      exact hx.1
  have hNcompact : IsCompact N := by
    apply hKcompact.of_isClosed_subset
    · exact hKcompact.isClosed.isClosed_eq (hg.mono hKsub) continuousOn_const
    · intro x hx
      exact hx.1
  have hPN : Disjoint P N := by
    rw [Set.disjoint_left]
    intro x hxP hxN
    have : E = -E := hxP.2.symm.trans hxN.2
    have : E = 0 := by linarith
    exact hE.ne' (by simpa [E] using this)
  have hsignK : ∀ x ∈ K, g x = boolSign (decide (0 < g x)) * E := by
    intro x hx
    have hEp : 0 < E := by simpa [E] using hE
    rcases (abs_eq hEp.le).mp hx.2 with hp | hn
    · rw [hp]
      simp [boolSign, hEp]
    · rw [hn]
      have hnot : ¬0 < -E := by linarith
      simp [boolSign, hnot]
  by_cases hPne : P.Nonempty
  case neg =>
    refine ⟨C (-1), by simp, ?_⟩
    intro x hxI hxE
    have hxK : x ∈ K := ⟨hxI, by simpa [E] using hxE⟩
    have hxsign := hsignK x hxK
    have hcolor : decide (0 < g x) = false := by
      by_contra h
      have ht : decide (0 < g x) = true := Bool.eq_true_of_not_eq_false h
      have : g x = E := by simpa [boolSign, ht] using hxsign
      exact hPne ⟨x, hxK, this⟩
    have hgx : g x = -E := by simpa [boolSign, hcolor] using hxsign
    simp only [eval_C]
    rw [hgx]
    simpa [E] using hE
  by_cases hNne : N.Nonempty
  case neg =>
    refine ⟨C 1, by simp, ?_⟩
    intro x hxI hxE
    have hxK : x ∈ K := ⟨hxI, by simpa [E] using hxE⟩
    have hxsign := hsignK x hxK
    have hcolor : decide (0 < g x) = true := by
      by_contra h
      have hf : decide (0 < g x) = false := Bool.eq_false_of_not_eq_true h
      have : g x = -E := by simpa [boolSign, hf] using hxsign
      exact hNne ⟨x, hxK, this⟩
    have hgx : g x = E := by simpa [boolSign, hcolor] using hxsign
    simp only [eval_C]
    rw [hgx]
    simpa [E] using hE
  obtain ⟨δ, hδ, hdist⟩ :
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ P, ∀ y ∈ N, δ < |x - y| := by
    obtain ⟨d, hd, hd'⟩ :=
      Metric.exists_pos_forall_lt_edist hPcompact hNcompact.isClosed hPN
    refine ⟨(d : ℝ), by exact_mod_cast hd, ?_⟩
    intro x hx y hy
    simpa [edist_dist, Real.dist_eq] using hd' x hx y hy
  let ε := δ / 5
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover
    (fun z : K ↦ Metric.ball (z : ℝ) ε) (fun _ ↦ Metric.isOpen_ball) (by
      intro x hx
      rw [Set.mem_iUnion]
      exact ⟨⟨x, hx⟩, Metric.mem_ball_self hε⟩)
  let centers : Finset ℝ := t.map ⟨Subtype.val, Subtype.val_injective⟩
  let l : List ℝ := centers.sort
  let color : ℝ → Bool := fun x ↦ decide (0 < g x)
  have hlK : ∀ c ∈ l, c ∈ K := by
    intro c hc
    have hc' : c ∈ centers := (Finset.mem_sort (· ≤ ·)).mp hc
    rcases Finset.mem_map.mp hc' with ⟨z, hz, rfl⟩
    exact z.2
  have hcover : ∀ x ∈ K, ∃ c ∈ l, |x - c| < ε := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (ht hx) with ⟨z, hz, hxz⟩
    refine ⟨z, ?_, ?_⟩
    · apply (Finset.mem_sort (· ≤ ·)).mpr
      exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
    · simpa [Metric.mem_ball, Real.dist_eq] using hxz
  have hlne : l ≠ [] := by
    intro hl
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨c, hc, -⟩ := hcover x hx
    simpa [hl] using hc
  have hlsort : l.Pairwise (· < ·) := by
    simpa [l] using (Finset.sortedLT_sort centers).pairwise
  have hlsep : ∀ a ∈ l, ∀ b ∈ l, color a ≠ color b → 4 * ε < |a - b| := by
    intro a ha b hb hab
    have haK := hlK a ha
    have hbK := hlK b hb
    have hga := hsignK a haK
    have hgb := hsignK b hbK
    dsimp [color] at hab ⊢
    cases hca : decide (0 < g a) <;> cases hcb : decide (0 < g b)
    · exfalso
      apply hab
      rw [hca, hcb]
    · have haN : a ∈ N := ⟨haK, by simpa [boolSign, hca] using hga⟩
      have hbP : b ∈ P := ⟨hbK, by simpa [boolSign, hcb] using hgb⟩
      have hd := hdist b hbP a haN
      rw [abs_sub_comm] at hd
      dsimp [ε]
      linarith
    · have haP : a ∈ P := ⟨haK, by simpa [boolSign, hca] using hga⟩
      have hbN : b ∈ N := ⟨hbK, by simpa [boolSign, hcb] using hgb⟩
      have hd := hdist a haP b hbN
      dsimp [ε]
      linarith
    · exfalso
      apply hab
      rw [hca, hcb]
  have hchanges : signChanges color l ≤ L := by
    by_contra hle
    have hlt : L < signChanges color l := Nat.lt_of_not_ge hle
    cases hl : l with
    | nil => simp [hl, signChanges] at hlt
    | cons a tail =>
      have hsortCons : (a :: tail).Pairwise (· < ·) := by simpa [hl] using hlsort
      obtain ⟨w, hwlen, hword, hwchain, hwmem⟩ :=
        exists_alternating_sublist_of_lt_signChanges color hsortCons (by simpa [hl] using hlt)
      let nodes : Fin (L + 2) → ℝ := fun i ↦
        (a :: w).get ⟨i, by simpa [hwlen] using i.isLt⟩
      have hnodesK : ∀ i, nodes i ∈ K := by
        intro i
        apply hlK _ (by rw [hl]; exact hwmem _ (List.get_mem _ _))
      have hnodesMono : StrictMono nodes := by
        intro i j hij
        exact hword.rel_get_of_lt hij
      have hnodeSigns := boolSign_get_eq_of_chain color hwchain
      apply hno
      refine ⟨nodes, boolSign (color a), hnodesMono, ?_, ?_, ?_⟩
      · intro i
        exact hKsub (hnodesK i)
      · cases color a <;> simp [boolSign]
      · intro i
        have hgNode := hsignK (nodes i) (hnodesK i)
        have hsNode := hnodeSigns ⟨i, by simpa [hwlen] using i.isLt⟩
        dsimp [nodes] at hgNode ⊢
        rw [hgNode]
        change boolSign (color ((a :: w).get ⟨i, _⟩)) * E =
          boolSign (color a) * (-1 : ℝ) ^ (i : ℕ) * intervalSupNorm g r s
        rw [hsNode]
  cases hl : l with
  | nil => exact (hlne hl).elim
  | cons a tail =>
    let Q := listSignPolynomial color (a :: tail)
    have hchanges' : signChanges color (a :: tail) ≤ L := by simpa [hl] using hchanges
    have hlsort' : (a :: tail).Pairwise (· < ·) := by simpa [hl] using hlsort
    have hlsep' : ∀ u ∈ a :: tail, ∀ v ∈ a :: tail,
        color u ≠ color v → 4 * ε < |u - v| := by simpa [hl] using hlsep
    refine ⟨Q, (listSignPolynomial_degree color (a :: tail)).trans hchanges', ?_⟩
    have hQsign := listSignPolynomial_sign color ε (a :: tail) hε (by simp) hlsort' hlsep'
    intro x hxI hxE
    have hxK : x ∈ K := ⟨hxI, by simpa [E] using hxE⟩
    obtain ⟨c, hc, hxc⟩ := hcover x hxK
    have hcK := hlK c hc
    have hsame : color x = color c := by
      by_contra hne
      have hxsign := hsignK x hxK
      have hcsign := hsignK c hcK
      dsimp [color] at hne ⊢
      cases hcx : decide (0 < g x) <;> cases hcc : decide (0 < g c)
      · exfalso
        apply hne
        rw [hcx, hcc]
      · have hxN : x ∈ N := ⟨hxK, by simpa [boolSign, hcx] using hxsign⟩
        have hcP : c ∈ P := ⟨hcK, by simpa [boolSign, hcc] using hcsign⟩
        have hd := hdist c hcP x hxN
        rw [abs_sub_comm] at hd
        dsimp [ε] at hxc
        linarith
      · have hxP : x ∈ P := ⟨hxK, by simpa [boolSign, hcx] using hxsign⟩
        have hcN : c ∈ N := ⟨hcK, by simpa [boolSign, hcc] using hcsign⟩
        have hd := hdist x hxP c hcN
        dsimp [ε] at hxc
        linarith
      · exfalso
        apply hne
        rw [hcx, hcc]
    have hc' : c ∈ a :: tail := by simpa [hl] using hc
    have hpoly := hQsign.2 c hc' x hxc
    have hxsign := hsignK x hxK
    dsimp [Q]
    rw [hxsign]
    change 0 < boolSign (color x) * E * (listSignPolynomial color (a :: tail)).eval x
    rw [hsame]
    have hp := mul_pos (show 0 < E by simpa [E] using hE) hpoly
    rw [show boolSign (color c) * E *
      (listSignPolynomial color (a :: tail)).eval x =
      E * (boolSign (color c) * (listSignPolynomial color (a :: tail)).eval x) by ring]
    exact hp

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
