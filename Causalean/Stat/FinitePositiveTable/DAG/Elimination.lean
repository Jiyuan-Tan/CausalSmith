module
public import Causalean.Stat.FinitePositiveTable.DAG.Basic

/-!
# Reverse-topological elimination for truncated finite DAG products

This module isolates the finite-sum algebra behind DAG fixing.  A maximal remaining vertex can
be summed out because no other remaining local factor depends on it and its own local row is
normalized.  Iterating this reverse-topological step normalizes every row of a truncated product
and identifies the conditional mass used by graph-independent fixing with the vertex's local
factor.
-/

public section

open Finset
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.FinitePositiveTable.DAG

open Causalean.Graph
open Causalean.Graph.FiniteDensity
open Causalean.Mathlib.MeasureTheory.FiniteCoordinate
open Causalean.Stat.FinitePositiveTable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {r : V → ℕ}
variable {G : DAG V} {p : PositiveTable r}

namespace PositiveDAGTableFactorization

/-- A [factorized table](hyp:fac) and [fixed vertex set](hyp:fixed) give [strictly positive mass
at every profile for the truncated product kernel](goal). -/
theorem remainingFactorKernel_pos (fac : PositiveDAGTableFactorization G p)
    (fixed : Finset V) :
    (fac.remainingFactorKernel fixed).IsStrictlyPositive := by
  intro x
  exact Finset.prod_pos fun v _ ↦ fac.mechanism.factor_pos v x

/-- A [kernel](hyp:q), [coordinate outside the marginal set](hyp:hv), and [reference profile](hyp:x)
give [the finite decomposition of its marginal across that coordinate's states](goal). -/
theorem kernelMarginalMass_decompose (q : Kernel r) {S : Finset V} {v : V}
    (hv : v ∉ S) (x : ProfileSpace r) :
    (∑ z : Fin (r v),
      kernelMarginalMass q (insert v S) (Function.update x v z)) =
      kernelMarginalMass q S x := by
  simpa [kernelMarginalMass] using sum_fiberSum_insert_update q hv x

/-- Two [kernels](hyp:q,qNext), [a coordinate outside the marginal set](hyp:hv), [a pointwise
coordinate-summation identity](hyp:hsum), and [reference profile](hyp:x) give [the corresponding
elimination identity for kernel marginals](goal). -/
theorem kernelMarginalMass_eliminate_coordinate
    (q qNext : Kernel r) {S : Finset V} {v : V} (hv : v ∉ S)
    (hsum : ∀ y, (∑ z : Fin (r v), q (Function.update y v z)) = qNext y)
    (x : ProfileSpace r) :
    kernelMarginalMass q S x = kernelMarginalMass qNext (insert v S) x := by
  classical
  let e := Equiv.piSplitAt v (fun i ↦ Fin (r i))
  let base (t : ∀ j : {j // j ≠ v}, Fin (r j)) : ProfileSpace r :=
    e.symm (x v, t)
  have hbase_v (t : ∀ j : {j // j ≠ v}, Fin (r j)) : base t v = x v := by
    simp [base, e, Equiv.piSplitAt]
  have hupdate (t : ∀ j : {j // j ≠ v}, Fin (r j)) (z : Fin (r v)) :
      Function.update (base t) v z = e.symm (z, t) := by
    funext i
    by_cases hiv : i = v
    · subst i
      simp [base, e, Equiv.piSplitAt]
    · simp [base, e, Equiv.piSplitAt, hiv]
  have hagree (t : ∀ j : {j // j ≠ v}, Fin (r j)) (z : Fin (r v)) :
      AgreeOn S (e.symm (z, t)) x ↔ AgreeOn S (base t) x := by
    constructor <;> intro h w hw
    · simpa only [← hupdate t z, Function.update_of_ne
        (ne_of_mem_of_not_mem hw hv)] using h w hw
    · have hwv : w ≠ v := ne_of_mem_of_not_mem hw hv
      simpa only [← hupdate t z, Function.update_of_ne hwv] using h w hw
  have hagree_insert (t : ∀ j : {j // j ≠ v}, Fin (r j)) (z : Fin (r v)) :
      AgreeOn (insert v S) (e.symm (z, t)) x ↔
        z = x v ∧ AgreeOn S (base t) x := by
    rw [← hupdate t z]
    constructor
    · intro h
      constructor
      · simpa using h v (mem_insert_self v S)
      · intro w hw
        have hwv : w ≠ v := ne_of_mem_of_not_mem hw hv
        simpa only [Function.update_of_ne hwv] using h w (mem_insert_of_mem hw)
    · rintro ⟨rfl, h⟩ w hw
      rcases mem_insert.mp hw with rfl | hw
      · simp
      · have hwv : w ≠ v := ne_of_mem_of_not_mem hw hv
        simpa only [Function.update_of_ne hwv] using h w hw
  unfold kernelMarginalMass fiberSum
  calc
    (∑ y : ProfileSpace r, if AgreeOn S y x then q y else 0) =
        ∑ a : Fin (r v) × (∀ j : {j // j ≠ v}, Fin (r j)),
          if AgreeOn S (e.symm a) x then q (e.symm a) else 0 := by
            exact Fintype.sum_equiv e _ _ (fun y ↦ by simp)
    _ = ∑ t : (∀ j : {j // j ≠ v}, Fin (r j)),
        ∑ z : Fin (r v),
          if AgreeOn S (e.symm (z, t)) x then q (e.symm (z, t)) else 0 := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ t : (∀ j : {j // j ≠ v}, Fin (r j)),
        if AgreeOn S (base t) x then qNext (base t) else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          simp_rw [hagree t]
          split_ifs with h
          · simp_rw [← hupdate t]
            exact hsum (base t)
          · simp
    _ = ∑ a : Fin (r v) × (∀ j : {j // j ≠ v}, Fin (r j)),
          if AgreeOn (insert v S) (e.symm a) x then qNext (e.symm a) else 0 := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro t ht
            simp_rw [hagree_insert t]
            rw [Finset.sum_eq_single (x v)]
            · simp [base]
            · intro z hz hne
              simp [hne]
            · intro hnot
              exact (hnot (Finset.mem_univ _)).elim
    _ = ∑ y : ProfileSpace r,
          if AgreeOn (insert v S) y x then qNext y else 0 := by
            symm
            exact Fintype.sum_equiv e _ _ (fun y ↦ by simp)

/-- A [DAG](hyp:G), [fixed vertex set](hyp:fixed), and [nonempty set of remaining vertices](hyp:hne)
give [a remaining vertex with no remaining child](goal). -/
theorem exists_remaining_sink (G : DAG V) (fixed : Finset V)
    (hne : (Finset.univ \ fixed).Nonempty) :
    ∃ v, v ∉ fixed ∧ ∀ w, w ∉ fixed → ¬ G.edge v w := by
  /-
  Choose a vertex maximizing `G.topoOrder` on `univ \ fixed`.  An edge to another remaining
  vertex would strictly increase `topoOrder`, contradicting maximality.  `Finset.exists_max_image`
  is the same selection lemma used by the ordered-local d-separation closure.
  -/
  obtain ⟨v, hv, hmax⟩ :=
    Finset.exists_max_image (Finset.univ \ fixed) G.topoOrder hne
  refine ⟨v, (Finset.mem_sdiff.mp hv).2, ?_⟩
  intro w hw hEdge
  have hwRemaining : w ∈ Finset.univ \ fixed :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩
  exact (not_lt_of_ge (hmax w hwRemaining)) (G.topoOrder_lt v w hEdge)

/-- A [factorized table](hyp:fac), [fixed vertex set](hyp:fixed), [remaining vertex](hyp:hv),
[proof that it has no remaining child](hyp:hsink), and [profile](hyp:x) give [the identity
obtained by summing out that sink's local factor](goal). -/
theorem sum_remainingFactorKernel_sink
    (fac : PositiveDAGTableFactorization G p) (fixed : Finset V) {v : V}
    (hv : v ∉ fixed) (hsink : ∀ w, w ∉ fixed → ¬ G.edge v w)
    (x : ProfileSpace r) :
    (∑ z : Fin (r v),
      fac.remainingFactorKernel fixed (Function.update x v z)) =
      fac.remainingFactorKernel (insert v fixed) x := by
  /-
  Split the product into the factor at `v` and the remaining factors.  For any remaining
  `w ≠ v`, locality of factor `w` and `hsink w` show that updating `v` does not change it.
  Pull this common product outside the sum and apply `factor_normalized v x`.
  -/
  let S : Finset V := Finset.univ \ fixed
  have hvS : v ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
  have hrest (z : Fin (r v)) :
      (∏ w ∈ S.erase v,
        fac.mechanism.factor w (Function.update x v z)) =
      ∏ w ∈ S.erase v, fac.mechanism.factor w x := by
    apply Finset.prod_congr rfl
    intro w hw
    apply fac.mechanism.factor_local w
    intro i hi
    have hwS : w ∈ S := Finset.mem_of_mem_erase hw
    have hwFixed : w ∉ fixed := (Finset.mem_sdiff.mp hwS).2
    have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
    have hvNotLocal : v ∉ insert w (G.parents w) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨Ne.symm hwne, fun hvParent ↦
        hsink w hwFixed (G.mem_parents.mp hvParent)⟩
    have hine : i ≠ v := fun hiv ↦ hvNotLocal (hiv ▸ hi)
    exact Function.update_of_ne hine z x
  rw [remainingFactorKernel]
  simp only [S] at hvS hrest ⊢
  calc
    (∑ z : Fin (r v),
        ∏ w ∈ (Finset.univ \ fixed),
          fac.mechanism.factor w (Function.update x v z)) =
      ∑ z : Fin (r v),
        fac.mechanism.factor v (Function.update x v z) *
          ∏ w ∈ (Finset.univ \ fixed).erase v,
            fac.mechanism.factor w (Function.update x v z) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact (Finset.mul_prod_erase (Finset.univ \ fixed)
                (fun w ↦ fac.mechanism.factor w (Function.update x v z)) hvS).symm
    _ = ∑ z : Fin (r v),
        fac.mechanism.factor v (Function.update x v z) *
          ∏ w ∈ (Finset.univ \ fixed).erase v,
            fac.mechanism.factor w x := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [hrest z]
    _ = (∑ z : Fin (r v),
          fac.mechanism.factor v (Function.update x v z)) *
        ∏ w ∈ (Finset.univ \ fixed).erase v,
          fac.mechanism.factor w x := by
            rw [Finset.sum_mul]
    _ = ∏ w ∈ (Finset.univ \ fixed).erase v,
          fac.mechanism.factor w x := by
            rw [fac.mechanism.factor_normalized, one_mul]
    _ = ∏ w ∈ (Finset.univ \ insert v fixed),
          fac.mechanism.factor w x := by
            congr 1
            ext w
            simp

/-- A [factorized table](hyp:fac), [fixed vertex set](hyp:fixed), and [profile](hyp:x) give
[unit total mass for the truncated product in that fixed-coordinate row](goal). -/
theorem remainingFactorKernel_row_normalized
    (fac : PositiveDAGTableFactorization G p) (fixed : Finset V)
    (x : ProfileSpace r) :
    kernelMarginalMass (fac.remainingFactorKernel fixed) fixed x = 1 := by
  /-
  Induct on `card (univ \ fixed)`.  The empty case reduces the fibre to `x` and the empty
  product to one.  Otherwise select `exists_remaining_sink`, partition the fibre with
  `kernelMarginalMass_decompose`, rewrite each summand by `sum_remainingFactorKernel_sink`,
  and apply the induction hypothesis to `insert v fixed`.
  -/
  classical
  induction hcard : (Finset.univ \ fixed).card using Nat.strong_induction_on generalizing fixed x with
  | h n ih =>
      by_cases hne : (Finset.univ \ fixed).Nonempty
      · obtain ⟨v, hv, hsink⟩ := exists_remaining_sink G fixed hne
        have hlt : (Finset.univ \ insert v fixed).card < n := by
          rw [← hcard]
          simpa [Finset.sdiff_insert] using
            Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩)
        rw [kernelMarginalMass_eliminate_coordinate
          (fac.remainingFactorKernel fixed)
          (fac.remainingFactorKernel (insert v fixed)) (S := fixed) (v := v) hv
          (fac.sum_remainingFactorKernel_sink fixed hv hsink) x]
        exact ih _ hlt (insert v fixed) x rfl
      · have hempty : Finset.univ \ fixed = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hfixed : fixed = Finset.univ := by
          ext w
          simpa using congrArg (w ∈ ·) hempty
        subst fixed
        rw [kernelMarginalMass, fiberSum_univ, remainingFactorKernel]
        simp

/-- A [factorized table](hyp:fac), [fixed vertex set](hyp:fixed), [proof that the vertex remains
random](hyp:hv), [profile](hyp:x), and [proposed vertex state](hyp:z) give [the equality between
the truncated kernel's parent-conditional mass and its normalized local factor](goal). -/
theorem remainingFactorKernel_conditionalMass_eq_factor
    (fac : PositiveDAGTableFactorization G p) (fixed : Finset V) {v : V}
    (hv : v ∉ fixed) (x : ProfileSpace r) (z : Fin (r v)) :
    kernelConditionalMass (fac.remainingFactorKernel fixed)
        v (G.parents v) x z =
      fac.mechanism.factor v (Function.update x v z) := by
  /-
  Expand numerator and denominator as truncated-product fibre sums.  Reverse-topologically
  eliminate every remaining vertex except `v` and its parents; locality makes the surviving
  numerator equal the factor at `v` times the denominator.  Strict positivity from
  `remainingFactorKernel_pos` cancels the denominator.  This is the finite-table form of the
  ordered local Markov calculation and should reuse `remainingFactorKernel_row_normalized`.
  -/
  classical
  let (i : V) : Nonempty (Fin (r i)) :=
    ⟨⟨0, fac.cardinalitiesPositive i⟩⟩
  let M : PositiveFiniteDAGMechanism G (fun i ↦ Fin (r i)) :=
    { factor := fun i y ↦
        if i ∈ fixed then (r i : ℝ)⁻¹ else fac.mechanism.factor i y
      factor_pos := by
        intro i y
        split_ifs with hi
        · exact inv_pos.mpr (Nat.cast_pos.mpr (fac.cardinalitiesPositive i))
        · exact fac.mechanism.factor_pos i y
      factor_normalized := by
        intro i y
        by_cases hi : i ∈ fixed
        · simp only [hi, if_pos]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
            (Nat.ne_of_gt (fac.cardinalitiesPositive i)))
        · simp only [hi]
          exact fac.mechanism.factor_normalized i y
      factor_local := by
        intro i y y' hyy'
        by_cases hi : i ∈ fixed
        · simp [hi]
        · simp only [hi]
          exact fac.mechanism.factor_local i hyy' }
  let c : ℝ := ∏ i ∈ fixed, (r i : ℝ)⁻¹
  have hcpos : 0 < c := by
    exact Finset.prod_pos fun i hi ↦
      inv_pos.mpr (Nat.cast_pos.mpr (fac.cardinalitiesPositive i))
  have hjoint (y : ProfileSpace r) :
      M.jointMass y = c * fac.remainingFactorKernel fixed y := by
    unfold PositiveFiniteDAGMechanism.jointMass remainingFactorKernel c M
    rw [Finset.prod_ite]
    congr 1
    · congr 1
      ext i
      simp
    · congr 1
      ext i
      simp
  have hagree_iff_projection (S : Finset V) (a y : ProfileSpace r) :
      AgreeOn S y a ↔
        coordinateProjection (X := fun i ↦ Fin (r i)) S y =
          coordinateProjection (X := fun i ↦ Fin (r i)) S a := by
    constructor
    · intro h
      funext w
      exact h w w.property
    · intro h w hw
      exact congrFun h ⟨w, hw⟩
  have hmarginal (S : Finset V) (a : ProfileSpace r) :
      M.marginalMass S a = c * kernelMarginalMass
        (fac.remainingFactorKernel fixed) S a := by
    unfold PositiveFiniteDAGMechanism.marginalMass kernelMarginalMass fiberSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hjoint]
    by_cases hya : AgreeOn S y a
    · have hp := (hagree_iff_projection S a y).mp hya
      simp [hya, hp]
    · have hp : coordinateProjection (X := fun i ↦ Fin (r i)) S y ≠
          coordinateProjection (X := fun i ↦ Fin (r i)) S a :=
        fun hp ↦ hya ((hagree_iff_projection S a y).mpr hp)
      simp [hya, hp]
  have hcond := M.conditionalMass_given_parents v x z
  unfold PositiveFiniteDAGMechanism.conditionalMass at hcond
  rw [hmarginal, hmarginal] at hcond
  rw [mul_div_mul_left _ _ hcpos.ne'] at hcond
  unfold kernelConditionalMass
  simpa [M, hv] using hcond

/-- A [factorized table](hyp:fac), [fixed vertex set](hyp:fixed), and [proof that the vertex is
not fixed already](hyp:hv) give [the parent-conditioned fixing identity that removes its local
factor](goal). -/
theorem fixKernelCoordinate_remainingFactorKernel
    (fac : PositiveDAGTableFactorization G p) (fixed : Finset V) {v : V}
    (hv : v ∉ fixed) :
    fixKernelCoordinate (fac.remainingFactorKernel fixed) v (G.parents v) =
      fac.remainingFactorKernel (insert v fixed) := by
  /-
  Extensionality, `fixKernelCoordinate_apply`, and
  `remainingFactorKernel_conditionalMass_eq_factor` reduce the claim to cancelling the
  positive factor at `v` from the finite product.  Use `Finset.prod_erase` (or the corresponding
  insert/sdiff product lemma) and `factor_pos.ne'`.
  -/
  funext x
  rw [fixKernelCoordinate_apply,
    fac.remainingFactorKernel_conditionalMass_eq_factor fixed hv x (x v)]
  simp only [Function.update_eq_self]
  unfold remainingFactorKernel
  have hvRemaining : v ∈ Finset.univ \ fixed :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
  have hsets : Finset.univ \ insert v fixed = (Finset.univ \ fixed).erase v := by
    ext w
    simp
  rw [hsets, ← Finset.mul_prod_erase (Finset.univ \ fixed)
    (fun w ↦ fac.mechanism.factor w x) hvRemaining]
  exact mul_div_cancel_left₀ _ (fac.mechanism.factor_pos v x).ne'

end PositiveDAGTableFactorization

end Causalean.Stat.FinitePositiveTable.DAG
