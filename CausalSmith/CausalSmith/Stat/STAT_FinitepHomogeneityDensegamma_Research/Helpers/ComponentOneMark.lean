module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentCancellations

/-! Exact cancellation of the even full-record discrepancy for at most one mark. -/
public section
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A single outcome coefficient can be averaged by replacing just its local marginal with its signed first moment; all remaining outcome coefficients use their ordinary marginals. [This is the stated conclusion](goal). -/
-- @node: finite_pair_average_one_snd
lemma finite_pair_average_one_snd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Bool → Bool → ℝ) (j : ι) (F : (ι → Bool) → ℝ) :
    (∑ p : ι → Bool × Bool, (∏ i, w i (p i).1 (p i).2) *
      (F (fun i => (p i).1) * signVal (p j).2)) =
    ∑ l : ι → Bool, (∏ i, ∑ h : Bool,
      w i (l i) h * (if i = j then signVal h else 1)) * F l := by
  have he (p : ι → Bool × Bool) :
      (∏ i, w i (p i).1 (p i).2) * (F (fun i => (p i).1) * signVal (p j).2) =
      (∏ i, w i (p i).1 (p i).2 * (if i = j then signVal (p i).2 else 1)) *
        F (fun i => (p i).1) := by
    rw [Finset.prod_mul_distrib]
    rw [Fintype.prod_ite_eq']
    ring
  simp_rw [he]
  exact finite_pair_average_fst
    (fun i l h => w i l h * (if i = j then signVal h else 1))
    (fun i l => ∑ h : Bool, w i l h * (if i = j then signVal h else 1))
    (fun _ _ => rfl) F

/-- The constant positive and negative coarse signs give opposite tent fields. [This is the stated conclusion](goal). -/
-- @node: coarseTent_constant_sign_neg
lemma coarseTent_constant_sign_neg (M : ℕ) (x : ℝ) :
    coarseTent M (fun _ => false) x = -coarseTent M (fun _ => true) x := by
  simp [coarseTent, signVal, Finset.sum_neg_distrib]

/-- The interpolated tent changes sign together with the coarse field. [This is the stated conclusion](goal). -/
-- @node: smoothedTent_constant_sign_neg
lemma smoothedTent_constant_sign_neg (K M : ℕ) (x : ℝ) :
    smoothedTent K M (fun _ => false) x = -smoothedTent K M (fun _ => true) x := by
  simp only [smoothedTent, coarseTent_constant_sign_neg, neg_mul, Finset.sum_neg_distrib]

/-- A single outcome sign has the null conditional first moment after the two coarse signs are averaged, even when other propensity signs are retained in an arbitrary function. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_one_snd_even
lemma conditionalPairWeight_one_snd_even (K M : ℕ) (δ : Disclosure K)
    (j : Fin (K+1)) (F : (Fin (K+1) → Bool) → ℝ) :
    (∑ p : CoefficientPairs K, conditionalPairWeight true K M (fun _ => true) δ p *
      (F (fun i => (p i).1) * signVal (p j).2)) +
    (∑ p : CoefficientPairs K, conditionalPairWeight true K M (fun _ => false) δ p *
      (F (fun i => (p i).1) * signVal (p j).2)) =
    2 * ∑ p : CoefficientPairs K, conditionalPairWeight false K M (fun _ => false) δ p *
      (F (fun i => (p i).1) * signVal (p j).2) := by
  classical
  let w (ν s : Bool) (i : Fin (K+1)) (l h : Bool) : ℝ :=
    match δ i with
    | some q => if (l,h) = q then 1 else 0
    | none => pairWeight ν (coarseTent M (fun _ => s) ((i:ℝ)/K)) l h
  let m (ν s : Bool) (i : Fin (K+1)) (l : Bool) : ℝ :=
    ∑ h : Bool, w ν s i l h * (if i = j then signVal h else 1)
  have hn (ν s : Bool) (i : Fin (K+1)) (l : Bool) (hi : i ≠ j) :
      m ν s i l = m false false i l := by
    simp only [m, if_neg hi, mul_one]
    cases hd : δ i with
    | some q => simp only [w, hd]
    | none => simp only [w, hd, pairWeight_fst_sum]
  have hj (l : Bool) : m true true j l + m true false j l = 2*m false false j l := by
    simp only [m, if_pos rfl]
    cases hd : δ j with
    | some q => simp only [w, hd]; ring
    | none =>
      simp only [w, hd, coarseTent_constant_sign_neg]
      cases l <;> simp [pairWeight, signVal] <;> ring
  have hp (l : Fin (K+1) → Bool) :
      (∏ i, m true true i (l i)) + (∏ i, m true false i (l i)) =
        2 * ∏ i, m false false i (l i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have he (ν s : Bool) :
        (∏ i ∈ Finset.univ.erase j, m ν s i (l i)) =
          ∏ i ∈ Finset.univ.erase j, m false false i (l i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hn ν s i (l i) (Finset.mem_erase.mp hi).1
    rw [he true true, he true false, ← add_mul, hj]
    ring
  change (∑ p : CoefficientPairs K, (∏ i, w true true i (p i).1 (p i).2) *
      (F (fun i => (p i).1) * signVal (p j).2)) +
    (∑ p : CoefficientPairs K, (∏ i, w true false i (p i).1 (p i).2) *
      (F (fun i => (p i).1) * signVal (p j).2)) =
    2 * ∑ p : CoefficientPairs K, (∏ i, w false false i (p i).1 (p i).2) *
      (F (fun i => (p i).1) * signVal (p j).2)
  rw [finite_pair_average_one_snd, finite_pair_average_one_snd, finite_pair_average_one_snd]
  change (∑ l, (∏ i, m true true i (l i)) * F l) +
    (∑ l, (∏ i, m true false i (l i)) * F l) =
    2 * ∑ l, (∏ i, m false false i (l i)) * F l
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [← add_mul, hp]
  ring

/-- Averaging opposite coarse signs removes the copula tilt from every likelihood affine in outcome coefficients, together with any odd correction depending only on propensity signs. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_affine_snd_even
lemma conditionalPairWeight_affine_snd_even (K M : ℕ) (δ : Disclosure K)
    (F H : (Fin (K+1) → Bool) → ℝ)
    (G : Fin (K+1) → (Fin (K+1) → Bool) → ℝ) (t : ℝ) :
    let V (ν s : Bool) (p : CoefficientPairs K) :=
      F (fun i => (p i).1) + ∑ j, G j (fun i => (p i).1) * signVal (p j).2 +
        (if ν then (if s then t else -t) else 0) * H (fun i => (p i).1)
    (∑ p, conditionalPairWeight true K M (fun _ => true) δ p * V true true p) +
    (∑ p, conditionalPairWeight true K M (fun _ => false) δ p * V true false p) =
    2 * ∑ p, conditionalPairWeight false K M (fun _ => false) δ p * V false false p := by
  classical
  dsimp only
  have hf (ν s : Bool) (J : (Fin (K+1) → Bool) → ℝ) :
      (∑ p, conditionalPairWeight ν K M (fun _ => s) δ p * J (fun i => (p i).1)) =
      ∑ p, conditionalPairWeight false K M (fun _ => false) δ p * J (fun i => (p i).1) := by
    rw [conditionalPairWeight_fst_average, conditionalPairWeight_fst_average]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero, add_zero, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  simp_rw [Finset.sum_comm (f := fun p j => conditionalPairWeight _ K M _ δ p *
    (G j (fun i => (p i).1) * signVal (p j).2))]
  have ht (ν s : Bool) (c : ℝ) :
      (∑ p, conditionalPairWeight ν K M (fun _ => s) δ p * (c * H (fun i => (p i).1))) =
        c * ∑ p, conditionalPairWeight false K M (fun _ => false) δ p * H (fun i => (p i).1) := by
    simp_rw [mul_left_comm _ c]
    rw [← Finset.mul_sum, hf]
  rw [hf true true F, hf true false F, ht true true t, ht true false (-t)]
  have hg :
      (∑ j, ∑ p, conditionalPairWeight true K M (fun _ => true) δ p *
        (G j (fun i => (p i).1) * signVal (p j).2)) +
      (∑ j, ∑ p, conditionalPairWeight true K M (fun _ => false) δ p *
        (G j (fun i => (p i).1) * signVal (p j).2)) =
      2 * ∑ j, ∑ p, conditionalPairWeight false K M (fun _ => false) δ p *
        (G j (fun i => (p i).1) * signVal (p j).2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => conditionalPairWeight_one_snd_even K M δ j (G j))
  simp only [← Finset.mul_sum]
  have hg0 :
      (∑ p, conditionalPairWeight false K M (fun _ => false) δ p *
        ∑ j, G j (fun i => (p i).1) * signVal (p j).2) =
      ∑ j, ∑ p, conditionalPairWeight false K M (fun _ => false) δ p *
        (G j (fun i => (p i).1) * signVal (p j).2) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hg0]
  linear_combination hg

/-- A component with one specified marked record has identical sign-averaged and null densities. All other records retain their full treatment-label likelihoods. This statement assumes [the hj condition](hyp:hj), [the hmark condition](hyp:hmark), [the hrest condition](hyp:hrest). [This is the stated conclusion](goal). -/
-- @node: componentDensity_one_mark_even
lemma componentDensity_one_mark_even (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n)
    (j : Fin n) (hj : j ∈ C) (hmark : aug.2.1 j = true)
    (hrest : ∀ i ∈ C, i ≠ j → aug.2.1 i = false) :
    componentDensity true true n K M a u aug C labels +
      componentDensity true false n K M a u aug C labels =
        2 * nullComponent n K M a u aug C labels := by
  classical
  let X (l : Fin (K+1) → Bool) (i : Fin n) : ℝ :=
    a * frameField K (fun k => signVal (l k)) (aug.1 i)
  let R (l : Fin (K+1) → Bool) : ℝ :=
    ∏ i ∈ C.erase j, (1 + signVal (labels i).1 * X l i)
  let F (l : Fin (K+1) → Bool) : ℝ := R l * (1 + signVal (labels j).1 * X l j)
  let G (k : Fin (K+1)) (l : Fin (K+1) → Bool) : ℝ :=
    R l * signVal (labels j).2 * u * (1 + signVal (labels j).1 * X l j) *
      frameCoord K k (aug.1 j)
  let H (l : Fin (K+1) → Bool) : ℝ :=
    R l * signVal (labels j).1 * signVal (labels j).2 * (1 - X l j^2)
  let t : ℝ := -a*u*kappa0/(1-a^2)*smoothedTent K M (fun _ => true) (aug.1 j)
  have ht (ν s : Bool) (p : CoefficientPairs K) :
      copulaT ν K M a u ((fun _ => s),p) (aug.1 j) =
        if ν then (if s then t else -t) else 0 := by
    cases ν <;> cases s <;>
      simp [copulaT, smoothedTent_constant_sign_neg, t] <;> ring
  have hprod (ν s : Bool) (p : CoefficientPairs K) :
      (∏ i ∈ C, labelDensity ν K M a u ((fun _ => s),p)
        (aug.1 i) (aug.2.1 i) (labels i)) =
      F (fun k => (p k).1) + ∑ k, G k (fun i => (p i).1) * signVal (p k).2 +
        (if ν then (if s then t else -t) else 0) * H (fun k => (p k).1) := by
    rw [← Finset.mul_prod_erase C _ hj]
    have hr : (∏ i ∈ C.erase j, labelDensity ν K M a u ((fun _ => s),p)
        (aug.1 i) (aug.2.1 i) (labels i)) = R (fun k => (p k).1) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [labelDensity, hrest i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1]
      rfl
    rw [hr]
    simp only [labelDensity, hmark, ↓reduceIte, copulaZeta, ht]
    change (1 + signVal (labels j).1 * X (fun k => (p k).1) j +
      signVal (labels j).2 * (u * ∑ k, signVal (p k).2 * frameCoord K k (aug.1 j)) +
      signVal (labels j).1 * signVal (labels j).2 *
        (X (fun k => (p k).1) j * (u * ∑ k, signVal (p k).2 * frameCoord K k (aug.1 j)) +
          (if ν then (if s then t else -t) else 0) * (1-X (fun k => (p k).1) j^2))) *
        R (fun k => (p k).1) = _
    have hg : (∑ k, G k (fun i => (p i).1) * signVal (p k).2) =
        R (fun k => (p k).1) * signVal (labels j).2 * u *
          (1 + signVal (labels j).1 * X (fun k => (p k).1) j) *
            ∑ k, signVal (p k).2 * frameCoord K k (aug.1 j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [G]
      ring
    rw [hg]
    dsimp only [F, H]
    ring
  unfold nullComponent componentDensity
  simp_rw [hprod]
  exact conditionalPairWeight_affine_snd_even K M aug.2.2 F H G t

/-- At most one marked record forces the even discrepancy to vanish exactly, at every amplitude and every disclosed design. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: evenDiscrepancy_at_most_one_mark
lemma evenDiscrepancy_at_most_one_mark (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n)
    (hm : (C.filter (fun i => aug.2.1 i)).card ≤ 1) :
    evenDiscrepancy n K M a u aug C labels = 0 := by
  classical
  by_cases hz : (C.filter (fun i => aug.2.1 i)).card = 0
  · exact (component_discrepancies_no_marks n K M a u aug C labels hz).1
  have hone : (C.filter (fun i => aug.2.1 i)).card = 1 := by omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
  have hjmem : j ∈ C ∧ aug.2.1 j = true := by
    have : j ∈ C.filter (fun i => aug.2.1 i) := by rw [hj]; simp
    exact Finset.mem_filter.mp this
  have hrest : ∀ i ∈ C, i ≠ j → aug.2.1 i = false := by
    intro i hi hij
    by_cases h : aug.2.1 i = true
    · have : i ∈ C.filter (fun i => aug.2.1 i) := Finset.mem_filter.mpr ⟨hi, h⟩
      rw [hj] at this
      exact False.elim (hij (Finset.mem_singleton.mp this))
    · exact Bool.eq_false_iff.mpr h
  have he := componentDensity_one_mark_even n K M a u aug C labels j hjmem.1 hjmem.2 hrest
  unfold evenDiscrepancy averageComponent
  rw [he]
  ring

/-- Components with fewer than two marked records contribute exactly zero even chi-square activity, establishing the two-mark rarity restriction before occupancy counting. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: componentEvenActivity_at_most_one_mark
lemma componentEvenActivity_at_most_one_mark (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n))
    (hm : (C.filter (fun i => aug.2.1 i)).card ≤ 1) :
    componentEvenActivity n K M a u aug C = 0 := by
  have hz := fun labels => evenDiscrepancy_at_most_one_mark n K M a u aug C labels hm
  simp only [componentEvenActivity, hz, zero_pow (by decide : 2 ≠ 0),
    zero_div, Finset.sum_const_zero, mul_zero]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
