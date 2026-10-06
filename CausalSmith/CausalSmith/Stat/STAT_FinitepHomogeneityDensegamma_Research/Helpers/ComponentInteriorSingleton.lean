module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentCoefficientMoments

/-! Exact singleton cancellation when every active frame coefficient is undisclosed. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- An undisclosed active frame has zero coordinate-field means and unit propensity energy; its mixed moment is precisely the squared-frame interpolation of the copula correlation. This statement assumes [the hK condition](hyp:hK), [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_active_frame_moments
lemma conditionalPairWeight_active_frame_moments (ν : Bool) (K M : ℕ)
    (hK : 0 < K) (σ : Fin (M/2) → Bool) (δ : Disclosure K) (x : unitInterval)
    (hd : ∀ i, frameCoord K i x ≠ 0 → δ i = none) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      frameField K (fun i => signVal (p i).1) x) = 0 ∧
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      frameField K (fun i => signVal (p i).2) x) = 0 ∧
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      (frameField K (fun i => signVal (p i).1) x)^2) = 1 ∧
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      (frameField K (fun i => signVal (p i).1) x *
        frameField K (fun i => signVal (p i).2) x)) =
      (if ν then 1 else 0) * kappa0 * smoothedTent K M σ x := by
  let w := conditionalPairWeight ν K M σ δ
  let f := fun i : Fin (K+1) => frameCoord K i x
  have hfirst (r : Bool) :
      (∑ p : CoefficientPairs K, w p *
        frameField K (fun i => signVal (if r then (p i).1 else (p i).2)) x) = 0 := by
    simp only [frameField, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hz : frameCoord K i x = 0
    · simp [hz]
    · simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      have hm := conditionalPairWeight_undisclosed_node_moments ν K M σ δ i (hd i hz)
      cases r
      · change (∑ p, w p * signVal (p i).2) * frameCoord K i x = 0
        rw [hm.2.1, zero_mul]
      · change (∑ p, w p * signVal (p i).1) * frameCoord K i x = 0
        rw [hm.1, zero_mul]
  have hoff (i j : Fin (K+1)) (hij : i ≠ j) (r s : Bool) :
      (∑ p : CoefficientPairs K, w p *
        ((signVal (if r then (p i).1 else (p i).2) * f i) *
          (signVal (if s then (p j).1 else (p j).2) * f j))) = 0 := by
    by_cases hi : f i = 0
    · simp [hi]
    by_cases hj : f j = 0
    · simp [hj]
    have hm := conditionalPairWeight_distinct_undisclosed_moment ν K M σ δ i j hij
      (hd i hi) (hd j hj) r s
    have he (p : CoefficientPairs K) : w p *
        ((signVal (if r then (p i).1 else (p i).2) * f i) *
          (signVal (if s then (p j).1 else (p j).2) * f j)) =
        (w p * (signVal (if r then (p i).1 else (p i).2) *
          signVal (if s then (p j).1 else (p j).2))) * (f i * f j) := by ring
    simp_rw [he]
    rw [← Finset.sum_mul, hm, zero_mul]
  have hexpand (r s : Bool) :
      (∑ p : CoefficientPairs K, w p *
        (frameField K (fun i => signVal (if r then (p i).1 else (p i).2)) x *
          frameField K (fun i => signVal (if s then (p i).1 else (p i).2)) x)) =
        ∑ i, ∑ p : CoefficientPairs K, w p *
          ((signVal (if r then (p i).1 else (p i).2) * f i) *
            (signVal (if s then (p i).1 else (p i).2) * f i)) := by
    simp only [frameField, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    exact Finset.sum_eq_single i
      (fun j _ hji => hoff j i hji r s) (by simp)
  dsimp only [w] at hexpand
  refine ⟨by simpa using hfirst true, by simpa using hfirst false, ?_, ?_⟩
  · simp_rw [pow_two]
    have hx := hexpand true true
    simp only [↓reduceIte] at hx
    rw [hx]
    have he (p : CoefficientPairs K) (i : Fin (K+1)) :
        w p * ((signVal (p i).1 * f i) * (signVal (p i).1 * f i)) = w p * f i^2 := by
      have hs : signVal (p i).1^2 = 1 := by cases (p i).1 <;> norm_num [signVal]
      calc
        _ = w p * (signVal (p i).1^2) * f i^2 := by ring
        _ = _ := by rw [hs]; ring
    change (∑ i, ∑ p : CoefficientPairs K, w p *
      ((signVal (p i).1 * f i) * (signVal (p i).1 * f i))) = 1
    simp_rw [he, ← Finset.sum_mul]
    dsimp only [w]
    simp_rw [conditionalPairWeight_sum, one_mul]
    exact frame_partition K hK x
  · have hx := hexpand true false
    simp only [Bool.false_eq_true, ↓reduceIte] at hx
    rw [hx]
    have he (p : CoefficientPairs K) (i : Fin (K+1)) :
        w p * ((signVal (p i).1 * f i) * (signVal (p i).2 * f i)) =
          (w p * (signVal (p i).1 * signVal (p i).2)) * f i^2 := by ring
    change (∑ i, ∑ p : CoefficientPairs K, w p *
      ((signVal (p i).1 * f i) * (signVal (p i).2 * f i))) = _
    simp_rw [he, ← Finset.sum_mul]
    dsimp only [w]
    rw [smoothedTent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f i = 0
    · simp [f] at hi
      simp [f, hi]
    · rw [(conditionalPairWeight_undisclosed_node_moments ν K M σ δ i (hd i hi)).2.2]
      dsimp [f]
      ring

/-- The deterministic effect correction cancels the actual singleton copula mixed moment. All treatment and marked-outcome label categories are retained. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: labelDensity_active_undisclosed_average
lemma labelDensity_active_undisclosed_average (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (σ : Fin (M/2) → Bool) (δ : Disclosure K)
    (x : unitInterval) (hd : ∀ i, frameCoord K i x ≠ 0 → δ i = none)
    (marked : Bool) (label : Bool × Bool) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      labelDensity ν K M a u (σ,p) x marked label) = 1 := by
  let w := conditionalPairWeight ν K M σ δ
  let Λ := fun p : CoefficientPairs K => frameField K (fun i => signVal (p i).1) x
  let H := fun p : CoefficientPairs K => frameField K (fun i => signVal (p i).2) x
  let t : ℝ := -(if ν then 1 else 0)*a*u*kappa0/(1-a^2)*smoothedTent K M σ x
  obtain ⟨hΛ, hH, hΛ2, hΛH⟩ := conditionalPairWeight_active_frame_moments ν K M hK σ δ x hd
  have hs : ∑ p, w p = 1 := conditionalPairWeight_sum ν K M σ δ
  change (∑ p, w p * Λ p) = 0 at hΛ
  change (∑ p, w p * H p) = 0 at hH
  change (∑ p, w p * (Λ p)^2) = 1 at hΛ2
  change (∑ p, w p * (Λ p * H p)) = _ at hΛH
  have ht : a*u*((if ν then 1 else 0)*kappa0*smoothedTent K M σ x) + t*(1-a^2) = 0 := by
    dsimp [t]
    field_simp
    <;> ring
  have hz : (∑ p, w p * copulaZeta ν K M a u (σ,p) x) = 0 := by
    have he (p : CoefficientPairs K) : w p * copulaZeta ν K M a u (σ,p) x =
        (a*u)*(w p*(Λ p*H p)) + t*w p - (t*a^2)*(w p*(Λ p)^2) := by
      dsimp [copulaZeta, copulaXi, copulaUpsilon, copulaT, Λ, H, t]
      ring
    simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hΛH, hs, hΛ2]
    linear_combination ht
  have hx : (∑ p, w p * copulaXi K M a (σ,p) x) = 0 := by
    have he (p : CoefficientPairs K) : w p * copulaXi K M a (σ,p) x = a*(w p*Λ p) := by
      dsimp [copulaXi, Λ]; ring
    simp_rw [he, ← Finset.mul_sum, hΛ, mul_zero]
  have hy : (∑ p, w p * copulaUpsilon K M u (σ,p) x) = 0 := by
    have he (p : CoefficientPairs K) : w p * copulaUpsilon K M u (σ,p) x = u*(w p*H p) := by
      dsimp [copulaUpsilon, H]; ring
    simp_rw [he, ← Finset.mul_sum, hH, mul_zero]
  change (∑ p, w p * labelDensity ν K M a u (σ,p) x marked label) = 1
  cases marked <;>
    simp only [labelDensity, Bool.false_eq_true, ↓reduceIte, mul_add, mul_one,
      Finset.sum_add_distrib] <;>
    simp_rw [mul_left_comm (w _) (signVal _), ← Finset.mul_sum] <;>
    simp [hs, hx, hy, hz, mul_assoc, mul_left_comm]
  simp_rw [mul_left_comm (w _) (signVal _), ← Finset.mul_sum, hz, mul_zero]

/-- For a singleton with no active disclosed coefficient both discrepancies vanish exactly. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: component_discrepancies_interior_singleton
lemma component_discrepancies_interior_singleton (n K M : ℕ) (hK : 0 < K)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K) (labels : Labels n) (j : Fin n)
    (hd : ∀ i, frameCoord K i (aug.1 j) ≠ 0 → aug.2.2 i = none) :
    evenDiscrepancy n K M a u aug {j} labels = 0 ∧
      oddDiscrepancy n K M a u aug {j} labels = 0 := by
  have he (ν s : Bool) : componentDensity ν s n K M a u aug {j} labels = 1 := by
    simp only [componentDensity, Finset.prod_singleton]
    exact labelDensity_active_undisclosed_average ν K M hK a u ha (fun _ => s)
      aug.2.2 (aug.1 j) hd (aug.2.1 j) (labels j)
  simp [evenDiscrepancy, oddDiscrepancy, averageComponent, nullComponent, he]

/-- The interior cancellation also includes the empty component, whose density is normalized. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hs condition](hyp:hs), [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: component_discrepancies_interior_small
lemma component_discrepancies_interior_small (n K M : ℕ) (hK : 0 < K)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K) (C : Finset (Fin n))
    (labels : Labels n) (hs : C.card ≤ 1)
    (hd : ∀ j ∈ C, ∀ i, frameCoord K i (aug.1 j) ≠ 0 → aug.2.2 i = none) :
    evenDiscrepancy n K M a u aug C labels = 0 ∧
      oddDiscrepancy n K M a u aug C labels = 0 := by
  by_cases he : C = ∅
  · subst C
    exact component_discrepancies_no_marks n K M a u aug ∅ labels (by simp)
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hc : C = {j} := by
      ext i
      constructor
      · intro hi
        simp only [Finset.mem_singleton]
        exact Finset.card_le_one.mp hs i hi j hj
      · intro hi
        have hij := Finset.mem_singleton.mp hi
        simpa only [hij] using hj
    rw [hc]
    exact component_discrepancies_interior_singleton n K M hK a u ha aug labels j (hd j hj)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
