module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentBoundaryGeometry

/-! Conditional singleton moments including fixed coarse-boundary coefficients. -/
public section
set_option linter.style.whitespace false
set_option linter.style.longLine false
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Conditional product weights reduce every one-node expectation to its actual local law. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_one_node
lemma conditionalPairWeight_one_node (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (δ : Disclosure K) (j : Fin (K+1))
    (f : Bool × Bool → ℝ) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p * f (p j)) =
      match δ j with
      | some q => f q
      | none => ∑ q : Bool × Bool,
          pairWeight ν (coarseTent M σ ((j:ℝ)/K)) q.1 q.2 * f q := by
  let w (i : Fin (K+1)) (q : Bool × Bool) : ℝ := match δ i with
    | some r => if q = r then 1 else 0
    | none => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) q.1 q.2
  have hw (i : Fin (K+1)) : ∑ q, w i q = 1 := by
    cases hd : δ i with
    | some q => simp [w, hd]
    | none => simpa [w, hd] using pairWeight_sum ν (coarseTent M σ ((i:ℝ)/K))
  change (∑ p : CoefficientPairs K, (∏ i, w i (p i)) * f (p j)) = _
  rw [finite_product_weight_one_node w hw]
  cases hd : δ j <;> simp [w, hd]

/-- Fixed disclosed values and fair undisclosed marginal signs have the same means under either prior. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_sign_mean_common
lemma conditionalPairWeight_sign_mean_common (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (δ : Disclosure K) (j : Fin (K+1)) (r : Bool) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      signVal (if r then (p j).1 else (p j).2)) =
    ∑ p : CoefficientPairs K, conditionalPairWeight false K M (fun _ => false) δ p *
      signVal (if r then (p j).1 else (p j).2) := by
  rw [conditionalPairWeight_one_node ν K M σ δ j
    (fun q => signVal (if r then q.1 else q.2)),
    conditionalPairWeight_one_node false K M (fun _ => false) δ j
      (fun q => signVal (if r then q.1 else q.2))]
  cases hd : δ j with
  | some q => rfl
  | none =>
    cases r
    · exact (pairWeight_sign_moments ν _).2.1.trans (pairWeight_sign_moments false _).2.1.symm
    · exact (pairWeight_sign_moments ν _).1.trans (pairWeight_sign_moments false _).1.symm

/-- Distinct nodes have zero mixed moments if either node is undisclosed. This statement assumes [the hij condition](hyp:hij), [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_distinct_one_undisclosed
lemma conditionalPairWeight_distinct_one_undisclosed (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (δ : Disclosure K) (i j : Fin (K+1)) (hij : i ≠ j)
    (hd : δ i = none ∨ δ j = none) (r s : Bool) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      (signVal (if r then (p i).1 else (p i).2) *
        signVal (if s then (p j).1 else (p j).2))) = 0 := by
  let w (k : Fin (K+1)) (q : Bool × Bool) : ℝ := match δ k with
    | some t => if q = t then 1 else 0
    | none => pairWeight ν (coarseTent M σ ((k:ℝ)/K)) q.1 q.2
  have hw (k : Fin (K+1)) : ∑ q, w k q = 1 := by
    cases hd : δ k with
    | some q => simp [w, hd]
    | none => simpa [w, hd] using pairWeight_sum ν (coarseTent M σ ((k:ℝ)/K))
  change (∑ p : CoefficientPairs K, (∏ k, w k (p k)) *
    (signVal (if r then (p i).1 else (p i).2) *
      signVal (if s then (p j).1 else (p j).2))) = 0
  rw [finite_product_weight_two_nodes w hw i j hij
    (fun q => signVal (if r then q.1 else q.2))
    (fun q => signVal (if s then q.1 else q.2))]
  have hz (k : Fin (K+1)) (hk : δ k = none) (t : Bool) :
      (∑ q, w k q * signVal (if t then q.1 else q.2)) = 0 := by
    simp only [w, hk]
    cases t
    · exact (pairWeight_sign_moments ν _).2.1
    · exact (pairWeight_sign_moments ν _).1
  rcases hd with hi | hj
  · rw [hz i hi r, zero_mul]
  · rw [hz j hj s, mul_zero]

/-- With at most one active disclosed coefficient, propensity energy is still one and the change in the mixed field moment is exactly the interpolated copula correlation. This statement assumes [the hK condition](hyp:hK), [the hd condition](hyp:hd), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_boundary_frame_moments
lemma conditionalPairWeight_boundary_frame_moments (ν : Bool) (K M : ℕ)
    (hK : 0 < K) (σ : Fin (M/2) → Bool) (δ : Disclosure K) (x : unitInterval)
    (hd : ∀ i j, frameCoord K i x ≠ 0 → frameCoord K j x ≠ 0 →
      i ≠ j → δ i = none ∨ δ j = none)
    (hg : ∀ i, δ i ≠ none → coarseTent M σ ((i:ℝ)/K) = 0) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      (frameField K (fun i => signVal (p i).1) x)^2) = 1 ∧
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      (frameField K (fun i => signVal (p i).1) x *
        frameField K (fun i => signVal (p i).2) x)) =
      (∑ p : CoefficientPairs K, conditionalPairWeight false K M (fun _ => false) δ p *
        (frameField K (fun i => signVal (p i).1) x *
          frameField K (fun i => signVal (p i).2) x)) +
        (if ν then 1 else 0)*kappa0*smoothedTent K M σ x := by
  let f := fun i : Fin (K+1) => frameCoord K i x
  have hexpand (ν' : Bool) (σ' : Fin (M/2) → Bool) (r s : Bool) :
      (∑ p : CoefficientPairs K, conditionalPairWeight ν' K M σ' δ p *
        (frameField K (fun i => signVal (if r then (p i).1 else (p i).2)) x *
          frameField K (fun i => signVal (if s then (p i).1 else (p i).2)) x)) =
        ∑ i, (∑ p : CoefficientPairs K, conditionalPairWeight ν' K M σ' δ p *
          (signVal (if r then (p i).1 else (p i).2) *
            signVal (if s then (p i).1 else (p i).2))) * f i^2 := by
    let w := conditionalPairWeight ν' K M σ' δ
    have hoff (i j : Fin (K+1)) (hij : i ≠ j) :
        (∑ p : CoefficientPairs K, w p *
          ((signVal (if r then (p i).1 else (p i).2) * f i) *
            (signVal (if s then (p j).1 else (p j).2) * f j))) = 0 := by
      by_cases hi : f i = 0
      · simp [hi]
      by_cases hj : f j = 0
      · simp [hj]
      have hm := conditionalPairWeight_distinct_one_undisclosed ν' K M σ' δ i j hij
        (hd i j hi hj hij) r s
      have he (p : CoefficientPairs K) : w p *
          ((signVal (if r then (p i).1 else (p i).2) * f i) *
            (signVal (if s then (p j).1 else (p j).2) * f j)) =
          (w p * (signVal (if r then (p i).1 else (p i).2) *
            signVal (if s then (p j).1 else (p j).2))) * (f i*f j) := by ring
      simp_rw [he, ← Finset.sum_mul]
      rw [hm, zero_mul]
    simp only [frameField, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm, Finset.sum_eq_single i
      (fun j _ hji => hoff j i hji) (by simp)]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [f]
    ring
  constructor
  · simp_rw [pow_two]
    have hx := hexpand ν σ true true
    simp only [↓reduceIte] at hx
    rw [hx]
    have he (p : CoefficientPairs K) (i : Fin (K+1)) :
        signVal (p i).1 * signVal (p i).1 = (1:ℝ) := by
      cases (p i).1 <;> norm_num [signVal]
    simp only [he, mul_one, conditionalPairWeight_sum, one_mul]
    exact frame_partition K hK x
  · have hx := hexpand ν σ true false
    have hx₀ := hexpand false (fun _ => false) true false
    simp only [Bool.false_eq_true, ↓reduceIte] at hx hx₀
    rw [hx, hx₀]
    rw [smoothedTent, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [conditionalPairWeight_one_node ν K M σ δ i (fun q => signVal q.1*signVal q.2),
      conditionalPairWeight_one_node false K M (fun _ => false) δ i
        (fun q => signVal q.1*signVal q.2)]
    cases hi : δ i with
    | some q =>
      have hz := hg i (by simp [hi])
      simp [hz]
    | none =>
      rw [(pairWeight_sign_moments ν _).2.2, (pairWeight_sign_moments false _).2.2]
      simp [f, mul_assoc]

/-- Averaging a coordinate field uses only the common marginal sign means, including disclosures. [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_frame_mean_common
lemma conditionalPairWeight_frame_mean_common (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (δ : Disclosure K) (x : unitInterval) (r : Bool) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      frameField K (fun i => signVal (if r then (p i).1 else (p i).2)) x) =
    ∑ p : CoefficientPairs K, conditionalPairWeight false K M (fun _ => false) δ p *
      frameField K (fun i => signVal (if r then (p i).1 else (p i).2)) x := by
  simp only [frameField, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← mul_assoc, ← Finset.sum_mul,
    conditionalPairWeight_sign_mean_common ν K M σ δ i r]

/-- The correction cancels the changed singleton mixed moment while retaining the common nonzero means contributed by a disclosed boundary pair. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hd condition](hyp:hd), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: labelDensity_boundary_singleton_common
lemma labelDensity_boundary_singleton_common (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (σ : Fin (M/2) → Bool) (δ : Disclosure K)
    (x : unitInterval)
    (hd : ∀ i j, frameCoord K i x ≠ 0 → frameCoord K j x ≠ 0 →
      i ≠ j → δ i = none ∨ δ j = none)
    (hg : ∀ i, δ i ≠ none → coarseTent M σ ((i:ℝ)/K) = 0)
    (marked : Bool) (label : Bool × Bool) :
    (∑ p : CoefficientPairs K, conditionalPairWeight ν K M σ δ p *
      labelDensity ν K M a u (σ,p) x marked label) =
    ∑ p : CoefficientPairs K, conditionalPairWeight false K M (fun _ => false) δ p *
      labelDensity false K M a u ((fun _ => false),p) x marked label := by
  let w := conditionalPairWeight ν K M σ δ
  let w₀ := conditionalPairWeight false K M (fun _ => false) δ
  let Λ := fun p : CoefficientPairs K => frameField K (fun i => signVal (p i).1) x
  let H := fun p : CoefficientPairs K => frameField K (fun i => signVal (p i).2) x
  let t : ℝ := -(if ν then 1 else 0)*a*u*kappa0/(1-a^2)*smoothedTent K M σ x
  obtain ⟨hΛ2, hΛH⟩ := conditionalPairWeight_boundary_frame_moments ν K M hK σ δ x hd hg
  have hs : ∑ p, w p = 1 := conditionalPairWeight_sum ν K M σ δ
  have hs₀ : ∑ p, w₀ p = 1 := conditionalPairWeight_sum false K M (fun _ => false) δ
  change (∑ p, w p * (Λ p)^2) = 1 at hΛ2
  change (∑ p, w p * (Λ p*H p)) = (∑ p, w₀ p * (Λ p*H p)) + _ at hΛH
  have ht : a*u*((if ν then 1 else 0)*kappa0*smoothedTent K M σ x) + t*(1-a^2) = 0 := by
    dsimp [t]
    field_simp
    <;> ring
  have hz : (∑ p, w p * copulaZeta ν K M a u (σ,p) x) =
      ∑ p, w₀ p * copulaZeta false K M a u ((fun _ => false),p) x := by
    have he (p : CoefficientPairs K) : w p * copulaZeta ν K M a u (σ,p) x =
        (a*u)*(w p*(Λ p*H p)) + t*w p - (t*a^2)*(w p*(Λ p)^2) := by
      dsimp [copulaZeta, copulaXi, copulaUpsilon, copulaT, Λ, H, t]
      ring
    have he₀ (p : CoefficientPairs K) : w₀ p * copulaZeta false K M a u ((fun _ => false),p) x =
        (a*u)*(w₀ p*(Λ p*H p)) := by
      simp [copulaZeta, copulaXi, copulaUpsilon, copulaT, Λ, H]
      ring
    simp_rw [he, he₀, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hΛH, hs, hΛ2]
    linear_combination ht
  have hx : (∑ p, w p * copulaXi K M a (σ,p) x) =
      ∑ p, w₀ p * copulaXi K M a ((fun _ => false),p) x := by
    have he (p : CoefficientPairs K) : w p * copulaXi K M a (σ,p) x = a*(w p*Λ p) := by
      dsimp [copulaXi, Λ]; ring
    have he₀ (p : CoefficientPairs K) : w₀ p * copulaXi K M a ((fun _ => false),p) x = a*(w₀ p*Λ p) := by
      dsimp [copulaXi, Λ]; ring
    simp_rw [he, he₀, ← Finset.mul_sum]
    exact congrArg (a*·) (conditionalPairWeight_frame_mean_common ν K M σ δ x true)
  have hy : (∑ p, w p * copulaUpsilon K M u (σ,p) x) =
      ∑ p, w₀ p * copulaUpsilon K M u ((fun _ => false),p) x := by
    have he (p : CoefficientPairs K) : w p * copulaUpsilon K M u (σ,p) x = u*(w p*H p) := by
      dsimp [copulaUpsilon, H]; ring
    have he₀ (p : CoefficientPairs K) : w₀ p * copulaUpsilon K M u ((fun _ => false),p) x = u*(w₀ p*H p) := by
      dsimp [copulaUpsilon, H]; ring
    simp_rw [he, he₀, ← Finset.mul_sum]
    exact congrArg (u*·) (conditionalPairWeight_frame_mean_common ν K M σ δ x false)
  change (∑ p, w p * labelDensity ν K M a u (σ,p) x marked label) =
    ∑ p, w₀ p * labelDensity false K M a u ((fun _ => false),p) x marked label
  cases marked <;>
    simp only [labelDensity, Bool.false_eq_true, ↓reduceIte, mul_add, mul_one,
      Finset.sum_add_distrib] <;>
    simp_rw [mul_left_comm (w _) (signVal _), mul_left_comm (w₀ _) (signVal _),
      ← Finset.mul_sum] <;>
    simp [hs, hs₀, hx, hy, mul_assoc, mul_left_comm]
  simp_rw [mul_left_comm (w _) (signVal _)]
  simp_rw [← Finset.mul_sum]
  rw [hz]

/-- Every singleton density agrees with the null density under actual boundary-only disclosure. This statement assumes [the hM condition](hyp:hM), [the hKM condition](hyp:hKM), [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: component_discrepancies_boundary_singleton
lemma component_discrepancies_boundary_singleton (n K M : ℕ)
    (hM : 0 < M) (hKM : 2*M ≤ K) (a u : ℝ) (ha : 1-a^2 ≠ 0)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) (pairs : CoefficientPairs K)
    (labels : Labels n) (j : Fin n) :
    evenDiscrepancy n K M a u (xs,marks,disclose K M pairs) {j} labels = 0 ∧
      oddDiscrepancy n K M a u (xs,marks,disclose K M pairs) {j} labels = 0 := by
  have hK : 0 < K := by omega
  have hd (i k : Fin (K+1)) (hi : frameCoord K i (xs j) ≠ 0)
      (hk : frameCoord K k (xs j) ≠ 0) (hik : i ≠ k) :
      disclose K M pairs i = none ∨ disclose K M pairs k = none := by
    by_cases hbi : boundaryNode K M i
    · by_cases hbk : boundaryNode K M k
      · exact False.elim (hik (active_boundaryNode_unique K M hM hKM (xs j) i k hbi hbk hi hk))
      · exact Or.inr (by simp [disclose, hbk])
    · exact Or.inl (by simp [disclose, hbi])
  have hg (σ : Fin (M/2) → Bool) (i : Fin (K+1))
      (hi : disclose K M pairs i ≠ none) : coarseTent M σ ((i:ℝ)/K) = 0 := by
    apply coarseTent_boundaryNode_zero K M hK i _ σ
    by_contra hb
    exact hi (by simp [disclose, hb])
  have he (ν s : Bool) :
      componentDensity ν s n K M a u (xs,marks,disclose K M pairs) {j} labels =
        componentDensity false false n K M a u (xs,marks,disclose K M pairs) {j} labels := by
    simp only [componentDensity, Finset.prod_singleton]
    exact labelDensity_boundary_singleton_common ν K M hK a u ha (fun _ => s)
      (disclose K M pairs) (xs j) hd (hg _) (marks j) (labels j)
  simp only [evenDiscrepancy, oddDiscrepancy, averageComponent, nullComponent, he]
  constructor <;> ring

open MeasureTheory

/-- Boundary disclosure is almost surely an actual output of the specified disclosure map. [This is the stated conclusion](goal). -/
-- @node: disclosureLaw_ae_actual_disclosure
lemma disclosureLaw_ae_actual_disclosure (K M : ℕ) :
    ∀ᵐ δ ∂disclosureLaw K M, ∃ p : CoefficientPairs K, δ = disclose K M p := by
  classical
  unfold disclosureLaw
  rw [ae_finsetSum_measure_iff]
  intro p _
  apply Measure.ae_smul_measure
  apply (ae_dirac_iff (MeasurableSet.of_discrete :
    MeasurableSet {δ : Disclosure K | ∃ p : CoefficientPairs K, δ = disclose K M p})).mpr
  exact ⟨p, rfl⟩

/-- The common augmentation carries only actual boundary disclosures. [This is the stated conclusion](goal). -/
-- @node: commonAugmentation_ae_actual_disclosure
lemma commonAugmentation_ae_actual_disclosure (n K M : ℕ) (ε : ℝ) :
    ∀ᵐ aug ∂commonAugmentation n K M ε,
      ∃ p : CoefficientPairs K, aug.2.2 = disclose K M p := by
  classical
  letI : IsFiniteMeasure (disclosureLaw K M) := ⟨by
    simp only [disclosureLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    finiteness⟩
  letI : IsFiniteMeasure (markFlagLaw ε) := ⟨by
    simp [markFlagLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']⟩
  have hd : MeasurableSet {δ : Disclosure K | ∃ p : CoefficientPairs K, δ = disclose K M p} :=
    MeasurableSet.of_discrete
  unfold commonAugmentation
  apply (Measure.ae_prod_iff_ae_ae (hd.preimage (measurable_snd.comp measurable_snd))).mpr
  apply ae_of_all
  intro xs
  apply (Measure.ae_prod_iff_ae_ae (hd.preimage measurable_snd)).mpr
  apply ae_of_all
  intro marks
  exact disclosureLaw_ae_actual_disclosure K M

/-- Empty and singleton components have zero discrepancies, including every disclosed boundary. This statement assumes [the hM condition](hyp:hM), [the hKM condition](hyp:hKM), [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: component_discrepancies_small_ae
lemma component_discrepancies_small_ae (n K M : ℕ) (ε a u : ℝ)
    (hM : 0 < M) (hKM : 2*M ≤ K) (ha : 1-a^2 ≠ 0) :
    ∀ᵐ aug ∂commonAugmentation n K M ε, ∀ C : Finset (Fin n), ∀ labels : Labels n,
      C.card ≤ 1 → evenDiscrepancy n K M a u aug C labels = 0 ∧
        oddDiscrepancy n K M a u aug C labels = 0 := by
  classical
  filter_upwards [commonAugmentation_ae_actual_disclosure n K M ε] with aug haug
  intro C labels hs
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
        simpa only [Finset.mem_singleton.mp hi] using hj
    obtain ⟨p, hp⟩ := haug
    have haug' : aug = (aug.1, aug.2.1, disclose K M p) := by
      exact Prod.ext rfl (Prod.ext rfl hp)
    rw [hc, haug']
    exact component_discrepancies_boundary_singleton n K M hM hKM a u ha _ _ p labels j

end CausalSmith.Stat.FinitepHomogeneityDensegamma
