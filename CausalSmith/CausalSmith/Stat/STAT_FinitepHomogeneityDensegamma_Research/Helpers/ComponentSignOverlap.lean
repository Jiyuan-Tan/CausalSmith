module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentProductOverlap

/-! Integration of full component labels and independent copies of shared coarse signs. -/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Two independent uniform sign vectors factor a product of coordinatewise functions into its local two-sign averages. [This is the stated conclusion](goal). -/
-- @node: double_sign_mean_prod
lemma double_sign_mean_prod {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : κ → Bool → Bool → ℝ) :
    (Fintype.card (κ → Bool) : ℝ)⁻¹ ^ 2 *
      (∑ s : κ → Bool, ∑ t : κ → Bool, ∏ k, f k (s k) (t k)) =
      ∏ k, (∑ s : Bool, ∑ t : Bool, f k s t) / 4 := by
  classical
  let e : (κ → Bool × Bool) ≃ (κ → Bool) × (κ → Bool) :=
    { toFun := fun p => (fun k => (p k).1, fun k => (p k).2)
      invFun := fun p k => (p.1 k, p.2 k)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : (∑ s : κ → Bool, ∑ t : κ → Bool, ∏ k, f k (s k) (t k)) =
      ∑ p : κ → Bool × Bool, ∏ k, f k (p k).1 (p k).2 := by
    rw [← Fintype.sum_prod_type (f := fun z : (κ → Bool) × (κ → Bool) => ∏ k, f k (z.1 k) (z.2 k))]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have hc : (Fintype.card (κ → Bool) : ℝ)⁻¹ ^ 2 =
      (Fintype.card (κ → Bool × Bool) : ℝ)⁻¹ := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
    ring
  rw [hs, hc, finite_pi_mean_prod (fun k (z : Bool × Bool) => f k z.1 z.2)]
  simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    Fintype.sum_prod_type]
  apply Finset.prod_congr rfl
  intro k _
  ring

/-- Mixing two copies of each coarse sign selects the even-subset product in every group. No component's diagonal square is introduced by this averaging. [This is the stated conclusion](goal). -/
-- @node: grouped_sign_overlap_average
lemma grouped_sign_overlap_average {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (d : ι → ℝ) :
    (Fintype.card (κ → Bool) : ℝ)⁻¹ ^ 2 *
      (∑ s : κ → Bool, ∑ t : κ → Bool,
        ∏ i ∈ S, (1 + signVal (s (g i)) * signVal (t (g i)) * d i)) =
      ∏ k, ((∏ i ∈ S.filter (fun i => g i = k), (1+d i)) +
        ∏ i ∈ S.filter (fun i => g i = k), (1-d i))/2 := by
  classical
  have hp (s t : κ → Bool) :
      (∏ i ∈ S, (1 + signVal (s (g i)) * signVal (t (g i)) * d i)) =
      ∏ k, ∏ i ∈ S.filter (fun i => g i = k),
        (1 + signVal (s k) * signVal (t k) * d i) := by
    rw [← Finset.prod_fiberwise S g]
    apply Finset.prod_congr rfl
    intro k _
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [hp]
  rw [double_sign_mean_prod (fun k s t => ∏ i ∈ S.filter (fun i => g i = k),
    (1 + signVal s * signVal t * d i))]
  exact Finset.prod_congr rfl (fun k _ => shared_sign_overlap_average _ d)

/-- Full-label integration of two fixed component-sign configurations factors into the proved local signed overlaps against the actual intermediate denominators. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: component_signed_overlap_product
lemma component_signed_overlap_product (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (s t : Finset (Fin n) → Bool) :
    (4:ℝ)^(-(n:ℤ)) * (∑ l : Labels n,
      (∏ C ∈ components n K M aug, componentDensity true (s C) n K M a u aug C l) *
      (∏ C ∈ components n K M aug, componentDensity true (t C) n K M a u aug C l) /
        intermediateDensity n K M a u aug l) =
      ∏ C ∈ components n K M aug,
        (1 + signVal (s C) * signVal (t C) * componentOddActivity n K M a u aug C) := by
  have hp (l : Labels n) :
      (∏ C ∈ components n K M aug, componentDensity true (s C) n K M a u aug C l) *
      (∏ C ∈ components n K M aug, componentDensity true (t C) n K M a u aug C l) /
        intermediateDensity n K M a u aug l =
      ∏ C : {C // C ∈ components n K M aug},
        componentDensity true (s C.val) n K M a u aug C.val l *
          componentDensity true (t C.val) n K M a u aug C.val l /
            averageComponent n K M a u aug C.val l := by
    simp only [intermediateDensity, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    exact (Finset.prod_coe_sort (components n K M aug)
      (fun C => componentDensity true (s C) n K M a u aug C l *
        componentDensity true (t C) n K M a u aug C l /
          averageComponent n K M a u aug C l)).symm
  simp_rw [hp]
  rw [component_partition_mean_prod]
  · simp_rw [component_signed_overlap _ _ n K M a u hK ha hu aug]
    exact Finset.prod_coe_sort (components n K M aug)
      (fun C => 1 + signVal (s C) * signVal (t C) * componentOddActivity n K M a u aug C)
  · intro C l l' hl
    have hh (v sign : Bool) := componentDensity_labels_congr v sign n K M a u aug C.val l l' hl
    simp only [averageComponent, hh]

/-- Once the conditional coefficient mixture is expressed as products with shared fair signs, full-label integration gives exactly the even-subset chi-square product. The factorization hypothesis isolates the remaining geometric independence argument for the original prior. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hfactor condition](hyp:hfactor). [This is the stated conclusion](goal). -/
-- @node: alternative_chiSq_of_component_factorization
lemma alternative_chiSq_of_component_factorization {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (g : Finset (Fin n) → κ)
    (hfactor : ∀ l : Labels n, alternativeConditionalDensity n K M a u aug l =
      (Fintype.card (κ → Bool) : ℝ)⁻¹ * ∑ s : κ → Bool,
        ∏ C ∈ components n K M aug, componentDensity true (s (g C)) n K M a u aug C l) :
    1 + Causalean.Stat.chiSqDiv (alternativeConditionalLaw n K M a u aug)
      (intermediateConditionalLaw n K M a u aug) =
      ∏ k, ((∏ C ∈ (components n K M aug).filter (fun C => g C = k),
          (1 + componentOddActivity n K M a u aug C)) +
        ∏ C ∈ (components n K M aug).filter (fun C => g C = k),
          (1 - componentOddActivity n K M a u aug C))/2 := by
  classical
  rw [alternativeConditionalLaw, intermediateConditionalLaw, fairLabelMeasure_one_add_chiSqDiv]
  · let R (s : κ → Bool) (l : Labels n) : ℝ :=
      ∏ C ∈ components n K M aug, componentDensity true (s (g C)) n K M a u aug C l
    have he (l : Labels n) : alternativeConditionalDensity n K M a u aug l^2 /
        intermediateDensity n K M a u aug l =
        (Fintype.card (κ → Bool) : ℝ)⁻¹ ^ 2 *
          ∑ s : κ → Bool, ∑ t : κ → Bool,
            R s l * R t l / intermediateDensity n K M a u aug l := by
      rw [hfactor, mul_pow, pow_two (∑ s : κ → Bool, R s l), Fintype.sum_mul_sum]
      simp only [Finset.sum_div, mul_div_assoc]
    simp_rw [he]
    rw [← Finset.mul_sum]
    rw [Finset.sum_comm (f := fun l s => ∑ t : κ → Bool,
      R s l * R t l / intermediateDensity n K M a u aug l)]
    simp_rw [Finset.sum_comm (f := fun l t =>
      R _ l * R t l / intermediateDensity n K M a u aug l)]
    have hswap : ∀ (x y z : ℝ), x * (y*z) = y*(x*z) := by intros; ring
    rw [hswap, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    have ho (s t : κ → Bool) :
        (4:ℝ)^(-(n:ℤ)) * ∑ l : Labels n,
          R s l * R t l / intermediateDensity n K M a u aug l =
        ∏ C ∈ components n K M aug,
          (1 + signVal (s (g C)) * signVal (t (g C)) * componentOddActivity n K M a u aug C) :=
      component_signed_overlap_product n K M a u hK ha hu aug (fun C => s (g C)) (fun C => t (g C))
    have hin (s t : κ → Bool) :
        (∑ l : Labels n, (Fintype.card (κ → Bool) : ℝ)⁻¹ ^ 2 *
          ((4:ℝ)^(-(n:ℤ)) * (R s l * R t l / intermediateDensity n K M a u aug l))) =
        (Fintype.card (κ → Bool) : ℝ)⁻¹ ^ 2 *
          ∏ C ∈ components n K M aug,
            (1 + signVal (s (g C)) * signVal (t (g C)) * componentOddActivity n K M a u aug C) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, ho]
    simp_rw [hin, ← Finset.mul_sum]
    exact grouped_sign_overlap_average _ g (componentOddActivity n K M a u aug)
  · intro l
    exact alternativeConditionalDensity_nonneg n K M a u hK ha hu aug l
  · intro l
    apply Finset.prod_pos
    intro C _
    exact lt_of_lt_of_le (by positivity) (component_denominator_bounds n K M a u hK ha hu aug C l).2
  · exact alternativeConditionalDensity_sum n K M a u aug
  · exact intermediateDensity_sum n K M a u aug

end CausalSmith.Stat.FinitepHomogeneityDensegamma
