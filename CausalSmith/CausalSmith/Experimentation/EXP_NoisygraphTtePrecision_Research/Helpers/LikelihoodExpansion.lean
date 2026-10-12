module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.LikelihoodPolynomial

/-!
# Exact donor-image expansion through all odd interaction orders

The finite donor-image polynomial and full-reference orthogonality identify every
odd interaction order. Regrouping their squared norms yields the exact energy.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hfit), [All mark/sign monomials are bounded by one in norm.](goal) -/
-- @node: imageMonomial_norm_le_one
lemma imageMonomial_norm_le_one (n m : ℕ) (hfit : 2*m ≤ n) (δ : ℝ)
    (S J : Finset (Fin m)) (o : Record (Fin n)) :
    ‖imageMonomial n m hfit δ S J o‖ ≤ 1 := by
  have ha : ∀ c : Fin m, ‖responseMark δ (o.2.2 (recipientOf n m hfit c))‖ ≤ 1 := by
    intro c
    rw [Real.norm_eq_abs, abs_le]
    exact responseMark_mem_Icc δ _
  have hb : ∀ j : Fin m,
      ‖CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
        (o.2.1 (donorOf n m hfit j))‖ ≤ 1 := by
    intro j
    cases o.2.1 (donorOf n m hfit j) <;>
      norm_num [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf]
  unfold imageMonomial
  rw [norm_mul, norm_prod, norm_prod]
  have hpa := Finset.prod_le_prod (s := S) (fun c _ => norm_nonneg _) (fun c _ => ha c)
  have hpb := Finset.prod_le_prod (s := J) (fun j _ => norm_nonneg _) (fun j _ => hb j)
  simp only [Finset.prod_const_one] at hpa hpb
  exact mul_le_one₀ hpa (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hpb

/-- Given [the stated assumptions](hyp:hfit,hqr), [Coefficient-weighted monomial cross terms are integrable on the full reference.](goal) -/
-- @node: imageMonomial_cross_integrable
lemma imageMonomial_cross_integrable (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hqr : ChannelDomain q r) (S J T K : Finset (Fin m)) :
    Integrable (fun o =>
      (imageProb n m hfit q r o.1 S J * imageMonomial n m hfit δ S J o) *
      (imageProb n m hfit q r o.1 T K * imageMonomial n m hfit δ T K o))
      (referenceLaw n m hfit q r δ) := by
  letI := referenceLaw_probability n m hfit q r δ hqr
  have hm (S J : Finset (Fin m)) : Measurable (fun H => imageProb n m hfit q r H S J) :=
    Measurable.of_discrete
  apply Integrable.of_bound (by fun_prop) 1
  apply Filter.Eventually.of_forall
  intro o
  have hc (S J : Finset (Fin m)) : ‖imageProb n m hfit q r o.1 S J‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (imageProb_mem_Icc n m hfit q r hqr _ S J).1]
    exact (imageProb_mem_Icc n m hfit q r hqr _ S J).2
  rw [norm_mul, norm_mul, norm_mul]
  apply mul_le_one₀
  · exact mul_le_one₀ (hc S J) (norm_nonneg _) (imageMonomial_norm_le_one n m hfit δ S J o)
  · positivity
  · exact mul_le_one₀ (hc T K) (norm_nonneg _) (imageMonomial_norm_le_one n m hfit δ T K o)

/-- Given [the stated assumptions](hyp:hfit,hqr), [The posterior coefficient remains inside the planted-graph squared norm.](goal) -/
-- @node: imageMonomial_cross_integral
lemma imageMonomial_cross_integral (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hqr : ChannelDomain q r) (S J T K : Finset (Fin m)) :
    (∫ o,
      (imageProb n m hfit q r o.1 S J * imageMonomial n m hfit δ S J o) *
      (imageProb n m hfit q r o.1 T K * imageMonomial n m hfit δ T K o)
      ∂referenceLaw n m hfit q r δ) =
      if (S,J) = (T,K) then
        markEnergy δ ^ S.card *
          (∫ H, imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r) else 0 := by
  have heq : (fun o : Record (Fin n) =>
      (imageProb n m hfit q r o.1 S J * imageMonomial n m hfit δ S J o) *
      (imageProb n m hfit q r o.1 T K * imageMonomial n m hfit δ T K o)) =
      (fun o => (imageProb n m hfit q r o.1 S J * imageProb n m hfit q r o.1 T K) *
        imageMonomial n m hfit δ S J o * imageMonomial n m hfit δ T K o) := by
    funext o
    ring
  rw [heq, reference_imageMonomial_pair_integral n m hfit q r δ hqr S J T K
    (fun H => imageProb n m hfit q r H S J * imageProb n m hfit q r H T K)
    (Measurable.of_discrete)]
  by_cases h : (S,J) = (T,K)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp only [true_and, if_true, ← sq]
    ring
  · have h' : ¬ (S = T ∧ J = K) := fun he => h (Prod.ext he.1 he.2)
    simp only [h, h', if_false]

/-- Given [the stated assumptions](hyp:hi,ho), [A finite orthogonal family has the sum of its squared norms as squared-sum integral.](goal) -/
-- @node: finite_orthogonal_sum_integral_sq
lemma finite_orthogonal_sum_integral_sq {ι α : Type*} [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (u : ι → α → ℝ) (e : ι → ℝ)
    (hi : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun x => u i x * u j x) μ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, (∫ x, u i x * u j x ∂μ) = if i = j then e i else 0) :
    (∫ x, (∑ i ∈ s, u i x)^2 ∂μ) = ∑ i ∈ s, e i := by
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi' => integrable_finsetSum _ (fun j hj => hi i hi' j hj))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum s (fun j hj => hi i hi' j hj)]
  rw [Finset.sum_congr rfl (fun j hj => ho i hi' j hj)]
  simp [hi']

/-- Given [the stated assumptions](hyp:hfit,hqr), [Orthogonality gives the exact energy before regrouping terms by cardinality.](goal) -/
-- @node: likelihood_odd_subset_energy
lemma likelihood_odd_subset_energy (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hqr : ChannelDomain q r) :
    (∫ o, (likelihoodPoly n m hfit q r δ true o - likelihoodPoly n m hfit q r δ false o)^2
      ∂referenceLaw n m hfit q r δ) =
    4 * ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => Odd S.card),
      ∑ J : Finset (Fin m), markEnergy δ ^ S.card *
        (∫ H, imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r) := by
  let A := Finset.univ.filter (fun S : Finset (Fin m) => Odd S.card)
  let u := fun (p : Finset (Fin m) × Finset (Fin m)) (o : Record (Fin n)) =>
    imageProb n m hfit q r o.1 p.1 p.2 * imageMonomial n m hfit δ p.1 p.2 o
  let e := fun p : Finset (Fin m) × Finset (Fin m) => markEnergy δ ^ p.1.card *
    (∫ H, imageProb n m hfit q r H p.1 p.2 ^ 2 ∂plantedGraphLaw n m hfit q r)
  have hexp (o : Record (Fin n)) :
      (likelihoodPoly n m hfit q r δ true o - likelihoodPoly n m hfit q r δ false o)^2 =
      4 * (∑ p ∈ (A ×ˢ Finset.univ), u p o)^2 := by
    rw [likelihoodPoly_odd_image_expansion, Finset.sum_product A Finset.univ (fun p => u p o)]
    change (2 * ∑ S ∈ A, ∑ J, u (S,J) o)^2 = 4 * (∑ S ∈ A, ∑ J, u (S,J) o)^2
    ring
  simp_rw [hexp]
  rw [integral_const_mul]
  rw [finite_orthogonal_sum_integral_sq _ _ u e
    (fun i _ j _ => imageMonomial_cross_integrable n m hfit q r δ hqr i.1 i.2 j.1 j.2)
    (fun i _ j _ => imageMonomial_cross_integral n m hfit q r δ hqr i.1 i.2 j.1 j.2)]
  rw [Finset.sum_product A Finset.univ e]

/-- Given [the stated assumptions](hyp:hfit,hqr), [Posterior image squares are bounded integrable functions of the full graph report.](goal) -/
-- @node: imageProb_sq_integrable
lemma imageProb_sq_integrable (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (S J : Finset (Fin m)) :
    Integrable (fun H => imageProb n m hfit q r H S J ^ 2) (plantedGraphLaw n m hfit q r) := by
  letI := plantedGraphLaw_probability n m hfit q r hqr
  apply Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1
  apply Filter.Eventually.of_forall
  intro H
  have h := imageProb_mem_Icc n m hfit q r hqr H S J
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [h.1, h.2]

/-- Given [the stated assumptions](hyp:hfit,hqr), [Finite integration expresses each order energy as a sum of individual squared norms.](goal) -/
-- @node: orderEnergy_eq_sum_integrals
lemma orderEnergy_eq_sum_integrals (n m : ℕ) (hfit : 2*m ≤ n) (q r : ℝ)
    (hqr : ChannelDomain q r) (k : ℕ) :
    orderEnergy n m hfit q r k =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.card = k),
        ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => J.card = k),
          ∫ H, imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r := by
  have hp : (Finset.univ : Finset (Fin m)).powerset = Finset.univ := by ext S; simp
  unfold orderEnergy
  rw [hp]
  rw [integral_finsetSum _ (fun S _ => integrable_finsetSum _
    (fun J _ => imageProb_sq_integrable n m hfit q r hqr S J))]
  apply Finset.sum_congr rfl
  intro S _
  exact integral_finsetSum _ (fun J _ => imageProb_sq_integrable n m hfit q r hqr S J)

/-- Given [the stated assumptions](hyp:hfit,hqr), [Regrouping the orthogonal subset energy by its cardinality gives the declared order energies.](goal) -/
-- @node: odd_subset_energy_eq_order_sum
lemma odd_subset_energy_eq_order_sum (n m : ℕ) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hqr : ChannelDomain q r) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => Odd S.card),
      ∑ J : Finset (Fin m), markEnergy δ ^ S.card *
        (∫ H, imageProb n m hfit q r H S J ^ 2 ∂plantedGraphLaw n m hfit q r)) =
    ∑ k ∈ (Finset.Icc 1 m).filter Odd, markEnergy δ ^ k * orderEnergy n m hfit q r k := by
  have hmap (S : Finset (Fin m)) (hS : S ∈ Finset.univ.filter (fun S : Finset (Fin m) => Odd S.card)) :
      S.card ∈ (Finset.Icc 1 m).filter Odd := by
    have ho := (Finset.mem_filter.mp hS).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ho⟩
    · obtain ⟨v, hv⟩ := ho
      omega
    · simpa using Finset.card_le_univ S
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro k hk
  have hok := (Finset.mem_filter.mp hk).2
  have hfilter :
      (Finset.univ.filter (fun S : Finset (Fin m) => Odd S.card)).filter (fun S => S.card = k) =
        Finset.univ.filter (fun S : Finset (Fin m) => S.card = k) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro h
      exact ⟨h ▸ hok, h⟩
  rw [hfilter, orderEnergy_eq_sum_integrals n m hfit q r hqr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hcard := (Finset.mem_filter.mp hS).2
  rw [hcard, Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJ : J.card = k
  · simp [hJ]
  · have hne : S.card ≠ J.card := by omega
    simp [hJ, imageProb_eq_zero_of_card_ne n m hfit q r _ S J hne]

/-- Given [the stated assumptions](hyp:hm,hfit,hr,hrq,hq,hδ,hδu), [Under the full product reference, recipient marks and donor signs isolate precisely the odd orders.](goal) -/
lemma likelihood_odd_energy (n m : ℕ) (hm : 1 ≤ m) (hfit : 2*m ≤ n) (q r δ : ℝ)
    (hr : 0 < r) (hrq : r ≤ q) (hq : q ≤ 1) (hδ : 0 < δ) (hδu : δ ≤ 1/12) :
    (∫ o, (likelihoodPoly n m hfit q r δ true o - likelihoodPoly n m hfit q r δ false o)^2
      ∂referenceLaw n m hfit q r δ) =
    4 * ∑ k ∈ (Finset.Icc 1 m).filter Odd, markEnergy δ ^ k * orderEnergy n m hfit q r k := by
  have hqr : ChannelDomain q r := ⟨hr.le, hrq, hq⟩
  rw [likelihood_odd_subset_energy n m hfit q r δ hqr,
    odd_subset_energy_eq_order_sum n m hfit q r δ hqr]

end CausalSmith.Experimentation.NoisygraphTtePrecision
