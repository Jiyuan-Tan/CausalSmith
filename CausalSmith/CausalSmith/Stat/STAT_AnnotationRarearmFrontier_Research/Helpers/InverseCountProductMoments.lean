module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.PoissonInverseMoments
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments
public import Mathlib.Probability.Independence.Integration

/-!
Independent product moments for the inverse-count arm statistic.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:Om,mu,hX,hY,hind,X,Y), Independent square-integrable factors have a square-integrable product.  This gives [the stated result](goal).-/
-- @node: inverse_count_independent_product_memLp
lemma inverse_count_independent_product_memLp {Om : Type} [MeasurableSpace Om]
    {mu : Measure Om} {X Y : Om → Real}
    (hX : MemLp X 2 mu) (hY : MemLp Y 2 mu) (hind : IndepFun X Y mu) :
    MemLp (fun om => X om * Y om) 2 mu := by
  apply (memLp_two_iff_integrable_sq (hX.aestronglyMeasurable.mul
    hY.aestronglyMeasurable)).2
  have hi := (hind.comp (φ := fun x : Real => x ^ 2) (ψ := fun y : Real => y ^ 2)
    (by fun_prop) (by fun_prop)).integrable_mul hX.integrable_sq hY.integrable_sq
  change Integrable (fun om => X om ^ 2 * Y om ^ 2) mu at hi
  change Integrable (fun om => (X om * Y om) ^ 2) mu
  simpa only [mul_pow] using hi

/-- [Under the stated inputs and conditions](hyp:Om,mu,hX,hY,hind,X,Y), The exact independent-product variance identity separates count and weight fluctuations.  This gives [the stated result](goal).-/
-- @node: inverse_count_independent_product_variance
lemma inverse_count_independent_product_variance {Om : Type} [MeasurableSpace Om]
    {mu : Measure Om} [IsProbabilityMeasure mu] {X Y : Om → Real}
    (hX : MemLp X 2 mu) (hY : MemLp Y 2 mu) (hind : IndepFun X Y mu) :
    variance (fun om => X om * Y om) mu =
      variance X mu * (∫ om, Y om ^ 2 ∂mu) +
        (∫ om, X om ∂mu) ^ 2 * variance Y mu := by
  have hm := hind.integral_mul_eq_mul_integral hX.aestronglyMeasurable
    hY.aestronglyMeasurable
  have hs := (hind.comp (φ := fun x : Real => x ^ 2) (ψ := fun y : Real => y ^ 2)
    (by fun_prop) (by fun_prop)).integral_mul_eq_mul_integral
    hX.integrable_sq.aestronglyMeasurable hY.integrable_sq.aestronglyMeasurable
  rw [variance_eq_sub (inverse_count_independent_product_memLp hX hY hind),
    variance_eq_sub hX, variance_eq_sub hY]
  simp only [Pi.pow_apply, mul_pow, Pi.mul_apply, Function.comp_def] at hm hs ⊢
  rw [hm, hs]
  ring

/-- [Under the stated hypotheses](hyp:hX,hlaw), A measurable Poisson count inherits its first two moments and variance.  This gives [the stated result](goal). -/
-- @node: inverse_count_poisson_count_moments
lemma inverse_count_poisson_count_moments {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (X : Om → Nat) (lam : NNReal)
    (hX : Measurable X) (hlaw : mu.map X = poissonMeasure lam) :
    MemLp (fun om => (X om : Real)) 2 mu ∧
      (∫ om, (X om : Real) ∂mu) = (lam : Real) ∧
      (∫ om, (X om : Real) ^ 2 ∂mu) = (lam : Real) ^ 2 + (lam : Real) ∧
      variance (fun om => (X om : Real)) mu = (lam : Real) := by
  have hLp : MemLp (fun om => (X om : Real)) 2 mu :=
    MeasureTheory.MemLp.comp_measurePreserving
      (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two lam) ⟨hX, hlaw⟩
  have hmean : (∫ om, (X om : Real) ∂mu) = (lam : Real) := by
    rw [← integral_map hX.aemeasurable (by fun_prop), hlaw]
    exact Causalean.Mathlib.Probability.Poisson.poisson_natCast_first_moment lam
  have hsq : (∫ om, (X om : Real) ^ 2 ∂mu) = (lam : Real) ^ 2 + (lam : Real) := by
    rw [← integral_map (f := fun k : Nat => (k : Real) ^ 2) hX.aemeasurable
      (by fun_prop), hlaw]
    exact Causalean.Mathlib.Probability.Poisson.PairSecondMoment.poisson_count_second_moment lam
  refine ⟨hLp, hmean, hsq, ?_⟩
  rw [variance_eq_sub hLp]
  change (∫ om, (X om : Real) ^ 2 ∂mu) - (∫ om, (X om : Real) ∂mu) ^ 2 = _
  rw [hsq, hmean]
  ring

/-- [Under the stated hypotheses](hyp:hK,hlaw), A measurable Poisson count inherits reciprocal square-integrability and moment bounds.  This gives [the stated result](goal). -/
-- @node: inverse_count_poisson_reciprocal_moments
lemma inverse_count_poisson_reciprocal_moments {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (K : Om → Nat) (lam : NNReal)
    (hK : Measurable K) (hlaw : mu.map K = poissonMeasure lam) :
    MemLp (fun om => ((K om : Real) + 1)⁻¹) 2 mu ∧
      (∫ om, (((K om : Real) + 1)⁻¹) ^ 2 ∂mu) ≤
        2 ^ 16 / (1 + (lam : Real)) ^ 2 ∧
      variance (fun om => ((K om : Real) + 1)⁻¹) mu ≤
        2 ^ 16 * (lam : Real) / (1 + (lam : Real)) ^ 4 := by
  have hg : MemLp (fun k : Nat => ((k : Real) + 1)⁻¹) 2 (poissonMeasure lam) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two lam
  refine ⟨hg.comp_measurePreserving ⟨hK, hlaw⟩, ?_, ?_⟩
  · rw [← integral_map (f := fun k : Nat => (((k : Real) + 1)⁻¹) ^ 2)
      hK.aemeasurable (by fun_prop), hlaw]
    exact (poisson_inverse_moments lam).2.1
  · have hp : MeasurePreserving K mu (poissonMeasure lam) := ⟨hK, hlaw⟩
    rw [hp.variance_fun_comp (f := fun k : Nat => ((k : Real) + 1)⁻¹) (by fun_prop)]
    exact (poisson_inverse_moments lam).2.2

/-- [Under the stated hypotheses](hyp:hK,hW,hKlaw,hWlaw,hind), Independence yields both moment bounds for the marginal inverse-count weight.  This gives [the stated result](goal). -/
-- @node: inverse_count_weight_moments
lemma inverse_count_weight_moments {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (K W : Om → Nat) (lam rho : NNReal)
    (hK : Measurable K) (hW : Measurable W)
    (hKlaw : mu.map K = poissonMeasure lam) (hWlaw : mu.map W = poissonMeasure rho)
    (hind : IndepFun W K mu) :
    MemLp (fun om => 1 + (W om : Real) / ((K om : Real) + 1)) 2 mu ∧
      (∫ om, (1 + (W om : Real) / ((K om : Real) + 1)) ^ 2 ∂mu) ≤
        2 + 2 * (2 ^ 16 : Real) * ((rho : Real) ^ 2 + rho) / (1 + (lam : Real)) ^ 2 ∧
      variance (fun om => 1 + (W om : Real) / ((K om : Real) + 1)) mu ≤
        (2 ^ 16 : Real) * ((rho : Real) / (1 + (lam : Real)) ^ 2 +
          (rho : Real) ^ 2 * (lam : Real) / (1 + (lam : Real)) ^ 4) := by
  obtain ⟨hw, hwm, hws, hwv⟩ := inverse_count_poisson_count_moments mu W rho hW hWlaw
  obtain ⟨hg, hgs, hgv⟩ := inverse_count_poisson_reciprocal_moments mu K lam hK hKlaw
  let V : Om → Real := fun om => (W om : Real) * ((K om : Real) + 1)⁻¹
  have hi : IndepFun (fun om => (W om : Real))
      (fun om => ((K om : Real) + 1)⁻¹) mu :=
    hind.comp (φ := fun k : Nat => (k : Real))
      (ψ := fun k : Nat => ((k : Real) + 1)⁻¹) (by fun_prop) (by fun_prop)
  have hv : MemLp V 2 mu := inverse_count_independent_product_memLp hw hg hi
  have hs : (∫ om, V om ^ 2 ∂mu) =
      ((rho : Real) ^ 2 + rho) * (∫ om, (((K om : Real) + 1)⁻¹) ^ 2 ∂mu) := by
    have hs := (hi.comp (φ := fun x : Real => x ^ 2)
      (ψ := fun x : Real => x ^ 2) (by fun_prop) (by fun_prop)).integral_mul_eq_mul_integral
        hw.integrable_sq.aestronglyMeasurable
        hg.integrable_sq.aestronglyMeasurable
    simpa only [V, mul_pow, Function.comp_def, Pi.mul_apply, hws] using hs
  have hvv := inverse_count_independent_product_variance hw hg hi
  change variance V mu = _ at hvv
  rw [hwv, hwm] at hvv
  have hLp : MemLp (fun om => 1 + V om) 2 mu := (memLp_const (μ := mu) (1 : Real)).add hv
  change MemLp (fun om => 1 + V om) 2 mu ∧
    (∫ om, (1 + V om) ^ 2 ∂mu) ≤ _ ∧ variance (fun om => 1 + V om) mu ≤ _
  refine ⟨hLp, ?_, ?_⟩
  · calc
      (∫ om, (1 + V om) ^ 2 ∂mu) ≤ ∫ om, 2 + 2 * V om ^ 2 ∂mu := by
        apply integral_mono hLp.integrable_sq
          ((integrable_const 2).add (hv.integrable_sq.const_mul 2))
        intro om
        change (1 + V om) ^ 2 ≤ 2 + 2 * V om ^ 2
        nlinarith only [sq_nonneg (V om - 1)]
      _ = 2 + 2 * (∫ om, V om ^ 2 ∂mu) := by
        rw [integral_add (integrable_const 2) (hv.integrable_sq.const_mul 2),
          integral_const, integral_const_mul]
        simp
      _ ≤ _ := by
        rw [hs]
        have hb := mul_le_mul_of_nonneg_left hgs
          (show 0 ≤ (rho : Real) ^ 2 + rho by positivity)
        convert add_le_add_left
          (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : Real) ≤ 2)) 2 using 1 <;>
          first | rfl | ring
  · rw [variance_const_add hv.aestronglyMeasurable 1, hvv]
    have hb := mul_le_mul_of_nonneg_left hgs rho.coe_nonneg
    have hc := mul_le_mul_of_nonneg_left hgv (sq_nonneg (rho : Real))
    calc
      _ ≤ (rho : Real) * (2 ^ 16 / (1 + (lam : Real)) ^ 2) +
          (rho : Real) ^ 2 * (2 ^ 16 * (lam : Real) / (1 + (lam : Real)) ^ 4) :=
        add_le_add hb hc
      _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:Om,mu,X,lam,u,hX,hlaw,hind), All three independent Poisson factors give the cell variance envelope.  This gives [the stated result](goal).-/
-- @node: inverse_count_poisson_cell_variance
lemma inverse_count_poisson_cell_variance {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (X : Fin 3 → Om → Nat)
    (lam : Fin 3 → NNReal) (u : Real)
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, mu.map (X i) = poissonMeasure (lam i))
    (hind : iIndepFun X mu) :
    MemLp (fun om => (X 0 om : Real) / u *
      (1 + (X 2 om : Real) / ((X 1 om : Real) + 1))) 2 mu ∧
    variance (fun om => (X 0 om : Real) / u *
      (1 + (X 2 om : Real) / ((X 1 om : Real) + 1))) mu ≤
      (lam 0 : Real) / u ^ 2 * (2 + 2 * (2 ^ 16 : Real) *
        ((lam 2 : Real) ^ 2 + lam 2) / (1 + (lam 1 : Real)) ^ 2) +
      ((lam 0 : Real) / u) ^ 2 * (2 ^ 16 : Real) *
        ((lam 2 : Real) / (1 + (lam 1 : Real)) ^ 2 +
          (lam 2 : Real) ^ 2 * (lam 1 : Real) / (1 + (lam 1 : Real)) ^ 4) := by
  obtain ⟨hz, hzm, _, hzv⟩ :=
    inverse_count_poisson_count_moments mu (X 0) (lam 0) (hX 0) (hlaw 0)
  have hwk : IndepFun (X 2) (X 1) mu := hind.indepFun (by decide)
  obtain ⟨hb, hbs, hbv⟩ := inverse_count_weight_moments mu (X 1) (X 2)
    (lam 1) (lam 2) (hX 1) (hX 2) (hlaw 1) (hlaw 2) hwk
  have hip := (hind.indepFun_prodMk hX 2 1 0 (by decide) (by decide)).symm
  have hi : IndepFun (fun om => (X 0 om : Real) / u)
      (fun om => 1 + (X 2 om : Real) / ((X 1 om : Real) + 1)) mu :=
    hip.comp (φ := fun k : Nat => (k : Real) / u)
      (ψ := fun kw : Nat × Nat => 1 + (kw.1 : Real) / ((kw.2 : Real) + 1))
      (by fun_prop) (by fun_prop)
  have hzu : MemLp (fun om => (X 0 om : Real) / u) 2 mu := by
    simpa only [div_eq_mul_inv] using hz.mul_const u⁻¹
  refine ⟨inverse_count_independent_product_memLp hzu hb hi, ?_⟩
  rw [inverse_count_independent_product_variance hzu hb hi,
    integral_div, hzm]
  have hv : variance (fun om => (X 0 om : Real) / u) mu = (lam 0 : Real) / u ^ 2 := by
    simp only [div_eq_mul_inv, variance_mul_const, hzv, inv_pow]
  rw [hv]
  calc
    _ ≤ (lam 0 : Real) / u ^ 2 * (2 + 2 * (2 ^ 16 : Real) *
          ((lam 2 : Real) ^ 2 + lam 2) / (1 + (lam 1 : Real)) ^ 2) +
        ((lam 0 : Real) / u) ^ 2 * ((2 ^ 16 : Real) *
          ((lam 2 : Real) / (1 + (lam 1 : Real)) ^ 2 +
            (lam 2 : Real) ^ 2 * (lam 1 : Real) / (1 + (lam 1 : Real)) ^ 4)) :=
      add_le_add (mul_le_mul_of_nonneg_left hbs (by positivity))
        (mul_le_mul_of_nonneg_left hbv (sq_nonneg _))
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:Om,J,mu,X,hX,hind,u,hjk,j,k), Statistics computed in distinct three-count cells are independent.  This gives [the stated result](goal).-/
-- @node: inverse_count_cell_blocks_independent
lemma inverse_count_cell_blocks_independent {Om : Type} [MeasurableSpace Om]
    {J : Type} (mu : Measure Om)
    (X : Fin 3 × J → Om → Nat) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X mu) (u : Real) (j k : J) (hjk : j ≠ k) :
    IndepFun (fun om => (X (0, j) om : Real) / u *
      (1 + (X (2, j) om : Real) / ((X (1, j) om : Real) + 1)))
      (fun om => (X (0, k) om : Real) / u *
        (1 + (X (2, k) om : Real) / ((X (1, k) om : Real) + 1))) mu := by
  classical
  let S : Finset (Fin 3 × J) := Finset.univ ×ˢ {j}
  let T : Finset (Fin 3 × J) := Finset.univ ×ˢ {k}
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxj : x.2 = j := by simpa only [S, Finset.mem_product, Finset.mem_univ,
      Finset.mem_singleton, true_and] using hx
    have hxk : x.2 = k := by simpa only [T, Finset.mem_product, Finset.mem_univ,
      Finset.mem_singleton, true_and] using hy
    exact hjk (hxj.symm.trans hxk)
  have hi := hind.indepFun_finset S T hd hX
  let f : (S → Nat) → Real := fun v =>
    (v ⟨(0, j), by simp [S]⟩ : Real) / u *
      (1 + (v ⟨(2, j), by simp [S]⟩ : Real) /
        ((v ⟨(1, j), by simp [S]⟩ : Real) + 1))
  let g : (T → Nat) → Real := fun v =>
    (v ⟨(0, k), by simp [T]⟩ : Real) / u *
      (1 + (v ⟨(2, k), by simp [T]⟩ : Real) /
        ((v ⟨(1, k), by simp [T]⟩ : Real) + 1))
  exact hi.comp (φ := f) (ψ := g) (by dsimp [f]; fun_prop) (by dsimp [g]; fun_prop)

end CausalSmith.Stat.AnnotationRarearmFrontier
