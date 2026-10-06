module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.FalseLight
public import Causalean.Mathlib.Probability.EventSelectedMixture

/-!
Variance algebra for pilot-controlled branch mixtures, without branch independence.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[Under the stated inputs and conditions](hyp:hpi,hVP,hVH,pi,VP,VH,mp,mh), [The Bernoulli branch-mixture variance expression admits a deterministic upper bound](goal).
-/
-- @node: branch_mixture_variance_le
lemma branch_mixture_variance_le (pi VP VH mp mh : Real)
    (hpi : pi ∈ Set.Icc 0 1) (hVP : 0 ≤ VP) (hVH : 0 ≤ VH) :
    pi * VP + (1 - pi) * VH + pi * (1 - pi) * (mp - mh) ^ 2 ≤ VP + VH + (mp - mh) ^ 2 := by
  have hmix : pi * (1 - pi) ≤ 1 := by
    nlinarith [sq_nonneg pi]
  have hpol : pi * VP ≤ VP :=
    mul_le_of_le_one_left hVP hpi.2
  have hheavy : (1 - pi) * VH ≤ VH :=
    mul_le_of_le_one_left hVH (by linarith [hpi.1])
  have hbetween : pi * (1 - pi) * (mp - mh) ^ 2 ≤ (mp - mh) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) hmix
  exact add_le_add (add_le_add hpol hheavy) hbetween

/-- [Under the stated inputs and conditions](hyp:L,B,u,t,q,s,v), Both canonical branches are square-integrable, including null cells and zero intensities.  This gives [the stated result](goal).-/
-- @node: hybrid_cell_branches_memLp
lemma hybrid_cell_branches_memLp (L : Nat) (B u t q s v : Real) :
    MemLp (polynomialCellBranch L B u t) 2 (cellPoissonLaw u t q s v) ∧
    MemLp (inverseCellBranch u) 2 (cellPoissonLaw u t q s v) := by
  let muZ := poissonMeasure (Real.toNNReal (u * q))
  let muK := poissonMeasure (Real.toNNReal (t * s))
  let muW := poissonMeasure (Real.toNNReal (t * v))
  have hZ : MemLp (fun Z : Nat => (Z : Real) / u) 2 muZ := by
    simpa only [div_eq_mul_inv] using
      (Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two _).mul_const u⁻¹
  have hW : MemLp (fun W : Nat => (W : Real)) 2 muW :=
    Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two _
  have hG := poisson_factorial_polynomial_memLp (Real.toNNReal (t * s))
    (L - 1) (fun h => (chebG L).coeff h) (t * B)
  have hrec : MemLp (fun K : Nat => ((K : Real) + 1)⁻¹) 2 muK := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Causalean.Mathlib.Probability.Poisson.shifted_reciprocal_memLp_two
        (Real.toNNReal (t * s))
  have hpol := Causalean.Mathlib.Probability.memLp_mul_prod_two
    (hG.mul_const ((t * B)⁻¹)) hW
  have hheavy := Causalean.Mathlib.Probability.memLp_mul_prod_two hrec hW
  have hpol' := (memLp_const (μ := muK.prod muW) (1 : Real)).add hpol
  have hheavy' := (memLp_const (μ := muK.prod muW) (1 : Real)).add hheavy
  constructor
  · have hh := Causalean.Mathlib.Probability.memLp_mul_prod_two hZ hpol'
    convert hh using 1 <;> try rfl
    funext z
    simp only [polynomialCellBranch, Pi.add_apply, div_eq_mul_inv]
    ring
  · have hh := Causalean.Mathlib.Probability.memLp_mul_prod_two hZ hheavy'
    convert hh using 1 <;> try rfl
    funext z
    simp only [inverseCellBranch, Pi.add_apply, div_eq_mul_inv]
    ring

/-- [The implemented hybrid cell is exactly the pilot-event mixture of the two branches. ](goal)-/
-- @node: hybrid_cell_event_mixture
lemma hybrid_cell_event_mixture (L k0 : Nat) (B u t : Real) :
    (fun z : Nat × (Nat × Nat × Nat) =>
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2) =
    Causalean.Mathlib.Probability.eventSelectedMixture (Set.Iic k0)
      (polynomialCellBranch L B u t) (inverseCellBranch u) := by
  funext z
  by_cases hz : z.1 ≤ k0
  · simp [Causalean.Mathlib.Probability.eventSelectedMixture, hybridCellValue,
      polynomialCellBranch, hz, Set.mem_Iic, div_eq_mul_inv, mul_assoc, mul_comm]
  · simp [Causalean.Mathlib.Probability.eventSelectedMixture, hybridCellValue,
      inverseCellBranch, hz, Set.mem_Iic]

/-- [The actual pilot-selected cell has finite second moment under the independent pool law. ](goal)-/
-- @node: hybrid_pilot_cell_memLp
lemma hybrid_pilot_cell_memLp (L k0 : Nat) (B u tp t q s v : Real) :
    MemLp (fun z : Nat × (Nat × Nat × Nat) =>
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2) 2
      ((poissonMeasure (Real.toNNReal (tp * s))).prod (cellPoissonLaw u t q s v)) := by
  let : IsProbabilityMeasure (cellPoissonLaw u t q s v) := by
    unfold cellPoissonLaw
    infer_instance
  rw [hybrid_cell_event_mixture]
  exact Causalean.Mathlib.Probability.memLp_eventSelectedMixture _ _ _
    measurableSet_Iic _ _ (hybrid_cell_branches_memLp L B u t q s v).1
    (hybrid_cell_branches_memLp L B u t q s v).2

/-- [Equation (13): the independent pilot mixes branch variances and their mean separation;
the polynomial and heavy branches may share all their evaluation counts. ](goal)-/
-- @node: hybrid_pilot_cell_variance
lemma hybrid_pilot_cell_variance (L k0 : Nat) (B u tp t q s v : Real) :
    let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic k0)
    let nu := cellPoissonLaw u t q s v
    variance (fun z : Nat × (Nat × Nat × Nat) =>
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2)
      ((poissonMeasure (Real.toNNReal (tp * s))).prod nu) =
      pi * variance (polynomialCellBranch L B u t) nu +
        (1 - pi) * variance (inverseCellBranch u) nu + pi * (1 - pi) *
          ((∫ z, polynomialCellBranch L B u t z ∂nu) -
            ∫ z, inverseCellBranch u z ∂nu) ^ 2 := by
  let : IsProbabilityMeasure (cellPoissonLaw u t q s v) := by
    unfold cellPoissonLaw
    infer_instance
  dsimp only
  rw [hybrid_cell_event_mixture]
  exact Causalean.Mathlib.Probability.variance_eventSelectedMixture _ _ _
    measurableSet_Iic _ _ (hybrid_cell_branches_memLp L B u t q s v).1
    (hybrid_cell_branches_memLp L B u t q s v).2

/-- [Under the stated inputs and conditions](hyp:hL,hB,hu,ht,hs,hv,hmu,L,k0,B,u,tp,t,s,v,mu), The hybrid's bias is the pilot-weighted sum of the two explicit branch biases.  This gives [the stated result](goal).-/
-- @node: hybrid_pilot_cell_mean
lemma hybrid_pilot_cell_mean (L k0 : Nat) (B u tp t s v mu : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (hu : 0 < u) (ht : 0 < t)
    (hs : 0 < s) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1) :
    let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic k0)
    (∫ z : Nat × (Nat × Nat × Nat),
      hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2 ∂
      (poissonMeasure (Real.toNNReal (tp * s))).prod
        (cellPoissonLaw u t (s * mu) s v)) =
      (s + v) * mu - v * mu *
        (pi * (chebE L).eval (s / B) + (1 - pi) * Real.exp (-t * s)) := by
  let : IsProbabilityMeasure (cellPoissonLaw u t (s * mu) s v) := by
    unfold cellPoissonLaw
    infer_instance
  dsimp only
  rw [hybrid_cell_event_mixture]
  have hLp := hybrid_cell_branches_memLp L B u t (s * mu) s v
  rw [Causalean.Mathlib.Probability.integral_eventSelectedMixture _ _ _
    measurableSet_Iic _ _ (hLp.1.integrable (by norm_num)) (hLp.2.integrable (by norm_num))]
  obtain ⟨hp, hh⟩ := hybrid_branch_means L B u t s v mu hL hB hu ht hs hv hmu
  rw [hp, hh]
  ring

/-- [Under the stated inputs and conditions](hyp:L,hL,hB,hu,ht,hs,hsB,hv,hmu,heps,hov,B,u,t,s,v,mu,eps), Equation (2): overlap turns the light-cell approximation error into the public
bandwidth divided by epsilon and squared degree.  This gives [the stated result](goal).-/
-- @node: hybrid_light_polynomial_bias
lemma hybrid_light_polynomial_bias (L : Nat) (B u t s v mu eps : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (hu : 0 < u) (ht : 0 < t)
    (hs : 0 < s) (hsB : s ≤ B) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1)
    (heps : 0 < eps) (hov : eps * (s + v) ≤ s) :
    |(∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t (s * mu) s v) -
      (s + v) * mu| ≤ B / (eps * (L : Real) ^ 2) := by
  have hLpos : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
  obtain ⟨hE0, hE⟩ := (chebyshev_factorial_certificate L hL).1
    (s / B) (div_pos hs hB) ((div_le_one hB).2 hsB)
  have hEB : (chebE L).eval (s / B) ≤ B / ((L : Real) ^ 2 * s) := by
    calc
      _ ≤ ((L : Real) ^ 2 * (s / B))⁻¹ := hE.trans (min_le_right _ _)
      _ = _ := by field_simp
  rw [(hybrid_branch_means L B u t s v mu hL hB hu ht hs hv hmu).1]
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hv hmu.1) hE0)]
  have hvmu : v * mu ≤ v := mul_le_of_le_one_right hv hmu.2
  calc
    _ ≤ v * (B / ((L : Real) ^ 2 * s)) := mul_le_mul hvmu hEB hE0 hv
    _ ≤ B / (eps * (L : Real) ^ 2) := by
      apply (le_div_iff₀ (mul_pos heps (sq_pos_of_pos hLpos))).2
      have hvs : eps * v ≤ s := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hvs (div_nonneg hB.le hs.le)
      have heq : v * (B / ((L : Real) ^ 2 * s)) * (eps * (L : Real) ^ 2) =
          eps * v * (B / s) := by field_simp
      rw [heq]
      simpa only [mul_div_cancel₀ B hs.ne'] using hh

/-- [Under the stated inputs and conditions](hyp:L,hL,hB,hu,ht,hs,hsB,hv,hmu,heps,hov,B,u,t,s,v,mu,eps,pi), On a light cell the between-branch term of equation (13) is bounded by twice the
squared polynomial bias plus twice the squared inverse-count bias.  This gives [the stated result](goal).-/
-- @node: hybrid_light_between_branch_bound
lemma hybrid_light_between_branch_bound (L : Nat) (B u t s v mu eps pi : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (hu : 0 < u) (ht : 0 < t)
    (hs : 0 < s) (hsB : s ≤ B) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1)
    (heps : 0 < eps) (hov : eps * (s + v) ≤ s) :
    pi * (1 - pi) *
      ((∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t (s * mu) s v) -
        ∫ z, inverseCellBranch u z ∂cellPoissonLaw u t (s * mu) s v) ^ 2 ≤
      2 * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        2 * ((s + v) * Real.exp (-t * s)) ^ 2 := by
  let mp := ∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t (s * mu) s v
  let mh := ∫ z, inverseCellBranch u z ∂cellPoissonLaw u t (s * mu) s v
  let theta := (s + v) * mu
  have hp := hybrid_light_polynomial_bias L B u t s v mu eps
    hL hB hu ht hs hsB hv hmu heps hov
  have hp2 : (mp - theta) ^ 2 ≤ (B / (eps * (L : Real) ^ 2)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hp 2
  have hh := (hybrid_branch_means L B u t s v mu hL hB hu ht hs hv hmu).2
  have hheavy : |mh - theta| ≤ (s + v) * Real.exp (-t * s) := by
    dsimp [mh, theta]
    rw [hh, sub_sub_cancel_left, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg hv hmu.1) (Real.exp_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_right hv hmu.2).trans (by linarith)) (Real.exp_nonneg _)
  have hh2 : (mh - theta) ^ 2 ≤ ((s + v) * Real.exp (-t * s)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hheavy 2
  have hmix : pi * (1 - pi) ≤ 1 := by nlinarith [sq_nonneg pi]
  calc
    _ ≤ (mp - mh) ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hmix
    _ ≤ 2 * (mp - theta) ^ 2 + 2 * (mh - theta) ^ 2 := by
      nlinarith only [sq_nonneg ((mp - theta) + (mh - theta))]
    _ ≤ _ := by linarith

end CausalSmith.Stat.AnnotationRarearmFrontier
