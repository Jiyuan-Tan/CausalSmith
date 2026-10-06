module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairEffectBounds

/-! # Exact fair singleton matching

The explicit comparator effect matches the two-point risk average at both cell
endpoints. The zero-effect and zero-amplitude identities also cover the axes when
assembling matching from the normalized root equation.
-/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The fair comparator preserves effect on the zero-amplitude axis. [the stated conclusion](goal) holds. -/
lemma comparatorEffect_zero_amplitude (t : ℝ) : comparatorEffect t 0 = t := by
  simp [comparatorEffect]

/-- The fair comparator vanishes on the zero-effect axis. [the stated conclusion](goal) holds. -/
-- @node: comparatorEffect_zero_effect
lemma comparatorEffect_zero_effect (δ : ℝ) : comparatorEffect 0 δ = 0 := by
  simp [comparatorEffect]

/-- Zero effect makes the risk shift the identity. [the stated conclusion](goal) holds. -/
-- @node: riskShift_zero_effect
lemma riskShift_zero_effect (ξ : ℝ) : riskShift 0 ξ = ξ := by
  simp [riskShift]

/-- The fair numerator vanishes for zero amplitude, at every centering value. [the stated conclusion](goal) holds. -/
-- @node: fairNumerator_zero_amplitude
lemma fairNumerator_zero_amplitude (t ξ u : ℝ) : fairNumerator t 0 ξ u = 0 := by
  simp [fairNumerator, comparatorEffect_zero_amplitude, signAverage,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- The mean-zero sign field gives exact matching at zero effect. [the stated conclusion](goal) holds. -/
-- @node: fairNumerator_zero_effect
lemma fairNumerator_zero_effect (δ ξ u : ℝ) : fairNumerator 0 δ ξ u = 0 := by
  simp [fairNumerator, comparatorEffect_zero_effect, riskShift_zero_effect,
    signAverage, Fintype.sum_prod_type, Fintype.sum_bool, localSignField, signValue]
  ring

/-- Positivity of the logarithm arguments and shifted-risk denominators in the fair construction. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:ht,hδ) hold, and [the stated conclusion follows](goal). -/
-- @node: fair_matching_denominators
lemma fair_matching_denominators (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100) :
    let d := Real.exp t - 1
    let B := 1 + d*(2/5)
    0 < B ∧ 0 < 1-d*δ^2/((2/5)*B) ∧
    0 < 1+d*δ^2/((1-2/5)*B) ∧
    0 < 1+d*(2/5+δ) ∧ 0 < 1+d*(2/5-δ) := by
  dsimp only
  obtain ⟨hdlo, hdhi⟩ := fair_exp_increment_bounds t ht
  have hd : 0 ≤ Real.exp t - 1 := ht.1.trans hdlo
  have hd' : Real.exp t - 1 ≤ 1/3 := by linarith [ht.2]
  obtain ⟨hδlo, hδhi⟩ := abs_le.mp hδ
  have hsq : δ^2 ≤ 1/10000 := by nlinarith
  have hB : 1 ≤ 1+(Real.exp t-1)*(2/5) := by linarith
  have hBp : 0 < 1+(Real.exp t-1)*(2/5) := by linarith
  have hprod : (Real.exp t-1)*δ^2 ≤ 1/30000 := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsq)]
  refine ⟨hBp, ?_, ?_, ?_, ?_⟩
  · have hden : 0 < (2/5 : ℝ)*(1+(Real.exp t-1)*(2/5)) := by positivity
    have hlt : (Real.exp t-1)*δ^2/((2/5)*(1+(Real.exp t-1)*(2/5))) < 1 :=
      (div_lt_one hden).mpr (by linarith)
    linarith
  · positivity
  · have hx : 0 ≤ 2/5+δ := by linarith
    positivity
  · have hx : 0 ≤ 2/5-δ := by linarith
    positivity

/-- [The comparator exponential is exactly the rational odds correction in the roadmap.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:ht). -/
-- @node: comparatorEffect_exp_formula
lemma comparatorEffect_exp_formula (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100) :
    Real.exp (comparatorEffect t δ) = Real.exp t *
      (1-(Real.exp t-1)*δ^2/((2/5)*(1+(Real.exp t-1)*(2/5)))) /
      (1+(Real.exp t-1)*δ^2/((1-2/5)*(1+(Real.exp t-1)*(2/5)))) := by
  obtain ⟨_, ha, hb, _, _⟩ := fair_matching_denominators t δ ht hδ
  unfold comparatorEffect
  rw [Real.exp_sub, Real.exp_add, Real.exp_log ha, Real.exp_log hb]

/-- [At the fixed centering value, the fair comparator matches the average of the two shifted risks.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:ht). -/
-- @node: fair_two_point_matching
lemma fair_two_point_matching (t δ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100) :
    (riskShift t (2/5+δ)+riskShift t (2/5-δ))/2 =
      riskShift (comparatorEffect t δ) (2/5) := by
  obtain ⟨hB, ha, hb, hp, hm⟩ := fair_matching_denominators t δ ht hδ
  have he := comparatorEffect_exp_formula t δ ht hδ
  have hc : 0 < 1+(Real.exp (comparatorEffect t δ)-1)*(2/5) := by
    nlinarith [Real.exp_pos (comparatorEffect t δ)]
  have hd : 0 ≤ Real.exp t - 1 := ht.1.trans (fair_exp_increment_bounds t ht).1
  unfold riskShift
  field_simp (disch := nlinarith [Real.exp_pos t]) at he ⊢
  field_simp (disch := positivity) at he
  nlinarith [he]

/-- [At either cell endpoint, the sign field has the law of one fair sign.](goal) Under [the stated assumptions](hyp:F,hu). -/
-- @node: fair_endpoint_sign_average
lemma fair_endpoint_sign_average (F : ℝ → ℝ) (u : ℝ) (hu : u = 0 ∨ u = 1) :
    signAverage (fun s => F (localSignField u s)) = (F 1+F (-1))/2 := by
  rcases hu with rfl | rfl
  · simp [signAverage, Fintype.sum_prod_type, Fintype.sum_bool, localSignField, signValue]
    ring
  · simp [signAverage, Fintype.sum_prod_type, Fintype.sum_bool, localSignField, signValue]
    ring

/-- [The explicit fair comparator has exactly zero endpoint numerator at the prescribed center.](goal) Under [the stated assumptions](hyp:hδ,hu). Under [the stated assumptions](hyp:ht). -/
-- @node: fairNumerator_endpoints
lemma fairNumerator_endpoints (t δ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (hu : u = 0 ∨ u = 1) : fairNumerator t δ (2/5) u = 0 := by
  unfold fairNumerator
  rw [fair_endpoint_sign_average (fun z => riskShift t (2/5+δ*z)) u hu]
  simp only [mul_one, mul_neg_one, ← sub_eq_add_neg]
  rw [fair_two_point_matching t δ ht hδ, sub_self]

/-- [A normalized root gives singleton matching; the zero axes use their exact identities.](goal) Under [the stated assumptions](hyp:hroot). Under [the stated assumptions](hyp:hdiv). -/
-- @node: fair_matching_of_normalized_equation
lemma fair_matching_of_normalized_equation (t δ ξ u : ℝ)
    (hroot : fairEquation t δ ξ u = 0)
    (hdiv : t*δ ≠ 0 → fairEquation t δ ξ u = fairNumerator t δ ξ u/(t*δ^2)) :
    signAverage (fun s => riskShift t (ξ+δ*localSignField u s)) =
      riskShift (comparatorEffect t δ) ξ := by
  apply sub_eq_zero.mp
  change fairNumerator t δ ξ u = 0
  by_cases ht : t = 0
  · subst t
    exact fairNumerator_zero_effect δ ξ u
  by_cases hδ : δ = 0
  · subst δ
    exact fairNumerator_zero_amplitude t ξ u
  have hden : t*δ^2 ≠ 0 := mul_ne_zero ht (pow_ne_zero _ hδ)
  have hquot : fairNumerator t δ ξ u/(t*δ^2) = 0 :=
    (hdiv (mul_ne_zero ht hδ)).symm.trans hroot
  exact (div_eq_zero_iff.mp hquot).resolve_right hden

end CausalSmith.Stat.LogoddsLowsmoothFrontier
