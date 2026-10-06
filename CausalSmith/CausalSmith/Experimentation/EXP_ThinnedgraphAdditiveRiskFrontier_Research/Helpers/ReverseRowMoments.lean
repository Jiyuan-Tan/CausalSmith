module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ReverseTestMoments
public import Mathlib.Probability.Independence.Integration

/-!
# Actual source-row marginals for the reverse test

Injective restrictions of the full independent assignments and reveals have the
size-d product law. This connects the finite sign moments to labeled source rows.
-/

public section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Restricting an independent Boolean vector to distinct labels preserves its law.  [For the stated data and conditions](hyp:N,d,p,hp,e,he), [the stated conclusion holds](goal). -/
-- @node: reverse_pi_injection_law
lemma reverse_pi_injection_law {N d : ℕ} (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (e : Fin d → Fin N) (he : Function.Injective e) :
    (Measure.pi (fun _ : Fin N => bernoulliLaw p)).map (fun z k => z (e k)) =
      Measure.pi (fun _ : Fin d => bernoulliLaw p) := by
  let := bernoulliLaw_probability p hp
  have hi := (iIndepFun_pi (μ := fun _ : Fin N => bernoulliLaw p)
    (X := fun _ => (id : Bool → Bool)) (fun _ => measurable_id.aemeasurable)).precomp he
  have hm := hi.map_fun_eq_pi_map (fun k => (measurable_pi_apply (e k)).aemeasurable)
  simpa only [Function.id_def, (measurePreserving_eval
    (fun _ : Fin N => bernoulliLaw p) _).map_eq] using hm

/-- A row selected at distinct assignment and reveal labels has the actual row law.  [For the stated data and conditions](hyp:n,m,d,p,hp,v,j,hv,hj), [the stated conclusion holds](goal). -/
-- @node: reverse_row_injection_law
lemma reverse_row_injection_law {n m d : ℕ} (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (v : Fin d → Fin n) (j : Fin d → Fin m)
    (hv : Function.Injective v) (hj : Function.Injective j) :
    ((halfBernoulli (Fin n)).prod
      (Measure.pi (fun _ : Fin m => bernoulliLaw p))).map
        (fun zr => (fun k => zr.1 (v k), fun k => zr.2 (j k))) =
      (halfBernoulli (Fin d)).prod
        (Measure.pi (fun _ : Fin d => bernoulliLaw p)) := by
  have hm := Measure.map_prod_map (halfBernoulli (Fin n))
    (Measure.pi (fun _ : Fin m => bernoulliLaw p))
    (measurable_of_finite (fun z k => z (v k)))
    (measurable_of_finite (fun r k => r (j k)))
  rw [show (halfBernoulli (Fin n)).map (fun z k => z (v k)) =
      halfBernoulli (Fin d) from
    reverse_pi_injection_law (1 / 2) (by constructor <;> norm_num) v hv,
    reverse_pi_injection_law p hp j hj] at hm
  exact hm.symm

/-- Integrating a row function against its actual labeled inputs uses the row marginal.  [For the stated data and conditions](hyp:n,m,d,p,hp,v,j,hv,hj,f), [the stated conclusion holds](goal). -/
-- @node: reverse_row_injection_integral
lemma reverse_row_injection_integral {n m d : ℕ} (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (v : Fin d → Fin n) (j : Fin d → Fin m)
    (hv : Function.Injective v) (hj : Function.Injective j)
    (f : Assign (Fin d) × (Fin d → Bool) → ℝ) :
    (∫ zr, f (fun k => zr.1 (v k), fun k => zr.2 (j k))
      ∂((halfBernoulli (Fin n)).prod
        (Measure.pi (fun _ : Fin m => bernoulliLaw p)))) =
      ∫ zr, f zr ∂((halfBernoulli (Fin d)).prod
        (Measure.pi (fun _ : Fin d => bernoulliLaw p))) := by
  rw [← reverse_row_injection_law p hp v j hv hj,
    integral_map (measurable_of_finite _).aemeasurable
      (measurable_of_finite f).aestronglyMeasurable]

/-- The actual row product law gives the revealed sign energy dp.  [For the stated data and conditions](hyp:d,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_row_second_moment
lemma reverse_row_second_moment (d : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, (∑ k : Fin d, if zr.2 k then signOf (zr.1 k) else 0) ^ 2
      ∂((halfBernoulli (Fin d)).prod
        (Measure.pi (fun _ : Fin d => bernoulliLaw p)))) = d * p := by
  let := halfBernoulli_probability (V := Fin d)
  let := bernoulliLaw_probability p hp
  rw [integral_prod_symm _ Integrable.of_finite]
  simp_rw [← Finset.sum_filter]
  exact reverse_revealed_second_moment_average d p hp

/-- The actual row product law gives the signal mean dp.  [For the stated data and conditions](hyp:d,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_row_product_mean
lemma reverse_row_product_mean (d : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, (∑ k : Fin d, if zr.2 k then signOf (zr.1 k) else 0) *
      (∑ k : Fin d, signOf (zr.1 k))
      ∂((halfBernoulli (Fin d)).prod
        (Measure.pi (fun _ : Fin d => bernoulliLaw p)))) = d * p := by
  let := halfBernoulli_probability (V := Fin d)
  let := bernoulliLaw_probability p hp
  rw [integral_prod_symm _ Integrable.of_finite]
  simp_rw [← Finset.sum_filter]
  exact reverse_revealed_total_product_mean_average d p hp

/-- The actual row product law bounds the signal second moment by 3d²p.  [For the stated data and conditions](hyp:d,p,hp), [the stated conclusion holds](goal). -/
-- @node: reverse_row_product_second_le
lemma reverse_row_product_second_le (d : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    (∫ zr, ((∑ k : Fin d, if zr.2 k then signOf (zr.1 k) else 0) *
      (∑ k : Fin d, signOf (zr.1 k))) ^ 2
      ∂((halfBernoulli (Fin d)).prod
        (Measure.pi (fun _ : Fin d => bernoulliLaw p)))) ≤ 3 * (d : ℝ) ^ 2 * p := by
  let := halfBernoulli_probability (V := Fin d)
  let := bernoulliLaw_probability p hp
  rw [integral_prod_symm _ Integrable.of_finite]
  simp_rw [mul_pow, ← Finset.sum_filter]
  exact reverse_revealed_total_mixed_moment_average_le d p hp

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
