module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Basic
public import Mathlib.Probability.Distributions.Uniform
/-! Uniform finite sign averages as independent fair-bit product integrals, and the
published bounded-differences gate transported to arbitrary finite sign indices. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Every atom of the independent fair-bit product has the same reciprocal-cardinality mass. [The displayed conclusion](goal) follows. -/
-- @node: fairSignProduct_singleton
lemma fairSignProduct_singleton {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → Bool) :
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure) {z} =
      (Fintype.card (ι → Bool) : ENNReal)⁻¹ := by
  classical
  rw [Measure.pi_singleton]
  simp only [(PMF.uniformOfFintype Bool).toMeasure_apply_singleton _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- Integrating a function of independent fair bits is exactly its uniform finite average. [The displayed conclusion](goal) follows. -/
-- @node: integral_fairSignProduct
lemma integral_fairSignProduct {ι : Type*} [Fintype ι] [DecidableEq ι] (F : (ι → Bool) → ℝ) :
    (∫ z, F z ∂Measure.pi (fun _ : ι => (PMF.uniformOfFintype Bool).toMeasure)) =
      (∑ z, F z) / (Fintype.card (ι → Bool) : ℝ) := by
  classical
  rw [integral_fintype Integrable.of_finite]
  simp only [Measure.real, fairSignProduct_singleton, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

/-- The published independent-coordinate mgf gate bounds a centered uniform finite-sign
average on any finite index type, after reindexing its coordinates by `Fin`.  [the theorem's stated inputs and assumptions](hyp:ι,F,hzero,hbound,c,hc,hchange,u,hu), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:gate). -/
-- @node: finite_sign_mgf_average
lemma finite_sign_mgf_average (gate : BoundedDifferencesMGF)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : (ι → Bool) → ℝ)
    (hzero : (∑ z, F z) = 0) (hbound : ∃ C : ℝ, ∀ z, |F z| ≤ C)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hchange : ∀ i z b, |F z - F (Function.update z i b)| ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑ z, Real.exp (u * F z)) / (Fintype.card (ι → Bool) : ℝ) ≤
      Real.exp (u^2 / 8 * ∑ i, (c i)^2) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (Fin (Fintype.card ι) → Bool) ≃ (ι → Bool) :=
    e.arrowCongr (Equiv.refl Bool)
  have hupdate (z : Fin (Fintype.card ι) → Bool) (i : Fin (Fintype.card ι)) (b : Bool) :
      E (Function.update z i b) = Function.update (E z) (e i) b := by
    funext j
    change Function.update z i b (e.symm j) = Function.update (E z) (e i) b j
    by_cases hj : j = e i
    · subst j; simp
    · have hi : e.symm j ≠ i := by intro h; apply hj; exact (e.symm_apply_eq).mp h
      simp [Function.update_of_ne hj, Function.update_of_ne hi, E, Equiv.arrowCongr]
  have hmean :
      (∫ z, F (E z) ∂Measure.pi
        (fun _ : Fin (Fintype.card ι) => (PMF.uniformOfFintype Bool).toMeasure)) = 0 := by
    rw [integral_fairSignProduct, E.sum_comp F, hzero, zero_div]
  have hm := gate (Fintype.card ι) (fun _ => Bool) (fun _ => inferInstance)
    (fun _ => (PMF.uniformOfFintype Bool).toMeasure) (fun _ => inferInstance)
    (fun z => F (E z)) (by fun_prop) (by
      obtain ⟨C, hC⟩ := hbound
      exact ⟨C, fun z => hC (E z)⟩)
    (fun i => c (e i)) (fun i => hc (e i)) (by
      intro i z b
      rw [hupdate]
      exact hchange (e i) (E z) b) u hu
  rw [hmean] at hm
  simp only [sub_zero] at hm
  rw [integral_fairSignProduct, E.sum_comp (fun z => Real.exp (u * F z))] at hm
  have hcard : Fintype.card (Fin (Fintype.card ι) → Bool) = Fintype.card (ι → Bool) :=
    Fintype.card_congr E
  rw [hcard, e.sum_comp (fun i => (c i)^2)] at hm
  exact hm

end CausalSmith.Stat.PrivateCateRoughdesign
