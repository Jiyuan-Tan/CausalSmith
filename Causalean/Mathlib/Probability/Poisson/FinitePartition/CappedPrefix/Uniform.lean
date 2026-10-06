module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic

/-!
# Uniform permutation and Boolean mark laws

An iid sample remains iid after a coordinate permutation. Independent fair
Boolean marks pair with that sample to give the paired iid product law. The
finite mark and permutation normalizations are explicit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- [The fair Boolean law](goal) assigns probability one half to each Boolean value. -/
noncomputable def fairBoolLaw : Measure Bool :=
  (1 / 2 : ENNReal) • (Measure.dirac false + Measure.dirac true)

/-- [The fair Boolean law is a probability measure](goal). -/
instance fairBoolLaw_isProbabilityMeasure : IsProbabilityMeasure fairBoolLaw := by
  /- Evaluate the two Dirac measures at `univ`; their total mass is two. -/
  refine ⟨?_⟩
  simp [fairBoolLaw, smul_eq_mul]
  exact ENNReal.inv_two_add_inv_two

/-- For [an iid probability law](hyp:μ), [a sample size](hyp:n), and [a coordinate permutation](hyp:perm),
[reordering its finite iid product leaves the law unchanged](goal). -/
theorem map_perm_pi {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (perm : Equiv.Perm (Fin n)) :
    Measure.map (fun x : Fin n → X => fun i => x (perm i))
      (Measure.pi (fun _ : Fin n => μ)) =
      Measure.pi (fun _ : Fin n => μ) := by
  /- Use `measurePreserving_piCongrLeft` for the index equivalence `perm`. -/
  have hf : (fun x : Fin n → X => fun i => x (perm i)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) perm.symm :
        (Fin n → X) → (Fin n → X)) := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hf]
  simpa using Measure.pi_map_piCongrLeft perm.symm (fun _ : Fin n => μ)

/-- For [an iid probability law](hyp:μ), [a sample size](hyp:n), and [a coordinate permutation](hyp:perm),
[independently fair marked permuted observations have the paired iid product law](goal). -/
theorem map_permuted_marked_pi {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (perm : Equiv.Perm (Fin n)) :
    Measure.map
      (fun z : (Fin n → X) × (Fin n → Bool) =>
        fun i => (z.1 (perm i), z.2 i))
      ((Measure.pi (fun _ : Fin n => μ)).prod
        (Measure.pi (fun _ : Fin n => fairBoolLaw))) =
      Measure.pi (fun _ : Fin n => μ.prod fairBoolLaw) := by
  /- Combine `map_perm_pi` with `Measure.pi_prod`/the measurable Pi-product equivalence. -/
  let f : (Fin n → X) → (Fin n → X) := fun x i => x (perm i)
  let e := MeasurableEquiv.arrowProdEquivProdArrow X Bool (Fin n)
  have hf : Measurable f := by
    unfold f
    fun_prop
  have hpair : Measure.map e.symm
      ((Measure.pi (fun _ : Fin n => μ)).prod
        (Measure.pi (fun _ : Fin n => fairBoolLaw))) =
      Measure.pi (fun _ : Fin n => μ.prod fairBoolLaw) :=
    (measurePreserving_arrowProdEquivProdArrow X Bool (Fin n)
      (fun _ => μ) (fun _ => fairBoolLaw)).symm.map_eq
  calc
    Measure.map (fun z : (Fin n → X) × (Fin n → Bool) =>
      fun i => (z.1 (perm i), z.2 i))
        ((Measure.pi (fun _ : Fin n => μ)).prod
          (Measure.pi (fun _ : Fin n => fairBoolLaw))) =
      Measure.map e.symm
        (Measure.map (Prod.map f id)
          ((Measure.pi (fun _ : Fin n => μ)).prod
            (Measure.pi (fun _ : Fin n => fairBoolLaw)))) := by
          rw [Measure.map_map e.symm.measurable (hf.prodMap measurable_id)]
          rfl
    _ = Measure.map e.symm
        ((Measure.pi (fun _ : Fin n => μ)).prod
          (Measure.pi (fun _ : Fin n => fairBoolLaw))) := by
          rw [← Measure.map_prod_map _ _ hf measurable_id]
          rw [show Measure.map f (Measure.pi (fun _ : Fin n => μ)) =
            Measure.pi (fun _ : Fin n => μ) from map_perm_pi μ n perm]
          simp
    _ = _ := hpair

/-- For [a sample size](hyp:n), [the finite law of independent fair Boolean marks](goal)
is the uniform average of the point masses on all Boolean mark vectors. -/
theorem fairMarkPi_eq_uniform_sum (n : ℕ) :
    Measure.pi (fun _ : Fin n => fairBoolLaw) =
      (Fintype.card (Fin n → Bool) : ENNReal)⁻¹ •
        (∑ marks : Fin n → Bool, Measure.dirac marks) := by
  /- Compare singleton masses, using `Measure.pi_pi` and `Fintype.card_fun`. -/
  have hpoint (b : Bool) : fairBoolLaw {b} = 2⁻¹ := by
    cases b <;> simp [fairBoolLaw, smul_eq_mul]
  apply Measure.ext_of_singleton
  intro marks
  rw [Measure.pi_singleton]
  simp [hpoint, Finset.prod_const]
  exact ENNReal.inv_pow.symm

/-- For [a sample size](hyp:n), [the finite permutation and mark averaging weights sum to one](goal),
including when the sample size is zero. -/
theorem perm_mark_weight_sum (n : ℕ) :
    (∑ _perm : Equiv.Perm (Fin n),
      ∑ _marks : Fin n → Bool,
        (1 : ℝ) / ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
          (Fintype.card (Fin n → Bool) : ℝ))) = 1 := by
  /- Both finite types are nonempty; reduce the two constant sums to cardinalities. -/
  have hp : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hm : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  simp [div_eq_mul_inv, hp, ← mul_assoc]

end Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix
