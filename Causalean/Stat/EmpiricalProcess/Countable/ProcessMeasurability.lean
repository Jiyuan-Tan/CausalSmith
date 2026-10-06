module
public import Causalean.Stat.EmpiricalProcess.Countable.Basic

/-!
# Legal fourth moments of countable bounded processes

Countability makes the real supremum measurable; uniform bounds justify the
conditionally complete real supremum and every fourth-moment integral.
These are genuine conclusions, not moment assumptions in the symmetrization API.
-/

public section

open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

variable {Ω ι : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (F : BoundedClass Ω ι)

/-- [Every member](hyp:i) of a uniformly bounded measurable class [is
integrable under the probability law μ](goal). -/
theorem BoundedClass.integrable (i : ι) : Integrable (F.f i) μ := by
  exact Integrable.of_bound (F.measurable i).aestronglyMeasurable F.bound
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using F.bounded i x))

/-- If [a bound B is nonnegative](hyp:B,hB) and [every entry of a real
vector of length n is at most B in absolute value](hyp:a,ha,n), then [the
absolute value of the entries' sum divided by n is at most B](goal),
including the empty sum. -/
theorem normalized_sum_bound {n : ℕ} (a : Fin n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (ha : ∀ j, |a j| ≤ B) :
    |(n : ℝ)⁻¹ * ∑ j, a j| ≤ B := by
  by_cases hn : n = 0
  · subst n
    simpa using hB
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc
    |(n : ℝ)⁻¹ * ∑ j, a j| = (n : ℝ)⁻¹ * |∑ j, a j| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    _ ≤ (n : ℝ)⁻¹ * ∑ j, |a j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ha j) (by positivity)
    _ = B := by simp [hn']

/-- [Multiplying a real number by the sign ±1 attached to a Boolean value
leaves its absolute value unchanged](goal). -/
theorem abs_bool_sign (b : Bool) (a : ℝ) :
    |(if b then (1 : ℝ) else -1) * a| = |a| := by
  cases b <;> simp

/-- If [every member of a nonempty family of reals lies between 0 and
B](hyp:a,B,ha), then [the family's supremum also lies between 0 and
B](goal). -/
theorem supremum_bounds [Nonempty ι] (a : ι → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ B) : 0 ≤ iSup a ∧ iSup a ≤ B := by
  have hb : BddAbove (Set.range a) := ⟨B, by rintro _ ⟨i, rfl⟩; exact (ha i).2⟩
  exact ⟨le_ciSup_of_le hb (Classical.arbitrary ι) (ha _).1,
    ciSup_le fun i => (ha i).2⟩

/-- A measurable nonnegative bounded function has an integrable fourth power
under every finite measure. -/
@[fun_prop] private theorem fourth_integrable {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (g : X → ℝ) (B : ℝ)
    (hg : Measurable g) (hb : ∀ x, 0 ≤ g x ∧ g x ≤ B) :
    Integrable (fun x => g x ^ 4) ν := by
  refine Integrable.of_bound (hg.pow_const 4).aestronglyMeasurable (B ^ 4) ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hb x).1 4)]
    exact pow_le_pow_left₀ (hb x).1 (hb x).2 4

variable [Countable ι] [Nonempty ι]

/-- For [any sample size n](hyp:n), [the centered supremum of the class is
a measurable function of the sample, lies between zero and twice the class
bound, and has an integrable fourth power under the iid product law](goal). -/
theorem centeredSup_legal (n : ℕ) :
    Measurable (centeredSup μ F.f (n := n)) ∧
    (∀ x : Fin n → Ω, 0 ≤ centeredSup μ F.f x ∧
      centeredSup μ F.f x ≤ 2 * F.bound) ∧
    Integrable (fun x => centeredSup μ F.f x ^ 4)
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hm : Measurable (centeredSup μ F.f (n := n)) := by
    apply Measurable.iSup
    intro i
    unfold Causalean.Stat.Concentration.centeredEmpiricalAverage
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_apply] using
      (((measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        (F.measurable i).comp (measurable_pi_apply j))).sub measurable_const).norm)
  have hb : ∀ x : Fin n → Ω, 0 ≤ centeredSup μ F.f x ∧
      centeredSup μ F.f x ≤ 2 * F.bound := by
    intro x
    apply supremum_bounds
    intro i
    refine ⟨abs_nonneg _, ?_⟩
    have hi : |∫ z, F.f i z ∂μ| ≤ F.bound := by
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (f := F.f i) (C := F.bound)
        (ae_of_all μ fun z => by simpa only [Real.norm_eq_abs] using F.bounded i z))
    exact (abs_sub _ _).trans (by
      have ha := normalized_sum_bound (fun j => F.f i (x j)) F.bound
        F.bound_nonneg (fun j => F.bounded i (x j))
      change |(n : ℝ)⁻¹ * ∑ j, F.f i (x j)| + |∫ z, F.f i z ∂μ| ≤ _
      linarith)
  exact ⟨hm, hb, fourth_integrable _ _ _ hm hb⟩

/-- For [any sample size n](hyp:n), [the ghost supremum is jointly
measurable in the two samples, lies between zero and twice the class bound,
and has an integrable fourth power under the product of two iid
laws](goal). -/
theorem ghostSup_legal (n : ℕ) :
    Measurable (fun p : (Fin n → Ω) × (Fin n → Ω) => ghostSup F.f p.1 p.2) ∧
    (∀ x y : Fin n → Ω, 0 ≤ ghostSup F.f x y ∧ ghostSup F.f x y ≤ 2 * F.bound) ∧
    Integrable (fun p : (Fin n → Ω) × (Fin n → Ω) => ghostSup F.f p.1 p.2 ^ 4)
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) := by
  have hm : Measurable (fun p : (Fin n → Ω) × (Fin n → Ω) =>
      ghostSup F.f p.1 p.2) := by
    apply Measurable.iSup
    intro i
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_apply] using
      (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        ((F.measurable i).comp ((measurable_pi_apply j).comp measurable_fst)).sub
          ((F.measurable i).comp ((measurable_pi_apply j).comp measurable_snd)))).norm
  have hb : ∀ x y : Fin n → Ω, 0 ≤ ghostSup F.f x y ∧
      ghostSup F.f x y ≤ 2 * F.bound := by
    intro x y
    apply supremum_bounds
    intro i
    refine ⟨abs_nonneg _, normalized_sum_bound _ _ (mul_nonneg (by norm_num) F.bound_nonneg) ?_⟩
    intro j
    exact (abs_sub _ _).trans (by
      have hx := F.bounded i (x j)
      have hy := F.bounded i (y j)
      linarith)
  exact ⟨hm, hb, fourth_integrable _ _ _ hm (fun p => hb p.1 p.2)⟩

/-- For [any sample size n](hyp:n), [each fixed-sign signed supremum is a
measurable function of the sample lying between zero and the class bound,
and the sign average of its fourth power is integrable under the iid
product law](goal). -/
theorem signedSup_legal (n : ℕ) :
    (∀ σ : Fin n → Bool, Measurable (fun x => signedSup F.f x σ)) ∧
    (∀ x σ, 0 ≤ signedSup F.f (n := n) x σ ∧ signedSup F.f x σ ≤ F.bound) ∧
    Integrable (fun x => signAverage (fun σ => signedSup F.f x σ ^ 4))
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hm (σ : Fin n → Bool) : Measurable (fun x : Fin n → Ω =>
      signedSup F.f x σ) := by
    apply Measurable.iSup
    intro i
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_apply] using
      (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((F.measurable i).comp (measurable_pi_apply j)))).norm
  have hb : ∀ (x : Fin n → Ω) σ, 0 ≤ signedSup F.f x σ ∧
      signedSup F.f x σ ≤ F.bound := by
    intro x σ
    apply supremum_bounds
    intro i
    refine ⟨abs_nonneg _, normalized_sum_bound _ _ F.bound_nonneg ?_⟩
    intro j
    rw [abs_bool_sign]
    exact F.bounded i (x j)
  refine ⟨hm, hb, ?_⟩
  unfold signAverage
  exact (integrable_finsetSum _ fun σ _ =>
    fourth_integrable _ _ _ (hm σ) (fun x => hb x σ)).div_const _

/-- For [any sample size n](hyp:n) and [any fixed sign vector σ](hyp:σ),
[the σ-signed ghost supremum is jointly measurable in the two samples, its
fourth power is integrable under the product of two iid laws, and so is
every section obtained by freezing the first sample](goal). -/
theorem signedGhostSup_legal (n : ℕ) (σ : Fin n → Bool) :
    Measurable (fun p : (Fin n → Ω) × (Fin n → Ω) =>
      signedGhostSup F.f p.1 p.2 σ) ∧
    Integrable (fun p : (Fin n → Ω) × (Fin n → Ω) =>
      signedGhostSup F.f p.1 p.2 σ ^ 4)
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) ∧
    (∀ x : Fin n → Ω, Integrable (fun y => signedGhostSup F.f x y σ ^ 4)
      (Measure.pi (fun _ : Fin n => μ))) := by
  have hm : Measurable (fun p : (Fin n → Ω) × (Fin n → Ω) =>
      signedGhostSup F.f p.1 p.2 σ) := by
    apply Measurable.iSup
    intro i
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_apply] using
      (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        measurable_const.mul
          (((F.measurable i).comp ((measurable_pi_apply j).comp measurable_fst)).sub
            ((F.measurable i).comp ((measurable_pi_apply j).comp measurable_snd))))).norm
  have hb : ∀ x y : Fin n → Ω, 0 ≤ signedGhostSup F.f x y σ ∧
      signedGhostSup F.f x y σ ≤ 2 * F.bound := by
    intro x y
    apply supremum_bounds
    intro i
    refine ⟨abs_nonneg _, normalized_sum_bound _ _ (mul_nonneg (by norm_num) F.bound_nonneg) ?_⟩
    intro j
    rw [abs_bool_sign]
    exact (abs_sub _ _).trans (by
      have hx := F.bounded i (x j)
      have hy := F.bounded i (y j)
      linarith)
  refine ⟨hm, fourth_integrable
    ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))
    (fun p : (Fin n → Ω) × (Fin n → Ω) => signedGhostSup F.f p.1 p.2 σ)
    (2 * F.bound) hm (fun p => hb p.1 p.2), ?_⟩
  intro x
  have hmap : Measurable (fun y : Fin n → Ω => (x, y)) :=
    measurable_const.prodMk measurable_id
  have hs := hm.comp hmap
  exact fourth_integrable (Measure.pi (fun _ : Fin n => μ))
    (fun y => signedGhostSup F.f x y σ) (2 * F.bound) hs (fun y => hb x y)

end Causalean.Stat.EmpiricalProcess.Countable
