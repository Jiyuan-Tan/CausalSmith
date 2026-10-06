module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.Basic

/-!
# Finite count-and-label expansion

This module gives the explicit finite count-and-label-map expression for the
capped conditional mean, so downstream estimators can identify an existing
Rao--Blackwellized formula without changing its definition.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

private lemma map_labelPrefix_pi (p : I → ℝ≥0) (hp : ∑ i, p i = 1)
    {n m : ℕ} (h : m ≤ n) :
    Measure.map (fun w : Fin n → I ↦ fun k : Fin m ↦
        w ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
      (Measure.pi (fun _ : Fin n ↦ labelLaw p hp)) =
      Measure.pi (fun _ : Fin m ↦ labelLaw p hp) := by
  classical
  letI := labelLaw_isProbabilityMeasure p hp
  symm
  refine Measure.pi_eq (μ := fun _ : Fin m ↦ labelLaw p hp) (fun s hs ↦ ?_)
  rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  have hpre : (fun w : Fin n → I ↦ fun k : Fin m ↦
        w ⟨k.val, lt_of_lt_of_le k.isLt h⟩) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun j : Fin n ↦
        if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hw j
      split
      · exact hw ⟨j.val, ‹j.val < m›⟩
      · trivial
    · intro hw k
      simpa using hw ⟨k.val, lt_of_lt_of_le k.isLt h⟩
  rw [hpre, Measure.pi_pi]
  let t : Finset (Fin n) := Finset.univ.filter fun j ↦ j.val < m
  have ht (j : t) : j.val.val < m := by
    simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using j.property
  let e : Fin m ≃ t :=
    { toFun := fun k ↦ ⟨⟨k.val, lt_of_lt_of_le k.isLt h⟩, by simp [t, k.isLt]⟩
      invFun := fun j ↦ ⟨j.val.val, ht j⟩
      left_inv := fun k ↦ by rfl
      right_inv := fun j ↦ by ext; rfl }
  calc
    (∏ j : Fin n, (labelLaw p hp)
        (if hj : j.val < m then s ⟨j.val, hj⟩ else Set.univ)) =
        ∏ j : Fin n, if hj : j.val < m then
          (labelLaw p hp) (s ⟨j.val, hj⟩) else 1 := by
          apply Fintype.prod_congr
          intro j
          split <;> simp
    _ = ∏ j : t, (labelLaw p hp) (s ⟨j.val.val, ht j⟩) := by
      rw [Finset.prod_dite]
      simp only [Finset.prod_const_one, mul_one]
      apply Fintype.prod_congr
      intro j
      congr 2
    _ = ∏ k : Fin m, (labelLaw p hp) (s k) := by
      symm
      apply Fintype.prod_equiv e
      intro k
      rfl

private lemma integral_label_pi_eq_sum (p : I → ℝ≥0) (hp : ∑ i, p i = 1)
    (m : ℕ) (f : (Fin m → I) → ℝ) :
    (∫ w, f w ∂Measure.pi (fun _ : Fin m => labelLaw p hp)) =
      ∑ w : Fin m → I, (∏ k, (p (w k) : ℝ)) * f w := by
  classical
  have hmass (i : I) : (labelLaw p hp).real {i} = (p i : ℝ) := by
    unfold labelLaw
    rw [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
      PMF.ofFintype_apply]
    simp
  haveI := labelLaw_isProbabilityMeasure p hp
  rw [integral_fintype (Integrable.of_finite)]
  congr 1
  funext w
  rw [smul_eq_mul]
  congr 1
  rw [Measure.real_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro k _
  exact hmass (w k)

/-- Given [label masses](hyp:p) [summing to one](hyp:hp), [a Poisson mean](hyp:lambda),
[a fixed pool](hyp:x), [a stream statistic](hyp:T), and [an overflow value](hyp:zOver),
[the conditional mean equals the explicit finite sum over admissible counts and label
maps, plus the Poisson overflow mass times the overflow value](goal). -/
theorem fixedStatistic_eq_finite_sum
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0)
    {n : ℕ} (x : Fin n → X) (T : (I → FiniteSample X) → ℝ)
    (zOver : ℝ) :
    fixedStatistic p hp lambda x T zOver =
      (∑ M : Fin (n + 1),
        (poissonMeasure lambda).real {M.val} *
          ∑ w : Fin M.val → I,
            (∏ k : Fin M.val, (p (w k) : ℝ)) *
              T (labeledPrefix x M.val (Nat.le_of_lt_succ M.isLt) w)) +
        (poissonMeasure lambda).real (Set.Ioi n) * zOver := by
  classical
  let μ : Measure ℕ := poissonMeasure lambda
  let ρ : Measure (Fin n → I) := Measure.pi (fun _ : Fin n => labelLaw p hp)
  let f : ℕ × (Fin n → I) → ℝ := cappedStatistic x T zOver
  haveI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    haveI := labelLaw_isProbabilityMeasure p hp
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfinite : (Set.range f).Finite := by
    let g : Fin (n + 1) × (Fin n → I) → ℝ :=
      fun z => f (z.1.val, z.2)
    have hsub : Set.range f ⊆ Set.insert zOver (Set.range g) := by
      rintro a ⟨z, rfl⟩
      by_cases hz : z.1 ≤ n
      · right
        exact ⟨(⟨z.1, Nat.lt_succ_of_le hz⟩, z.2), rfl⟩
      · left
        simp [f, cappedStatistic, hz]
    exact (Set.finite_range g).insert zOver |>.subset hsub
  obtain ⟨C, hC⟩ := hfinite.isBounded.exists_norm_le
  have hf : Integrable f (μ.prod ρ) := by
    apply Integrable.of_bound (C := C)
    · exact (measurable_of_countable f).aestronglyMeasurable
    · filter_upwards [] with z
      exact hC (f z) ⟨z, rfl⟩
  have hprod :
      fixedStatistic p hp lambda x T zOver =
        ∫ m : ℕ, (∫ w : Fin n → I, f (m, w) ∂ρ) ∂μ := by
    change (∫ z, f z ∂μ.prod ρ) = _
    exact integral_prod f hf
  have hslice (m : ℕ) (hm : m ≤ n) :
      (∫ w : Fin n → I, f (m, w) ∂ρ) =
        ∑ w : Fin m → I, (∏ k, (p (w k) : ℝ)) *
          T (labeledPrefix x m hm w) := by
    let q : (Fin n → I) → (Fin m → I) :=
      fun w k => w ⟨k.val, lt_of_lt_of_le k.isLt hm⟩
    have hq : Measurable q := by fun_prop
    have hmeas : Measurable (fun w : Fin m → I => T (labeledPrefix x m hm w)) :=
      measurable_of_countable _
    calc
      (∫ w : Fin n → I, f (m, w) ∂ρ) =
          ∫ w : Fin n → I, T (labeledPrefix x m hm (q w)) ∂ρ := by
            congr 1
            funext w
            simp [f, cappedStatistic, hm, q]
      _ = ∫ w : Fin m → I, T (labeledPrefix x m hm w)
            ∂Measure.map q ρ :=
        (integral_map hq.aemeasurable hmeas.aestronglyMeasurable).symm
      _ = ∫ w : Fin m → I, T (labeledPrefix x m hm w)
            ∂Measure.pi (fun _ : Fin m => labelLaw p hp) := by
        rw [show Measure.map q ρ = Measure.pi (fun _ : Fin m => labelLaw p hp) from
          map_labelPrefix_pi p hp hm]
      _ = _ := integral_label_pi_eq_sum p hp m _
  have htail (m : ℕ) (hm : n < m) :
      (∫ w : Fin n → I, f (m, w) ∂ρ) = zOver := by
    have hn : ¬ m ≤ n := Nat.not_le.mpr hm
    simp [f, cappedStatistic, hn, ρ]
  let g : ℕ → ℝ := fun m => ∫ w : Fin n → I, f (m, w) ∂ρ
  have hg : Integrable g μ := hf.integral_prod_left
  have hcap : (↑(Finset.range (n + 1)) : Set ℕ) = Set.Iic n := by
    ext m
    simp
  have hfirst :
      (∫ m in Set.Iic n, g m ∂μ) =
        ∑ M : Fin (n + 1), μ.real {M.val} *
          ∑ w : Fin M.val → I, (∏ k, (p (w k) : ℝ)) *
            T (labeledPrefix x M.val (Nat.le_of_lt_succ M.isLt) w) := by
    rw [← hcap, setIntegral_finset (Finset.range (n + 1)) hg.integrableOn]
    simp_rw [smul_eq_mul]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro M _
    change μ.real {M.val} * (∫ w : Fin n → I, f (M.val, w) ∂ρ) = _
    rw [hslice M.val (Nat.le_of_lt_succ M.isLt)]
  have hlast : (∫ m in Set.Ioi n, g m ∂μ) = μ.real (Set.Ioi n) * zOver := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun m hm => htail m hm)]
    simp [Measure.real_def]
  rw [hprod]
  calc
    (∫ m, g m ∂μ) =
        (∫ m in Set.Iic n, g m ∂μ) + (∫ m in Set.Ioi n, g m ∂μ) := by
          simpa only [Set.compl_Iic] using
            (integral_add_compl measurableSet_Iic hg).symm
    _ = _ := by rw [hfirst, hlast]

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
