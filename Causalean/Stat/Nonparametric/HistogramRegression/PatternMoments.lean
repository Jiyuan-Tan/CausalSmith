module
public import Causalean.Stat.Nonparametric.HistogramRegression.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Membership-pattern product moments

A fixed subset of sample indices defines a measurable rectangle: selected
coordinates lie in a given cell, and other coordinates lie in its complement.
Mathlib's restricted product measure and coordinate-product integral formulas
give the factorization directly. The diagonal and centered cross-coordinate
moments are isolated before the squared-sum identity. This layer depends only
on the estimator definitions, not on binomial counts or regression hypotheses.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The [membership pattern event](goal) specifies exactly which positions
of a sample are in [the cell determined by the partition, covariates, and label](hyp:label,X,k),
using [the prescribed index set](hyp:T). -/
def cellPattern {m : ℕ} (label : A → κ) (X : Ω → A) (k : κ)
    (T : Finset (Fin m)) : Set (Fin m → Ω) :=
  {z | ∀ r, label (X (z r)) = k ↔ r ∈ T}

/-- The [membership pattern](hyp:label,X,k,T) is [the rectangle with the
cell in selected coordinates and its complement elsewhere](goal). -/
theorem cellPattern_eq_pi {m : ℕ} (label : A → κ) (X : Ω → A) (k : κ)
    (T : Finset (Fin m)) :
    cellPattern label X k T =
      Set.univ.pi (fun r => if r ∈ T then cell label X k else (cell label X k)ᶜ) := by
  ext z
  simp only [cellPattern, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro hz r
    by_cases hr : r ∈ T
    · simpa [hr, cell] using (hz r).mpr hr
    · simpa [hr, cell] using (fun h => hr ((hz r).mp h))
  · intro hz r
    by_cases hr : r ∈ T
    · simpa [hr, cell] using hz r
    · simpa [hr, cell] using hz r

/-- [Measurable labels and covariates](hyp:hlabel,hX) give [a measurable
membership pattern](goal) for any selected subset. -/
theorem measurableSet_cellPattern {m : ℕ} (label : A → κ) (X : Ω → A)
    (k : κ) (T : Finset (Fin m)) (hlabel : Measurable label) (hX : Measurable X) :
    MeasurableSet (cellPattern label X k T) := by
  have hc : MeasurableSet (cell label X k) :=
    (measurableSet_singleton k).preimage (hlabel.comp hX)
  rw [cellPattern_eq_pi]
  apply MeasurableSet.univ_pi
  intro r
  split_ifs <;> first | exact hc | exact hc.compl

/-- [A sample in the specified membership pattern](hyp:hz) has [cell count
equal to the size of the selected index set](goal). -/
theorem cellCount_on_pattern {m : ℕ} (label : A → κ) (X : Ω → A) (k : κ)
    (T : Finset (Fin m)) (z : Fin m → Ω) (hz : z ∈ cellPattern label X k T) :
    cellCount label X k z = T.card := by
  unfold cellCount
  congr 1
  ext r
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hz r

/-- [Integrable coordinate factors](hyp:hf) have [an integrable product on
every membership pattern](goal) under the iid law. -/
theorem integrableOn_pattern_prod {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : A → κ) (X : Ω → A) (k : κ) (T : Finset (Fin m))
    (f : Fin m → Ω → ℝ) (hf : ∀ r, Integrable (f r) μ) :
    IntegrableOn (fun z : Fin m → Ω => ∏ r, f r (z r))
      (cellPattern label X k T) (Measure.pi (fun _ : Fin m => μ)) := by
  exact (Integrable.fintype_prod hf).integrableOn

/-- The [coordinate product on a fixed membership pattern](hyp:label,X,k,T,f)
has [integral equal to the product of the corresponding cell or complement
set integrals](goal) under the iid probability law. -/
theorem integral_pattern_prod {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : A → κ) (X : Ω → A) (k : κ) (T : Finset (Fin m))
    (f : Fin m → Ω → ℝ) :
    (∫ z in cellPattern label X k T, (∏ r, f r (z r))
        ∂Measure.pi (fun _ : Fin m => μ)) =
      ∏ r, ∫ ω in (if r ∈ T then cell label X k else (cell label X k)ᶜ),
        f r ω ∂μ := by
  rw [cellPattern_eq_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod f

omit [DecidableEq κ] in
/-- [Measurable partition inputs](hyp:hlabel,hX) and [a selected coordinate](hyp:hi)
give [a pattern-restricted squared residual
integral equal to its cell second moment times the masses of all other
coordinates](goal). -/
theorem integral_pattern_coordinate_sq {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (c : ℝ) (k : κ) (T : Finset (Fin m))
    (hlabel : Measurable label) (hX : Measurable X)
    (i : Fin m) (hi : i ∈ T) :
    (∫ z in cellPattern label X k T, (Y (z i) - c) ^ 2
        ∂Measure.pi (fun _ : Fin m => μ)) =
      (∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ) *
        cellMass μ label X k ^ (T.card - 1) *
        (1 - cellMass μ label X k) ^ (m - T.card) := by
  classical
  let f : Fin m → Ω → ℝ := fun r ω => if r = i then (Y ω - c) ^ 2 else 1
  have hp (z : Fin m → Ω) : (∏ r, f r (z r)) = (Y (z i) - c) ^ 2 := by
    simp [f]
  rw [← integral_congr_ae (Filter.Eventually.of_forall hp)]
  rw [integral_pattern_prod]
  let g : Fin m → ℝ := fun r =>
    ∫ ω in (if r ∈ T then cell label X k else (cell label X k)ᶜ), f r ω ∂μ
  change (∏ r, g r) = _
  have hc : MeasurableSet (cell label X k) :=
    (measurableSet_singleton k).preimage (hlabel.comp hX)
  have hcompl : μ.real (cell label X k)ᶜ = 1 - cellMass μ label X k := by
    simpa [cellMass, measureReal_def] using measureReal_compl (μ := μ) hc
  rw [← Finset.prod_mul_prod_compl T g, ← Finset.mul_prod_erase T g hi]
  have hgi : g i = ∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ := by
    simp [g, f, hi]
  have hT : (∏ r ∈ T.erase i, g r) = cellMass μ label X k ^ (T.card - 1) := by
    calc
      _ = ∏ _r ∈ T.erase i, cellMass μ label X k := by
        apply Finset.prod_congr rfl
        intro r hr
        rcases Finset.mem_erase.mp hr with ⟨hri, hrT⟩
        simp [g, f, hri, hrT, cellMass, measureReal_def]
      _ = _ := by simp [Finset.card_erase_of_mem hi]
  have hTc : (∏ r ∈ Tᶜ, g r) = (1 - cellMass μ label X k) ^ (m - T.card) := by
    calc
      _ = ∏ _r ∈ Tᶜ, (1 - cellMass μ label X k) := by
        apply Finset.prod_congr rfl
        intro r hr
        have hrT : r ∉ T := Finset.mem_compl.mp hr
        have hri : r ≠ i := fun h => hrT (h ▸ hi)
        simp [g, f, hri, hrT, hcompl]
      _ = _ := by simp [Finset.card_compl]
  rw [hgi, hT, hTc]

omit [DecidableEq κ] in
/-- [Two distinct selected coordinates](hyp:hi,hj,hij) with [centered cell
residuals](hyp:hcenter) have [zero cross moment on the fixed pattern](goal). -/
theorem integral_pattern_cross_eq_zero {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (c : ℝ) (k : κ) (T : Finset (Fin m))
    (i j : Fin m) (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j)
    (hcenter : (∫ ω in cell label X k, (Y ω - c) ∂μ) = 0) :
    (∫ z in cellPattern label X k T, (Y (z i) - c) * (Y (z j) - c)
        ∂Measure.pi (fun _ : Fin m => μ)) = 0 := by
  classical
  let f : Fin m → Ω → ℝ := fun r ω =>
    (if r = i then Y ω - c else 1) * (if r = j then Y ω - c else 1)
  have hp (z : Fin m → Ω) :
      (∏ r, f r (z r)) = (Y (z i) - c) * (Y (z j) - c) := by
    simp only [f, Finset.prod_mul_distrib]
    simp
  rw [← integral_congr_ae (Filter.Eventually.of_forall hp), integral_pattern_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [f, hi, hij] using hcenter

omit [DecidableEq κ] in
/-- [Measurable inputs and integrable first and second response moments](hyp:hlabel,hX,hY,hint,hsq),
with [zero cell residual mean](hyp:hcenter), imply [the exact second moment
of the selected residual sum on a fixed membership pattern](goal). -/
theorem integral_centered_sum_sq_on_pattern {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (c : ℝ) (k : κ) (T : Finset (Fin m))
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hint : Integrable Y μ) (hsq : Integrable (fun ω => Y ω ^ 2) μ)
    (hcenter : (∫ ω in cell label X k, (Y ω - c) ∂μ) = 0) :
    (∫ z in cellPattern label X k T,
        (∑ r ∈ T, (Y (z r) - c)) ^ 2 ∂Measure.pi (fun _ : Fin m => μ)) =
      (T.card : ℝ) * (∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ) *
        cellMass μ label X k ^ (T.card - 1) *
        (1 - cellMass μ label X k) ^ (m - T.card) := by
  classical
  have hres : Integrable (fun ω => Y ω - c) μ := hint.sub (integrable_const c)
  have hres2 : Integrable (fun ω => (Y ω - c) ^ 2) μ := by
    have h := (hsq.sub (hint.const_mul (2 * c))).add (integrable_const (c ^ 2))
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro ω
    change Y ω ^ 2 - (2 * c) * Y ω + c ^ 2 = (Y ω - c) ^ 2
    ring
  have hterm (i j : Fin m) :
      IntegrableOn (fun z : Fin m → Ω => (Y (z i) - c) * (Y (z j) - c))
        (cellPattern label X k T) (Measure.pi (fun _ : Fin m => μ)) := by
    by_cases hij : i = j
    · subst j
      simpa only [pow_two] using
        (integrable_comp_eval (μ := fun _ : Fin m => μ) (i := i) hres2).integrableOn
    · let f : Fin m → Ω → ℝ := fun r ω =>
        (if r = i then Y ω - c else 1) * (if r = j then Y ω - c else 1)
      have hf : ∀ r, Integrable (f r) μ := by
        intro r
        by_cases hri : r = i
        · subst r
          simpa [f, hij] using hres
        · by_cases hrj : r = j
          · subst r
            simpa [f, hri] using hres
          · simpa [f, hri, hrj] using (integrable_const (1 : ℝ) : Integrable _ μ)
      have hp (z : Fin m → Ω) :
          (∏ r, f r (z r)) = (Y (z i) - c) * (Y (z j) - c) := by
        simp only [f, Finset.prod_mul_distrib]
        simp
      exact (integrableOn_pattern_prod μ label X k T f hf).congr
        (Filter.Eventually.of_forall hp)
  have hexpand (z : Fin m → Ω) :
      (∑ r ∈ T, (Y (z r) - c)) ^ 2 =
        ∑ i ∈ T, ∑ j ∈ T, (Y (z i) - c) * (Y (z j) - c) := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  rw [integral_finsetSum T (fun i _ => integrable_finsetSum T (fun j _ => hterm i j))]
  simp_rw [integral_finsetSum T (fun j _ => hterm _ j)]
  have hmom (i : Fin m) (hi : i ∈ T) (j : Fin m) (hj : j ∈ T) :
      (∫ z in cellPattern label X k T, (Y (z i) - c) * (Y (z j) - c)
          ∂Measure.pi (fun _ : Fin m => μ)) =
        if j = i then
          (∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ) *
            cellMass μ label X k ^ (T.card - 1) *
            (1 - cellMass μ label X k) ^ (m - T.card)
        else 0 := by
    by_cases hji : j = i
    · subst j
      simpa only [ite_true, ← pow_two] using
        integral_pattern_coordinate_sq μ label X Y c k T hlabel hX i hi
    · simpa only [if_neg hji] using
        integral_pattern_cross_eq_zero μ label X Y c k T i j hi hj (Ne.symm hji) hcenter
  calc
    _ = ∑ i ∈ T,
        (∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ) *
          cellMass μ label X k ^ (T.card - 1) *
          (1 - cellMass μ label X k) ^ (m - T.card) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_congr rfl (fun j hj => hmom i hi j hj)]
      simp [hi]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end

end Causalean.Stat.Nonparametric.HistogramRegression
