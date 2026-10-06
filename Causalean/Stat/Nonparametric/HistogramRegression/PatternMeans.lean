module
public import Causalean.Stat.Nonparametric.HistogramRegression.PatternMoments

/-!
# Totalized centered means on membership patterns

This layer turns the closed rectangle moments into a reciprocal-count identity
on each membership pattern. It also isolates square integrability of the
zero-totalized empirical mean, including sample size zero. The global variance
formula in `Centered` can then sum over patterns and invoke the count law,
without another combinatorial grouping by cardinality.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The [zero-totalized empirical centered cell mean](goal) divides the cell
sum of [responses centered at the specified value](hyp:Y,c) by the cell count
for [the given partition, covariates, label, and sample](hyp:label,X,k,z). -/
def centeredCellMean {m : ℕ} (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (c : ℝ) (k : κ) (z : Fin m → Ω) : ℝ :=
  cellSum label X (fun ω => Y ω - c) k z / (cellCount label X k z : ℝ)

/-- [Measurable partition inputs and responses](hyp:hlabel,hX,hY) with
[integrable first and second response moments](hyp:hint,hsq) give
[an integrable squared totalized centered cell mean under iid sampling](goal). -/
theorem integrable_centeredCellMean_sq {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (c : ℝ) (k : κ)
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hint : Integrable Y μ) (hsq : Integrable (fun ω => Y ω ^ 2) μ) :
    Integrable (fun z : Fin m → Ω => (centeredCellMean label X Y c k z) ^ 2)
      (Measure.pi (fun _ : Fin m => μ)) := by
  -- First derive integrability of (Y-c)^2 from the two response moments.
  -- Measurability follows by finite sums, measurable_cellCount, and division.
  -- At count zero the quotient is zero. Otherwise its squared value is bounded
  -- by m times the sum of coordinate residual squares (finite Cauchy-Schwarz
  -- and count >= 1). Each coordinate square is integrable_comp_eval.
  classical
  have hres2 : Integrable (fun ω => (Y ω - c) ^ 2) μ := by
    have h := (hsq.sub (hint.const_mul (2 * c))).add (integrable_const (c ^ 2))
    refine h.congr (Filter.Eventually.of_forall ?_)
    intro ω
    change Y ω ^ 2 - (2 * c) * Y ω + c ^ 2 = (Y ω - c) ^ 2
    ring
  have hsum : Measurable (cellSum (m := m) label X (fun ω => Y ω - c) k) := by
    unfold cellSum
    apply Finset.measurable_fun_sum
    intro r _
    exact Measurable.ite
      ((measurableSet_singleton k).preimage
        (hlabel.comp (hX.comp (measurable_pi_apply r))))
      ((hY.comp (measurable_pi_apply r)).sub measurable_const) measurable_const
  have hcast : Measurable (fun z : Fin m → Ω => (cellCount label X k z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_cellCount label X k hlabel hX)
  have hmeas : Measurable (fun z : Fin m → Ω =>
      (centeredCellMean label X Y c k z) ^ 2) := (hsum.div hcast).pow_const 2
  have hdom : Integrable (fun z : Fin m → Ω =>
      (m : ℝ) * ∑ r : Fin m, (Y (z r) - c) ^ 2)
      (Measure.pi (fun _ : Fin m => μ)) :=
    (integrable_finsetSum Finset.univ (fun r _ =>
      integrable_comp_eval (μ := fun _ : Fin m => μ) (i := r) hres2)).const_mul _
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnonneg : 0 ≤ (m : ℝ) * ∑ r : Fin m, (Y (z r) - c) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun r _ => sq_nonneg _))
  by_cases hn : cellCount label X k z = 0
  · simpa [centeredCellMean, hn] using hnonneg
  · have hn1 : (1 : ℝ) ≤ (cellCount label X k z : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hn2 : (1 : ℝ) ≤ (cellCount label X k z : ℝ) ^ 2 := by nlinarith
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin m => (1 : ℝ))
      (fun r => if label (X (z r)) = k then Y (z r) - c else 0)
    have hcs' : (cellSum label X (fun ω => Y ω - c) k z) ^ 2 ≤
        (m : ℝ) * ∑ r : Fin m, (Y (z r) - c) ^ 2 := by
      have hcs0 : (cellSum label X (fun ω => Y ω - c) k z) ^ 2 ≤
          (m : ℝ) * ∑ r : Fin m,
            (if label (X (z r)) = k then Y (z r) - c else 0) ^ 2 := by
        simpa [cellSum] using hcs
      refine hcs0.trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
      apply Finset.sum_le_sum
      intro r _
      split_ifs <;> simp [sq_nonneg]
    simpa only [centeredCellMean, div_pow] using
      (div_le_self (sq_nonneg (cellSum label X (fun ω => Y ω - c) k z)) hn2).trans hcs'

/-- [Measurable inputs and integrable response moments](hyp:hlabel,hX,hY,hint,hsq),
[zero cell residual mean](hyp:hcenter), and [positive cell mass](hyp:hp) give
[a patternwise squared centered-mean integral equal to the within-cell second
moment times the patternwise totalized reciprocal-count integral](goal). -/
theorem integral_centeredCellMean_sq_on_pattern {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (c : ℝ) (k : κ) (T : Finset (Fin m))
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hint : Integrable Y μ) (hsq : Integrable (fun ω => Y ω ^ 2) μ)
    (hcenter : (∫ ω in cell label X k, (Y ω - c) ∂μ) = 0)
    (hp : 0 < cellMass μ label X k) :
    (∫ z in cellPattern label X k T, (centeredCellMean label X Y c k z) ^ 2
      ∂Measure.pi (fun _ : Fin m => μ)) =
      ((∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ) / cellMass μ label X k) *
        (∫ z in cellPattern label X k T,
          (if 0 < cellCount label X k z then (cellCount label X k z : ℝ)⁻¹ else 0)
          ∂Measure.pi (fun _ : Fin m => μ)) := by
  -- On the pattern, cellCount=T.card and cellSum is the residual sum over T.
  -- Empty T gives zero on both sides. Otherwise apply the closed
  -- integral_centered_sum_sq_on_pattern and pull out the squared denominator.
  -- Obtain pattern mass via integral_pattern_prod with all factors equal to 1:
  -- p^T.card * (1-p)^(m-T.card). Cancel p>0 and T.card>0; handle p=1 without
  -- cancelling the complement mass. No choose/cardinality regrouping is needed.
  classical
  have hpat := measurableSet_cellPattern label X k T hlabel hX
  have hsum (z : Fin m → Ω) (hz : z ∈ cellPattern label X k T) :
      cellSum label X (fun ω => Y ω - c) k z = ∑ r ∈ T, (Y (z r) - c) := by
    have hfilter : (Finset.univ.filter fun r => label (X (z r)) = k) = T := by
      ext r
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hz r
    rw [cellSum, ← Finset.sum_filter, hfilter]
  have hmean :
      (∫ z in cellPattern label X k T, (centeredCellMean label X Y c k z) ^ 2
        ∂Measure.pi (fun _ : Fin m => μ)) =
      ((T.card : ℝ) * (∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ) *
        cellMass μ label X k ^ (T.card - 1) *
        (1 - cellMass μ label X k) ^ (m - T.card)) / (T.card : ℝ) ^ 2 := by
    calc
      _ = ∫ z in cellPattern label X k T,
          (∑ r ∈ T, (Y (z r) - c)) ^ 2 / (T.card : ℝ) ^ 2
          ∂Measure.pi (fun _ : Fin m => μ) := by
        apply setIntegral_congr_fun hpat
        intro z hz
        change (centeredCellMean label X Y c k z) ^ 2 = _
        unfold centeredCellMean
        rw [cellCount_on_pattern label X k T z hz, hsum z hz, div_pow]
      _ = _ := by
        rw [integral_div, integral_centered_sum_sq_on_pattern
          μ label X Y c k T hlabel hX hY hint hsq hcenter]
  by_cases hT : T.card = 0
  · rw [hmean]
    have hrec :
        (∫ z in cellPattern label X k T,
          (if 0 < cellCount label X k z then (cellCount label X k z : ℝ)⁻¹ else 0)
          ∂Measure.pi (fun _ : Fin m => μ)) = 0 := by
      calc
        _ = ∫ z in cellPattern label X k T, (0 : ℝ)
            ∂Measure.pi (fun _ : Fin m => μ) := by
          apply setIntegral_congr_fun hpat
          intro z hz
          simp [cellCount_on_pattern label X k T z hz, hT]
        _ = 0 := by simp
    simp [hT, hrec]
  · have hnpos : 0 < T.card := Nat.pos_of_ne_zero hT
    have hn : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
    have hc : MeasurableSet (cell label X k) :=
      (measurableSet_singleton k).preimage (hlabel.comp hX)
    have hcompl : μ.real (cell label X k)ᶜ = 1 - cellMass μ label X k := by
      simpa [cellMass, measureReal_def] using measureReal_compl (μ := μ) hc
    have hmass :
        (∫ z in cellPattern label X k T, (1 : ℝ)
          ∂Measure.pi (fun _ : Fin m => μ)) =
        cellMass μ label X k ^ T.card *
          (1 - cellMass μ label X k) ^ (m - T.card) := by
      calc
        _ = ∫ z in cellPattern label X k T, (∏ _r : Fin m, (1 : ℝ))
            ∂Measure.pi (fun _ : Fin m => μ) := by simp
        _ = ∏ r : Fin m, ∫ ω in
            (if r ∈ T then cell label X k else (cell label X k)ᶜ), (1 : ℝ) ∂μ :=
          integral_pattern_prod μ label X k T (fun _ _ => 1)
        _ = _ := by
          rw [← Finset.prod_mul_prod_compl T]
          have hsel : (∏ r ∈ T, ∫ ω in
              (if r ∈ T then cell label X k else (cell label X k)ᶜ), (1 : ℝ) ∂μ) =
              cellMass μ label X k ^ T.card := by
            calc
              _ = ∏ _r ∈ T, cellMass μ label X k := by
                apply Finset.prod_congr rfl
                intro r hr
                simp [hr, cellMass, measureReal_def]
              _ = _ := by simp
          have hunsel : (∏ r ∈ Tᶜ, ∫ ω in
              (if r ∈ T then cell label X k else (cell label X k)ᶜ), (1 : ℝ) ∂μ) =
              (1 - cellMass μ label X k) ^ (m - T.card) := by
            calc
              _ = ∏ _r ∈ Tᶜ, (1 - cellMass μ label X k) := by
                apply Finset.prod_congr rfl
                intro r hr
                simp [Finset.mem_compl.mp hr, hcompl]
              _ = _ := by simp [Finset.card_compl]
          rw [hsel, hunsel]
    have hrec :
        (∫ z in cellPattern label X k T,
          (if 0 < cellCount label X k z then (cellCount label X k z : ℝ)⁻¹ else 0)
          ∂Measure.pi (fun _ : Fin m => μ)) =
        (T.card : ℝ)⁻¹ * (cellMass μ label X k ^ T.card *
          (1 - cellMass μ label X k) ^ (m - T.card)) := by
      calc
        _ = ∫ z in cellPattern label X k T, (T.card : ℝ)⁻¹ * (1 : ℝ)
            ∂Measure.pi (fun _ : Fin m => μ) := by
          apply setIntegral_congr_fun hpat
          intro z hz
          simp [cellCount_on_pattern label X k T z hz, hnpos]
        _ = _ := by rw [integral_const_mul, hmass]
    rw [hmean, hrec]
    by_cases hpone : cellMass μ label X k = 1
    · simp only [hpone, one_pow, div_one]
      field_simp [hn, ne_of_gt hp]
    · have hpow : cellMass μ label X k ^ T.card =
          cellMass μ label X k ^ (T.card - 1) * cellMass μ label X k := by
        rw [← pow_succ, Nat.sub_add_cancel hnpos]
      rw [hpow]
      field_simp [hn, ne_of_gt hp]

end

end Causalean.Stat.Nonparametric.HistogramRegression
