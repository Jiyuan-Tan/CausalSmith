module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingMoments
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.RoundingRankBorel

/-! # Seed-history integration and fairness

Integrating one fresh coordinate of the product seed law preserves the
fractional-state mean. Finite iteration from zero gives fair terminal signs.
-/

public section
noncomputable section
open MeasureTheory Set
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ A fresh-coordinate conditional mean integrates to the preceding mean under
product uniform seeds, provided that the preceding state ignores that seed.](goal) Under [the stated conditions](hyp:hf,hg,hmean,hignore). -/
-- @node: cube_integral_eq_of_fresh_coordinate
lemma cube_integral_eq_of_fresh_coordinate {m : ℕ} (j : Fin m)
    (f g : Cube m → ℝ) (hf : Integrable f (cubeMeasure m))
    (hg : Integrable g (cubeMeasure m))
    (hmean : ∀ x, (∫ t, f (Function.update x j t)
      ∂volume.restrict (Icc (0 : ℝ) 1)) = g x)
    (hignore : ∀ x t, g (Function.update x j t) = g x) :
    (∫ x, f x ∂cubeMeasure m) = ∫ x, g x ∂cubeMeasure m := by
  classical
  cases m with
  | zero => exact Fin.elim0 j
  | succ m =>
    let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
    have : IsFiniteMeasure (cubeMeasure m) := by
      unfold cubeMeasure
      infer_instance
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j).symm
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) j).symm
    have hf' : Integrable (fun x => f (e x)) (μ.prod (cubeMeasure m)) :=
      (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
    have hg' : Integrable (fun x => g (e x)) (μ.prod (cubeMeasure m)) :=
      (hp.integrable_comp_emb e.measurableEmbedding).mpr hg
    change (∫ x, f x ∂Measure.pi (fun _ : Fin (m + 1) => μ)) =
      ∫ x, g x ∂Measure.pi (fun _ : Fin (m + 1) => μ)
    rw [← hp.integral_comp' f, ← hp.integral_comp' g]
    change (∫ x, f (e x) ∂μ.prod (cubeMeasure m)) =
      ∫ x, g (e x) ∂μ.prod (cubeMeasure m)
    rw [integral_prod_symm _ hf', integral_prod_symm _ hg']
    apply integral_congr_ae
    filter_upwards [] with x
    have he (t : ℝ) : e (t, x) = Function.update (e (0, x)) j t := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.update_insertNth]
    have hfc : (fun t => f (e (t, x))) =
        (fun t => f (Function.update (e (0, x)) j t)) := by
      funext t
      rw [he t]
    have hgc : (fun t => g (e (t, x))) = (fun _ : ℝ => g (e (0, x))) := by
      funext t
      rw [he t, hignore]
    rw [hfc, hgc, hmean]
    simp [μ, integral_const, measureReal_def, Real.volume_Icc]

variable {n : ℕ}

/-- Each fractional coordinate is Borel as a function of all seeds. This uses [the stated conclusion](goal). -/
@[fun_prop]
-- @node: roundingIteration_coordinate_measurable
lemma roundingIteration_coordinate_measurable (a : Fin (n / 4) → Fin n → ℝ)
    (k : ℕ) (i : Fin n) :
    Measurable (fun seeds : RoundingSeeds n => (roundingIteration a seeds k).1 i) := by
  fun_prop

/-- Cube preservation makes every fractional coordinate integrable under the
full product seed law, without any row bound. [The asserted mathematical result follows](goal). -/
-- @node: roundingIteration_coordinate_integrable
lemma roundingIteration_coordinate_integrable (a : Fin (n / 4) → Fin n → ℝ)
    (k : ℕ) (i : Fin n) :
    Integrable (fun seeds => (roundingIteration a seeds k).1 i) (roundingSeedLaw n) := by
  have : IsFiniteMeasure (roundingSeedLaw n) := by
    unfold roundingSeedLaw cubeMeasure
    infer_instance
  apply Integrable.of_bound (roundingIteration_coordinate_measurable a k i).aestronglyMeasurable 1
  filter_upwards [] with seeds
  simpa only [Real.norm_eq_abs] using (roundingIteration_cube_and_count a seeds k).1 i

/-- Successive fresh-coin integration preserves the full-seed coordinate mean. Under [the stated conditions](hyp:hk), [the asserted mathematical result follows](goal). -/
-- @node: roundingIteration_integral_succ
lemma roundingIteration_integral_succ (a : Fin (n / 4) → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (i : Fin n) :
    (∫ seeds, (roundingIteration a seeds (k + 1)).1 i ∂roundingSeedLaw n) =
      ∫ seeds, (roundingIteration a seeds k).1 i ∂roundingSeedLaw n := by
  apply cube_integral_eq_of_fresh_coordinate ⟨2 * k + 1, by omega⟩
    _ _ (roundingIteration_coordinate_integrable a (k + 1) i)
    (roundingIteration_coordinate_integrable a k i)
  · exact fun seeds => roundingIteration_next_coin_mean a seeds k hk i
  · intro seeds t
    rw [roundingIteration_update_future a seeds k _ t (by dsimp; omega)]

/-- [ Starting at zero and integrating the fresh seed at each move gives zero
mean for every fractional coordinate up to the deterministic move limit.](goal) Under [the stated conditions](hyp:hk). -/
-- @node: roundingIteration_integral_zero
lemma roundingIteration_integral_zero (a : Fin (n / 4) → Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (i : Fin n) :
    (∫ seeds, (roundingIteration a seeds k).1 i ∂roundingSeedLaw n) = 0 := by
  induction k with
  | zero => simp [roundingIteration]
  | succ k ih =>
    rw [roundingIteration_integral_succ a k (by omega) i]
    exact ih (by omega)

/-- Terminal signs equal the final fractional state, so the constructed signing
is fair under its actual product seed law. [The asserted mathematical result follows](goal). -/
-- @node: orderedBoundaryRounding_fair
lemma orderedBoundaryRounding_fair (a : Fin (n / 4) → Fin n → ℝ) (i : Fin n) :
    (∫ seeds, sgn (orderedBoundaryRounding n a seeds i) ∂roundingSeedLaw n) = 0 := by
  simp_rw [← roundingIteration_terminal_eq_sign a]
  exact roundingIteration_integral_zero a n le_rfl i

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
