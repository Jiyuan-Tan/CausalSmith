module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_CalibratedSupport
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ObservableOdds
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Densities of the actual original-record laws

Finite cell integration identifies the one-record density relative to the
uniform four-label reference, with the actual law's cells substituted.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The relative density uses the actual continuous cells of the observed law. -/
-- @node: recordCellDensity
def recordCellDensity (P : ObservedLaw) (o : Record) : ℝ :=
  4 * P.cells o.2.1 o.2.2 o.1

/-- Discrete label selection preserves measurability of continuous cell functions. [The stated conclusion follows](goal). -/
-- @node: recordCellDensity_measurable
@[fun_prop] lemma recordCellDensity_measurable (P : ObservedLaw) :
    Measurable (recordCellDensity P) := by
  have he : recordCellDensity P = (fun o : Record => 4 *
      (if o.2.1 then (if o.2.2 then P.cells true true o.1 else P.cells true false o.1)
      else (if o.2.2 then P.cells false true o.1 else P.cells false false o.1))) := by
    funext o
    rcases o with ⟨x, a, y⟩
    cases a <;> cases y <;> rfl
  rw [he]
  have hc (a y : Bool) : Measurable (fun o : Record => P.cells a y o.1) :=
    (P.continuous_cells a y).measurable.comp measurable_fst
  exact ((hc true true).ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    (hc true false)).ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    ((hc false true).ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      (hc false false)) |>.const_mul 4

/-- Cell positivity makes the explicit likelihood ratio nonnegative. [the stated conclusion](goal) holds. -/
-- @node: recordCellDensity_nonneg
lemma recordCellDensity_nonneg (P : ObservedLaw) (o : Record) :
    0 ≤ recordCellDensity P o :=
  mul_nonneg (by norm_num) (P.interior_cells _ _ _).1.le

/-- A law with public uniform design is its explicit cell density times the reference. Under the stated assumptions. [The stated hypotheses](hyp:hP) hold, and [the stated conclusion follows](goal). -/
-- @node: uniformObservedLaw_withDensity
lemma uniformObservedLaw_withDensity (P : ObservedLaw)
    (hP : Measure.map covariate P.measure = uniformLaw) :
    P.measure = recordReference.withDensity (fun o => ENNReal.ofReal (recordCellDensity P o)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hd := (recordCellDensity_measurable P).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf, P.disintegration, hP,
    lintegral_jointLaw_cells P f hf]
  change _ = ∫⁻ o, ENNReal.ofReal (recordCellDensity P o) * f o
    ∂jointLaw uniformLaw (fun _ _ _ => 1/4)
  have hnull : (lawFromCells (fun _ _ _ => 1/4) fairDefault_valid).cells =
      (fun _ _ _ => (1/4 : ℝ)) := rfl
  rw [← hnull]
  rw [lintegral_jointLaw_cells (lawFromCells (fun _ _ _ => 1/4) fairDefault_valid)
    (fun o => ENNReal.ofReal (recordCellDensity P o) * f o) (hd.mul hf)]
  apply lintegral_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  change ENNReal.ofReal (P.cells a y x) * f (x,a,y) =
    ENNReal.ofReal (1/4) * (ENNReal.ofReal (4 * P.cells a y x) * f (x,a,y))
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
  congr 2
  ring

/-- [The reference is the probability law of uniform covariates and fair labels. [the stated conclusion](goal) holds. -/
-- @node: recordReference_probability
instance recordReference_probability : IsProbabilityMeasure recordReference :=
  jointLaw_probability _ fairDefault_valid

/-- Continuous interior cells give a bounded integrable relative density. [the stated conclusion](goal) holds. -/
-- @node: recordCellDensity_integrable
lemma recordCellDensity_integrable (P : ObservedLaw) :
    Integrable (recordCellDensity P) recordReference := by
  apply (integrable_const (4 : ℝ)).mono'
    (recordCellDensity_measurable P).aestronglyMeasurable
  filter_upwards [] with o
  rw [Real.norm_eq_abs, abs_of_nonneg (recordCellDensity_nonneg P o)]
  change 4 * P.cells o.2.1 o.2.2 o.1 ≤ 4
  linarith [(P.interior_cells o.2.1 o.2.2 o.1).2]

/-- The actual iid likelihood retains every original covariate and label. -/
-- @node: sampleCellDensity
def sampleCellDensity (n : ℕ) (P : ObservedLaw) (o : Fin n → Record) : ℝ :=
  ∏ i, recordCellDensity P (o i)

/-- Finite products of the cell densities are measurable. [The stated conclusion follows](goal). -/
-- @node: sampleCellDensity_measurable
@[fun_prop] lemma sampleCellDensity_measurable (n : ℕ) (P : ObservedLaw) :
    Measurable (sampleCellDensity n P) := by
  unfold sampleCellDensity
  fun_prop

/-- The iid likelihood is nonnegative, including for an empty sample. [the stated conclusion](goal) holds. -/
-- @node: sampleCellDensity_nonneg
lemma sampleCellDensity_nonneg (n : ℕ) (P : ObservedLaw) (o : Fin n → Record) :
    0 ≤ sampleCellDensity n P o :=
  Finset.prod_nonneg (fun i _ => recordCellDensity_nonneg P (o i))

/-- Rectangle integration proves the explicit product density for the actual iid law. Under the stated assumptions. [The stated hypotheses](hyp:hP) hold, and [the stated conclusion follows](goal). -/
-- @node: uniformObservedLaw_iid_withDensity
lemma uniformObservedLaw_iid_withDensity (n : ℕ) (P : ObservedLaw)
    (hP : Measure.map covariate P.measure = uniformLaw) :
    Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n =
      (Measure.pi (fun _ : Fin n => recordReference)).withDensity
        (fun o => ENNReal.ofReal (sampleCellDensity n P o)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hi : ∀ i : Fin n, Integrable (recordCellDensity P) (recordReference.restrict (s i)) :=
    fun i => (recordCellDensity_integrable P).restrict
  have hp := Integrable.fintype_prod_dep hi
  unfold sampleCellDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hp
    (Filter.Eventually.of_forall (sampleCellDensity_nonneg n P))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
    (recordCellDensity_nonneg P))]
  apply Finset.prod_congr rfl
  intro i _
  rw [ofReal_integral_eq_lintegral_ofReal (hi i)
    (Filter.Eventually.of_forall (recordCellDensity_nonneg P))]
  rw [uniformObservedLaw_withDensity P hP, withDensity_apply _ (hs i)]

/-- [The product reference sees the explicit iid likelihood as its actual RN derivative.](goal) Under [the stated assumptions](hyp:hP). -/
-- @node: uniformObservedLaw_iid_rnDeriv
lemma uniformObservedLaw_iid_rnDeriv (n : ℕ) (P : ObservedLaw)
    (hP : Measure.map covariate P.measure = uniformLaw) :
    (fun o => ((Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n).rnDeriv
      (Measure.pi (fun _ : Fin n => recordReference)) o).toReal) =ᵐ[
        Measure.pi (fun _ : Fin n => recordReference)] sampleCellDensity n P := by
  have h := Measure.rnDeriv_withDensity (Measure.pi (fun _ : Fin n => recordReference))
    (sampleCellDensity_measurable n P).ennreal_ofReal
  rw [← uniformObservedLaw_iid_withDensity n P hP] at h
  filter_upwards [h] with o ho
  rw [ho, ENNReal.toReal_ofReal (sampleCellDensity_nonneg n P o)]

/-- The sign is averaged once over the entire original sample likelihood. -/
-- @node: signMixtureCellDensity
def signMixtureCellDensity (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) (o : Fin n → Record) : ℝ :=
  (2 : ℝ)^(-(k+1 : ℕ) : ℤ) * ∑ σ, sampleCellDensity n (laws σ) o

/-- A finite prior of measurable likelihoods is measurable. [The stated conclusion follows](goal). -/
-- @node: signMixtureCellDensity_measurable
@[fun_prop] lemma signMixtureCellDensity_measurable (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) :
    Measurable (signMixtureCellDensity n k laws) := by
  unfold signMixtureCellDensity
  fun_prop

/-- Every finite-prior likelihood is nonnegative. [the stated conclusion](goal) holds. -/
-- @node: signMixtureCellDensity_nonneg
lemma signMixtureCellDensity_nonneg (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) (o : Fin n → Record) :
    0 ≤ signMixtureCellDensity n k laws o := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun σ _ => sampleCellDensity_nonneg n (laws σ) o)

/-- Finite averaging identifies the density of the actual shared-sign experiment. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hU). -/
-- @node: finiteSignMixture_withDensity
lemma finiteSignMixture_withDensity (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw)
    (hU : ∀ σ, Measure.map covariate (laws σ).measure = uniformLaw) :
    finiteSignMixture n k laws =
      (Measure.pi (fun _ : Fin n => recordReference)).withDensity
        (fun o => ENNReal.ofReal (signMixtureCellDensity n k laws o)) := by
  unfold finiteSignMixture
  simp_rw [uniformObservedLaw_iid_withDensity n _ (hU _)]
  apply Measure.ext
  intro s hs
  simp only [Measure.smul_apply, Measure.finsetSum_apply, hs, withDensity_apply]
  simp only [signMixtureCellDensity,
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^(-(k+1 : ℕ) : ℤ) by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun σ _ => sampleCellDensity_nonneg n (laws σ) _)]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum]
  · rfl
  · intro σ _
    exact (sampleCellDensity_measurable n (laws σ)).ennreal_ofReal

/-- The RN derivative is the finite average of actual original-sample likelihoods. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hU). -/
-- @node: finiteSignMixture_rnDeriv
lemma finiteSignMixture_rnDeriv (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw)
    (hU : ∀ σ, Measure.map covariate (laws σ).measure = uniformLaw) :
    (fun o => ((finiteSignMixture n k laws).rnDeriv
      (Measure.pi (fun _ : Fin n => recordReference)) o).toReal) =ᵐ[
        Measure.pi (fun _ : Fin n => recordReference)] signMixtureCellDensity n k laws := by
  have h := Measure.rnDeriv_withDensity (Measure.pi (fun _ : Fin n => recordReference))
    (signMixtureCellDensity_measurable n k laws).ennreal_ofReal
  rw [← finiteSignMixture_withDensity n k laws hU] at h
  filter_upwards [h] with o ho
  rw [ho, ENNReal.toReal_ofReal (signMixtureCellDensity_nonneg n k laws o)]

/-- The sign-prior weight equals the inverse number of sign vectors used in component factorization. [the stated conclusion](goal) holds. -/
-- @node: signMixtureCellDensity_card_average
lemma signMixtureCellDensity_card_average (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw) (o : Fin n → Record) :
    signMixtureCellDensity n k laws o =
      (Fintype.card (Fin (k+1) → Bool) : ℝ)⁻¹ * ∑ σ, ∏ i, recordCellDensity (laws σ) (o i) := by
  simp only [signMixtureCellDensity, sampleCellDensity, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    zpow_neg, zpow_natCast]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
