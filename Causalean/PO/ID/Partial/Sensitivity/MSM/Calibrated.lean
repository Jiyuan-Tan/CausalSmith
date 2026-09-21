/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — calibrated candidate bounds

The uncalibrated endpoints of `Bounds.lean` optimize an unnormalized IPW functional over the
odds-ratio box `MSMSet d Λ`. This file additionally imposes the **calibration** identity

    E[1{D=d} / ẽ | σ(X)] = 1   a.e.

(the true complete propensity satisfies it by the tower property after conditioning on `Y(d)`).
Imposing it cuts the ambiguity set down to `MSMSetCalib d Λ`, whose candidate-mean range is
`[msmLowerCalib d Λ, msmUpperCalib d Λ]`.

This file establishes two properties of the calibrated set:
* it is **valid** under the stated bridge and boundedness hypotheses — `E[Y(d)]` then lies in the
  calibrated interval; and
* under the stated nonemptiness and boundedness hypotheses, its endpoints are **tighter** than
  those of the uncalibrated HT relaxation because `MSMSetCalib d Λ ⊆ MSMSet d Λ`.

**Scope.** These results prove validity and tightening, not realizability of every calibrated
candidate by a data-compatible full-data law. The quantile-balancing, cutoff-selection,
lower-bound, and Gaussian files downstream evaluate these variational endpoints under their
respective cutoff-existence and distributional hypotheses.
-/

module
public import Causalean.PO.ID.Partial.Sensitivity.MSM.Setup

/-! # Calibrated marginal-sensitivity set

This file defines the arm-generic calibrated MSM ambiguity set and proves its basic validity
properties. It introduces `Calibrated`, `MSMSetCalib`, `msmUpperCalib`, and `msmLowerCalib`;
proves that the true complete propensity is calibrated and therefore belongs to the calibrated
set when the MSM assumption holds; proves validity via `Ymean_mem_Icc_calib`; and, under the
stated nonemptiness and boundedness hypotheses, shows that the calibrated endpoints tighten the
uncalibrated HT relaxation.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- Given [a binary-treatment backdoor system](hyp:S), [a treatment arm](hyp:d), and [a candidate complete-propensity function](hyp:etilde), the [calibration condition](goal) holds exactly when the conditional mean, given the covariate σ-algebra, of that arm's indicator divided by that function equals one almost surely.

**Calibration (data-compatibility).** A candidate complete propensity `ẽ` is *calibrated* if
inverse-propensity weighting of the arm indicator averages to one within every covariate stratum:
`E[1{D=d} / ẽ | σ(X)] = 1` a.e. This is the only restriction on `ẽ`
beyond the odds-ratio box implied by the observed-data distribution. -/
def Calibrated (d : Bool) (etilde : P.Ω → ℝ) : Prop :=
  P.μ[fun ω => S.dVar.indicator d ω / etilde ω | S.sigmaX] =ᵐ[P.μ] (fun _ => 1)

/-- Calibration [makes the arm-indicator inverse-weight integrand integrable](goal) for
[a binary-treatment backdoor system](hyp:S), [the selected arm](hyp:d), and [a candidate complete
propensity](hyp:etilde) whenever [that candidate is calibrated for the arm](hyp:hcal).

If it were not integrable, its conditional expectation would be zero by definition, contradicting
calibration to one under the probability law. -/
@[fun_prop]
theorem calibrated_weight_integrable (d : Bool) (etilde : P.Ω → ℝ)
    (hcal : S.Calibrated d etilde) :
    Integrable (fun ω => S.dVar.indicator d ω / etilde ω) P.μ := by
  unfold POBackdoorSystem.Calibrated at hcal
  by_contra hnot
  rw [MeasureTheory.condExp_of_not_integrable hnot] at hcal
  have hzero_eq_one := integral_congr_ae hcal
  simp at hzero_eq_one

/-- Given [a binary-treatment backdoor system](hyp:S), [a treatment arm](hyp:d), and [a sensitivity level](hyp:Λ), the [calibrated MSM ambiguity set](goal) contains exactly the candidate complete-propensity functions that [belong to the MSM ambiguity set at that level](step:1) and satisfy the calibration condition.

**The calibrated MSM ambiguity set:** odds-ratio-box members that also satisfy
calibration. -/
def MSMSetCalib (d : Bool) (Λ : ℝ) : Set (P.Ω → ℝ) :=
  { etilde | etilde ∈ S.MSMSet d Λ ∧ S.Calibrated d etilde }

/-- Given [a binary-treatment backdoor system](hyp:S), [a treatment arm](hyp:d), and [a sensitivity level](hyp:Λ), the [calibrated MSM upper bound](goal) is the supremum of candidate inverse-probability-weighted means over the calibrated MSM ambiguity set. -/
noncomputable def msmUpperCalib (d : Bool) (Λ : ℝ) : ℝ :=
  sSup (S.candMean d '' S.MSMSetCalib d Λ)

/-- Given [a binary-treatment backdoor system](hyp:S), [a treatment arm](hyp:d), and [a sensitivity level](hyp:Λ), the [calibrated MSM lower bound](goal) is the infimum of candidate inverse-probability-weighted means over the calibrated MSM ambiguity set. -/
noncomputable def msmLowerCalib (d : Bool) (Λ : ℝ) : ℝ :=
  sInf (S.candMean d '' S.MSMSetCalib d Λ)

/-- The [complete propensity is calibrated for its arm](goal) in [a binary-treatment backdoor
system](hyp:S) when [that propensity is positive almost surely](hyp:hpos) and [the corresponding
inverse-weighted arm indicator is integrable](hyp:hint), for [the selected arm](hyp:d).

Writing `e₀,d = P[D=d | σ(X,Y(d))]`, the tower property and pull-out identity give
`E[1{D=d}/e₀,d | σ(X)] = 1` almost surely. -/
theorem completeProp_calibrated
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (d : Bool)
    (hpos : ∀ᵐ ω ∂P.μ, 0 < S.completeProp d ω)
    (hint : Integrable (fun ω => S.dVar.indicator d ω / S.completeProp d ω) P.μ) :
    S.Calibrated d (S.completeProp d) := by
  classical
  set A : P.Ω → ℝ := S.dVar.indicator d with hA_def
  set e : P.Ω → ℝ := S.completeProp d with he_def
  -- `σ(X) ≤ σ(X, Y(d))`.
  have hX_le : S.sigmaX ≤ S.sigmaXY d := by
    rw [POBackdoorSystem.sigmaX, POBackdoorSystem.sigmaXY]
    exact le_sup_left
  -- `1/e` is `σ(X,Y(d))`-strongly measurable (`e = condExp` is).
  have he_smeas : StronglyMeasurable[S.sigmaXY d] e := by
    rw [he_def]; exact stronglyMeasurable_condExp
  have hinv_smeas : StronglyMeasurable[S.sigmaXY d] (fun ω => 1 / e ω) :=
    (measurable_const.div he_smeas.measurable).stronglyMeasurable
  -- Integrability of `A` and `(1/e)·A` (= `A/e`).
  have hA_int : Integrable A P.μ := S.dVar.integrable_indicator d (measurableSet_singleton d)
  have hinvA_int : Integrable (fun ω => (1 / e ω) * A ω) P.μ := by
    refine hint.congr (Filter.Eventually.of_forall ?_)
    intro ω
    simp [hA_def, he_def, div_eq_inv_mul]
  -- Pull out `1/e` through conditional expectation with respect to `σ(X,Y(d))`.
  have he_cond : (P.μ[A | S.sigmaXY d]) = e := by rw [hA_def, he_def]; rfl
  have hpull :
      P.μ[fun ω => (1 / e ω) * A ω | S.sigmaXY d] =ᵐ[P.μ] (fun ω => (1 / e ω) * e ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaXY d) (μ := P.μ) hinv_smeas hinvA_int hA_int
    refine h.trans ?_
    rw [he_cond]
    rfl
  -- Cancel: `(1/e)·e = 1` a.e. from positivity.
  have hcancel : (fun ω => (1 / e ω) * e ω) =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hpos] with ω hω
    rw [he_def] at hω
    rw [he_def]
    field_simp
  -- Thus `μ[A/e | σ(X,Y(d))] =ᵐ 1`.
  have hinner : P.μ[fun ω => A ω / e ω | S.sigmaXY d] =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    have hrw : (fun ω => A ω / e ω) = (fun ω => (1 / e ω) * A ω) := by
      funext ω; rw [one_div, div_eq_inv_mul]
    rw [hrw]
    exact hpull.trans hcancel
  -- Apply the tower property from `σ(X,Y(d))` down to `σ(X)`.
  unfold POBackdoorSystem.Calibrated
  have htower :
      P.μ[fun ω => A ω / e ω | S.sigmaX]
        =ᵐ[P.μ] P.μ[P.μ[fun ω => A ω / e ω | S.sigmaXY d] | S.sigmaX] :=
    (MeasureTheory.condExp_condExp_of_le hX_le (S.sigmaXY_le d)).symm
  refine htower.trans ?_
  have hcongr :
      P.μ[P.μ[fun ω => A ω / e ω | S.sigmaXY d] | S.sigmaX]
        =ᵐ[P.μ] P.μ[(fun _ => (1 : ℝ)) | S.sigmaX] :=
    condExp_congr_ae hinner
  refine hcongr.trans ?_
  exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const S.sigmaX_le (1 : ℝ))

/-- The d complete propensity lies in the calibrated set when it satisfies MSM membership and
calibration. -/
theorem completeProp_mem_MSMSetCalib (d : Bool) (Λ : ℝ)
    (hmem : S.completeProp d ∈ S.MSMSet d Λ) (hcalib : S.Calibrated d (S.completeProp d)) :
    S.completeProp d ∈ S.MSMSetCalib d Λ :=
  ⟨hmem, hcalib⟩

/-- The [mean potential outcome for an arm lies in its calibrated sensitivity interval](goal) in
[a binary-treatment backdoor system](hyp:S) at [a sensitivity level](hyp:Λ) when [the arm's
complete propensity is calibrated and admissible](hyp:hmem), [its candidate mean equals its
potential-outcome mean](hyp:hbridge), and [the calibrated candidate means are bounded below and
above](hyp:hbdd,hbdd'), for [the selected arm](hyp:d). -/
theorem Ymean_mem_Icc_calib (d : Bool) (Λ : ℝ)
    (hmem : S.completeProp d ∈ S.MSMSetCalib d Λ)
    (hbridge : S.candMean d (S.completeProp d) = S.Ymean d)
    (hbdd : BddBelow (S.candMean d '' S.MSMSetCalib d Λ))
    (hbdd' : BddAbove (S.candMean d '' S.MSMSetCalib d Λ)) :
    S.Ymean d ∈ Set.Icc (S.msmLowerCalib d Λ) (S.msmUpperCalib d Λ) := by
  have hmemImg : S.candMean d (S.completeProp d) ∈ S.candMean d '' S.MSMSetCalib d Λ :=
    Set.mem_image_of_mem _ hmem
  rw [Set.mem_Icc, ← hbridge]
  refine ⟨?_, ?_⟩
  · exact csInf_le hbdd hmemImg
  · exact le_csSup hbdd' hmemImg

/-- Deprecated treated-arm specialization of calibrated MSM interval validity. -/
@[deprecated "Use Ymean_mem_Icc_calib true." (since := "2026-09-17")]
theorem Y1mean_mem_Icc_calib (Λ : ℝ)
    (hmem : S.completeProp true ∈ S.MSMSetCalib true Λ)
    (hbridge : S.candMean true (S.completeProp true) = S.Y1mean)
    (hbdd : BddBelow (S.candMean true '' S.MSMSetCalib true Λ))
    (hbdd' : BddAbove (S.candMean true '' S.MSMSetCalib true Λ)) :
    S.Y1mean ∈ Set.Icc (S.msmLowerCalib true Λ) (S.msmUpperCalib true Λ) :=
  S.Ymean_mem_Icc_calib true Λ hmem hbridge hbdd hbdd'

/-- The calibrated set is a subset of the odds-ratio box. -/
theorem MSMSetCalib_subset (d : Bool) (Λ : ℝ) : S.MSMSetCalib d Λ ⊆ S.MSMSet d Λ :=
  fun _ h => h.1

/-- The [calibrated upper endpoint does not exceed the uncalibrated HT-relaxation upper
endpoint](goal) for [a binary-treatment backdoor system](hyp:S), [the selected arm](hyp:d), and
[a sensitivity level](hyp:Λ), provided [the calibrated candidate-mean range is
nonempty](hyp:hne) and [the uncalibrated range is bounded above](hyp:hbdd). -/
theorem msmUpperCalib_le_msmUpper (d : Bool) (Λ : ℝ)
    (hne : (S.candMean d '' S.MSMSetCalib d Λ).Nonempty)
    (hbdd : BddAbove (S.candMean d '' S.MSMSet d Λ)) :
    S.msmUpperCalib d Λ ≤ S.msmUpper d Λ := by
  have hsub : S.MSMSetCalib d Λ ⊆ S.MSMSet d Λ := S.MSMSetCalib_subset d Λ
  have himg : S.candMean d '' S.MSMSetCalib d Λ ⊆ S.candMean d '' S.MSMSet d Λ :=
    Set.image_mono hsub
  exact csSup_le_csSup hbdd hne himg

/-- The [uncalibrated HT-relaxation lower endpoint does not exceed the calibrated lower
endpoint](goal) for [a binary-treatment backdoor system](hyp:S), [the selected arm](hyp:d), and
[a sensitivity level](hyp:Λ), provided [the calibrated candidate-mean range is
nonempty](hyp:hne) and [the uncalibrated range is bounded below](hyp:hbdd). -/
theorem msmLower_le_msmLowerCalib (d : Bool) (Λ : ℝ)
    (hne : (S.candMean d '' S.MSMSetCalib d Λ).Nonempty)
    (hbdd : BddBelow (S.candMean d '' S.MSMSet d Λ)) :
    S.msmLower d Λ ≤ S.msmLowerCalib d Λ := by
  have hsub : S.MSMSetCalib d Λ ⊆ S.MSMSet d Λ := S.MSMSetCalib_subset d Λ
  have himg : S.candMean d '' S.MSMSetCalib d Λ ⊆ S.candMean d '' S.MSMSet d Λ :=
    Set.image_mono hsub
  exact csInf_le_csInf hbdd hne himg

end POBackdoorSystem

end PO
end Causalean
