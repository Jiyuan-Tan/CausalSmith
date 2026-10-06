module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyEnvelope
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.FrontierLower
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservableRule
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RateArithmetic

/-! Conditional coverage and first-moment guarantees for the exact frozen tuning,
with the public constants 2¹⁶ and 2²⁴ and no additional probabilistic premises. -/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Equation (49) and its first-moment counterpart for each good trained realization. -/
-- @node: tuned_energy_conditional_guarantees
lemma tuned_energy_conditional_guarantees (n : ℕ) (hbranch : reportingBranch n)
    (P : ObsLaw) (hModel : Model P) (train : Fin (roleSize n) → Omega)
    (hGood : GoodPilot P train (2 ^ 16) (tunedMx (roleSize n)) (tunedMy (roleSize n))) :
    let m := roleSize n
    let Z := energy train (tunedMx m) (tunedMy m) (tunedL m) (tunedT m)
      (tunedJ m) (tunedQ m) (tunedKt m)
    (19 / 20 : ℝ) ≤ (evalLaw P m).real
      {eval | |Z eval - Psi P| ≤ aci (tunedB n) (tunedW n) * Real.sqrt (Psi P) +
        dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m)} ∧
    (∫ eval, |Z eval - Psi P| ∂evalLaw P m) ≤
      aci (tunedB n) (tunedW n) * Real.sqrt (Psi P) +
        dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m) := by
  obtain ⟨hm, hh, _hz⟩ := hbranch
  obtain ⟨_hx, hq, hr⟩ := tuned_rank_compatibility (roleSize n) hm
  have h := energy_envelope_public_constant (2 ^ 16) (by positivity) P hModel
    (roleSize n) (by omega) (tunedMx (roleSize n)) (tunedMy (roleSize n))
    (tunedK (roleSize n)) (tunedL (roleSize n)) (tunedT (roleSize n))
    (tunedJ (roleSize n)) (tunedQ (roleSize n)) (tunedKt (roleSize n)) train
    (sampleLaw P (13 * roleSize n)) rfl
  exact (h.2.2 hr hq hGood hh).2.2

/-- The conditional first-moment bound in the extended-integral form needed by
scalar inversion. Integrability comes from independent square-integrable chains. -/
-- @node: tuned_energy_conditional_lintegral
lemma tuned_energy_conditional_lintegral (n : ℕ) (hbranch : reportingBranch n)
    (P : ObsLaw) (hModel : Model P) (train : Fin (roleSize n) → Omega)
    (hGood : GoodPilot P train (2 ^ 16) (tunedMx (roleSize n)) (tunedMy (roleSize n))) :
    let m := roleSize n
    let Z := energy train (tunedMx m) (tunedMy m) (tunedL m) (tunedT m)
      (tunedJ m) (tunedQ m) (tunedKt m)
    (∫⁻ eval, ENNReal.ofReal |Z eval - Psi P| ∂evalLaw P m) ≤
      ENNReal.ofReal (aci (tunedB n) (tunedW n) * Real.sqrt (Psi P) +
        dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m)) := by
  let m := roleSize n
  let Z := energy train (tunedMx m) (tunedMy m) (tunedL m) (tunedT m)
    (tunedJ m) (tunedQ m) (tunedKt m)
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  let : MeasurableSpace (Hj (tunedJ m)) := borel _
  let : BorelSpace (Hj (tunedJ m)) := ⟨rfl⟩
  have hL2 : MemLp Z 2 (evalLaw P m) :=
    (energy_moments_of_independent_chains P train (tunedMx m) (tunedMy m)
      (tunedL m) (tunedT m) (tunedQ m) (tunedKt m)
      (indepFun_coefficientChain P train _ _ _ _ _ _ _)
      (identDistrib_coefficientChain P train _ _ _ _ _ _ _)
      (memLp_coefficientChain P train _ _ _ _ _ _ _ 0 2)).1
  have hi : Integrable (fun eval => |Z eval - Psi P|) (evalLaw P m) :=
    ((hL2.sub (memLp_const (Psi P))).integrable (by norm_num)).abs
  change (∫⁻ eval, ENNReal.ofReal |Z eval - Psi P| ∂evalLaw P m) ≤
    ENNReal.ofReal (aci (tunedB n) (tunedW n) * Real.sqrt (Psi P) +
      dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m))
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal
    (tuned_energy_conditional_guarantees n hbranch P hModel train hGood).2

/-- On the equality subclass the conditional error moment is exactly a bound
on the absolute energy by the frozen constant inversion allowance. -/
-- @node: tuned_null_energy_conditional_moment
lemma tuned_null_energy_conditional_moment (n : ℕ) (hbranch : reportingBranch n)
    (P : ObsLaw) (hNull : NullModel P) (train : Fin (roleSize n) → Omega)
    (hGood : GoodPilot P train (2 ^ 16) (tunedMx (roleSize n)) (tunedMy (roleSize n))) :
    (∫⁻ eval, ENNReal.ofReal |energy train (tunedMx (roleSize n))
      (tunedMy (roleSize n)) (tunedL (roleSize n)) (tunedT (roleSize n))
      (tunedJ (roleSize n)) (tunedQ (roleSize n)) (tunedKt (roleSize n)) eval|
      ∂evalLaw P (roleSize n)) ≤
        ENNReal.ofReal (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))) := by
  have h := tuned_energy_conditional_lintegral n hbranch P hNull.1 train hGood
  simpa only [NullModel_Psi_zero P hNull, sub_zero, Real.sqrt_zero, mul_zero, zero_add] using h

/-- The good-training energy event is contained in coverage of the actual inversion interval. -/
-- @node: tuned_conditional_interval_coverage
lemma tuned_conditional_interval_coverage (n : ℕ) (hbranch : reportingBranch n)
    (P : ObsLaw) (hModel : Model P) (train : Fin (roleSize n) → Omega)
    (hGood : GoodPilot P train (2 ^ 16) (tunedMx (roleSize n)) (tunedMy (roleSize n))) :
    (19 / 20 : ℝ) ≤ (evalLaw P (roleSize n)).real
      {eval | Psi P ∈ invSet (energy train (tunedMx (roleSize n))
        (tunedMy (roleSize n)) (tunedL (roleSize n)) (tunedT (roleSize n))
        (tunedJ (roleSize n)) (tunedQ (roleSize n)) (tunedKt (roleSize n)) eval)
        (aci (tunedB n) (tunedW n))
        (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))} := by
  let : IsProbabilityMeasure (evalLaw P (roleSize n)) := by unfold evalLaw; infer_instance
  apply (tuned_energy_conditional_guarantees n hbranch P hModel train hGood).1.trans
  apply measureReal_mono (h₂ := by finiteness)
  intro eval hEval
  exact inversion_covers_accepted _ _ _ _ (model_Psi_mem_Icc P hModel) hEval

/-- Conditional expected length at every equality law is controlled by the frozen
allowances; bounded reported length requires no moment assumption on bad training. -/
-- @node: tuned_null_conditional_length
lemma tuned_null_conditional_length (n : ℕ) (hbranch : reportingBranch n)
    (P : ObsLaw) (hNull : NullModel P) (train : Fin (roleSize n) → Omega)
    (hGood : GoodPilot P train (2 ^ 16) (tunedMx (roleSize n)) (tunedMy (roleSize n))) :
    (∫ eval, intervalLength (invSet (energy train (tunedMx (roleSize n))
      (tunedMy (roleSize n)) (tunedL (roleSize n)) (tunedT (roleSize n))
      (tunedJ (roleSize n)) (tunedQ (roleSize n)) (tunedKt (roleSize n)) eval)
      (aci (tunedB n) (tunedW n))
      (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))))
      ∂evalLaw P (roleSize n)) ≤
        (aci (tunedB n) (tunedW n)) ^ 2 +
          4 * dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)) := by
  let m := roleSize n
  let Z := energy train (tunedMx m) (tunedMy m) (tunedL m) (tunedT m)
    (tunedJ m) (tunedQ m) (tunedKt m)
  let a := aci (tunedB n) (tunedW n)
  let d := dci (tunedB n) (tunedW n) (tunedV n) (tunedJ m)
  let f := fun eval => intervalLength (invSet (Z eval) a d)
  let : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  have ha : 0 ≤ a := (tuned_inversion_nonneg n).1
  have hd : 0 ≤ d := (tuned_inversion_nonneg n).2
  have hZ : Measurable Z := by
    exact measurable_energy train _ _ _ _ _ _ _
  obtain ⟨hierr, hmean⟩ := inversion_first_moment_real (evalLaw P m) Z hZ d hd
    (tuned_null_energy_conditional_moment n hbranch P hNull train hGood)
  have hf : Measurable f := by
    have heq : f = fun eval => invUpper (Z eval) a d - invLower (Z eval) a d := by
      funext eval
      exact inversion_length_eq _ _ _ ha
    rw [heq]
    exact ((inversion_endpoints_measurable a d).2.comp hZ).sub
      ((inversion_endpoints_measurable a d).1.comp hZ)
  have hif : Integrable f (evalLaw P m) :=
    Integrable.of_bound hf.aestronglyMeasurable 16
      (Filter.Eventually.of_forall (fun eval => by
        have hr := inversion_length_range (Z eval) a d
        rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
        exact hr.2))
  have hib : Integrable (fun eval => 2 * |Z eval| + a ^ 2 + 2 * d) (evalLaw P m) :=
    ((hierr.const_mul 2).add (integrable_const _)).add (integrable_const _)
  have hb := integral_mono hif hib (fun eval => invSet_length_bound (Z eval) a d hd)
  rw [integral_add (show Integrable (fun eval => 2 * |Z eval| + a ^ 2) (evalLaw P m) from
      (hierr.const_mul 2).add (integrable_const (a ^ 2))) (integrable_const (2 * d)),
    integral_add (hierr.const_mul 2) (integrable_const (a ^ 2)), integral_const_mul,
    integral_const, integral_const, probReal_univ, one_smul, one_smul] at hb
  change (∫ eval, f eval ∂evalLaw P m) ≤ a ^ 2 + 4 * d
  linarith

/-- Every public fallback branch is fully honest at every finite sample size. -/
-- @node: starRule_isHonest_of_not_reportingBranch
lemma starRule_isHonest_of_not_reportingBranch (n : ℕ) (hbranch : ¬reportingBranch n) :
    IsHonest n (starRule n) := by
  have heq : starRule n = fun _ => Set.Icc (0 : ℝ) 16 := by
    funext ω
    exact if_neg hbranch
  rw [heq]
  exact fullInterval_isHonest n

end CausalSmith.Stat.DensityEffectRoughNull
