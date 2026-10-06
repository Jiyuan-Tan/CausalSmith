module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.CellLikelihood

/-!
Pointwise identification of the paper's cell likelihood with the likelihood ratio of the
actual lower-law sign mixtures.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Density of one observed record with respect to the common covariate/counting/outcome
reference measure. -/
def lowerRecordDensity (P : ObsLaw) (o : Omega) : ℝ :=
  armProbability P.e (A o) (X o) * P.eta (A o) (X o) (Y o)

/-- Updating one propensity sign makes the actual null-law record density equal the
corresponding abstract cell-sign factor times the common outcome baseline. -/
-- @node: lower_null_record_density_eq_cell_factor
lemma lower_null_record_density_eq_cell_factor (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (r : Fin k) (b a : Bool) (x y u : ℝ)
    (hcell : signedBumps k (Function.update lambda r b) x = signValue b * u) :
    lowerRecordDensity (lowerNullLaw theta k j hp (Function.update lambda r b) omega)
        (x, a, y) =
      (1 / 2 : ℝ) * baselineDensity y *
        (1 + lowerTau theta k * signValue b * u * signValue a) := by
  change armProbability (lowerPropensity theta k (Function.update lambda r b)) a x *
      lowerNullDensity a x y = _
  cases a <;> simp only [armProbability, lowerPropensity, lowerNullDensity,
    Bool.false_eq_true, if_false, if_true] <;> rw [hcell]
  all_goals cases b <;> norm_num [signValue] <;> ring

/-- Under the same cell localization, the actual alternative-law record density is the
null cell factor times the treated outcome likelihood factor. -/
-- @node: lower_alternative_record_density_eq_cell_factor
lemma lower_alternative_record_density_eq_cell_factor (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (r : Fin k) (b a : Bool) (x y u : ℝ)
    (hcell : signedBumps k (Function.update lambda r b) x = signValue b * u) :
    lowerRecordDensity (lowerAlternativeLaw theta k j hp (Function.update lambda r b) omega)
        (x, a, y) =
      (1 / 2 : ℝ) * baselineDensity y *
        (1 + lowerTau theta k * signValue b * u * signValue a) *
        (if a then 1 + lowerGamma theta j *
          (signValue b * u / (1 + lowerTau theta k * signValue b * u)) *
            (signedBumps j omega y / baselineDensity y) else 1) := by
  have hb : baselineDensity y ≠ 0 := by
    have := lower_baseline_valid.2.1 y
    linarith
  have hd : 1 + lowerTau theta k * signValue b * u ≠ 0 := by
    have h := lower_denominator_ge theta k j hp (Function.update lambda r b) x
    rw [hcell] at h
    linarith
  change armProbability (lowerPropensity theta k (Function.update lambda r b)) a x *
      lowerAlternativeDensity theta k j (Function.update lambda r b) omega a x y = _
  cases a <;> simp only [armProbability, lowerPropensity, lowerAlternativeDensity,
    Bool.false_eq_true, if_false, if_true] <;> rw [hcell]
  · cases b <;> norm_num [armProbability, lowerPropensity, lowerNullDensity, signValue] <;> ring
  · cases b <;> norm_num [signValue] at hd ⊢
      <;> field_simp [hb, hd]

/-- For records localized to one covariate cell, the abstract `cellAlternativeRatio` is
exactly the ratio of the two-point actual alternative-law density mixture to the matching
actual null-law density mixture. -/
-- @node: cellAlternativeRatio_eq_lowerLaw_cellMixture
lemma cellAlternativeRatio_eq_lowerLaw_cellMixture {M : ℕ} (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (lambda : Fin k → Bool) (omega : Fin j → Bool)
    (r : Fin k) (x y : Fin M → ℝ) (a : Fin M → Bool) (u : Fin M → ℝ)
    (hcell : ∀ b i, signedBumps k (Function.update lambda r b) (x i) = signValue b * u i) :
    cellAlternativeRatio (lowerTau theta k) (lowerGamma theta j) u a
        (fun i => signedBumps j omega (y i) / baselineDensity (y i)) =
      (∑ b : Bool, ∏ i : Fin M,
          lowerRecordDensity
            (lowerAlternativeLaw theta k j hp (Function.update lambda r b) omega)
            (x i, a i, y i)) /
        (∑ b : Bool, ∏ i : Fin M,
          lowerRecordDensity
            (lowerNullLaw theta k j hp (Function.update lambda r b) omega)
            (x i, a i, y i)) := by
  classical
  simp_rw [lower_alternative_record_density_eq_cell_factor theta k j hp lambda omega r _ _ _ _ _
      (hcell _ _),
    lower_null_record_density_eq_cell_factor theta k j hp lambda omega r _ _ _ _ _
      (hcell _ _)]
  rw [cellAlternativeRatio_eq_weighted_product]
  let c : ℝ := ∏ i : Fin M, (1 / 2 : ℝ) * baselineDensity (y i)
  have hc : c ≠ 0 := by
    dsimp [c]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hb := lower_baseline_valid.2.1 (y i)
    positivity
  have hselected (b : Bool) :
      (∏ i : Fin M, if a i then
          1 + lowerGamma theta j *
            (signValue b * u i / (1 + lowerTau theta k * signValue b * u i)) *
              (signedBumps j omega (y i) / baselineDensity (y i))
        else 1) =
      ∏ i ∈ Finset.univ.filter (fun i => a i = true),
          (1 + lowerGamma theta j *
            (signValue b * u i / (1 + lowerTau theta k * signValue b * u i)) *
              (signedBumps j omega (y i) / baselineDensity (y i))) := by
    rw [Finset.prod_filter]
  have halt (b : Bool) :
      (∏ i : Fin M,
        (1 / 2 : ℝ) * baselineDensity (y i) *
          (1 + lowerTau theta k * signValue b * u i * signValue (a i)) *
          (if a i then 1 + lowerGamma theta j *
            (signValue b * u i / (1 + lowerTau theta k * signValue b * u i)) *
              (signedBumps j omega (y i) / baselineDensity (y i)) else 1)) =
        c * cellSignLikelihood (lowerTau theta k) u a b *
          ∏ i ∈ Finset.univ.filter (fun i => a i = true),
            (1 + lowerGamma theta j *
              (signValue b * u i / (1 + lowerTau theta k * signValue b * u i)) *
                (signedBumps j omega (y i) / baselineDensity (y i))) := by
    calc
      _ = (∏ i : Fin M, (1 / 2 : ℝ) * baselineDensity (y i)) *
          (∏ i : Fin M, (1 + lowerTau theta k * signValue b * u i * signValue (a i))) *
          (∏ i : Fin M, if a i then 1 + lowerGamma theta j *
            (signValue b * u i / (1 + lowerTau theta k * signValue b * u i)) *
              (signedBumps j omega (y i) / baselineDensity (y i)) else 1) := by
            simp only [Finset.prod_mul_distrib]
      _ = _ := by rw [hselected]; rfl
  have hnull (b : Bool) :
      (∏ i : Fin M, (1 / 2 : ℝ) * baselineDensity (y i) *
        (1 + lowerTau theta k * signValue b * u i * signValue (a i))) =
        c * cellSignLikelihood (lowerTau theta k) u a b := by
    calc
      _ = (∏ i : Fin M, (1 / 2 : ℝ) * baselineDensity (y i)) *
          (∏ i : Fin M, (1 + lowerTau theta k * signValue b * u i * signValue (a i))) := by
            simp only [Finset.prod_mul_distrib]
      _ = _ := rfl
  simp only [Fintype.sum_bool, halt, hnull]
  simp only [cellSignLikelihood, signValue, Bool.false_eq_true, ite_true, ite_false,
    mul_one, mul_neg_one, neg_mul, ← sub_eq_add_neg]
  field_simp [hc]

end CausalSmith.Stat.DensityEffectRoughNull
