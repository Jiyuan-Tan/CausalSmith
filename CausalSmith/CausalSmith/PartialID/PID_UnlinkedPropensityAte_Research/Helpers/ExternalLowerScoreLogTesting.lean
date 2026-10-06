module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerTrialTesting

/-! Testing estimates for the three-score external-log perturbation. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,x,y,z), [this definition](goal) introduces the corresponding object. -/
def threeScoreBaseLaw {ε : ℝ} (x y z : ScoreSpace ε) : Measure (ScoreSpace ε) :=
  ENNReal.ofReal (1 / 3 : ℝ) • Measure.dirac x +
    ENNReal.ofReal (1 / 3 : ℝ) • Measure.dirac y +
    ENNReal.ofReal (1 / 3 : ℝ) • Measure.dirac z

/-- For [the specified mathematical inputs](hyp:ε,x,y,z,u), [this definition](goal) introduces the corresponding object. -/
def threeScorePerturbedLaw {ε : ℝ} (x y z : ScoreSpace ε) (u : ℝ) :
    Measure (ScoreSpace ε) :=
  ENNReal.ofReal (1 / 3 + u * ((z : ℝ) - y)) • Measure.dirac x +
    ENNReal.ofReal (1 / 3 - u * ((z : ℝ) - x)) • Measure.dirac y +
    ENNReal.ofReal (1 / 3 + u * ((y : ℝ) - x)) • Measure.dirac z

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreBaseLaw_isProbabilityMeasure {ε : ℝ} (x y z : ScoreSpace ε) :
    IsProbabilityMeasure (threeScoreBaseLaw x y z) := by
  rw [isProbabilityMeasure_iff]
  unfold threeScoreBaseLaw
  rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 3 + 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  norm_num

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,u,hx,hy,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScorePerturbedLaw_isProbabilityMeasure {ε : ℝ}
    (x y z : ScoreSpace ε) (u : ℝ)
    (hx : 0 < 1 / 3 + u * ((z : ℝ) - y))
    (hy : 0 < 1 / 3 - u * ((z : ℝ) - x))
    (hz : 0 < 1 / 3 + u * ((y : ℝ) - x)) :
    IsProbabilityMeasure (threeScorePerturbedLaw x y z u) := by
  rw [isProbabilityMeasure_iff]
  unfold threeScorePerturbedLaw
  rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hx.le hy.le,
    ← ENNReal.ofReal_add (add_nonneg hx.le hy.le) hz.le]
  rw [show (1 / 3 + u * ((z : ℝ) - y)) +
      (1 / 3 - u * ((z : ℝ) - x)) +
      (1 / 3 + u * ((y : ℝ) - x)) = 1 by ring,
    ENNReal.ofReal_one]

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,u,hxy,hyz), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScorePerturbedLaw_ac_integrable {ε : ℝ}
    (x y z : ScoreSpace ε) (u : ℝ) (hxy : x < y) (hyz : y < z) :
    threeScorePerturbedLaw x y z u ≪ threeScoreBaseLaw x y z ∧
      Integrable (fun e =>
        (((threeScorePerturbedLaw x y z u).rnDeriv
          (threeScoreBaseLaw x y z) e).toReal - 1) ^ 2)
        (threeScoreBaseLaw x y z) := by
  let wx : ℝ := 1 / 3 + u * ((z : ℝ) - y)
  let wy : ℝ := 1 / 3 - u * ((z : ℝ) - x)
  let wz : ℝ := 1 / 3 + u * ((y : ℝ) - x)
  let d : ScoreSpace ε → ENNReal := fun e =>
    if e = x then ENNReal.ofReal (3 * wx)
    else if e = y then ENNReal.ofReal (3 * wy)
    else if e = z then ENNReal.ofReal (3 * wz)
    else 0
  have hxy_ne : x ≠ y := ne_of_lt hxy
  have hxz_ne : x ≠ z := ne_of_lt (lt_trans hxy hyz)
  have hyz_ne : y ≠ z := ne_of_lt hyz
  have hd : Measurable d := by
    dsimp [d]
    exact Measurable.ite (measurableSet_singleton x) measurable_const
      (Measurable.ite (measurableSet_singleton y) measurable_const
        (Measurable.ite (measurableSet_singleton z) measurable_const measurable_const))
  have hscale (w : ℝ) :
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (3 * w) = ENNReal.ofReal w := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    exact congrArg ENNReal.ofReal (by ring)
  have hwd : threeScorePerturbedLaw x y z u =
      (threeScoreBaseLaw x y z).withDensity d := by
    unfold threeScorePerturbedLaw threeScoreBaseLaw
    rw [withDensity_add_measure, withDensity_add_measure,
      withDensity_smul_measure, withDensity_smul_measure,
      withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
      dirac_withDensity]
    dsimp only [d]
    simp only [if_pos, if_neg hxy_ne.symm, if_neg hxz_ne.symm,
      if_neg hxy_ne, if_neg hyz_ne.symm, if_neg hxz_ne, if_neg hyz_ne]
    repeat' rw [smul_smul]
    rw [hscale wx, hscale wy, hscale wz]
  constructor
  · rw [hwd]
    exact withDensity_absolutelyContinuous _ _
  · unfold threeScoreBaseLaw
    apply Integrable.add_measure
    · apply Integrable.add_measure
      · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
      · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
    · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,u,hxy,hyz,hx,hy,hz), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScorePerturbedLaw_chisq {ε : ℝ}
    (x y z : ScoreSpace ε) (u : ℝ) (hxy : x < y) (hyz : y < z)
    (hx : 0 < 1 / 3 + u * ((z : ℝ) - y))
    (hy : 0 < 1 / 3 - u * ((z : ℝ) - x))
    (hz : 0 < 1 / 3 + u * ((y : ℝ) - x)) :
    Causalean.Stat.chiSqDiv (threeScorePerturbedLaw x y z u)
      (threeScoreBaseLaw x y z) =
        3 * u ^ 2 * (((z : ℝ) - y) ^ 2 + ((z : ℝ) - x) ^ 2 +
          ((y : ℝ) - x) ^ 2) := by
  let wx : ℝ := 1 / 3 + u * ((z : ℝ) - y)
  let wy : ℝ := 1 / 3 - u * ((z : ℝ) - x)
  let wz : ℝ := 1 / 3 + u * ((y : ℝ) - x)
  let d : ScoreSpace ε → ENNReal := fun e =>
    if e = x then ENNReal.ofReal (3 * wx)
    else if e = y then ENNReal.ofReal (3 * wy)
    else if e = z then ENNReal.ofReal (3 * wz)
    else 0
  have hxy_ne : x ≠ y := ne_of_lt hxy
  have hxz_ne : x ≠ z := ne_of_lt (lt_trans hxy hyz)
  have hyz_ne : y ≠ z := ne_of_lt hyz
  have hd : Measurable d := by
    dsimp [d]
    exact Measurable.ite (measurableSet_singleton x) measurable_const
      (Measurable.ite (measurableSet_singleton y) measurable_const
        (Measurable.ite (measurableSet_singleton z) measurable_const measurable_const))
  have hscale (w : ℝ) :
      ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (3 * w) = ENNReal.ofReal w := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    exact congrArg ENNReal.ofReal (by ring)
  have hwd : threeScorePerturbedLaw x y z u =
      (threeScoreBaseLaw x y z).withDensity d := by
    unfold threeScorePerturbedLaw threeScoreBaseLaw
    rw [withDensity_add_measure, withDensity_add_measure,
      withDensity_smul_measure, withDensity_smul_measure,
      withDensity_smul_measure, dirac_withDensity, dirac_withDensity,
      dirac_withDensity]
    dsimp only [d]
    simp only [if_pos, if_neg hxy_ne.symm, if_neg hxz_ne.symm,
      if_neg hxy_ne, if_neg hyz_ne.symm, if_neg hxz_ne, if_neg hyz_ne]
    repeat' rw [smul_smul]
    rw [hscale wx, hscale wy, hscale wz]
  letI : IsProbabilityMeasure (threeScoreBaseLaw x y z) :=
    threeScoreBaseLaw_isProbabilityMeasure x y z
  have hrn : (threeScorePerturbedLaw x y z u).rnDeriv
      (threeScoreBaseLaw x y z) =ᵐ[threeScoreBaseLaw x y z] d := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity _ hd
  rw [Causalean.Stat.chiSqDiv]
  trans ∫ e, ((d e).toReal - 1) ^ 2 ∂(threeScoreBaseLaw x y z)
  · exact integral_congr_ae <| hrn.mono fun e he => by
      simpa only using congrArg (fun r : ENNReal => (r.toReal - 1) ^ 2) he
  unfold threeScoreBaseLaw
  rw [integral_add_measure]
  · rw [integral_add_measure]
    · rw [integral_smul_measure, integral_smul_measure, integral_smul_measure]
      simp only [integral_dirac]
      dsimp [d, wx, wy, wz]
      simp only [if_pos, if_neg hxy_ne.symm, if_neg hxz_ne.symm,
        if_neg hxy_ne, if_neg hyz_ne.symm, if_neg hxz_ne, if_neg hyz_ne]
      rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hx.le),
        ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hy.le),
        ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hz.le)]
      norm_num
      ring
    · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
    · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
  · apply Integrable.add_measure
    · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
    · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (integrable_dirac (by simp [enorm])) (by simp)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,x,y,z,u,hxy,hyz,hx,hy,hz,m), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScorePerturbedLaw_product_tv_bound {ε : ℝ}
    (x y z : ScoreSpace ε) (u : ℝ) (hxy : x < y) (hyz : y < z)
    (hx : 0 < 1 / 3 + u * ((z : ℝ) - y))
    (hy : 0 < 1 / 3 - u * ((z : ℝ) - x))
    (hz : 0 < 1 / 3 + u * ((y : ℝ) - x)) (m : ℕ) :
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin m => threeScorePerturbedLaw x y z u))
      (Measure.pi (fun _ : Fin m => threeScoreBaseLaw x y z)) ≤
      (1 / 2 : ℝ) * Real.sqrt
        ((1 + 3 * u ^ 2 * (((z : ℝ) - y) ^ 2 + ((z : ℝ) - x) ^ 2 +
          ((y : ℝ) - x) ^ 2)) ^ m - 1) := by
  letI : IsProbabilityMeasure (threeScorePerturbedLaw x y z u) :=
    threeScorePerturbedLaw_isProbabilityMeasure x y z u hx hy hz
  letI : IsProbabilityMeasure (threeScoreBaseLaw x y z) :=
    threeScoreBaseLaw_isProbabilityMeasure x y z
  have h := threeScorePerturbedLaw_ac_integrable x y z u hxy hyz
  simpa [threeScorePerturbedLaw_chisq x y z u hxy hyz hx hy hz] using
    trialProduct_tv_le_of_chisq (threeScorePerturbedLaw x y z u)
      (threeScoreBaseLaw x y z) h.1 h.2 m

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,T,ρ,x,y,z,u,hxy,hyz,hx,hy,hz,m), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScorePerturbedLaw_commonTrial_tv_bound {ε : ℝ} {T : Type*}
    [MeasurableSpace T] (ρ : Measure T) [IsProbabilityMeasure ρ]
    (x y z : ScoreSpace ε) (u : ℝ) (hxy : x < y) (hyz : y < z)
    (hx : 0 < 1 / 3 + u * ((z : ℝ) - y))
    (hy : 0 < 1 / 3 - u * ((z : ℝ) - x))
    (hz : 0 < 1 / 3 + u * ((y : ℝ) - x)) (m : ℕ) :
    Causalean.Stat.tvDist
      (ρ.prod (Measure.pi (fun _ : Fin m => threeScorePerturbedLaw x y z u)))
      (ρ.prod (Measure.pi (fun _ : Fin m => threeScoreBaseLaw x y z))) ≤
      (1 / 2 : ℝ) * Real.sqrt
        ((1 + 3 * u ^ 2 * (((z : ℝ) - y) ^ 2 + ((z : ℝ) - x) ^ 2 +
          ((y : ℝ) - x) ^ 2)) ^ m - 1) := by
  letI : IsProbabilityMeasure (threeScorePerturbedLaw x y z u) :=
    threeScorePerturbedLaw_isProbabilityMeasure x y z u hx hy hz
  letI : IsProbabilityMeasure (threeScoreBaseLaw x y z) :=
    threeScoreBaseLaw_isProbabilityMeasure x y z
  have hprod := Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add
    ρ ρ
    (Measure.pi (fun _ : Fin m => threeScorePerturbedLaw x y z u))
    (Measure.pi (fun _ : Fin m => threeScoreBaseLaw x y z))
  have hself : Causalean.Stat.tvDist ρ ρ = 0 := by
    unfold Causalean.Stat.tvDist
    simp
  calc
    _ ≤ Causalean.Stat.tvDist ρ ρ +
        Causalean.Stat.tvDist
          (Measure.pi (fun _ : Fin m => threeScorePerturbedLaw x y z u))
          (Measure.pi (fun _ : Fin m => threeScoreBaseLaw x y z)) := hprod
    _ = Causalean.Stat.tvDist
          (Measure.pi (fun _ : Fin m => threeScorePerturbedLaw x y z u))
          (Measure.pi (fun _ : Fin m => threeScoreBaseLaw x y z)) := by rw [hself, zero_add]
    _ ≤ _ := threeScorePerturbedLaw_product_tv_bound
      x y z u hxy hyz hx hy hz m

end
end CausalSmith.PartialID.UnlinkedPropensityAte
