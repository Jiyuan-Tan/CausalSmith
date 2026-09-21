module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridCellAnalysis
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridBlockCalibration

/-! Quantitative pilot-selection probabilities in the exact cell product law. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

/-- Probability that the pilot declares one cell light.  [the stated conditions](hyp:P,tp,threshold,x) [the stated conclusion](goal). -/
noncomputable def hybridPilotLightProbability {d : Nat} (P : DiscreteLaw d)
    (tp : Real) (threshold : Nat) (x : Fin d) : Real :=
  (Measure.pi fun a : Bool ↦
    poissonMeasure (Real.toNNReal (tp * armMass P x a))).real
      (hybridPilotEvent threshold)

/-- Probability that the pilot declares one cell heavy.  [the stated conditions](hyp:P,tp,threshold,x) [the stated conclusion](goal). -/
noncomputable def hybridPilotHeavyProbability {d : Nat} (P : DiscreteLaw d)
    (tp : Real) (threshold : Nat) (x : Fin d) : Real :=
  (Measure.pi fun a : Bool ↦
    poissonMeasure (Real.toNNReal (tp * armMass P x a))).real
      (hybridPilotEvent threshold)ᶜ
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma hybridPilotHeavyProbability_eq_one_sub_light {d : Nat}
    (P : DiscreteLaw d) (tp : Real) (threshold : Nat) (x : Fin d) :
    hybridPilotHeavyProbability P tp threshold x =
      1 - hybridPilotLightProbability P tp threshold x := by
  rw [hybridPilotHeavyProbability, hybridPilotLightProbability,
    measureReal_compl (Set.to_countable (hybridPilotEvent threshold)).measurableSet]
  simp

/-- Exact two-coordinate representation of the pilot probability.  [the stated conclusion](goal). -/
lemma hybridPilotLightProbability_eq_prod {d : Nat} (P : DiscreteLaw d)
    (tp : Real) (threshold : Nat) (x : Fin d) :
    hybridPilotLightProbability P tp threshold x =
      ((poissonMeasure (Real.toNNReal (tp * armMass P x false))).prod
        (poissonMeasure (Real.toNNReal (tp * armMass P x true)))).real
          {z : Nat × Nat | z.1 + z.2 ≤ threshold} := by
  let mu : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (tp * armMass P x a))
  let A : Set (Nat × Nat) := {z | z.1 + z.2 ≤ threshold}
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hmap := (boolPair_measurePreserving mu).map_eq
  have heq : (Measure.pi mu) (hybridPilotEvent threshold) =
      ((Measure.pi mu).map boolPair) A := by
    rw [Measure.map_apply (by fun_prop) hA]
    rfl
  rw [hybridPilotLightProbability, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def, heq, hmap]

/-- Exact two-coordinate representation of the complementary pilot event.  [the stated conclusion](goal). -/
lemma hybridPilotHeavyProbability_eq_prod {d : Nat} (P : DiscreteLaw d)
    (tp : Real) (threshold : Nat) (x : Fin d) :
    hybridPilotHeavyProbability P tp threshold x =
      ((poissonMeasure (Real.toNNReal (tp * armMass P x false))).prod
        (poissonMeasure (Real.toNNReal (tp * armMass P x true)))).real
          {z : Nat × Nat | threshold < z.1 + z.2} := by
  let mu : Bool → Measure Nat := fun a ↦
    poissonMeasure (Real.toNNReal (tp * armMass P x a))
  let A : Set (Nat × Nat) := {z | threshold < z.1 + z.2}
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hmap := (boolPair_measurePreserving mu).map_eq
  have heq : (Measure.pi mu) (hybridPilotEvent threshold)ᶜ =
      ((Measure.pi mu).map boolPair) A := by
    rw [Measure.map_apply (by fun_prop) hA]
    apply congrArg
    ext J
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    exact Nat.not_le
  rw [hybridPilotHeavyProbability, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def, heq, hmap]

/-- C19 before its deterministic exponential absorption.  [the stated conditions](hyp:htp,hp,hk) [the stated conclusion](goal). -/
lemma hybridPilotLightProbability_le_exp {d : Nat} (P : DiscreteLaw d)
    {tp B : Real} (threshold : Nat) (x : Fin d)
    (htp : 0 < tp) (hp : B < cellMass P x)
    (hk : (threshold : Real) ≤ tp * B / 4) :
    hybridPilotLightProbability P tp threshold x ≤
      Real.exp (-(tp * cellMass P x) / 4) := by
  have hs0 : 0 ≤ armMass P x false := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x false y).1
  have hs1 : 0 ≤ armMass P x true := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x true y).1
  have hsum : armMass P x false + armMass P x true = cellMass P x := by
    simp [armMass, cellMass]
    ring
  have hcut : (threshold : Real) < tp *
      (armMass P x false + armMass P x true) / 4 := by
    rw [hsum]
    have := mul_lt_mul_of_pos_left hp htp
    nlinarith
  rw [hybridPilotLightProbability_eq_prod]
  have h := pilot_light_probability_le threshold htp.le hs0 hs1 hcut
  rw [hsum] at h
  have htop : ENNReal.ofReal (Real.exp (-(tp * cellMass P x) / 4)) ≠ ⊤ := by simp
  have hreal :
      (((poissonMeasure (Real.toNNReal (tp * armMass P x false))).prod
        (poissonMeasure (Real.toNNReal (tp * armMass P x true))))
          {z : Nat × Nat | z.1 + z.2 ≤ threshold}).toReal ≤
        (ENNReal.ofReal (Real.exp (-(tp * cellMass P x) / 4))).toReal :=
    ENNReal.toReal_mono htop h
  rw [MeasureTheory.measureReal_def]
  calc
    _ ≤ (ENNReal.ofReal (Real.exp (-(tp * cellMass P x) / 4))).toReal := hreal
    _ = Real.exp (-(tp * cellMass P x) / 4) :=
      ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- C24 in the exact cell-product notation.  [the stated conditions](hyp:htp,hr) [the stated conclusion](goal). -/
lemma hybridPilotHeavyProbability_mul_exp_le_inv_pow {d : Nat}
    (P : DiscreteLaw d) {tp r : Real} (threshold : Nat) (x : Fin d)
    (htp : 0 ≤ tp) (hr : 0 ≤ r) :
    hybridPilotHeavyProbability P tp threshold x *
        Real.exp (-r * (tp * cellMass P x)) ≤ ((1 + r) ^ threshold)⁻¹ := by
  have hs0 : 0 ≤ armMass P x false := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x false y).1
  have hs1 : 0 ≤ armMass P x true := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x true y).1
  have hsum : armMass P x false + armMass P x true = cellMass P x := by
    simp [armMass, cellMass]
    ring
  rw [hybridPilotHeavyProbability_eq_prod, ← hsum]
  exact pilot_heavy_probability_mul_exp_le_inv_pow threshold htp hs0 hs1 hr

/-- Exponential decay on the binary schedule is at most the corresponding
inverse sample-size power.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma exp_neg_twelve_binLen_le (n : Nat) (hn : 1 ≤ n) :
    Real.exp (-12 * binLen n) ≤ ((n : Real) ^ 12)⁻¹ := by
  have hnR : (0 : Real) < n := by positivity
  have hlogn : Real.log (n : Real) ≤ binLen n := by
    have h := logEN_le_binLen n hn
    have hs : logEN n = 1 + Real.log (n : Real) := by
      rw [logEN, Real.log_mul (by positivity : Real.exp 1 ≠ 0) hnR.ne']
      simp
    rw [hs] at h
    linarith
  calc
    Real.exp (-12 * binLen n) ≤ Real.exp (-12 * Real.log (n : Real)) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    _ = ((n : Real) ^ 12)⁻¹ := by
      rw [show -12 * Real.log (n : Real) = -((12 : Nat) * Real.log (n : Real)) by
        push_cast; ring, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnR]

/-- Under the finite predicate, every truly heavy cell is sent to the light
branch with probability at most `n⁻¹²`.  [the stated conditions](hyp:hn,hcal,hp) [the stated conclusion](goal). -/
lemma calibrated_heavy_cell_pilot_le {d : Nat} (P : DiscreteLaw d)
    {n m : Nat} {eps : Real} (hn : 1 ≤ n)
    (hcal : calibrationPredicate n m eps) (x : Fin d)
    (hp : Bscale n m eps < cellMass P x) :
    let bs := blockSizes n m
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    hybridPilotLightProbability P tp (k0 n m eps) x ≤ ((n : Real) ^ 12)⁻¹ := by
  dsimp only
  obtain ⟨_hu, htp, _ht, hB⟩ := calibrationPredicate_positive_parameters hcal
  simp only [calibrationPredicate] at hcal
  rcases hcal with ⟨_hn24, _hu0, _hu1, _hp0, _hp1, _hf0, _hf1,
    _hr0, _hr1, _hL, _htpB, _htB, _hm4, _hm6, htail, _hrat, _hlast⟩
  let tp : Real :=
    (((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8
  let B := Bscale n m eps
  have hk : (k0 n m eps : Real) ≤ tp * B / 4 := by
    exact k0_upper_quarter n m eps (mul_nonneg htp.le hB.le)
  have hpilot := hybridPilotLightProbability_le_exp P (k0 n m eps) x htp hp hk
  have hexp : Real.exp (-(tp * cellMass P x) / 4) ≤
      Real.exp (-12 * binLen n) := by
    apply Real.exp_le_exp.mpr
    have hmass := mul_lt_mul_of_pos_left hp htp
    change 15 * (Ldeg n : Real) + 12 * binLen n ≤ tp * B / 4 at htail
    nlinarith [show 0 ≤ (Ldeg n : Real) by positivity]
  exact hpilot.trans (hexp.trans (exp_neg_twelve_binLen_le n hn))

/-- C25: after multiplication by the heavy-branch bias exponential, the
opposite pilot error is uniformly at most `n⁻¹²`.  [the stated conditions](hyp:heps,heps2,hcal) [the stated conclusion](goal). -/
lemma calibrated_light_cell_heavy_probability_mul_exp_le {d : Nat}
    (P : DiscreteLaw d) {n m : Nat} {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (hcal : calibrationPredicate n m eps) (x : Fin d) :
    let bs := blockSizes n m
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    hybridPilotHeavyProbability P tp (k0 n m eps) x *
        Real.exp (-eps * t * cellMass P x) ≤ ((n : Real) ^ 12)⁻¹ := by
  dsimp only
  obtain ⟨_hu, htp, ht, _hB⟩ := calibrationPredicate_positive_parameters hcal
  have hb_le : barEps eps ≤ eps := (dyadicIndex_spec heps heps2).2
  have hr : 0 ≤ eps *
      ((((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8) /
      ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8) := by
    positivity
  have hraw := hybridPilotHeavyProbability_mul_exp_le_inv_pow P
    (k0 n m eps) x htp.le hr
  have hexp :
      -(eps * (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8) /
          (((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8)) *
          ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8 *
            cellMass P x) =
        -eps * (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8) *
          cellMass P x := by
    norm_num [Nat.cast_add] at htp ⊢
    field_simp [htp.ne']
  rw [hexp] at hraw
  simp only [calibrationPredicate] at hcal
  rcases hcal with ⟨hncal, _hu0, _hu1, _hp0, _hp1, _hf0, _hf1,
    hratio, _hratio1, _hL, _htpB, _htB, _hm4, _hm6, _htail,
    hpow, _hlast⟩
  let ratio : Real :=
    (((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8 /
      ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8)
  have hratio0 : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hbase : 1 + barEps eps * ratio ≤ 1 + eps * ratio := by
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_right hb_le hratio0) 1
  have hpowmono : (1 + barEps eps * ratio) ^ k0 n m eps ≤
      (1 + eps * ratio) ^ k0 n m eps := by
    exact pow_le_pow_left₀ (by nlinarith [mul_nonneg heps.le hratio0]) hbase _
  have hpow' : (n : Real) ^ 12 ≤
      (1 + barEps eps * ratio) ^ k0 n m eps := by
    convert hpow using 1 <;> dsimp [ratio] <;> ring
  have hden : 0 < (n : Real) ^ 12 := by
    have : 0 < n := by
      omega
    positivity
  have hinv : ((1 + eps * ratio) ^ k0 n m eps)⁻¹ ≤ ((n : Real) ^ 12)⁻¹ :=
    inv_anti₀ hden (hpow'.trans hpowmono)
  exact hraw.trans (by
    simpa only [ratio, div_eq_mul_inv, mul_assoc] using hinv)

/-- On a truly heavy cell, the intrinsic inverse-count bias exponential is
also at most the scheduled inverse power.  [the stated conditions](hyp:heps,heps2,hn,hcal,hp) [the stated conclusion](goal). -/
lemma calibrated_heavy_cell_bias_exp_le {d : Nat} (P : DiscreteLaw d)
    {n m : Nat} {eps : Real} (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (hn : 1 ≤ n) (hcal : calibrationPredicate n m eps) (x : Fin d)
    (hp : Bscale n m eps < cellMass P x) :
    Real.exp (-eps *
      (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8) * cellMass P x) ≤
      ((n : Real) ^ 12)⁻¹ := by
  have hbar := (dyadicIndex_spec heps heps2).2
  have ht : 0 < (((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8 :=
    (calibrationPredicate_positive_parameters hcal).2.2.1
  have hB := (calibrationPredicate_positive_parameters hcal).2.2.2
  have hcal' := hcal
  simp only [calibrationPredicate] at hcal'
  rcases hcal' with ⟨_hn24, _hu0, _hu1, _hp0, _hp1, _hf0, _hf1,
    _hr0, _hr1, _hL, _htpB, _htB, _hm4, _hm6, _htail, _hrat, hlast⟩
  have hprod : 12 * binLen n ≤ eps *
      (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8) * cellMass P x := by
    have h1 := mul_le_mul_of_nonneg_right hbar
      (mul_nonneg ht.le hB.le)
    have h2 := mul_le_mul_of_nonneg_left hp.le
      (mul_nonneg heps.le ht.le)
    nlinarith
  calc
    _ ≤ Real.exp (-12 * binLen n) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := exp_neg_twelve_binLen_le n hn

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
