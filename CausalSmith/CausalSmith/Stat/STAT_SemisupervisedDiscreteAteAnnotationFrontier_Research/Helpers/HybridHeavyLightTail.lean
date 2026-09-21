module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridPilotAggregate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLightAggregate
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridExponentialAbsorption

/-! The heavy-cell contribution of the mistakenly selected light branch. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Polynomial

/-- Coefficient-L1 control of the Chebyshev continuation outside its fitting interval.  [the stated conditions](hyp:hL,hz,hzy,hy) [the stated conclusion](goal). -/
lemma abs_chebG_eval_le {L : Nat} (hL : 2 ≤ L) {z y : Real}
    (hz : 0 ≤ z) (hzy : z ≤ y) (hy : 0 ≤ y) :
    |(chebG L).eval z| ≤ coefficientL1 (chebG L) * (1 + y) ^ L := by
  obtain ⟨_A, _hA, hcert⟩ := chebyshev_factorial_certificate
  have hdeg := (hcert L hL).1
  rw [Polynomial.eval_eq_sum]
  change |∑ i ∈ (chebG L).support, (chebG L).coeff i * z ^ i| ≤ _
  calc
    _ ≤ ∑ i ∈ (chebG L).support,
        |(chebG L).coeff i * z ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ (chebG L).support,
        |(chebG L).coeff i| * (1 + y) ^ L := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hz _)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hiz : i ≤ (chebG L).natDegree :=
        Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
      have hiL : i ≤ L := hiz.trans (hdeg.trans (Nat.sub_le L 2))
      exact (pow_le_pow_left₀ hz (by linarith) i).trans
        (pow_le_pow_right₀ (by linarith) hiL)
    _ = _ := by
      rw [← Finset.sum_mul]
      rfl

/-- C20, in a form whose extra continuation power is absorbed by C22.  [the stated conditions](hyp:hu,ht,hB,hL,hp) [the stated conclusion](goal). -/
lemma abs_integral_hybridLightPools_heavy_le {d : Nat}
    (P : DiscreteLaw d) (x : Fin d) {u t B : Real} {L : Nat}
    (hu : 0 < u) (ht : 0 < t) (hB : 0 < B) (hL : 2 ≤ L)
    (hp : B < cellMass P x) :
    |∫ W, hybridLightPools L B u t W ∂
      ((Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
       (Measure.pi fun a : Bool ↦
        poissonMeasure (Real.toNNReal (t * armMass P x a))))| ≤
      cellMass P x * 14 ^ L *
        (1 + cellMass P x / B) ^ (2 * L) := by
  have hp0 := (cellMass_mem_unitInterval P x).1
  have hs0 : 0 ≤ armMass P x false := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x false y).1
  have hs1 : 0 ≤ armMass P x true := Finset.sum_nonneg fun y _ ↦
    (jointMass_mem_unitInterval P x true y).1
  have hsum : armMass P x false + armMass P x true = cellMass P x := by
    simp [armMass, cellMass]
    ring
  have hsle (a : Bool) : armMass P x a ≤ cellMass P x := by
    cases a <;> rw [← hsum] <;> linarith
  have hmle (a : Bool) : markedMass P x a ≤ cellMass P x := by
    calc
      markedMass P x a ≤ armMass P x a := by
        simp [markedMass, armMass]
        exact (jointMass_mem_unitInterval P x a false).1
      _ ≤ cellMass P x := hsle a
  have hG (a : Bool) : |(chebG L).eval (armMass P x a / B)| ≤
      coefficientL1 (chebG L) * (1 + cellMass P x / B) ^ L :=
    abs_chebG_eval_le hL (div_nonneg (by cases a <;> assumption) hB.le)
      (div_le_div_of_nonneg_right (hsle a) hB.le) (div_nonneg hp0 hB.le)
  have hcoef := (explicit_chebyshev_calibration L hL).2.1
  rw [integral_hybridLightPools P hu ht hB L x]
  have hy0 : 0 ≤ cellMass P x / B := div_nonneg hp0 hB.le
  have hy1 : cellMass P x / B ≤ (1 + cellMass P x / B) ^ L := by
    have hybase : cellMass P x / B ≤ 1 + cellMass P x / B := by linarith
    exact hybase.trans (by
      have : 1 ≤ L := by omega
      simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + cellMass P x / B) this)
  have hm0 : 0 ≤ markedMass P x false :=
    (jointMass_mem_unitInterval P x false true).1
  have hm1 : 0 ≤ markedMass P x true :=
    (jointMass_mem_unitInterval P x true true).1
  calc
    |_ - _| ≤ |markedMass P x true * (cellMass P x / B) *
        (chebG L).eval (armMass P x true / B)| +
      |markedMass P x false * (cellMass P x / B) *
        (chebG L).eval (armMass P x false / B)| := abs_sub _ _
    _ ≤ 2 * cellMass P x * (cellMass P x / B) *
        (coefficientL1 (chebG L) * (1 + cellMass P x / B) ^ L) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hm0, abs_of_nonneg hm1, abs_of_nonneg hy0]
      have htrue : markedMass P x true * (cellMass P x / B) *
          |(chebG L).eval (armMass P x true / B)| ≤
          cellMass P x * (cellMass P x / B) *
            (coefficientL1 (chebG L) * (1 + cellMass P x / B) ^ L) := by
        gcongr
        · exact hmle true
        · exact hG true
      have hfalse : markedMass P x false * (cellMass P x / B) *
          |(chebG L).eval (armMass P x false / B)| ≤
          cellMass P x * (cellMass P x / B) *
            (coefficientL1 (chebG L) * (1 + cellMass P x / B) ^ L) := by
        gcongr
        · exact hmle false
        · exact hG false
      linarith
    _ ≤ cellMass P x * 14 ^ L *
        (1 + cellMass P x / B) ^ (2 * L) := by
      have hpcoef : 2 * coefficientL1 (chebG L) ≤ 14 ^ L := hcoef
      have hcoef0 : 0 ≤ coefficientL1 (chebG L) := by
        unfold coefficientL1
        exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      have hpow0 : 0 ≤ (1 + cellMass P x / B) ^ L := by positivity
      rw [show 2 * L = L + L by omega, pow_add]
      calc
        2 * cellMass P x * (cellMass P x / B) *
            (coefficientL1 (chebG L) * (1 + cellMass P x / B) ^ L) =
          cellMass P x * (cellMass P x / B) *
            (2 * coefficientL1 (chebG L)) *
              (1 + cellMass P x / B) ^ L := by ring
        _ ≤ cellMass P x * (1 + cellMass P x / B) ^ L *
            (14 ^ L) * (1 + cellMass P x / B) ^ L := by gcongr
        _ = _ := by ring

/-- C23 mean part, cellwise: the wrong-light mean retains a factor of cell mass.  [the stated conditions](hyp:heps,hn,hcal,hp) [the stated conclusion](goal). -/
lemma calibrated_heavy_cell_light_mean_le {d : Nat}
    (P : DiscreteLaw d) {n m : Nat} {eps : Real}
    (heps : 0 < eps) (hn : 1 ≤ n)
    (hcal : calibrationPredicate n m eps) (x : Fin d)
    (hp : Bscale n m eps < cellMass P x) :
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    hybridPilotLightProbability P tp (k0 n m eps) x *
      |∫ W, hybridLightPools (Ldeg n) (Bscale n m eps) u t W ∂
        ((Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
         (Measure.pi fun a : Bool ↦
          poissonMeasure (Real.toNNReal (t * armMass P x a))))| ≤
      cellMass P x * ((n : Real) ^ 12)⁻¹ := by
  dsimp only
  let u : Real := (blockSizes n m).M0 / 8
  let tp : Real := ((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  obtain ⟨hu, htp, ht, hB⟩ := calibrationPredicate_positive_parameters hcal
  have hL : 2 ≤ Ldeg n := Ldeg_ge_two n
  have hcal' := hcal
  simp only [calibrationPredicate] at hcal'
  rcases hcal' with ⟨hn24, _hu0, _hu1, _hp0, _hp1, _hf0, _hf1,
    _hr0, _hr1, hLbin, _htpB, _htB, _hm4, _hm6, _htail, _hrat, _hlast⟩
  let p := cellMass P x
  let B := Bscale n m eps
  let y := p / B
  have hy : 1 ≤ y := by
    dsimp [y, p, B]
    apply (le_div_iff₀ hB).2
    simpa using hp.le
  have hpi := hybridPilotLightProbability_le_exp P (k0 n m eps) x htp hp
    (k0_upper_quarter n m eps (mul_nonneg htp.le hB.le))
  have hmean := abs_integral_hybridLightPools_heavy_le P x hu ht hB hL hp
  have htpBL := (blockSizes_mul_Bscale_lower n m eps hn24).1
  have hexp : Real.exp (-(tp * p) / 4) ≤
      Real.exp (-(Hconst eps : Real) * Ldeg n * y / 4) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right htpBL (show 0 ≤ y by linarith)
    have hp_eq : p = B * y := by
      dsimp [y, p, B]
      field_simp [hB.ne']
    rw [hp_eq]
    dsimp [tp, B]
    nlinarith [hmul]
  have h14 : (14 : Real) ^ Ldeg n ≤ starA ^ Ldeg n := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num [starA]) _
  have hcancel := factorial_growth_mul_heavy_exp_le (L := Ldeg n) heps hy
  have hdecay : Real.exp (-24 * (Ldeg n : Real) * y / cCirc) ≤
      ((n : Real) ^ 12)⁻¹ := by
    have hc : 0 < cCirc := by norm_num [cCirc]
    have hraw : 12 * binLen n ≤ 24 * (Ldeg n : Real) * y / cCirc := by
      have hmul := mul_le_mul_of_nonneg_right hLbin (show 0 ≤ y by linarith)
      apply (le_div_iff₀ hc).2
      nlinarith [mul_nonneg (show 0 ≤ (binLen n : Real) by positivity)
        (show 0 ≤ y by linarith)]
    have h12 := exp_neg_twelve_binLen_le n hn
    norm_num only [neg_mul] at h12 ⊢
    simpa only [neg_mul, neg_div] using
      (Real.exp_le_exp.mpr (neg_le_neg hraw)).trans h12
  have hfactor : (14 : Real) ^ Ldeg n * (1 + p / B) ^ (2 * Ldeg n) *
      Real.exp (-(tp * p) / 4) ≤ ((n : Real) ^ 12)⁻¹ := by
    calc
      _ ≤ starA ^ Ldeg n * (1 + y) ^ (2 * Ldeg n) *
          Real.exp (-(Hconst eps : Real) * Ldeg n * y / 4) := by
        dsimp [y, p, B]
        gcongr
      _ ≤ Real.exp (-24 * (Ldeg n : Real) * y / cCirc) := hcancel
      _ ≤ _ := hdecay
  have hpi0 : 0 ≤ hybridPilotLightProbability P tp (k0 n m eps) x :=
    measureReal_nonneg
  have hp0 := (cellMass_mem_unitInterval P x).1
  calc
    _ ≤ hybridPilotLightProbability P tp (k0 n m eps) x *
        (p * 14 ^ Ldeg n * (1 + p / B) ^ (2 * Ldeg n)) :=
      mul_le_mul_of_nonneg_left hmean hpi0
    _ ≤ Real.exp (-(tp * p) / 4) *
        (p * 14 ^ Ldeg n * (1 + p / B) ^ (2 * Ldeg n)) := by
      gcongr
    _ ≤ p * ((n : Real) ^ 12)⁻¹ := by
      have := mul_le_mul_of_nonneg_left hfactor hp0
      nlinarith

/-- C23, cellwise form: the pilot exponential cancels the polynomial growth.  [the stated conditions](hyp:heps,hn,hcal,hp) [the stated conclusion](goal). -/
lemma calibrated_heavy_cell_light_secondMoment_le {d : Nat}
    (P : DiscreteLaw d) {n m : Nat} {eps : Real}
    (heps : 0 < eps) (hn : 1 ≤ n)
    (hcal : calibrationPredicate n m eps) (x : Fin d)
    (hp : Bscale n m eps < cellMass P x) :
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    hybridPilotLightProbability P tp (k0 n m eps) x *
        (∫ W, hybridLightPools (Ldeg n) (Bscale n m eps) u t W ^ 2 ∂
          ((Measure.pi fun a : Bool ↦
            poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
           (Measure.pi fun a : Bool ↦
            poissonMeasure (Real.toNNReal (t * armMass P x a))))) ≤
      4 * (cellMass P x / u + cellMass P x ^ 2) * ((n : Real) ^ 12)⁻¹ := by
  dsimp only
  let u : Real := (blockSizes n m).M0 / 8
  let tp : Real := ((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  obtain ⟨hu_pos, htp_pos, ht_pos, hB⟩ :=
    calibrationPredicate_positive_parameters hcal
  have hL : 2 ≤ Ldeg n := Ldeg_ge_two n
  simp only [calibrationPredicate] at hcal
  rcases hcal with ⟨hn24, _hu0, _hu1, _hp0, _hp1, _hf0, _hf1,
    _hr0, _hr1, _hL, _htpB, htB, _hm4, _hm6, _htail, _hrat, _hlast⟩
  let p := cellMass P x
  let B := Bscale n m eps
  let y := p / B
  have hy : 1 ≤ y := by
    dsimp [y, p, B]
    exact (le_div_iff₀ hB).2 (by linarith)
  have hpi := hybridPilotLightProbability_le_exp P (k0 n m eps) x htp_pos hp
    (k0_upper_quarter n m eps (mul_nonneg htp_pos.le hB.le))
  have hsecond := integral_hybridLightPools_sq_le P x hu_pos ht_pos hB hL htB
  have htpBL := (blockSizes_mul_Bscale_lower n m eps hn24).1
  have hexp : Real.exp (-(tp * p) / 4) ≤
      Real.exp (-(Hconst eps : Real) * Ldeg n * y / 4) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right htpBL (show 0 ≤ y by linarith)
    have hp_eq : p = B * y := by
      dsimp [y, p, B]
      field_simp [hB.ne']
    rw [hp_eq]
    have hneg := neg_le_neg hmul
    have hdiv := div_le_div_of_nonneg_right hneg (by norm_num : (0 : Real) ≤ 4)
    dsimp [tp, B]
    nlinarith [hdiv]
  have hcancel := factorial_growth_mul_heavy_exp_le (L := Ldeg n) heps hy
  have hdecay : Real.exp (-24 * (Ldeg n : Real) * y / cCirc) ≤
      ((n : Real) ^ 12)⁻¹ := by
    have hLbin : cCirc * binLen n / 2 ≤ (Ldeg n : Real) := by
      simpa only [calibrationPredicate] using _hL
    have hc : 0 < cCirc := by norm_num [cCirc]
    have hbin0 : 0 ≤ (binLen n : Real) := by positivity
    have hraw : 12 * binLen n ≤ 24 * (Ldeg n : Real) * y / cCirc := by
      have := mul_le_mul_of_nonneg_right hLbin (show 0 ≤ y by linarith)
      apply (le_div_iff₀ hc).2
      nlinarith [mul_nonneg hbin0 (show 0 ≤ y by linarith)]
    have h12 := exp_neg_twelve_binLen_le n hn
    norm_num only [neg_mul] at h12 ⊢
    simpa only [neg_mul, neg_div] using
      (Real.exp_le_exp.mpr (neg_le_neg hraw)).trans h12
  have hfactor :
      (starA : Real) ^ Ldeg n * (1 + p / B) ^ (2 * Ldeg n) *
          Real.exp (-(tp * p) / 4) ≤ ((n : Real) ^ 12)⁻¹ := by
    calc
      _ ≤ (starA : Real) ^ Ldeg n * (1 + y) ^ (2 * Ldeg n) *
          Real.exp (-(Hconst eps : Real) * Ldeg n * y / 4) := by
            dsimp [y, p, B]
            exact mul_le_mul_of_nonneg_left hexp
              (mul_nonneg (pow_nonneg (by positivity) _)
                (pow_nonneg (by positivity) _))
      _ ≤ Real.exp (-24 * (Ldeg n : Real) * y / cCirc) := hcancel
      _ ≤ _ := hdecay
  have hpi0 : 0 ≤ hybridPilotLightProbability P tp (k0 n m eps) x :=
    MeasureTheory.measureReal_nonneg
  have hbase0 : 0 ≤ 4 * (p / u + p ^ 2) := by
    have hp0 := (cellMass_mem_unitInterval P x).1
    positivity
  calc
    _ ≤ hybridPilotLightProbability P tp (k0 n m eps) x *
      (4 * (p / u + p ^ 2) *
          ((starA : Real) ^ Ldeg n * (1 + p / B) ^ (2 * Ldeg n))) :=
      mul_le_mul_of_nonneg_left hsecond hpi0
    _ ≤ Real.exp (-(tp * p) / 4) *
        (4 * (p / u + p ^ 2) *
          ((starA : Real) ^ Ldeg n * (1 + p / B) ^ (2 * Ldeg n))) :=
      mul_le_mul_of_nonneg_right hpi
        (mul_nonneg hbase0 (mul_nonneg (pow_nonneg (by positivity) _)
          (pow_nonneg (by positivity) _)))
    _ ≤ 4 * (p / u + p ^ 2) * ((n : Real) ^ 12)⁻¹ := by
      nlinarith [mul_le_mul_of_nonneg_left hfactor hbase0]

/-- C23 summed over the truly heavy cells, without an alphabet-size factor.  [the stated conditions](hyp:heps,hn,hcal) [the stated conclusion](goal). -/
lemma sum_heavy_light_secondMoment_le {d : Nat}
    (P : DiscreteLaw d) {n m : Nat} {eps : Real}
    (heps : 0 < eps) (hn : 1 ≤ n)
    (hcal : calibrationPredicate n m eps) :
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    (∑ x ∈ Finset.univ.filter
        (fun x : Fin d ↦ Bscale n m eps < cellMass P x),
      hybridPilotLightProbability P tp (k0 n m eps) x *
        (∫ W, hybridLightPools (Ldeg n) (Bscale n m eps) u t W ^ 2 ∂
          ((Measure.pi fun a : Bool ↦
            poissonMeasure (Real.toNNReal (u * markedMass P x a))).prod
           (Measure.pi fun a : Bool ↦
            poissonMeasure (Real.toNNReal (t * armMass P x a)))))) ≤
      132 * ((n : Real) ^ 12)⁻¹ := by
  dsimp only
  classical
  let S : Finset (Fin d) := Finset.univ.filter
    (fun x ↦ Bscale n m eps < cellMass P x)
  let u : Real := (blockSizes n m).M0 / 8
  obtain ⟨hu, _htp, _ht, _hB⟩ := calibrationPredicate_positive_parameters hcal
  have hnR : (0 : Real) < n := by positivity
  have hp0 (x : Fin d) : 0 ≤ cellMass P x := (cellMass_mem_unitInterval P x).1
  have hsumAll : ∑ x : Fin d, cellMass P x = 1 :=
    cellMass_sum_eq_one_annotation P
  have hsum1 : ∑ x ∈ S, cellMass P x ≤ 1 := by
    rw [← hsumAll]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [S])
      (fun _ _ _ ↦ hp0 _)
  have hsq : ∑ x ∈ S, cellMass P x ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ x ∈ S, cellMass P x := Finset.sum_le_sum fun x _ ↦ by
        have hp1 := (cellMass_mem_unitInterval P x).2
        nlinarith [mul_nonneg (hp0 x) (sub_nonneg.mpr hp1)]
      _ ≤ 1 := hsum1
  simp only [calibrationPredicate] at hcal
  have hu_ratio := hcal.2.1
  have hnu : (n : Real) / 32 ≤ u := by
    have := (le_div_iff₀ hnR).1 hu_ratio
    dsimp [u]
    nlinarith
  have huinv : u⁻¹ ≤ 32 := by
    have hu32 : (1 : Real) / 32 ≤ u := by
      have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
      nlinarith
    calc
      u⁻¹ ≤ ((1 : Real) / 32)⁻¹ := inv_anti₀ (by norm_num) hu32
      _ = 32 := by norm_num
  have hpoint (x : Fin d) (hx : x ∈ S) :=
    calibrated_heavy_cell_light_secondMoment_le P heps hn
      (show calibrationPredicate n m eps from by
        simpa only [calibrationPredicate] using hcal) x
      (by simpa [S] using (Finset.mem_filter.mp hx).2)
  change (∑ x ∈ S, _) ≤ _
  calc
    _ ≤ ∑ x ∈ S, 4 * (cellMass P x / u + cellMass P x ^ 2) *
        ((n : Real) ^ 12)⁻¹ := Finset.sum_le_sum fun x hx ↦ hpoint x hx
    _ = 4 * (((∑ x ∈ S, cellMass P x) / u) +
        ∑ x ∈ S, cellMass P x ^ 2) * ((n : Real) ^ 12)⁻¹ := by
      have hdivsum : (∑ x ∈ S, cellMass P x / u) =
          (∑ x ∈ S, cellMass P x) / u := by rw [Finset.sum_div]
      rw [← hdivsum, ← Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_mul]
    _ ≤ 132 * ((n : Real) ^ 12)⁻¹ := by
      have hinv0 : 0 ≤ ((n : Real) ^ 12)⁻¹ := by positivity
      have hsum0 : 0 ≤ ∑ x ∈ S, cellMass P x :=
        Finset.sum_nonneg fun x _ ↦ hp0 x
      have hdiv : (∑ x ∈ S, cellMass P x) / u ≤ 32 := by
        rw [div_eq_mul_inv]
        calc
          _ ≤ 1 * u⁻¹ := mul_le_mul hsum1 le_rfl (by positivity) (by positivity)
          _ ≤ 1 * 32 := mul_le_mul_of_nonneg_left huinv zero_le_one
          _ = 32 := by norm_num
      nlinarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
