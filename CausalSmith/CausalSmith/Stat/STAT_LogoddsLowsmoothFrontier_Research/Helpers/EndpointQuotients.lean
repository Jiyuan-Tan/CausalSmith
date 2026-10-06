module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EndpointRadii

/-! # Literal quotient widths

The denominator floor controls both reciprocal magnitudes and reciprocal widths.
The four-corner product estimate then bounds the actual quotient evaluation,
including numerator boxes that straddle zero.
-/
public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [A denominator above the public floor has bounded reciprocal endpoints and width.](goal) Under [the stated assumptions](hyp:hD). -/
-- @node: endpoint_reciprocal_bounds
lemma endpoint_reciprocal_bounds (D : RatInterval) (hD : 1/512 ≤ D.lo) :
    ∃ h : D.AwayFromZero,
      |(D.inv h).lo| ≤ 512 ∧ |(D.inv h).hi| ≤ 512 ∧
      (D.inv h).width ≤ 512^2*D.width := by
  have hlo : 0 < D.lo := lt_of_lt_of_le (by norm_num) hD
  have hhi : 0 < D.hi := hlo.trans_le D.lo_le_hi
  refine ⟨Or.inr hlo, ?_, ?_, ?_⟩
  · change |D.hi⁻¹| ≤ 512
    rw [abs_of_pos (inv_pos.mpr hhi)]
    rw [inv_le_comm₀ hhi (by norm_num : (0 : ℚ) < 512)]
    norm_num
    exact hD.trans D.lo_le_hi
  · change |D.lo⁻¹| ≤ 512
    rw [abs_of_pos (inv_pos.mpr hlo)]
    rw [inv_le_comm₀ hlo (by norm_num : (0 : ℚ) < 512)]
    norm_num
    exact hD
  · change D.lo⁻¹-D.hi⁻¹ ≤ 512^2*(D.hi-D.lo)
    have hid : D.lo⁻¹-D.hi⁻¹ = (D.hi-D.lo)/(D.lo*D.hi) := by
      field_simp
      <;> ring
    rw [hid]
    apply (div_le_iff₀ (mul_pos hlo hhi)).2
    have hp : (1/512 : ℚ)^2 ≤ D.lo*D.hi :=
      by simpa only [pow_two] using mul_le_mul hD (hD.trans D.lo_le_hi) (by norm_num) hlo.le
    have hw : 0 ≤ D.hi-D.lo := sub_nonneg.mpr D.lo_le_hi
    nlinarith [mul_nonneg hw (show 0 ≤ 512^2*(D.lo*D.hi)-1 by nlinarith)]

/-- [Exact rational quotient evaluation preserves containment and has the roadmap width bound.](goal) Under [the stated assumptions](hyp:hc,hd,hv,hz,hD,hB,hClo,hChi). -/
-- @node: endpoint_quotient_enclosure
lemma endpoint_quotient_enclosure (E : ArithmeticEngine) (q : ℕ) (xs : List RatInterval)
    (c d : BoxExpr) (C D : RatInterval) (v z : ℝ) (B : ℚ)
    (hc : c.eval E q xs = some C) (hd : d.eval E q xs = some D)
    (hv : C.Contains v) (hz : D.Contains z) (hD : 1/512 ≤ D.lo)
    (hB : 0 ≤ B) (hClo : |C.lo| ≤ B) (hChi : |C.hi| ≤ B) :
    ∃ Q : RatInterval, (BoxExpr.div c d).eval E q xs = some Q ∧
      Q.Contains (v/z) ∧
      (Q.width : ℝ) ≤ 512*(C.width : ℝ)+(B : ℝ)*512^2*(D.width : ℝ) := by
  obtain ⟨h, hlo, hhi, hw⟩ := endpoint_reciprocal_bounds D hD
  have hpos : 0 < D.lo := lt_of_lt_of_le (by norm_num) hD
  refine ⟨C.div D h, ?_, RatInterval.div_sound h hv hz, ?_⟩
  · simp [BoxExpr.eval, hc, hd, boxDiv, hpos]
  · have hp := endpoint_product_width C (D.inv h) B 512 hB (by norm_num)
      hClo hChi hlo hhi
    have hdw : 0 ≤ D.width := D.width_nonneg
    have hb := mul_le_mul_of_nonneg_left hw hB
    have hq : (C.div D h).width ≤ 512*C.width+B*512^2*D.width := by
      dsimp only [RatInterval.div]
      nlinarith only [hp, hb]
    exact_mod_cast hq

/-- [Width contraction for logarithms on the public positive argument range. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hI). -/
-- @node: endpoint_log_range_width
lemma endpoint_log_range_width (I : RatInterval) (hI : (1/2 : ℚ) ≤ I.lo) :
    Real.log (I.hi : ℝ)-Real.log (I.lo : ℝ) ≤ 2*(I.width : ℝ) := by
  have hlo : (1/2 : ℝ) ≤ I.lo := by
    have h : ((1/2 : ℚ) : ℝ) ≤ (I.lo : ℝ) := Rat.cast_le.mpr hI
    norm_num at h
    exact h
  have ho : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.lo_le_hi
  have hpos : (0 : ℝ) < I.lo := by linarith
  have hhi : (0 : ℝ) < I.hi := hpos.trans_le ho
  rw [← Real.log_div hhi.ne' hpos.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hhi hpos)
  have hb : (I.hi : ℝ)/(I.lo : ℝ)-1 ≤ 2*((I.hi : ℝ)-I.lo) := by
    rw [div_sub_one hpos.ne']
    apply (div_le_iff₀ hpos).2
    nlinarith [mul_nonneg (sub_nonneg.mpr ho) (show 0 ≤ 2*(I.lo : ℝ)-1 by linarith)]
  exact h.trans (by simpa [RatInterval.width] using hb)

/-- The two clipping exponentials stay strictly inside the public argument range. [the stated conclusion](goal) holds. -/
-- @node: endpoint_exp_half_bounds
lemma endpoint_exp_half_bounds :
    (9/16 : ℝ) ≤ Real.exp (-(1/2)) ∧ Real.exp (1/2 : ℝ) ≤ 16/9 := by
  have hquarter : Real.exp (1/4 : ℝ) ≤ 4/3 := by
    have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) < 1)
    norm_num at h
    exact h
  have hhalf : Real.exp (1/2 : ℝ) ≤ 16/9 := by
    have he : Real.exp (1/2 : ℝ) = Real.exp (1/4)*Real.exp (1/4) := by
      rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith [Real.exp_pos (1/4 : ℝ)]
  refine ⟨?_, hhalf⟩
  rw [Real.exp_neg]
  have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 16/9) (Real.exp_pos (1/2 : ℝ))).2 hhalf
  norm_num at h
  exact h

/-- The literal exponential boundary boxes have two-error widths and positive public bounds. Under the stated assumptions. [The stated hypotheses](hyp:hE,hq) hold, and [the stated conclusion follows](goal). -/
-- @node: endpoint_exp_boundary_boxes
lemma endpoint_exp_boundary_boxes (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (hq : precisionError q ≤ 1/16) :
    let A := E.expBox q (RatInterval.point (-(1/2)))
    let B := E.expBox q (RatInterval.point (1/2))
    A.Contains (Real.exp (-(1/2))) ∧ B.Contains (Real.exp (1/2)) ∧
    1/2 ≤ A.lo ∧ B.hi ≤ 2 ∧
    (A.width : ℝ) ≤ 2*precisionError q ∧ (B.width : ℝ) ≤ 2*precisionError q := by
  dsimp only
  have hA := (hE.2.2.1 q (RatInterval.point (-(1/2)))).1
  have hB := (hE.2.2.1 q (RatInterval.point (1/2))).1
  have hcA := hA.1 _ (RatInterval.point_sound (-(1/2)))
  have hcB := hB.1 _ (RatInterval.point_sound (1/2))
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] at hcA hcB
  have haL := hA.2.2.1
  have haH := hA.2.2.2.2
  have hbL := hB.2.2.1
  have hbH := hB.2.2.2.2
  change Real.exp (((-(1/2) : ℚ) : ℝ)) - (E.expBox q (RatInterval.point (-(1/2)))).lo ≤ precisionError q at haL
  change (E.expBox q (RatInterval.point (-(1/2)))).hi - Real.exp (((-(1/2) : ℚ) : ℝ)) ≤ precisionError q at haH
  change Real.exp (((1/2 : ℚ) : ℝ)) - (E.expBox q (RatInterval.point (1/2))).lo ≤ precisionError q at hbL
  change (E.expBox q (RatInterval.point (1/2))).hi - Real.exp (((1/2 : ℚ) : ℝ)) ≤ precisionError q at hbH
  norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] at haL haH hbL hbH
  obtain ⟨hlo, hhi⟩ := endpoint_exp_half_bounds
  refine ⟨hcA, hcB, ?_, ?_, ?_, ?_⟩
  · have h : (1/2 : ℝ) ≤ (E.expBox q (RatInterval.point (-(1/2)))).lo := by linarith
    have h' : (((1/2 : ℚ) : ℝ)) ≤ (E.expBox q (RatInterval.point (-(1/2)))).lo := by simpa using h
    exact Rat.cast_le.mp h'
  · have h : ((E.expBox q (RatInterval.point (1/2))).hi : ℝ) ≤ 2 := by linarith
    exact_mod_cast h
  · simp only [RatInterval.width, Rat.cast_sub]; linarith
  · simp only [RatInterval.width, Rat.cast_sub]; linarith

/-- [A successful positive argument produces a logarithm box with twice its input width plus two errors.](goal) Under [the stated assumptions](hyp:hE,he,hv). Under [the stated assumptions](hyp:hlo). -/
-- @node: endpoint_log_enclosure
lemma endpoint_log_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (xs : List RatInterval) (e : BoxExpr) (I : RatInterval) (v : ℝ)
    (he : e.eval E q xs = some I) (hv : I.Contains v) (hlo : (1/2 : ℚ) ≤ I.lo) :
    ∃ L : RatInterval, (BoxExpr.log e).eval E q xs = some L ∧
      L.Contains (Real.log v) ∧
      (L.width : ℝ) ≤ 2*(I.width : ℝ)+2*precisionError q := by
  have hpos : 0 < I.lo := lt_of_lt_of_le (by norm_num) hlo
  have hc := hE.2.2.2.1 q I hpos
  refine ⟨E.logBox q I, ?_, hc.1 _ hv, ?_⟩
  · simp [BoxExpr.eval, he, hpos]
  · have hL := hc.2.2.1
    have hH := hc.2.2.2.2
    have hw := endpoint_log_range_width I hlo
    simp only [RatInterval.width, Rat.cast_sub] at *
    linarith

/-- [The literal clipping and logarithm tree terminates and propagates the quotient width.](goal) Under [the stated assumptions](hyp:hE,hq,hc,hd,hv,hz,hD,hB,hClo,hChi). -/
-- @node: endpoint_inversion_enclosure
lemma endpoint_inversion_enclosure (E : ArithmeticEngine) (hE : E.Admissible)
    (q : ℕ) (hq : precisionError q ≤ 1/16) (xs : List RatInterval)
    (c d : BoxExpr) (C D : RatInterval) (v z : ℝ) (B : ℚ)
    (hc : c.eval E q xs = some C) (hd : d.eval E q xs = some D)
    (hv : C.Contains v) (hz : D.Contains z) (hD : 1/512 ≤ D.lo)
    (hB : 0 ≤ B) (hClo : |C.lo| ≤ B) (hChi : |C.hi| ≤ B) :
    ∃ L : RatInterval, (inversionExpression c d).eval E q xs = some L ∧
      L.Contains (inversion v z) ∧
      (L.width : ℝ) ≤ 2*(512*(C.width : ℝ)+(B : ℝ)*512^2*(D.width : ℝ))+6*precisionError q := by
  obtain ⟨Q, heQ, hvQ, hwQ⟩ := endpoint_quotient_enclosure E q xs c d C D v z B
    hc hd hv hz hD hB hClo hChi
  let A := E.expBox q (RatInterval.point (-(1/2)))
  let Bp := E.expBox q (RatInterval.point (1/2))
  let J := (RatInterval.point 1).add Q
  let I := boxMax A (boxMin Bp J)
  obtain ⟨hvA, hvB, hloA, _hhiB, hwA, hwB⟩ := endpoint_exp_boundary_boxes E hE q hq
  have hvJ : J.Contains (1+v/z) := by
    exact RatInterval.add_sound (by norm_num [RatInterval.point, RatInterval.Contains]) hvQ
  have hvI : I.Contains (clip (Real.exp (-(1/2))) (Real.exp (1/2)) (1+v/z)) :=
    (endpoint_min_max_contains A (boxMin Bp J) _ _ hvA
      (endpoint_min_max_contains Bp J _ _ hvB hvJ).1).2
  have hloI : (1/2 : ℚ) ≤ I.lo := by
    exact hloA.trans ((endpoint_min_max_endpoints A (boxMin Bp J)).2.2.1.symm ▸ le_max_left _ _)
  have heJ : (BoxExpr.add (.constant 1) (.div c d)).eval E q xs = some J := by
    change (do let X ← some (RatInterval.point 1)
               let Y ← (BoxExpr.div c d).eval E q xs
               pure (X.add Y)) = _
    rw [heQ]; rfl
  have heMin : (BoxExpr.min (.exp (.constant (1/2)))
      (.add (.constant 1) (.div c d))).eval E q xs = some (boxMin Bp J) := by
    change (do let X ← some Bp
               let Y ← (BoxExpr.add (.constant 1) (.div c d)).eval E q xs
               pure (boxMin X Y)) = _
    rw [heJ]; rfl
  have heI : (BoxExpr.max (.exp (.constant (-(1/2))))
      (.min (.exp (.constant (1/2))) (.add (.constant 1) (.div c d)))).eval E q xs = some I := by
    change (do let X ← some A
               let Y ← (BoxExpr.min (.exp (.constant (1/2))) (.add (.constant 1) (.div c d))).eval E q xs
               pure (boxMax X Y)) = _
    rw [heMin]; rfl
  have hwJ : (J.width : ℝ) = Q.width := by
    rw [RatInterval.width_add]
    simp [RatInterval.width, RatInterval.point]
  have hwI : (I.width : ℝ) ≤ (Q.width : ℝ)+2*precisionError q := by
    have herr : 0 ≤ precisionError q := by unfold precisionError; positivity
    have hwQ0 : (0 : ℝ) ≤ Q.width := by exact_mod_cast Q.width_nonneg
    have hwMin : ((boxMin Bp J).width : ℝ) ≤ (Q.width : ℝ)+2*precisionError q := by
      have h : ((boxMin Bp J).width : ℝ) ≤ max (Bp.width : ℝ) (J.width : ℝ) := by
        exact_mod_cast (endpoint_min_max_width Bp J).1
      apply h.trans
      rw [hwJ]
      exact max_le (by linarith) (by linarith)
    have h : (I.width : ℝ) ≤ max (A.width : ℝ) ((boxMin Bp J).width : ℝ) := by
      exact_mod_cast (endpoint_min_max_width A (boxMin Bp J)).2
    exact h.trans (max_le (by linarith) hwMin)
  obtain ⟨L, heL, hvL, hwL⟩ := endpoint_log_enclosure E hE q xs _ I _ heI hvI hloI
  refine ⟨L, ?_, ?_, ?_⟩
  · simpa only [inversionExpression, neg_div] using heL
  · simpa only [inversion, neg_div] using hvL
  · linarith

/-- [The exact cosine kernel has the roadmap magnitude envelope.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: endpoint_exact_kernel_abs
lemma endpoint_exact_kernel_abs (k : ℕ) (x z : Covariate) :
    |projectionKernel k x z| ≤ 2*(k : ℝ) := by
  have hb (j : ℕ) (x : Covariate) : |cosineBasis j x| ≤ Real.sqrt 2 := by
    unfold cosineBasis
    split
    · norm_num
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.sqrt_nonneg 2)
  calc
    _ ≤ ∑ j ∈ Finset.range k, |cosineBasis j x*cosineBasis j z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have h := mul_le_mul (hb j x) (hb j z) (abs_nonneg _) (Real.sqrt_nonneg 2)
      simpa [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using h
    _ = _ := by simp; ring

/-- [Normalization by the number of distinct pairs preserves the kernel magnitude bound.](goal) Under [the stated assumptions](hyp:hn,hW,hV). -/
-- @node: endpoint_exact_statistic_abs
lemma endpoint_exact_statistic_abs (n k : ℕ) (hn : 2 ≤ n)
    (W V : Record → ℝ) (hW : ∀ o, |W o| ≤ 1) (hV : ∀ o, |V o| ≤ 1)
    (o : Fin n → Record) : |projectionStatistic n k W V o| ≤ 2*(k : ℝ) := by
  have hpos : 0 < (n : ℝ)*((n : ℝ)-1) := by
    have h : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    positivity
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 ≠ ij.2)
  have hs : |∑ ij ∈ pairs, projectionKernel k (covariate (o ij.1)) (covariate (o ij.2))*W (o ij.1)*V (o ij.2)| ≤
      (pairs.card : ℝ)*(2*(k : ℝ)) := by
    calc
      _ ≤ ∑ ij ∈ pairs, |projectionKernel k (covariate (o ij.1)) (covariate (o ij.2))*W (o ij.1)*V (o ij.2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ij ∈ pairs, 2*(k : ℝ) := by
        apply Finset.sum_le_sum
        intro ij hij
        rw [abs_mul, abs_mul]
        calc
          _ ≤ (2*(k : ℝ))*1*1 := by
            gcongr
            · exact endpoint_exact_kernel_abs _ _ _
            · exact hW _
            · exact hV _
          _ = _ := by ring
      _ = _ := by simp
  unfold projectionStatistic
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  calc
    _ ≤ ((n : ℝ)*((n : ℝ)-1))⁻¹*((pairs.card : ℝ)*(2*(k : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpos.le)
    _ = _ := by rw [endpoint_pair_card n, ← mul_assoc, inv_mul_cancel₀ hpos.ne']; ring

/-- [The covariance coordinate is bounded by one plus twice its retained rank.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: endpoint_exact_cHat_abs
lemma endpoint_exact_cHat_abs (n k : ℕ) (hn : 2 ≤ n) (o : Fin n → Record) :
    |cHat n k o| ≤ 1+2*(k : ℝ) := by
  have hA (r : Record) : |treatment r| ≤ 1 := by
    simp [treatment]; split <;> norm_num
  have hY (r : Record) : |outcome r| ≤ 1 := by
    simp [outcome]; split <;> norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : |(n : ℝ)⁻¹*∑ i, treatment (o i)*outcome (o i)| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hn0)]
    calc
      _ ≤ (n : ℝ)⁻¹*∑ i, |treatment (o i)*outcome (o i)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (n : ℝ)⁻¹*∑ _i : Fin n, (1 : ℝ) := by
        gcongr with i
        rw [abs_mul]
        simpa using mul_le_mul (hA (o i)) (hY (o i)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ = 1 := by simp [hn0.ne']
  unfold cHat
  rw [sub_eq_add_neg]
  apply (abs_add_le _ _).trans
  rw [abs_neg]
  exact add_le_add hm (endpoint_exact_statistic_abs n k hn _ _ hA hY o)

/-- [The variance radius and its square root have elementary rank-dependent envelopes.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: endpoint_exact_noise_bound
lemma endpoint_exact_noise_bound (n k : ℕ) (hn : 2 ≤ n) :
    varianceRadius n k ≤ 5+2*(k : ℝ) ∧
    Real.sqrt (20*varianceRadius n k) ≤ 10+7*(k : ℝ) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 2 ≤ (n : ℝ)*((n : ℝ)-1) := by nlinarith
  have hv : varianceRadius n k ≤ 5+2*(k : ℝ) := by
    unfold varianceRadius
    have h1 : 10/(n : ℝ) ≤ 5 := (div_le_iff₀ (by linarith)).2 (by linarith)
    have h2 : 4*(k : ℝ)/((n : ℝ)*((n : ℝ)-1)) ≤ 2*(k : ℝ) := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) (show 0 ≤ (n : ℝ)*((n : ℝ)-1)-2 by linarith)]
    linarith
  refine ⟨hv, ?_⟩
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [sq_nonneg (k : ℝ)]

/-- [The exact numerator radius obeys the roadmap magnitude bound.](goal) Under [the stated assumptions](hyp:hn,hk,hab). -/
-- @node: endpoint_exact_cRadius_bound
lemma endpoint_exact_cRadius_bound (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (α β : ℝ) (hab : ExponentDomain α β) :
    0 ≤ 8*(k : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n k) ∧
    8*(k : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n k) ≤ 25*(k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (k : ℝ)^(-(α+β)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith [hab.1, hab.2.2.1])
  refine ⟨by positivity, ?_⟩
  linarith [(endpoint_exact_noise_bound n k hn).2]

/-- [Containment and width turn an exact magnitude bound into endpoint magnitude bounds.](goal) Under [the stated assumptions](hyp:hv,hB). Under [the stated assumptions](hyp:hw). -/
-- @node: endpoint_contains_abs_bounds
lemma endpoint_contains_abs_bounds (I : RatInterval) (v B w : ℝ)
    (hv : I.Contains v) (hB : |v| ≤ B) (hw : (I.width : ℝ) ≤ w) :
    |(I.lo : ℝ)| ≤ B+w ∧ |(I.hi : ℝ)| ≤ B+w := by
  have hwidth : (I.hi : ℝ)-I.lo ≤ w := by simpa [RatInterval.width] using hw
  rw [abs_le] at hB ⊢
  constructor
  · constructor <;> linarith [hv.1, hv.2]
  · rw [abs_le]; constructor <;> linarith [hv.1, hv.2]

/-- [The public endpoint budget controls the full quartic precision product. [the stated conclusion](goal) holds. -/
-- @node: endpoint_precision_quartic_bound
lemma endpoint_precision_quartic_bound (n kC kS : ℕ) :
    (2 : ℝ)^44*((n : ℝ)+1)*((max kC kS : ℕ)+1)^4*
      precisionError (qEnd n kC kS) ≤ 1 := by
  have hn : (n : ℝ)+1 ≤ (2 : ℝ)^(Nat.clog 2 (n+1)) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (n+1)
  have hk : ((max kC kS : ℕ) : ℝ)+1 ≤ (2 : ℝ)^(Nat.clog 2 (max kC kS+1)) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (max kC kS+1)
  have hb : (2 : ℝ)^44*((n : ℝ)+1)*((max kC kS : ℕ)+1)^4 ≤ (2 : ℝ)^qEnd n kC kS := by
    unfold qEnd
    rw [pow_add, pow_add, pow_mul, ← pow_mul (2 : ℝ) 4, Nat.mul_comm 4, pow_mul]
    gcongr
  rw [precisionError, zpow_neg, zpow_natCast]
  exact (mul_le_mul_of_nonneg_right hb (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))

/-- Every coefficient below the quartic budget has a precision product at most one. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:ha). -/
-- @node: endpoint_precision_coefficient_bound
lemma endpoint_precision_coefficient_bound (n kC kS : ℕ) (a : ℝ)
    (ha : a ≤ (2 : ℝ)^44*((n : ℝ)+1)*((max kC kS : ℕ)+1)^4) :
    a*precisionError (qEnd n kC kS) ≤ 1 := by
  exact (mul_le_mul_of_nonneg_right ha (by unfold precisionError; positivity)).trans
    (endpoint_precision_quartic_bound n kC kS)

/-- The endpoint budget pays for coordinate widths, positive log arguments, and final widths. Under the stated assumptions. [The stated hypotheses](hyp:hn) hold, and [the stated conclusion follows](goal). -/
-- @node: endpoint_precision_final_estimates
lemma endpoint_precision_final_estimates (n kC kS : ℕ) (hn : 2 ≤ n) :
    precisionError (qEnd n kC kS) ≤ 1/16 ∧
    300*(max kC kS : ℕ)^2*precisionError (qEnd n kC kS) ≤ 1 ∧
    (2 : ℝ)^37*((max kC kS : ℕ)+1)^3*precisionError (qEnd n kC kS) ≤ 1/(n : ℝ) := by
  let K : ℝ := (max kC kS : ℕ)
  have hK : 0 ≤ K := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hK1 : 1 ≤ K+1 := by linarith
  have hKpow : 1 ≤ (K+1)^4 := one_le_pow₀ hK1
  have hK2 : K^2 ≤ (K+1)^4 := by
    have h : K^2 ≤ (K+1)^2 := by gcongr; linarith
    have h' : (K+1)^2 ≤ (K+1)^4 := by
      exact pow_le_pow_right₀ hK1 (by norm_num)
    exact h.trans h'
  have h16 := endpoint_precision_coefficient_bound n kC kS 16 (by
    change 16 ≤ (2 : ℝ)^44*((n : ℝ)+1)*(K+1)^4
    have h : (2 : ℝ)^44 ≤ (2 : ℝ)^44*((n : ℝ)+1)*(K+1)^4 := by
      calc
        _ = (2 : ℝ)^44*1*1 := by ring
        _ ≤ _ := by gcongr; linarith
    norm_num at h ⊢
    linarith)
  have h300 := endpoint_precision_coefficient_bound n kC kS (300*K^2) (by
    change 300*K^2 ≤ (2 : ℝ)^44*((n : ℝ)+1)*(K+1)^4
    calc
      _ ≤ 300*(K+1)^4 := by gcongr
      _ ≤ _ := by gcongr; norm_num; nlinarith)
  have hfinal := endpoint_precision_coefficient_bound n kC kS ((2 : ℝ)^37*(K+1)^3*n) (by
    change (2 : ℝ)^37*(K+1)^3*n ≤ (2 : ℝ)^44*((n : ℝ)+1)*(K+1)^4
    calc
      _ = (2 : ℝ)^37*(n : ℝ)*(K+1)^3 := by ring
      _ ≤ _ := by
        gcongr <;> norm_num <;> linarith)
  refine ⟨by linarith, h300, ?_⟩
  apply (le_div_iff₀ hn0).2
  simpa only [K, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- [Both actual numerator corners have bounded magnitudes and the roadmap widths.](goal) Under [the stated assumptions](hyp:hn,hkC,hab). Under [the stated assumptions](hyp:hC,hBC,hvC,hvBC,hwC,hwBC). -/
-- @node: endpoint_numerator_corners
lemma endpoint_numerator_corners (E : ArithmeticEngine) (n kC kS : ℕ)
    (hn : 2 ≤ n) (hkC : 1 ≤ kC) (α β : ℝ) (hab : ExponentDomain α β)
    (o : Fin n → Record) (xs : List RatInterval) (C BC : RatInterval)
    (hC : (coordinateExpressions n kC kS o).1.eval E (qEnd n kC kS) xs = some C)
    (hBC : (endpointRadiusExpressions n kC kS).1.eval E (qEnd n kC kS) xs = some BC)
    (hvC : C.Contains (cHat n kC o))
    (hvBC : BC.Contains (8*(kC : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n kC)))
    (hwC : (C.width : ℝ) ≤ 160*(kC : ℝ)^2*precisionError (qEnd n kC kS))
    (hwBC : (BC.width : ℝ) ≤ 34*(max kC kS : ℕ)*precisionError (qEnd n kC kS)) :
    ∃ Cm Cp : RatInterval,
      (BoxExpr.sub (coordinateExpressions n kC kS o).1 (endpointRadiusExpressions n kC kS).1).eval E (qEnd n kC kS) xs = some Cm ∧
      (BoxExpr.add (coordinateExpressions n kC kS o).1 (endpointRadiusExpressions n kC kS).1).eval E (qEnd n kC kS) xs = some Cp ∧
      Cm.Contains (cHat n kC o-(8*(kC : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n kC))) ∧
      Cp.Contains (cHat n kC o+(8*(kC : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n kC))) ∧
      |Cm.lo| ≤ 100*((max kC kS : ℕ)+1) ∧ |Cm.hi| ≤ 100*((max kC kS : ℕ)+1) ∧
      |Cp.lo| ≤ 100*((max kC kS : ℕ)+1) ∧ |Cp.hi| ≤ 100*((max kC kS : ℕ)+1) ∧
      (Cm.width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError (qEnd n kC kS) ∧
      (Cp.width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError (qEnd n kC kS) := by
  let K : ℝ := (max kC kS : ℕ)
  let h := precisionError (qEnd n kC kS)
  have hK1 : 1 ≤ K := by dsimp [K]; exact_mod_cast hkC.trans (le_max_left kC kS)
  have hkK : (kC : ℝ) ≤ K := by dsimp [K]; exact_mod_cast le_max_left kC kS
  have herr : 0 ≤ h := by unfold h precisionError; positivity
  have hw : (C.width : ℝ)+(BC.width : ℝ) ≤ 300*K^2*h := by
    have hk2 : (kC : ℝ)^2 ≤ K^2 := by gcongr
    have hKK : K ≤ K^2 := by nlinarith
    nlinarith only [hwC, hwBC, mul_nonneg herr (show 0 ≤ 300*K^2-160*(kC : ℝ)^2-34*K by nlinarith)]
  have hwm : ((C.sub BC).width : ℝ) ≤ 300*K^2*h := by
    rw [RatInterval.width_sub, Rat.cast_add]; exact hw
  have hwp : ((C.add BC).width : ℝ) ≤ 300*K^2*h := by
    rw [RatInterval.width_add, Rat.cast_add]; exact hw
  have hvM := RatInterval.sub_sound hvC hvBC
  have hvP := RatInterval.add_sound hvC hvBC
  have hcb := endpoint_exact_cHat_abs n kC hn o
  obtain ⟨hb0, hbb⟩ := endpoint_exact_cRadius_bound n kC hn hkC α β hab
  have habm : |cHat n kC o-(8*(kC : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n kC))| ≤ 1+27*K := by
    rw [sub_eq_add_neg]
    apply (abs_add_le _ _).trans
    rw [abs_neg, abs_of_nonneg hb0]
    linarith
  have habp : |cHat n kC o+(8*(kC : ℝ)^(-(α+β))+Real.sqrt (20*varianceRadius n kC))| ≤ 1+27*K := by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg hb0]
    linarith
  have hsmall := (endpoint_precision_final_estimates n kC kS hn).2.1
  have hwM1 : ((C.sub BC).width : ℝ) ≤ 1 := hwm.trans hsmall
  have hwP1 : ((C.add BC).width : ℝ) ≤ 1 := hwp.trans hsmall
  obtain ⟨hml, hmh⟩ := endpoint_contains_abs_bounds _ _ _ 1 hvM habm hwM1
  obtain ⟨hpl, hph⟩ := endpoint_contains_abs_bounds _ _ _ 1 hvP habp hwP1
  have hcast (a : ℚ) (ha : |(a : ℝ)| ≤ 1+27*K+1) : |a| ≤ 100*((max kC kS : ℕ)+1) := by
    have h : |(a : ℝ)| ≤ 100*(K+1) := by linarith
    dsimp [K] at h
    exact_mod_cast h
  refine ⟨C.sub BC, C.add BC, ?_, ?_, hvM, hvP,
    hcast _ hml, hcast _ hmh, hcast _ hpl, hcast _ hph, hwm, hwp⟩
  · change (do let A ← (coordinateExpressions n kC kS o).1.eval E (qEnd n kC kS) xs
               let B ← (endpointRadiusExpressions n kC kS).1.eval E (qEnd n kC kS) xs
               pure (A.sub B)) = _
    rw [hC, hBC]; rfl
  · change (do let A ← (coordinateExpressions n kC kS o).1.eval E (qEnd n kC kS) xs
               let B ← (endpointRadiusExpressions n kC kS).1.eval E (qEnd n kC kS) xs
               pure (A.add B)) = _
    rw [hC, hBC]; rfl

/-- [At the endpoint budget every inversion corner has width at most one over sample size.](goal) Under [the stated assumptions](hyp:hE,hn,hv,hz,hD). Under [the stated assumptions](hyp:hc,hd,hClo,hChi,hwC,hwD). -/
-- @node: endpoint_inversion_budget_contract
lemma endpoint_inversion_budget_contract (E : ArithmeticEngine) (hE : E.Admissible)
    (n kC kS : ℕ) (hn : 2 ≤ n) (xs : List RatInterval)
    (c d : BoxExpr) (C D : RatInterval) (v z : ℝ)
    (hc : c.eval E (qEnd n kC kS) xs = some C) (hd : d.eval E (qEnd n kC kS) xs = some D)
    (hv : C.Contains v) (hz : D.Contains z) (hD : 1/512 ≤ D.lo)
    (hClo : |C.lo| ≤ 100*((max kC kS : ℕ)+1))
    (hChi : |C.hi| ≤ 100*((max kC kS : ℕ)+1))
    (hwC : (C.width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError (qEnd n kC kS))
    (hwD : (D.width : ℝ) ≤ 300*(max kC kS : ℕ)^2*precisionError (qEnd n kC kS)) :
    ∃ L : RatInterval, (inversionExpression c d).eval E (qEnd n kC kS) xs = some L ∧
      L.Contains (inversion v z) ∧ (L.width : ℝ) ≤ 1/(n : ℝ) := by
  obtain ⟨hq, _, hfinal⟩ := endpoint_precision_final_estimates n kC kS hn
  obtain ⟨L, heL, hvL, hwL⟩ := endpoint_inversion_enclosure E hE _ hq xs c d C D v z _
    hc hd hv hz hD (by positivity) hClo hChi
  refine ⟨L, heL, hvL, hwL.trans (le_trans ?_ hfinal)⟩
  let K : ℝ := (max kC kS : ℕ)
  let h := precisionError (qEnd n kC kS)
  have hK : 0 ≤ K := by positivity
  have herr : 0 ≤ h := by unfold h precisionError; positivity
  have hBcast : ((100*((max kC kS : ℕ)+1) : ℚ) : ℝ) = 100*(K+1) := by simp [K]
  rw [hBcast]
  change 2*(512*(C.width : ℝ)+100*(K+1)*512^2*(D.width : ℝ))+6*h ≤ (2 : ℝ)^37*(K+1)^3*h
  calc
    _ ≤ (2*(512*300*K^2+100*(K+1)*512^2*300*K^2)+6)*h := by nlinarith only [hwC, hwD, mul_nonneg (show 0 ≤ 100*(K+1)*512^2 by positivity) (show 0 ≤ 300*K^2*h-(D.width : ℝ) by linarith)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ herr
      have h2 : K^2 ≤ (K+1)^2 := by gcongr; linarith
      have h3 : (K+1)*K^2 ≤ (K+1)^3 := by nlinarith
      have h23 : K^2 ≤ (K+1)^3 := by nlinarith [sq_nonneg K]
      have h13 : 1 ≤ (K+1)^3 := one_le_pow₀ (by linarith)
      norm_num
      nlinarith only [h23, h3, h13]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
