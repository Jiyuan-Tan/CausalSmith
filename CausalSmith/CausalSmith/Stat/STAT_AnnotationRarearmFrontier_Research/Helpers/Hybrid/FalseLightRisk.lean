module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.LightCellRisk

/-!
Global polynomial second moments and false-light pilot-weighted risk, implementing
roadmap equations (7), (9), and (10) without a minimum cell mass.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- Under the stated inputs and conditions, The factorial multiplier has a global squared-moment envelope. This gives [the stated conclusion](goal). -/
-- @node: polynomial_multiplier_second_moment
lemma polynomial_multiplier_second_moment :
    ∃ C : Real, 0 < C ∧ ∀ (L : Nat) (B t s v : Real),
      4 ≤ L → 0 < B → 0 < t → 0 ≤ s → 0 ≤ v → (L : Real) ≤ t * B →
      (∫ z : Nat × Nat,
        (1 + (z.2 : Real) / (t * B) * (∑ h ∈ Finset.range (L - 1),
          (chebG L).coeff h * (z.1.descFactorial h : Real) / (t * B) ^ h)) ^ 2 ∂
        (poissonMeasure (Real.toNNReal (t * s))).prod (poissonMeasure (Real.toNNReal (t * v)))) ≤
      C * (((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) *
        (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro L B t s v hL hB ht hs hv hD
  let G : Nat → Real := fun K => ∑ h ∈ Finset.range (L - 1),
    (chebG L).coeff h * (K.descFactorial h : Real) / (t * B) ^ h
  let mu := poissonMeasure (Real.toNNReal (t * s))
  let nu := poissonMeasure (Real.toNNReal (t * v))
  have hG : MemLp G 2 mu := poisson_factorial_polynomial_memLp _ _ _ _
  have hW := Causalean.Mathlib.Probability.Poisson.poisson_natCast_memLp_two
    (Real.toNNReal (t * v))
  have hprod : Integrable (fun z : Nat × Nat => G z.1 ^ 2 *
      ((z.2 : Real) / (t * B)) ^ 2) (mu.prod nu) :=
    hG.integrable_sq.mul_prod (by
      simpa only [div_eq_mul_inv] using (hW.mul_const ((t * B)⁻¹)).integrable_sq)
  have hbound : (∫ z : Nat × Nat, (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2
      ∂mu.prod nu) ≤ 2 + 2 * ((∫ K, G K ^ 2 ∂mu) *
        (∫ W : Nat, ((W : Real) / (t * B)) ^ 2 ∂nu)) := by
    calc
      _ ≤ ∫ z : Nat × Nat, 2 + 2 * (G z.1 ^ 2 * ((z.2 : Real) / (t * B)) ^ 2)
          ∂mu.prod nu := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
          ((integrable_const 2).add (hprod.const_mul 2))
        exact Filter.Eventually.of_forall (fun z => by
          have hh : (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2 ≤
              2 + 2 * ((z.2 : Real) / (t * B) * G z.1) ^ 2 := by
            nlinarith only [sq_nonneg (1 - (z.2 : Real) / (t * B) * G z.1)]
          change (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2 ≤
            2 + 2 * (G z.1 ^ 2 * ((z.2 : Real) / (t * B)) ^ 2)
          calc
            _ ≤ 2 + 2 * ((z.2 : Real) / (t * B) * G z.1) ^ 2 := hh
            _ = _ := by ring)
      _ = _ := by
        rw [integral_add (integrable_const 2) (hprod.const_mul 2), integral_const_mul,
          integral_prod_mul (fun K => G K ^ 2) (fun W : Nat => ((W : Real) / (t * B)) ^ 2)]
        simp
  have hsratio : 0 ≤ s / B := div_nonneg hs hB.le
  have hcert := (chebyshev_factorial_certificate L (by omega)).2.2.2.2.2
    t B (s / B) ht hB hsratio hD
  have hrate : t * (s / B) * B = t * s := by field_simp
  have hGs : (∫ K, G K ^ 2 ∂mu) ≤
      ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L) := by
    have hg := hcert.2
    rw [hrate] at hg
    exact hg.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 392) (by norm_num) L)
      (by positivity))
  have hWmoment : (∫ W : Nat, ((W : Real) / (t * B)) ^ 2 ∂nu) =
      v ^ 2 / B ^ 2 + v / (t * B ^ 2) := by
    have hm := Causalean.Stat.Concentration.Poisson.poisson_descFactorial_mixed
      (Real.toNNReal (t * v)) 1 1
    norm_num [Finset.sum_range_succ,
      Real.toNNReal_of_nonneg (mul_nonneg ht.le hv)] at hm
    simp_rw [div_pow]
    rw [integral_div]
    simp only [nu]
    simp_rw [pow_two]
    simp only [Real.toNNReal_of_nonneg (mul_nonneg ht.le hv)]
    rw [hm]
    field_simp
  have hF : 1 ≤ (((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith))
  have hV : 0 ≤ v ^ 2 / B ^ 2 + v / (t * B ^ 2) := by positivity
  change (∫ z : Nat × Nat, (1 + (z.2 : Real) / (t * B) * G z.1) ^ 2
    ∂mu.prod nu) ≤ _
  rw [hWmoment] at hbound
  calc
    _ ≤ 2 + 2 * ((∫ K, G K ^ 2 ∂mu) * (v ^ 2 / B ^ 2 + v / (t * B ^ 2))) := hbound
    _ ≤ 2 * (((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) := by
      have hh := mul_le_mul_of_nonneg_right hGs hV
      calc
        _ ≤ 2 * (((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) +
            2 * ((((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) * (v ^ 2 / B ^ 2 + v / (t * B ^ 2))) :=
          add_le_add (by linarith only [hF]) (mul_le_mul_of_nonneg_left hh (by norm_num))
        _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:hB,hu,ht,hq,hqs,hsB,hv,heps,heps1,hov,hD,B,u,t,q,s,v,eps), Outside the bandwidth, rescaling the light-cell overlap monomials retains only
cell mass, squared cell mass, and the quadratic continuation factor.  This gives [the stated result](goal).-/
-- @node: false_light_second_moment_algebra
lemma false_light_second_moment_algebra (B u t q s v eps : Real)
    (hB : 0 < B) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q) (hqs : q ≤ s)
    (hsB : B < s) (hv : 0 ≤ v) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hov : eps * (s + v) ≤ s) (hD : 1 ≤ t * B) :
    (q / u + q ^ 2) * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) ≤
      3 * (1 + s / B) ^ 2 * ((s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t) := by
  have hs : 0 < s := hB.trans hsB
  have hDs : 1 ≤ t * s := hD.trans (mul_le_mul_of_nonneg_left hsB.le ht.le)
  obtain ⟨h1, h2, h3, h4, h5, _⟩ :=
    light_cell_overlap_monomials s t s v eps hs ht hs.le le_rfl hv heps hov hDs
  have hp : 0 ≤ s + v := by positivity
  have hse : s ≤ (s + v) / eps := by
    apply (le_div_iff₀ heps).2
    nlinarith
  have hvse : v ≤ (s + v) / eps := by
    apply (le_div_iff₀ heps).2
    nlinarith
  have hlocal : (q / u + q ^ 2) * (1 + v ^ 2 / s ^ 2 + v / (t * s ^ 2)) ≤
      3 * (s + v) / (u * eps) + (s + v) / t + 2 * (s + v) ^ 2 := by
    calc
      _ ≤ (s / u + s ^ 2) * (1 + v ^ 2 / s ^ 2 + v / (t * s ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (add_le_add (div_le_div_of_nonneg_right hqs hu.le)
            (pow_le_pow_left₀ hq hqs 2)) (by positivity)
      _ = s / u + (s * v ^ 2 / s ^ 2) / u +
          (s * v / (t * s ^ 2)) / u + s ^ 2 +
          s ^ 2 * v ^ 2 / s ^ 2 + s ^ 2 * v / (t * s ^ 2) := by ring
      _ ≤ (s + v) / eps / u + (s + v) / eps / u +
          (s + v) / eps / u + (s + v) ^ 2 + (s + v) ^ 2 + (s + v) / t :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (div_le_div_of_nonneg_right hse hu.le)
          (div_le_div_of_nonneg_right h1 hu.le))
          (div_le_div_of_nonneg_right (h2.trans hvse) hu.le)) h5) h4) h3
      _ = _ := by ring
  have hz : 0 ≤ s / B := by positivity
  have hz2 : (s / B) ^ 2 ≤ (1 + s / B) ^ 2 := by nlinarith
  have hbase : 1 ≤ (1 + s / B) ^ 2 := by nlinarith
  have hscale : 1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2) ≤
      (1 + s / B) ^ 2 * (1 + v ^ 2 / s ^ 2 + v / (t * s ^ 2)) := by
    have halg : v ^ 2 / B ^ 2 + v / (t * B ^ 2) =
        (s / B) ^ 2 * (v ^ 2 / s ^ 2 + v / (t * s ^ 2)) := by field_simp
    rw [show 1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2) =
      1 + (v ^ 2 / B ^ 2 + v / (t * B ^ 2)) by ring, halg]
    have hh := mul_le_mul_of_nonneg_right hz2
      (show 0 ≤ v ^ 2 / s ^ 2 + v / (t * s ^ 2) by positivity)
    nlinarith only [hbase, hh]
  calc
    _ ≤ (q / u + q ^ 2) * ((1 + s / B) ^ 2 *
        (1 + v ^ 2 / s ^ 2 + v / (t * s ^ 2))) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (1 + s / B) ^ 2 * ((q / u + q ^ 2) *
        (1 + v ^ 2 / s ^ 2 + v / (t * s ^ 2))) := by ring
    _ ≤ (1 + s / B) ^ 2 *
        (3 * (s + v) / (u * eps) + (s + v) / t + 2 * (s + v) ^ 2) :=
      mul_le_mul_of_nonneg_left hlocal (sq_nonneg _)
    _ ≤ _ := by
      have hh : 3 * (s + v) / (u * eps) + (s + v) / t + 2 * (s + v) ^ 2 ≤
          3 * ((s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t) := by
        have hpT : 0 ≤ (s + v) / t := by positivity
        calc
          _ = 3 * ((s + v) / (u * eps)) + (s + v) / t + 2 * (s + v) ^ 2 := by ring
          _ ≤ _ := by nlinarith only [hpT, sq_nonneg (s + v)]
      calc
        _ ≤ (1 + s / B) ^ 2 *
            (3 * ((s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t)) :=
          mul_le_mul_of_nonneg_left hh (sq_nonneg _)
        _ = _ := by ring

/-- Under the stated inputs and conditions, Equation (7): the heavy-cell polynomial second moment has the full factorial
continuation factor and no extra inverse-overlap factor on its squared mass.  This gives [the stated result](goal). -/
-- @node: false_light_polynomial_second_moment
lemma false_light_polynomial_second_moment :
    ∃ C : Real, 0 < C ∧ ∀ (L : Nat) (B u t q s v eps : Real),
      4 ≤ L → 0 < B → 0 < u → 0 < t → 0 ≤ q → q ≤ s → B < s →
      0 ≤ v → 0 < eps → eps ≤ 1 → eps * (s + v) ≤ s → (L : Real) ≤ t * B →
      (∫ z, polynomialCellBranch L B u t z ^ 2 ∂cellPoissonLaw u t q s v) ≤
        C * ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2) *
          ((s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t) := by
  obtain ⟨C, hC, hb⟩ := polynomial_multiplier_second_moment
  refine ⟨3 * C, by positivity, ?_⟩
  intro L B u t q s v eps hL hB hu ht hq hqs hsB hv heps heps1 hov hD
  have hs := hB.trans hsB
  have hD1 : 1 ≤ t * B := by
    have hLreal : (4 : Real) ≤ L := by exact_mod_cast hL
    linarith
  have ha := false_light_second_moment_algebra B u t q s v eps
    hB hu ht hq hqs hsB hv heps heps1 hov hD1
  rw [polynomial_cell_second_moment L B u t q s v hu hq]
  calc
    _ ≤ (q / u + q ^ 2) * (C * (((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) *
        (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2))) :=
      mul_le_mul_of_nonneg_left (hb L B t s v hL hB ht hs.le hv hD) (by positivity)
    _ = (C * ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) *
        ((q / u + q ^ 2) * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2))) := by ring
    _ ≤ (C * ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L)) *
        (3 * (1 + s / B) ^ 2 * ((s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t)) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- [Equations (7) and (9): the actual false-light selection probability absorbs the
polynomial branch's second moment into the inverse twentieth power of S. ](goal)-/
-- @node: false_light_weighted_polynomial_moment
lemma false_light_weighted_polynomial_moment :
    ∃ C : Real, 0 < C ∧ ∀ (S B u tp t q s v eps : Real),
      Real.exp 4096 ≤ S → 0 < B → 0 < u → 0 < tp → 0 < t →
      0 ≤ q → q ≤ s → B < s → 0 ≤ v → 0 < eps → eps ≤ 1 →
      eps * (s + v) ≤ s →
      (Nat.floor (Real.log S / 1024) : Real) ≤ t * B →
      (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B →
      let L := Nat.floor (Real.log S / 1024)
      let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4)))
      pi * (∫ z, polynomialCellBranch L B u t z ^ 2 ∂cellPoissonLaw u t q s v) ≤
        C * (S ^ 20)⁻¹ * ((s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t) := by
  obtain ⟨C, hC, hb⟩ := false_light_polynomial_second_moment
  refine ⟨C, hC, ?_⟩
  intro S B u tp t q s v eps hS hB hu htp ht hq hqs hsB hv heps heps1 hov hD hscale
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4)))
  let M := (s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t
  have hcal := hybrid_degree_calibration S hS
  have hs : 0 < s := hB.trans hsB
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpi : 0 ≤ pi := measureReal_nonneg
  have htail := pilot_false_light_tail tp B s htp hB hsB
  have hm := hb L B u t q s v eps hcal.1 hB hu ht hq hqs hsB hv heps heps1 hov hD
  have habs := (false_light_absorption L tp B s hcal.1 htp hB hsB hscale).trans hcal.2.2.2
  calc
    _ ≤ pi * (C * ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2) * M) :=
      mul_le_mul_of_nonneg_left hm hpi
    _ ≤ Real.exp (-tp * s / 4) *
        (C * ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2) * M) :=
      mul_le_mul_of_nonneg_right htail (by positivity)
    _ = (C * M) * (Real.exp (-tp * s / 4) *
        ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2)) := by ring
    _ ≤ (C * M) * (S ^ 20)⁻¹ :=
      mul_le_mul_of_nonneg_left habs (mul_nonneg hC.le hM)
    _ = _ := by ring

/-- Under the stated inputs and conditions, Equation (10): summing false-light polynomial second moments uses only the total
mass bound, retaining the outcome and factorial intensity terms.  This gives [the stated result](goal). -/
-- @node: false_light_weighted_moment_sum
lemma false_light_weighted_moment_sum :
    ∃ C : Real, 0 < C ∧ ∀ (S B u tp t eps : Real),
      Real.exp 4096 ≤ S → 0 < B → 0 < u → 0 < tp → 0 < t → 0 < eps → eps ≤ 1 →
      (Nat.floor (Real.log S / 1024) : Real) ≤ t * B →
      (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B →
      ∀ {alpha : Type} (J : Finset alpha) (q s v : alpha → Real),
      (∀ j ∈ J, 0 ≤ q j ∧ q j ≤ s j ∧ B < s j ∧ 0 ≤ v j ∧ eps * (s j + v j) ≤ s j) →
      (J.sum (fun j => s j + v j)) ≤ 1 →
      (∑ j ∈ J, (poissonMeasure (Real.toNNReal (tp * s j))).real
        (Set.Iic (Nat.floor (tp * B / 4))) *
        (∫ z, polynomialCellBranch (Nat.floor (Real.log S / 1024)) B u t z ^ 2
          ∂cellPoissonLaw u t (q j) (s j) (v j))) ≤
        C * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) := by
  obtain ⟨C, hC, hb⟩ := false_light_weighted_polynomial_moment
  refine ⟨C, hC, ?_⟩
  intro S B u tp t eps hS hB hu htp ht heps heps1 hD hscale alpha J q s v hcell hmass
  have hp (j) (hj : j ∈ J) : 0 ≤ s j + v j := by
    obtain ⟨hq, hqs, _, hv, _⟩ := hcell j hj
    linarith
  have hp1 (j) (hj : j ∈ J) : s j + v j ≤ 1 := by
    exact (Finset.single_le_sum (fun j hj => hp j hj) hj).trans hmass
  have hsq : (J.sum (fun j => (s j + v j) ^ 2)) ≤ 1 := by
    calc
      _ ≤ J.sum (fun j => s j + v j) := by
        apply Finset.sum_le_sum
        intro j hj
        nlinarith only [hp j hj, hp1 j hj]
      _ ≤ 1 := hmass
  calc
    _ ≤ ∑ j ∈ J, C * (S ^ 20)⁻¹ *
        ((s j + v j) / (u * eps) + (s j + v j) ^ 2 + (s j + v j) / t) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hq, hqs, hsB, hv, hov⟩ := hcell j hj
      exact hb S B u tp t (q j) (s j) (v j) eps
        hS hB hu htp ht hq hqs hsB hv heps heps1 hov hD hscale
    _ = C * (S ^ 20)⁻¹ *
        ((J.sum (fun j => s j + v j)) / (u * eps) +
          (J.sum (fun j => (s j + v j) ^ 2)) + (J.sum (fun j => s j + v j)) / t) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add
        (div_le_div_of_nonneg_right hmass (by positivity)) hsq)
        (div_le_div_of_nonneg_right hmass ht.le)

/-- [Under the stated inputs and conditions](hyp:hS,htp,hB,hsB,hscale,S,tp,B,s), The unweighted false-light pilot probability obeys the same public-scale tail
bound, since the absorbed factorial continuation factor is at least one.  This gives [the stated result](goal).-/
-- @node: false_light_pilot_public_scale
lemma false_light_pilot_public_scale (S tp B s : Real)
    (hS : Real.exp 4096 ≤ S) (htp : 0 < tp) (hB : 0 < B) (hsB : B < s)
    (hscale : (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B) :
    (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4))) ≤
      (S ^ 20)⁻¹ := by
  let L := Nat.floor (Real.log S / 1024)
  have hcal := hybrid_degree_calibration S hS
  have hs : 0 < s := hB.trans hsB
  have hF : 1 ≤ ((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (le_add_of_nonneg_right (div_nonneg hs.le hB.le)))
  calc
    _ ≤ Real.exp (-tp * s / 4) := pilot_false_light_tail tp B s htp hB hsB
    _ ≤ Real.exp (-tp * s / 4) *
        (((2 : Real) ^ 24) ^ L * (1 + s / B) ^ (2 * L + 2)) :=
      le_mul_of_one_le_right (Real.exp_nonneg _) hF
    _ = Real.exp (-tp * s / 4) * ((2 : Real) ^ 24) ^ L *
        (1 + s / B) ^ (2 * L + 2) := by ring
    _ ≤ Real.exp (-200000 * (L : Real)) :=
      false_light_absorption L tp B s hcal.1 htp hB hsB hscale
    _ ≤ (S ^ 20)⁻¹ := hcal.2.2.2

/-- [Under the stated inputs and conditions](hyp:L,hL,hB,hu,ht,hs,hv,hmu,hpi,B,u,t,s,v,mu,pi), On a heavy cell the mixture separation is bounded by the pilot-weighted polynomial
second moment and squared mass, using square integrability rather than branch independence.  This gives [the stated result](goal).-/
-- @node: false_light_between_branch_moment
lemma false_light_between_branch_moment (L : Nat) (B u t s v mu pi : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (hu : 0 < u) (ht : 0 < t)
    (hs : 0 < s) (hv : 0 ≤ v) (hmu : mu ∈ Set.Icc 0 1) (hpi : pi ∈ Set.Icc 0 1) :
    pi * (1 - pi) *
      ((∫ z, polynomialCellBranch L B u t z ∂cellPoissonLaw u t (s * mu) s v) -
        ∫ z, inverseCellBranch u z ∂cellPoissonLaw u t (s * mu) s v) ^ 2 ≤
      2 * pi * (∫ z, polynomialCellBranch L B u t z ^ 2 ∂cellPoissonLaw u t (s * mu) s v) +
        2 * pi * (s + v) ^ 2 := by
  let nu := cellPoissonLaw u t (s * mu) s v
  let : IsProbabilityMeasure nu := by unfold nu cellPoissonLaw; infer_instance
  let mp := ∫ z, polynomialCellBranch L B u t z ∂nu
  let mh := ∫ z, inverseCellBranch u z ∂nu
  have hp := (hybrid_cell_branches_memLp L B u t (s * mu) s v).1
  have hvar := variance_nonneg (polynomialCellBranch L B u t) nu
  rw [variance_eq_sub hp] at hvar
  have hp2 : mp ^ 2 ≤ ∫ z, polynomialCellBranch L B u t z ^ 2 ∂nu := by
    change 0 ≤ (∫ z, polynomialCellBranch L B u t z ^ 2 ∂nu) - mp ^ 2 at hvar
    exact sub_nonneg.mp hvar
  have hh := (hybrid_branch_means L B u t s v mu hL hB hu ht hs hv hmu).2
  have hexp : Real.exp (-t * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hmh : mh ∈ Set.Icc 0 (s + v) := by
    dsimp [mh, nu]
    rw [hh]
    have hvm : 0 ≤ v * mu := mul_nonneg hv hmu.1
    have hsm : 0 ≤ s * mu := mul_nonneg hs.le hmu.1
    have hprod := mul_le_of_le_one_right hvm hexp
    constructor
    · nlinarith only [hprod, hsm]
    · have hupper := mul_le_of_le_one_right (show 0 ≤ s + v by positivity) hmu.2
      nlinarith only [hupper, mul_nonneg hvm (Real.exp_nonneg (-t * s))]
  have hmh2 : mh ^ 2 ≤ (s + v) ^ 2 := pow_le_pow_left₀ hmh.1 hmh.2 2
  calc
    _ ≤ pi * (mp - mh) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_of_le_one_right hpi.1 (by linarith [hpi.1])
    _ ≤ pi * (2 * mp ^ 2 + 2 * mh ^ 2) :=
      mul_le_mul_of_nonneg_left
        (by nlinarith only [sq_nonneg (mp + mh)]) hpi.1
    _ ≤ pi * (2 * (∫ z, polynomialCellBranch L B u t z ^ 2 ∂nu) + 2 * (s + v) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hp2, hmh2]) hpi.1
    _ = _ := by ring

/-- [The heavy-cell contribution to the between-branch mixture variance is absorbed
by the same public-scale bound as its falsely selected polynomial second moment. ](goal)-/
-- @node: false_light_between_branch_public_scale
lemma false_light_between_branch_public_scale :
    ∃ C : Real, 0 < C ∧ ∀ (S B u tp t s v mu eps : Real),
      Real.exp 4096 ≤ S → 0 < B → 0 < u → 0 < tp → 0 < t → B < s →
      0 ≤ v → mu ∈ Set.Icc 0 1 → 0 < eps → eps ≤ 1 → eps * (s + v) ≤ s →
      (Nat.floor (Real.log S / 1024) : Real) ≤ t * B →
      (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B →
      let L := Nat.floor (Real.log S / 1024)
      let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4)))
      let nu := cellPoissonLaw u t (s * mu) s v
      pi * (1 - pi) *
        ((∫ z, polynomialCellBranch L B u t z ∂nu) - ∫ z, inverseCellBranch u z ∂nu) ^ 2 ≤
        C * (S ^ 20)⁻¹ * ((s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t) := by
  obtain ⟨C, hC, hb⟩ := false_light_weighted_polynomial_moment
  refine ⟨2 * C + 2, by positivity, ?_⟩
  intro S B u tp t s v mu eps hS hB hu htp ht hsB hv hmu heps heps1 hov hD hscale
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let pi := (poissonMeasure (Real.toNNReal (tp * s))).real (Set.Iic (Nat.floor (tp * B / 4)))
  let nu := cellPoissonLaw u t (s * mu) s v
  let M := (s + v) / (u * eps) + (s + v) ^ 2 + (s + v) / t
  have hs : 0 < s := hB.trans hsB
  have hp : 0 ≤ s + v := by positivity
  have hq : 0 ≤ s * mu := mul_nonneg hs.le hmu.1
  have hqs : s * mu ≤ s := mul_le_of_le_one_right hs.le hmu.2
  have hpi : pi ∈ Set.Icc 0 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hm := hb S B u tp t (s * mu) s v eps
    hS hB hu htp ht hq hqs hsB hv heps heps1 hov hD hscale
  have htail := false_light_pilot_public_scale S tp B s hS htp hB hsB hscale
  have hp2 : (s + v) ^ 2 ≤ M := by
    have hU : 0 ≤ (s + v) / (u * eps) := by positivity
    have hT : 0 ≤ (s + v) / t := by positivity
    dsimp [M]
    linarith
  have hcal := hybrid_degree_calibration S hS
  calc
    _ ≤ 2 * pi * (∫ z, polynomialCellBranch L B u t z ^ 2 ∂nu) + 2 * pi * (s + v) ^ 2 :=
      false_light_between_branch_moment L B u t s v mu pi
        (by have := hcal.1; omega) hB hu ht hs hv hmu hpi
    _ = 2 * (pi * (∫ z, polynomialCellBranch L B u t z ^ 2 ∂nu)) +
        2 * (pi * (s + v) ^ 2) := by ring
    _ ≤ 2 * (C * (S ^ 20)⁻¹ * M) + 2 * ((S ^ 20)⁻¹ * (s + v) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htail (sq_nonneg _)) (by norm_num))
    _ ≤ 2 * (C * (S ^ 20)⁻¹ * M) + 2 * ((S ^ 20)⁻¹ * M) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp2 (by positivity)) (by norm_num)
    _ = _ := by ring

/-- Under the stated inputs and conditions, The falsely selected polynomial variances are bounded by the already summed
second moments in equation (10).  This gives [the stated result](goal). -/
-- @node: false_light_weighted_variance_sum
lemma false_light_weighted_variance_sum :
    ∃ C : Real, 0 < C ∧ ∀ (S B u tp t eps : Real),
      Real.exp 4096 ≤ S → 0 < B → 0 < u → 0 < tp → 0 < t → 0 < eps → eps ≤ 1 →
      (Nat.floor (Real.log S / 1024) : Real) ≤ t * B →
      (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B →
      ∀ {alpha : Type} (J : Finset alpha) (q s v : alpha → Real),
      (∀ j ∈ J, 0 ≤ q j ∧ q j ≤ s j ∧ B < s j ∧ 0 ≤ v j ∧ eps * (s j + v j) ≤ s j) →
      (J.sum (fun j => s j + v j)) ≤ 1 →
      (∑ j ∈ J, (poissonMeasure (Real.toNNReal (tp * s j))).real
        (Set.Iic (Nat.floor (tp * B / 4))) *
        variance (polynomialCellBranch (Nat.floor (Real.log S / 1024)) B u t)
          (cellPoissonLaw u t (q j) (s j) (v j))) ≤
        C * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) := by
  obtain ⟨C, hC, hb⟩ := false_light_weighted_moment_sum
  refine ⟨C, hC, ?_⟩
  intro S B u tp t eps hS hB hu htp ht heps heps1 hD hscale alpha J q s v hcell hmass
  calc
    _ ≤ ∑ j ∈ J, (poissonMeasure (Real.toNNReal (tp * s j))).real
        (Set.Iic (Nat.floor (tp * B / 4))) *
        (∫ z, polynomialCellBranch (Nat.floor (Real.log S / 1024)) B u t z ^ 2
          ∂cellPoissonLaw u t (q j) (s j) (v j)) := by
      apply Finset.sum_le_sum
      intro j hj
      let : IsProbabilityMeasure (cellPoissonLaw u t (q j) (s j) (v j)) := by
        unfold cellPoissonLaw
        infer_instance
      exact mul_le_mul_of_nonneg_left
        (variance_le_expectation_sq
          (hybrid_cell_branches_memLp _ B u t (q j) (s j) (v j)).1.aestronglyMeasurable)
        measureReal_nonneg
    _ ≤ _ := hb S B u tp t eps hS hB hu htp ht heps heps1 hD hscale
      J q s v hcell hmass

/-- Under the stated inputs and conditions, The heavy-cell part of equation (13) sums to a universal pilot-tail remainder,
without any independence assumption between the polynomial and inverse branches.  This gives [the stated result](goal). -/
-- @node: false_light_between_branch_sum
lemma false_light_between_branch_sum :
    ∃ C : Real, 0 < C ∧ ∀ (S B u tp t eps : Real),
      Real.exp 4096 ≤ S → 0 < B → 0 < u → 0 < tp → 0 < t → 0 < eps → eps ≤ 1 →
      (Nat.floor (Real.log S / 1024) : Real) ≤ t * B →
      (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B →
      ∀ {alpha : Type} (J : Finset alpha) (s v mu : alpha → Real),
      (∀ j ∈ J, B < s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
        eps * (s j + v j) ≤ s j) →
      (J.sum (fun j => s j + v j)) ≤ 1 →
      let L := Nat.floor (Real.log S / 1024)
      let pi := fun j => (poissonMeasure (Real.toNNReal (tp * s j))).real
        (Set.Iic (Nat.floor (tp * B / 4)))
      let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
      (∑ j ∈ J, pi j * (1 - pi j) *
        ((∫ z, polynomialCellBranch L B u t z ∂nu j) -
          ∫ z, inverseCellBranch u z ∂nu j) ^ 2) ≤
        C * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) := by
  obtain ⟨C, hC, hb⟩ := false_light_between_branch_public_scale
  refine ⟨C, hC, ?_⟩
  intro S B u tp t eps hS hB hu htp ht heps heps1 hD hscale alpha J s v mu hcell hmass
  dsimp only
  have hp (j) (hj : j ∈ J) : 0 ≤ s j + v j := by
    obtain ⟨hsB, hv, _, _⟩ := hcell j hj
    linarith
  have hp1 (j) (hj : j ∈ J) : s j + v j ≤ 1 :=
    (Finset.single_le_sum (fun j hj => hp j hj) hj).trans hmass
  have hsq : (J.sum (fun j => (s j + v j) ^ 2)) ≤ 1 := by
    calc
      _ ≤ J.sum (fun j => s j + v j) := by
        apply Finset.sum_le_sum
        intro j hj
        nlinarith only [hp j hj, hp1 j hj]
      _ ≤ 1 := hmass
  calc
    _ ≤ ∑ j ∈ J, C * (S ^ 20)⁻¹ *
        ((s j + v j) / (u * eps) + (s j + v j) ^ 2 + (s j + v j) / t) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hsB, hv, hmu, hov⟩ := hcell j hj
      exact hb S B u tp t (s j) (v j) (mu j) eps
        hS hB hu htp ht hsB hv hmu heps heps1 hov hD hscale
    _ = C * (S ^ 20)⁻¹ *
        ((J.sum (fun j => s j + v j)) / (u * eps) +
          (J.sum (fun j => (s j + v j) ^ 2)) + (J.sum (fun j => s j + v j)) / t) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add
        (div_le_div_of_nonneg_right hmass (by positivity)) hsq)
        (div_le_div_of_nonneg_right hmass ht.le)


/-- Under the stated inputs and conditions, Equation (13), summed over heavy cells: the actual pilot-selected variances
retain the inverse-count variance sum and absorb both false-light contributions.  This gives [the stated result](goal). -/
-- @node: heavy_hybrid_variance_sum
lemma heavy_hybrid_variance_sum :
    ∃ C : Real, 0 < C ∧ ∀ (S B u tp t eps : Real),
      Real.exp 4096 ≤ S → 0 < B → 0 < u → 0 < tp → 0 < t → 0 < eps → eps ≤ 1 →
      (Nat.floor (Real.log S / 1024) : Real) ≤ t * B →
      (2 : Real) ^ 20 * Nat.floor (Real.log S / 1024) ≤ tp * B →
      ∀ {alpha : Type} (J : Finset alpha) (s v mu : alpha → Real),
      (∀ j ∈ J, B < s j ∧ 0 ≤ v j ∧ mu j ∈ Set.Icc 0 1 ∧
        eps * (s j + v j) ≤ s j) →
      (J.sum (fun j => s j + v j)) ≤ 1 →
      let L := Nat.floor (Real.log S / 1024)
      let k0 := Nat.floor (tp * B / 4)
      let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
      (∑ j ∈ J, variance (fun z : Nat × (Nat × Nat × Nat) =>
        hybridCellValue L B k0 u t z.2.1 z.1 z.2.2.1 z.2.2.2)
        ((poissonMeasure (Real.toNNReal (tp * s j))).prod (nu j))) ≤
        (∑ j ∈ J, variance (inverseCellBranch u) (nu j)) +
          C * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) := by
  obtain ⟨CP, hCP, hpol⟩ := false_light_weighted_variance_sum
  obtain ⟨CB, hCB, hbetween⟩ := false_light_between_branch_sum
  refine ⟨CP + CB, by positivity, ?_⟩
  intro S B u tp t eps hS hB hu htp ht heps heps1 hD hscale alpha J s v mu hcell hmass
  dsimp only
  let L := Nat.floor (Real.log S / 1024)
  let k0 := Nat.floor (tp * B / 4)
  let nu := fun j => cellPoissonLaw u t (s j * mu j) (s j) (v j)
  let pi := fun j => (poissonMeasure (Real.toNNReal (tp * s j))).real (Set.Iic k0)
  have hq (j) (hj : j ∈ J) :
      0 ≤ s j * mu j ∧ s j * mu j ≤ s j ∧ B < s j ∧ 0 ≤ v j ∧
        eps * (s j + v j) ≤ s j := by
    obtain ⟨hsB, hv, hmu, hov⟩ := hcell j hj
    have hs := (hB.trans hsB).le
    exact ⟨mul_nonneg hs hmu.1, mul_le_of_le_one_right hs hmu.2, hsB, hv, hov⟩
  have hp := hpol S B u tp t eps hS hB hu htp ht heps heps1 hD hscale
    J (fun j => s j * mu j) s v hq hmass
  have hb := hbetween S B u tp t eps hS hB hu htp ht heps heps1 hD hscale
    J s v mu hcell hmass
  calc
    _ ≤ ∑ j ∈ J, (variance (inverseCellBranch u) (nu j) +
        pi j * variance (polynomialCellBranch L B u t) (nu j) +
        pi j * (1 - pi j) *
          ((∫ z, polynomialCellBranch L B u t z ∂nu j) -
            ∫ z, inverseCellBranch u z ∂nu j) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [hybrid_pilot_cell_variance]
      have hheavy : (1 - pi j) * variance (inverseCellBranch u) (nu j) ≤
          variance (inverseCellBranch u) (nu j) :=
        mul_le_of_le_one_left (variance_nonneg _ _) (by
          have hh : 0 ≤ pi j := measureReal_nonneg
          linarith)
      change pi j * _ + (1 - pi j) * _ + _ ≤ _
      linarith only [hheavy]
    _ = (∑ j ∈ J, variance (inverseCellBranch u) (nu j)) +
        (∑ j ∈ J, pi j * variance (polynomialCellBranch L B u t) (nu j)) +
        (∑ j ∈ J, pi j * (1 - pi j) *
          ((∫ z, polynomialCellBranch L B u t z ∂nu j) -
            ∫ z, inverseCellBranch u z ∂nu j) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (∑ j ∈ J, variance (inverseCellBranch u) (nu j)) +
        CP * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) +
        CB * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) :=
      add_le_add (add_le_add le_rfl hp) hb
    _ = _ := by ring

end CausalSmith.Stat.AnnotationRarearmFrontier
