module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.MixtureVariance
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Moments

/-!
Light-cell polynomial second moments and the overlap algebra for equation (5).+-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:L,hu,hq,B,u,t,q,s,v), The independent success count factors the polynomial branch's second moment into
its Poisson second moment and the factorial multiplier's second moment.  This gives [the stated result](goal).-/
-- @node: polynomial_cell_second_moment
lemma polynomial_cell_second_moment (L : Nat) (B u t q s v : Real)
    (hu : 0 < u) (hq : 0 ≤ q) :
    (∫ z, polynomialCellBranch L B u t z ^ 2 ∂cellPoissonLaw u t q s v) =
      (q / u + q ^ 2) * (∫ z : Nat × Nat,
        (1 + (z.2 : Real) / (t * B) * (∑ h ∈ Finset.range (L - 1),
          (chebG L).coeff h * (z.1.descFactorial h : Real) / (t * B) ^ h)) ^ 2 ∂
        (poissonMeasure (Real.toNNReal (t * s))).prod
          (poissonMeasure (Real.toNNReal (t * v)))) := by
  let W : Nat × Nat → Real := fun z =>
    1 + (z.2 : Real) / (t * B) * (∑ h ∈ Finset.range (L - 1),
      (chebG L).coeff h * (z.1.descFactorial h : Real) / (t * B) ^ h)
  change (∫ z : Nat × (Nat × Nat), ((z.1 : Real) / u * W z.2) ^ 2 ∂
    (poissonMeasure (Real.toNNReal (u * q))).prod
      ((poissonMeasure (Real.toNNReal (t * s))).prod
        (poissonMeasure (Real.toNNReal (t * v))))) =
    (q / u + q ^ 2) * _
  simp only [mul_pow]
  rw [integral_prod_mul (fun Z : Nat => ((Z : Real) / u) ^ 2)
    (fun z : Nat × Nat => W z ^ 2)]
  have hm := Causalean.Mathlib.Probability.Poisson.PairSecondMoment.poisson_count_second_moment
    (Real.toNNReal (u * q))
  simp only [Real.coe_toNNReal _ (mul_nonneg hu.le hq)] at hm
  have hz : (∫ Z : Nat, ((Z : Real) / u) ^ 2 ∂
      poissonMeasure (Real.toNNReal (u * q))) = q / u + q ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div, hm]
    field_simp
    ring
  rw [hz]
  simp only [W, mul_pow]

/-- Under the stated inputs and conditions, The light-cell multiplier certificate controls the actual polynomial branch variance,
retaining both the outcome-count fluctuation and its squared mean.  This gives [the stated result](goal). -/
-- @node: light_polynomial_variance_envelope
lemma light_polynomial_variance_envelope :
    ∃ C : Real, 0 < C ∧ ∀ (L : Nat) (B u t q s v : Real),
      4 ≤ L → 0 < B → 0 < u → 0 < t → 0 ≤ q → 0 ≤ s → s ≤ B →
      0 ≤ v → (L : Real) ≤ t * B →
      variance (polynomialCellBranch L B u t) (cellPoissonLaw u t q s v) ≤
        C * ((2 : Real) ^ 24) ^ L * (q / u + q ^ 2) *
          (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := light_multiplier_second_moment
  refine ⟨C, hC, ?_⟩
  intro L B u t q s v hL hB hu ht hq hs hsB hv hD
  let : IsProbabilityMeasure (cellPoissonLaw u t q s v) := by
    unfold cellPoissonLaw
    infer_instance
  calc
    _ ≤ ∫ z, polynomialCellBranch L B u t z ^ 2 ∂cellPoissonLaw u t q s v :=
      variance_le_expectation_sq (hybrid_cell_branches_memLp L B u t q s v).1.aestronglyMeasurable
    _ = _ := polynomial_cell_second_moment L B u t q s v hu hq
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (hbound L B t s v hL hB ht hs hsB hv hD)
        (show 0 ≤ q / u + q ^ 2 by positivity)
      convert hh using 1 <;> first | rfl | ring

/-- [Under the stated inputs and conditions](hyp:hB,ht,hs,hsB,hv,heps,hov,hD,B,t,s,v,eps), Equation (4): light-cell bandwidth and overlap control every mixed monomial in
the polynomial second-moment envelope, including null own-arm cells.  This gives [the stated result](goal).-/
-- @node: light_cell_overlap_monomials
lemma light_cell_overlap_monomials (B t s v eps : Real)
    (hB : 0 < B) (ht : 0 < t) (hs : 0 ≤ s) (hsB : s ≤ B) (hv : 0 ≤ v)
    (heps : 0 < eps) (hov : eps * (s + v) ≤ s) (hD : 1 ≤ t * B) :
    s * v ^ 2 / B ^ 2 ≤ (s + v) / eps ∧
      s * v / (t * B ^ 2) ≤ v ∧
      s ^ 2 * v / (t * B ^ 2) ≤ (s + v) / t ∧
      s ^ 2 * v ^ 2 / B ^ 2 ≤ (s + v) ^ 2 ∧
      s ^ 2 ≤ (s + v) ^ 2 ∧ s + v ≤ B / eps := by
  have hs2 : s ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hs hsB 2
  have hvp : v ≤ s + v := by linarith
  have hp : 0 ≤ s + v := by positivity
  have hvs : eps * v ≤ s := by nlinarith
  have hv2 : eps * v ^ 2 ≤ s * (s + v) := by
    have hh := mul_le_mul hvs hvp hv (by positivity : 0 ≤ s)
    nlinarith
  have htB : B ≤ t * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hD hB.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ (sq_pos_of_pos hB) heps).2
    have hh := mul_le_mul_of_nonneg_left hv2 hs
    have hh' := mul_le_mul_of_nonneg_right hs2 hp
    nlinarith
  · apply (div_le_iff₀ (mul_pos ht (sq_pos_of_pos hB))).2
    exact (mul_le_mul_of_nonneg_right hsB hv).trans
      (by nlinarith [mul_le_mul_of_nonneg_right htB hv])
  · apply (div_le_div_iff₀ (mul_pos ht (sq_pos_of_pos hB)) ht).2
    have hh := mul_le_mul hs2 hvp hv (sq_nonneg B)
    have hh' := mul_le_mul_of_nonneg_left hh ht.le
    nlinarith
  · apply (div_le_iff₀ (sq_pos_of_pos hB)).2
    have hvp2 := pow_le_pow_left₀ hv hvp 2
    have hh := mul_le_mul hs2 hvp2 (sq_nonneg v) (sq_nonneg B)
    nlinarith only [hh]
  · exact pow_le_pow_left₀ hs (by linarith) 2
  · exact (le_div_iff₀ heps).2 (by nlinarith [hov.trans hsB])

/-- [Under the stated inputs and conditions](hyp:hB,hu,ht,hq,hqs,hsB,hv,heps,heps1,hov,hD,B,u,t,q,s,v,eps), Expanding the light-cell envelope gives the mass-over-intensity and squared-bandwidth
terms used in equation (5), without a minimum positive cell mass.  This gives [the stated result](goal).-/
-- @node: light_cell_second_moment_algebra
lemma light_cell_second_moment_algebra (B u t q s v eps : Real)
    (hB : 0 < B) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q) (hqs : q ≤ s)
    (hsB : s ≤ B) (hv : 0 ≤ v) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hov : eps * (s + v) ≤ s) (hD : 1 ≤ t * B) :
    (q / u + q ^ 2) * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) ≤
      3 * (s + v) / (u * eps) + (s + v) / t + 2 * B ^ 2 / eps ^ 2 := by
  have hs : 0 ≤ s := hq.trans hqs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    light_cell_overlap_monomials B t s v eps hB ht hs hsB hv heps hov hD
  have hp : 0 ≤ s + v := by positivity
  have hse : s ≤ (s + v) / eps := by
    apply (le_div_iff₀ heps).2
    nlinarith
  have hsq : (s + v) ^ 2 ≤ B ^ 2 / eps ^ 2 := by
    have hh := pow_le_pow_left₀ hp h6 2
    simpa only [div_pow] using hh
  have hqs2 := pow_le_pow_left₀ hq hqs 2
  calc
    _ ≤ (s / u + s ^ 2) * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) :=
      mul_le_mul_of_nonneg_right
        (add_le_add (div_le_div_of_nonneg_right hqs hu.le) hqs2) (by positivity)
    _ = s / u + (s * v ^ 2 / B ^ 2) / u +
        (s * v / (t * B ^ 2)) / u + s ^ 2 +
        s ^ 2 * v ^ 2 / B ^ 2 + s ^ 2 * v / (t * B ^ 2) := by ring
    _ ≤ (s + v) / eps / u + (s + v) / eps / u +
        (s + v) / eps / u + B ^ 2 / eps ^ 2 +
        B ^ 2 / eps ^ 2 + (s + v) / t := by
      have hvse : v ≤ (s + v) / eps := by
        apply (le_div_iff₀ heps).2
        nlinarith
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (div_le_div_of_nonneg_right hse hu.le)
        (div_le_div_of_nonneg_right h1 hu.le))
        (div_le_div_of_nonneg_right (h2.trans hvse) hu.le))
        (h5.trans hsq)) (h4.trans hsq)) h3
    _ = _ := by ring

/-- Under the stated inputs and conditions, A light polynomial cell has variance controlled by its mass over the outcome and
factorial intensities, plus squared bandwidth over squared overlap.  This gives [the stated result](goal). -/
-- @node: light_polynomial_cell_variance
lemma light_polynomial_cell_variance :
    ∃ C : Real, 0 < C ∧ ∀ (L : Nat) (B u t q s v eps : Real),
      4 ≤ L → 0 < B → 0 < u → 0 < t → 0 ≤ q → q ≤ s → s ≤ B →
      0 ≤ v → 0 < eps → eps ≤ 1 → eps * (s + v) ≤ s → (L : Real) ≤ t * B →
      variance (polynomialCellBranch L B u t) (cellPoissonLaw u t q s v) ≤
        C * ((2 : Real) ^ 24) ^ L *
          ((s + v) / (u * eps) + (s + v) / t + B ^ 2 / eps ^ 2) := by
  obtain ⟨C, hC, hb⟩ := light_polynomial_variance_envelope
  refine ⟨3 * C, by positivity, ?_⟩
  intro L B u t q s v eps hL hB hu ht hq hqs hsB hv heps heps1 hov hD
  have hs := hq.trans hqs
  have hD1 : 1 ≤ t * B := by
    have hLreal : (4 : Real) ≤ L := by exact_mod_cast hL
    linarith
  have ha := light_cell_second_moment_algebra B u t q s v eps
    hB hu ht hq hqs hsB hv heps heps1 hov hD1
  have hF : 0 ≤ C * ((2 : Real) ^ 24) ^ L := by positivity
  calc
    _ ≤ C * ((2 : Real) ^ 24) ^ L * (q / u + q ^ 2) *
        (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2)) :=
      hb L B u t q s v hL hB hu ht hq hs hsB hv hD
    _ = C * ((2 : Real) ^ 24) ^ L *
        ((q / u + q ^ 2) * (1 + v ^ 2 / B ^ 2 + v / (t * B ^ 2))) := by ring
    _ ≤ C * ((2 : Real) ^ 24) ^ L *
        (3 * (s + v) / (u * eps) + (s + v) / t + 2 * B ^ 2 / eps ^ 2) :=
      mul_le_mul_of_nonneg_left ha hF
    _ ≤ _ := by
      have ht0 : 0 ≤ (s + v) / t := by positivity
      have hB0 : 0 ≤ B ^ 2 / eps ^ 2 := by positivity
      have hh : 3 * (s + v) / (u * eps) + (s + v) / t + 2 * B ^ 2 / eps ^ 2 ≤
          3 * ((s + v) / (u * eps) + (s + v) / t + B ^ 2 / eps ^ 2) := by
        calc
          _ = 3 * ((s + v) / (u * eps)) + (s + v) / t +
              2 * (B ^ 2 / eps ^ 2) := by ring
          _ ≤ _ := by linarith
      have hh' := mul_le_mul_of_nonneg_left hh hF
      convert hh' using 1 <;> first | rfl | ring

/-- Under the stated inputs and conditions, Equation (5): summing the actual light-cell polynomial variances keeps the total
light mass in both intensity terms and the cell count in the bandwidth term.  This gives [the stated result](goal). -/
-- @node: light_polynomial_variance_sum
lemma light_polynomial_variance_sum :
    ∃ C : Real, 0 < C ∧ ∀ (L : Nat) (B u t eps : Real),
      4 ≤ L → 0 < B → 0 < u → 0 < t → 0 < eps → eps ≤ 1 →
      (L : Real) ≤ t * B → ∀ {alpha : Type} (J : Finset alpha) (q s v : alpha → Real),
      (∀ j ∈ J, 0 ≤ q j ∧ q j ≤ s j ∧ s j ≤ B ∧ 0 ≤ v j ∧
        eps * (s j + v j) ≤ s j) →
      (∑ j ∈ J, variance (polynomialCellBranch L B u t)
        (cellPoissonLaw u t (q j) (s j) (v j))) ≤
      C * ((2 : Real) ^ 24) ^ L *
        ((J.sum (fun j : alpha => s j + v j)) / (u * eps) +
          (J.sum (fun j : alpha => s j + v j)) / t + (J.card : Real) * B ^ 2 / eps ^ 2) := by
  obtain ⟨C, hC, hb⟩ := light_polynomial_cell_variance
  refine ⟨C, hC, ?_⟩
  intro L B u t eps hL hB hu ht heps heps1 hD alpha J q s v hcell
  calc
    _ ≤ ∑ j ∈ J, C * ((2 : Real) ^ 24) ^ L *
        ((s j + v j) / (u * eps) + (s j + v j) / t + B ^ 2 / eps ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hq, hqs, hsB, hv, hov⟩ := hcell j hj
      exact hb L B u t (q j) (s j) (v j) eps
        hL hB hu ht hq hqs hsB hv heps heps1 hov hD
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div,
        Finset.sum_const, nsmul_eq_mul]

/-- [Under the stated hypotheses](hyp:heps,hcell,hmass), The light-cell mass is at most one and at most the number of light cells times
bandwidth over overlap, as used in equation (5).  This gives [the stated result](goal). -/
-- @node: light_cell_mass_bound
lemma light_cell_mass_bound {alpha : Type} (J : Finset alpha) (s v : alpha → Real)
    (B eps : Real) (heps : 0 < eps)
    (hcell : ∀ j ∈ J, eps * (s j + v j) ≤ s j ∧ s j ≤ B)
    (hmass : (J.sum (fun j : alpha => s j + v j)) ≤ 1) :
    (J.sum (fun j : alpha => s j + v j)) ≤ min 1 ((J.card : Real) * B / eps) := by
  apply le_min hmass
  calc
    _ ≤ ∑ j ∈ J, B / eps := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hov, hsB⟩ := hcell j hj
      apply (le_div_iff₀ heps).2
      nlinarith
    _ = _ := by simp [mul_div_assoc]

end CausalSmith.Stat.AnnotationRarearmFrontier
