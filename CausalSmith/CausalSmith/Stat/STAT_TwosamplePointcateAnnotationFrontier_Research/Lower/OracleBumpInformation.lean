module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationMoments
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.OracleBump

/-! # Information in the oracle bump alternatives
The treated outcome cells alone change. Their densities stay bounded away from
zero, and the bump's support has volume equal to its side raised to dimension.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Oracle bump likelihoods equal one in control cells and have a signed perturbation in treated cells.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input hb](hyp:hb), [the specified input hbsmall](hyp:hbsmall), [the specified input x](hyp:x), [the specified input s](hyp:s), [the oracle bump likelihood conclusion](goal) holds. -/
lemma oracle_bump_likelihood (d : ℕ) (h b : ℝ) (theta : Bool)
    (hb : 0 ≤ b) (hbsmall : b ≤ 1/8) (x : Cov d) (s : Bool × Bool) :
    labelLikelihood (oracleBumpPrimitive d h b theta) x s =
      if s.1 then 1+2*thetaSign s.2*thetaSign theta*b*macroBump h x else 1 := by
  obtain ⟨he, h0, h1, hband⟩ := oracleBumpPrimitive_margins d h b theta hb hbsmall
  have hm := macroBump_mem h x
  have hp : 0 ≤ 1/2+b*macroBump h x := by nlinarith [hm.1, hm.2]
  have hm' : 0 ≤ 1/2-b*macroBump h x := by nlinarith [hm.1, hm.2]
  rcases s with ⟨A,Y⟩
  cases A <;> cases Y <;> cases theta <;>
    simp [labelLikelihood, he, h0, h1, bern, thetaSign] <;>
    norm_num only [ENNReal.toReal_ofReal, invOf_eq_inv, inv_nonneg, sub_nonneg, one_div] <;>
    rw [ENNReal.toReal_ofReal (by nlinarith only [hp, hm'])] <;> ring

/-- Each oracle bump likelihood lies between one half and two.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the specified input hb](hyp:hb), [the specified input hbsmall](hyp:hbsmall), [the specified input z](hyp:z), [the oracle bump likelihood bounds conclusion](goal) holds. -/
lemma oracle_bump_likelihood_bounds (d : ℕ) (h b : ℝ) (theta : Bool)
    (hb : 0 ≤ b) (hbsmall : b ≤ 1/8) (z : Cov d × (Bool × Bool)) :
    1/2 ≤ labelLikelihood (oracleBumpPrimitive d h b theta) z.1 z.2 ∧
      labelLikelihood (oracleBumpPrimitive d h b theta) z.1 z.2 ≤ 2 := by
  rw [oracle_bump_likelihood d h b theta hb hbsmall]
  have hm := macroBump_mem h z.1
  rcases z with ⟨x,A,Y⟩
  cases A <;> cases Y <;> cases theta <;> norm_num [thetaSign] <;>
    constructor <;> nlinarith [hm.1, hm.2]

/-- A density floor removes the square-root denominator in the elementary Hellinger identity.  Given [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the oracle sqrt difference le conclusion](goal) holds. -/
lemma oracle_sqrt_difference_le (a b : ℝ) (ha : 1/2 ≤ a) (hb : 1/2 ≤ b) :
    (Real.sqrt a-Real.sqrt b)^2 ≤ (a-b)^2 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hsa := Real.sq_sqrt ha0
  have hsb := Real.sq_sqrt hb0
  have hsum : 1 ≤ (Real.sqrt a+Real.sqrt b)^2 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have hid : (a-b)^2 = (Real.sqrt a-Real.sqrt b)^2 * (Real.sqrt a+Real.sqrt b)^2 := by
    rw [show (Real.sqrt a-Real.sqrt b)^2 * (Real.sqrt a+Real.sqrt b)^2 =
      ((Real.sqrt a)^2-(Real.sqrt b)^2)^2 by ring, hsa, hsb]
  rw [hid]
  exact le_mul_of_one_le_right (sq_nonneg _) hsum

/-- The centered localization box has its Euclidean product volume.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the oracle loc cube volume conclusion](goal) holds. -/
lemma oracle_locCube_volume (d : ℕ) (h : ℝ) (hh : 0 < h) :
    volume (locCube d h) = ENNReal.ofReal (h^d) := by
  have heq : locCube d h = WithLp.ofLp ⁻¹'
      Set.pi Set.univ (fun _ : Fin d => Icc (1/2-h/2) (1/2+h/2)) := by
    ext x
    simp only [locCube, mem_setOf_eq, mem_preimage, mem_pi, mem_univ, forall_const]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    ((MeasurableSet.univ_pi (fun _ : Fin d => measurableSet_Icc)).nullMeasurableSet),
    volume_pi_pi]
  simp only [Real.volume_Icc, show (1/2+h/2)-(1/2-h/2) = h by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hh.le]

/-- Squared bump energy is at most its support volume under the uniform design.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh1](hyp:hh1), [the oracle bump square energy conclusion](goal) holds. -/
lemma oracle_bump_square_energy (d : ℕ) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫ x : Cov d, (macroBump h x)^2 ∂uniformLaw d) ≤ h^d := by
  letI := uniformLaw_probability d
  have hi : Integrable (fun x : Cov d => (macroBump h x)^2) (uniformLaw d) := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hm := macroBump_mem h x
    nlinarith [hm.1, hm.2]
  have hsub : locCube d h ⊆ cube d := by
    intro x hx i
    constructor <;> linarith [(hx i).1, (hx i).2]
  calc
    _ ≤ ∫ x : Cov d, (locCube d h).indicator (fun _ => (1:ℝ)) x ∂uniformLaw d := by
      apply integral_mono hi ((integrable_const (1:ℝ)).indicator (isClosed_locCube d h).measurableSet)
      intro x
      by_cases hx : x ∈ locCube d h
      · rw [indicator_of_mem hx]
        have hm := macroBump_mem h x
        nlinarith [hm.1, hm.2]
      · simp [indicator_of_notMem hx, macroBump_zero_outside h hh x hx]
    _ = h^d := by
      rw [integral_indicator (isClosed_locCube d h).measurableSet, integral_const]
      simp only [smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ]
      rw [uniformLaw, Measure.restrict_apply (isClosed_locCube d h).measurableSet,
        inter_eq_left.mpr hsub, oracle_locCube_volume d h hh,
        ENNReal.toReal_ofReal (pow_nonneg hh.le _)]

/-- The one-record Hellinger cost of the two oracle alternatives is of bump-squared times volume order.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input b](hyp:b), [the specified input hh](hyp:hh), [the specified input hh1](hyp:hh1), [the specified input hb](hyp:hb), [the specified input hbsmall](hyp:hbsmall), [the oracle bump hellinger bound conclusion](goal) holds. -/
lemma oracle_bump_hellinger_bound (d : ℕ) (h b : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hb : 0 ≤ b) (hbsmall : b ≤ 1/8) :
    hellingerSq (obsLaw (oracleBumpPrimitive d h b false))
      (obsLaw (oracleBumpPrimitive d h b true)) ≤ 16*b^2*h^d := by
  let P0 := oracleBumpPrimitive d h b false
  let P1 := oracleBumpPrimitive d h b true
  let f := fun z : Cov d × (Bool × Bool) => labelLikelihood P0 z.1 z.2
  let g := fun z : Cov d × (Bool × Bool) => labelLikelihood P1 z.1 z.2
  letI := uniformLaw_probability d
  letI := bern_probability (1/2) (by norm_num)
  letI : IsProbabilityMeasure fairObserved := by unfold fairObserved; infer_instance
  letI := obsLaw_probability P0
  letI := obsLaw_probability P1
  have hf : Measurable f := measurable_labelLikelihood P0
  have hg : Measurable g := measurable_labelLikelihood P1
  have hfbound (z) := oracle_bump_likelihood_bounds d h b false hb hbsmall z
  have hgbound (z) := oracle_bump_likelihood_bounds d h b true hb hbsmall z
  change hellingerSq (obsLaw P0) (obsLaw P1) ≤ _
  have hd0 : obsLaw P0 = ((uniformLaw d).prod fairObserved).withDensity
      (fun z => ENNReal.ofReal (f z)) := independent_obsLaw_density d _ _ _ _ _ _
  have hd1 : obsLaw P1 = ((uniformLaw d).prod fairObserved).withDensity
      (fun z => ENNReal.ofReal (g z)) := independent_obsLaw_density d _ _ _ _ _ _
  rw [hellingerSq_real_density (obsLaw P0) (obsLaw P1) ((uniformLaw d).prod fairObserved) f g hf hg
    (fun z => by dsimp [f, P0]; linarith [(hfbound z).1])
    (fun z => by dsimp [g, P1]; linarith [(hgbound z).1])
    hd0 hd1]
  unfold Causalean.Stat.hellingerSqDensity
  have hpoint (z : Cov d × (Bool × Bool)) :
      (Real.sqrt (f z)-Real.sqrt (g z))^2 ≤ 16*b^2*(macroBump h z.1)^2 := by
    calc
      _ ≤ (f z-g z)^2 := oracle_sqrt_difference_le _ _ (hfbound z).1 (hgbound z).1
      _ ≤ _ := by
        dsimp only [f, g, P0, P1]
        rw [oracle_bump_likelihood d h b false hb hbsmall,
          oracle_bump_likelihood d h b true hb hbsmall]
        rcases z with ⟨x,A,Y⟩
        cases A <;> cases Y <;> simp [thetaSign] <;> nlinarith [sq_nonneg (b*macroBump h x)]
  have hi : Integrable (fun z : Cov d × (Bool × Bool) =>
      (Real.sqrt (f z)-Real.sqrt (g z))^2) ((uniformLaw d).prod fairObserved) := by
    apply (integrable_const (16:ℝ)).mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hs : Real.sqrt (f z) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by
      dsimp [f, P0]; linarith [(hfbound z).2]⟩
    have ht : Real.sqrt (g z) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by
      dsimp [g, P1]; linarith [(hgbound z).2]⟩
    nlinarith [Real.sqrt_nonneg (f z), Real.sqrt_nonneg (g z)]
  have hbi : Integrable (fun z : Cov d × (Bool × Bool) => 16*b^2*(macroBump h z.1)^2)
      ((uniformLaw d).prod fairObserved) := by
    apply (integrable_const (16*b^2)).mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hm := macroBump_mem h z.1
    have hsq : (macroBump h z.1)^2 ≤ 1 := by nlinarith [hm.1, hm.2]
    nlinarith [sq_nonneg b]
  calc
    _ ≤ ∫ z, 16*b^2*(macroBump h z.1)^2 ∂(uniformLaw d).prod fairObserved :=
      integral_mono hi hbi hpoint
    _ = 16*b^2*(∫ x : Cov d, (macroBump h x)^2 ∂uniformLaw d) := by
      rw [integral_const_mul, integral_fun_fst (fun x : Cov d => (macroBump h x)^2)]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (oracle_bump_square_energy d h hh hh1) (by positivity)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
