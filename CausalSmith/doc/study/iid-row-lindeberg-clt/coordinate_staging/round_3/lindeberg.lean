module
public import Causalean.Stat.CLT.Martingale.Main
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Lindeberg--Feller CLT for i.i.d. rows

This module provides finite i.i.d.-row sum laws, their square-root scaling identities, and the
Lindeberg--Feller central limit theorem for row-dependent real laws.  Its normalized theorem is
the form used by bootstrap arguments: it permits the i.i.d. law to change with the row index and
includes a zero-variance Gaussian limit.
-/

@[expose] public section

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory Topology

/-- For [a row length](hyp:n), [the row-sum function](goal) is [given by adding its real-valued
coordinates](step:1). -/
def iidRowSum (n : ℕ) : (Fin n → ℝ) → ℝ := fun y => ∑ i, y i

/-- For [a row length](hyp:n), [the row-sum function is measurable for the product Borel
σ-algebra](goal). -/
lemma measurable_iidRowSum (n : ℕ) : Measurable (iidRowSum n) := by
  unfold iidRowSum
  fun_prop

/-- For [a sequence of probability laws](hyp:Q) and [a row index](hyp:n), [the i.i.d. row-sum
law](goal) is [given by pushing the product law forward through the coordinate sum](step:1). -/
noncomputable def iidRowSumLaw (Q : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (Q n)]
    (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(Measure.pi (fun _ : Fin n => Q n)).map (iidRowSum n),
    Measure.isProbabilityMeasure_map (measurable_iidRowSum n).aemeasurable⟩

/-- For [a sequence of probability laws](hyp:Q), [a row index](hyp:n), and [a Fourier
argument](hyp:t), [the row-sum characteristic function equals the corresponding
one-coordinate characteristic function raised to the row length](goal). -/
lemma charFun_iidRowSumLaw (Q : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (Q n)]
    (n : ℕ) (t : ℝ) :
    charFun (iidRowSumLaw Q n : Measure ℝ) t = charFun (Q n) t ^ n := by
  change charFun ((Measure.pi (fun _ : Fin n => Q n)).map (fun p => ∑ i, p i)) t = _
  simpa using
    congrFun (charFun_map_sum_pi_eq_prod (fun _ : Fin n => Q n)) t

/-- For [a sequence of probability laws](hyp:R) and [a row index](hyp:n), [the normalized
i.i.d. row-sum law](goal) is [given by pushing the product law forward through the row sum
divided by its square-root length](step:1). -/
noncomputable def iidRowNormalizedSumLaw (R : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (R n)] (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(Measure.pi (fun _ : Fin n => R n)).map
      (fun y => (Real.sqrt (n : ℝ))⁻¹ * iidRowSum n y),
    Measure.isProbabilityMeasure_map
      (measurable_const.mul (measurable_iidRowSum n)).aemeasurable⟩

/-- For [a sequence of row laws](hyp:R) and [a row index](hyp:n), [the scaled row law](goal) is
[given by pushing that row law forward through division by its square-root length](step:1). -/
noncomputable def scaledRowMeasure (R : ℕ → Measure ℝ) (n : ℕ) : Measure ℝ :=
  (R n).map (fun x => (Real.sqrt (n : ℝ))⁻¹ * x)

/-- For [a sequence of probability laws](hyp:R) and [a row index](hyp:n), [summing independently
drawn scaled coordinates has the same law as scaling their row sum](goal). -/
theorem iidRowSumLaw_scaledRowMeasure_eq_normalized
    (R : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (R n)] (n : ℕ) :
    @iidRowSumLaw (fun n => scaledRowMeasure R n)
        (fun n => Measure.isProbabilityMeasure_map (by fun_prop)) n =
      iidRowNormalizedSumLaw R n := by
  /-
  Use `Measure.pi_map_pi` to identify the product of the coordinate pushforwards with the
  pushforward of the product law by coordinatewise scaling.  Then use `Measure.map_map`; the
  sum of the scaled coordinates is pointwise the scaled sum (`Finset.mul_sum`).
  -/
  apply Subtype.ext
  change
    (Measure.pi (fun _ : Fin n => (R n).map (fun x => (Real.sqrt (n : ℝ))⁻¹ * x))).map
        (iidRowSum n) =
      (Measure.pi (fun _ : Fin n => R n)).map
        (fun y => (Real.sqrt (n : ℝ))⁻¹ * iidRowSum n y)
  rw [← Measure.pi_map_pi (fun _ => (by fun_prop :
    AEMeasurable (fun x : ℝ => (Real.sqrt (n : ℝ))⁻¹ * x) (R n)))]
  rw [Measure.map_map (measurable_iidRowSum n) (by fun_prop)]
  congr 1
  funext y
  simp only [Function.comp_apply, iidRowSum]
  rw [← Finset.mul_sum]

open Complex Filter MeasureTheory ProbabilityTheory Topology

/-- For [row laws](hyp:Q) with [limiting variance](hyp:σ2),
[square-integrable coordinates](hyp:hQ2),
[zero means](hyp:hcenter), [convergent scaled second moments](hyp:hsecond), and [vanishing
Lindeberg tails](hyp:hlindeberg), each [Fourier argument](hyp:t) has [rowwise characteristic
functions converging to the corresponding centered Gaussian characteristic function](goal). -/
theorem charFun_pow_tendsto_gaussian
    (Q : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (Q n)]
    (σ2 : NNReal)
    (hQ2 : ∀ n, MemLp id 2 (Q n))
    (hcenter : ∀ n, ∫ x, x ∂Q n = 0)
    (hsecond : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, x ^ 2 ∂Q n)
      atTop (𝓝 (σ2 : ℝ)))
    (hlindeberg : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (n : ℝ) *
        ∫ x in {x | ε ≤ |x|}, x ^ 2 ∂Q n) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n : ℕ => charFun (Q n) t ^ n) atTop
      (𝓝 (charFun (gaussianReal 0 σ2) t)) := by
  /-
  Expand `exp (I*t*x)` to second order.  After integrating, centering removes the linear
  term.  Split the quadratic remainder at a fixed `η > 0` and apply
  `Causalean.Stat.norm_expQuadraticRemainder_le_truncated`: the small part is bounded by
  `O(η)` times the total second moment, while the large part is bounded by the Lindeberg
  tail.  Hence `n * (charFun (Q n) t - 1)` tends to `-σ²*t²/2`.  Finish with
  `Complex.tendsto_one_add_pow_exp_of_tendsto` and `charFun_gaussianReal`.
  -/
  let R : ℕ → ℂ := fun n =>
    ∫ x, Causalean.Stat.expQuadraticRemainder (t * x) ∂Q n
  have hRint (n : ℕ) : Integrable
      (fun x => Causalean.Stat.expQuadraticRemainder (t * x)) (Q n) := by
    have hx1 : Integrable (fun x : ℝ => x) (Q n) :=
      (hQ2 n).integrable (by norm_num)
    have hx2 : Integrable (fun x : ℝ => x ^ 2) (Q n) :=
      (hQ2 n).integrable_sq
    have hexp : Integrable
        (fun x : ℝ => Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) (Q n) := by
      have hmeas : AEStronglyMeasurable
          (fun x : ℝ => Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) (Q n) := by
        fun_prop
      refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas ?_
      filter_upwards with x
      rw [Complex.norm_exp]
      simp
    apply (((hexp.sub (integrable_const (1 : ℂ))).sub
      (hx1.ofReal.const_mul (Complex.I * (t : ℂ)))).add
      (hx2.ofReal.const_mul (((t ^ 2 / 2 : ℝ) : ℂ)))).congr
    filter_upwards with x
    rw [Causalean.Stat.expQuadraticRemainder]
    push_cast
    simp only [Pi.add_apply, Pi.sub_apply]
    ring_nf
    rfl
  have hchar (n : ℕ) :
      charFun (Q n) t = 1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
        ((∫ x, x ^ 2 ∂Q n : ℝ) : ℂ)) + R n := by
    have hx1 : Integrable (fun x : ℝ => x) (Q n) :=
      (hQ2 n).integrable (by norm_num)
    have hx2 : Integrable (fun x : ℝ => x ^ 2) (Q n) :=
      (hQ2 n).integrable_sq
    rw [charFun_apply_real]
    have hpoint : (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
        fun x : ℝ => (1 : ℂ) + (Complex.I * (t : ℂ)) * (x : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ) +
          Causalean.Stat.expQuadraticRemainder (t * x) := by
      funext x
      rw [Causalean.Stat.expQuadraticRemainder]
      push_cast
      ring_nf
    rw [hpoint]
    have hlin : Integrable (fun x : ℝ =>
        (Complex.I * (t : ℂ)) * (x : ℂ)) (Q n) :=
      hx1.ofReal.const_mul (Complex.I * (t : ℂ))
    have hquad : Integrable (fun x : ℝ =>
        ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ)) (Q n) :=
      hx2.ofReal.const_mul (((t ^ 2 / 2 : ℝ) : ℂ))
    have hbase : Integrable (fun x : ℝ =>
        (1 : ℂ) + (Complex.I * (t : ℂ)) * (x : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ)) (Q n) :=
      ((integrable_const (1 : ℂ)).add hlin).sub hquad
    calc
      (∫ x : ℝ, (1 : ℂ) + (Complex.I * (t : ℂ)) * (x : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ) +
          Causalean.Stat.expQuadraticRemainder (t * x) ∂Q n) =
          (∫ x : ℝ, (1 : ℂ) + (Complex.I * (t : ℂ)) * (x : ℂ) -
            ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ) ∂Q n) + R n := by
            rw [integral_add hbase (hRint n)]
      _ = 1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
          ((∫ x, x ^ 2 ∂Q n : ℝ) : ℂ)) + R n := by
        have hsplitBase :
            (∫ x : ℝ, (1 : ℂ) + (Complex.I * (t : ℂ)) * (x : ℂ) -
              ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ) ∂Q n) =
              (∫ x : ℝ, (1 : ℂ) + (Complex.I * (t : ℂ)) * (x : ℂ) ∂Q n) -
              ∫ x : ℝ, ((t ^ 2 / 2 : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ) ∂Q n := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            integral_sub ((integrable_const (1 : ℂ)).add hlin) hquad
        have hsplitLin :
            (∫ x : ℝ, (1 : ℂ) + (Complex.I * (t : ℂ)) * (x : ℂ) ∂Q n) =
              (∫ _ : ℝ, (1 : ℂ) ∂Q n) +
              ∫ x : ℝ, (Complex.I * (t : ℂ)) * (x : ℂ) ∂Q n := by
          simpa only [Pi.add_apply] using
            integral_add (integrable_const (1 : ℂ)) hlin
        rw [hsplitBase, hsplitLin]
        rw [integral_const_mul, integral_const_mul]
        have hcoe1 : (∫ x : ℝ, (x : ℂ) ∂Q n) =
            ((∫ x : ℝ, x ∂Q n : ℝ) : ℂ) := integral_complex_ofReal
        have hcoe2 : (∫ x : ℝ, ((x ^ 2 : ℝ) : ℂ) ∂Q n) =
            ((∫ x : ℝ, x ^ 2 ∂Q n : ℝ) : ℂ) := integral_complex_ofReal
        rw [hcoe1, hcoe2]
        simp [hcenter n]
  have htrunc_le (n : ℕ) (η : ℝ) :
      (∫ x, if η < |x| then x ^ 2 else 0 ∂Q n) ≤
        ∫ x in {x | η ≤ |x|}, x ^ 2 ∂Q n := by
    have hs : MeasurableSet {x : ℝ | η < |x|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable)
    have ht : MeasurableSet {x : ℝ | η ≤ |x|} :=
      measurableSet_le measurable_const (continuous_abs.measurable)
    have hif : (fun x : ℝ => if η < |x| then x ^ 2 else 0) =
        {x : ℝ | η < |x|}.indicator (fun x => x ^ 2) := by
      funext x
      by_cases hx : η < |x| <;> simp [Set.indicator, hx]
    rw [hif, integral_indicator hs]
    exact setIntegral_mono_set (hQ2 n).integrable_sq.integrableOn
      (ae_of_all _ fun x => sq_nonneg x)
      (ae_of_all _ fun x hx => hx.le)
  have hRscaled : Tendsto (fun n : ℕ => (n : ℂ) * R n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let A : ℝ := |t| ^ 3
    let B : ℝ := (σ2 : ℝ) + 1
    let η : ℝ := min (1 / (|t| + 1)) (ε / (4 * (A * B + 1)))
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 < B := by dsimp [B]; positivity
    have hAB : 0 < A * B + 1 := by positivity
    have hη : 0 < η := by
      dsimp [η]
      apply lt_min
      · positivity
      · positivity
    have htη : |t| * η ≤ 1 := by
      calc
        |t| * η ≤ |t| * (1 / (|t| + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg t)
        _ = |t| / (|t| + 1) := by ring
        _ ≤ 1 := (div_lt_one (by positivity)).2 (by linarith [abs_nonneg t]) |>.le
    have hsmall : A * η * B ≤ ε / 4 := by
      have hηle : η ≤ ε / (4 * (A * B + 1)) := min_le_right _ _
      have hABnonneg : 0 ≤ A * B := mul_nonneg hA hB.le
      calc
        A * η * B = (A * B) * η := by ring
        _ ≤ (A * B) * (ε / (4 * (A * B + 1))) :=
          mul_le_mul_of_nonneg_left hηle hABnonneg
        _ ≤ ε / 4 := by
          have hfrac : A * B / (A * B + 1) ≤ 1 :=
            (div_le_one hAB).2 (by linarith)
          calc
            A * B * (ε / (4 * (A * B + 1))) =
                (ε / 4) * (A * B / (A * B + 1)) := by
              field_simp
            _ ≤ (ε / 4) * 1 :=
              mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ = ε / 4 := by ring
    let C : ℝ := 2 / η ^ 2 + |t| / η + t ^ 2 / 2
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hsecondEventually : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * ∫ x, x ^ 2 ∂Q n < B :=
      (tendsto_order.1 hsecond).2 B (by dsimp [B]; linarith)
    have htail : Tendsto (fun n : ℕ => C * ((n : ℝ) *
        ∫ x in {x | η ≤ |x|}, x ^ 2 ∂Q n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul (hlindeberg η hη))
    have htailEventually : ∀ᶠ n : ℕ in atTop,
        C * ((n : ℝ) * ∫ x in {x | η ≤ |x|}, x ^ 2 ∂Q n) < ε / 2 := by
      have he := Metric.tendsto_nhds.mp htail (ε / 2) (by positivity)
      filter_upwards [he] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact (le_abs_self _).trans_lt hn
    apply Filter.eventually_atTop.mp
    filter_upwards [hsecondEventually, htailEventually] with n hnsecond hntail
    rw [dist_zero_right]
    have hrem := Causalean.Stat.integral_norm_expQuadraticRemainder_le
      (fun x : ℝ => x) (hQ2 n) t η hη htη
    have hnorm : ‖R n‖ ≤
        A * η * (∫ x, x ^ 2 ∂Q n) +
          C * (∫ x, if η < |x| then x ^ 2 else 0 ∂Q n) := by
      calc
        ‖R n‖ ≤ ∫ x, ‖Causalean.Stat.expQuadraticRemainder (t * x)‖ ∂Q n :=
          norm_integral_le_integral_norm _
        _ ≤ A * η * (∫ x, x ^ 2 ∂Q n) +
            C * (∫ x, if η < |x| then x ^ 2 else 0 ∂Q n) := by
          simpa only [A, C] using hrem
    calc
      ‖(n : ℂ) * R n‖ = (n : ℝ) * ‖R n‖ := by simp
      _ ≤ (n : ℝ) * (A * η * (∫ x, x ^ 2 ∂Q n) +
          C * (∫ x, if η < |x| then x ^ 2 else 0 ∂Q n)) :=
        mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n)
      _ = A * η * ((n : ℝ) * ∫ x, x ^ 2 ∂Q n) +
          C * ((n : ℝ) * ∫ x, if η < |x| then x ^ 2 else 0 ∂Q n) := by ring
      _ ≤ A * η * ((n : ℝ) * ∫ x, x ^ 2 ∂Q n) +
          C * ((n : ℝ) * ∫ x in {x | η ≤ |x|}, x ^ 2 ∂Q n) := by
        gcongr
        exact htrunc_le n η
      _ < ε := by
        have hfirst : A * η * ((n : ℝ) * ∫ x, x ^ 2 ∂Q n) ≤ ε / 4 :=
          (mul_le_mul_of_nonneg_left hnsecond.le (mul_nonneg hA hη.le)).trans hsmall
        linarith
  let z : ℂ := -((((σ2 : ℝ) * t ^ 2 / 2 : ℝ) : ℂ))
  have hscaledChar : Tendsto
      (fun n : ℕ => (n : ℂ) * (charFun (Q n) t - 1)) atTop (𝓝 z) := by
    have hsecondComplex : Tendsto
        (fun n : ℕ => (((n : ℝ) * ∫ x, x ^ 2 ∂Q n : ℝ) : ℂ)) atTop
        (𝓝 ((σ2 : ℝ) : ℂ)) := hsecond.ofReal
    have hquadratic := hsecondComplex.const_mul (-(((t ^ 2 / 2 : ℝ) : ℂ)))
    have hsum := hquadratic.add hRscaled
    have hlimit : -(((t ^ 2 / 2 : ℝ) : ℂ)) * (((σ2 : ℝ) : ℂ)) + 0 = z := by
      dsimp [z]
      push_cast
      ring
    rw [hlimit] at hsum
    apply hsum.congr'
    filter_upwards with n
    rw [hchar n]
    push_cast
    ring
  have hpow := Complex.tendsto_one_add_pow_exp_of_tendsto hscaledChar
  have hgaussian : charFun (gaussianReal 0 σ2) t = Complex.exp z := by
    rw [charFun_gaussianReal]
    dsimp [z]
    push_cast
    congr 1
    ring
  rw [hgaussian]
  convert hpow using 1
  funext n
  congr 1
  ring

/-- For [row laws](hyp:Q) with [limiting variance](hyp:σ2),
[square-integrable coordinates](hyp:hQ2),
[zero means](hyp:hcenter), [convergent scaled second moments](hyp:hsecond), and [vanishing
Lindeberg tails](hyp:hlindeberg), [the laws of their i.i.d. row sums converge weakly to the
centered Gaussian law with that variance](goal). -/
theorem iidRowSumLaw_tendsto_gaussian
    (Q : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (Q n)]
    (σ2 : NNReal)
    (hQ2 : ∀ n, MemLp id 2 (Q n))
    (hcenter : ∀ n, ∫ x, x ∂Q n = 0)
    (hsecond : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, x ^ 2 ∂Q n)
      atTop (𝓝 (σ2 : ℝ)))
    (hlindeberg : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (n : ℝ) *
        ∫ x in {x | ε ≤ |x|}, x ^ 2 ∂Q n) atTop (𝓝 0)) :
    Tendsto (iidRowSumLaw Q) atTop
      (𝓝 (⟨gaussianReal 0 σ2, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  simpa only [charFun_iidRowSumLaw, ProbabilityMeasure.coe_mk] using
    charFun_pow_tendsto_gaussian Q σ2 hQ2 hcenter hsecond hlindeberg t

open MeasureTheory

/-- For [row laws](hyp:R), [a row index](hyp:n), and [a square-integrable row](hyp:hR2), [the
corresponding scaled row law remains square-integrable](goal). -/
lemma memLp_id_scaledRowMeasure
    (R : ℕ → Measure ℝ) (n : ℕ) (hR2 : MemLp id 2 (R n)) :
    MemLp id 2 (scaledRowMeasure R n) := by
  unfold scaledRowMeasure
  refine (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 ?_
  simpa [Function.comp_def] using hR2.const_mul ((Real.sqrt (n : ℝ))⁻¹)

/-- For [row laws](hyp:R), [a positive row index](hyp:n,hn), [a square-integrable row](hyp:hR2),
and [a zero row mean](hyp:hcenter), [the scaled row law also has zero mean](goal). -/
lemma integral_id_scaledRowMeasure_eq_zero
    (R : ℕ → Measure ℝ) (n : ℕ) (hn : n ≠ 0)
    (hR2 : MemLp id 2 (R n)) (hcenter : ∫ x, x ∂R n = 0) :
    ∫ x, x ∂scaledRowMeasure R n = 0 := by
  have _hn := hn
  have hident := (memLp_id_scaledRowMeasure R n hR2).aestronglyMeasurable
  change AEStronglyMeasurable (fun x : ℝ => x) (scaledRowMeasure R n) at hident
  unfold scaledRowMeasure at hident ⊢
  rw [integral_map (μ := R n) (φ := fun x : ℝ => (Real.sqrt (n : ℝ))⁻¹ * x)
    (f := fun x : ℝ => x) (by fun_prop) hident]
  rw [integral_const_mul, hcenter, mul_zero]

/-- For [row laws](hyp:R), [a positive row index](hyp:n,hn), and [a square-integrable row](hyp:hR2),
[the scaled row's second moment is its original second moment divided by the row length](goal). -/
lemma integral_sq_scaledRowMeasure
    (R : ℕ → Measure ℝ) (n : ℕ) (hn : n ≠ 0) (hR2 : MemLp id 2 (R n)) :
    ∫ x, x ^ 2 ∂scaledRowMeasure R n =
      ((n : ℝ)⁻¹ * ∫ x, x ^ 2 ∂R n) := by
  have hident := (memLp_id_scaledRowMeasure R n hR2).aestronglyMeasurable
  change AEStronglyMeasurable (fun x : ℝ => x) (scaledRowMeasure R n) at hident
  have hsq := hident.pow 2
  change AEStronglyMeasurable (fun x : ℝ => x ^ 2) (scaledRowMeasure R n) at hsq
  unfold scaledRowMeasure at hsq ⊢
  rw [integral_map (μ := R n) (φ := fun x : ℝ => (Real.sqrt (n : ℝ))⁻¹ * x)
    (f := fun x : ℝ => x ^ 2) (by fun_prop) hsq]
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    ∫ x, ((Real.sqrt (n : ℝ))⁻¹ * x) ^ 2 ∂R n =
        ∫ x, ((Real.sqrt (n : ℝ))⁻¹ ^ 2) * x ^ 2 ∂R n := by
          congr 1
          funext x
          ring
    _ = (Real.sqrt (n : ℝ))⁻¹ ^ 2 * ∫ x, x ^ 2 ∂R n := integral_const_mul _ _
    _ = (n : ℝ)⁻¹ * ∫ x, x ^ 2 ∂R n := by
      rw [inv_pow, Real.sq_sqrt hnpos.le]

/-- For [row laws](hyp:R), [a positive row index](hyp:n,hn), [a square-integrable row](hyp:hR2),
and [a positive threshold](hyp:ε,hε), [the scaled row's Lindeberg tail second moment equals the
original tail above the square-root-scaled threshold, divided by the row length](goal). -/
lemma setIntegral_sq_scaledRowMeasure
    (R : ℕ → Measure ℝ) (n : ℕ) (hn : n ≠ 0) (hR2 : MemLp id 2 (R n))
    (ε : ℝ) (hε : 0 < ε) :
    ∫ x in {x | ε ≤ |x|}, x ^ 2 ∂scaledRowMeasure R n =
      (n : ℝ)⁻¹ * ∫ x in {x | ε * Real.sqrt (n : ℝ) ≤ |x|}, x ^ 2 ∂R n := by
  have _hε := hε
  have hident := (memLp_id_scaledRowMeasure R n hR2).aestronglyMeasurable
  change AEStronglyMeasurable (fun x : ℝ => x) (scaledRowMeasure R n) at hident
  have hsq := hident.pow 2
  change AEStronglyMeasurable (fun x : ℝ => x ^ 2) (scaledRowMeasure R n) at hsq
  unfold scaledRowMeasure at hsq ⊢
  rw [setIntegral_map (s := {x : ℝ | ε ≤ |x|})
    (measurableSet_le measurable_const measurable_id.abs) hsq (by fun_prop)]
  have hnpos : 0 < (n : ℝ) := by positivity
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hpre :
      (fun x : ℝ => (Real.sqrt (n : ℝ))⁻¹ * x) ⁻¹' {x : ℝ | ε ≤ |x|} =
        {x : ℝ | ε * Real.sqrt (n : ℝ) ≤ |x|} := by
    ext x
    change ε ≤ |(Real.sqrt (n : ℝ))⁻¹ * x| ↔
      ε * Real.sqrt (n : ℝ) ≤ |x|
    rw [← div_eq_inv_mul, abs_div, abs_of_pos hsqrtpos, le_div_iff₀ hsqrtpos]
  rw [hpre]
  calc
    ∫ x in {x : ℝ | ε * Real.sqrt (n : ℝ) ≤ |x|},
        ((Real.sqrt (n : ℝ))⁻¹ * x) ^ 2 ∂R n =
      ∫ x in {x : ℝ | ε * Real.sqrt (n : ℝ) ≤ |x|},
        ((Real.sqrt (n : ℝ))⁻¹ ^ 2) * x ^ 2 ∂R n := by
          congr 1
          funext x
          ring
    _ = (Real.sqrt (n : ℝ))⁻¹ ^ 2 *
        ∫ x in {x : ℝ | ε * Real.sqrt (n : ℝ) ≤ |x|}, x ^ 2 ∂R n :=
      integral_const_mul _ _
    _ = (n : ℝ)⁻¹ *
        ∫ x in {x : ℝ | ε * Real.sqrt (n : ℝ) ≤ |x|}, x ^ 2 ∂R n := by
      rw [inv_pow, Real.sq_sqrt hnpos.le]

open Filter MeasureTheory ProbabilityTheory Topology

/-- For [row laws](hyp:R) with [limiting variance](hyp:σ2),
[square-integrable coordinates](hyp:hR2),
[zero means](hyp:hcenter), [convergent row second moments](hyp:hsecond), and [vanishing
square-root-scale Lindeberg tails](hyp:hlindeberg), [normalized i.i.d. row-sum laws converge
weakly to the centered Gaussian law with that variance](goal). -/
theorem iidRowNormalizedSumLaw_tendsto_gaussian
    (R : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (R n)]
    (σ2 : NNReal)
    (hR2 : ∀ n, MemLp id 2 (R n))
    (hcenter : ∀ n, ∫ x, x ∂R n = 0)
    (hsecond : Tendsto (fun n : ℕ => ∫ x, x ^ 2 ∂R n)
      atTop (𝓝 (σ2 : ℝ)))
    (hlindeberg : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
        ∫ x in {x | ε * Real.sqrt (n : ℝ) ≤ |x|}, x ^ 2 ∂R n)
        atTop (𝓝 0)) :
    Tendsto (iidRowNormalizedSumLaw R) atTop
      (𝓝 (⟨gaussianReal 0 σ2, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let Q : ℕ → Measure ℝ := scaledRowMeasure R
  let hQprob : ∀ n, IsProbabilityMeasure (Q n) := fun n =>
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hQ2 : ∀ n, MemLp id 2 (Q n) := fun n =>
    memLp_id_scaledRowMeasure R n (hR2 n)
  have hcenterQ : ∀ n, ∫ x, x ∂Q n = 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [Q, scaledRowMeasure]
    · exact integral_id_scaledRowMeasure_eq_zero R n hn (hR2 n) (hcenter n)
  have hsecondQ :
      Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, x ^ 2 ∂Q n)
        atTop (𝓝 (σ2 : ℝ)) := by
    apply Tendsto.congr' _ hsecond
    filter_upwards [Nat.eventually_pos] with n hn
    rw [integral_sq_scaledRowMeasure R n hn.ne' (hR2 n)]
    rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul]
  have hlindebergQ : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (n : ℝ) *
        ∫ x in {x | ε ≤ |x|}, x ^ 2 ∂Q n) atTop (𝓝 0) := by
    intro ε hε
    apply Tendsto.congr' _ (hlindeberg ε hε)
    filter_upwards [Nat.eventually_pos] with n hn
    rw [setIntegral_sq_scaledRowMeasure R n hn.ne' (hR2 n) ε hε]
    rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul]
  have hscaled :=
    @iidRowSumLaw_tendsto_gaussian Q hQprob σ2 hQ2 hcenterQ hsecondQ hlindebergQ
  apply hscaled.congr'
  filter_upwards with n
  exact iidRowSumLaw_scaledRowMeasure_eq_normalized R n

end Causalean.Stat
