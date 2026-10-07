module
public import Causalean.Mathlib.MeasureTheory.FiniteAtomicMeasure
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Triple

/-!
# Marked-Poisson predictive laws

This module defines the one-cell marked-Poisson experiment and proves its singleton Taylor expansion for bounded finitely supported triple priors.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- A [real rate](hyp:r) determines [its nonnegative Poisson rate](goal) by [clipping negative values to zero](step:1). -/
noncomputable def nnRate (r : ℝ) : NNReal := Real.toNNReal r

/-- An [experiment size](hyp:n) and [parameter triple](hyp:t) of arrival mass p, propensity π, and conditional success probability μ determine [the conditional three-mark Poisson law](goal) as [the product of three independent Poisson count laws with rates npπμ, npπ(1−μ), and np(1−π), each negative rate clipped to zero](step:1). -/
noncomputable def markedPoissonLaw (n : ℝ) (t : MarkedParam) : Measure ((ℕ × ℕ) × ℕ) :=
  ((poissonMeasure (nnRate (n * t.1 * t.2.1 * t.2.2))).prod
    (poissonMeasure (nnRate (n * t.1 * t.2.1 * (1 - t.2.2))))).prod
    (poissonMeasure (nnRate (n * t.1 * (1 - t.2.1))))

/-- An [experiment size](hyp:n) and [prior on parameter triples](hyp:ν) determine [the one-cell predictive law](goal) by [mixing the conditional marked Poisson law over that prior](step:1). -/
noncomputable def predictiveLaw (n : ℝ) (ν : Measure MarkedParam) :
    Measure ((ℕ × ℕ) × ℕ) := ν.bind (markedPoissonLaw n)

/- Each clipped rate is nonnegative and each Poisson law is a probability
  measure. Show that the parameter-to-law kernel is measurable, then use the
  probability-preserving bind rule. -/

private lemma measurable_poissonMeasure_rate :
    Measurable (fun r : NNReal => poissonMeasure r) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [poissonMeasure, Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro k
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  fun_prop

private lemma measurable_markedPoissonLaw (n : ℝ) :
    Measurable (markedPoissonLaw n) := by
  have h₁ : Measurable (fun t : MarkedParam =>
      (⟨poissonMeasure (nnRate (n * t.1 * t.2.1 * t.2.2)), inferInstance⟩ :
        ProbabilityMeasure ℕ)) :=
    Measurable.subtype_mk (measurable_poissonMeasure_rate.comp (by
      unfold nnRate
      fun_prop))
  have h₂ : Measurable (fun t : MarkedParam =>
      (⟨poissonMeasure (nnRate (n * t.1 * t.2.1 * (1 - t.2.2))), inferInstance⟩ :
        ProbabilityMeasure ℕ)) :=
    Measurable.subtype_mk (measurable_poissonMeasure_rate.comp (by
      unfold nnRate
      fun_prop))
  have h₃ : Measurable (fun t : MarkedParam =>
      (⟨poissonMeasure (nnRate (n * t.1 * (1 - t.2.1))), inferInstance⟩ :
        ProbabilityMeasure ℕ)) :=
    Measurable.subtype_mk (measurable_poissonMeasure_rate.comp (by
      unfold nnRate
      fun_prop))
  have h₁₂ : Measurable (fun t : MarkedParam =>
      (⟨(poissonMeasure (nnRate (n * t.1 * t.2.1 * t.2.2))).prod
        (poissonMeasure (nnRate (n * t.1 * t.2.1 * (1 - t.2.2)))), inferInstance⟩ :
          ProbabilityMeasure (ℕ × ℕ))) :=
    Measurable.subtype_mk (ProbabilityMeasure.measurable_fun_prod.comp (h₁.prodMk h₂))
  exact ProbabilityMeasure.measurable_fun_prod.comp (h₁₂.prodMk h₃)

/-- An [experiment size](hyp:n) and [probability prior](hyp:ν) give [a probability one-cell predictive law](goal). -/
theorem predictiveLaw_isProbability (n : ℝ) (ν : Measure MarkedParam)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (predictiveLaw n ν) := by
  unfold predictiveLaw
  exact MeasureTheory.isProbabilityMeasure_bind
    (measurable_markedPoissonLaw n).aemeasurable
    (Filter.Eventually.of_forall fun t => by
      unfold markedPoissonLaw
      infer_instance)

/- Use the product singleton rule and the Poisson singleton mass formula.
  The three unclipped rates add to n p under the displayed bounds, so their
  exponential factors multiply to exp(-np). -/

/-- A [nonnegative experiment size](hyp:hn), [bounded parameter triple](hyp:t,hp,hπ₀,hπ₁,hμ₀,hμ₁), and [three observed counts](hyp:u,v,w) give [the stated singleton mass of the conditional marked Poisson law](goal). -/
theorem markedPoissonLaw_singleton {n : ℝ} (hn : 0 ≤ n)
    (t : MarkedParam) (hp : 0 ≤ t.1)
    (hπ₀ : 0 ≤ t.2.1) (hπ₁ : t.2.1 ≤ 1)
    (hμ₀ : 0 ≤ t.2.2) (hμ₁ : t.2.2 ≤ 1)
    (u v w : ℕ) :
    (markedPoissonLaw n t).real {((u, v), w)} =
      Real.exp (-n * t.1) *
        (n * t.1 * t.2.1 * t.2.2) ^ u *
        (n * t.1 * t.2.1 * (1 - t.2.2)) ^ v *
        (n * t.1 * (1 - t.2.1)) ^ w /
        ((Nat.factorial u : ℝ) * (Nat.factorial v : ℝ) *
          (Nat.factorial w : ℝ)) := by
  have hr₁ : 0 ≤ n * t.1 * t.2.1 * t.2.2 := by positivity
  have hr₂ : 0 ≤ n * t.1 * t.2.1 * (1 - t.2.2) := by positivity
  have hr₃ : 0 ≤ n * t.1 * (1 - t.2.1) := by positivity
  have hmass : (markedPoissonLaw n t).real {((u, v), w)} =
      (poissonMeasure (nnRate (n * t.1 * t.2.1 * t.2.2))).real {u} *
      (poissonMeasure (nnRate (n * t.1 * t.2.1 * (1 - t.2.2)))).real {v} *
      (poissonMeasure (nnRate (n * t.1 * (1 - t.2.1)))).real {w} := by
    rw [measureReal_def, markedPoissonLaw,
      ← Set.singleton_prod_singleton, Measure.prod_prod,
      ← Set.singleton_prod_singleton, Measure.prod_prod,
      ENNReal.toReal_mul, ENNReal.toReal_mul]
    rfl
  rw [hmass, poissonMeasure_real_singleton, poissonMeasure_real_singleton,
    poissonMeasure_real_singleton]
  simp only [nnRate, Real.coe_toNNReal _ hr₁, Real.coe_toNNReal _ hr₂,
    Real.coe_toNNReal _ hr₃]
  have hexp : Real.exp (-(n * t.1 * t.2.1 * t.2.2)) *
      Real.exp (-(n * t.1 * t.2.1 * (1 - t.2.2))) *
      Real.exp (-(n * t.1 * (1 - t.2.1))) = Real.exp (-n * t.1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [show -n * t.1 = -(n * t.1) by ring] at hexp
  field_simp
  rw [← hexp]
  ring

/- Apply bind on a singleton and convert the bounded ENNReal mass integral
  to a real integral. Use the conditional singleton formula almost everywhere
  under the support hypothesis. -/

/-- A [nonnegative experiment size](hyp:hn), [probability prior](hyp:ν), [its bounded support](hyp:hsupport), and [three observed counts](hyp:u,v,w) give [the predictive singleton mass as the prior mean of the conditional singleton mass](goal). -/
theorem predictiveLaw_singleton {n : ℝ} (hn : 0 ≤ n)
    (ν : Measure MarkedParam) [IsProbabilityMeasure ν]
    (hsupport : ν {t | 0 ≤ t.1 ∧ 0 ≤ t.2.1 ∧ t.2.1 ≤ 1 ∧
      0 ≤ t.2.2 ∧ t.2.2 ≤ 1} = 1) (u v w : ℕ) :
    (predictiveLaw n ν).real {((u, v), w)} =
      ∫ t, Real.exp (-n * t.1) *
        (n * t.1 * t.2.1 * t.2.2) ^ u *
        (n * t.1 * t.2.1 * (1 - t.2.2)) ^ v *
        (n * t.1 * (1 - t.2.1)) ^ w /
        ((Nat.factorial u : ℝ) * (Nat.factorial v : ℝ) *
          (Nat.factorial w : ℝ)) ∂ν := by
  let s : Set MarkedParam := {t | 0 ≤ t.1 ∧ 0 ≤ t.2.1 ∧ t.2.1 ≤ 1 ∧
    0 ≤ t.2.2 ∧ t.2.2 ≤ 1}
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability
  have hae : ∀ᵐ t ∂ν, t ∈ s :=
    (mem_ae_iff_prob_eq_one hs).2 hsupport
  have hmeas : Measurable (markedPoissonLaw n) := measurable_markedPoissonLaw n
  have hmass_meas : AEMeasurable
      (fun t => markedPoissonLaw n t {((u, v), w)}) ν :=
    ((Measure.measurable_coe (measurableSet_singleton _)).comp hmeas).aemeasurable
  have hmass_finite : ∀ᵐ t ∂ν,
      markedPoissonLaw n t {((u, v), w)} < ⊤ :=
    Filter.Eventually.of_forall fun t => by
      haveI : IsProbabilityMeasure (markedPoissonLaw n t) := by
        unfold markedPoissonLaw
        infer_instance
      exact (measure_mono (Set.subset_univ _)).trans_lt (by simp)
  rw [measureReal_def, predictiveLaw,
    Measure.bind_apply (measurableSet_singleton _) hmeas.aemeasurable,
    ← integral_toReal hmass_meas hmass_finite]
  apply integral_congr_ae
  filter_upwards [hae] with t ht
  rcases ht with ⟨hp, hπ₀, hπ₁, hμ₀, hμ₁⟩
  exact markedPoissonLaw_singleton hn t hp hπ₀ hπ₁ hμ₀ hμ₁ u v w

/-- A [matching degree](hyp:K), [experiment size](hyp:n), and [support bound](hyp:b) determine [the unmatched Taylor tail](goal) by [summing factorial-weighted terms beyond degree `3K` at intensity `2nb`](step:1). -/
noncomputable def unmatchedTail (K : ℕ) (n b : ℝ) : ℝ :=
  ∑' m : ℕ, if 3 * K < m then (2 * n * b) ^ m / (Nat.factorial m : ℝ) else 0

/-- A [matching degree](hyp:K), [nonnegative experiment size](hyp:hn), and [nonnegative support bound](hyp:hb) give [the stated first-omitted-term bound for the unmatched factorial tail](goal). -/
theorem unmatchedTail_le_factorial (K : ℕ)
    {n b : ℝ} (hn : 0 ≤ n) (hb : 0 ≤ b) :
    unmatchedTail K n b ≤
      Real.exp (2 * n * b) * (2 * n * b) ^ (3 * K + 1) /
        (Nat.factorial (3 * K + 1) : ℝ) := by
  let x : ℝ := 2 * n * b
  let q : ℕ := 3 * K + 1
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hs : Summable (fun m : ℕ => x ^ m / (m.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x
  have hshift : Summable (fun j : ℕ => x ^ (j + q) / ((j + q).factorial : ℝ)) :=
    (summable_nat_add_iff q).2 hs
  have htail : unmatchedTail K n b =
      ∑' j : ℕ, x ^ (j + q) / ((j + q).factorial : ℝ) := by
    let g : ℕ → ℝ := fun m =>
      if q ≤ m then x ^ m / (m.factorial : ℝ) else 0
    have hg : Summable (fun j : ℕ => g (j + q)) := by
      simpa [g] using hshift
    have h := hg.sum_add_tsum_nat_add' (f := g) (k := q)
    have hzero : (∑ i ∈ Finset.range q, g i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [g, Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) (le_refl q)]
    rw [hzero, zero_add] at h
    have hshiftg : (fun i => g (i + q)) =
        (fun i => x ^ (i + q) / ((i + q).factorial : ℝ)) := by
      funext i
      simp [g]
    rw [hshiftg] at h
    have hiff (m : ℕ) : (3 * K < m) ↔ q ≤ m := by dsimp [q]; omega
    simpa only [unmatchedTail, hiff, g, x] using h.symm
  rw [htail]
  have hterm (j : ℕ) :
      x ^ (j + q) / ((j + q).factorial : ℝ) ≤
        (x ^ q / (q.factorial : ℝ)) * (x ^ j / (j.factorial : ℝ)) := by
    have hf : (q.factorial : ℝ) * (j.factorial : ℝ) ≤
        ((q + j).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add q j)
    rw [add_comm j q, pow_add]
    calc
      x ^ q * x ^ j / ((q + j).factorial : ℝ) ≤
          x ^ q * x ^ j / ((q.factorial : ℝ) * (j.factorial : ℝ)) := by
            gcongr
      _ = x ^ q / (q.factorial : ℝ) * (x ^ j / (j.factorial : ℝ)) := by ring
  calc
    (∑' j : ℕ, x ^ (j + q) / ((j + q).factorial : ℝ)) ≤
        ∑' j : ℕ, (x ^ q / (q.factorial : ℝ)) *
          (x ^ j / (j.factorial : ℝ)) := by
            exact Summable.tsum_le_tsum (fun j => hterm j) hshift
              (hs.mul_left _)
    _ = Real.exp x * x ^ q / (q.factorial : ℝ) := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      ring

/- Expand each conditional count mass as `exp(-np)` times a product
  of powers of the three rates.  Taylor-expand `exp(-np)`.  Terms with
  `t+i+j+ℓ ≤ 3K` are polynomials in `p,pπ,pπμ` and cancel by
  `mixed_match`.  Taking absolute values of the remaining coefficients
  yields half the two prior tails, each at most `unmatchedTail`.
  The support condition also ensures the clipped rates equal the rates.
  `tvDist_le_half_tsum_singleton_abs` supplies the factor `1/2` for the
  countable observation space.  The four nonnegative Taylor-envelope
  rates add to `2np`; group by total degree to obtain `unmatchedTail`. -/

/- Write the three unscaled mark rates as z, y-z, and x-y, where
  x=p, y=pπ, z=pπμ. Expanding the two differences by the binomial theorem
  expresses every term as a finite linear combination of mixedMonomial
  values of total degree t+u+v+w. The same coefficients occur for both
  priors, so mixed_match cancels them term by term. -/

/-- [Bounded triple priors](hyp:T) and [four Taylor indices whose total degree is at most `3K`](hyp:t,u,v,w,hdegree) give [matching integrated marked-rate Taylor coefficients](goal). -/
theorem integral_markedRateProduct_match {K : ℕ}
    {b ε gap : ℝ} (T : TriplePriors K b ε gap)
    (t u v w : ℕ) (hdegree : t + u + v + w ≤ 3 * K) :
    (∫ θ : MarkedParam, θ.1 ^ t *
      (θ.1 * θ.2.1 * θ.2.2) ^ u *
      (θ.1 * θ.2.1 * (1 - θ.2.2)) ^ v *
      (θ.1 * (1 - θ.2.1)) ^ w ∂T.ν₀) =
    (∫ θ : MarkedParam, θ.1 ^ t *
      (θ.1 * θ.2.1 * θ.2.2) ^ u *
      (θ.1 * θ.2.1 * (1 - θ.2.2)) ^ v *
      (θ.1 * (1 - θ.2.1)) ^ w ∂T.ν₁) := by
  let F (i j k a c : ℕ) (θ : MarkedParam) : ℝ :=
    θ.1 ^ i * (θ.1 * θ.2.1) ^ j *
      (θ.1 * θ.2.1 * θ.2.2) ^ k *
      (θ.1 * θ.2.1 * (1 - θ.2.2)) ^ a *
      (θ.1 * (1 - θ.2.1)) ^ c
  have integrable_F (μ : Measure MarkedParam) [IsProbabilityMeasure μ]
      (hfin : ∃ s : Finset MarkedParam, μ (s : Set MarkedParam) = 1)
      (i j k a c : ℕ) : Integrable (F i j k a c) μ := by
    obtain ⟨s, hs⟩ := hfin
    let cell : (s : Set MarkedParam) ↪ MarkedParam :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hrange : μ (Set.range cell) = μ Set.univ := by
      have heq : Set.range cell = (s : Set MarkedParam) := by
        ext θ
        simp [cell]
      rw [heq, hs]
      simp
    apply Causalean.Mathlib.MeasureTheory.integrable_of_finite_atomic_support
      μ cell (fun _ => measurableSet_singleton _) hrange
    dsimp [F]
    fun_prop
  haveI := T.probability₀
  haveI := T.probability₁
  have hmatch₀ : ∀ i j k a, i + j + k + a ≤ 3 * K →
      (∫ θ, F i j k a 0 θ ∂T.ν₀) = ∫ θ, F i j k a 0 θ ∂T.ν₁ := by
    intro i j k a
    induction a generalizing i j k with
    | zero =>
        intro hd
        simpa [F, mixedMonomial] using T.mixed_match i j k (by omega)
    | succ a ih =>
        intro hd
        have hp (θ : MarkedParam) :
            F i j k (a + 1) 0 θ =
              F i (j + 1) k a 0 θ - F i j (k + 1) a 0 θ := by
          dsimp [F]
          rw [pow_succ, pow_succ, pow_succ]
          ring
        have hleft : i + (j + 1) + k + a ≤ 3 * K := by omega
        have hright : i + j + (k + 1) + a ≤ 3 * K := by omega
        calc
          (∫ θ, F i j k (a + 1) 0 θ ∂T.ν₀) =
              ∫ θ, F i (j + 1) k a 0 θ - F i j (k + 1) a 0 θ ∂T.ν₀ := by
                apply integral_congr_ae
                filter_upwards [] with θ
                exact hp θ
          _ = (∫ θ, F i (j + 1) k a 0 θ ∂T.ν₀) -
              (∫ θ, F i j (k + 1) a 0 θ ∂T.ν₀) := by
                rw [integral_sub
                  (integrable_F T.ν₀ T.finite₀ _ _ _ _ _)
                  (integrable_F T.ν₀ T.finite₀ _ _ _ _ _)]
          _ = (∫ θ, F i (j + 1) k a 0 θ ∂T.ν₁) -
              (∫ θ, F i j (k + 1) a 0 θ ∂T.ν₁) := by
                rw [ih _ _ _ hleft, ih _ _ _ hright]
          _ = ∫ θ, F i j k (a + 1) 0 θ ∂T.ν₁ := by
                rw [← integral_sub
                  (integrable_F T.ν₁ T.finite₁ _ _ _ _ _)
                  (integrable_F T.ν₁ T.finite₁ _ _ _ _ _)]
                apply integral_congr_ae
                filter_upwards [] with θ
                exact (hp θ).symm
  have hmatch : ∀ c i j k a, i + j + k + a + c ≤ 3 * K →
      (∫ θ, F i j k a c θ ∂T.ν₀) = ∫ θ, F i j k a c θ ∂T.ν₁ := by
    intro c
    induction c with
    | zero =>
        intro i j k a hd
        exact hmatch₀ i j k a (by omega)
    | succ c ih =>
        intro i j k a hd
        have hp (θ : MarkedParam) :
            F i j k a (c + 1) θ =
              F (i + 1) j k a c θ - F i (j + 1) k a c θ := by
          dsimp [F]
          rw [pow_succ, pow_succ, pow_succ]
          ring
        have hleft : (i + 1) + j + k + a + c ≤ 3 * K := by omega
        have hright : i + (j + 1) + k + a + c ≤ 3 * K := by omega
        calc
          (∫ θ, F i j k a (c + 1) θ ∂T.ν₀) =
              ∫ θ, F (i + 1) j k a c θ - F i (j + 1) k a c θ ∂T.ν₀ := by
                apply integral_congr_ae
                filter_upwards [] with θ
                exact hp θ
          _ = (∫ θ, F (i + 1) j k a c θ ∂T.ν₀) -
              (∫ θ, F i (j + 1) k a c θ ∂T.ν₀) := by
                rw [integral_sub
                  (integrable_F T.ν₀ T.finite₀ _ _ _ _ _)
                  (integrable_F T.ν₀ T.finite₀ _ _ _ _ _)]
          _ = (∫ θ, F (i + 1) j k a c θ ∂T.ν₁) -
              (∫ θ, F i (j + 1) k a c θ ∂T.ν₁) := by
                rw [ih _ _ _ _ hleft, ih _ _ _ _ hright]
          _ = ∫ θ, F i j k a (c + 1) θ ∂T.ν₁ := by
                rw [← integral_sub
                  (integrable_F T.ν₁ T.finite₁ _ _ _ _ _)
                  (integrable_F T.ν₁ T.finite₁ _ _ _ _ _)]
                apply integral_congr_ae
                filter_upwards [] with θ
                exact (hp θ).symm
  simpa [F] using hmatch w t 0 u v (by omega)

/- Use `predictiveLaw_singleton` and the exponential series for
  `exp (-n*p)`. Finite support permits interchanging the pointwise
  series and the prior integral by finite atomic decomposition. An
  alternative is `hasSum_integral_of_dominated_convergence`, as used in
  Causalean's `exponentialPriorEnergy_eq_tsum`, with
  envelope `(n*b)^t/t!` times the bounded mark-rate factor. -/

/-- A [nonnegative experiment size](hyp:hn), [finitely supported probability prior](hyp:ν,hfinite), [support on arrival mass between 0 and b and propensity and success probability between 0 and 1](hyp:hsupport), and [three observed count values](hyp:u,v,w) give [the predictive mass of the count triple (u, v, w) as the series Σ over t ≥ 0 of (−n)ᵗ · n^(u+v+w) / (t! u! v! w!) times the prior mean of pᵗ (pπμ)ᵘ (pπ(1−μ))ᵛ (p(1−π))ʷ](goal). -/
theorem predictiveLaw_singleton_eq_tsum_markedRateProduct
    {n b : ℝ} (hn : 0 ≤ n) (ν : Measure MarkedParam)
    [IsProbabilityMeasure ν]
    (hfinite : ∃ s : Finset MarkedParam, ν (s : Set MarkedParam) = 1)
    (hsupport : ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧
      0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} = 1)
    (u v w : ℕ) :
    (predictiveLaw n ν).real {((u, v), w)} =
      ∑' t : ℕ,
        ((-n) ^ t * n ^ (u + v + w) /
          ((Nat.factorial t : ℝ) * (Nat.factorial u : ℝ) *
            (Nat.factorial v : ℝ) * (Nat.factorial w : ℝ))) *
          (∫ θ : MarkedParam, θ.1 ^ t *
            (θ.1 * θ.2.1 * θ.2.2) ^ u *
            (θ.1 * θ.2.1 * (1 - θ.2.2)) ^ v *
            (θ.1 * (1 - θ.2.1)) ^ w ∂ν) := by
  let P (θ : MarkedParam) : ℝ :=
    (n * θ.1 * θ.2.1 * θ.2.2) ^ u *
      (n * θ.1 * θ.2.1 * (1 - θ.2.2)) ^ v *
      (n * θ.1 * (1 - θ.2.1)) ^ w /
      ((Nat.factorial u : ℝ) * (Nat.factorial v : ℝ) *
        (Nat.factorial w : ℝ))
  let F (t : ℕ) (θ : MarkedParam) : ℝ :=
    (-n * θ.1) ^ t / (Nat.factorial t : ℝ) * P θ
  have hmeas (t : ℕ) : AEStronglyMeasurable (F t) ν := by
    apply Measurable.aestronglyMeasurable
    dsimp [F, P]
    fun_prop
  have hbound (t : ℕ) : ∀ᵐ θ ∂ν, ‖F t θ‖ ≤ ‖F t θ‖ :=
    Filter.Eventually.of_forall fun _ => le_refl _
  have hsummable (θ : MarkedParam) : Summable (fun t => ‖F t θ‖) := by
    have h := Real.summable_pow_div_factorial (-n * θ.1)
    have h' : Summable (fun t : ℕ => ‖(-n * θ.1) ^ t / (Nat.factorial t : ℝ)‖) := h.norm
    simpa only [F, norm_mul] using h'.mul_right ‖P θ‖
  have hrange (s : Finset MarkedParam) (hs : ν (s : Set MarkedParam) = 1) :
      ν (Set.range (⟨Subtype.val, Subtype.val_injective⟩ :
        (s : Set MarkedParam) ↪ MarkedParam)) = ν Set.univ := by
    have heq : Set.range (⟨Subtype.val, Subtype.val_injective⟩ :
        (s : Set MarkedParam) ↪ MarkedParam) = (s : Set MarkedParam) := by
      ext θ
      simp
    rw [heq, hs]
    simp
  obtain ⟨s, hs⟩ := hfinite
  let cell : (s : Set MarkedParam) ↪ MarkedParam :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hintegrable : Integrable (fun θ => ∑' t, ‖F t θ‖) ν := by
    apply Causalean.Mathlib.MeasureTheory.integrable_of_finite_atomic_support
      ν cell (fun _ => measurableSet_singleton _) (hrange s hs)
    apply Measurable.stronglyMeasurable
    apply Measurable.tsum
    intro t
    dsimp [F, P]
    fun_prop
  have hseries (θ : MarkedParam) :
      HasSum (fun t => F t θ) (Real.exp (-n * θ.1) * P θ) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (-n * θ.1)).mul_right (P θ)
    rw [← Real.exp_eq_exp_ℝ] at h
    simpa only [F] using h.congr_fun (fun t => by ring)
  have hinterchange :
      (∫ θ, Real.exp (-n * θ.1) * P θ ∂ν) =
        ∑' t, ∫ θ, F t θ ∂ν := by
    exact (MeasureTheory.hasSum_integral_of_dominated_convergence
      (fun t θ => ‖F t θ‖) hmeas hbound
      (Filter.Eventually.of_forall hsummable) hintegrable
      (Filter.Eventually.of_forall hseries)).tsum_eq.symm
  calc
    (predictiveLaw n ν).real {((u, v), w)} =
        ∫ θ, Real.exp (-n * θ.1) * P θ ∂ν := by
          rw [predictiveLaw_singleton hn ν (by
            apply le_antisymm
            · calc
                ν {θ : MarkedParam | 0 ≤ θ.1 ∧ 0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧
                    0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} ≤ ν Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            · calc
                (1 : ENNReal) = ν {θ | 0 ≤ θ.1 ∧ θ.1 ≤ b ∧
                    0 ≤ θ.2.1 ∧ θ.2.1 ≤ 1 ∧ 0 ≤ θ.2.2 ∧ θ.2.2 ≤ 1} := hsupport.symm
                _ ≤ _ := measure_mono (by
                  intro θ hθ
                  exact ⟨hθ.1, hθ.2.2.1, hθ.2.2.2.1,
                    hθ.2.2.2.2.1, hθ.2.2.2.2.2⟩)) u v w]
          apply integral_congr_ae
          filter_upwards [] with θ
          dsimp [P]
          ring
    _ = ∑' t, ∫ θ, F t θ ∂ν := hinterchange
    _ = _ := by
      apply tsum_congr
      intro t
      dsimp [F, P]
      rw [← integral_const_mul]
      congr 1
      funext θ
      rw [mul_pow (-n) θ.1 t,
        mul_pow (n * θ.1 * θ.2.1) θ.2.2 u,
        mul_pow (n * θ.1 * θ.2.1) (1 - θ.2.2) v,
        mul_pow (n * θ.1) (1 - θ.2.1) w]
      rw [mul_pow (θ.1 * θ.2.1) θ.2.2 u,
        mul_pow (θ.1 * θ.2.1) (1 - θ.2.2) v,
        mul_pow θ.1 (1 - θ.2.1) w]
      rw [mul_pow (n * θ.1) θ.2.1 u,
        mul_pow (n * θ.1) θ.2.1 v,
        mul_pow n θ.1 u, mul_pow n θ.1 v, mul_pow n θ.1 w,
        neg_pow]
      ring

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
