module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldMoments

/-! # Uniform foldwise tail bounds and asymptotic linearity

Under the uniform score-rate conditions of `FoldMoments`, conditional independence of the
evaluation fold converts the L² rate into a uniform centered-sum tail bound. The drift rate then
yields class-indexed root-sample-size asymptotic linearity of the cross-fitted estimator.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

/-- A training-measurable fold with L² score error at most `r n` has a
centered held-out tail of order `r n` plus its good-event failure probability,
uniformly for each law in the class. -/
theorem foldCentered_tail
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    (R : RateConditions F r a b C δ)
    (n : ℕ) (p : ι) (hp : p ∈ F.lawClass n) (k : Fin K)
    (ε : ℝ) (hε : 0 < ε) :
    F.sampleLaw p {ω | ε ≤ |F.foldCentered n p k ω|} ≤
      δ n + ENNReal.ofReal ((r n) ^ 2 / ε ^ 2) := by
  letI : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  letI : IsProbabilityMeasure (F.laws p) := by
    rw [← (F.sample p).law]
    exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
  have hmA :
      (MeasurableSpace.comap
        (fun ω (i : (F.split p).trainComplement n k) => (F.sample p).Z i ω)
        inferInstance : MeasurableSpace Ω) ≤ (inferInstance : MeasurableSpace Ω) := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact (measurable_pi_iff.mpr
      fun i : (F.split p).trainComplement n k => (F.sample p).meas i) ht
  have hgood : MeasurableSet (R.good n p k) :=
    hmA _ (R.good_train n p k)
  have hdiffMean :
      Measurable (fun ω => ∫ z,
        F.score n p k ω z - F.oracle p z ∂F.laws p) :=
    (R.diff_meas n p k).stronglyMeasurable.integral_prod_right.measurable
  have hfold : Measurable (F.foldCentered n p k) := by
    unfold foldCentered
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact ((R.diff_meas n p k).comp
      (measurable_id.prodMk ((F.sample p).meas i))).sub hdiffMean
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  let e : ℝ≥0∞ := ENNReal.ofReal (ε ^ 2)
  have he0 : e ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hεsq)
  have heTop : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov :
      (F.sampleLaw p) ({ω | ε ≤ |F.foldCentered n p k ω|} ∩ R.good n p k) ≤
        ENNReal.ofReal ((r n) ^ 2 / ε ^ 2) := by
    have hsubset :
        {ω | ε ≤ |F.foldCentered n p k ω|} ∩ R.good n p k ⊆
          {ω | e ≤ ENNReal.ofReal ((F.foldCentered n p k ω) ^ 2)} := by
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      have hs := pow_le_pow_left₀ (le_of_lt hε) hω.1 2
      simpa only [sq_abs] using hs
    calc
      (F.sampleLaw p) ({ω | ε ≤ |F.foldCentered n p k ω|} ∩ R.good n p k)
          ≤ ((F.sampleLaw p).restrict (R.good n p k))
              {ω | e ≤ ENNReal.ofReal ((F.foldCentered n p k ω) ^ 2)} := by
            rw [Measure.restrict_apply' hgood]
            exact measure_mono (fun ω hω => ⟨hsubset hω, hω.2⟩)
      _ ≤ (∫⁻ ω in R.good n p k,
            ENNReal.ofReal ((F.foldCentered n p k ω) ^ 2) ∂F.sampleLaw p) / e :=
          meas_ge_le_lintegral_div
            ((hfold.pow_const 2).ennreal_ofReal.aemeasurable) he0 heTop
      _ ≤ ENNReal.ofReal ((r n) ^ 2) / e := by
          gcongr
          exact F.foldCentered_good_sq_lintegral_le R n p k
      _ = ENNReal.ofReal ((r n) ^ 2 / ε ^ 2) := by
          exact (ENNReal.ofReal_div_of_pos hεsq).symm
  have hcover :
      {ω | ε ≤ |F.foldCentered n p k ω|} ⊆
        (R.good n p k)ᶜ ∪
          ({ω | ε ≤ |F.foldCentered n p k ω|} ∩ R.good n p k) := by
    intro ω hω
    by_cases hg : ω ∈ R.good n p k
    · exact Or.inr ⟨hω, hg⟩
    · exact Or.inl hg
  calc
    (F.sampleLaw p) {ω | ε ≤ |F.foldCentered n p k ω|}
        ≤ (F.sampleLaw p) ((R.good n p k)ᶜ ∪
            ({ω | ε ≤ |F.foldCentered n p k ω|} ∩ R.good n p k)) :=
          measure_mono hcover
    _ ≤ (F.sampleLaw p) (R.good n p k)ᶜ +
          (F.sampleLaw p) ({ω | ε ≤ |F.foldCentered n p k ω|} ∩ R.good n p k) :=
        measure_union_le _ _
    _ ≤ δ n + ENNReal.ofReal ((r n) ^ 2 / ε ^ 2) :=
        add_le_add (R.fail n p hp k) hmarkov

/-- If [the foldwise rate conditions hold — on training-measurable good events whose failure
probability vanishes uniformly over the law class, the L² score error and the root-sample-size-scaled
mean drift are bounded by vanishing rates](hyp:R), then [the root-sample-size-scaled cross-fitted estimator error equals the oracle
empirical score sum up to a remainder that is uniformly negligible in probability](goal). -/
theorem uniform_asymptotic_linearity
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    (R : RateConditions F r a b C δ) :
    F.UniformOP (fun n p ω =>
      Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
        F.oracleSum n p ω) := by
  classical
  have hpair (p : ι) (n : ℕ) :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin K)))
        ((F.split p).fold n) := by
    intro k hk l hl hkl
    exact (F.split p).partition n k l hkl
  have hcard (p : ι) (n : ℕ) :
      (∑ k : Fin K, ((F.split p).fold n k).card) = n := by
    rw [← Finset.card_biUnion (hpair p n), (F.split p).cover]
    simp
  have horacle (p : ι) (n : ℕ) (ω : Ω) :
      (∑ i ∈ Finset.range n, F.oracle p ((F.sample p).Z i ω)) =
      ∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
        F.oracle p ((F.sample p).Z i ω) := by
    rw [← (F.split p).cover n, Finset.sum_biUnion (hpair p n)]
  have hfoldid (p : ι) (n : ℕ) (k : Fin K) (ω : Ω) :
      (Real.sqrt (n : ℝ))⁻¹ *
        (∑ i ∈ (F.split p).fold n k,
          (F.score n p k ω ((F.sample p).Z i ω) -
            F.oracle p ((F.sample p).Z i ω))) =
      F.foldCentered n p k ω +
        (Real.sqrt (n : ℝ))⁻¹ *
          (((F.split p).fold n k).card : ℝ) *
            ∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p := by
    simp [foldCentered, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  have hdecomp (n : ℕ) (hn : 0 < n) (p : ι) (ω : Ω) :
      Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
          F.oracleSum n p ω =
        (∑ k : Fin K, F.foldCentered n p k ω) +
          (Real.sqrt (n : ℝ))⁻¹ *
            ∑ k : Fin K, (((F.split p).fold n k).card : ℝ) *
              ∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p := by
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have hscale : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
        (Real.sqrt (n : ℝ))⁻¹ := by
      field_simp
      nlinarith [Real.sq_sqrt (le_of_lt hnR)]
    calc
      _ = ∑ k : Fin K, (Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ (F.split p).fold n k,
              (F.score n p k ω ((F.sample p).Z i ω) -
                F.oracle p ((F.sample p).Z i ω)) := by
          rw [estimate, oracleSum, horacle]
          simp only [add_sub_cancel_left]
          rw [← mul_assoc, hscale]
          simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      _ = _ := by
          simp_rw [hfoldid p n]
          rw [Finset.sum_add_distrib]
          simp only [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          ring
  have hbound (n : ℕ) (hn : 0 < n) (p : ι) (ω : Ω)
      (hgood : ∀ k : Fin K, ω ∈ R.good n p k) :
      |Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
          F.oracleSum n p ω| ≤
        (∑ k : Fin K, |F.foldCentered n p k ω|) +
          Real.sqrt (n : ℝ) * (C * a n * b n) := by
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have hscale : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) =
        Real.sqrt (n : ℝ) := by
      field_simp
      nlinarith [Real.sq_sqrt (le_of_lt hnR)]
    have hsum :
        |∑ k : Fin K, (((F.split p).fold n k).card : ℝ) *
            ∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p| ≤
          (n : ℝ) * (C * a n * b n) := by
      calc
        _ ≤ ∑ k : Fin K, |(((F.split p).fold n k).card : ℝ) *
            ∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin K, (((F.split p).fold n k).card : ℝ) *
            |∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p| := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        _ ≤ ∑ k : Fin K, (((F.split p).fold n k).card : ℝ) *
            (C * a n * b n) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (R.drift n p k ω (hgood k))
            (Nat.cast_nonneg _)
        _ = (n : ℝ) * (C * a n * b n) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum, hcard]
    rw [hdecomp n hn p ω]
    calc
      _ ≤ |∑ k : Fin K, F.foldCentered n p k ω| +
            |(Real.sqrt (n : ℝ))⁻¹ *
              ∑ k : Fin K, (((F.split p).fold n k).card : ℝ) *
                ∫ z, F.score n p k ω z - F.oracle p z ∂F.laws p| := abs_add_le _ _
      _ ≤ (∑ k : Fin K, |F.foldCentered n p k ω|) +
            (Real.sqrt (n : ℝ))⁻¹ *
              ((n : ℝ) * (C * a n * b n)) := by
          gcongr
          · exact Finset.abs_sum_le_sum_abs _ _
          · simpa [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hsqrt))]
              using mul_le_mul_of_nonneg_left hsum
                (inv_nonneg.mpr (le_of_lt hsqrt))
      _ = _ := by rw [← mul_assoc, hscale]
  intro ε hε
  let q : ℝ := ε / (2 * (K : ℝ))
  have hK : (0 : ℝ) < K := by exact_mod_cast F.K_pos
  have hq : 0 < q := div_pos hε (by positivity)
  let E (n : ℕ) (p : ι) (k : Fin K) : Set Ω :=
    (R.good n p k)ᶜ ∪ {ω | q ≤ |F.foldCentered n p k ω|}
  have hE (n : ℕ) (p : ι) (hp : p ∈ F.lawClass n) (k : Fin K) :
      F.sampleLaw p (E n p k) ≤
        δ n + (δ n + ENNReal.ofReal ((r n) ^ 2 / q ^ 2)) := by
    calc
      _ ≤ F.sampleLaw p (R.good n p k)ᶜ +
            F.sampleLaw p {ω | q ≤ |F.foldCentered n p k ω|} :=
          measure_union_le _ _
      _ ≤ δ n + (δ n + ENNReal.ofReal ((r n) ^ 2 / q ^ 2)) :=
          add_le_add (R.fail n p hp k) (F.foldCentered_tail R n p hp k q hq)
  have hqK : (K : ℝ) * q = ε / 2 := by
    dsimp [q]
    field_simp
  have hpoint (n : ℕ) (hn : 0 < n)
      (hd : Real.sqrt (n : ℝ) * (C * a n * b n) < ε / 2)
      (p : ι) (ω : Ω) :
      ε ≤ |Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) -
        F.oracleSum n p ω| → ω ∈ ⋃ k : Fin K, E n p k := by
    intro hω
    by_contra hnot
    have hno (k : Fin K) : ω ∉ E n p k := by
      intro hk
      exact hnot (Set.mem_iUnion.mpr ⟨k, hk⟩)
    have hgood (k : Fin K) : ω ∈ R.good n p k := by
      by_contra hg
      exact hno k (Or.inl hg)
    have hsmall (k : Fin K) : |F.foldCentered n p k ω| ≤ q := by
      exact le_of_lt (lt_of_not_ge (fun h => hno k (Or.inr h)))
    have hsum : (∑ k : Fin K, |F.foldCentered n p k ω|) ≤ ε / 2 := by
      calc
        _ ≤ ∑ _k : Fin K, q := Finset.sum_le_sum (fun k hk => hsmall k)
        _ = (K : ℝ) * q := by simp
        _ = ε / 2 := hqK
    have hb := hbound n hn p ω hgood
    linarith
  have hprob (n : ℕ) (hn : 0 < n)
      (hd : Real.sqrt (n : ℝ) * (C * a n * b n) < ε / 2)
      (p : ι) (hp : p ∈ F.lawClass n) :
      F.sampleLaw p {ω | ε ≤ |Real.sqrt (n : ℝ) *
          (F.estimate n p ω - F.target p) - F.oracleSum n p ω|} ≤
        (K : ℝ≥0∞) *
          (δ n + (δ n + ENNReal.ofReal ((r n) ^ 2 / q ^ 2))) := by
    calc
      _ ≤ F.sampleLaw p (⋃ k : Fin K, E n p k) :=
          measure_mono (fun ω hω => hpoint n hn hd p ω hω)
      _ ≤ ∑ k : Fin K, F.sampleLaw p (E n p k) :=
          measure_iUnion_fintype_le (F.sampleLaw p) (E n p)
      _ ≤ ∑ _k : Fin K,
          (δ n + (δ n + ENNReal.ofReal ((r n) ^ 2 / q ^ 2))) :=
          Finset.sum_le_sum (fun k hk => hE n p hp k)
      _ = _ := by simp [mul_add]
  have hdrift : Tendsto (fun n : ℕ =>
      Real.sqrt (n : ℝ) * (C * a n * b n)) atTop (𝓝 0) := by
    convert R.sqrt_product_tendsto.const_mul C using 1
    · funext n; ring
    · simp
  have hdrift_event : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) * (C * a n * b n) < ε / 2 :=
    hdrift.eventually_lt_const (half_pos hε)
  have hrate : Tendsto (fun n : ℕ => ENNReal.ofReal ((r n) ^ 2 / q ^ 2))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      ((R.r_tendsto.pow 2).div_const (q ^ 2))
  have hub : Tendsto (fun n : ℕ =>
      (K : ℝ≥0∞) *
        (δ n + (δ n + ENNReal.ofReal ((r n) ^ 2 / q ^ 2))))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        δ n + (δ n + ENNReal.ofReal ((r n) ^ 2 / q ^ 2)))
        atTop (𝓝 0) := by
      convert R.δ_tendsto.add (R.δ_tendsto.add hrate) using 1 <;> simp
    convert ENNReal.Tendsto.const_mul hsum (Or.inr (by simp : (K : ℝ≥0∞) ≠ ⊤))
      using 1 <;> simp
  rw [ENNReal.tendsto_nhds_zero]
  intro ζ hζ
  have hevent := (ENNReal.tendsto_nhds_zero.mp hub) ζ hζ
  filter_upwards [eventually_gt_atTop (0 : ℕ), hdrift_event, hevent]
    with n hn hd hu
  refine (le_trans ?_ hu)
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  exact hprob n hn hd p hp

end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
