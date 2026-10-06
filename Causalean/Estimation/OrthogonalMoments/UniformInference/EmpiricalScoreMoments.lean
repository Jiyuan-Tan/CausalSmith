module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldRates
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldSquaredError
public import Causalean.Estimation.OrthogonalMoments.UniformInference.OracleNormal
public import Causalean.Stat.Concentration.TailBounds.Hoeffding

/-! # Uniform empirical score moments

Bounded oracle scores and foldwise L² approximation control the empirical
oracle and feasible score second moments uniformly over the law class.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

/-- For uniformly bounded oracle scores, the empirical oracle second
moment differs from its population value by a uniformly negligible amount. -/
theorem oracle_secondMoment_uniformOP
    {B vmin M3 : ℝ} (O : OracleConditions F B vmin M3) :
    F.UniformOP (fun n p ω =>
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (F.oracle p ((F.sample p).Z i ω)) ^ 2 - F.oracleVar p) := by
  intro ε hε
  let b : ℝ := B ^ 2 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hrate : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / b ^ 2)))
      atTop (𝓝 0) := by
    have hc : 0 < 2 * ε ^ 2 / b ^ 2 := by positivity
    have ht : Tendsto (fun n : ℕ => (n : ℝ) * (2 * ε ^ 2 / b ^ 2))
        atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hc
    have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul 2
    have hr (n : ℕ) :
        -2 * (n : ℝ) * ε ^ 2 / b ^ 2 =
          -((n : ℝ) * (2 * ε ^ 2 / b ^ 2)) := by ring
    have hreal : Tendsto (fun n : ℕ =>
        2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / b ^ 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, hr, mul_zero] using he
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  rw [ENNReal.tendsto_nhds_zero]
  intro ζ hζ
  have he := (ENNReal.tendsto_nhds_zero.mp hrate) ζ hζ
  filter_upwards [eventually_gt_atTop (0 : ℕ), he] with n hn htail
  apply le_trans _ htail
  refine iSup_le fun p => iSup_le fun hp => ?_
  haveI : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure (F.laws p) := by
    rw [← (F.sample p).law]
    exact Measure.isProbabilityMeasure_map ((F.sample p).meas 0).aemeasurable
  let f : Z → ℝ := fun z => (F.oracle p z) ^ 2
  have hf : Measurable f := (O.measurable p).pow_const 2
  have hbound : ∀ᵐ z ∂F.laws p, f z ∈ Set.Icc 0 b := by
    filter_upwards with z
    have hz := O.bounded n p hp z
    constructor
    · exact sq_nonneg _
    · dsimp [f, b]
      nlinarith [sq_nonneg (|F.oracle p z| - B), abs_nonneg (F.oracle p z),
        sq_abs (F.oracle p z)]
  have hh := Causalean.Stat.Concentration.hoeffding_abs_ge
    (F.sample p) hf (a := 0) (b := b) hb hbound n hn hε.le
  have heq : ∀ ω,
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (F.oracle p ((F.sample p).Z i ω)) ^ 2 - F.oracleVar p =
      (F.sample p).sampleMean f n ω - ∫ z, f z ∂F.laws p := by
    intro ω
    simp only [IIDSample.sampleMean, f, oracleVar]
  have htail : (F.sampleLaw p).real
      {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (F.oracle p ((F.sample p).Z i ω)) ^ 2 - F.oracleVar p|} ≤
      2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / b ^ 2) := by
    simpa only [heq, sub_zero, b] using hh
  have hfinite : F.sampleLaw p
      {ω | ε ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (F.oracle p ((F.sample p).Z i ω)) ^ 2 - F.oracleVar p|} ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp)
      (measure_mono (Set.subset_univ _))
  exact (ENNReal.ofReal_toReal hfinite).symm ▸
    ENNReal.ofReal_le_ofReal htail

/-- For [a cross-fitting family](hyp:F) satisfying [the foldwise rate conditions](hyp:R) and
[the oracle-score conditions](hyp:O), [the empirical second moment of the held-out estimated
scores minus the empirical second moment of the oracle scores vanishes in probability uniformly
over the law class](goal). -/
theorem score_secondMoment_approx_uniformOP
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    {B vmin M3 : ℝ}
    (R : RateConditions F r a b C δ) (O : OracleConditions F B vmin M3) :
    F.UniformOP (fun n p ω =>
      (n : ℝ)⁻¹ *
        (∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
          (F.score n p k ω ((F.sample p).Z i ω)) ^ 2) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (F.oracle p ((F.sample p).Z i ω)) ^ 2) := by
  /- Use the fold partition, then `s ^ 2 - o ^ 2 = (s-o)^2 + 2*o*(s-o)`.
  On each training good event the conditional expected average squared score
  difference is at most `r n ^ 2`; Markov and a finite union bound control
  this average uniformly. The cross term follows from a quadratic bound and
  the pointwise oracle bound `B`. -/
  classical
  let D (n : ℕ) (p : ι) (k : Fin K) (ω : Ω) : ℝ :=
    (n : ℝ)⁻¹ * ∑ i ∈ (F.split p).fold n k,
      (F.score n p k ω ((F.sample p).Z i ω) -
        F.oracle p ((F.sample p).Z i ω)) ^ 2
  have hD_nonneg (n : ℕ) (p : ι) (k : Fin K) (ω : Ω) :
      0 ≤ D n p k ω := by
    dsimp [D]
    positivity
  have htail (n : ℕ) (hn : 0 < n) (p : ι)
      (hp : p ∈ F.lawClass n) (k : Fin K)
      (q : ℝ) (hq : 0 < q) :
      F.sampleLaw p {ω | q ≤ D n p k ω} ≤
        δ n + ENNReal.ofReal ((r n) ^ 2 / q) := by
    have hmA :
        (MeasurableSpace.comap
          (fun ω (i : (F.split p).trainComplement n k) =>
            (F.sample p).Z i ω)
          inferInstance : MeasurableSpace Ω) ≤
          (inferInstance : MeasurableSpace Ω) := by
      intro s hs
      rcases hs with ⟨t, ht, rfl⟩
      exact (measurable_pi_iff.mpr
        fun i : (F.split p).trainComplement n k => (F.sample p).meas i) ht
    have hgood : MeasurableSet (R.good n p k) :=
      hmA _ (R.good_train n p k)
    have hD : Measurable (D n p k) := by
      dsimp [D]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i hi
      exact (((R.diff_meas n p k).comp
        (measurable_id.prodMk ((F.sample p).meas i))).pow_const 2)
    have hmarkov :
        F.sampleLaw p ({ω | q ≤ D n p k ω} ∩ R.good n p k) ≤
          ENNReal.ofReal ((r n) ^ 2 / q) := by
      have hsubset :
          {ω | q ≤ D n p k ω} ∩ R.good n p k ⊆
            {ω | ENNReal.ofReal q ≤ ENNReal.ofReal (D n p k ω)} := by
        intro ω hω
        exact ENNReal.ofReal_le_ofReal hω.1
      calc
        _ ≤ ((F.sampleLaw p).restrict (R.good n p k))
            {ω | ENNReal.ofReal q ≤ ENNReal.ofReal (D n p k ω)} := by
              rw [Measure.restrict_apply' hgood]
              exact measure_mono (fun ω hω => ⟨hsubset hω, hω.2⟩)
        _ ≤ (∫⁻ ω in R.good n p k,
              ENNReal.ofReal (D n p k ω) ∂F.sampleLaw p) /
              ENNReal.ofReal q :=
            meas_ge_le_lintegral_div
              hD.ennreal_ofReal.aemeasurable
              (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal ((r n) ^ 2) / ENNReal.ofReal q := by
              gcongr
              exact F.foldSquaredError_good_lintegral_le R n hn p k
        _ = ENNReal.ofReal ((r n) ^ 2 / q) := by
              exact (ENNReal.ofReal_div_of_pos hq).symm
    have hcover :
        {ω | q ≤ D n p k ω} ⊆
          (R.good n p k)ᶜ ∪
            ({ω | q ≤ D n p k ω} ∩ R.good n p k) := by
      intro ω hω
      by_cases hg : ω ∈ R.good n p k
      · exact Or.inr ⟨hω, hg⟩
      · exact Or.inl hg
    calc
      _ ≤ F.sampleLaw p ((R.good n p k)ᶜ ∪
          ({ω | q ≤ D n p k ω} ∩ R.good n p k)) :=
            measure_mono hcover
      _ ≤ F.sampleLaw p (R.good n p k)ᶜ +
          F.sampleLaw p ({ω | q ≤ D n p k ω} ∩ R.good n p k) :=
            measure_union_le _ _
      _ ≤ δ n + ENNReal.ofReal ((r n) ^ 2 / q) :=
            add_le_add (R.fail n p hp k) hmarkov
  intro ε hε
  have hK : (0 : ℝ) < K := by exact_mod_cast F.K_pos
  have hB1 : 0 < B + 1 := by linarith [O.B_nonneg]
  let t : ℝ := ε / (4 * (K : ℝ) * (B + 1))
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos hε (by positivity)
  have hfactor : 0 < 1 + 2 * B / t := by
    have : 0 ≤ 2 * B / t :=
      div_nonneg (mul_nonneg (by norm_num) O.B_nonneg) ht.le
    linarith
  let q : ℝ := ε / (4 * (K : ℝ) * (1 + 2 * B / t))
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos hε (by positivity)
  let E (n : ℕ) (p : ι) (k : Fin K) : Set Ω :=
    {ω | q ≤ D n p k ω}
  have hpair (p : ι) (n : ℕ) :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin K)))
        ((F.split p).fold n) := by
    intro k hk l hl hkl
    exact (F.split p).partition n k l hkl
  have horacle (p : ι) (n : ℕ) (ω : Ω) :
      (∑ i ∈ Finset.range n,
        (F.oracle p ((F.sample p).Z i ω)) ^ 2) =
      ∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
        (F.oracle p ((F.sample p).Z i ω)) ^ 2 := by
    rw [← (F.split p).cover n, Finset.sum_biUnion (hpair p n)]
  have hpoint (n : ℕ) (hn : 0 < n) (p : ι)
      (hp : p ∈ F.lawClass n) (ω : Ω) :
      ε ≤ |(n : ℝ)⁻¹ *
        (∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
          (F.score n p k ω ((F.sample p).Z i ω)) ^ 2) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          (F.oracle p ((F.sample p).Z i ω)) ^ 2| →
      ω ∈ ⋃ k : Fin K, E n p k := by
    intro hω
    by_contra hnot
    have hsmall (k : Fin K) : D n p k ω ≤ q := by
      have hk : ω ∉ E n p k := by
        intro hmem
        exact hnot (Set.mem_iUnion.mpr ⟨k, hmem⟩)
      exact le_of_lt (lt_of_not_ge hk)
    have hcross (k : Fin K) (i : ℕ) :
        let s := F.score n p k ω ((F.sample p).Z i ω)
        let o := F.oracle p ((F.sample p).Z i ω)
        |s ^ 2 - o ^ 2| ≤
          (1 + 2 * B / t) * (s - o) ^ 2 + B * t / 2 := by
      dsimp
      have hb := O.bounded n p hp ((F.sample p).Z i ω)
      have hy := sq_nonneg
        (|F.score n p k ω ((F.sample p).Z i ω) -
          F.oracle p ((F.sample p).Z i ω)| - t / 2)
      have hsq := sq_abs
        (F.score n p k ω ((F.sample p).Z i ω) -
          F.oracle p ((F.sample p).Z i ω))
      have hid :
          (F.score n p k ω ((F.sample p).Z i ω)) ^ 2 -
            (F.oracle p ((F.sample p).Z i ω)) ^ 2 =
          (F.score n p k ω ((F.sample p).Z i ω) -
            F.oracle p ((F.sample p).Z i ω)) ^ 2 +
          2 * F.oracle p ((F.sample p).Z i ω) *
            (F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) := by ring
      rw [hid]
      have habs := abs_add_le
        ((F.score n p k ω ((F.sample p).Z i ω) -
          F.oracle p ((F.sample p).Z i ω)) ^ 2)
        (2 * F.oracle p ((F.sample p).Z i ω) *
          (F.score n p k ω ((F.sample p).Z i ω) -
            F.oracle p ((F.sample p).Z i ω)))
      have habs' :
          |(F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) ^ 2 +
            2 * F.oracle p ((F.sample p).Z i ω) *
              (F.score n p k ω ((F.sample p).Z i ω) -
                F.oracle p ((F.sample p).Z i ω))| ≤
          (F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) ^ 2 +
            2 * |F.oracle p ((F.sample p).Z i ω)| *
              |F.score n p k ω ((F.sample p).Z i ω) -
                F.oracle p ((F.sample p).Z i ω)| := by
        calc
          _ ≤ |(F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) ^ 2| +
            |2 * F.oracle p ((F.sample p).Z i ω) *
              (F.score n p k ω ((F.sample p).Z i ω) -
                F.oracle p ((F.sample p).Z i ω))| := habs
          _ = _ := by
            rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul,
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hterm :
          2 * |F.oracle p ((F.sample p).Z i ω)| *
            |F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)| ≤
          2 * B * |F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)| := by
        gcongr
      have hquad :
          t * |F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)| ≤
          (F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) ^ 2 + t ^ 2 / 4 := by
        nlinarith
      have hb0 := O.B_nonneg
      have hupper :
          2 * B * |F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)| ≤
          (2 * B / t) *
            (F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) ^ 2 + B * t / 2 := by
        have hc : 0 ≤ 2 * B / t := div_nonneg (by positivity) ht.le
        have hh := mul_le_mul_of_nonneg_left hquad hc
        have heq1 : (2 * B / t) * (t *
            |F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)|) =
            2 * B * |F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)| := by
          field_simp
        have heq2 : (2 * B / t) *
            ((F.score n p k ω ((F.sample p).Z i ω) -
              F.oracle p ((F.sample p).Z i ω)) ^ 2 + t ^ 2 / 4) =
            (2 * B / t) *
              (F.score n p k ω ((F.sample p).Z i ω) -
                F.oracle p ((F.sample p).Z i ω)) ^ 2 + B * t / 2 := by
          field_simp
          ring
        simpa only [heq1, heq2] using hh
      nlinarith
    have hfold (k : Fin K) :
        |(n : ℝ)⁻¹ * ∑ i ∈ (F.split p).fold n k,
          ((F.score n p k ω ((F.sample p).Z i ω)) ^ 2 -
            (F.oracle p ((F.sample p).Z i ω)) ^ 2)| ≤
        (1 + 2 * B / t) * D n p k ω + B * t / 2 := by
      have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hcard : ((F.split p).fold n k).card ≤ n := by
        have hs : (F.split p).fold n k ⊆ Finset.range n := by
          intro i hi
          rw [← (F.split p).cover n]
          exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hi⟩
        simpa using Finset.card_le_card hs
      calc
        _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ (F.split p).fold n k,
            |(F.score n p k ω ((F.sample p).Z i ω)) ^ 2 -
              (F.oracle p ((F.sample p).Z i ω)) ^ 2| := by
              rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hnR.le)]
              exact mul_le_mul_of_nonneg_left
                (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hnR.le)
        _ ≤ (n : ℝ)⁻¹ * ∑ i ∈ (F.split p).fold n k,
            ((1 + 2 * B / t) *
              (F.score n p k ω ((F.sample p).Z i ω) -
                F.oracle p ((F.sample p).Z i ω)) ^ 2 + B * t / 2) := by
              gcongr with i hi
              exact hcross k i
        _ = (1 + 2 * B / t) * D n p k ω +
            (n : ℝ)⁻¹ * (((F.split p).fold n k).card : ℝ) * (B * t / 2) := by
              simp only [Finset.sum_add_distrib, Finset.sum_const,
                nsmul_eq_mul, ← Finset.mul_sum]
              dsimp [D]
              ring
        _ ≤ (1 + 2 * B / t) * D n p k ω + B * t / 2 := by
              have hcardR : (((F.split p).fold n k).card : ℝ) ≤ n := by
                exact_mod_cast hcard
              have hratio : (n : ℝ)⁻¹ *
                  (((F.split p).fold n k).card : ℝ) ≤ 1 := by
                apply (inv_mul_le_iff₀ hnR).mpr
                simpa using hcardR
              have hBt : 0 ≤ B * t / 2 :=
                div_nonneg (mul_nonneg O.B_nonneg ht.le)
                  (by norm_num : (0 : ℝ) ≤ 2)
              have hh := mul_le_mul_of_nonneg_right hratio hBt
              nlinarith
    have hqK : (K : ℝ) * q = ε / (4 * (1 + 2 * B / t)) := by
      dsimp [q]
      field_simp
    have htB : (K : ℝ) * (B * t / 2) ≤ ε / 4 := by
      have hbfrac : B / (B + 1) ≤ 1 :=
        (div_le_iff₀ hB1).2 (by linarith)
      have hident : (K : ℝ) * (B * t / 2) =
          ε / 8 * (B / (B + 1)) := by
        dsimp [t]
        field_simp
        ring
      rw [hident]
      have hh := mul_le_mul_of_nonneg_left hbfrac
        (by positivity : 0 ≤ ε / 8)
      nlinarith
    have hbound :
        |(n : ℝ)⁻¹ *
          (∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
            (F.score n p k ω ((F.sample p).Z i ω)) ^ 2) -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            (F.oracle p ((F.sample p).Z i ω)) ^ 2| < ε := by
      calc
        _ = |∑ k : Fin K, (n : ℝ)⁻¹ *
            ∑ i ∈ (F.split p).fold n k,
              ((F.score n p k ω ((F.sample p).Z i ω)) ^ 2 -
                (F.oracle p ((F.sample p).Z i ω)) ^ 2)| := by
                  rw [horacle p n ω]
                  congr 1
                  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [← Finset.sum_sub_distrib]
        _ ≤ ∑ k : Fin K, |(n : ℝ)⁻¹ *
            ∑ i ∈ (F.split p).fold n k,
              ((F.score n p k ω ((F.sample p).Z i ω)) ^ 2 -
                (F.oracle p ((F.sample p).Z i ω)) ^ 2)| :=
                  Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin K,
            ((1 + 2 * B / t) * D n p k ω + B * t / 2) :=
              Finset.sum_le_sum (fun k hk => hfold k)
        _ ≤ ∑ _k : Fin K,
            ((1 + 2 * B / t) * q + B * t / 2) := by
              apply Finset.sum_le_sum
              intro k hk
              gcongr
              exact hsmall k
        _ = (1 + 2 * B / t) * ((K : ℝ) * q) +
            (K : ℝ) * (B * t / 2) := by simp; ring
        _ < ε := by
          rw [hqK]
          have hscale :
              (1 + 2 * B / t) *
                (ε / (4 * (1 + 2 * B / t))) = ε / 4 := by
            calc
              _ = ((1 + 2 * B / t) * ε) /
                  (4 * (1 + 2 * B / t)) := by ring
              _ = ε / 4 := by
                apply (div_eq_iff (mul_ne_zero (by norm_num)
                  (ne_of_gt hfactor))).2
                ring
          rw [hscale]
          linarith
    linarith
  have hrate : Tendsto (fun n : ℕ =>
      ENNReal.ofReal ((r n) ^ 2 / q)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      ((R.r_tendsto.pow 2).div_const q)
  have hub : Tendsto (fun n : ℕ =>
      (K : ℝ≥0∞) * (δ n + ENNReal.ofReal ((r n) ^ 2 / q)))
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        δ n + ENNReal.ofReal ((r n) ^ 2 / q)) atTop (𝓝 0) := by
      convert R.δ_tendsto.add hrate using 1 <;> simp
    convert ENNReal.Tendsto.const_mul hsum
      (Or.inr (by simp : (K : ℝ≥0∞) ≠ ⊤)) using 1 <;> simp
  rw [ENNReal.tendsto_nhds_zero]
  intro ζ hζ
  have hevent := (ENNReal.tendsto_nhds_zero.mp hub) ζ hζ
  filter_upwards [eventually_gt_atTop (0 : ℕ), hevent]
    with n hn hu
  apply le_trans _ hu
  refine iSup_le fun p => iSup_le fun hp => ?_
  calc
    _ ≤ F.sampleLaw p (⋃ k : Fin K, E n p k) :=
      measure_mono (fun ω hω => hpoint n hn p hp ω hω)
    _ ≤ ∑ k : Fin K, F.sampleLaw p (E n p k) :=
      measure_iUnion_fintype_le (F.sampleLaw p) (E n p)
    _ ≤ ∑ _k : Fin K,
        (δ n + ENNReal.ofReal ((r n) ^ 2 / q)) :=
      Finset.sum_le_sum (fun k hk => htail n hn p hp k q hq)
    _ = _ := by simp [mul_add]


end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
