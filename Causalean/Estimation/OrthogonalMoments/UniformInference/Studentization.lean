module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.GaussianTransfer
public import Causalean.Estimation.OrthogonalMoments.UniformInference.VarianceConsistency

/-! # Uniform studentized Gaussian inference

Uniform asymptotic linearity, quantitative oracle normal approximation, and
feasible variance consistency imply uniform studentized Gaussian convergence.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

private theorem gaussian_tail_exists (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧
      ((gaussianReal 0 1) (Set.Iic (-M))).toReal < η ∧
      1 - ((gaussianReal 0 1) (Set.Iic M)).toReal < η := by
  let G : ℝ → ℝ := fun x => ((gaussianReal 0 1) (Set.Iic x)).toReal
  have heq : G = ⇑(cdf (gaussianReal 0 1)) := by
    funext x
    exact (cdf_eq_real (gaussianReal 0 1) x).symm
  have htop : Tendsto G atTop (𝓝 1) := by
    rw [heq]
    exact tendsto_cdf_atTop (gaussianReal 0 1)
  have hbot : Tendsto (fun x : ℝ => G (-x)) atTop (𝓝 0) := by
    rw [heq]
    exact (tendsto_cdf_atBot (gaussianReal 0 1)).comp tendsto_neg_atTop_atBot
  have hev1 : ∀ᶠ x : ℝ in atTop, 1 - G x < η :=
    (Filter.Tendsto.eventually (tendsto_const_nhds.sub htop)
      (eventually_lt_nhds (by simpa using hη)))
  have hev2 : ∀ᶠ x : ℝ in atTop, G (-x) < η :=
    hbot.eventually (eventually_lt_nhds hη)
  obtain ⟨M, ⟨hM, hm1⟩, hm2⟩ :=
    (Filter.Eventually.exists (Filter.Eventually.and
      (Filter.Eventually.and (eventually_gt_atTop (0 : ℝ)) hev1) hev2))
  exact ⟨M, hM, hm2, hm1⟩

private theorem uniformGaussian_tight
    (X : ℕ → ι → Ω → ℝ)
    (hX : F.UniformGaussian X)
    (hXm : ∀ n p, Measurable (X n p))
    (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
      ∀ p : ι, p ∈ F.lawClass n →
        F.sampleLaw p {ω | M ≤ |X n p ω|} ≤ ENNReal.ofReal η := by
  obtain ⟨m, hm, hleft, hright⟩ := gaussian_tail_exists (η / 4) (by positivity)
  refine ⟨m + 1, by linarith, ?_⟩
  have hgev := (ENNReal.tendsto_nhds_zero.mp hX)
    (ENNReal.ofReal (η / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  filter_upwards [hgev] with n hn
  intro p hp
  let μ := F.sampleLaw p
  haveI : IsProbabilityMeasure μ := (F.sample p).indep.isProbabilityMeasure
  let Y := X n p
  let G : ℝ → ℝ := fun x => ((gaussianReal 0 1) (Set.Iic x)).toReal
  have herror (x : ℝ) :
      |μ.real {ω | Y ω ≤ x} - G x| ≤ η / 4 := by
    have he : ENNReal.ofReal |μ.real {ω | Y ω ≤ x} - G x| ≤
        ENNReal.ofReal (η / 4) :=
      (le_iSup_of_le p (le_iSup_of_le hp
        (le_iSup (fun t : ℝ => ENNReal.ofReal
          |μ.real {ω | X n p ω ≤ t} - G t|) x))).trans hn
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  have hmeas : MeasurableSet {ω | Y ω ≤ m} := by
    exact (hXm n p) measurableSet_Iic
  have hsubset :
      {ω | m + 1 ≤ |Y ω|} ⊆
        {ω | Y ω ≤ -m} ∪ ({ω | Y ω ≤ m})ᶜ := by
    intro ω hω
    change m + 1 ≤ |Y ω| at hω
    by_cases h : Y ω ≤ -m
    · exact Or.inl h
    · right
      change ¬ Y ω ≤ m
      rcases le_total (Y ω) 0 with hneg | hpos
      · rw [abs_of_nonpos hneg] at hω
        linarith
      · rw [abs_of_nonneg hpos] at hω
        linarith
  have htail : μ.real {ω | m + 1 ≤ |Y ω|} ≤
      μ.real {ω | Y ω ≤ -m} + (1 - μ.real {ω | Y ω ≤ m}) := by
    calc
      _ ≤ μ.real ({ω | Y ω ≤ -m} ∪ ({ω | Y ω ≤ m})ᶜ) :=
        measureReal_mono hsubset
      _ ≤ μ.real {ω | Y ω ≤ -m} + μ.real ({ω | Y ω ≤ m})ᶜ :=
        measureReal_union_le _ _
      _ = _ := by rw [measureReal_compl hmeas]; simp
  have hl := herror (-m)
  have hr := herror m
  rw [abs_le] at hl hr
  have hreal : μ.real {ω | m + 1 ≤ |Y ω|} ≤ η := by
    dsimp [G] at hleft hright hl hr
    linarith
  have hfinite : μ {ω | m + 1 ≤ |Y ω|} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _))
  exact (ENNReal.ofReal_toReal hfinite).symm ▸
    ENNReal.ofReal_le_ofReal hreal

private theorem student_pointwise
    (A S V v c M ε : ℝ) (hc : 0 < c) (hM : 0 ≤ M) (hε : 0 < ε)
    (hV0 : 0 ≤ V) (hv0 : 0 ≤ v)
    (hV : c ≤ Real.sqrt V) (hv : c ≤ Real.sqrt v)
    (hlin : |A - S| ≤ ε * c / 4)
    (hvar : |V - v| ≤ ε * c ^ 2 / (4 * (M + 1)))
    (hX : |S / Real.sqrt v| ≤ M) :
    |A / Real.sqrt V - S / Real.sqrt v| ≤ ε := by
  have hrv : 0 < Real.sqrt V := lt_of_lt_of_le hc hV
  have hrv' : 0 < Real.sqrt v := lt_of_lt_of_le hc hv
  have hsV : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV0
  have hsv : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv0
  have hfactor : |V - v| =
      |Real.sqrt v - Real.sqrt V| * (Real.sqrt V + Real.sqrt v) := by
    calc
      _ = |(Real.sqrt V - Real.sqrt v) * (Real.sqrt V + Real.sqrt v)| := by
        congr 1
        nlinarith [hsV, hsv]
      _ = _ := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.sqrt V + Real.sqrt v by positivity)]
        exact congrArg (fun t : ℝ => t * (Real.sqrt V + Real.sqrt v))
          (abs_sub_comm (Real.sqrt V) (Real.sqrt v))
  have hroot : |Real.sqrt v - Real.sqrt V| * Real.sqrt v ≤ |V - v| := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg V])
      (abs_nonneg _)
  have hroot' : |Real.sqrt v - Real.sqrt V| ≤
      (ε * c ^ 2 / (4 * (M + 1))) / c := by
    apply (le_div_iff₀ hc).mpr
    calc
      _ ≤ |Real.sqrt v - Real.sqrt V| * Real.sqrt v := by
        gcongr
      _ ≤ |V - v| := hroot
      _ ≤ _ := hvar
  have heq : A / Real.sqrt V - S / Real.sqrt v =
      (A - S) / Real.sqrt V +
        (S / Real.sqrt v) * (Real.sqrt v - Real.sqrt V) / Real.sqrt V := by
    field_simp
    ring
  rw [heq]
  have htri : |(A - S) / Real.sqrt V +
        (S / Real.sqrt v) * (Real.sqrt v - Real.sqrt V) / Real.sqrt V| ≤
      |A - S| / Real.sqrt V +
        |S / Real.sqrt v| * |Real.sqrt v - Real.sqrt V| / Real.sqrt V := by
    simpa [abs_div, abs_mul, abs_of_pos hrv] using
      (abs_add_le ((A - S) / Real.sqrt V)
        ((S / Real.sqrt v) * (Real.sqrt v - Real.sqrt V) / Real.sqrt V))
  have hfirst : |A - S| / Real.sqrt V ≤ ε / 4 := by
    apply (div_le_iff₀ hrv).mpr
    calc
      _ ≤ ε * c / 4 := hlin
      _ ≤ ε / 4 * Real.sqrt V := by
        nlinarith [mul_le_mul_of_nonneg_left hV (show 0 ≤ ε / 4 by positivity)]
  have hsecond :
      |S / Real.sqrt v| * |Real.sqrt v - Real.sqrt V| / Real.sqrt V ≤
        ε / 4 := by
    calc
      _ ≤ M * ((ε * c ^ 2 / (4 * (M + 1))) / c) / c := by
        gcongr
      _ ≤ ε / 4 := by
        have hM1 : 0 < M + 1 := by linarith
        field_simp
        nlinarith
  linarith

/-- For [a cross-fitting family](hyp:F) satisfying [the foldwise rate conditions](hyp:R) and
[the oracle-score conditions](hyp:O), [the studentized cross-fitted estimator converges to the
standard Gaussian in Kolmogorov distance uniformly over the law class](goal).

The proof combines uniform asymptotic linearity, the oracle Berry–Esseen approximation, and
consistency of the feasible variance. -/
theorem student_uniformGaussian
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    {B vmin M3 : ℝ}
    (R : RateConditions F r a b C δ) (O : OracleConditions F B vmin M3) :
    F.UniformGaussian F.student := by
  apply F.uniformGaussian_of_uniformOP_difference
    F.standardizedOracle F.student (F.standardizedOracle_uniformGaussian O)
  have hlinear := F.uniform_asymptotic_linearity R
  have hvariance := F.scoreVar_uniform_consistent R O
  have hsmall := F.scoreVar_small_uniformly_rare R O
  have hmeas (n : ℕ) (p : ι) :
      Measurable (F.standardizedOracle n p) := by
    unfold standardizedOracle oracleSum
    apply Measurable.div_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (O.measurable p).comp ((F.sample p).meas i)
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro ζ hζ
  by_cases hζtop : ζ = ⊤
  · subst ζ
    exact Filter.Eventually.of_forall (fun _ => le_top)
  let η : ℝ := ζ.toReal / 4
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (ENNReal.toReal_pos hζ.ne' hζtop) (by norm_num)
  obtain ⟨M, hM, hMtight⟩ :=
    F.uniformGaussian_tight F.standardizedOracle
      (F.standardizedOracle_uniformGaussian O) hmeas η hη
  let c : ℝ := Real.sqrt (vmin / 2)
  have hc : 0 < c := Real.sqrt_pos.2 (by linarith [O.vmin_pos])
  let tL : ℝ := ε * c / 8
  let tV : ℝ := ε * c ^ 2 / (8 * (M + 1))
  have htL : 0 < tL := by dsimp [tL]; positivity
  have htV : 0 < tV := by dsimp [tV]; positivity
  have hLev := (ENNReal.tendsto_nhds_zero.mp (hlinear tL htL))
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  have hVev := (ENNReal.tendsto_nhds_zero.mp (hvariance tV htV))
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  have hSev := (ENNReal.tendsto_nhds_zero.mp hsmall)
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  filter_upwards [hMtight, hLev, hVev, hSev] with n hnM hnL hnV hnS
  refine iSup_le fun p => iSup_le fun hp => ?_
  let X : Ω → ℝ := F.standardizedOracle n p
  let A : Ω → ℝ := fun ω =>
    Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p)
  let S : ℝ := F.oracleVar p
  let E₁ : Set Ω := {ω | tL ≤ |A ω - F.oracleSum n p ω|}
  let E₂ : Set Ω := {ω | tV ≤ |F.scoreVar n p ω - S|}
  let E₃ : Set Ω := {ω | F.scoreVar n p ω ≤ vmin / 2}
  let E₄ : Set Ω := {ω | M ≤ |X ω|}
  have hpoint :
      {ω | ε ≤ |F.student n p ω - X ω|} ⊆
        E₁ ∪ E₂ ∪ E₃ ∪ E₄ := by
    intro ω hω
    by_contra hbad
    simp only [Set.mem_union, not_or, E₁, E₂, E₃, E₄,
      Set.mem_ofPred_eq] at hbad
    have hVlow : vmin / 2 < F.scoreVar n p ω := lt_of_not_ge hbad.1.2
    have hVnonneg : 0 ≤ F.scoreVar n p ω := by linarith [O.vmin_pos]
    have hSnonneg : 0 ≤ S := by
      dsimp [S]
      linarith [O.variance_lower n p hp, O.vmin_pos]
    have hrootV : c ≤ Real.sqrt (F.scoreVar n p ω) := by
      exact Real.sqrt_le_sqrt hVlow.le
    have hrootS : c ≤ Real.sqrt S := by
      apply Real.sqrt_le_sqrt
      dsimp [S]
      linarith [O.variance_lower n p hp]
    have hb := student_pointwise (A ω) (F.oracleSum n p ω)
      (F.scoreVar n p ω) S c M (ε / 2) hc hM.le (by positivity)
      hVnonneg hSnonneg hrootV hrootS
      (by
        have heq : tL = (ε / 2) * c / 4 := by dsimp [tL]; ring
        rw [← heq]
        exact le_of_lt (lt_of_not_ge hbad.1.1.1))
      (by
        have heq : tV = (ε / 2) * c ^ 2 / (4 * (M + 1)) := by
          dsimp [tV]
          field_simp
          ring
        rw [← heq]
        exact le_of_lt (lt_of_not_ge hbad.1.1.2))
      (le_of_lt (lt_of_not_ge hbad.2))
    change ε ≤ |F.student n p ω - X ω| at hω
    have heq : F.student n p ω = A ω / Real.sqrt (F.scoreVar n p ω) := rfl
    rw [heq] at hω
    change ε ≤ |A ω / Real.sqrt (F.scoreVar n p ω) -
      F.oracleSum n p ω / Real.sqrt S| at hω
    linarith
  have h₁ : F.sampleLaw p E₁ ≤ ENNReal.ofReal η :=
    (le_iSup_of_le p (le_iSup (fun hp : p ∈ F.lawClass n =>
      F.sampleLaw p {ω | tL ≤ |Real.sqrt (n : ℝ) *
        (F.estimate n p ω - F.target p) - F.oracleSum n p ω|}) hp)).trans hnL
  have h₂ : F.sampleLaw p E₂ ≤ ENNReal.ofReal η :=
    (le_iSup_of_le p (le_iSup (fun hp : p ∈ F.lawClass n =>
      F.sampleLaw p {ω | tV ≤ |F.scoreVar n p ω - F.oracleVar p|}) hp)).trans hnV
  have h₃ : F.sampleLaw p E₃ ≤ ENNReal.ofReal η :=
    (le_iSup_of_le p (le_iSup (fun hp : p ∈ F.lawClass n =>
      F.sampleLaw p {ω | F.scoreVar n p ω ≤ vmin / 2}) hp)).trans hnS
  have h₄ : F.sampleLaw p E₄ ≤ ENNReal.ofReal η := hnM p hp
  calc
    F.sampleLaw p {ω | ε ≤ |F.student n p ω - X ω|} ≤
        F.sampleLaw p (E₁ ∪ E₂ ∪ E₃ ∪ E₄) := measure_mono hpoint
    _ ≤ F.sampleLaw p E₁ + F.sampleLaw p E₂ +
        F.sampleLaw p E₃ + F.sampleLaw p E₄ := by
      calc
        _ ≤ F.sampleLaw p (E₁ ∪ E₂ ∪ E₃) + F.sampleLaw p E₄ :=
          measure_union_le _ _
        _ ≤ (F.sampleLaw p (E₁ ∪ E₂) + F.sampleLaw p E₃) +
            F.sampleLaw p E₄ := by
          gcongr
          exact measure_union_le (E₁ ∪ E₂) E₃
        _ ≤ _ := by
          gcongr
          exact measure_union_le E₁ E₂
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal η +
        ENNReal.ofReal η + ENNReal.ofReal η :=
      add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = ENNReal.ofReal (4 * η) := by
      rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
      · congr 1
        ring
      all_goals positivity
    _ = ζ := by
      have heq : 4 * η = ζ.toReal := by dsimp [η]; ring
      rw [heq, ENNReal.ofReal_toReal hζtop]


end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
