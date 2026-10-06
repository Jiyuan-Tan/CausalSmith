module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.Studentization

/-! # Uniform Wald coverage

Uniform studentized Gaussian convergence gives two-sided Wald coverage
uniformly over a possibly sample-size-indexed class of data laws.
-/

public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
open scoped ENNReal

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

namespace Family

private theorem student_measurable
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    {B vmin M3 : ℝ}
    (R : RateConditions F r a b C δ) (O : OracleConditions F B vmin M3)
    (n : ℕ) (p : ι) : Measurable (F.student n p) := by
  have hscore (k : Fin K) (i : ℕ) :
      Measurable (fun ω => F.score n p k ω ((F.sample p).Z i ω)) := by
    have hdiff := (R.diff_meas n p k).comp
      (measurable_id.prodMk ((F.sample p).meas i))
    have horacle := (O.measurable p).comp ((F.sample p).meas i)
    convert hdiff.add horacle using 1 <;> ext ω <;> simp
  have hmean : Measurable (F.scoreMean n p) := by
    unfold scoreMean
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro k hk
    apply Finset.measurable_sum
    intro i hi
    exact hscore k i
  have hvar : Measurable (F.scoreVar n p) := by
    unfold scoreVar
    apply Measurable.sub
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro k hk
      apply Finset.measurable_sum
      intro i hi
      exact (hscore k i).pow_const 2
    · exact hmean.pow_const 2
  have hest : Measurable (F.estimate n p) := by
    unfold estimate
    apply Measurable.add measurable_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro k hk
    apply Finset.measurable_sum
    intro i hi
    exact hscore k i
  unfold student
  exact ((measurable_const.mul (hest.sub measurable_const))).div
    (Real.continuous_sqrt.measurable.comp hvar)

private theorem interval_probability_cdf_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (a b t d : ℝ)
    (hab : a ≤ b) (ht : 0 < t) (G : ℝ → ℝ)
    (hmono : G (a - t) ≤ G a)
    (hbound : ∀ x, |μ.real {ω | X ω ≤ x} - G x| ≤ d) :
    |μ.real {ω | a ≤ X ω ∧ X ω ≤ b} - (G b - G a)| ≤
      2 * d + (G a - G (a - t)) := by
  let L : Set Ω := {ω | X ω < a}
  let U : Set Ω := {ω | X ω ≤ b}
  let W : Set Ω := {ω | a ≤ X ω ∧ X ω ≤ b}
  have hs : L ⊆ U := by
    intro ω hω
    exact le_trans (le_of_lt hω) hab
  have heq : W = U \ L := by
    ext ω
    simp only [W, U, L, Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · intro h
      exact ⟨h.2, not_lt.mpr h.1⟩
    · intro h
      exact ⟨le_of_not_gt h.2, h.1⟩
  have hW : μ.real W = μ.real U - μ.real L := by
    rw [heq, measureReal_sdiff hs (hX measurableSet_Iio)]
  have hnear : μ.real {ω | X ω ≤ a - t} ≤ μ.real L := by
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ω hω
    change X ω ≤ a - t at hω
    change X ω < a
    linarith
  have hfar : μ.real L ≤ μ.real {ω | X ω ≤ a} := by
    refine measureReal_mono ?_ (measure_ne_top μ _)
    intro ω hω
    change X ω < a at hω
    change X ω ≤ a
    linarith
  have hb := hbound b
  have ha := hbound a
  have hnear' := hbound (a - t)
  rw [abs_le] at hb ha hnear' ⊢
  dsimp [W, U] at *
  constructor <;> linarith

/-- For [a cross-fitting family](hyp:F) satisfying [the foldwise rate conditions](hyp:R) and
[the oracle-score conditions](hyp:O), and [a level α](hyp:α) [strictly between zero](hyp:hα0)
[and one](hyp:hα1), [the coverage probability of the two-sided Wald interval — the cross-fitted
estimate plus or minus the standard-normal (1 − α/2)-quantile times the square root of the
empirical score variance over √n — converges to 1 − α uniformly over the law class](goal). -/
theorem wald_uniform_coverage
    {r a b : ℕ → ℝ} {C : ℝ} {δ : ℕ → ℝ≥0∞}
    {B vmin M3 : ℝ}
    (R : RateConditions F r a b C δ) (O : OracleConditions F B vmin M3)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun n => ⨆ (p : ι) (_hp : p ∈ F.lawClass n),
      ENNReal.ofReal
        |(F.sampleLaw p {ω |
            |F.estimate n p ω - F.target p| ≤
              Causalean.Mathlib.probit (1 - α / 2) *
                Real.sqrt (F.scoreVar n p ω) / Real.sqrt (n : ℝ)}).toReal -
          (1 - α)|) atTop (𝓝 0) := by
  /- Put `q = probit (1-α/2)`. `stdNormalCDF_probit` and
  `stdNormalCDF_neg` give `P(-q ≤ N ≤ q) = 1-α`, while strict
  monotonicity and `Φ(0)=1/2` give `q > 0`. Uniform Gaussian CDF
  convergence of `student` controls the two endpoints. For the lower
  endpoint, sandwich `P(student < -q)` between CDF values at
  `-q-ε` and `-q`; Gaussian continuity lets `ε ↓ 0` uniformly.
  On the event `scoreVar > vmin/2` and for `n>0`, the displayed Wald
  event is exactly `|student| ≤ q`. Its complement is uniformly rare
  by `scoreVar_small_uniformly_rare`. -/
  let G : ℝ → ℝ := Causalean.Mathlib.stdNormalCDF
  let q : ℝ := Causalean.Mathlib.probit (1 - α / 2)
  have hp0 : 0 < 1 - α / 2 := by linarith
  have hp1 : 1 - α / 2 < 1 := by linarith
  have hqval : G q = 1 - α / 2 :=
    Causalean.Mathlib.stdNormalCDF_probit hp0 hp1
  have hG0 : G 0 = 1 / 2 := by
    have hs := Causalean.Mathlib.stdNormalCDF_neg 0
    simp only [neg_zero] at hs
    change G 0 = 1 - G 0 at hs
    linarith
  have hq : 0 < q := by
    by_contra h
    have hle : q ≤ 0 := le_of_not_gt h
    have hGle := Causalean.Mathlib.stdNormalCDF_strictMono.monotone hle
    change G q ≤ G 0 at hGle
    linarith
  have hnom : G q - G (-q) = 1 - α := by
    have hs := Causalean.Mathlib.stdNormalCDF_neg q
    change G (-q) = 1 - G q at hs
    linarith
  have hgauss := F.student_uniformGaussian R O
  have hsmall := F.scoreVar_small_uniformly_rare R O
  rw [ENNReal.tendsto_nhds_zero]
  intro ζ hζ
  by_cases htop : ζ = ⊤
  · subst ζ
    exact Filter.Eventually.of_forall (fun _ => le_top)
  let η : ℝ := ζ.toReal / 8
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (ENNReal.toReal_pos hζ.ne' htop) (by norm_num)
  obtain ⟨ρ, hρ, hρbound⟩ :=
    (Metric.continuousAt_iff.mp Causalean.Mathlib.stdNormalCDF_continuous.continuousAt)
      η hη
  let t : ℝ := ρ / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have hdist : dist (-q - t) (-q) < ρ := by
    rw [Real.dist_eq]
    have heq : -q - t - -q = -t := by ring
    rw [heq, abs_neg, abs_of_pos ht]
    dsimp [t]
    linarith
  have hgapabs := hρbound hdist
  have hgap : G (-q) - G (-q - t) < η := by
    rw [Real.dist_eq] at hgapabs
    change |G (-q - t) - G (-q)| < η at hgapabs
    have := (abs_lt.mp hgapabs).1
    linarith
  have hgev := (ENNReal.tendsto_nhds_zero.mp hgauss)
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  have hsev := (ENNReal.tendsto_nhds_zero.mp hsmall)
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  filter_upwards [hgev, hsev, eventually_gt_atTop (0 : ℕ)] with n hnG hnV hn
  refine iSup_le fun p => iSup_le fun hp => ?_
  haveI : IsProbabilityMeasure (F.sampleLaw p) :=
    (F.sample p).indep.isProbabilityMeasure
  let μ : Measure Ω := F.sampleLaw p
  let X : Ω → ℝ := F.student n p
  have hXm : Measurable X := F.student_measurable R O n p
  have hΦ (x : ℝ) : ((gaussianReal 0 1) (Set.Iic x)).toReal = G x := by
    exact (cdf_eq_real (gaussianReal 0 1) x).symm
  have herror (x : ℝ) : |μ.real {ω | X ω ≤ x} - G x| ≤ η := by
    have he : ENNReal.ofReal
        |(F.sampleLaw p {ω | F.student n p ω ≤ x}).toReal -
          ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤ ENNReal.ofReal η := by
      apply le_trans _ hnG
      exact le_iSup_of_le p (le_iSup_of_le hp
        (le_iSup (fun y : ℝ => ENNReal.ofReal
          |(F.sampleLaw p {ω | F.student n p ω ≤ y}).toReal -
            ((gaussianReal 0 1) (Set.Iic y)).toReal|) x))
    exact (ENNReal.ofReal_le_ofReal_iff hη.le).mp
      (by simpa only [μ, X, hΦ, measureReal_def] using he)
  have hmono : G (-q - t) ≤ G (-q) :=
    Causalean.Mathlib.stdNormalCDF_strictMono.monotone (by linarith)
  have hinterval :
      |μ.real {ω | -q ≤ X ω ∧ X ω ≤ q} - (1 - α)| ≤
        2 * η + (G (-q) - G (-q - t)) := by
    simpa only [hnom] using
      interval_probability_cdf_bound (μ := μ) X hXm (-q) q t η
        (by linarith) ht G hmono herror
  have hbridge (ω : Ω) (hV : vmin / 2 < F.scoreVar n p ω) :
      (|F.estimate n p ω - F.target p| ≤
        q * Real.sqrt (F.scoreVar n p ω) / Real.sqrt (n : ℝ)) ↔
      |X ω| ≤ q := by
    have hVpos : 0 < F.scoreVar n p ω := by linarith [O.vmin_pos]
    have hrootV : 0 < Real.sqrt (F.scoreVar n p ω) := Real.sqrt_pos.2 hVpos
    have hrootn : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    change (|F.estimate n p ω - F.target p| ≤
        q * Real.sqrt (F.scoreVar n p ω) / Real.sqrt (n : ℝ)) ↔
      |Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) /
        Real.sqrt (F.scoreVar n p ω)| ≤ q
    rw [abs_div, abs_mul, abs_of_pos hrootn, abs_of_pos hrootV]
    constructor
    · intro h
      have hm := (le_div_iff₀ hrootn).1 h
      apply (div_le_iff₀ hrootV).2
      nlinarith
    · intro h
      have hm := (div_le_iff₀ hrootV).1 h
      apply (le_div_iff₀ hrootn).2
      nlinarith
  let Cset : Set Ω := {ω |
    |F.estimate n p ω - F.target p| ≤
      q * Real.sqrt (F.scoreVar n p ω) / Real.sqrt (n : ℝ)}
  let Wset : Set Ω := {ω | |X ω| ≤ q}
  let D : Set Ω := {ω | F.scoreVar n p ω ≤ vmin / 2}
  have hW_eq : Wset = {ω | -q ≤ X ω ∧ X ω ≤ q} := by
    ext ω
    change (|X ω| ≤ q) ↔ (-q ≤ X ω ∧ X ω ≤ q)
    exact abs_le
  have hsubC : Cset ⊆ Wset ∪ D := by
    intro ω hω
    by_cases hd : ω ∈ D
    · exact Or.inr hd
    · left
      have hv : vmin / 2 < F.scoreVar n p ω := by
        change ¬ F.scoreVar n p ω ≤ vmin / 2 at hd
        exact lt_of_not_ge hd
      exact (hbridge ω hv).mp hω
  have hsubW : Wset ⊆ Cset ∪ D := by
    intro ω hω
    by_cases hd : ω ∈ D
    · exact Or.inr hd
    · left
      have hv : vmin / 2 < F.scoreVar n p ω := by
        change ¬ F.scoreVar n p ω ≤ vmin / 2 at hd
        exact lt_of_not_ge hd
      exact (hbridge ω hv).mpr hω
  have hbadENN' : F.sampleLaw p
      {ω | F.scoreVar n p ω ≤ vmin / 2} ≤ ENNReal.ofReal η :=
    (le_iSup_of_le p (le_iSup
      (fun hp : p ∈ F.lawClass n => F.sampleLaw p
        {ω | F.scoreVar n p ω ≤ vmin / 2}) hp)).trans hnV
  have hbadENN : μ D ≤ ENNReal.ofReal η := hbadENN'
  have hbad : μ.real D ≤ η := by
    have he : ENNReal.ofReal (μ.real D) ≤ ENNReal.ofReal η := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ D)]
      exact hbadENN
    exact (ENNReal.ofReal_le_ofReal_iff hη.le).mp he
  have hCW : |μ.real Cset - μ.real Wset| ≤ μ.real D := by
    have h₁ : μ.real Cset ≤ μ.real Wset + μ.real D :=
      (measureReal_mono hsubC (measure_ne_top μ _)).trans
        (measureReal_union_le Wset D)
    have h₂ : μ.real Wset ≤ μ.real Cset + μ.real D :=
      (measureReal_mono hsubW (measure_ne_top μ _)).trans
        (measureReal_union_le Cset D)
    rw [abs_le]
    constructor <;> linarith
  have hcover : |μ.real Cset - (1 - α)| ≤
      μ.real D + (2 * η + (G (-q) - G (-q - t))) := by
    rw [← hW_eq] at hinterval
    calc
      |μ.real Cset - (1 - α)| =
          |(μ.real Cset - μ.real Wset) + (μ.real Wset - (1 - α))| := by ring
      _ ≤ |μ.real Cset - μ.real Wset| +
          |μ.real Wset - (1 - α)| := abs_add_le _ _
      _ ≤ _ := add_le_add hCW hinterval
  have hfinal : |μ.real Cset - (1 - α)| ≤ 4 * η := by
    linarith
  have hfinalENN : ENNReal.ofReal |μ.real Cset - (1 - α)| ≤ ζ := by
    calc
      _ ≤ ENNReal.ofReal (4 * η) := ENNReal.ofReal_le_ofReal hfinal
      _ ≤ ENNReal.ofReal ζ.toReal :=
        ENNReal.ofReal_le_ofReal (by
          have heq : 4 * η = ζ.toReal / 2 := by dsimp [η]; ring
          rw [heq]
          linarith [hη])
      _ = ζ := ENNReal.ofReal_toReal htop
  simpa only [μ, Cset, measureReal_def] using hfinalENN


end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
