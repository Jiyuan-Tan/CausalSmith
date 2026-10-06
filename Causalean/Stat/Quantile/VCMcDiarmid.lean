module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.RademacherBridge
public import Causalean.Stat.Concentration.VC.Parametric
public import Causalean.Stat.Concentration.VC.Rademacher.Conditional
public import Causalean.Stat.Quantile.MarkedSubsampleEmpiricalCDF.Measurability
public import FoML.Main

/-!
# A VC--McDiarmid bound for uniform empirical-CDF deviation

This module proves a distribution-free finite-sample exponential bound for the
uniform empirical-CDF deviation under a canonical iid product law. Real lower
half-lines have at most `n+1` traces on an `n`-point sample. Finite-pattern
Rademacher control, symmetrization, and McDiarmid's inequality therefore give
the following distribution-free VC bound

`8 * (n+1) * exp (-n * ε^2 / 32)`.

The module also provides upper and lower one-sided forms. The sharp
Dvoretzky--Kiefer--Wolfowitz--Massart bound `2 * exp (-2 * n * ε^2)` remains
outside its scope.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal

namespace Causalean.Stat.Quantile.VCMcDiarmid

open Causalean.Stat.Quantile.MarkedSubsampleEmpiricalCDF

open Causalean.Stat.Concentration

private noncomputable def lowerRayClassifier (q : ℚ) (x : ℝ) : Bool :=
  decide (x ≤ (q : ℝ))

private theorem lowerRayClassifier_hasVCAtMost : HasVCAtMost lowerRayClassifier 1 := by
  intro n S
  unfold Finset.vcDim
  refine Finset.sup_le fun s hs => ?_
  rw [Finset.mem_shatterer] at hs
  by_contra hcard
  have htwo : 2 ≤ s.card := by omega
  have hone : 1 < s.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hone
  rcases le_total (S a) (S b) with habS | hbaS
  · obtain ⟨u, hu, hsu⟩ := hs.exists_inter_eq_singleton hb
    obtain ⟨q, hq⟩ := mem_growthFamily_iff.mp hu
    have hbu : b ∈ u := by
      have : b ∈ s ∩ u := by simpa [hsu]
      exact (Finset.mem_inter.mp this).2
    have hau : a ∉ u := by
      intro hau
      have : a ∈ s ∩ u := Finset.mem_inter.mpr ⟨ha, hau⟩
      rw [hsu] at this
      exact hab (Finset.mem_singleton.mp this)
    have hbq : lowerRayClassifier q (S b) = true := by
      rw [← restrictionPattern_mem_iff (p := lowerRayClassifier q) (S := S), hq]
      exact hbu
    have haq : lowerRayClassifier q (S a) = true := by
      simpa [lowerRayClassifier] using le_trans habS (of_decide_eq_true hbq)
    apply hau
    rw [← hq]
    exact restrictionPattern_mem_iff.mpr haq
  · obtain ⟨u, hu, hsu⟩ := hs.exists_inter_eq_singleton ha
    obtain ⟨q, hq⟩ := mem_growthFamily_iff.mp hu
    have hau : a ∈ u := by
      have : a ∈ s ∩ u := by simpa [hsu]
      exact (Finset.mem_inter.mp this).2
    have hbu : b ∉ u := by
      intro hbu
      have : b ∈ s ∩ u := Finset.mem_inter.mpr ⟨hb, hbu⟩
      rw [hsu] at this
      exact hab (Finset.mem_singleton.mp this).symm
    have haq : lowerRayClassifier q (S a) = true := by
      rw [← restrictionPattern_mem_iff (p := lowerRayClassifier q) (S := S), hq]
      exact hau
    have hbq : lowerRayClassifier q (S b) = true := by
      simpa [lowerRayClassifier] using le_trans hbaS (of_decide_eq_true haq)
    apply hbu
    rw [← hq]
    exact restrictionPattern_mem_iff.mpr hbq

private noncomputable def lowerRayClass (q : ℚ) (x : ℝ) : ℝ :=
  Causalean.Stat.cdfStat (q : ℝ) x

private lemma lowerRayClass_eq_indicatorClass (q : ℚ) (x : ℝ) :
    lowerRayClass q x = if lowerRayClassifier q x = true then 1 else 0 := by
  simp [lowerRayClass, lowerRayClassifier, Causalean.Stat.cdfStat,
    Set.indicator_apply]

private lemma lowerRayClass_envelope (q : ℚ) (x : ℝ) : |lowerRayClass q x| ≤ 1 := by
  have h0 := Causalean.Stat.cdfStat_nonneg (q : ℝ) x
  have h1 := Causalean.Stat.cdfStat_le_one (q : ℝ) x
  rw [lowerRayClass, abs_of_nonneg h0]
  exact h1

private noncomputable def lowerRayPatternClass {n : ℕ} (S : Fin n → ℝ) :
    {A // A ∈ growthFamily lowerRayClassifier S} → ℝ → ℝ :=
  fun A => lowerRayClass (growthFamilyRep lowerRayClassifier S A)

private lemma lowerRayClass_empiricalRademacher_le_patternClass {n : ℕ}
    (S : Fin n → ℝ) :
    empiricalRademacherComplexity n lowerRayClass S ≤
      empiricalRademacherComplexity n (lowerRayPatternClass S) S := by
  classical
  have hnonempty : (growthFamily lowerRayClassifier S).Nonempty := by
    refine ⟨restrictionPattern (lowerRayClassifier 0) S, ?_⟩
    rw [mem_growthFamily_iff]
    exact ⟨0, rfl⟩
  haveI : Nonempty {A // A ∈ growthFamily lowerRayClassifier S} := by
    rcases hnonempty with ⟨A, hA⟩
    exact ⟨⟨A, hA⟩⟩
  unfold empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
  refine ciSup_le fun q => ?_
  let A : {A // A ∈ growthFamily lowerRayClassifier S} :=
    ⟨restrictionPattern (lowerRayClassifier q) S, by
      rw [mem_growthFamily_iff]
      exact ⟨q, rfl⟩⟩
  have hsample (k : Fin n) :
      lowerRayClass q (S k) = lowerRayPatternClass S A (S k) := by
    unfold lowerRayPatternClass
    rw [lowerRayClass_eq_indicatorClass, lowerRayClass_eq_indicatorClass]
    congr 1
    apply propext
    rw [← restrictionPattern_mem_iff (p := lowerRayClassifier q) (S := S) (j := k),
      show restrictionPattern (lowerRayClassifier q) S = A.1 from rfl,
      ← growthFamilyRep_spec lowerRayClassifier S A,
      restrictionPattern_mem_iff]
  rw [show (∑ k : Fin n, (σ k : ℝ) * lowerRayClass q (S k)) =
      ∑ k : Fin n, (σ k : ℝ) * lowerRayPatternClass S A (S k) by
        apply Finset.sum_congr rfl
        intro k _
        rw [hsample]]
  exact le_ciSup
    (Finite.bddAbove_range fun B : {B // B ∈ growthFamily lowerRayClassifier S} =>
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * lowerRayPatternClass S B (S k)|)
    A

private theorem lowerRayClass_empiricalRademacher_le {n : ℕ} (hn : 0 < n)
    (S : Fin n → ℝ) :
    empiricalRademacherComplexity n lowerRayClass S ≤
      Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ)) := by
  classical
  let W := lowerRayPatternClass S
  have hgf_nonempty : (growthFamily lowerRayClassifier S).Nonempty := by
    refine ⟨restrictionPattern (lowerRayClassifier 0) S, ?_⟩
    rw [mem_growthFamily_iff]
    exact ⟨0, rfl⟩
  haveI : Nonempty {A // A ∈ growthFamily lowerRayClassifier S} := by
    rcases hgf_nonempty with ⟨A, hA⟩
    exact ⟨⟨A, hA⟩⟩
  have hfinite :
      empiricalRademacherComplexity n W S ≤
        (1 / Real.sqrt (n : ℝ)) *
          Real.sqrt (2 * Real.log
            (2 * ((growthFamily lowerRayClassifier S).card : ℝ))) := by
    have hmain := empiricalRademacher_withAbs_finiteClass_le hn W S
      (Finset.univ : Finset {A // A ∈ growthFamily lowerRayClassifier S})
      Finset.univ_nonempty (1 / Real.sqrt (n : ℝ)) (by
        intro A _
        calc
          Real.sqrt (∑ k : Fin n, ((n : ℝ)⁻¹ * |W A (S k)|) ^ 2) ≤
              Real.sqrt (∑ _k : Fin n, ((n : ℝ)⁻¹ * 1) ^ 2) := by
                apply Real.sqrt_le_sqrt
                apply Finset.sum_le_sum
                intro k _
                gcongr
                exact lowerRayClass_envelope _ _
          _ = 1 / Real.sqrt (n : ℝ) := by
            have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [show (n : ℝ) * ((n : ℝ)⁻¹ * 1) ^ 2 = 1 / (n : ℝ) by
              field_simp]
            rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one])
    rw [empiricalRademacherComplexity_F_on_univ_eq W S] at hmain
    simpa using hmain
  have hcard : (growthFamily lowerRayClassifier S).card ≤ n + 1 := by
    have htrace : BinaryTraceEntropyControl lowerRayClassifier 1 :=
      Or.inl (fun {m} T => lowerRayClassifier_hasVCAtMost m T)
    simpa using growthFamily_card_le_succ_pow_of_trace
      lowerRayClassifier 1 n htrace S
  have hcardR : ((growthFamily lowerRayClassifier S).card : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast hcard
  have hcard_pos : 0 < (growthFamily lowerRayClassifier S).card :=
    Finset.card_pos.mpr hgf_nonempty
  have hlog_mono :
      Real.log (2 * ((growthFamily lowerRayClassifier S).card : ℝ)) ≤
        Real.log (2 * ((n : ℝ) + 1)) := by
    apply Real.log_le_log
    · positivity
    · nlinarith
  have hlog_nonneg :
      0 ≤ Real.log (2 * ((growthFamily lowerRayClassifier S).card : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((growthFamily lowerRayClassifier S).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hcard_pos)
    nlinarith
  have htarget_nonneg : 0 ≤ Real.log (2 * ((n : ℝ) + 1)) := by
    apply Real.log_nonneg
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    nlinarith
  calc
    empiricalRademacherComplexity n lowerRayClass S ≤
        empiricalRademacherComplexity n W S := by
          simpa [W] using lowerRayClass_empiricalRademacher_le_patternClass S
    _ ≤ (1 / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log
          (2 * ((growthFamily lowerRayClassifier S).card : ℝ))) := hfinite
    _ ≤ (1 / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1))) := by
          gcongr
    _ = Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ)) := by
      rw [Real.sqrt_div (mul_nonneg (by norm_num) htarget_nonneg)]
      ring

private theorem lowerRayClass_populationRademacher_le
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {n : ℕ} (hn : 0 < n) :
    rademacherComplexity n lowerRayClass ρ id ≤
      Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ)) := by
  let μn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => ρ)
  let rad : (Fin n → ℝ) → ℝ := fun S => empiricalRademacherComplexity n lowerRayClass S
  have hmeas : Measurable rad :=
    empiricalRademacherComplexity_measurable_countable lowerRayClass
      (fun q => Causalean.Stat.measurable_cdfStat (q : ℝ)) n
  have hmem (S : Fin n → ℝ) : rad S ∈ Set.Icc 0 1 :=
    empiricalRademacherComplexity_mem_Icc lowerRayClass (by norm_num)
      lowerRayClass_envelope n S
  have hint : Integrable rad μn :=
    (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (ae_of_all _ fun S => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hmem S).1]
        exact (hmem S).2)
  unfold rademacherComplexity
  change ∫ S, rad S ∂μn ≤ _
  calc
    ∫ S, rad S ∂μn ≤
        ∫ _S, Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ)) ∂μn := by
      apply integral_mono hint (integrable_const _)
      exact lowerRayClass_empiricalRademacher_le hn
    _ = Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ)) := by
      simp [μn]

private lemma abs_empiricalCDFVec_sub_cdf_le_one {n : ℕ} (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (x : Fin n → ℝ) (y : ℝ) :
    |empiricalCDFVec x y - cdf ρ y| ≤ 1 := by
  have hstat_nonneg : 0 ≤ ∑ i : Fin n, Causalean.Stat.cdfStat y (x i) :=
    Finset.sum_nonneg fun i _ => Causalean.Stat.cdfStat_nonneg y (x i)
  have hstat_le : (∑ i : Fin n, Causalean.Stat.cdfStat y (x i)) ≤ n := by
    calc
      (∑ i : Fin n, Causalean.Stat.cdfStat y (x i)) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Causalean.Stat.cdfStat_le_one y (x i)
      _ = n := by simp
  have he0 : 0 ≤ empiricalCDFVec x y := by
    simp only [empiricalCDFVec]
    positivity
  have he1 : empiricalCDFVec x y ≤ 1 := by
    by_cases hn0 : n = 0
    · subst n
      simp [empiricalCDFVec]
    · rw [empiricalCDFVec, inv_mul_le_iff₀ (by positivity)]
      simpa using hstat_le
  have hc0 := cdf_nonneg ρ y
  have hc1 := cdf_le_one ρ y
  rw [abs_le]
  constructor <;> linarith

private lemma uniformCDFDeviation_eq_uniformDeviation {n : ℕ} (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (x : Fin n → ℝ) :
    uniformCDFDeviation ρ x = uniformDeviation n lowerRayClass ρ id x := by
  have hbound (y : ℝ) :
      |empiricalCDFVec x y - cdf ρ y| ≤ 1 :=
    abs_empiricalCDFVec_sub_cdf_le_one ρ x y
  have hsep :
      uniformCDFDeviation ρ x =
        ⨆ q : ℚ, |empiricalCDFVec x (q : ℝ) - cdf ρ (q : ℝ)| := by
    let g : ℝ → ℝ := fun y => |empiricalCDFVec x y - cdf ρ y|
    have hg_bound (y : ℝ) : g y ≤ 1 := hbound y
    have hreal_bdd : BddAbove (Set.range g) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hg_bound y
    have hrat_bdd : BddAbove (Set.range fun q : ℚ => g (q : ℝ)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨q, rfl⟩
      exact hg_bound q
    change sSup (Set.range g) = ⨆ q : ℚ, g (q : ℝ)
    apply le_antisymm
    · apply csSup_le
      · exact ⟨g 0, ⟨0, rfl⟩⟩
      · intro z hz
        rcases hz with ⟨y, rfl⟩
        obtain ⟨u, _, hu_above, hu_lim⟩ :=
          Rat.denseRange_cast.exists_seq_strictAnti_tendsto
            Rat.cast_strictMono.monotone y
        have hdev : ContinuousWithinAt g (Set.Ici y) y :=
          ((empiricalCDFVec_continuousWithinAt_Ici x y).sub
            ((cdf ρ).right_continuous y)).abs
        have hu_within : Filter.Tendsto (Rat.cast ∘ u) Filter.atTop (𝓝[Set.Ici y] y) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu_lim
            (Filter.Eventually.of_forall fun m =>
              Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp (hu_above m))))
        apply le_of_tendsto' (hdev.tendsto.comp hu_within)
        intro m
        exact le_ciSup hrat_bdd (u m)
    · apply ciSup_le
      intro q
      exact le_csSup hreal_bdd ⟨(q : ℝ), rfl⟩
  rw [hsep]
  unfold uniformDeviation
  apply iSup_congr
  intro q
  simp only [lowerRayClass, id_eq, Causalean.Stat.integral_cdfStat]
  rfl

/-- For [a population law on the real line](hyp:ρ) and [a finite sample vector](hyp:x),
[the upper one-sided empirical-CDF deviation is the supremum of the empirical CDF minus the
population CDF over all real thresholds](goal). -/
noncomputable def upperCDFDeviation {n : ℕ} (ρ : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun y : ℝ => empiricalCDFVec x y - cdf ρ y)

/-- For [a population law on the real line](hyp:ρ) and [a finite sample vector](hyp:x),
[the lower one-sided empirical-CDF deviation is the supremum of the population CDF minus the
empirical CDF over all real thresholds](goal). -/
noncomputable def lowerCDFDeviation {n : ℕ} (ρ : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun y : ℝ => cdf ρ y - empiricalCDFVec x y)

/-- For [a population law](hyp:ρ) and [a deviation threshold](hyp:ε),
[the upper one-sided empirical-CDF bad set contains the sample vectors whose upper deviation is
greater than that threshold](goal). -/
def upperCDFBadSet {n : ℕ} (ρ : Measure ℝ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {x | upperCDFDeviation ρ x > ε}

/-- For [a population law](hyp:ρ) and [a deviation threshold](hyp:ε),
[the lower one-sided empirical-CDF bad set contains the sample vectors whose lower deviation is
greater than that threshold](goal). -/
def lowerCDFBadSet {n : ℕ} (ρ : Measure ℝ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {x | lowerCDFDeviation ρ x > ε}

private lemma upperCDFDeviation_le_uniformCDFDeviation {n : ℕ} (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (x : Fin n → ℝ) :
    upperCDFDeviation ρ x ≤ uniformCDFDeviation ρ x := by
  have hbdd : BddAbove (Set.range fun y : ℝ =>
      |empiricalCDFVec x y - cdf ρ y|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact abs_empiricalCDFVec_sub_cdf_le_one ρ x y
  unfold upperCDFDeviation uniformCDFDeviation
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨y, rfl⟩
    exact (le_abs_self _).trans (le_csSup hbdd ⟨y, rfl⟩)

private lemma lowerCDFDeviation_le_uniformCDFDeviation {n : ℕ} (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (x : Fin n → ℝ) :
    lowerCDFDeviation ρ x ≤ uniformCDFDeviation ρ x := by
  have hbdd : BddAbove (Set.range fun y : ℝ =>
      |empiricalCDFVec x y - cdf ρ y|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact abs_empiricalCDFVec_sub_cdf_le_one ρ x y
  unfold lowerCDFDeviation uniformCDFDeviation
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨y, rfl⟩
    have hneg : cdf ρ y - empiricalCDFVec x y =
        -(empiricalCDFVec x y - cdf ρ y) := by ring
    change cdf ρ y - empiricalCDFVec x y ≤ _
    rw [hneg]
    exact (neg_le_abs _).trans (le_csSup hbdd ⟨y, rfl⟩)

private theorem empiricalCDF_vc_mcdiarmid_large_toReal (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ]
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (hlarge : 4 * Real.sqrt
      (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ)) ≤ ε) :
    ((Measure.pi (fun _ : Fin n => ρ)) (fixedCDFBadSet ρ ε)).toReal ≤
      Real.exp (-((n : ℝ) * ε ^ 2) / 8) := by
  let R : ℝ := rademacherComplexity n lowerRayClass ρ id
  let A : ℝ := Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ))
  have hR : R ≤ A := lowerRayClass_populationRademacher_le ρ hn
  have hthreshold : 2 • R + ε / 2 ≤ ε := by
    simp only [two_smul]
    change 4 * A ≤ ε at hlarge
    nlinarith
  have htail := uniform_deviation_tail_bound_countable_of_pos
    (μ := ρ) (n := n) lowerRayClass
    (fun q => Causalean.Stat.measurable_cdfStat (q : ℝ)) id measurable_id
    (b := 1) (by norm_num) lowerRayClass_envelope
    (ε := ε / 2) (by positivity)
  change ((Measure.pi (fun _ : Fin n => ρ))
    {x : Fin n → ℝ |
      2 • R + ε / 2 ≤ uniformDeviation n lowerRayClass ρ id x}).toReal ≤
        Real.exp (-((ε / 2) ^ 2) * n / (2 * 1 ^ 2)) at htail
  calc
    ((Measure.pi (fun _ : Fin n => ρ)) (fixedCDFBadSet ρ ε)).toReal ≤
        ((Measure.pi (fun _ : Fin n => ρ))
          {x : Fin n → ℝ |
            2 • R + ε / 2 ≤ uniformDeviation n lowerRayClass ρ id x}).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro x hx
      change ε < uniformCDFDeviation ρ x at hx
      change 2 • R + ε / 2 ≤ uniformDeviation n lowerRayClass ρ id x
      rw [← uniformCDFDeviation_eq_uniformDeviation ρ x]
      exact hthreshold.trans (le_of_lt hx)
    _ ≤ Real.exp (-((ε / 2) ^ 2) * n / (2 * 1 ^ 2)) := by
      simpa [R] using htail
    _ = Real.exp (-((n : ℝ) * ε ^ 2) / 8) := by congr 1 <;> ring

/-- Given [a population probability law](hyp:ρ), [a positive sample size](hyp:hn),
[a positive threshold](hyp:hε), and the [large-threshold condition](hyp:hlarge), [the
uniform empirical-CDF tail is at most `exp (-n * ε² / 8)`](goal).

This is the large-threshold branch of the VC--McDiarmid proof. Massart's sharper
`2 * exp (-2 * n * ε²)` inequality is not formalized here. -/
theorem empiricalCDF_vc_mcdiarmid_large (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (hlarge : 4 * Real.sqrt
      (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ)) ≤ ε) :
    (Measure.pi (fun _ : Fin n => ρ)) (fixedCDFBadSet ρ ε) ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ε ^ 2) / 8)) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact empiricalCDF_vc_mcdiarmid_large_toReal ρ hn hε hlarge

private theorem empiricalCDF_vc_mcdiarmid_toReal (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ]
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi (fun _ : Fin n => ρ)) (fixedCDFBadSet ρ ε)).toReal ≤
      8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * ε ^ 2) / 32) := by
  let μn : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => ρ)
  let R : ℝ := rademacherComplexity n lowerRayClass ρ id
  let A : ℝ := Real.sqrt (2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ))
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : 0 < Real.log (2 * ((n : ℝ) + 1)) := by
    apply Real.log_pos
    nlinarith
  have hA_nonneg : 0 ≤ A := Real.sqrt_nonneg _
  have hA_sq : A ^ 2 = 2 * Real.log (2 * ((n : ℝ) + 1)) / (n : ℝ) := by
    dsimp [A]
    rw [Real.sq_sqrt]
    positivity
  have hR : R ≤ A := by
    exact lowerRayClass_populationRademacher_le ρ hn
  by_cases hlarge : 4 * A ≤ ε
  · have htail' := empiricalCDF_vc_mcdiarmid_large_toReal ρ hn hε hlarge
    calc
      (μn (fixedCDFBadSet ρ ε)).toReal ≤
          Real.exp (-((n : ℝ) * ε ^ 2) / 8) := htail'
      _ ≤ Real.exp (-((n : ℝ) * ε ^ 2) / 32) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ε]
      _ ≤ 8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * ε ^ 2) / 32) := by
        have he := Real.exp_pos (-((n : ℝ) * ε ^ 2) / 32)
        nlinarith
  · have hlt : ε < 4 * A := lt_of_not_ge hlarge
    have hsq : ε ^ 2 < (4 * A) ^ 2 := by nlinarith
    have hsmall : (n : ℝ) * ε ^ 2 / 32 <
        Real.log (2 * ((n : ℝ) + 1)) := by
      have hscaled : (n : ℝ) * ε ^ 2 <
          (n : ℝ) * (4 * A) ^ 2 := mul_lt_mul_of_pos_left hsq hnR
      have hscaled' : (n : ℝ) * ε ^ 2 <
          32 * Real.log (2 * ((n : ℝ) + 1)) := by
        calc
          (n : ℝ) * ε ^ 2 < (n : ℝ) * (4 * A) ^ 2 := hscaled
          _ = 32 * Real.log (2 * ((n : ℝ) + 1)) := by
            rw [mul_pow, hA_sq]
            field_simp [hnR.ne']
            <;> ring
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 32)]
      nlinarith
    have hexp : Real.exp ((n : ℝ) * ε ^ 2 / 32) ≤ 8 * ((n : ℝ) + 1) := by
      calc
        Real.exp ((n : ℝ) * ε ^ 2 / 32) ≤
            Real.exp (Real.log (2 * ((n : ℝ) + 1))) :=
          Real.exp_le_exp.mpr hsmall.le
        _ = 2 * ((n : ℝ) + 1) := by
          rw [Real.exp_log]
          positivity
        _ ≤ 8 * ((n : ℝ) + 1) := by nlinarith
    calc
      (μn (fixedCDFBadSet ρ ε)).toReal ≤ 1 := measureReal_le_one
      _ = Real.exp ((n : ℝ) * ε ^ 2 / 32) *
          Real.exp (-((n : ℝ) * ε ^ 2) / 32) := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero.symm
      _ ≤ 8 * ((n : ℝ) + 1) *
          Real.exp (-((n : ℝ) * ε ^ 2) / 32) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le

/-- Given [an arbitrary population probability law on the real line](hyp:ρ), [a positive sample
size](hyp:hn), and [a positive deviation threshold](hyp:hε), [the product-law probability that
the empirical CDF differs uniformly from the population CDF by more than that threshold is at
most `8 * (n+1) * exp (-n * ε² / 32)`](goal).

This is the classical VC bound for lower half-lines (Vapnik--Chervonenkis, 1971;
Devroye--Györfi--Lugosi, 1996, Theorem 12.5). Massart's sharp
`2 * exp (-2 * n * ε²)` bound is not claimed. -/
theorem empiricalCDF_vc_mcdiarmid (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => ρ)) (fixedCDFBadSet ρ ε) ≤
      ENNReal.ofReal
        (8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * ε ^ 2) / 32)) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_ofReal]
  · exact empiricalCDF_vc_mcdiarmid_toReal ρ hn hε
  · positivity

/-- Given [an arbitrary population probability law on the real line](hyp:ρ), [a positive sample
size](hyp:hn), and [a positive deviation threshold](hyp:hε), [the product-law probability that
the empirical CDF exceeds the population CDF somewhere by more than that threshold is at most
`8 * (n+1) * exp (-n * ε² / 32)`](goal). -/
theorem empiricalCDF_vc_mcdiarmid_upper (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => ρ)) (upperCDFBadSet ρ ε) ≤
      ENNReal.ofReal
        (8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * ε ^ 2) / 32)) := by
  have hmono : (Measure.pi (fun _ : Fin n => ρ)) (upperCDFBadSet ρ ε) ≤
      (Measure.pi (fun _ : Fin n => ρ)) (fixedCDFBadSet ρ ε) := by
    apply measure_mono
    intro x hx
    change ε < upperCDFDeviation ρ x at hx
    change ε < uniformCDFDeviation ρ x
    exact hx.trans_le (upperCDFDeviation_le_uniformCDFDeviation ρ x)
  exact hmono.trans (empiricalCDF_vc_mcdiarmid ρ hn hε)

/-- Given [an arbitrary population probability law on the real line](hyp:ρ), [a positive sample
size](hyp:hn), and [a positive deviation threshold](hyp:hε), [the product-law probability that
the population CDF exceeds the empirical CDF somewhere by more than that threshold is at most
`8 * (n+1) * exp (-n * ε² / 32)`](goal). -/
theorem empiricalCDF_vc_mcdiarmid_lower (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n => ρ)) (lowerCDFBadSet ρ ε) ≤
      ENNReal.ofReal
        (8 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * ε ^ 2) / 32)) := by
  have hmono : (Measure.pi (fun _ : Fin n => ρ)) (lowerCDFBadSet ρ ε) ≤
      (Measure.pi (fun _ : Fin n => ρ)) (fixedCDFBadSet ρ ε) := by
    apply measure_mono
    intro x hx
    change ε < lowerCDFDeviation ρ x at hx
    change ε < uniformCDFDeviation ρ x
    exact hx.trans_le (lowerCDFDeviation_le_uniformCDFDeviation ρ x)
  exact hmono.trans (empiricalCDF_vc_mcdiarmid ρ hn hε)

end Causalean.Stat.Quantile.VCMcDiarmid
