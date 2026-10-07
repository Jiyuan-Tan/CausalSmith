module
public import Causalean.Stat.OrderStatistic.CDFTransport
public import Causalean.Stat.OrderStatistic.DensityEnvelope
public import Causalean.Stat.OrderStatistic.Moments

/-!
# Density-envelope comparison for iid real spacings

A real distribution with density bounded above and below on its support has a
CDF that transports it to the unit uniform law and compares its sorted gaps
with uniform sorted gaps. The resulting bounds apply to individual gaps and to
the alternating sum.
-/

public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory

noncomputable section

/-- Given [a real probability law](hyp:μ), [a density](hyp:p), and [its density representation](hyp:hμ), [its CDF pushes the law forward to the unit-uniform law](goal). -/
theorem cdf_pushforward_uniform01 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ → ℝ)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x))) :
    μ.map (fun x => ProbabilityTheory.cdf μ x) = uniform01 := by
  exact cdf_pushforward_of_continuous μ (cdf_continuous_of_withDensity μ p hμ)

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [density constants and their order](hyp:cg,Cg,hcg,hCg), [a density](hyp:p), [its density representation](hyp:hμ), [an almost-everywhere density envelope](hyp:hbound), and [two ordered points inside it](hyp:hax,hxy,hyb), [the CDF increment lies between the density constants times their distance](goal). -/
theorem cdf_increment_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b cg Cg : ℝ) (p : ℝ → ℝ)
    (hcg : 0 < cg) (hCg : cg ≤ Cg)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), cg ≤ p x ∧ p x ≤ Cg)
    {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    cg * (y - x) ≤ ProbabilityTheory.cdf μ y - ProbabilityTheory.cdf μ x ∧
      ProbabilityTheory.cdf μ y - ProbabilityTheory.cdf μ x ≤ Cg * (y - x) := by
  rw [cdf_increment_eq_interval_mass μ hxy]
  exact withDensity_interval_mass_bounds μ a b cg Cg p hcg hCg hμ hbound hax hxy hyb

/-- Given [a real probability law](hyp:μ), [a density](hyp:p), [its density representation](hyp:hμ), and [a sample size](hyp:n), [coordinatewise CDF transformation sends the iid sample law to the iid unit-uniform law](goal). -/
theorem iid_cdf_pushforward_uniform01 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ → ℝ)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (n : ℕ) :
    (iidSample μ n).map (fun x i => ProbabilityTheory.cdf μ (x i)) =
      iidSample uniform01 n := by
  have hc := cdf_continuous_of_withDensity μ p hμ
  have hmap := cdf_pushforward_uniform01 μ p hμ
  haveI : IsProbabilityMeasure (μ.map (fun x => ProbabilityTheory.cdf μ x)) :=
    Measure.isProbabilityMeasure_map hc.measurable.aemeasurable
  change (Measure.pi (fun _ : Fin n => μ)).map
      (fun x i => ProbabilityTheory.cdf μ (x i)) = Measure.pi (fun _ : Fin n => uniform01)
  rw [Measure.pi_map_pi (fun _ : Fin n => hc.measurable.aemeasurable)]
  simp only [hmap]

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [support in that interval](hyp:hsupp), and [a sample size](hyp:n), [every iid sample coordinate lies in that interval almost surely](goal). -/
theorem iid_support_interval_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hsupp : μ (Set.Icc a b)ᶜ = 0) (n : ℕ) :
    ∀ᵐ x ∂iidSample μ n, ∀ i, x i ∈ Set.Icc a b := by
  have hcoord : ∀ᵐ y ∂μ, y ∈ Set.Icc a b := mem_ae_iff.mpr hsupp
  change ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ i, x i ∈ Set.Icc a b
  exact Filter.eventually_all.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually hcoord)

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [support in that interval](hyp:hsupp), [a sample size and adjacent-gap index](hyp:n,k), and [proof that the gap is interior](hyp:hk), [the squared sorted gap is integrable](goal). -/
theorem sortedGap_square_integrable_of_interval_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (n k : ℕ) (hk : k + 1 < n) :
    Integrable (fun x => (sortedGap n k x) ^ 2) (iidSample μ n) := by
  classical
  let lo : Fin n := ⟨k, by omega⟩
  let hi : Fin n := ⟨k + 1, hk⟩
  have hsort : AEMeasurable (sortedSample n) (iidSample μ n) := by
    let s (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
      {x | Monotone (x ∘ σ)}
    have hs (σ : Equiv.Perm (Fin n)) : MeasurableSet (s σ) := by
      have hc : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      exact (isClosed_monotone.preimage hc).measurableSet
    have hcover : (⋃ σ, s σ) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨Tuple.sort x, Tuple.monotone_sort x⟩
    have hpiece (σ : Equiv.Perm (Fin n)) :
        AEMeasurable (sortedSample n) ((iidSample μ n).restrict (s σ)) := by
      have hp : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      apply hp.aemeasurable.congr
      exact ae_restrict_of_forall_mem (hs σ) (fun x hx =>
        (show (fun x => x ∘ σ) x = sortedSample n x from
          (Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 hx))
    simpa only [hcover, Measure.restrict_univ] using (AEMeasurable.iUnion hpiece)
  have hmeas : AEStronglyMeasurable
      (fun x => (sortedGap n k x) ^ 2) (iidSample μ n) := by
    have hp : Measurable (fun y : Fin n → ℝ => (y hi - y lo) ^ 2) := by fun_prop
    have h := hp.aestronglyMeasurable.comp_aemeasurable hsort
    convert h using 1
    funext x
    simp [sortedGap, hk, sortedSample, lo, hi]
  have hfinite : (iidSample μ n) Set.univ ≠ ⊤ := by
    simp [iidSample]
  have hbound : ∀ᵐ x ∂iidSample μ n,
      ‖(sortedGap n k x) ^ 2‖ ≤ (b - a) ^ 2 := by
    filter_upwards [iid_support_interval_ae μ a b hsupp n] with x hx
    have hmono : sortedSample n x lo ≤ sortedSample n x hi :=
      (Tuple.monotone_sort x) (by simp [lo, hi, Fin.le_def])
    have hlo : a ≤ sortedSample n x lo := (hx (Tuple.sort x lo)).1
    have hhi : sortedSample n x hi ≤ b := (hx (Tuple.sort x hi)).2
    have hgap : sortedGap n k x = sortedSample n x hi - sortedSample n x lo := by
      simp [sortedGap, hk, lo, hi]
    have hg0 : 0 ≤ sortedGap n k x := by rw [hgap]; linarith
    have hgle : sortedGap n k x ≤ b - a := by rw [hgap]; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hg0 (by linarith)).2 hgle
  exact integrableOn_univ.mp
    (Measure.integrableOn_of_bounded hfinite hmeas
      (by simpa only [Measure.restrict_univ] using hbound) :
      IntegrableOn (fun x => (sortedGap n k x) ^ 2) Set.univ (iidSample μ n))

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [density constants and their order](hyp:cg,Cg,hcg,hCg), [a density](hyp:p), [its density representation](hyp:hμ), [an almost-everywhere density envelope](hyp:hbound), [a sample size and adjacent-gap index](hyp:n,k), [proof that the gap is interior](hyp:hk), [a real sample](hyp:x), and [coordinatewise interval membership](hyp:hx), [the sorted CDF gap lies between the density constants times the original gap](goal). -/
theorem sortedGap_cdf_linear_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b cg Cg : ℝ) (p : ℝ → ℝ)
    (hcg : 0 < cg) (hCg : cg ≤ Cg)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), cg ≤ p x ∧ p x ≤ Cg)
    (n k : ℕ) (hk : k + 1 < n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc a b) :
    cg * sortedGap n k x ≤
        sortedGap n k (fun i => ProbabilityTheory.cdf μ (x i)) ∧
      sortedGap n k (fun i => ProbabilityTheory.cdf μ (x i)) ≤
        Cg * sortedGap n k x := by
  let lo : Fin n := ⟨k, by omega⟩
  let hi : Fin n := ⟨k + 1, hk⟩
  have hxy : sortedSample n x lo ≤ sortedSample n x hi :=
    (Tuple.monotone_sort x) (by simp [lo, hi, Fin.le_def])
  have hax : a ≤ sortedSample n x lo :=
    (hx (Tuple.sort x lo)).1
  have hyb : sortedSample n x hi ≤ b :=
    (hx (Tuple.sort x hi)).2
  have hinc := cdf_increment_bounds μ a b cg Cg p hcg hCg hμ
    hbound hax hxy hyb
  have hsort := sortedSample_map_monotone n
    (fun z => ProbabilityTheory.cdf μ z) (ProbabilityTheory.monotone_cdf μ) x
  simpa only [sortedGap, dif_pos hk, lo, hi, hsort] using hinc

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [density constants and their order](hyp:cg,Cg,hcg,hCg), [a density](hyp:p), [its density representation](hyp:hμ), [an almost-everywhere density envelope](hyp:hbound), [a sample size and adjacent-gap index](hyp:n,k), [proof that the gap is interior](hyp:hk), [a real sample](hyp:x), and [coordinatewise interval membership](hyp:hx), [the squared sorted CDF gap lies between squared density multiples of the original gap](goal). -/
theorem sortedGap_cdf_square_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b cg Cg : ℝ) (p : ℝ → ℝ)
    (hcg : 0 < cg) (hCg : cg ≤ Cg)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), cg ≤ p x ∧ p x ≤ Cg)
    (n k : ℕ) (hk : k + 1 < n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc a b) :
    cg ^ 2 * (sortedGap n k x) ^ 2 ≤
        (sortedGap n k (fun i => ProbabilityTheory.cdf μ (x i))) ^ 2 ∧
      (sortedGap n k (fun i => ProbabilityTheory.cdf μ (x i))) ^ 2 ≤
        Cg ^ 2 * (sortedGap n k x) ^ 2 := by
  have hmono := Tuple.monotone_sort x
  have hg0 : 0 ≤ sortedGap n k x := by
    simp only [sortedGap, dif_pos hk]
    exact sub_nonneg.mpr (hmono (by simp [Fin.le_def]))
  have hlin := sortedGap_cdf_linear_bounds μ a b cg Cg p hcg hCg hμ
    hbound n k hk x hx
  have hcg0 : 0 ≤ cg * sortedGap n k x := mul_nonneg hcg.le hg0
  have hCg0 : 0 ≤ Cg * sortedGap n k x :=
    mul_nonneg (le_trans hcg.le hCg) hg0
  have hfg0 : 0 ≤ sortedGap n k (fun i => ProbabilityTheory.cdf μ (x i)) :=
    le_trans hcg0 hlin.1
  have hlow := (sq_le_sq₀ hcg0 hfg0).2 hlin.1
  have hupp := (sq_le_sq₀ hfg0 hCg0).2 hlin.2
  constructor <;> nlinarith [hlow, hupp]

/-- Given [a real probability law](hyp:μ), [a sample size and adjacent-gap index](hyp:n,k), [proof that the gap is interior](hyp:hk), [a continuous CDF](hyp:hcont), and [its coordinatewise iid pushforward identity](hyp:hmap), [the transformed squared sorted gap has the exact unit-uniform second moment](goal). -/
theorem cdf_transformed_gap_second_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n k : ℕ) (hk : k + 1 < n)
    (hcont : Continuous (ProbabilityTheory.cdf μ))
    (hmap : (iidSample μ n).map
      (fun x i => ProbabilityTheory.cdf μ (x i)) = iidSample uniform01 n) :
    ∫ x, (sortedGap n k (fun i => ProbabilityTheory.cdf μ (x i))) ^ 2
      ∂iidSample μ n =
      (2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
  -- Use integral_map for the coordinatewise CDF. The gap function is
  -- a.e. strongly measurable under the uniform product law because it is
  -- integrable there; the uniform law lives on the unit cube.
  have hmeas : Measurable (fun x : Fin n → ℝ =>
      fun i => ProbabilityTheory.cdf μ (x i)) :=
    measurable_pi_lambda _ fun i => hcont.measurable.comp (measurable_pi_apply i)
  have hstrong : AEStronglyMeasurable
      (fun x => (sortedGap n k x) ^ 2) (iidSample uniform01 n) :=
    (uniform_gap_square_integrable n k hk).aestronglyMeasurable
  rw [← hmap] at hstrong
  rw [← integral_map hmeas.aemeasurable hstrong, hmap]
  exact uniform_gap_second_moment n k hk

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [density constants and their order](hyp:cg,Cg,hcg,hCg), [a density](hyp:p), [its density representation](hyp:hμ), [support in that interval](hyp:hsupp), [an almost-everywhere density envelope](hyp:hbound), [a sample size and adjacent-gap index](hyp:n,k), and [proof that the gap is interior](hyp:hk), [the squared sorted-gap moment lies between the inverse squared density bounds times the uniform moment](goal). -/
theorem real_gap_second_moment_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b cg Cg : ℝ) (p : ℝ → ℝ)
    (hcg : 0 < cg) (hCg : cg ≤ Cg)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), cg ≤ p x ∧ p x ≤ Cg)
    (n k : ℕ) (hk : k + 1 < n) :
    (1 / Cg ^ 2) * ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) ≤
      ∫ x, (sortedGap n k x) ^ 2 ∂iidSample μ n ∧
    (∫ x, (sortedGap n k x) ^ 2 ∂iidSample μ n) ≤
      (1 / cg ^ 2) * ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) := by
  let F : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun x i => ProbabilityTheory.cdf μ (x i)
  have hcont := cdf_continuous_of_withDensity μ p hμ
  have hmap := iid_cdf_pushforward_uniform01 μ p hμ n
  have hmeas : Measurable F :=
    measurable_pi_lambda _ fun i => hcont.measurable.comp (measurable_pi_apply i)
  have horig : Integrable (fun x => (sortedGap n k x) ^ 2) (iidSample μ n) :=
    sortedGap_square_integrable_of_interval_support μ a b hsupp n k hk
  have htrans : Integrable (fun x => (sortedGap n k (F x)) ^ 2) (iidSample μ n) := by
    have hu := uniform_gap_square_integrable n k hk
    rw [← hmap] at hu
    simpa only [Function.comp_def] using hu.comp_measurable hmeas
  have hpoint : ∀ᵐ x ∂iidSample μ n,
      cg ^ 2 * (sortedGap n k x) ^ 2 ≤ (sortedGap n k (F x)) ^ 2 ∧
      (sortedGap n k (F x)) ^ 2 ≤ Cg ^ 2 * (sortedGap n k x) ^ 2 := by
    filter_upwards [iid_support_interval_ae μ a b hsupp n] with x hx
    exact sortedGap_cdf_square_bounds μ a b cg Cg p hcg hCg hμ
      hbound n k hk x hx
  have hlow : cg ^ 2 * (∫ x, (sortedGap n k x) ^ 2 ∂iidSample μ n) ≤
      ∫ x, (sortedGap n k (F x)) ^ 2 ∂iidSample μ n := by
    rw [← integral_const_mul]
    exact integral_mono_ae (horig.const_mul _) htrans (hpoint.mono fun x hx => hx.1)
  have hupp : (∫ x, (sortedGap n k (F x)) ^ 2 ∂iidSample μ n) ≤
      Cg ^ 2 * (∫ x, (sortedGap n k x) ^ 2 ∂iidSample μ n) := by
    rw [← integral_const_mul]
    exact integral_mono_ae htrans (horig.const_mul _) (hpoint.mono fun x hx => hx.2)
  have hmoment := cdf_transformed_gap_second_moment μ n k hk hcont hmap
  change (∫ x, (sortedGap n k (F x)) ^ 2 ∂iidSample μ n) = _ at hmoment
  rw [hmoment] at hlow hupp
  have hcg2 : 0 < cg ^ 2 := sq_pos_of_pos hcg
  have hCg2 : 0 < Cg ^ 2 := sq_pos_of_pos (lt_of_lt_of_le hcg hCg)
  constructor
  · have h : ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) / Cg ^ 2 ≤
        ∫ x, (sortedGap n k x) ^ 2 ∂iidSample μ n :=
      (div_le_iff₀ hCg2).2 (by simpa only [mul_comm] using hupp)
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using h
  · have h : (∫ x, (sortedGap n k x) ^ 2 ∂iidSample μ n) ≤
        ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) / cg ^ 2 :=
      (le_div_iff₀ hcg2).2 (by simpa only [mul_comm] using hlow)
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using h

/-- Given [a real probability law](hyp:μ), [interval endpoints](hyp:a,b), [density constants and their order](hyp:cg,Cg,hcg,hCg), [a density](hyp:p), [its density representation](hyp:hμ), [support in that interval](hyp:hsupp), [an almost-everywhere density envelope](hyp:hbound), [a sample size](hyp:n), and [proof that it is even](hyp:hn), [the expected sum of squares of every other sorted gap (the gaps between the order statistics of ranks `2j+1` and `2j+2`, over all `n/2` such pairs) lies between `n/((n+1)(n+2))` divided by the squared upper density constant and `n/((n+1)(n+2))` divided by the squared lower density constant](goal). -/
theorem real_alternating_gap_second_moment_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b cg Cg : ℝ) (p : ℝ → ℝ)
    (hcg : 0 < cg) (hCg : cg ≤ Cg)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), cg ≤ p x ∧ p x ≤ Cg)
    (n : ℕ) (hn : Even n) :
    (1 / Cg ^ 2) * ((n : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) ≤
      ∫ x, (∑ j ∈ Finset.range (n / 2), (sortedGap n (2 * j) x) ^ 2)
        ∂iidSample μ n ∧
    (∫ x, (∑ j ∈ Finset.range (n / 2), (sortedGap n (2 * j) x) ^ 2)
        ∂iidSample μ n) ≤
      (1 / cg ^ 2) * ((n : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) := by
  have heven : 2 * (n / 2) = n := by
    rcases hn with ⟨m, hm⟩
    omega
  have hindex (j : ℕ) (hj : j ∈ Finset.range (n / 2)) : 2 * j + 1 < n := by
    simp only [Finset.mem_range] at hj
    omega
  have hsumconst :
      (∑ _j ∈ Finset.range (n / 2),
        (2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) =
      (n : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hreal : (2 : ℝ) * (n / 2 : ℕ) = n := by exact_mod_cast heven
    have hden : ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  have hfactor (c : ℝ) :
      (∑ _j ∈ Finset.range (n / 2),
        c * ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)))) =
      c * ((n : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) := by
    rw [← Finset.mul_sum, hsumconst]
  rw [integral_finsetSum (Finset.range (n / 2)) (fun j hj =>
    sortedGap_square_integrable_of_interval_support μ a b hsupp n (2 * j)
      (hindex j hj))]
  have hlow :
      (∑ j ∈ Finset.range (n / 2),
        (1 / Cg ^ 2) * ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ)))) ≤
      ∑ j ∈ Finset.range (n / 2),
        ∫ x, (sortedGap n (2 * j) x) ^ 2 ∂iidSample μ n := by
    apply Finset.sum_le_sum
    intro j hj
    exact (real_gap_second_moment_bounds μ a b cg Cg p hcg hCg hμ hsupp
      hbound n (2 * j) (hindex j hj)).1
  have hupp :
      (∑ j ∈ Finset.range (n / 2),
        ∫ x, (sortedGap n (2 * j) x) ^ 2 ∂iidSample μ n) ≤
      ∑ j ∈ Finset.range (n / 2),
        (1 / cg ^ 2) * ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (real_gap_second_moment_bounds μ a b cg Cg p hcg hCg hμ hsupp
      hbound n (2 * j) (hindex j hj)).2
  constructor
  · calc
      _ = ∑ _j ∈ Finset.range (n / 2),
          (1 / Cg ^ 2) * ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) :=
        (hfactor _).symm
      _ ≤ _ := hlow
  · calc
      _ ≤ ∑ _j ∈ Finset.range (n / 2),
          (1 / cg ^ 2) * ((2 : ℝ) / ((n + 1 : ℕ) * (n + 2 : ℕ))) := hupp
      _ = _ := hfactor _

end
end Causalean.Stat.OrderStatistic
