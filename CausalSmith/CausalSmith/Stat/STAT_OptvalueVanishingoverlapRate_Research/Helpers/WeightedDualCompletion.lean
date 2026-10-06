module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedFiniteDual
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Common-atom completion of the optimal finite weighted dual

The finite dual's positive and negative atomic parts have equal mass and
first moment. Their weighted normalization gives t+u=1/2. Completing them
by the same atom preserves the exact optimal gap, proving E ≤ Delta.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators

/-- A finite weighted-normalized annihilator completes to a feasible pair, preserving the exact functional pairing. This implements roadmap (6)--(7) for the optimal witness as well as for any finite annihilator. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hM,hmem,hmom,hnorm), the [stated conclusion](goal) holds. -/
theorem finiteWeightedDual_completion {ι : Type} [Fintype ι]
    {K : ℕ} (hK : 1 ≤ K) {M : ℝ} (hM : 2 ≤ M)
    (nodes weights : ι → ℝ) (hmem : ∀ i, nodes i ∈ Set.Icc 0 M)
    (hmom : ∀ j : ℕ, j ≤ K → ∑ i, weights i * nodes i ^ j = 0)
    (hnorm : (∑ i, |weights i| * (1 + nodes i)) = 1) (ε : ℝ) :
    ∃ p : ConstrainedPriorPair K M,
      (∫ z, phiEpsFormula ε z ∂p.ν₁) - (∫ z, phiEpsFormula ε z ∂p.ν₀) =
        ∑ i, weights i * phiEpsFormula ε (nodes i) := by
  classical
  let cp := fun i => max (weights i) 0
  let cm := fun i => max (-weights i) 0
  have hcp (i : ι) : 0 ≤ cp i := le_max_right _ _
  have hcm (i : ι) : 0 ≤ cm i := le_max_right _ _
  have hdiff (i : ι) : cp i - cm i = weights i := by
    dsimp [cp, cm]
    rcases le_total 0 (weights i) with hi | hi
    · rw [max_eq_left hi, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right hi, max_eq_left (by linarith)]
      ring
  have hadd (i : ι) : cp i + cm i = |weights i| := by
    dsimp [cp, cm]
    rcases le_total 0 (weights i) with hi | hi
    · rw [max_eq_left hi, max_eq_right (by linarith), abs_of_nonneg hi]; ring
    · rw [max_eq_right hi, max_eq_left (by linarith), abs_of_nonpos hi]; ring
  let σp := Measure.sum (fun i => ENNReal.ofReal (cp i) • Measure.dirac (nodes i))
  let σm := Measure.sum (fun i => ENNReal.ofReal (cm i) • Measure.dirac (nodes i))
  letI (i : ι) : IsFiniteMeasure (ENNReal.ofReal (cp i) • Measure.dirac (nodes i)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  letI (i : ι) : IsFiniteMeasure (ENNReal.ofReal (cm i) • Measure.dirac (nodes i)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure σp := by dsimp [σp]; infer_instance
  letI : IsFiniteMeasure σm := by dsimp [σm]; infer_instance
  have hip (f : ℝ → ℝ) : (∫ z, f z ∂σp) = ∑ i, cp i * f (nodes i) := by
    dsimp [σp]
    rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), tsum_fintype]
    simp only [ENNReal.toReal_ofReal (hcp _), smul_eq_mul]
  have him (f : ℝ → ℝ) : (∫ z, f z ∂σm) = ∑ i, cm i * f (nodes i) := by
    dsimp [σm]
    rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), tsum_fintype]
    simp only [ENNReal.toReal_ofReal (hcm _), smul_eq_mul]
  have hsuppp : σp (Set.Icc 0 M)ᶜ = 0 := by
    simp [σp, Measure.sum_apply, Measure.smul_apply, hmem]
  have hsuppm : σm (Set.Icc 0 M)ᶜ = 0 := by
    simp [σm, Measure.sum_apply, Measure.smul_apply, hmem]
  have hmassp : (σp Set.univ).toReal = ∑ i, cp i := by
    have h := hip (fun _ => 1)
    simpa only [integral_const, smul_eq_mul, mul_one, Measure.real] using h
  have hmassm : (σm Set.univ).toReal = ∑ i, cm i := by
    have h := him (fun _ => 1)
    simpa only [integral_const, smul_eq_mul, mul_one, Measure.real] using h
  have hmoment : ∀ j : ℕ, j ≤ K → (∫ z, z ^ j ∂σp) = (∫ z, z ^ j ∂σm) := by
    intro j hj
    rw [hip, him]
    apply sub_eq_zero.mp
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, hdiff]
    exact hmom j hj
  have hmass : σp Set.univ = σm Set.univ := by
    have h := hmoment 0 (by omega)
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one, Measure.real] at h
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h
  have hhalf : (σp Set.univ).toReal + (∫ z, z ∂σp) = 1 / 2 := by
    have hzero : (∑ i, cp i) = ∑ i, cm i := by rw [← hmassp, ← hmassm, hmass]
    have hone : (∑ i, cp i * nodes i) = ∑ i, cm i * nodes i := by
      simpa only [pow_one, hip, him] using hmoment 1 hK
    have htotal : (∑ i, cp i) + (∑ i, cm i) +
        ((∑ i, cp i * nodes i) + (∑ i, cm i * nodes i)) = 1 := by
      rw [← hnorm]
      simp_rw [← hadd]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hmassp, hip]
    linarith
  have hu : 0 ≤ ∫ z, z ∂σp := by
    rw [hip]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hcp i) (hmem i).1)
  have ht : (σp Set.univ).toReal ≤ 1 / 2 := by linarith
  have hidp := integrable_of_supported_Icc σp M hsuppp (fun z => z) (by fun_prop)
  have hidm := integrable_of_supported_Icc σm M hsuppm (fun z => z) (by fun_prop)
  have hdom : CommonAtomDomain σp σm := by
    refine ⟨inferInstance, inferInstance, hidp, hidm, ?_⟩
    apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp
    simp only [ENNReal.toReal_one]
    linarith
  obtain ⟨p, hp⟩ := commonAtomCompletion_constrained K M hK hM σp σm hdom
    hsuppp hsuppm hmass hmoment hhalf
  refine ⟨p, ?_⟩
  have hg := commonAtomCompletion_phiEps_gap σp σm hdom M ε hsuppp hsuppm (by linarith)
  rw [hp] at hg
  rw [hg, hip, him, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, hdiff]

/-- Completing the optimal finite dual yields a mean-one probability-prior pair whose absolute gap is exactly E, proving the reverse comparison (8). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hM,hMhi,hε,hεhi), the [stated conclusion](goal) holds. -/
theorem weightedApproxError_le_constrainedPriorSeparation {K : ℕ} (hK : 2 ≤ K)
    {M ε : ℝ} (hM : 2 ≤ M) (hMhi : M ≤ (K : ℝ) ^ 2)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) :
    weightedApproxError K M ε ≤ constrainedPriorSeparation K M ε hK hM hMhi hε hεhi := by
  obtain ⟨nodes, weights, hmem, hmom, hnorm, htarget⟩ :=
    weightedApproxError_finite_dual hK hM hMhi hε hεhi
  obtain ⟨p, hp⟩ := finiteWeightedDual_completion (by omega : 1 ≤ K) hM
    nodes weights hmem hmom hnorm ε
  have hb : BddAbove (Set.range fun p : ConstrainedPriorPair K M =>
      |(∫ z, phiEpsFormula ε z ∂p.ν₁) - (∫ z, phiEpsFormula ε z ∂p.ν₀)|) := by
    refine ⟨4 * sSup ((fun z : ℝ => |phiEpsFormula ε z - (0 : Polynomial ℝ).eval z| /
      (1 + z)) '' Set.Icc 0 M), ?_⟩
    rintro v ⟨q, rfl⟩
    exact constrainedPriorPair_gap_le_polynomial_error q ε (by linarith) 0 (by simp)
  rw [← htarget, ← hp]
  exact le_csSup hb (Set.mem_range_self p)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
