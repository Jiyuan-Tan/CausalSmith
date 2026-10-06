module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketWeightBound

/-! # Common-atom completion of the explicit Jackson packet

Moment annihilation and weighted normalization give the exact identity
`t + u = 1/2`. Consequently the packet parts admit the common-atom
completion from roadmap (6)--(7), with no loss in their kink response.
Strict positivity of the weight is proved for the paper's range, so the
explicit prior witness has no normalization premise. The uniform kink-response
bound remains open.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory

-- @node: packetParts_mass_match
/-- Degree-zero annihilation equates the actual masses of the two packet parts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK), the [stated conclusion](goal) holds. -/
lemma packetParts_mass_match {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    (M : ℝ) :
    packetPositive A₀ K M Set.univ = packetNegative A₀ K M Set.univ := by
  let := packetPositive_finite A₀ K M
  let := packetNegative_finite A₀ K M
  have hm := packetParts_moments_match hA hK M (j := 0) (by omega)
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one, Measure.real] at hm
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hm

-- @node: packetParts_half_normalization
/-- Equal degree-zero and degree-one moments split the combined weighted normalization equally between the two Jordan parts, as in roadmap (6). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hM,hW), the [stated conclusion](goal) holds. -/
lemma packetParts_half_normalization {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    {M : ℝ} (hM : 0 ≤ M) (hW : 0 < packetWeight A₀ K M) :
    (packetPositive A₀ K M Set.univ).toReal +
      (∫ z, z ∂packetPositive A₀ K M) = 1 / 2 := by
  have hn := packetParts_mass_add_moment A₀ K hM hW
  have hm := packetParts_mass_match hA hK M
  have hu := packetParts_moments_match hA hK M (j := 1) (by omega)
  simp only [pow_one] at hu
  rw [← hm, ← hu] at hn
  linarith

-- @node: packetParts_commonAtomDomain
/-- Positive weight makes the concrete packet admissible for the common-atom map: its positive mass is at most one half, hence strictly less than one. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hM,hW), the [stated conclusion](goal) holds. -/
lemma packetParts_commonAtomDomain {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    {M : ℝ} (hM : 0 ≤ M) (hW : 0 < packetWeight A₀ K M) :
    CommonAtomDomain (packetPositive A₀ K M) (packetNegative A₀ K M) := by
  let := packetPositive_finite A₀ K M
  have hn := packetParts_half_normalization hA hK hM hW
  have hu : 0 ≤ ∫ z, z ∂packetPositive A₀ K M := by
    apply integral_nonneg_of_ae
    filter_upwards [show ∀ᵐ z ∂packetPositive A₀ K M, z ∈ Set.Icc 0 M from
      mem_ae_iff.mpr (packetPositive_support A₀ K hM)] with z hz
    exact hz.1
  apply (packetParts_commonAtomDomain_iff A₀ K hM).mpr
  apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mp
  simp only [ENNReal.toReal_one]
  linarith

/-- The explicit packet completes to probability priors supported on `[0,M]`, with mean one and matching moments through K. The common atom lies in `[1/2,2]`, and the objective gap is exactly the normalized circle response. This assembles the construction portion of roadmap (30), using proved positivity of the normalization weight. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hM), the [stated conclusion](goal) holds. -/
lemma packetCompletion_witness {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    {M : ℝ} (hM : 2 ≤ M) (ε : ℝ) :
    ∃ (p : ConstrainedPriorPair K M),
      ∃ hdom : CommonAtomDomain (packetPositive A₀ K M) (packetNegative A₀ K M),
      (packetPositive A₀ K M Set.univ).toReal ≤ 1 / 2 ∧
      (1 / 2 : ℝ) ≤ (1 - ∫ z, z ∂packetPositive A₀ K M) /
        (1 - (packetPositive A₀ K M Set.univ).toReal) ∧
      (1 - ∫ z, z ∂packetPositive A₀ K M) /
        (1 - (packetPositive A₀ K M Set.univ).toReal) ≤ 2 ∧
      commonAtomCompletion (packetPositive A₀ K M) (packetNegative A₀ K M) hdom =
        (p.ν₀, p.ν₁) ∧
      (∫ z, phiEpsFormula ε z ∂p.ν₁) - (∫ z, phiEpsFormula ε z ∂p.ν₀) =
        ∫ t in Set.Icc (-Real.pi) Real.pi,
          (packetWave A₀ K M t / packetWeight A₀ K M / (2 * Real.pi)) *
            phiEpsFormula ε (packetIntensity M t) := by
  have hW := packetWeight_pos hA hK hM
  have hM0 : 0 ≤ M := by linarith
  have hdom := packetParts_commonAtomDomain hA hK hM0 hW
  have hn := packetParts_half_normalization hA hK hM0 hW
  have hu : 0 ≤ ∫ z, z ∂packetPositive A₀ K M := by
    apply integral_nonneg_of_ae
    filter_upwards [show ∀ᵐ z ∂packetPositive A₀ K M, z ∈ Set.Icc 0 M from
      mem_ae_iff.mpr (packetPositive_support A₀ K hM0)] with z hz
    exact hz.1
  have hloc := commonAtom_location _ _ ENNReal.toReal_nonneg hu hn
  obtain ⟨p, hp⟩ := commonAtomCompletion_constrained K M (by omega) hM
    _ _ hdom (packetPositive_support A₀ K hM0) (packetNegative_support A₀ K hM0)
    (packetParts_mass_match hA hK M) (fun j hj => packetParts_moments_match hA hK M hj) hn
  refine ⟨p, hdom, hloc.1, hloc.2.1, hloc.2.2, hp, ?_⟩
  have hg := commonAtomCompletion_phiEps_gap _ _ hdom M ε
    (packetPositive_support A₀ K hM0) (packetNegative_support A₀ K hM0)
    (by linarith [hloc.1])
  rw [hp] at hg
  exact hg.trans (packetParts_phiEps_sub A₀ K hM0 ε)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
