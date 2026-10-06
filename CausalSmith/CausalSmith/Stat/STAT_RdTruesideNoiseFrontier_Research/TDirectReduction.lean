module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DirectLowerAssembly
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.TFiniteCertificate

/-!
# True-side Gaussian measurement-error endpoint frontier

Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- At zero noise only derivative order zero contributes to the public variance. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma kernelVariance_zero (L : ℕ) :
    kernelVariance L 0 = (3/4 : ℝ) *
      ∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2 := by
  unfold kernelVariance
  have ht (j : ℕ) :
      (0 : ℝ)^(2*j) / (Nat.factorial j : ℝ) *
        (∫ x in (0 : ℝ)..1, ((polyDeriv j (endpointKernel L)).eval x)^2) =
      if j = 0 then (∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2) else 0 := by
    by_cases hj : j = 0
    · subst j
      simp [polyDeriv]
    · simp [hj, show 2*j ≠ 0 by omega]
  simp_rw [ht]
  simp

/-- Rounding a real degree at least one down loses at most a factor two, even
for the small-sample range between one and two. Given [the displayed inputs and assumptions](hyp:a,ha), [the stated mathematical conclusion holds](goal). -/
lemma direct_degree_floor_bounds (a : ℝ) (ha : 1 ≤ a) :
    1 ≤ ⌊a⌋₊ ∧ a/2 ≤ (⌊a⌋₊ : ℝ) ∧ (⌊a⌋₊ : ℝ) ≤ a ∧ ⌊a⌋₊ ≤ ⌈a⌉₊ := by
  have hL := (Nat.one_le_floor_iff a).mpr ha
  have hLr : (1 : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast hL
  have hlt := Nat.lt_floor_add_one a
  exact ⟨hL, by linarith, Nat.floor_le (by linarith), Nat.floor_le_ceil a⟩

/-- The direct degree balances the negative kernel-bias exponent and the
square-root variance exponent at the same noiseless rate. Given [the displayed inputs and assumptions](hyp:β,N,hβ,hN), [the stated mathematical conclusion holds](goal). -/
lemma direct_degree_rate_identities (β N : ℝ) (hβ : 0 < β) (hN : 0 < N) :
    (N ^ (1/(4*β+2))) ^ (-2*β) = N ^ (-β/(2*β+1)) ∧
    N ^ (1/(4*β+2)) / Real.sqrt N = N ^ (-β/(2*β+1)) := by
  have hd : 2*β+1 ≠ 0 := by linarith
  constructor
  · rw [← Real.rpow_mul hN.le]
    congr 1
    field_simp
    ring
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hN]
    congr 1
    field_simp
    ring

/-- The rounded direct degree obeys the endpoint bias bound with a uniform
factor four because the public smoothness is at most one. Given [the displayed inputs and assumptions](hyp:β,a,C,L,hβ,ha,hC,hLa,hbias), [the stated mathematical conclusion holds](goal). -/
lemma direct_degree_bias_bound (β a C : ℝ) (L : ℕ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (ha : 1 ≤ a) (hC : 0 ≤ C)
    (hLa : a/2 ≤ (L : ℝ))
    (hbias : kernelMoment L β ≤ C * (L : ℝ)^(-2*β)) :
    kernelMoment L β ≤ 4*C*a^(-2*β) := by
  have ha0 : 0 < a := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < a/2) hLa
    (by linarith [hβ.1] : -2*β ≤ 0)
  have he : (a/2)^(-2*β) = a^(-2*β) * (2 : ℝ)^(2*β) := by
    rw [Real.div_rpow ha0.le (by norm_num), show -2*β = -(2*β) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_inv_eq_mul]
  have htwo : (2 : ℝ)^(2*β) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hβ.2])
      _ = 4 := by norm_num
  calc
    _ ≤ C*(L : ℝ)^(-2*β) := hbias
    _ ≤ C*(a/2)^(-2*β) := mul_le_mul_of_nonneg_left hp hC
    _ = C*(a^(-2*β) * (2 : ℝ)^(2*β)) := by rw [he]
    _ ≤ 4*C*a^(-2*β) := by
      have hh := mul_le_mul_of_nonneg_left htwo
        (mul_nonneg hC (Real.rpow_nonneg ha0.le (-2*β)))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

/-- The zero-noise covariance formula and endpoint squared-mass estimate
bound the public standard-deviation contribution at any degree below a. Given [the displayed inputs and assumptions](hyp:a,C,N,L,ha,hC,hN,hLa,hsq), [the stated mathematical conclusion holds](goal). -/
lemma direct_degree_variance_bound (a C N : ℝ) (L : ℕ)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hN : 0 < N) (hLa : (L : ℝ) ≤ a)
    (hsq : (∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2) ≤ C*(L : ℝ)^2) :
    Real.sqrt (40*kernelVariance L 0/N) ≤ Real.sqrt (30*C)*a/Real.sqrt N := by
  have hvar : 40*kernelVariance L 0/N ≤ (30*C)*a^2/N := by
    rw [kernelVariance_zero]
    apply div_le_div_of_nonneg_right _ hN.le
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ L) hLa 2
    have hm := mul_le_mul_of_nonneg_left hpow hC
    nlinarith only [hsq, hm]
  apply (Real.sqrt_le_sqrt hvar).trans_eq
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq ha]

/-- Public minimization inherits the direct-RD noiseless order from the
rounded balanced degree, using the positive endpoint kernel bounds. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
lemma certificate_zero_rate_bound (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      certificate β n 0 ≤ C*(n : ℝ)^(-β/(2*β+1)) := by
  obtain ⟨K, hK, hk⟩ := positive_endpoint β hβ
  refine ⟨48*K + 28*Real.sqrt (30*K), by positivity, ?_⟩
  intro n hn
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hβpos := hβ.1
  let a : ℝ := (n : ℝ)^(1/(4*β+2))
  have ha : 1 ≤ a := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
    (by positivity)
  obtain ⟨hL, hlo, hhi, hcap⟩ := direct_degree_floor_bounds a ha
  have hb := direct_degree_bias_bound β a K ⌊a⌋₊ hβ ha hK.le hlo (hk _ hL).2.2.1
  have hv := direct_degree_variance_bound a K n ⌊a⌋₊ (by linarith) hK.le hN hhi (hk _ hL).2.2.2
  have hid := direct_degree_rate_identities β n hβ.1 hN
  change a^(-2*β) = _ ∧ a/Real.sqrt (n : ℝ) = _ at hid
  rw [hid.1] at hb
  rw [show Real.sqrt (30*K)*a/Real.sqrt (n : ℝ) =
    Real.sqrt (30*K)*(a/Real.sqrt (n : ℝ)) by ring, hid.2] at hv
  apply (selectedDegree_radius_le β n 0 ⌊a⌋₊ hcap).trans
  rw [radius, if_neg (by omega : ⌊a⌋₊ ≠ 0)]
  nlinarith only [hb, hv]

/-- A finite extended worst-risk bound for the selected estimator also bounds
the real minimax risk, since the estimator belongs to the decision class. Given [the displayed inputs and assumptions](hyp:β,σ,B,n,hB,h), [the stated mathematical conclusion holds](goal). -/
lemma risk_le_of_attainerRisk_le (β σ B : ℝ) (n : ℕ) (hB : 0 ≤ B)
    (h : attainerRisk β n σ ≤ ENNReal.ofReal B) : risk β n σ ≤ B := by
  have hm := Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    (risk := fun (T : Estimator n) (P : {P // Model β σ P}) => absRisk P.val σ n T.val)
    (attainer β n σ)
  have hb := hm.trans h
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hB)

/-- An honest selected interval is an admissible minimax competitor; its
finite worst expected length controls the real minimax length. Given [the displayed inputs and assumptions](hyp:β,σ,B,n,hB,hh,h), [the stated mathematical conclusion holds](goal). -/
lemma lengthRisk_le_of_attainerLength_le (β σ B : ℝ) (n : ℕ) (hB : 0 ≤ B)
    (hh : honestAttainer β n σ ∈ honestIntervals β n σ)
    (h : attainerLength β n σ ≤ ENNReal.ofReal B) : lengthRisk β n σ ≤ B := by
  have hm := Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk
    (risk := fun (I : {I // I ∈ honestIntervals β n σ}) (P : {P // Model β σ P}) =>
      expectedLength P.val σ n I.val)
    ⟨honestAttainer β n σ, hh⟩
  have hb : Causalean.Stat.minimaxValueENNReal
      (fun (I : {I // I ∈ honestIntervals β n σ}) (P : {P // Model β σ P}) =>
        expectedLength P.val σ n I.val) ≤ ENNReal.ofReal B := hm.trans h
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hB)

/-- The direct converse is uniform in all noise, and the selected procedures attain the noiseless order. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
-- @node: thm:direct-reduction
theorem direct_reduction (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n → -- @realizes c(beta-only positive lower constant)
      (∀ σ ∈ Icc (0 : ℝ) 1,
        c * (n : ℝ)^(-β/(2*β+1)) ≤ risk β n σ ∧
        c * (n : ℝ)^(-β/(2*β+1)) ≤ lengthRisk β n σ) ∧
      risk β n 0 ≤ C * (n : ℝ)^(-β/(2*β+1)) ∧
      lengthRisk β n 0 ≤ C * (n : ℝ)^(-β/(2*β+1)) ∧
      attainerRisk β n 0 ≤ ENNReal.ofReal (C * (n : ℝ)^(-β/(2*β+1))) ∧
      attainerLength β n 0 ≤ ENNReal.ofReal (C * (n : ℝ)^(-β/(2*β+1))) ∧
      honestAttainer β n 0 ∈ honestIntervals β n 0 := by
  obtain ⟨K, hK, hrate⟩ := certificate_zero_rate_bound β hβ
  have hlower : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
      c * (n : ℝ)^(-β/(2*β+1)) ≤ risk β n σ ∧
      c * (n : ℝ)^(-β/(2*β+1)) ≤ lengthRisk β n σ := by
    refine ⟨(4 / 5 : ℝ) * kappa, ?_⟩
    exact direct_uniform_lower β hβ
  obtain ⟨c, hc, hlower⟩ := hlower
  refine ⟨c, 2*K, hc, by positivity, ?_⟩
  intro n hn
  let P := directAltLaw β 1 true hβ (by norm_num)
  have hP : Model β 0 P := directAltLaw_model β 1 0 true hβ (by norm_num)
  have hcert := finite_certificate β 0 n 1 P
    hβ (by norm_num) hn (by omega) hP
  have hh := hcert.2.2.2.1
  have hr := hcert.2.2.2.2.1
  have hl := hcert.2.2.2.2.2
  let r := (n : ℝ)^(-β/(2*β+1))
  have hKr : 0 ≤ K*r := mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _)
  have hb : certificate β n 0 ≤ K*r := hrate n hn
  have hr' : attainerRisk β n 0 ≤ ENNReal.ofReal ((2*K)*r) := by
    apply hr.trans (ENNReal.ofReal_le_ofReal _)
    nlinarith only [hb, hKr]
  have hl' : attainerLength β n 0 ≤ ENNReal.ofReal ((2*K)*r) := by
    apply hl.trans (ENNReal.ofReal_le_ofReal _)
    linarith only [hb]
  exact ⟨hlower n hn,
    risk_le_of_attainerRisk_le β 0 _ n (by positivity) hr',
    lengthRisk_le_of_attainerLength_le β 0 _ n (by positivity) hh hl', hr', hl', hh⟩

end CausalSmith.Stat.RdTruesideNoiseFrontier
