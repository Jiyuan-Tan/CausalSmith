module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TBoundedMomentCertificate
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.RateBounds
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.PermutationLowerBound
public import Causalean.Stat.Minimax.FanoInformationRadius
public import Causalean.Mathlib.InformationTheory.KLBind
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Permutation submodel and minimax order for full-cover label recovery. -/

public section

open MeasureTheory ProbabilityTheory

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- The permutation family has enough entropy for the logarithmic label lower bound. -/
-- @node: permutation_log_card_lower
lemma permutation_log_card_lower (p : ℕ) (hp : 4 ≤ p) :
    (p : ℝ) / 4 * Real.log p ≤ Real.log (Nat.factorial p) := by
  have hp0 : p ≠ 0 := by omega
  have h := Stirling.le_log_factorial_stirling hp0
  have hlog : (4 / 3 : ℝ) ≤ Real.log p := by
    have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
    have hh : (4 / 3 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0)]
      nlinarith [Real.log_two_gt_d9]
    exact hh.trans (Real.log_le_log (by norm_num) hpR)
  have hpR : (0 : ℝ) ≤ p := by positivity
  have hrest : (0 : ℝ) ≤ Real.log p / 2 + Real.log (2 * Real.pi) / 2 := by
    have hpLog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hpiLog : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    linarith
  nlinarith

/-- Fano's information radius yields error at least one quarter at the stated rate. -/
-- @node: permutation_fano_numeric
lemma permutation_fano_numeric (p n : ℕ) (a : ℝ) (hp : 4 ≤ p)
    (hrate : (n : ℝ) * a ^ 2 ≤ Real.log p / 8) :
    1 / 4 ≤ 1 - ((n : ℝ) * p * a ^ 2 / 2 + Real.log 2) /
      Real.log (Nat.factorial p) := by
  have hfac := permutation_log_card_lower p hp
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogfac : 0 < Real.log (Nat.factorial p) := by
    nlinarith
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hlogp2 : 2 * Real.log 2 ≤ Real.log p := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) hpR
  have haux : 2 * Real.log 2 ≤ Real.log (Nat.factorial p) := by
    nlinarith
  have hrate' : (n : ℝ) * p * a ^ 2 / 2 ≤
      (p : ℝ) / 16 * Real.log p := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ p by positivity)
      (show (0 : ℝ) ≤ Real.log p by positivity)]
  have hcore : (n : ℝ) * p * a ^ 2 / 2 + Real.log 2 ≤
      (3 / 4 : ℝ) * Real.log (Nat.factorial p) := by
    nlinarith
  exact (le_sub_iff_add_le).2 (by
    apply (div_le_iff₀ hlogfac).2 at hcore
    nlinarith)

/-- Fano converts the permutation information budget into a worst-case label error,
including estimators that can abstain. -/
-- @node: permutation_error_of_information
lemma permutation_error_of_information {Ω : Type*} [MeasurableSpace Ω]
    (p n : ℕ) (a : ℝ) (hp : 4 ≤ p)
    (hrate : (n : ℝ) * a ^ 2 ≤ Real.log p / 8)
    (P : Equiv.Perm (Fin p) → Measure Ω)
    [∀ π, IsProbabilityMeasure (P π)]
    (hinfo : Causalean.Stat.uniformMutualInformation P ≤ (n : ℝ) * p * a ^ 2 / 2)
    (est : Ω → Option (Equiv.Perm (Fin p)))
    (hest : ∀ π, MeasurableSet {y | est y = some π}) :
    ∃ π, P π {y | est y ≠ some π} ≥ ENNReal.ofReal (1 / 4) := by
  classical
  let decode : Ω → Equiv.Perm (Fin p) → ℝ :=
    fun y π => if est y = some π then 1 else 0
  have hdecode : Measurable decode := by
    apply measurable_pi_lambda
    intro π
    exact Measurable.ite (hest π) measurable_const measurable_const
  let θ : Equiv.Perm (Fin p) → Equiv.Perm (Fin p) → ℝ :=
    fun π => Pi.single π 1
  have hsep : ∀ i k, i ≠ k → 2 * (1 / 2 : ℝ) ≤ dist (θ i) (θ k) := by
    intro i k hik
    have h := dist_le_pi_dist (θ i) (θ k) i
    simpa [θ, hik, Ne.symm hik, Real.dist_eq] using h
  have hcard : 2 ≤ Fintype.card (Equiv.Perm (Fin p)) := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact (by norm_num : 2 ≤ Nat.factorial 4).trans (Nat.factorial_le hp)
  obtain ⟨π, hπ⟩ := Causalean.Stat.fano_exists_error P hdecode hsep hcard
  have hlog : 0 < Real.log (Fintype.card (Equiv.Perm (Fin p))) :=
    Real.log_pos (by exact_mod_cast (show 1 < Fintype.card (Equiv.Perm (Fin p)) by omega))
  have hbudget := permutation_fano_numeric p n a hp hrate
  have hquarter : (1 / 4 : ℝ) ≤ (P π).real {y | (1 / 2 : ℝ) ≤ dist (decode y) (θ π)} := by
    calc
      1 / 4 ≤ 1 - ((n : ℝ) * p * a ^ 2 / 2 + Real.log 2) /
          Real.log (Fintype.card (Equiv.Perm (Fin p))) := by
        simpa only [Fintype.card_perm, Fintype.card_fin] using hbudget
      _ ≤ 1 - (Causalean.Stat.uniformMutualInformation P + Real.log 2) /
          Real.log (Fintype.card (Equiv.Perm (Fin p))) := by gcongr
      _ ≤ _ := hπ
  apply Exists.intro π
  apply ENNReal.ofReal_le_of_le_toReal
  apply hquarter.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro y hy heq
  have hagree : decode y = θ π := by
    funext k
    simp [decode, θ, heq, Pi.single_apply, eq_comm]
  change (1 / 2 : ℝ) ≤ dist (decode y) (θ π) at hy
  rw [hagree, dist_self] at hy
  norm_num at hy

/-- A reference-law KL budget also bounds errors of independently randomized
permutation estimators. The common seed contributes no KL divergence. -/
-- @node: permutation_randomized_error_of_reference
lemma permutation_randomized_error_of_reference {Ω Seed : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (p n : ℕ) (a : ℝ) (hp : 4 ≤ p)
    (hrate : (n : ℝ) * a ^ 2 ≤ Real.log p / 8)
    (P : Equiv.Perm (Fin p) → Measure Ω)
    [∀ π, IsProbabilityMeasure (P π)]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hKL : ∀ π, InformationTheory.klDiv (P π) Q ≤
      ENNReal.ofReal ((n : ℝ) * p * a ^ 2 / 2))
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (est : Ω × Seed → Option (Equiv.Perm (Fin p)))
    (hest : ∀ π, MeasurableSet {y | est y = some π}) :
    ∃ π, ((P π).prod seedLaw) {y | est y ≠ some π} ≥
      ENNReal.ofReal (1 / 4) := by
  classical
  let R := fun π => (P π).prod seedLaw
  have hKLseed (π : Equiv.Perm (Fin p)) :
      InformationTheory.klDiv (R π) (Q.prod seedLaw) ≤
        ENNReal.ofReal ((n : ℝ) * p * a ^ 2 / 2) := by
    have h := InformationTheory.klDiv_compProd_left
      (μ := P π) (ν := Q) (κ := Kernel.const Ω seedLaw)
    simpa only [Measure.compProd_const] using h.trans_le (hKL π)
  have hfinite (π : Equiv.Perm (Fin p)) :
      InformationTheory.klDiv (R π) (Q.prod seedLaw) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKLseed π)
  have hinfo : Causalean.Stat.uniformMutualInformation R ≤ (n : ℝ) * p * a ^ 2 / 2 := by
    calc
      _ ≤ (Fintype.card (Equiv.Perm (Fin p)) : ℝ)⁻¹ *
          ∑ π, (InformationTheory.klDiv (R π) (Q.prod seedLaw)).toReal :=
        Causalean.Stat.uniformMutualInformation_le_average_kl R (Q.prod seedLaw) hfinite
      _ ≤ (Fintype.card (Equiv.Perm (Fin p)) : ℝ)⁻¹ *
          ∑ _π : Equiv.Perm (Fin p), ((n : ℝ) * p * a ^ 2 / 2) := by
        gcongr with π
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hKLseed π)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  exact permutation_error_of_information p n a hp hrate R hinfo est hest

/-- A sufficiently large multiple of `log p / a²` makes the certificate radius
smaller than half of the direct strength. -/
-- @node: epsN_lt_half_strength_of_rate
lemma epsN_lt_half_strength_of_rate (C ℓ v : ℝ) (hC : 0 < C)
    (hℓ : 0 < ℓ) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p n : ℕ) (a : ℝ),
      4 ≤ p → 0 < n → 0 < a → a ≤ 1 →
      K * Real.log p / a ^ 2 ≤ (n : ℝ) →
      2 * epsN C p n v ℓ (1 / 4) < a := by
  obtain ⟨_, c₂, _, hc₂, hε⟩ :=
    epsN_bounds C ℓ v (1 / 4) hC hℓ hv
      (by norm_num) (by norm_num)
  refine ⟨16 * c₂ ^ 2, by positivity, ?_⟩
  intro p n a hp hn ha _ hrate
  have hp' : 2 ≤ p := by omega
  have hε' := (hε p n hp' hn).2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hratio : 0 ≤ Real.log p / n := div_nonneg hlog hnR.le
  have hsqrt : Real.sqrt (Real.log p / n) ^ 2 = Real.log p / n :=
    Real.sq_sqrt hratio
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hbound : 16 * c₂ ^ 2 * Real.log p ≤ (n : ℝ) * a ^ 2 := by
    apply (div_le_iff₀ ha2).mp at hrate
    nlinarith
  have hx : 4 * c₂ * Real.sqrt (Real.log p / n) ≤ a := by
    have hdiv : 16 * c₂ ^ 2 * (Real.log p / n) ≤ a ^ 2 := by
      calc
        16 * c₂ ^ 2 * (Real.log p / n) =
            (16 * c₂ ^ 2 * Real.log p) / n := by ring
        _ ≤ a ^ 2 := (div_le_iff₀ hnR).2 (by nlinarith [hbound])
    have hsq : (4 * c₂ * Real.sqrt (Real.log p / n)) ^ 2 ≤ a ^ 2 := by
      nlinarith [hsqrt]
    nlinarith [Real.sqrt_nonneg (Real.log p / n)]
  nlinarith

/-- The same logarithmic rate also meets the baseline sample requirement of
the bounded-moment certificate. -/
-- @node: certificate_sample_size_of_rate
lemma certificate_sample_size_of_rate (C ℓ v : ℝ) (hC : 0 < C)
    (hℓ : 0 < ℓ) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p n : ℕ) (a : ℝ),
      4 ≤ p → 0 < n → 0 < a → a ≤ 1 →
      K * Real.log p / a ^ 2 ≤ (n : ℝ) →
      C * max 1 (v * ℓ⁻¹ ^ 4) *
        Real.log (4 * p * (p + 1) / (1 / 4 : ℝ)) ≤ (n : ℝ) ∧
      2 * epsN C p n v ℓ (1 / 4) < a := by
  obtain ⟨K₁, hK₁, hsmall⟩ := epsN_lt_half_strength_of_rate C ℓ v hC hℓ hv
  obtain ⟨Klog, hKlog, hlogs⟩ :=
    log_ratio_bounds (1 / 4) (by norm_num) (by norm_num)
  let K₂ := C * max 1 (v * ℓ⁻¹ ^ 4) * Klog
  have hK₂ : 0 < K₂ := by dsimp [K₂]; positivity
  let K := max K₁ K₂
  refine ⟨K, lt_of_lt_of_le hK₁ (le_max_left _ _), ?_⟩
  intro p n a hp hn ha ha1 hrate
  have hp' : 2 ≤ p := by omega
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2le : a ^ 2 ≤ 1 := by nlinarith
  have hrate' : K * Real.log p ≤ (n : ℝ) * a ^ 2 :=
    (div_le_iff₀ ha2).mp hrate
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hnbound : (n : ℝ) * a ^ 2 ≤ n := by nlinarith
  constructor
  · have hloghi := (hlogs p hp').2
    have hK₂bound : K₂ * Real.log p ≤ (n : ℝ) := by
      have hK₂le : K₂ ≤ K := le_max_right _ _
      nlinarith
    have hcoef : 0 ≤ C * max 1 (v * ℓ⁻¹ ^ 4) := by positivity
    calc
      C * max 1 (v * ℓ⁻¹ ^ 4) *
          Real.log (4 * p * (p + 1) / (1 / 4 : ℝ)) ≤
        C * max 1 (v * ℓ⁻¹ ^ 4) * (Klog * Real.log p) :=
          mul_le_mul_of_nonneg_left hloghi hcoef
      _ = K₂ * Real.log p := by dsimp [K₂]; ring
      _ ≤ n := hK₂bound
  · apply hsmall p n a hp hn ha ha1
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left K₁ K₂) hlogp) ha2.le).trans hrate

/-- At the logarithmic sample rate, the bounded-moment certificate recovers
every label of a full-cover model with probability at least three quarters. -/
-- @node: full_cover_label_recovery_of_rate
lemma full_cover_label_recovery_of_rate (ℓ v : ℝ)
    (hℓ : 0 < ℓ) (hℓle : ℓ ≤ Real.exp (1 / 2)) (hv : 0 < v) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (p n : ℕ) (a : ℝ), 4 ≤ p → 0 < n → 0 < a → a ≤ 1 →
      K * Real.log p / a ^ 2 ≤ (n : ℝ) →
      ∃ hεn : 0 < epsN C p n v ℓ (1 / 4),
      ∀ (Ω : Type) (ms : MeasurableSpace Ω) (μ : Measure Ω),
        letI : MeasurableSpace Ω := ms
        ∀ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
          (𝔐 : AtomicCountModel p p Ω μ),
          μ Set.univ = 1 →
          ∀ ht : Function.Bijective 𝔐.t,
          a ≤ minStrength μ 𝔐 →
          (∀ e r, μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
            obsLaw μ 𝔐 e) →
          μ {ω | oneSidedCertificate
              (robustShiftEstimator ℓ ⟨1 / 4, by norm_num, by norm_num⟩
                (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω))
              ⟨epsN C p n v ℓ (1 / 4), hεn⟩ =
                some (Equiv.ofBijective 𝔐.t ht)} ≥
            ENNReal.ofReal (3 / 4) := by
  obtain ⟨C, hC, hcert⟩ := bounded_moment_certificate
  obtain ⟨K, hK, hrate⟩ := certificate_sample_size_of_rate C ℓ v hC hℓ hv
  refine ⟨C, K, hC, hK, ?_⟩
  intro p n a hp hn ha ha1 hnrate
  obtain ⟨hlarge, hsmall⟩ := hrate p n a hp hn ha ha1 hnrate
  let r₀ : Fin n := ⟨0, hn⟩
  have hp0 : 0 < p := by omega
  have hεn : 0 < epsN C p n v ℓ (1 / 4) := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp0
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have harg : 1 < 4 * (p : ℝ) * (p + 1) / (1 / 4 : ℝ) := by
      norm_num
      nlinarith
    have hlog : 0 < Real.log (4 * (p : ℝ) * (p + 1) / (1 / 4 : ℝ)) :=
      Real.log_pos harg
    dsimp [epsN]
    positivity
  refine ⟨hεn, ?_⟩
  intro Ω ms μ
  letI : MeasurableSpace Ω := ms
  intro 𝒬 𝔐 hμ ht hstrength hLaw
  obtain ⟨_, hεcert, htwo⟩ :=
    hcert p n ℓ v (1 / 4) hp0 hn hℓ hℓle hv
      (by norm_num) (by norm_num) hlarge Ω ms μ 𝒬 r₀ hμ
  have hproof : hεcert = hεn := Subsingleton.elim _ _
  subst hεcert
  simpa only [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] using
    (htwo Ω ms μ 𝔐 ht hLaw).2 (lt_of_lt_of_le hsmall hstrength)

/-- Both unit-offset factorial variance formulas are bounded by the
envelope at the largest coordinate mean. -/
-- @node: unit_offset_variance_envelope
lemma unit_offset_variance_envelope (μ a : ℝ) (hμ : μ ≤ a) :
    Real.exp (μ + 1 / 2) + (Real.exp 1 - 1) * Real.exp (2 * μ + 1) ≤ v0 a ∧
    4 * Real.exp (3 * μ + 9 / 2) + 2 * Real.exp (2 * μ + 2) +
      Real.exp (4 * μ + 8) - Real.exp (4 * μ + 4) ≤ v0 a := by
  have he : 0 ≤ Real.exp 4 - 1 := by
    have : 1 ≤ Real.exp (4 : ℝ) := Real.one_le_exp (by norm_num)
    linarith
  have he1 : 0 ≤ Real.exp 1 - 1 := by
    have : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
    linarith
  have h₁ := Real.exp_le_exp.mpr (show μ + 1 / 2 ≤ a + 1 / 2 by linarith)
  have h₂ := Real.exp_le_exp.mpr (show 2 * μ + 1 ≤ 2 * a + 1 by linarith)
  have h₃ := Real.exp_le_exp.mpr (show 3 * μ + 9 / 2 ≤ 3 * a + 9 / 2 by linarith)
  have h₄ := Real.exp_le_exp.mpr (show 2 * μ + 2 ≤ 2 * a + 2 by linarith)
  have h₅ := Real.exp_le_exp.mpr (show 4 * μ + 4 ≤ 4 * a + 4 by linarith)
  have hid (x : ℝ) : Real.exp (4 * x + 8) - Real.exp (4 * x + 4) =
      (Real.exp 4 - 1) * Real.exp (4 * x + 4) := by
    rw [show 4 * x + 8 = (4 * x + 4) + 4 by ring, Real.exp_add]
    ring
  have hfirst : Real.exp (μ + 1 / 2) + (Real.exp 1 - 1) * Real.exp (2 * μ + 1) ≤
      Real.exp (a + 1 / 2) + (Real.exp 1 - 1) * Real.exp (2 * a + 1) := by
    nlinarith [mul_nonneg he1 (sub_nonneg.mpr h₂)]
  have hsecond : 4 * Real.exp (3 * μ + 9 / 2) + 2 * Real.exp (2 * μ + 2) +
      Real.exp (4 * μ + 8) - Real.exp (4 * μ + 4) ≤
      4 * Real.exp (3 * a + 9 / 2) + 2 * Real.exp (2 * a + 2) +
      Real.exp (4 * a + 8) - Real.exp (4 * a + 4) := by
    calc
      _ = 4 * Real.exp (3 * μ + 9 / 2) + 2 * Real.exp (2 * μ + 2) +
          (Real.exp (4 * μ + 8) - Real.exp (4 * μ + 4)) := by ring
      _ ≤ 4 * Real.exp (3 * a + 9 / 2) + 2 * Real.exp (2 * a + 2) +
          (Real.exp (4 * a + 8) - Real.exp (4 * a + 4)) := by
            rw [hid μ, hid a]
            nlinarith [mul_nonneg he (sub_nonneg.mpr h₅)]
      _ = _ := by ring
  constructor <;> unfold v0 <;> simp only [le_max_iff] <;> aesop

-- @node: thm:label-rate-lower-bound
theorem label_rate_lower_bound :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (ℓ v : ℝ), 0 < ℓ → ℓ ≤ Real.exp (1 / 2) →
      ∃ K : ℝ, 0 < K ∧
      ∀ (p n : ℕ) (a : ℝ), 0 < p → 0 < n →
      0 < a → a ≤ 1 → v0 a ≤ v →
      ∃ P : Equiv.Perm (Fin p) → Measure (ObservedSample p n),
        -- @realizes \pi(target-label permutation)
        (∀ π,
          ∃ (Ω : Type) (ms : MeasurableSpace Ω) (μ : Measure Ω),
            letI : MeasurableSpace Ω := ms
            ∃ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
              (𝔐 : AtomicCountModel p p Ω μ),
              μ Set.univ = 1 ∧ P π = obsSampleLaw μ 𝒬 ∧
              𝔐.A = 0 ∧ (∀ e, 𝔐.Ωc e = 1) ∧
              𝔐.η 0 = 0 ∧
              (∀ m, 𝔐.η m.succ = a • Pi.single (π m) 1) ∧
              𝔐.t = π ∧ (∀ m, 𝔐.α m = a) ∧
              (∀ e r ω j, 𝒬.S e r ω j = 1) ∧
              (∀ e r,
                μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
                  obsLaw μ 𝔐 e) ∧
              (∀ m r,
                variance (fun ω =>
                  firstFactorial (𝒬.X m.succ r ω)
                    (𝒬.S m.succ r ω) (π m)) μ =
                  Real.exp (a + 1 / 2) +
                    (Real.exp 1 - 1) * Real.exp (2 * a + 1)) ∧
              (∀ m r,
                variance (fun ω =>
                  secondFactorial (𝒬.X m.succ r ω)
                    (𝒬.S m.succ r ω) (π m)) μ =
                  4 * Real.exp (3 * a + 9 / 2) +
                    2 * Real.exp (2 * a + 2) +
                    Real.exp (4 * a + 8) - Real.exp (4 * a + 4))) ∧
        (4 ≤ p →
          (n * a ^ 2 ≤ c * Real.log p →
            ∀ (Seed : Type) (msSeed : MeasurableSpace Seed)
              (seedLaw : Measure Seed),
              letI : MeasurableSpace Seed := msSeed
              seedLaw Set.univ = 1 →
              ∀ est : ObservedSample p n × Seed →
                Option (Equiv.Perm (Fin p)),
                (∀ π, MeasurableSet {y | est y = some π}) →
                ∃ π, ((P π).prod seedLaw)
                  {y | est y ≠ some π} ≥ ENNReal.ofReal (1 / 4)) ∧
          ((n : ℝ) ≥ K * Real.log p / a ^ 2 →
            ∃ hεn : 0 < epsN C p n v ℓ (1 / 4),
            ∀ (Ω : Type) (ms : MeasurableSpace Ω)
              (μ : Measure Ω),
              letI : MeasurableSpace Ω := ms
              ∀ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
                (𝔐 : AtomicCountModel p p Ω μ),
                μ Set.univ = 1 →
                ∀ ht : Function.Bijective 𝔐.t,
                a ≤ minStrength μ 𝔐 →
                (∀ e r,
                  μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
                    obsLaw μ 𝔐 e) →
                μ {ω | oneSidedCertificate
                    (robustShiftEstimator ℓ ⟨1 / 4, by norm_num, by norm_num⟩
                      (fun e r => 𝒬.S e r ω)
                      (fun e r => 𝒬.X e r ω))
                    ⟨epsN C p n v ℓ (1 / 4), hεn⟩ =
                      some (Equiv.ofBijective 𝔐.t ht)} ≥
                  ENNReal.ofReal (3 / 4))) := by
  obtain ⟨C, hC, hcert⟩ := bounded_moment_certificate
  refine ⟨1 / 8, C, by norm_num, hC, ?_⟩
  intro ℓ v hℓ hℓle
  by_cases hv : 0 < v
  · obtain ⟨K, hK, hrate⟩ :=
      certificate_sample_size_of_rate C ℓ v hC hℓ hv
    refine ⟨K, hK, ?_⟩
    intro p n a hp0 hn ha ha1 hva
    have hcore :
        ∃ P : Equiv.Perm (Fin p) → Measure (ObservedSample p n),
          (∀ π,
            ∃ (Ω : Type) (ms : MeasurableSpace Ω) (μ : Measure Ω),
              letI : MeasurableSpace Ω := ms
              ∃ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
                (𝔐 : AtomicCountModel p p Ω μ),
                μ Set.univ = 1 ∧ P π = obsSampleLaw μ 𝒬 ∧
                𝔐.A = 0 ∧ (∀ e, 𝔐.Ωc e = 1) ∧
                𝔐.η 0 = 0 ∧
                (∀ m, 𝔐.η m.succ = a • Pi.single (π m) 1) ∧
                𝔐.t = π ∧ (∀ m, 𝔐.α m = a) ∧
                (∀ e r ω j, 𝒬.S e r ω j = 1) ∧
                (∀ e r, μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
                  obsLaw μ 𝔐 e) ∧
                (∀ m r,
                  variance (fun ω => firstFactorial
                    (𝒬.X m.succ r ω) (𝒬.S m.succ r ω) (π m)) μ =
                    Real.exp (a + 1 / 2) +
                      (Real.exp 1 - 1) * Real.exp (2 * a + 1)) ∧
                (∀ m r,
                  variance (fun ω => secondFactorial
                    (𝒬.X m.succ r ω) (𝒬.S m.succ r ω) (π m)) μ =
                    4 * Real.exp (3 * a + 9 / 2) +
                      2 * Real.exp (2 * a + 2) +
                      Real.exp (4 * a + 8) - Real.exp (4 * a + 4))) ∧
          (∀ π, IsProbabilityMeasure (P π)) ∧
          ∃ Q : Measure (ObservedSample p n), IsProbabilityMeasure Q ∧
            ∀ π, InformationTheory.klDiv (P π) Q ≤
              ENNReal.ofReal ((n : ℝ) * p * a ^ 2 / 2) := by
      let mkQ := fun π : Equiv.Perm (Fin p) =>
        permutationBoundedMomentClass π hp0 hn ha.le hℓ hℓle hv hva
      let P := fun π : Equiv.Perm (Fin p) =>
        obsSampleLaw (permutationExperimentMeasure π a) (mkQ π)
      refine ⟨P, ?_, ?_, ?_⟩
      · intro π
        let μ := permutationExperimentMeasure (n := n) π a
        let 𝒬 := mkQ π
        let r₀ : Fin n := ⟨0, hn⟩
        let 𝔐 := permutationAtomicModel hp0 r₀ π a ha
        refine ⟨PermutationOmega p n, inferInstance, μ, 𝒬, 𝔐, ?_⟩
        have hvars := permutationExperiment_target_variances
          (n := n) π a v ha.le hva
        refine ⟨by simp [μ], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rfl
        · intro e
          rfl
        · exact permutationEta_zero π a
        · exact permutationEta_succ π a
        · rfl
        · intro m
          rfl
        · intro e r ω j
          exact permutationS_apply e r ω j
        · exact permutation_bounded_model_obsLaw
            hp0 hn hℓ hℓle hv ha hva π r₀
        · simpa [𝒬, mkQ] using hvars.1
        · simpa [𝒬, mkQ] using hvars.2
      · intro π
        rw [show P π = (permutationExperimentMeasure π a).map
            permutationObservation by
          dsimp [P]
          rw [obsSampleLaw_eq_map]
          congr 1
          ]
        exact Measure.isProbabilityMeasure_map
          permutationObservation_measurable.aemeasurable
      · let π₀ : Equiv.Perm (Fin p) := Equiv.refl _
        let Qref : Measure (ObservedSample p n) :=
          (permutationExperimentMeasure (n := n) π₀ 0).map permutationObservation
        refine ⟨Qref, Measure.isProbabilityMeasure_map
          permutationObservation_measurable.aemeasurable, ?_⟩
        intro π
        have hP : P π = (permutationExperimentMeasure π a).map
            permutationObservation := by
          dsimp [P]
          rw [obsSampleLaw_eq_map]
          congr 1
        rw [hP]
        change InformationTheory.klDiv
          ((permutationExperimentMeasure π a).map permutationObservation)
          ((permutationExperimentMeasure π₀ 0).map permutationObservation) ≤ _
        rw [permutationExperimentMeasure_zero_eq π₀ π]
        exact (InformationTheory.klDiv_map_le
          (permutationExperimentMeasure π a)
          (permutationExperimentMeasure π 0)
          permutationObservation_measurable).trans
            (permutationExperiment_kl_reference π a ha.le)
    obtain ⟨P, hmodels, hprob, Q, hQ, hKL⟩ := hcore
    letI (π : Equiv.Perm (Fin p)) : IsProbabilityMeasure (P π) := hprob π
    letI : IsProbabilityMeasure Q := hQ
    refine ⟨P, hmodels, ?_⟩
    intro hp
    have hlower : n * a ^ 2 ≤ (1 / 8 : ℝ) * Real.log p →
        ∀ (Seed : Type) (msSeed : MeasurableSpace Seed) (seedLaw : Measure Seed),
          letI : MeasurableSpace Seed := msSeed
          seedLaw Set.univ = 1 →
          ∀ est : ObservedSample p n × Seed → Option (Equiv.Perm (Fin p)),
            (∀ π, MeasurableSet {y | est y = some π}) →
            ∃ π, ((P π).prod seedLaw) {y | est y ≠ some π} ≥
              ENNReal.ofReal (1 / 4) := by
      intro hnrate Seed msSeed seedLaw
      letI : MeasurableSpace Seed := msSeed
      intro hseed est hest
      letI : IsProbabilityMeasure seedLaw := ⟨hseed⟩
      apply permutation_randomized_error_of_reference p n a hp _ P Q hKL seedLaw est hest
      nlinarith [hnrate]
    have hupper : (n : ℝ) ≥ K * Real.log p / a ^ 2 →
        ∃ hεn : 0 < epsN C p n v ℓ (1 / 4),
        ∀ (Ω : Type) (ms : MeasurableSpace Ω) (μ : Measure Ω),
          letI : MeasurableSpace Ω := ms
          ∀ (𝒬 : BoundedMomentClass p n ℓ v Ω μ)
            (𝔐 : AtomicCountModel p p Ω μ),
            μ Set.univ = 1 →
            ∀ ht : Function.Bijective 𝔐.t,
            a ≤ minStrength μ 𝔐 →
            (∀ e r, μ.map (fun ω => (𝒬.S e r ω, 𝒬.X e r ω)) =
              obsLaw μ 𝔐 e) →
            μ {ω | oneSidedCertificate
                (robustShiftEstimator ℓ ⟨1 / 4, by norm_num, by norm_num⟩
                  (fun e r => 𝒬.S e r ω) (fun e r => 𝒬.X e r ω))
                ⟨epsN C p n v ℓ (1 / 4), hεn⟩ =
                  some (Equiv.ofBijective 𝔐.t ht)} ≥
              ENNReal.ofReal (3 / 4) := by
      intro hnrate
      obtain ⟨hlarge, hsmall⟩ := hrate p n a hp hn ha ha1 hnrate
      let r₀ : Fin n := ⟨0, hn⟩
      have hεn : 0 < epsN C p n v ℓ (1 / 4) := by
        have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp0
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have harg : 1 < 4 * (p : ℝ) * (p + 1) / (1 / 4 : ℝ) := by
          norm_num
          nlinarith
        have hlog : 0 < Real.log (4 * (p : ℝ) * (p + 1) / (1 / 4 : ℝ)) :=
          Real.log_pos harg
        dsimp [epsN]
        positivity
      refine ⟨hεn, ?_⟩
      intro Ω ms μ
      letI : MeasurableSpace Ω := ms
      intro 𝒬 𝔐 hμ ht hstrength hLaw
      obtain ⟨_, hεcert, htwo⟩ :=
        hcert p n ℓ v (1 / 4) hp0 hn hℓ hℓle hv
          (by norm_num) (by norm_num) hlarge Ω ms μ 𝒬 r₀ hμ
      have hproof : hεcert = hεn := Subsingleton.elim _ _
      subst hεcert
      simpa only [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] using
        (htwo Ω ms μ 𝔐 ht hLaw).2 (lt_of_lt_of_le hsmall hstrength)
    exact ⟨hlower, hupper⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro p n a hp0 hn ha ha1 hva
    have hv0 : 0 < v0 a := by
      unfold v0
      have he : 0 ≤ Real.exp 1 - 1 := by
        have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
        linarith
      have hfirst : 0 < Real.exp (a + 1 / 2) +
          (Real.exp 1 - 1) * Real.exp (2 * a + 1) := by positivity
      exact lt_of_lt_of_le hfirst (le_max_left _ _)
    exact False.elim (hv (lt_of_lt_of_le hv0 hva))

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
