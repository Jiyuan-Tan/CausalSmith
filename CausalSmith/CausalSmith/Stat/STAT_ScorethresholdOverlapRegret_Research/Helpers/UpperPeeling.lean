module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.RiskBounds
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperComparison

/-! # Fourth-moment Markov bounds and geometric peeling

Roadmap steps (4)–(5) for the upper bound. Bounded losses admit a finite
cover by dyadic shells, whose two geometric probability bounds sum uniformly
in the number of shells. No entropy bound or logarithmic multiplier is used.
-/

public section

set_option linter.style.whitespace false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators

/-- An almost-sure shell inclusion and an integrable fourth moment give
Markov's bound even if the shell itself is not presented as measurable. -/
-- @node: upperPeeling_fourth_markov
lemma upperPeeling_fourth_markov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (A : Set Ω)
    (t : ℝ) (ht : 0 < t) (hi : Integrable (fun w => S w ^ 4) μ)
    (hA : ∀ᵐ w ∂μ, w ∈ A → t ≤ S w) :
    μ.real A ≤ (∫ w, S w ^ 4 ∂μ) / t ^ 4 := by
  have hm : μ.real A ≤ μ.real {w | t ^ 4 ≤ S w ^ 4} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hA] with w hw
    intro hwa
    exact pow_le_pow_left₀ ht.le (hw hwa) 4
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun w => S w ^ 4)
    (Filter.Eventually.of_forall fun w => by positivity) hi (t ^ 4)
  apply (le_div_iff₀ (pow_pos ht 4)).2
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hm (pow_nonneg ht.le 4)).trans hmarkov

/-- The radius doubling and fourth power in Markov's inequality produce
exactly the two decaying dyadic factors in roadmap step (4). -/
-- @node: upperPeeling_shell_algebra
lemma upperPeeling_shell_algebra (C n a z : ℝ) (k : ℕ)
    (hn : 0 < n) (ha : 0 < a) (hz : 0 < z) :
    (C * (((2:ℝ)^(k+1)*z)^2/(n^2*a^2) +
      ((2:ℝ)^(k+1)*z)/(n^3*a^3))) / ((2:ℝ)^k*z/8)^4 =
      16384*C*((1/4:ℝ)^k/(n^2*a^2*z^2)) +
        8192*C*((1/8:ℝ)^k/(n^3*a^3*z^3)) := by
  rw [pow_succ]
  have h4 : (1/4:ℝ)^k = 1 / ((2:ℝ)^k)^2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num [div_pow]
  have h8 : (1/8:ℝ)^k = 1 / ((2:ℝ)^k)^3 := by
    rw [← pow_mul, mul_comm k 3, pow_mul]
    norm_num [div_pow]
  rw [h4, h8]
  have hp : (2:ℝ)^k ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Applying fourth-moment Markov to a shell gives its probability bound. -/
-- @node: upperPeeling_shell_probability
lemma upperPeeling_shell_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (A : Set Ω)
    (C n a z : ℝ) (k : ℕ) (hn : 0 < n) (ha : 0 < a) (hz : 0 < z)
    (hi : Integrable (fun w => S w ^ 4) μ)
    (hA : ∀ᵐ w ∂μ, w ∈ A → (2:ℝ)^k*z/8 ≤ S w)
    (hmoment : (∫ w, S w ^ 4 ∂μ) ≤
      C * (((2:ℝ)^(k+1)*z)^2/(n^2*a^2) +
        ((2:ℝ)^(k+1)*z)/(n^3*a^3))) :
    μ.real A ≤ 16384*C*((1/4:ℝ)^k/(n^2*a^2*z^2)) +
      8192*C*((1/8:ℝ)^k/(n^3*a^3*z^3)) := by
  have ht : 0 < (2:ℝ)^k*z/8 := by positivity
  calc
    μ.real A ≤ (∫ w, S w ^ 4 ∂μ) / ((2:ℝ)^k*z/8)^4 :=
      upperPeeling_fourth_markov μ S A _ ht hi hA
    _ ≤ (C * (((2:ℝ)^(k+1)*z)^2/(n^2*a^2) +
        ((2:ℝ)^(k+1)*z)/(n^3*a^3))) / ((2:ℝ)^k*z/8)^4 :=
      div_le_div_of_nonneg_right hmoment (by positivity)
    _ = _ := upperPeeling_shell_algebra C n a z k hn ha hz

/-- A bounded loss above a positive radius lies in one of finitely many
dyadic shells. This is the finite form of the geometric peeling cover. -/
-- @node: upperPeeling_finite_shell_cover
lemma upperPeeling_finite_shell_cover (B z : ℝ) (hz : 0 < z) :
    ∃ K : ℕ, ∀ t : ℝ, z ≤ t → t ≤ B →
      ∃ k : Fin K, (2:ℝ)^k.val*z ≤ t ∧ t < (2:ℝ)^(k.val+1)*z := by
  obtain ⟨L, hL⟩ := exists_nat_pow_near
    (show (1:ℝ) ≤ max 1 (B/z) from le_max_left _ _) (by norm_num : (1:ℝ) < 2)
  refine ⟨L+1, ?_⟩
  intro t ht htB
  obtain ⟨k, hk⟩ := exists_nat_pow_near ((le_div_iff₀ hz).2 (by simpa using ht))
    (by norm_num : (1:ℝ) < 2)
  have hlt : (2:ℝ)^k < (2:ℝ)^(L+1) :=
    hk.1.trans_lt ((div_le_div_of_nonneg_right htB hz.le).trans_lt
      ((le_max_right _ _).trans_lt hL.2))
  have hkL : k < L+1 := by
    by_contra h
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_of_not_gt h)
    exact (not_lt_of_ge hp) hlt
  exact ⟨⟨k, hkL⟩, (le_div_iff₀ hz).1 hk.1, (div_lt_iff₀ hz).1 hk.2⟩

/-- Both geometric series have a uniform finite-sum bound, independent
of the number of occupied shells. -/
-- @node: upperPeeling_geometric_sum
lemma upperPeeling_geometric_sum (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (K : ℕ) :
    (∑ k ∈ Finset.range K, (A*(1/4:ℝ)^k + B*(1/8:ℝ)^k)) ≤
      (4/3:ℝ)*A + (8/7:ℝ)*B := by
  have h4 := geom_sum_mul_neg (1/4:ℝ) K
  have h8 := geom_sum_mul_neg (1/8:ℝ) K
  have hb4 : (∑ k ∈ Finset.range K, (1/4:ℝ)^k) ≤ 4/3 := by
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) K]
  have hb8 : (∑ k ∈ Finset.range K, (1/8:ℝ)^k) ≤ 8/7 := by
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/8) K]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hb4 hA, mul_le_mul_of_nonneg_left hb8 hB]

/-- Summing dyadic shell probabilities gives roadmap step (5), with no
factor depending on the number of shells. -/
-- @node: upperPeeling_tail_probability
lemma upperPeeling_tail_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (T : Ω → ℝ)
    (A B z cap : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hz : 0 < z)
    (hcap : ∀ᵐ w ∂μ, T w ≤ cap)
    (hshell : ∀ k : ℕ,
      μ.real {w | (2:ℝ)^k*z ≤ T w ∧ T w < (2:ℝ)^(k+1)*z} ≤
        A*(1/4:ℝ)^k + B*(1/8:ℝ)^k) :
    μ.real {w | z ≤ T w} ≤ (4/3:ℝ)*A + (8/7:ℝ)*B := by
  classical
  obtain ⟨K, hK⟩ := upperPeeling_finite_shell_cover cap z hz
  let E : Fin K → Set Ω := fun k =>
    {w | (2:ℝ)^k.val*z ≤ T w ∧ T w < (2:ℝ)^(k.val+1)*z}
  have hcover : μ.real {w | z ≤ T w} ≤ μ.real (⋃ k, E k) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hcap] with w hw
    intro ht
    obtain ⟨k, hk⟩ := hK (T w) ht hw
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  calc
    μ.real {w | z ≤ T w} ≤ μ.real (⋃ k, E k) := hcover
    _ ≤ ∑ k : Fin K, μ.real (E k) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ k : Fin K, (A*(1/4:ℝ)^k.val + B*(1/8:ℝ)^k.val) :=
      Finset.sum_le_sum fun k _ => hshell k.val
    _ = ∑ k ∈ Finset.range K, (A*(1/4:ℝ)^k + B*(1/8:ℝ)^k) :=
      Fin.sum_univ_eq_sum_range (fun k => A*(1/4:ℝ)^k + B*(1/8:ℝ)^k) K
    _ ≤ _ := upperPeeling_geometric_sum A B hA hB K

/-- Threshold-policy regularized loss is between zero and three, as used
in the bounded-loss part of the upper-bound roadmap. -/
-- @node: upperPeeling_regularizedLoss_bounds
lemma upperPeeling_regularizedLoss_bounds (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a) (π : ℝ → Bool) (hπ : π ∈ thresholdClass) :
    0 ≤ regularizedLoss P a π ∧ regularizedLoss P a π ≤ 3 := by
  haveI : IsProbabilityMeasure P.PX := scoreLaw_isProbability P hP.wf
  have hw := regret_eq_effect_disagreement α γ θ n P e hP π
    (thresholdClass_mem_binaryPolicyClass π hπ)
  change rawRegret P π = _ at hw
  have hr0 : 0 ≤ rawRegret P π := by
    rw [hw]
    apply integral_nonneg
    intro x
    unfold effectMagnitude
    positivity
  have hr2 : rawRegret P π ≤ 2 := by
    rw [hw]
    have hb := norm_integral_le_of_norm_le_const (μ := P.PX) (C := 2)
      (f := fun x => effectMagnitude P x *
        (if π x = canonicalPolicy P x then (0:ℝ) else 1)) (by
      filter_upwards [hP.effectBound] with x hx
      split_ifs <;> simp [effectMagnitude, hx])
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (le_abs_self _).trans hb
  have hg : ∀ᵐ x ∂P.PX, 0 ≤ offsetG a P.logger x ∧ offsetG a P.logger x ≤ 1 := by
    filter_upwards [hP.positive, ae_iff.mpr hP.score.2] with x hx hs
    have he : 0 < P.logger x ∧ P.logger x < 1 := by
      simpa only [← hP.known hs] using hx
    have hp : 0 < min (P.logger x) (1-P.logger x) :=
      lt_min he.1 (by linarith [he.2])
    exact ⟨le_min zero_le_one (div_nonneg ha.le hp.le), min_le_left _ _⟩
  have hg0 : 0 ≤ offsetDisagreement P a π := by
    apply integral_nonneg_of_ae
    filter_upwards [hg] with x hx
    exact mul_nonneg hx.1 (by positivity)
  have hg1 : offsetDisagreement P a π ≤ 1 := by
    have hb := norm_integral_le_of_norm_le_const (μ := P.PX) (C := 1)
      (f := fun x => offsetG a P.logger x *
        (if π x = canonicalPolicy P x then (0:ℝ) else 1)) (by
      filter_upwards [hg] with x hx
      rw [Real.norm_eq_abs]
      split_ifs <;> simp [abs_of_nonneg hx.1, hx.2])
    simpa only [offsetDisagreement, Real.norm_eq_abs, probReal_univ, mul_one] using
      (le_abs_self _).trans hb
  unfold regularizedLoss
  exact ⟨add_nonneg hr0 hg0, by linarith⟩

/-- The actual supplied-logger selector satisfies the shell probability
bound when the localized process fourth moment is available. -/
-- @node: upperPeeling_selector_shell_probability
lemma upperPeeling_selector_shell_probability (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a z C : ℝ) (hn : 0 < n) (ha : 0 < a ∧ a ≤ 1/4) (hz : 0 < z)
    (hbias : 16*biasFunctional P a ≤ z) (k : ℕ)
    (hi : Integrable (fun d : Fin n → Observation =>
      (localizedProcess P a ((2:ℝ)^(k+1)*z) d)^4) (sampleLaw P n))
    (hmoment : (∫ d, (localizedProcess P a ((2:ℝ)^(k+1)*z) d)^4
      ∂sampleLaw P n) ≤ C * (((2:ℝ)^(k+1)*z)^2/((n:ℝ)^2*a^2) +
        ((2:ℝ)^(k+1)*z)/((n:ℝ)^3*a^3))) :
    (sampleLaw P n).real {d | (2:ℝ)^k*z ≤
      regularizedLoss P a (sortedSelector a e d) ∧
        regularizedLoss P a (sortedSelector a e d) < (2:ℝ)^(k+1)*z} ≤
      16384*C*((1/4:ℝ)^k/((n:ℝ)^2*a^2*z^2)) +
        8192*C*((1/8:ℝ)^k/((n:ℝ)^3*a^3*z^3)) := by
  haveI := sampleLaw_isProbability P n hP.wf
  apply upperPeeling_shell_probability (sampleLaw P n) _ _ C (n:ℝ) a z k
    (by exact_mod_cast hn) ha.1 hz hi _ hmoment
  filter_upwards [upperComparison_selector_shell_ae α γ θ n P e hP a ha z hbias]
    with d hd
  exact fun h => hd k h.1 h.2

/-- The fourth-moment bounds yield the no-log tail bound for the exact
selector, with an explicit universal numerical constant. -/
-- @node: upperPeeling_selector_tail_probability
lemma upperPeeling_selector_tail_probability (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a z C : ℝ) (hn : 0 < n) (ha : 0 < a ∧ a ≤ 1/4) (hz : 0 < z)
    (hC : 0 ≤ C) (hbias : 16*biasFunctional P a ≤ z)
    (hi : ∀ k : ℕ, Integrable (fun d : Fin n → Observation =>
      (localizedProcess P a ((2:ℝ)^(k+1)*z) d)^4) (sampleLaw P n))
    (hmoment : ∀ k : ℕ, (∫ d,
      (localizedProcess P a ((2:ℝ)^(k+1)*z) d)^4 ∂sampleLaw P n) ≤
        C * (((2:ℝ)^(k+1)*z)^2/((n:ℝ)^2*a^2) +
          ((2:ℝ)^(k+1)*z)/((n:ℝ)^3*a^3))) :
    (sampleLaw P n).real {d | z ≤ regularizedLoss P a (sortedSelector a e d)} ≤
      32768*C*(1/((n:ℝ)^2*a^2*z^2) + 1/((n:ℝ)^3*a^3*z^3)) := by
  haveI := sampleLaw_isProbability P n hP.wf
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have ha0 : 0 < a := ha.1
  have hb := upperPeeling_tail_probability (sampleLaw P n)
    (fun d => regularizedLoss P a (sortedSelector a e d))
    (16384*C/((n:ℝ)^2*a^2*z^2)) (8192*C/((n:ℝ)^3*a^3*z^3)) z 3
    (by positivity) (by positivity) hz
    (Filter.Eventually.of_forall fun d =>
      (upperPeeling_regularizedLoss_bounds α γ θ n P e hP a ha.1 _
        (firstScannedMinimizer_mem_thresholdClass a e d)).2) (by
      intro k
      convert upperPeeling_selector_shell_probability α γ θ n P e hP a z C
        hn ha hz hbias k (hi k) (hmoment k) using 1 <;> ring)
  apply hb.trans
  have hA : 0 ≤ C/((n:ℝ)^2*a^2*z^2) := by positivity
  have hB : 0 ≤ C/((n:ℝ)^3*a^3*z^3) := by positivity
  ring_nf at hA hB ⊢
  nlinarith

end CausalSmith.Stat.ScorethresholdOverlapRegret
