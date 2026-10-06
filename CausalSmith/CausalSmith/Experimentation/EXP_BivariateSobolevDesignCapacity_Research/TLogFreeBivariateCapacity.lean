module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.HTTransfer
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.UpperBound
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.Vanishing
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.TPublishedClassInclusion

/-! # Log-free bivariate full-design capacity

All asserted bounds refer to the concrete smoothness-free original-sample design. Both
law-level capacity transfer and the converse-only bounded-density comparison are retained,
as are the oscillating-sequence frontier and Gaussian sample-size corollaries.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The Gaussian identity identifies each admissible design's worst excess with loss.](goal) Under [the stated conditions](hyp:hC,hn,hd,hπ). -/
-- @node: gaussianWorst_eq_worstLoss
lemma gaussianWorst_eq_worstLoss (hC : ClassicalRademacherContraction)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (π : Design n d)
    (hπ : DesignClass n d π) (s : ℝ) :
    gaussianWorst (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) π s = worstLoss π s := by
  unfold gaussianWorst worstLoss
  congr 1
  funext m
  have h := ht_transfer_centeredL2 hC n d hn hd m.val π hπ.fair hπ.outcomeIndep
  change ENNReal.ofReal (gaussianExcessReal _ π m.val) = _
  rw [gaussianExcessReal, h.2.2.2.2, ENNReal.ofReal_toReal (ne_of_lt h.2.2.2.1)]

/-- [ The Gaussian identity also identifies the full admissible-design infimum.](goal) Under [the stated conditions](hyp:hC,hn,hd). -/
-- @node: gaussianCapacity_eq_capacity
lemma gaussianCapacity_eq_capacity (hC : ClassicalRademacherContraction)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (s : ℝ) :
    gaussianCapacity n d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s = capacity n d s := by
  change (⨅ π : {π : Design n d // DesignClass n d π},
    gaussianWorst _ π.val s) = ⨅ π : {π : Design n d // DesignClass n d π},
      worstLoss π.val s
  congr 1
  funext π
  exact gaussianWorst_eq_worstLoss hC n d hn hd π.val π.property s

/-- [ Inverting the upper power bound gives the sufficient sample-size condition.](goal) Under [the stated conditions](hyp:hn,hd,hs,hε,hsize). -/
-- @node: scale_sample_size_sufficient
lemma scale_sample_size_sufficient (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (hsize : (pairCount d : ℝ) * max 1 ((3072 / (4.01 * ε)) ^ (1 / s)) ≤ n) :
    3072 * aScale n d s ≤ 4.01 * ε := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hB : (0 : ℝ) < pairCount d := by exact_mod_cast (Nat.choose_pos hd)
  have he : 0 < 4.01 * ε := by positivity
  have hp : (3072 / (4.01 * ε)) ^ (s⁻¹) ≤ (n : ℝ) / pairCount d := by
    apply (le_div_iff₀ hB).2
    simpa only [one_div, mul_comm] using
      (mul_le_mul_of_nonneg_left (le_max_right 1 _) hB.le).trans hsize
  have hp' := (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) hs).mp hp
  have hratio : ((pairCount d : ℝ) / n) ^ s * ((n : ℝ) / pairCount d) ^ s = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have h : ((pairCount d : ℝ) / n) * ((n : ℝ) / pairCount d) = 1 := by field_simp
    rw [h, Real.one_rpow]
  have hmul := mul_le_mul_of_nonneg_left hp'
    (Real.rpow_nonneg (show 0 ≤ (pairCount d : ℝ) / n by positivity) s)
  rw [hratio] at hmul
  have hbound : 3072 * (((pairCount d : ℝ) / n) ^ s) ≤ 4.01 * ε := by
    have hdiv : 3072 * (((pairCount d : ℝ) / n) ^ s) / (4.01 * ε) ≤ 1 := by
      convert hmul using 1 <;> first | ring | rfl
    simpa only [one_mul] using (div_le_iff₀ he).mp hdiv
  exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)).trans hbound

/-- [ Below saturation, inverting the lower power bound gives the necessary sample size.](goal) Under [the stated conditions](hyp:hn,hd,hs,hε,hsmall,hbound). -/
-- @node: scale_sample_size_necessary
lemma scale_sample_size_necessary (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (hsmall : ε < cLower s / 4.01)
    (hbound : cLower s * aScale n d s ≤ 4.01 * ε) :
    (pairCount d : ℝ) * ((cLower s / (4.01 * ε)) ^ (1 / s)) ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hB : (0 : ℝ) < pairCount d := by exact_mod_cast (Nat.choose_pos hd)
  have he : 0 < 4.01 * ε := by positivity
  have hc : 0 < cLower s := by unfold cLower; positivity
  have hstrict : 4.01 * ε < cLower s := by
    have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4.01)).mp hsmall
    linarith
  have hpow : (((pairCount d : ℝ) / n) ^ s) < 1 := by
    by_contra h
    have ha : aScale n d s = 1 := min_eq_left (le_of_not_gt h)
    rw [ha, mul_one] at hbound
    linarith
  rw [aScale, min_eq_right hpow.le] at hbound
  have hratio : ((pairCount d : ℝ) / n) ^ s * ((n : ℝ) / pairCount d) ^ s = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have h : ((pairCount d : ℝ) / n) * ((n : ℝ) / pairCount d) = 1 := by field_simp
    rw [h, Real.one_rpow]
  have hmul := mul_le_mul_of_nonneg_right hbound
    (Real.rpow_nonneg (show 0 ≤ (n : ℝ) / pairCount d by positivity) s)
  have hpower : cLower s / (4.01 * ε) ≤ ((n : ℝ) / pairCount d) ^ s := by
    apply (div_le_iff₀ he).2
    rw [mul_assoc, hratio, mul_one] at hmul
    simpa only [mul_comm] using hmul
  have hroot := (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) hs).mpr hpower
  simpa only [one_div, mul_comm] using (le_div_iff₀ hB).mp hroot

-- @node: thm:log-free-bivariate-capacity
/-- One original-sample kernel attains the log-free scale for all smoothnesses, with a
legal independent finite prior, the exact published capacity, and the square-root frontier. This uses [the hContraction_of_gate hypothesis](hyp:hContraction_of_gate), [the hExcess_of_gate hypothesis](hyp:hExcess_of_gate), [the stated conclusion](goal). -/
theorem log_free_bivariate_capacity
    (hContraction_of_gate : ClassicalRademacherContraction)
    (hExcess_of_gate : PublishedHTExcessIdentity) :
    (∀ (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d), -- @realizes n(n≥2) @realizes d(d≥2)
      DesignClass n d (piStar n d) ∧
      (n ≤ pairCount d → piStar n d = fairSignKernel n d) ∧
      (pairCount d < n → (piStar n d).val = spectralRoundingKernel n d) ∧
      (∀ seed : SpectralSeeds n d, (∀ h, seed.2.2 h ∈ Icc (0 : ℝ) 1) →
        ∀ x i, (roundingIteration
          (spectralRows (shiftedSample x seed.1 seed.2.1)) seed.2.2 n).1 i =
            sgn (spectralSigns x seed i)) ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 → -- @realizes s(0<s≤1)
        aScale n d s = bScale n d s ∧
        (n < pairCount d → aScale n d s = 1) ∧
        (pairCount d ≤ n → aScale n d s = ((pairCount d : ℝ) / n) ^ s) ∧
        0 < cLower 1 ∧ cLower 1 ≤ cLower s ∧ cLower s < CUpper ∧
        ENNReal.ofReal (cLower 1 * aScale n d s) ≤
          ENNReal.ofReal (cLower s * aScale n d s) ∧
        ENNReal.ofReal (cLower s * aScale n d s) ≤ capacity n d s ∧
        capacity n d s ≤ worstLoss (piStar n d) s ∧
        worstLoss (piStar n d) s ≤ ENNReal.ofReal (3072 * aScale n d s) ∧
        (∀ ξ : PairIdx d (priorCutoff n d) → Bool,
          ∃ hm : Measurable (mXi s (priorCutoff n d) ξ) ∧
            MemLp (mXi s (priorCutoff n d) ξ) 2 (cubeMeasure d) ∧
            (∫ x, mXi s (priorCutoff n d) ξ x ∂cubeMeasure d) = 0,
            SobolevClass d s ⟨mXi s (priorCutoff n d) ξ, hm⟩) ∧
        (∀ π : Design n d, DesignClass n d π →
          ENNReal.ofReal (cLower s * aScale n d s) ≤ priorRisk π s) ∧
        publishedCapacity n d (frozenUniformClass d s) = capacity n d s ∧
        publishedWorst (piStar n d) (frozenUniformClass d s) = worstLoss (piStar n d) s ∧
        gaussianCapacity n d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s = capacity n d s ∧
        gaussianWorst (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) (piStar n d) s =
          worstLoss (piStar n d) s ∧
        gaussianLawClass d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s ⊂
          frozenUniformClass d s ∧
        (∀ lower upper : ℝ, 0 < lower → lower ≤ 1 → 1 ≤ upper →
          capacity n d s ≤ publishedCapacity n d (boundedDensityClass d s lower upper)) ∧
        (∀ π : Design n d, DesignClass n d π → ∀ m : CenteredL2Fn d,
          SobolevClass d s m →
          (n : ℝ) * variance (fun ω => htEstimator ω.1.2 ω.2)
            (experimentLaw (covLaw n d)
              (gaussianCompletion (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) m) π.val) -
              4.01 = (loss π m.val).toReal ∧ loss π m.val < ⊤) ∧
        (∀ ε : ℝ, 0 < ε →
          (pairCount d : ℝ) * max 1 ((3072 / (4.01 * ε)) ^ (1 / s)) ≤ n →
          gaussianWorst (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) (piStar n d) s ≤
            ENNReal.ofReal (4.01 * ε)) ∧
        (∀ ε : ℝ, 0 < ε → ε < cLower s / 4.01 →
          gaussianCapacity n d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s ≤
            ENNReal.ofReal (4.01 * ε) →
          (pairCount d : ℝ) * ((cLower s / (4.01 * ε)) ^ (1 / s)) ≤ n)) ∧
    (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ ds : ℕ → ℕ, (∀ n, 2 ≤ ds n) →
      (Tendsto (fun n => capacity n (ds n) s) atTop (𝓝 0) ↔
        Tendsto (fun n => (pairCount (ds n) : ℝ) / n) atTop (𝓝 0)) ∧
      (Tendsto (fun n => (pairCount (ds n) : ℝ) / n) atTop (𝓝 0) ↔
        Asymptotics.IsLittleO atTop (fun n => (ds n : ℝ)) (fun n => Real.sqrt (n : ℝ)))) ∧
    (∀ s lower upper : ℝ, 0 < s → s ≤ 1 → 0 < lower → lower ≤ 1 → 1 ≤ upper →
      ∀ ds : ℕ → ℕ, (∀ n, 2 ≤ ds n) →
      Tendsto (fun n => publishedCapacity n (ds n)
        (boundedDensityClass (ds n) s lower upper)) atTop (𝓝 0) →
      Asymptotics.IsLittleO atTop (fun n => (ds n : ℝ)) (fun n => Real.sqrt (n : ℝ))) :=
  by
    have hpub := published_prognostic_capacity hExcess_of_gate hContraction_of_gate
    have hlow := full_design_lower hContraction_of_gate
    have hmiddle (n d : ℕ) (hπ : DesignClass n d (piStar n d)) (s : ℝ) :
        capacity n d s ≤ worstLoss (piStar n d) s := by
      unfold capacity Causalean.Stat.minimaxValueENNReal
      exact iInf_le (fun π : {π : Design n d // DesignClass n d π} =>
        worstLoss π.val s) ⟨piStar n d, hπ⟩
    refine ⟨?_, ?_, ?_⟩
    · intro n d hn hd
      have hu := spectral_design_upper n d hn hd
      refine ⟨hu.1, ?_, ?_, ?_, ?_⟩
      · intro h; simp only [piStar, if_pos h]
      · intro h; simp only [piStar, if_neg (not_le.mpr h)]
      · intro seed hseed x i
        have ht := (ordered_prefix_rounding n
          (fun h i => features d h (shiftedSample x seed.1 seed.2.1 i))
          (Real.sqrt 2) (fun h i _ => features_abs_le d h _)).2.1 seed.2.2 hseed i
        have hp : rowPrefix (fun h i => features d h (shiftedSample x seed.1 seed.2.1 i)) =
            spectralRows (shiftedSample x seed.1 seed.2.1) := by
          funext h i
          rfl
        rw [hp] at ht
        exact ht
      · intro s hs hs1
        have hc := cLower_uniform_positive s hs1
        have hl := (hlow s hs hs1).2 n d hn hd
        have hupper := hu.2 s hs hs1
        have hgcap := gaussianCapacity_eq_capacity hContraction_of_gate n d hn hd s
        have hgw := gaussianWorst_eq_worstLoss hContraction_of_gate n d hn hd
          (piStar n d) hu.1 s
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hnonneg : 0 ≤ aScale n d s := by unfold aScale; positivity
        have hscale : aScale n d s = bScale n d s := rfl
        refine ⟨hscale, ?_, ?_, hc.1, hc.2, ?_,
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc.2 hnonneg),
          hl.2, hmiddle n d hu.1 s, hupper,
          cosinePrior_legal_and_isotropic.1 d (priorCutoff n d) hd (le_max_left _ _) s hs hs1,
          hl.1, hpub.2.2.2.1 n d hn hd s hs hs1,
          (hpub.2.2.1 n d hn hd s hs hs1 (piStar n d) hu.1).2,
          hgcap, hgw, (hpub.1 d hd s hs hs1).2.1, ?_, ?_, ?_, ?_⟩
        · intro h
          have hr : 1 ≤ (pairCount d : ℝ) / n :=
            (le_div_iff₀ hn0).2 (by
              simpa only [one_mul] using
                (show (n : ℝ) ≤ pairCount d by exact_mod_cast h.le))
          exact min_eq_left (Real.one_le_rpow hr hs.le)
        · intro h
          have hr : (pairCount d : ℝ) / n ≤ 1 :=
            (div_le_iff₀ hn0).2 (by
              simpa only [one_mul] using
                (show (pairCount d : ℝ) ≤ n by exact_mod_cast h))
          exact min_eq_right (Real.rpow_le_one (by positivity) hr hs.le)
        · have hpow : 1 ≤ (16384 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
          have hden : 48 ≤ (48 + 32 * Real.pi ^ 2) * (16384 : ℝ) ^ s := by
            nlinarith [sq_nonneg Real.pi]
          have hc' : cLower s ≤ 2 / 48 := by
            exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
          dsimp only [CUpper]
          linarith
        · intro lower upper hlower hl1 hu1
          exact (hpub.2.2.2.2 s lower upper hs hs1 hlower hl1 hu1).2.1 n d hn hd |>.2
        · intro π hπ m hm
          have ht := ht_transfer hContraction_of_gate n d hn hd s hs hs1 m hm π
            hπ.fair hπ.outcomeIndep
          exact ⟨by simpa only [ht.2.2.1] using ht.2.2.2.2, ht.2.2.2.1⟩
        · intro ε hε hsize
          rw [hgw]
          exact hupper.trans (ENNReal.ofReal_le_ofReal
            (scale_sample_size_sufficient n d hn hd s ε hs hε hsize))
        · intro ε hε hsmall hcap
          rw [hgcap] at hcap
          have hb := hl.2.trans hcap
          have hbR : cLower s * aScale n d s ≤ 4.01 * ε :=
            (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
          exact scale_sample_size_necessary n d hn hd s ε hs hε hsmall hbR
    · intro s hs hs1 ds hd
      have hscale := scale_vanishing s hs hs1 ds hd
      refine ⟨?_, hscale.2⟩
      constructor
      · intro hv
        have hnecess := dimension_necessity_of_scale_lower s hs hs1 ds hd
          (fun n => capacity n (ds n) s) ?_ hv
        · exact hscale.2.mpr hnecess
        · filter_upwards [eventually_ge_atTop 2] with n hn
          exact ((hlow s hs hs1).2 n (ds n) hn (hd n)).2
      · intro hv
        have ha := hscale.1.mpr hv
        have hupper : Tendsto (fun n => ENNReal.ofReal (CUpper * aScale n (ds n) s))
            atTop (𝓝 0) := by
          simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
            (ENNReal.continuous_ofReal.tendsto 0).comp
              (show Tendsto (fun n => CUpper * aScale n (ds n) s) atTop (𝓝 0) by
                simpa only [mul_zero] using ha.const_mul CUpper)
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds hupper (Filter.Eventually.of_forall (fun _ => bot_le))
        filter_upwards [eventually_ge_atTop 2] with n hn
        have hu := spectral_design_upper n (ds n) hn (hd n)
        exact (hmiddle n (ds n) hu.1 s).trans (hu.2 s hs hs1)
    · intro s lower upper hs hs1 hl hl1 hu1 ds hd hv
      exact (hpub.2.2.2.2 s lower upper hs hs1 hl hl1 hu1).2.2 ds hd hv

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
