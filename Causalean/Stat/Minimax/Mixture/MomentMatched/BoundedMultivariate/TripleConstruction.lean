module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate.Triple

/-!
# Constructing bounded triple priors

This module turns scalar inverse-and-ordinary-moment certificates into bounded
three-coordinate prior pairs.  It proves the full degree-`3K` mixed-moment
identity, common mean arrival mass, and the quantitative target separation.
-/

public section

open MeasureTheory

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/-- A [positive matching degree](hyp:hK), [scalar and triple parameters](hyp:a,q,gap,b,ε), [a positive scalar scale](hyp:ha₀), [the overlap parametrization](hyp:hq), [an overlap margin between zero and one half](hyp:hε₀,hε₁), [a positive arrival-mass scale](hyp:hb), and [scalar moment priors](hyp:S) produce [bounded triple priors with the stated explicit branches and common mean arrival mass](goal). -/
theorem scalarPriors_to_triple {K : ℕ} (hK : 1 ≤ K)
    {a q gap b ε : ℝ} (ha₀ : 0 < a)
    (hq : q = 1 - 2 * ε) (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (hb : 0 < b) (S : ScalarPriors K a q gap) :
    ∃ T : TriplePriors K b ε (a * b * gap),
      T.ν₀ = triplePrior b a q S.ω₀ ∧
      T.ν₁ = triplePrior b a q S.ω₁ ∧
      (∫ t, t.1 ∂T.ν₀) = a * b := by
  have hq₀ : 0 ≤ q := by rw [hq]; linarith
  have hq₁ : q ≤ 1 := by rw [hq]; linarith
  have hpolyInt (ω : Measure ℝ) [IsProbabilityMeasure ω]
      (hs : ω (Set.Icc a 1) = 1) (n j : ℕ) :
      Integrable (fun x : ℝ => x ^ n * (x + q * a) ^ j) ω := by
    have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 :=
      ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).2 hs)
    have hc : ContinuousOn (fun x : ℝ => x ^ n * (x + q * a) ^ j)
        (Set.Icc a 1) := by fun_prop
    have hi := hc.integrableOn_compact isCompact_Icc (μ := ω)
    have hu : (Set.univ : Set ℝ) =ᵐ[ω] Set.Icc a 1 := by
      filter_upwards [hae] with x hx
      exact propext (iff_of_true trivial hx)
    simpa using hi.congr_set_ae hu
  have hinvInt (ω : Measure ℝ) [IsProbabilityMeasure ω]
      (hs : ω (Set.Icc a 1) = 1) (j : ℕ) :
      Integrable (fun x : ℝ => x⁻¹ * (x + q * a) ^ j) ω := by
    have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 :=
      ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).2 hs)
    have hc : ContinuousOn (fun x : ℝ => x⁻¹ * (x + q * a) ^ j)
        (Set.Icc a 1) := by
      apply ContinuousOn.mul
      · apply continuousOn_id.inv₀
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le ha₀ hx.1)
      · fun_prop
    have hi := hc.integrableOn_compact isCompact_Icc (μ := ω)
    have hu : (Set.univ : Set ℝ) =ᵐ[ω] Set.Icc a 1 := by
      filter_upwards [hae] with x hx
      exact propext (iff_of_true trivial hx)
    simpa using hi.congr_set_ae hu
  have hpoly : ∀ n j : ℕ, n + j ≤ 3 * K →
      (∫ x, x ^ n * (x + q * a) ^ j ∂S.ω₀) =
        ∫ x, x ^ n * (x + q * a) ^ j ∂S.ω₁ := by
    intro n j
    induction j generalizing n with
    | zero =>
        intro hn
        simpa using S.ordinary_match n (by simpa using hn)
    | succ j ih =>
        intro hn
        letI := S.probability₀
        letI := S.probability₁
        have h₁ := ih (n + 1) (by omega)
        have h₂ := ih n (by omega)
        have hpoint (x : ℝ) : x ^ n * (x + q * a) ^ (j + 1) =
            x ^ (n + 1) * (x + q * a) ^ j +
              q * a * (x ^ n * (x + q * a) ^ j) := by
          rw [pow_succ, pow_succ]
          ring
        have hsplit (ω : Measure ℝ) [IsProbabilityMeasure ω]
            (hs : ω (Set.Icc a 1) = 1) :
            (∫ x, x ^ n * (x + q * a) ^ (j + 1) ∂ω) =
              (∫ x, x ^ (n + 1) * (x + q * a) ^ j ∂ω) +
                q * a * (∫ x, x ^ n * (x + q * a) ^ j ∂ω) := by
          simp_rw [hpoint]
          rw [integral_add (hpolyInt ω hs (n + 1) j)
            ((hpolyInt ω hs n j).const_mul (q * a)), integral_const_mul]
        rw [hsplit S.ω₀ S.supported₀, hsplit S.ω₁ S.supported₁, h₁, h₂]
  have hinv : ∀ j : ℕ, j ≤ 3 * K →
      (∫ x, x⁻¹ * (x + q * a) ^ j ∂S.ω₀) =
        ∫ x, x⁻¹ * (x + q * a) ^ j ∂S.ω₁ := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using S.inverse_match
    | succ j ih =>
        intro hj
        letI := S.probability₀
        letI := S.probability₁
        have h₁ := hpoly 0 j (by omega)
        have h₂ := ih (by omega)
        have hpoint (x : ℝ) (hx : x ∈ Set.Icc a 1) :
            x⁻¹ * (x + q * a) ^ (j + 1) =
              (x + q * a) ^ j + q * a * (x⁻¹ * (x + q * a) ^ j) := by
          have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha₀ hx.1)
          rw [pow_succ]
          field_simp
        have hsplit (ω : Measure ℝ) [IsProbabilityMeasure ω]
            (hs : ω (Set.Icc a 1) = 1) :
            (∫ x, x⁻¹ * (x + q * a) ^ (j + 1) ∂ω) =
              (∫ x, (x + q * a) ^ j ∂ω) +
                q * a * (∫ x, x⁻¹ * (x + q * a) ^ j ∂ω) := by
          have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 :=
            ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).2 hs)
          calc
            _ = ∫ x, (x + q * a) ^ j +
                q * a * (x⁻¹ * (x + q * a) ^ j) ∂ω :=
                integral_congr_ae (hae.mono fun x hx => hpoint x hx)
            _ = _ := by
              rw [integral_add (by simpa using hpolyInt ω hs 0 j)
                ((hinvInt ω hs j).const_mul (q * a)), integral_const_mul]
        rw [hsplit S.ω₀ S.supported₀, hsplit S.ω₁ S.supported₁]
        simpa using congrArg₂ (fun u v : ℝ => u + q * a * v) h₁ h₂
  have hmixed (i j k : ℕ) (hdeg : i + j + k ≤ 3 * K) :
      (∫ t, mixedMonomial i j k t ∂triplePrior b a q S.ω₀) =
        ∫ t, mixedMonomial i j k t ∂triplePrior b a q S.ω₁ := by
    letI := S.probability₀
    letI := S.probability₁
    by_cases hz : i + j + k = 0
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      have hk : k = 0 := by omega
      subst i; subst j; subst k
      have hp₀ := (reweightedScalar_probability_finite_supported ha₀ S.ω₀
        S.finite₀ S.supported₀).1
      have hp₁ := (reweightedScalar_probability_finite_supported ha₀ S.ω₁
        S.finite₁ S.supported₁).1
      have hmap : Measurable (scalarToTriple b a q) := by
        unfold scalarToTriple
        apply Measurable.ite (measurableSet_singleton 0)
        · fun_prop
        · fun_prop
      haveI : IsProbabilityMeasure (triplePrior b a q S.ω₀) := by
        exact (Measure.isProbabilityMeasure_map_iff hmap.aemeasurable).2 hp₀
      haveI : IsProbabilityMeasure (triplePrior b a q S.ω₁) := by
        exact (Measure.isProbabilityMeasure_map_iff hmap.aemeasurable).2 hp₁
      simp [mixedMonomial]
    · have hpos : 0 < i + j + k := Nat.pos_of_ne_zero hz
      rw [integral_mixedMonomial_triplePrior ha₀ hq₀ S.ω₀ S.supported₀ i j k hpos,
        integral_mixedMonomial_triplePrior ha₀ hq₀ S.ω₁ S.supported₁ i j k hpos]
      by_cases hn : i + k = 0
      · have hi : i = 0 := by omega
        have hk : k = 0 := by omega
        subst i; subst k
        have hscalar (ω : Measure ℝ) [IsProbabilityMeasure ω]
            (hs : ω (Set.Icc a 1) = 1) :
            (∫ x, a * b ^ (0 + j + 0) / (2 : ℝ) ^ (j + 0) *
              x ^ (0 + 0) / x * (x + q * a) ^ j ∂ω) =
              a * b ^ j / (2 : ℝ) ^ j *
                (∫ x, x⁻¹ * (x + q * a) ^ j ∂ω) := by
          have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 :=
            ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).2 hs)
          calc
            _ = ∫ x, (a * b ^ j / (2 : ℝ) ^ j) *
                (x⁻¹ * (x + q * a) ^ j) ∂ω := by
                congr 1; funext x; simp [div_eq_mul_inv]; ring
            _ = _ := integral_const_mul ..
        rw [hscalar S.ω₀ S.supported₀, hscalar S.ω₁ S.supported₁,
          hinv j (by omega)]
      · have hnpos : 0 < i + k := Nat.pos_of_ne_zero hn
        let n := i + k - 1
        have hbound : n + j ≤ 3 * K := by dsimp [n]; omega
        have hscalar (ω : Measure ℝ) [IsProbabilityMeasure ω]
            (hs : ω (Set.Icc a 1) = 1) :
            (∫ x, a * b ^ (i + j + k) / (2 : ℝ) ^ (j + k) *
              x ^ (i + k) / x * (x + q * a) ^ j ∂ω) =
              (a * b ^ (i + j + k) / (2 : ℝ) ^ (j + k)) *
                (∫ x, x ^ n * (x + q * a) ^ j ∂ω) := by
          have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 :=
            ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).2 hs)
          calc
            _ = ∫ x, (a * b ^ (i + j + k) / (2 : ℝ) ^ (j + k)) *
                (x ^ n * (x + q * a) ^ j) ∂ω := by
              apply integral_congr_ae
              filter_upwards [hae] with x hx
              have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha₀ hx.1)
              have he : i + k = n + 1 := by dsimp [n]; omega
              have hpow : x ^ (i + k) / x = x ^ n := by
                rw [he, pow_succ]
                field_simp
              calc
                _ = (a * b ^ (i + j + k) / (2 : ℝ) ^ (j + k)) *
                    ((x ^ (i + k) / x) * (x + q * a) ^ j) := by ring
                _ = _ := by rw [hpow]
            _ = _ := integral_const_mul ..
        rw [hscalar S.ω₀ S.supported₀, hscalar S.ω₁ S.supported₁,
          hpoly n j hbound]
  have hmap : Measurable (scalarToTriple b a q) := by
    unfold scalarToTriple
    apply Measurable.ite (measurableSet_singleton 0)
    · fun_prop
    · fun_prop
  let A : Set MarkedParam := {t | 0 ≤ t.1 ∧ t.1 ≤ b ∧ ε ≤ t.2.1 ∧
    t.2.1 ≤ 1 - ε ∧ 0 ≤ t.2.2 ∧ t.2.2 ≤ 1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hpoint (x : ℝ) (hx : x ∈ ({0} ∪ Set.Icc a 1)) :
      scalarToTriple b a q x ∈ A := by
    rcases hx with hx | hx
    · have hx0 : x = 0 := hx
      subst x
      dsimp [A, scalarToTriple]
      simp
      constructor
      · exact le_of_lt hb
      constructor
      · linarith
      · linarith
    · have hxpos : 0 < x := lt_of_lt_of_le ha₀ hx.1
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hqa : 0 ≤ q * a := mul_nonneg hq₀ ha₀.le
      have hden : 0 < x + q * a := by positivity
      have hratio₀ : 0 ≤ q * a / x := div_nonneg hqa hxpos.le
      have hratio₁ : q * a / x ≤ q := by
        apply (div_le_iff₀ hxpos).2
        nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hx.1)]
      have hp₀ : 0 ≤ b * x := mul_nonneg hb.le hxpos.le
      have hp₁ : b * x ≤ b := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hx.2)]
      have hμ₀ : 0 ≤ x / (x + q * a) := div_nonneg hxpos.le hden.le
      have hμ₁ : x / (x + q * a) ≤ 1 := (div_le_one hden).2 (by linarith)
      dsimp [A, scalarToTriple]
      simp only [if_neg hxne, Set.mem_setOf_eq]
      refine ⟨hp₀, hp₁, ?_, ?_, hμ₀, hμ₁⟩
      · linarith
      · linarith
  have hcert (ω : Measure ℝ) [IsProbabilityMeasure ω]
      (hfin : ∃ s : Finset ℝ, ω (s : Set ℝ) = 1)
      (hs : ω (Set.Icc a 1) = 1) :
      IsProbabilityMeasure (triplePrior b a q ω) ∧
        (∃ s : Finset MarkedParam, (triplePrior b a q ω) (s : Set MarkedParam) = 1) ∧
        (triplePrior b a q ω) A = 1 := by
    obtain ⟨hp, hfin', hs'⟩ :=
      reweightedScalar_probability_finite_supported ha₀ ω hfin hs
    letI := hp
    have htp : IsProbabilityMeasure (triplePrior b a q ω) := by
      exact (Measure.isProbabilityMeasure_map_iff hmap.aemeasurable).2 hp
    letI := htp
    refine ⟨htp, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := hfin'
      refine ⟨s.image (scalarToTriple b a q), ?_⟩
      rw [triplePrior, Measure.map_apply hmap (Finset.measurableSet _)]
      apply le_antisymm prob_le_one
      calc
        1 = (reweightedScalar a ω) (s : Set ℝ) := hs.symm
        _ ≤ (reweightedScalar a ω)
            ((scalarToTriple b a q) ⁻¹' (s.image (scalarToTriple b a q) : Set MarkedParam)) :=
          measure_mono (by intro x hx; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · rw [triplePrior, Measure.map_apply hmap hA]
      apply le_antisymm prob_le_one
      calc
        1 = (reweightedScalar a ω) ({0} ∪ Set.Icc a 1) := hs'.symm
        _ ≤ (reweightedScalar a ω) ((scalarToTriple b a q) ⁻¹' A) :=
          measure_mono (by intro x hx; exact hpoint x hx)
  have hmean (ω : Measure ℝ) [IsProbabilityMeasure ω]
      (hs : ω (Set.Icc a 1) = 1) :
      (∫ t, t.1 ∂triplePrior b a q ω) = a * b := by
    have hmix := integral_mixedMonomial_triplePrior (b := b) ha₀ hq₀ ω hs 1 0 0
      (by norm_num)
    have hae : ∀ᵐ x ∂ω, x ∈ Set.Icc a 1 :=
      ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Icc).2 hs)
    have hrhs : (∫ x, a * b ^ (1 + 0 + 0) / (2 : ℝ) ^ (0 + 0) *
        x ^ (1 + 0) / x * (x + q * a) ^ 0 ∂ω) = a * b := by
      calc
        _ = ∫ _x, a * b ∂ω := by
          apply integral_congr_ae
          filter_upwards [hae] with x hx
          have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha₀ hx.1)
          simp only [add_zero, pow_one, pow_zero, div_one, mul_one]
          field_simp
        _ = a * b := by simp
    simpa [mixedMonomial] using hmix.trans hrhs
  letI := S.probability₀
  letI := S.probability₁
  obtain ⟨hp₀, hfin₀, hs₀⟩ := hcert S.ω₀ S.finite₀ S.supported₀
  obtain ⟨hp₁, hfin₁, hs₁⟩ := hcert S.ω₁ S.finite₁ S.supported₁
  have hmean₀ := hmean S.ω₀ S.supported₀
  have hmean₁ := hmean S.ω₁ S.supported₁
  have hgap : a * b * gap ≤
      |(∫ t, targetFunctional t ∂triplePrior b a q S.ω₀) -
        ∫ t, targetFunctional t ∂triplePrior b a q S.ω₁| := by
    rw [integral_targetFunctional_triplePrior ha₀ hq₀ S.ω₀ S.supported₀,
      integral_targetFunctional_triplePrior ha₀ hq₀ S.ω₁ S.supported₁]
    have hab : 0 ≤ a * b := le_of_lt (mul_pos ha₀ hb)
    calc
      a * b * gap ≤ a * b *
          |(∫ x, x / (x + q * a) ∂S.ω₀) -
            ∫ x, x / (x + q * a) ∂S.ω₁| :=
        mul_le_mul_of_nonneg_left S.target_gap hab
      _ = _ := by rw [← mul_sub, abs_mul, abs_of_nonneg hab]
  refine ⟨{
    positive_degree := hK
    ν₀ := triplePrior b a q S.ω₀
    ν₁ := triplePrior b a q S.ω₁
    probability₀ := hp₀
    probability₁ := hp₁
    finite₀ := hfin₀
    finite₁ := hfin₁
    supported₀ := by simpa only [A] using hs₀
    supported₁ := by simpa only [A] using hs₁
    mixed_match := hmixed
    mean_p_match := hmean₀.trans hmean₁.symm
    target_gap := hgap }, rfl, rfl, hmean₀⟩

/-- An [overlap margin strictly between 0 and 1/2](hyp:ε,hε₀,hε₁) ε and [positive arrival-mass bound](hyp:b,hb) b admit [constants 0 < c₀ < 1 and gap > 0, not depending on the degree, such that for every degree K ≥ 1 there is a bounded finitely supported triple-prior pair with arrival-mass bound b and overlap margin ε whose mixed moments agree through total degree 3K, whose first prior has mean arrival mass c₀·b/K² (shared by the second), and whose mean success masses differ in absolute value by at least c₀·b·gap/K²](goal). -/
theorem exists_triplePriors (ε b : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2)
    (hb : 0 < b) :
    ∃ c₀ gap : ℝ, 0 < c₀ ∧ c₀ < 1 ∧ 0 < gap ∧
      ∀ K : ℕ, 1 ≤ K →
        ∃ T : TriplePriors K b ε (endpointScale c₀ K * b * gap),
          (∫ t, t.1 ∂T.ν₀) = endpointScale c₀ K * b := by
  have hq₀ : 0 < 1 - 2 * ε := by linarith
  have hq₁ : 1 - 2 * ε ≤ 1 := by linarith
  obtain ⟨c₀, gap, hc₀, hc₁, hgap, hS⟩ :=
    exists_scalarPriors (1 - 2 * ε) hq₀ hq₁
  refine ⟨c₀, gap, hc₀, hc₁, hgap, ?_⟩
  intro K hK
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hKsq : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have ha₀ : 0 < endpointScale c₀ K := by
    unfold endpointScale
    positivity
  obtain ⟨S⟩ := hS K hK
  obtain ⟨T, _, _, hmean⟩ :=
    scalarPriors_to_triple hK ha₀ rfl hε₀ hε₁ hb S
  exact ⟨T, hmean⟩

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
