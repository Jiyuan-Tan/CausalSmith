module
public import Causalean.Stat.CLT.AsymptoticLinearity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotCDFIdentity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalRiskAttainment
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRowUniformization
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotWeakLimitSupport

/-! # Transfer of conditional pilot-row Gaussian limits

This module transfers an explicit conditional Gaussian CDF limit for every
convergent sequence of genuine pilot selectors to the unconditional CDF of the
actual private-pilot transcript.  It contains no triangular-array CLT: that
analytic input remains a premise of the main theorem.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter MeasureTheory ProbabilityTheory Causalean.Stat
open scoped Topology BigOperators ENNReal

/-- The shrinking localization radius used to average conditional row limits. It goes to zero slowly enough that the pilot Chebyshev bound still vanishes. For the displayed inputs and conditions, the stated result follows. [The pilot Gaussian Radius](goal) is determined by [the displayed parameters](hyp:θ,h,m,n). -/
def pilotGaussianRadius (θ h : TrialParameter) (m : ℕ → ℕ) (n : ℕ) : ℝ :=
  2 * max
    (Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹))
    (Real.sqrt (dist (localAlternative θ h n) θ))

/-- The pilot-size component of `pilotGaussianRadius` tends to zero. For [the displayed inputs and conditions](hyp:m), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:hdiv), these specify the stated inputs. -/
lemma pilotGaussianBaseRadius_tendsto_zero (m : ℕ → ℕ)
    (hdiv : PilotDiverges m) :
    Tendsto (fun n => Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹))
      atTop (nhds 0) := by
  have hm : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdiv
  have hsqrt : Tendsto (fun n => Real.sqrt (m n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hm
  have hinv : Tendsto (fun n => (Real.sqrt (m n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  simpa using hinv.sqrt

/-- The localization radius tends to zero. For [the displayed inputs and conditions](hyp:h), [the stated result](goal) follows. For [the displayed quantities and conditions](hyp:m,hdiv), these specify the stated inputs. -/
lemma pilotGaussianRadius_tendsto_zero (θ h : TrialParameter)
    (m : ℕ → ℕ) (hdiv : PilotDiverges m) :
    Tendsto (pilotGaussianRadius θ h m) atTop (nhds 0) := by
  have hbase := pilotGaussianBaseRadius_tendsto_zero m hdiv
  have hdist : Tendsto (fun n => dist (localAlternative θ h n) θ)
      atTop (nhds 0) := by
    simpa using (localAlternative_tendsto θ h).dist
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => θ) atTop (nhds θ))
  have hshift : Tendsto (fun n => Real.sqrt
      (dist (localAlternative θ h n) θ)) atTop (nhds 0) := by
    simpa using hdist.sqrt
  change Tendsto (fun n => 2 * max
    (Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹))
    (Real.sqrt (dist (localAlternative θ h n) θ))) atTop (nhds 0)
  convert ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).mul
    (hbase.max hshift)) using 1 <;> norm_num

/-- Convergence along every selected subsequence gives uniform control over raw released prefixes in the shrinking Gaussian-transfer neighborhood. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hρ,hseq,hlt), [the pilot Prefix CDF uniform of subsequential tendsto](goal).

Under the stated assumptions, the pilot Prefix CDF uniform of subsequential tendsto. -/
lemma pilotPrefixCDF_uniform_of_subsequential_tendsto
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ) (ρ : ℕ → ℝ)
    (E : (n : ℕ) → (Fin (m n) → Fin 4) → ℝ) (L : ℝ)
    (hρ : Tendsto ρ atTop (nhds 0))
    (hseq : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (hφlarge : ∀ k, m (φ k) < φ k)
        (u : (k : ℕ) → Fin (m (φ k)) → Fin 4),
        Tendsto (fun k => pilotAdaptivePrefixTheta p ε m
            (Nat.le_of_lt (hφlarge k)) (u k))
          atTop (nhds θ) →
        Tendsto (fun k => E (φ k) (u k)) atTop (nhds L))
    (hlt : ∀ᶠ n in atTop, m n < n) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ (hmn : m n ≤ n) (u : Fin (m n) → Fin 4),
        dist (pilotAdaptivePrefixTheta p ε m hmn u) θ ≤ ρ n →
          |E n u - L| < δ := by
  intro δ hδ
  by_contra huniform
  have hfrequent : ∃ᶠ n in atTop,
      ¬(∀ (hmn : m n ≤ n) (u : Fin (m n) → Fin 4),
        dist (pilotAdaptivePrefixTheta p ε m hmn u) θ ≤ ρ n →
          |E n u - L| < δ) := not_eventually.mp huniform
  have hbad : ∃ᶠ n in atTop, ∃ hmn : m n < n,
      ∃ (u : Fin (m n) → Fin 4),
        dist (pilotAdaptivePrefixTheta p ε m
          (Nat.le_of_lt hmn) u) θ ≤ ρ n ∧
        δ ≤ |E n u - L| := by
    apply (hfrequent.and_eventually hlt).mono
    intro n hpair
    rcases hpair with ⟨hn, hmn⟩
    push Not at hn
    obtain ⟨hmn', u, hu, hE⟩ := hn
    refine ⟨hmn, u, ?_, hE⟩
    simpa only [Subsingleton.elim hmn' (Nat.le_of_lt hmn)] using hu
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad
  choose u hu using fun k => (hφbad k).2
  have hselector : Tendsto
      (fun k => pilotAdaptivePrefixTheta p ε m
        (Nat.le_of_lt (hφbad k).1) (u k)) atTop (nhds θ) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    have hρsub : Tendsto (fun k => ρ (φ k)) atTop (nhds 0) :=
      hρ.comp hφ.tendsto_atTop
    have hρlt : ∀ᶠ k in atTop, ρ (φ k) < η :=
      (tendsto_order.1 hρsub).2 η hη
    rcases eventually_atTop.1 hρlt with ⟨N, hN⟩
    exact ⟨N, fun k hk => lt_of_le_of_lt (hu k).1 (hN k hk)⟩
  have hE := hseq φ hφ (fun k => (hφbad k).1) u hselector
  have hclose : ∀ᶠ k in atTop, |E (φ k) (u k) - L| < δ := by
    exact eventually_atTop.2 (Metric.tendsto_atTop.1 hE δ hδ)
  rcases eventually_atTop.1 hclose with ⟨N, hN⟩
  exact (not_lt_of_ge (hu N).2 (hN N le_rfl)).elim

/-- The varying-radius Chebyshev envelope used in Gaussian transfer vanishes. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε,hdiv), [the pilot Gaussian Bad Envelope tendsto zero](goal).

Under the stated assumptions, the pilot Gaussian Bad Envelope tendsto zero. -/
lemma pilotGaussianBadEnvelope_tendsto_zero
    (p ε : ℝ) (m : ℕ → ℕ) (hp : InteriorAssignment p)
    (hε : 0 < ε) (hdiv : PilotDiverges m) :
    Tendsto (fun n => pilotBadMassEnvelope p ε
      (Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹)) m n) atTop (nhds 0) := by
  let c0 := controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)
  let c1 := p * (Real.exp ε - 1) / (Real.exp ε + 3)
  have hc0 : 0 < c0 := by
    dsimp [c0, controlProb]
    have hep : 1 < Real.exp ε := by
      simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
    have hcp : 0 < 1 - p := by linarith [hp.2]
    exact div_pos (mul_pos hcp (sub_pos.mpr hep)) (by positivity)
  have hc1 : 0 < c1 := by
    dsimp [c1]
    have hep : 1 < Real.exp ε := by
      simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
    exact div_pos (mul_pos hp.1 (sub_pos.mpr hep)) (by positivity)
  have hm : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdiv
  have hsqrt : Tendsto (fun n => Real.sqrt (m n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hm
  have hpos : ∀ᶠ n in atTop, 0 < (m n : ℝ) := hm.eventually_gt_atTop 0
  have hrewrite : ∀ᶠ n in atTop,
      pilotBadMassEnvelope p ε
          (Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹)) m n =
        1 / (Real.sqrt (m n : ℝ) * c0 ^ 2) +
          1 / (Real.sqrt (m n : ℝ) * c1 ^ 2) := by
    filter_upwards [hpos] with n hn
    have hs : 0 < Real.sqrt (m n : ℝ) := Real.sqrt_pos.2 hn
    have hsq : (Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹)) ^ 2 =
        (Real.sqrt (m n : ℝ))⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hs.le)
    have hcancel : (m n : ℝ) * (Real.sqrt (m n : ℝ))⁻¹ =
        Real.sqrt (m n : ℝ) := by
      nth_rewrite 1 [← Real.sq_sqrt hn.le]
      field_simp
    unfold pilotBadMassEnvelope
    have heq0 : Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹) * controlProb p *
        (Real.exp ε - 1) / (Real.exp ε + 3) =
        Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹) * c0 := by
      dsimp only [c0]
      ring
    have heq1 : Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹) * p *
        (Real.exp ε - 1) / (Real.exp ε + 3) =
        Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹) * c1 := by
      dsimp only [c1]
      ring
    rw [heq0, heq1]
    simp only [mul_pow, hsq, ← mul_assoc, hcancel]
  have h0 : Tendsto (fun n => 1 / (Real.sqrt (m n : ℝ) * c0 ^ 2))
      atTop (nhds 0) := by
    convert tendsto_inv_atTop_zero.comp
      (hsqrt.const_mul_atTop (sq_pos_of_pos hc0)) using 1 <;>
      simp [Function.comp_def, one_div, mul_comm]
  have h1 : Tendsto (fun n => 1 / (Real.sqrt (m n : ℝ) * c1 ^ 2))
      atTop (nhds 0) := by
    convert tendsto_inv_atTop_zero.comp
      (hsqrt.const_mul_atTop (sq_pos_of_pos hc1)) using 1 <;>
      simp [Function.comp_def, one_div, mul_comm]
  have ht : Tendsto (fun n =>
      1 / (Real.sqrt (m n : ℝ) * c0 ^ 2) +
      1 / (Real.sqrt (m n : ℝ) * c1 ^ 2)) atTop (nhds 0) := by
    convert h0.add h1 using 1 <;> norm_num
  exact ht.congr' (hrewrite.mono fun _ hn => hn.symm)

/-- An explicit conditional adaptive-row Gaussian CDF limit along every subsequence and every convergent genuine selector sequence implies the exact unconditional scaled-error CDF limit of the private-pilot transcript. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub,hrow), [the pilot scaled Error cdf tendsto of conditional Rows](goal).

Under the stated assumptions, the pilot scaled Error cdf tendsto of conditional Rows. -/
theorem pilot_scaledError_cdf_tendsto_of_conditionalRows
    (θ h : TrialParameter) (p ε x : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m)
    (hrow : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ η : ℕ → TrialParameter,
        (∀ k, InteriorMeans (η k)) → Tendsto η atTop (nhds θ) →
        Tendsto (fun k => adaptivePilotRowScaledCDF select θ h
          (fun _ => η k) p ε m hselect hp hε (φ k) x) atTop
          (nhds ((gaussianMeasure 0 (Vstar θ p ε)).real (Set.Iic x)))) :
    Tendsto (fun n =>
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε)
        (localAlternative θ h n) p n).real
        {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z ≤ x})
      atTop (nhds ((gaussianMeasure 0 (Vstar θ p ε)).real (Set.Iic x))) := by
  classical
  let L := (gaussianMeasure 0 (Vstar θ p ε)).real (Set.Iic x)
  let base : ℕ → ℝ := fun n => Real.sqrt ((Real.sqrt (m n : ℝ))⁻¹)
  let ρ := pilotGaussianRadius θ h m
  let E : (n : ℕ) → (Fin (m n) → Fin 4) → ℝ := fun n u =>
    if hn : 2 ≤ n then
      adaptivePilotRowScaledCDF select θ h
        (fun _ => pilotAdaptivePrefixTheta p ε m
          (Nat.le_of_lt (hsub.2 n hn).2) u)
        p ε m hselect hp hε n x else L
  have huniform : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ (hmn : m n ≤ n) (u : Fin (m n) → Fin 4),
        dist (pilotAdaptivePrefixTheta p ε m hmn u) θ ≤ ρ n →
          |E n u - L| < δ := by
    apply pilotPrefixCDF_uniform_of_subsequential_tendsto θ p ε m ρ E L
      (pilotGaussianRadius_tendsto_zero θ h m hdiv)
    · intro φ hφ hφlarge u hu
      let η : ℕ → TrialParameter := fun k => pilotAdaptivePrefixTheta p ε m
        (Nat.le_of_lt (hφlarge k)) (u k)
      have hηint : ∀ k, InteriorMeans (η k) := by
        intro k
        exact pilotTheta_interior p ε m
          (pilotAdaptiveEncode _ (u k) (fun _ => 0))
      have hev : ∀ᶠ k in atTop, 2 ≤ φ k :=
        hφ.tendsto_atTop.eventually_ge_atTop 2
      apply (hrow φ hφ η hηint hu).congr'
      filter_upwards [hev] with k hk
      simp only [E, dif_pos hk, η, Subsingleton.elim]
    · filter_upwards [eventually_ge_atTop 2] with n hn
      exact (hsub.2 n hn).2
  have htarget0 : 0 ≤ L := measureReal_nonneg
  have htarget1 : L ≤ 1 := by
    letI : IsProbabilityMeasure (gaussianMeasure 0 (Vstar θ p ε)) := by
      infer_instance
    exact measureReal_le_one
  let rowParam : ℕ → TrialParameter := fun n =>
    if InteriorMeans (localAlternative θ h n) then localAlternative θ h n else θ
  have hrowParamInterior (n : ℕ) : InteriorMeans (rowParam n) := by
    dsimp only [rowParam]
    split_ifs with hn
    · exact hn
    · exact hθ
  let w : (n : ℕ) → (Fin (m n) → Fin 4) → ℝ := fun n =>
    pilotPrefixWeight (rowParam n) p ε m n
  have havg : Tendsto (fun n => ∑ u, w n u * E n u) atTop (nhds L) := by
    apply finitePilot_conditionalCDF_tendsto w E L
    · intro n u
      exact pilotPrefixWeight_nonneg (rowParam n) p ε m n hp
        (hrowParamInterior n) u
    · intro n
      exact pilotPrefixWeight_sum (rowParam n) p ε m n
    · intro n u
      by_cases hn : 2 ≤ n
      · simp only [E, dif_pos hn]
        let η : ℕ → TrialParameter := fun _ => pilotAdaptivePrefixTheta p ε m
          (Nat.le_of_lt (hsub.2 n hn).2) u
        have hηint : ∀ k, InteriorMeans (η k) := fun _ =>
          pilotTheta_interior p ε m
            (pilotAdaptiveEncode _ u (fun _ => 0))
        unfold adaptivePilotRowScaledCDF
        apply Finset.sum_nonneg
        intro v _
        apply mul_nonneg
        · simpa only [η, Subsingleton.elim] using
            adaptivePilotRowProductMass_nonneg select θ h η p ε m hselect hp hθ
              hηint hε n v
        · split_ifs <;> positivity
      · simp only [E, dif_neg hn]
        exact htarget0
    · intro n u
      by_cases hn : 2 ≤ n
      · simp only [E, dif_pos hn]
        let η : ℕ → TrialParameter := fun _ => pilotAdaptivePrefixTheta p ε m
          (Nat.le_of_lt (hsub.2 n hn).2) u
        have hηint : ∀ k, InteriorMeans (η k) := fun _ =>
          pilotTheta_interior p ε m
            (pilotAdaptiveEncode _ u (fun _ => 0))
        unfold adaptivePilotRowScaledCDF
        calc
          _ ≤ ∑ v, adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v := by
            apply Finset.sum_le_sum
            intro v _
            have hm0 := adaptivePilotRowProductMass_nonneg select θ h η p ε m hselect hp hθ
              hηint hε n v
            split_ifs
            · simpa only [mul_one, η] using
                (le_refl (adaptivePilotRowProductMass select θ h η p ε m hselect hp hε n v))
            · simpa only [mul_zero] using hm0
          _ = 1 := adaptivePilotRowProductMass_sum select θ h η p ε m hselect hp
            hηint hε n
      · simp only [E, dif_neg hn]
        exact htarget1
    · exact htarget0
    · exact htarget1
    · intro δ hδ
      have hu := huniform δ hδ
      have hbase0 : Tendsto base atTop (nhds 0) :=
        pilotGaussianBaseRadius_tendsto_zero m hdiv
      have hbasepos : ∀ᶠ n in atTop, 0 < base n := by
        have hmpos : ∀ᶠ n in atTop, 0 < (m n : ℝ) :=
          (tendsto_natCast_atTop_atTop.comp hdiv).eventually_gt_atTop 0
        filter_upwards [hmpos] with n hn
        exact Real.sqrt_pos.2 (inv_pos.mpr (Real.sqrt_pos.2 hn))
      have hdist0 : Tendsto (fun n => dist (localAlternative θ h n) θ)
          atTop (nhds 0) := by
        simpa using (localAlternative_tendsto θ h).dist
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => θ) atTop (nhds θ))
      have hdistle : ∀ᶠ n in atTop,
          dist (localAlternative θ h n) θ ≤
            Real.sqrt (dist (localAlternative θ h n) θ) := by
        have hdlt : ∀ᶠ n in atTop,
            dist (localAlternative θ h n) θ < 1 :=
          (tendsto_order.1 hdist0).2 1 zero_lt_one
        filter_upwards [hdlt] with n hn
        let d := dist (localAlternative θ h n) θ
        have hd0 : 0 ≤ d := dist_nonneg
        have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
        have hs2 : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd0
        have hd1 : d ≤ 1 := hn.le
        nlinarith [sq_nonneg (d - Real.sqrt d)]
      let M := adaptiveInteriorMargin θ
      have hM : 0 < M := adaptiveInteriorMargin_pos θ hθ
      have hbaseSmall : ∀ᶠ n in atTop, base n < M / 4 :=
        (tendsto_order.1 hbase0).2 _ (by positivity)
      have hregSmall := pilotRegularizer_eventually_lt m hdiv (M / 4) (by positivity)
      have hlocalClose : ∀ᶠ n in atTop,
          dist (localAlternative θ h n) θ < M / 4 :=
        (Metric.tendsto_atTop.1 (localAlternative_tendsto θ h) (M / 4)
          (by positivity)) |> eventually_atTop.2
      have hlocal := eventually_localAlternative_interior θ h hθ
      have hn2 : ∀ᶠ n in atTop, 2 ≤ n := eventually_ge_atTop 2
      have hprefixBad : Tendsto (fun n => if hn : 2 ≤ n then
          pilotPrefixBadMass (localAlternative θ h n) p ε (base n) m
            (Nat.le_of_lt (hsub.2 n hn).2) else 0) atTop (nhds 0) := by
        have henv := pilotGaussianBadEnvelope_tendsto_zero p ε m hp hε hdiv
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henv
        · filter_upwards [hn2, hlocal] with n hn hln
          rw [dif_pos hn]
          unfold pilotPrefixBadMass
          apply Finset.sum_nonneg
          intro u _
          exact mul_nonneg
            (pilotPrefixWeight_nonneg _ p ε m n hp hln u)
            (by split_ifs <;> positivity)
        · filter_upwards [hn2, hlocal, hbasepos, hbaseSmall, hregSmall,
            hlocalClose] with n hn hln hbpos hbsmall hreg hclose
          rw [dif_pos hn]
          let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
          have hmpos : 0 < m n := lt_of_lt_of_le Nat.zero_lt_one
            (hsub.2 n hn).1
          have hcoord : ∀ k : Fin 2,
              |localAlternative θ h n k - θ k| < M / 4 := by
            have hd := (dist_pi_lt_iff (by positivity : 0 < M / 4)).mp hclose
            intro k
            simpa only [Real.dist_eq] using hd k
          have hM0l : M ≤ θ 0 := (min_le_left _ _).trans (min_le_left _ _)
          have hM0r : M ≤ 1 - θ 0 :=
            (min_le_left _ _).trans (min_le_right _ _)
          have hM1l : M ≤ θ 1 := (min_le_right _ _).trans (min_le_left _ _)
          have hM1r : M ≤ 1 - θ 1 :=
            (min_le_right _ _).trans (min_le_right _ _)
          have hδ0l : (m n + 2 : ℝ)⁻¹ + base n ≤
              localAlternative θ h n 0 := by
            have hc := (abs_lt.mp (hcoord 0)).1
            dsimp only [M] at hM0l hreg hbsmall hc ⊢
            linarith
          have hδ0r : (m n + 2 : ℝ)⁻¹ + base n ≤
              1 - localAlternative θ h n 0 := by
            have hc := (abs_lt.mp (hcoord 0)).2
            dsimp only [M] at hM0r hreg hbsmall hc ⊢
            linarith
          have hδ1l : (m n + 2 : ℝ)⁻¹ + base n ≤
              localAlternative θ h n 1 := by
            have hc := (abs_lt.mp (hcoord 1)).1
            dsimp only [M] at hM1l hreg hbsmall hc ⊢
            linarith
          have hδ1r : (m n + 2 : ℝ)⁻¹ + base n ≤
              1 - localAlternative θ h n 1 := by
            have hc := (abs_lt.mp (hcoord 1)).2
            dsimp only [M] at hM1r hreg hbsmall hc ⊢
            linarith
          simpa only [pilotBadMassEnvelope, base, Subsingleton.elim] using
            pilotPrefixBadMass_le
            select (localAlternative θ h n) p ε (base n) m hselect hp hln hε hbpos
            hmn hmpos hδ0l hδ0r hδ1l hδ1r
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprefixBad
      · filter_upwards [] with n
        apply Finset.sum_nonneg
        intro u _
        exact mul_nonneg (pilotPrefixWeight_nonneg (rowParam n) p ε m n hp
          (hrowParamInterior n) u) (by split_ifs <;> positivity)
      · filter_upwards [hn2, hlocal, hu, hbasepos, hdistle] with
          n hn hln hunif hbpos hdle
        rw [dif_pos hn]
        apply Finset.sum_le_sum
        intro u _
        simp only [w, rowParam, if_pos hln]
        apply mul_le_mul_of_nonneg_left _
          (pilotPrefixWeight_nonneg (localAlternative θ h n) p ε m n hp hln u)
        by_cases hgood :
            |pilotAdaptivePrefixTheta p ε m
                (Nat.le_of_lt (hsub.2 n hn).2) u 0 -
                localAlternative θ h n 0| < base n ∧
              |pilotAdaptivePrefixTheta p ε m
                (Nat.le_of_lt (hsub.2 n hn).2) u 1 -
                localAlternative θ h n 1| < base n
        · have hnearRow : dist (pilotAdaptivePrefixTheta p ε m
              (Nat.le_of_lt (hsub.2 n hn).2) u)
              (localAlternative θ h n) < base n := by
            rw [dist_pi_lt_iff hbpos]
            intro k
            fin_cases k
            · rw [Real.dist_eq]
              change |pilotAdaptivePrefixTheta p ε m
                  (Nat.le_of_lt (hsub.2 n hn).2) u 0 -
                  localAlternative θ h n 0| < base n
              exact hgood.1
            · rw [Real.dist_eq]
              change |pilotAdaptivePrefixTheta p ε m
                  (Nat.le_of_lt (hsub.2 n hn).2) u 1 -
                  localAlternative θ h n 1| < base n
              exact hgood.2
          have hnear : dist (pilotAdaptivePrefixTheta p ε m
              (Nat.le_of_lt (hsub.2 n hn).2) u) θ ≤ ρ n := by
            calc
              _ ≤ dist (pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u)
                    (localAlternative θ h n) +
                  dist (localAlternative θ h n) θ := dist_triangle _ _ _
              _ ≤ max (base n) (Real.sqrt
                    (dist (localAlternative θ h n) θ)) +
                  max (base n) (Real.sqrt
                    (dist (localAlternative θ h n) θ)) := by
                gcongr
                · exact hnearRow.le.trans (le_max_left _ _)
                · exact hdle.trans (le_max_right _ _)
              _ = ρ n := by simp [ρ, pilotGaussianRadius, base]; ring
          have hnotbad : ¬ δ ≤ |E n u - L| :=
            not_le_of_gt (hunif (Nat.le_of_lt (hsub.2 n hn).2) u hnear)
          have hnotprefix : ¬(base n ≤
                |pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u 0 -
                    localAlternative θ h n 0| ∨
              base n ≤ |pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u 1 -
                    localAlternative θ h n 1|) := by
            push Not
            exact hgood
          simp [hnotbad, hnotprefix]
        · have hbadprefix : base n ≤
                |pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u 0 -
                    localAlternative θ h n 0| ∨
              base n ≤ |pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u 1 -
                    localAlternative θ h n 1| := by
            by_cases h0 : base n ≤
                |pilotAdaptivePrefixTheta p ε m
                    (Nat.le_of_lt (hsub.2 n hn).2) u 0 -
                    localAlternative θ h n 0|
            · exact Or.inl h0
            · right
              by_contra h1
              apply hgood
              exact ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩
          rw [if_pos hbadprefix]
          split_ifs <;> norm_num
  have hprefix : Tendsto (fun n => if hn : 2 ≤ n then
      pilotPrefixScaledErrorCDF select θ h p ε m hselect hp hε
        (Nat.le_of_lt (hsub.2 n hn).2) x else 0) atTop (nhds L) := by
    apply havg.congr'
    filter_upwards [eventually_ge_atTop 2,
      eventually_localAlternative_interior θ h hθ] with n hn hlocal
    rw [dif_pos hn]
    simp only [w, rowParam, if_pos hlocal, E, dif_pos hn,
      pilotPrefixScaledErrorCDF]
  apply hprefix.congr'
  filter_upwards [eventually_ge_atTop 2,
    eventually_localAlternative_interior θ h hθ] with n hn hlocal
  rw [dif_pos hn]
  exact (transcriptLaw_real_scaledError_le_eq_pilotPrefixScaledErrorCDF
    select θ h p ε x m hselect hp hε hsub hn hlocal).symm

/-- A conditional adaptive-row Gaussian CDF limit for every local direction and threshold transfers to the corresponding family of actual transcript CDF limits. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub,hrow), [the pilot scaled Error cdf tendsto of all conditional Rows](goal).

Under the stated assumptions, the pilot scaled Error cdf tendsto of all conditional Rows. -/
theorem pilot_scaledError_cdf_tendsto_of_all_conditionalRows
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m)
    (hrow : ∀ (h : TrialParameter) (x : ℝ) (φ : ℕ → ℕ), StrictMono φ →
      ∀ η : ℕ → TrialParameter,
        (∀ k, InteriorMeans (η k)) → Tendsto η atTop (nhds θ) →
        Tendsto (fun k => adaptivePilotRowScaledCDF select θ h
          (fun _ => η k) p ε m hselect hp hε (φ k) x) atTop
          (nhds ((gaussianMeasure 0 (Vstar θ p ε)).real (Set.Iic x)))) :
    ∀ h : TrialParameter, ∀ x : ℝ,
      Tendsto (fun n =>
        (transcriptLaw (pilotEstimator p ε m select hselect hp hε)
          (localAlternative θ h n) p n).real
          {z | scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z ≤ x})
        atTop (nhds ((gaussianMeasure 0 (Vstar θ p ε)).real (Set.Iic x))) := by
  intro h x
  exact pilot_scaledError_cdf_tendsto_of_conditionalRows select θ h p ε x m hselect hp hθ hε
    hdiv hsub (hrow h x)

end CausalSmith.Stat.LdpAteEfficiencySurface
