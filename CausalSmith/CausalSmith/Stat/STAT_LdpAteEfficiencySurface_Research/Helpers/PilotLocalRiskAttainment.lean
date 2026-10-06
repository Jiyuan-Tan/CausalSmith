module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalRiskConvergence

/-! # Exact local-risk attainment for the private-pilot estimator -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter
open scoped Topology ENNReal BigOperators

/-- The parameter-free Chebyshev envelope appearing in the bad-prefix bound. For the displayed inputs and conditions, the stated result follows. [The pilot Bad Mass Envelope](goal) is determined by [the displayed parameters](hyp:p,ε,r,m,n). -/
def pilotBadMassEnvelope (p ε r : ℝ) (m : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 / ((m n : ℝ) *
    (r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2) +
  1 / ((m n : ℝ) *
    (r * p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2)

/-- For every fixed positive localization radius, pilot divergence makes the uniform Chebyshev envelope vanish. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε,hr,hdiv), [the pilot Bad Mass Envelope tendsto zero](goal).

Under the stated assumptions, the pilot Bad Mass Envelope tendsto zero. -/
lemma pilotBadMassEnvelope_tendsto_zero
    (p ε r : ℝ) (m : ℕ → ℕ) (hp : InteriorAssignment p)
    (hε : 0 < ε) (hr : 0 < r) (hdiv : PilotDiverges m) :
    Tendsto (pilotBadMassEnvelope p ε r m) atTop (nhds 0) := by
  let a0 := r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)
  let a1 := r * p * (Real.exp ε - 1) / (Real.exp ε + 3)
  have hep : 1 < Real.exp ε := by
    simpa using (Real.exp_lt_exp.mpr hε : Real.exp 0 < Real.exp ε)
  have ha0 : 0 < a0 := by
    dsimp [a0, controlProb]
    have hcp : 0 < 1 - p := by linarith [hp.2]
    exact div_pos (mul_pos (mul_pos hr hcp) (sub_pos.mpr hep)) (by positivity)
  have ha1 : 0 < a1 := by
    dsimp [a1]
    exact div_pos (mul_pos (mul_pos hr hp.1) (sub_pos.mpr hep)) (by positivity)
  have hmreal : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdiv
  have hinv : Tendsto (fun n => ((m n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hmreal
  have h0 : Tendsto (fun n => 1 / ((m n : ℝ) * a0 ^ 2)) atTop (nhds 0) := by
    have ht := hinv.mul_const (a0 ^ 2)⁻¹
    convert ht using 1
    · funext n
      rw [one_div, mul_inv_rev]
      ring
    · simp
  have h1 : Tendsto (fun n => 1 / ((m n : ℝ) * a1 ^ 2)) atTop (nhds 0) := by
    have ht := hinv.mul_const (a1 ^ 2)⁻¹
    convert ht using 1
    · funext n
      rw [one_div, mul_inv_rev]
      ring
    · simp
  change Tendsto (fun n => 1 / ((m n : ℝ) * a0 ^ 2) +
    1 / ((m n : ℝ) * a1 ^ 2)) atTop (nhds 0)
  simpa using h0.add h1

/-- The clipping regularizer is eventually smaller than every fixed positive
margin when the pilot size diverges. For [the displayed inputs and conditions](hyp:m,hdiv,c,hc), [the stated result](goal) follows. -/
lemma pilotRegularizer_eventually_lt
    (m : ℕ → ℕ) (hdiv : PilotDiverges m) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n in atTop, (m n + 2 : ℝ)⁻¹ < c := by
  have hmreal : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdiv
  have hadd : Tendsto (fun n => (m n : ℝ) + 2) atTop atTop :=
    by
      rw [tendsto_atTop]
      intro b
      filter_upwards [hmreal.eventually_ge_atTop b] with n hn
      linarith
  have hinv : Tendsto (fun n => ((m n : ℝ) + 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hadd
  have hev := (tendsto_order.1 hinv).2 c hc
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hev

/-- For every bounded local direction, the genuine prefix-averaged selected variance converges uniformly to the oracle variance. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub), [the eventually uniform pilot Prefix Variance Average](goal).

Under the stated assumptions, the eventually uniform pilot Prefix Variance Average. -/
lemma eventually_uniform_pilotPrefixVarianceAverage
    (θ : TrialParameter) (p ε H : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ (hn : 2 ≤ n) (h : TrialParameter),
        Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H →
        InteriorMeans (localAlternative θ h n) →
        |pilotPrefixVarianceAverage select (localAlternative θ h n) p ε m
            (Nat.le_of_lt (hsub.2 n hn).2) hselect hp hε - Vstar θ p ε| < δ := by
  intro δ hδ
  obtain ⟨R, hR, hcont⟩ :=
    adaptiveScoreVariance_uniform_near_diag select θ p ε hselect hp hθ hε (δ / 2) (half_pos hδ)
  let M := adaptiveInteriorMargin θ
  have hM : 0 < M := adaptiveInteriorMargin_pos θ hθ
  let r := min (R / 3) (M / 8)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r ≤ R / 3 := min_le_left _ _
  have hrM : r ≤ M / 8 := min_le_right _ _
  let C := (pilotPhiUpper p ε) ^ 2 + |Vstar θ p ε|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hloc := eventually_localAlternative_dist_lt_uniform θ H r hr
  have hreg := pilotRegularizer_eventually_lt m hdiv (M / 4) (by positivity)
  have henv : ∀ᶠ n in atTop,
      pilotBadMassEnvelope p ε r m n < δ / (2 * (C + 1)) :=
    (tendsto_order.1 (pilotBadMassEnvelope_tendsto_zero
      p ε r m hp hε hr hdiv)).2 _ (by positivity)
  filter_upwards [hloc, hreg, henv] with n hnloc hnreg hnenv
  intro hn h hH hlocal
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  have hmpos : 0 < m n := lt_of_lt_of_le Nat.zero_lt_one (hsub.2 n hn).1
  have hd : ∀ k : Fin 2, dist (localAlternative θ h n k) (θ k) < r :=
    (dist_pi_lt_iff hr).mp (hnloc h hH)
  have hM0l : M ≤ θ 0 := (min_le_left _ _).trans (min_le_left _ _)
  have hM0r : M ≤ 1 - θ 0 := (min_le_left _ _).trans (min_le_right _ _)
  have hM1l : M ≤ θ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hM1r : M ≤ 1 - θ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hd0 := hd 0
  have hd1 := hd 1
  rw [Real.dist_eq] at hd0 hd1
  have hδ0l : (m n + 2 : ℝ)⁻¹ + r ≤ localAlternative θ h n 0 := by
    have := (abs_lt.mp hd0).1
    dsimp [M] at hM0l
    dsimp [M] at hnreg hrM
    linarith
  have hδ0r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - localAlternative θ h n 0 := by
    have := (abs_lt.mp hd0).2
    dsimp [M] at hM0r
    dsimp [M] at hnreg hrM
    linarith
  have hδ1l : (m n + 2 : ℝ)⁻¹ + r ≤ localAlternative θ h n 1 := by
    have := (abs_lt.mp hd1).1
    dsimp [M] at hM1l
    dsimp [M] at hnreg hrM
    linarith
  have hδ1r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - localAlternative θ h n 1 := by
    have := (abs_lt.mp hd1).2
    dsimp [M] at hM1r
    dsimp [M] at hnreg hrM
    linarith
  have hbad := pilotPrefixBadMass_le select (localAlternative θ h n) p ε r m
    hselect hp hlocal hε hr hmn hmpos hδ0l hδ0r hδ1l hδ1r
  have hbad' : pilotPrefixBadMass (localAlternative θ h n) p ε r m hmn ≤
      pilotBadMassEnvelope p ε r m n := by
    exact hbad
  have hgood (η : TrialParameter) (hη : InteriorMeans η)
      (hηclose : ∀ k : Fin 2, |η k - localAlternative θ h n k| < r) :
      |adaptiveScoreVariance select (localAlternative θ h n) η p ε -
        Vstar θ p ε| ≤ δ / 2 := by
    have hηrow : dist η (localAlternative θ h n) < r := by
      rw [dist_pi_lt_iff hr]
      intro k
      simpa only [Real.dist_eq] using hηclose k
    have hθrow : dist (localAlternative θ h n) θ < R :=
      lt_of_lt_of_le (hnloc h hH) (by linarith [hrR, hR])
    have hηθ : dist η θ < R := by
      calc
        dist η θ ≤ dist η (localAlternative θ h n) +
            dist (localAlternative θ h n) θ := dist_triangle _ _ _
        _ < r + r := add_lt_add hηrow (hnloc h hH)
        _ < R := by linarith [hrR, hR]
    exact (hcont _ _ hθrow hηθ).le
  have havg := pilotPrefixVarianceAverage_error_le select θ (localAlternative θ h n)
    p ε r (δ / 2) m hselect hp hθ hlocal hε (half_pos hδ).le hmn hgood
  have hCbad : C * pilotPrefixBadMass (localAlternative θ h n) p ε r m hmn <
      δ / 2 := by
    calc
      C * pilotPrefixBadMass (localAlternative θ h n) p ε r m hmn ≤
          C * pilotBadMassEnvelope p ε r m n :=
        mul_le_mul_of_nonneg_left hbad' hC
      _ ≤ (C + 1) * pilotBadMassEnvelope p ε r m n := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        unfold pilotBadMassEnvelope
        positivity
      _ < (C + 1) * (δ / (2 * (C + 1))) :=
        mul_lt_mul_of_pos_left hnenv (by linarith)
      _ = δ / 2 := by
        have hCp : 0 < C + 1 := by linarith
        field_simp [ne_of_gt hCp]
  dsimp only [C] at hCbad
  exact lt_of_le_of_lt havg (by linarith)

/-- Under the supplied quantities and conditions, the pilot prefix variance average bounds assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmn,hselect,hp,hθ,hε), [the pilot Prefix Variance Average bounds](goal).

Under the stated assumptions, the pilot Prefix Variance Average bounds. -/
lemma pilotPrefixVarianceAverage_bounds
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ) {n : ℕ}
    (hmn : m n ≤ n) (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    0 ≤ pilotPrefixVarianceAverage select θ p ε m hmn hselect hp hε ∧
      pilotPrefixVarianceAverage select θ p ε m hmn hselect hp hε ≤
        (pilotPhiUpper p ε) ^ 2 := by
  have hw (u : Fin (m n) → Fin 4) :
      0 ≤ pilotPrefixWeight θ p ε m n u :=
    pilotPrefixWeight_nonneg θ p ε m n hp hθ u
  have hη (u : Fin (m n) → Fin 4) :
      InteriorMeans (pilotAdaptivePrefixTheta p ε m hmn u) := by
    exact pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0))
  constructor
  · unfold pilotPrefixVarianceAverage
    exact Finset.sum_nonneg fun u _ => mul_nonneg (hw u)
      (adaptiveScoreVariance_nonneg select θ _ p ε hselect hp hθ (hη u) hε)
  · calc
      pilotPrefixVarianceAverage select θ p ε m hmn hselect hp hε ≤
          ∑ u : Fin (m n) → Fin 4,
            pilotPrefixWeight θ p ε m n u * (pilotPhiUpper p ε) ^ 2 := by
        unfold pilotPrefixVarianceAverage
        apply Finset.sum_le_sum
        intro u _
        exact mul_le_mul_of_nonneg_left
          (adaptiveScoreVariance_le select θ _ p ε hselect hp hθ (hη u) hε) (hw u)
      _ = (pilotPhiUpper p ε) ^ 2 := by
        rw [← Finset.sum_mul, pilotPrefixWeight_sum θ p ε m n, one_mul]

/-- The finite main-row correction preserves the uniform prefix-risk limit. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub), [the eventually uniform scaled Prefix Variance Average](goal).

Under the stated assumptions, the eventually uniform scaled Prefix Variance Average. -/
lemma eventually_uniform_scaledPrefixVarianceAverage
    (θ : TrialParameter) (p ε H : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ (hn : 2 ≤ n) (h : TrialParameter),
        Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H →
        InteriorMeans (localAlternative θ h n) →
        |(n : ℝ) / (adaptiveMainSize m n : ℝ) *
            pilotPrefixVarianceAverage select (localAlternative θ h n) p ε m
              (Nat.le_of_lt (hsub.2 n hn).2) hselect hp hε - Vstar θ p ε| < δ := by
  intro δ hδ
  let K := (pilotPhiUpper p ε) ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have havg := eventually_uniform_pilotPrefixVarianceAverage
    select θ p ε H m hselect hp hθ hε hdiv hsub (δ / 2) (half_pos hδ)
  have hscale : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) / (adaptiveMainSize m n : ℝ) - 1| < δ / (2 * K) := by
    have ht := adaptive_mainScale_tendsto_one m hsub
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht
      (δ / (2 * K)) (by positivity)
    exact eventually_atTop.2 ⟨N, fun n hn => by
      simpa only [Real.dist_eq] using hN n hn⟩
  filter_upwards [havg, hscale] with n hnavg hnscale
  intro hn h hH hlocal
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let A := pilotPrefixVarianceAverage select (localAlternative θ h n) p ε m hmn hselect hp hε
  have hA := pilotPrefixVarianceAverage_bounds
    select (localAlternative θ h n) p ε m hmn hselect hp hlocal hε
  have hAabs : |A| ≤ (pilotPhiUpper p ε) ^ 2 := by
    rw [abs_of_nonneg hA.1]
    exact hA.2
  have havg' : |A - Vstar θ p ε| < δ / 2 := by
    simpa only [A, hmn] using hnavg hn h hH hlocal
  calc
    |(n : ℝ) / (adaptiveMainSize m n : ℝ) * A - Vstar θ p ε| ≤
        |((n : ℝ) / (adaptiveMainSize m n : ℝ) - 1) * A| +
          |A - Vstar θ p ε| := by
      have hid : (n : ℝ) / (adaptiveMainSize m n : ℝ) * A - Vstar θ p ε =
          ((n : ℝ) / (adaptiveMainSize m n : ℝ) - 1) * A +
            (A - Vstar θ p ε) := by ring
      rw [hid]
      exact abs_add_le _ _
    _ ≤ |(n : ℝ) / (adaptiveMainSize m n : ℝ) - 1| *
          (pilotPhiUpper p ε) ^ 2 + |A - Vstar θ p ε| := by
      rw [abs_mul]
      gcongr
    _ ≤ |(n : ℝ) / (adaptiveMainSize m n : ℝ) - 1| * K +
          |A - Vstar θ p ε| := by
      gcongr
      dsimp [K]
      linarith
    _ < δ / (2 * K) * K + δ / 2 :=
      add_lt_add_of_lt_of_lt
        (mul_lt_mul_of_pos_right hnscale hK) havg'
    _ = δ := by
      field_simp [ne_of_gt hK]
      norm_num

/-- Uniform real-risk control sandwiches the local worst risk between two finite `ENNReal.ofReal` bounds. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub,hH), [the eventually local Worst Risk sandwich](goal).

Under the stated assumptions, the eventually local Worst Risk sandwich. -/
lemma eventually_localWorstRisk_sandwich
    (θ : TrialParameter) (p ε H : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) (hH : 0 < H) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ENNReal.ofReal (Vstar θ p ε - δ) ≤
          localWorstRisk (pilotEstimator p ε m select hselect hp hε) θ p H n ∧
        localWorstRisk (pilotEstimator p ε m select hselect hp hε) θ p H n ≤
          ENNReal.ofReal (Vstar θ p ε + δ) := by
  intro δ hδ
  have hunif := eventually_uniform_scaledPrefixVarianceAverage
    select θ p ε H m hselect hp hθ hε hdiv hsub δ hδ
  filter_upwards [hunif, eventually_ge_atTop 2] with n hnif hn
  have hlower : ENNReal.ofReal (Vstar θ p ε - δ) ≤
      localWorstRisk (pilotEstimator p ε m select hselect hp hε) θ p H n := by
    let h0 : TrialParameter := fun _ => 0
    have hh0 : h0 ∈ localIndexSet θ n H := by
      constructor
      · dsimp [h0]
        simpa using hH.le
      · have hz : localAlternative θ h0 n = θ := by
          funext k
          simp [h0, localAlternative]
        rw [hz]
        exact hθ
    have hid := pilotEstimator_localRisk_eq_scaled_prefixVarianceAverage
      select θ h0 p ε H m hselect hp hθ hε hsub n hn hh0
    have hclose := hnif hn h0 hh0.1 hh0.2
    have hreal : Vstar θ p ε - δ <
        (n : ℝ) / (adaptiveMainSize m n : ℝ) *
          pilotPrefixVarianceAverage select (localAlternative θ h0 n) p ε m
            (Nat.le_of_lt (hsub.2 n hn).2) hselect hp hε := by
      linarith [(abs_lt.mp hclose).1]
    have hmember : localRisk (pilotEstimator p ε m select hselect hp hε) θ h0 p n ∈
        {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ n H,
          u = localRisk (pilotEstimator p ε m select hselect hp hε) θ h p n} :=
      ⟨h0, hh0, rfl⟩
    calc
      ENNReal.ofReal (Vstar θ p ε - δ) ≤
          localRisk (pilotEstimator p ε m select hselect hp hε) θ h0 p n := by
        rw [hid]
        exact ENNReal.ofReal_le_ofReal hreal.le
      _ ≤ localWorstRisk (pilotEstimator p ε m select hselect hp hε) θ p H n := by
        unfold localWorstRisk
        exact le_sSup hmember
  have hupper : localWorstRisk (pilotEstimator p ε m select hselect hp hε) θ p H n ≤
      ENNReal.ofReal (Vstar θ p ε + δ) := by
    unfold localWorstRisk
    apply sSup_le
    intro u hu
    obtain ⟨h, hh, rfl⟩ := hu
    rw [pilotEstimator_localRisk_eq_scaled_prefixVarianceAverage
      select θ h p ε H m hselect hp hθ hε hsub n hn hh]
    apply ENNReal.ofReal_le_ofReal
    linarith [(abs_lt.mp (hnif hn h hh.1 hh.2)).2]
  exact ⟨hlower, hupper⟩

/-- Under the supplied quantities and conditions, the pilot local worst risk tendsto assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub,hH), [the pilot local Worst Risk tendsto](goal).

Under the stated assumptions, the pilot local Worst Risk tendsto. -/
lemma pilot_localWorstRisk_tendsto
    (θ : TrialParameter) (p ε H : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) (hH : 0 < H) :
    Tendsto (fun n =>
      localWorstRisk (pilotEstimator p ε m select hselect hp hε) θ p H n) atTop
      (nhds (ENNReal.ofReal (Vstar θ p ε))) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have haTop : a ≠ ⊤ := by
      intro hat
      rw [hat] at ha
      exact (not_lt_of_ge le_top) ha
    have hV0 : 0 ≤ Vstar θ p ε :=
      (inv_pos.mpr (Jstar_pos_interior θ p ε hp hθ hε)).le
    have haV : a.toReal < Vstar θ p ε := by
      have := (ENNReal.toReal_lt_toReal haTop ENNReal.ofReal_ne_top).2 ha
      simpa [ENNReal.toReal_ofReal hV0] using this
    let δ := (Vstar θ p ε - a.toReal) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hsand := eventually_localWorstRisk_sandwich
      select θ p ε H m hselect hp hθ hε hdiv hsub hH δ hδ
    filter_upwards [hsand] with n hn
    have hreal : a.toReal < Vstar θ p ε - δ := by
      dsimp [δ]
      linarith
    have hlt : a < ENNReal.ofReal (Vstar θ p ε - δ) :=
      (ENNReal.lt_ofReal_iff_toReal_lt haTop).2 hreal
    exact hlt.trans_le hn.1
  · intro b hb
    by_cases hbTop : b = ⊤
    · have hsand := eventually_localWorstRisk_sandwich
        select θ p ε H m hselect hp hθ hε hdiv hsub hH 1 (by norm_num)
      filter_upwards [hsand] with n hn
      rw [hbTop]
      exact lt_top_iff_ne_top.2 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hn.2)
    · have hV0 : 0 ≤ Vstar θ p ε :=
        (inv_pos.mpr (Jstar_pos_interior θ p ε hp hθ hε)).le
      have hVb : Vstar θ p ε < b.toReal := by
        have := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hbTop).2 hb
        simpa [ENNReal.toReal_ofReal hV0] using this
      let δ := (b.toReal - Vstar θ p ε) / 2
      have hδ : 0 < δ := by dsimp [δ]; linarith
      have hsand := eventually_localWorstRisk_sandwich
        select θ p ε H m hselect hp hθ hε hdiv hsub hH δ hδ
      filter_upwards [hsand] with n hn
      have hsum0 : 0 ≤ Vstar θ p ε + δ := by positivity
      have hreal : Vstar θ p ε + δ < b.toReal := by
        dsimp [δ]
        linarith
      have hlt : ENNReal.ofReal (Vstar θ p ε + δ) < b := by
        apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hbTop).1
        simpa [ENNReal.toReal_ofReal hsum0] using hreal
      exact hn.2.trans_lt hlt

/-- Under the supplied quantities and conditions, the pilot liminf local worst risk eq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub,hH), [the pilot liminf local Worst Risk eq](goal).

Under the stated assumptions, the pilot liminf local Worst Risk eq. -/
lemma pilot_liminf_localWorstRisk_eq
    (θ : TrialParameter) (p ε H : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) (hH : 0 < H) :
    Filter.liminf (fun n =>
      localWorstRisk (pilotEstimator p ε m select hselect hp hε) θ p H n) atTop =
      ENNReal.ofReal (Vstar θ p ε) :=
  (pilot_localWorstRisk_tendsto select θ p ε H m hselect hp hθ hε hdiv hsub hH).liminf_eq

/-- The private-pilot estimator attains the exact local asymptotic risk. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hdiv,hsub), [the pilot local Asymptotic Risk eq](goal).

Under the stated assumptions, the pilot local Asymptotic Risk eq. -/
lemma pilot_localAsymptoticRisk_eq
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hdiv : PilotDiverges m) (hsub : PilotSublinear m) :
    localAsymptoticRisk (pilotEstimator p ε m select hselect hp hε) θ p =
      ENNReal.ofReal (Vstar θ p ε) := by
  apply localAsymptoticRisk_eq_of_liminf_localWorstRisk
  intro H hH
  exact pilot_liminf_localWorstRisk_eq
    select θ p ε H m hselect hp hθ hε hdiv hsub hH

end CausalSmith.Stat.LdpAteEfficiencySurface
