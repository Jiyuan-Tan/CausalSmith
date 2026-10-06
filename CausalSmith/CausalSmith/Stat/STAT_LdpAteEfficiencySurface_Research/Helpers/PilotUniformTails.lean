module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalRiskIdentity
/-! # Uniform squared tails for the private-pilot estimator — finite-product fourth moments. -/
public section
noncomputable section
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
private lemma finiteIID_sum_second_fourth {A : Type*} [Fintype A]
    (N : ℕ) (w f : A → ℝ)
    (hw : ∑ a, w a = 1) (hc : ∑ a, w a * f a = 0) :
    (∑ v : Fin N → A, (∏ j, w (v j)) * (∑ j, f (v j)) ^ 2) =
        (N : ℝ) * ∑ a, w a * (f a) ^ 2 ∧
    (∑ v : Fin N → A, (∏ j, w (v j)) * (∑ j, f (v j)) ^ 4) =
        (N : ℝ) * ∑ a, w a * (f a) ^ 4 +
          3 * (N : ℝ) * ((N : ℝ) - 1) * (∑ a, w a * (f a) ^ 2) ^ 2 := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    let m2 : ℝ := ∑ a, w a * (f a) ^ 2
    let m4 : ℝ := ∑ a, w a * (f a) ^ 4
    let mass : (Fin N → A) → ℝ := fun v => ∏ j, w (v j)
    let total : (Fin N → A) → ℝ := fun v => ∑ j, f (v j)
    have hmass : ∑ v : Fin N → A, mass v = 1 := by
      change (∑ v : Fin N → A, ∏ j, w (v j)) = 1
      rw [← Fintype.prod_sum]
      simp [hw]
    have htailfirst : ∑ v : Fin N → A, mass v * total v = 0 := by
      simpa [mass, total, hc] using
        (finiteProduct_weighted_sum_expectation N w f hw)
    have hsecond : ∑ v : Fin N → A, mass v * (total v) ^ 2 = (N : ℝ) * m2 := by
      simpa [mass, total, m2] using ih.1
    have hfourth : ∑ v : Fin N → A, mass v * (total v) ^ 4 =
        (N : ℝ) * m4 + 3 * (N : ℝ) * ((N : ℝ) - 1) * m2 ^ 2 := by
      simpa [mass, total, m2, m4] using ih.2
    constructor
    · rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) => A))
          (fun z : A × (Fin N → A) =>
            (∏ j, w ((Fin.cons (α := fun _ => A) z.1 z.2) j)) *
              (∑ j, f ((Fin.cons (α := fun _ => A) z.1 z.2) j)) ^ 2)
          _ (fun _ => rfl)]
      simp only [Fintype.sum_prod_type, Fin.prod_univ_succ, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      change (∑ a : A, ∑ v : Fin N → A,
        (w a * mass v) * (f a + total v) ^ 2) = _
      simp_rw [show ∀ (a : A) (v : Fin N → A),
          (w a * mass v) * (f a + total v) ^ 2 =
            (w a * (f a)^2) * mass v +
              (2 * w a * f a) * (mass v * total v) +
              w a * (mass v * (total v)^2) by intro a v; ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hmass]
      rw [hsecond]
      simp only [← Finset.sum_mul, hw]
      rw [htailfirst]
      simp [m2]
      ring
    · rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) => A))
          (fun z : A × (Fin N → A) =>
            (∏ j, w ((Fin.cons (α := fun _ => A) z.1 z.2) j)) *
              (∑ j, f ((Fin.cons (α := fun _ => A) z.1 z.2) j)) ^ 4)
          _ (fun _ => rfl)]
      simp only [Fintype.sum_prod_type, Fin.prod_univ_succ, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      change (∑ a : A, ∑ v : Fin N → A,
        (w a * mass v) * (f a + total v) ^ 4) = _
      simp_rw [show ∀ (a : A) (v : Fin N → A),
          (w a * mass v) * (f a + total v) ^ 4 =
            (w a * (f a)^4) * mass v +
              (4 * w a * (f a)^3) * (mass v * total v) +
              (6 * w a * (f a)^2) * (mass v * (total v)^2) +
              (4 * w a * f a) * (mass v * (total v)^3) +
              w a * (mass v * (total v)^4) by intro a v; ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hmass]
      rw [hsecond, hfourth]
      simp only [← Finset.sum_mul, hw]
      rw [htailfirst]
      rw [show (∑ a, 4 * w a * f a) = 0 by
        calc
          _ = 4 * ∑ a, w a * f a := by rw [Finset.mul_sum]; ring
          _ = 0 := by rw [hc]; ring]
      rw [show (∑ a, 6 * w a * f a ^ 2) = 6 * m2 by
        calc
          _ = 6 * ∑ a, w a * f a ^ 2 := by rw [Finset.mul_sum]; ring
          _ = 6 * m2 := by rfl]
      simp [m2, m4]
      ring
private lemma finiteIID_normalized_fourth_le {A : Type*} [Fintype A]
    (N : ℕ) (w f : A → ℝ) (B : ℝ)
    (hN : 0 < N) (hw0 : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1)
    (hc : ∑ a, w a * f a = 0) (hf : ∀ a, |f a| ≤ B) :
    (∑ v : Fin N → A, (∏ j, w (v j)) *
      ((Real.sqrt (N : ℝ))⁻¹ * ∑ j, f (v j)) ^ 4) ≤ 4 * B ^ 4 := by
  classical
  let m2 : ℝ := ∑ a, w a * f a ^ 2
  let m4 : ℝ := ∑ a, w a * f a ^ 4
  have hA : (Finset.univ : Finset A).Nonempty := by
    by_contra hempty
    have := hw
    simp [Finset.not_nonempty_iff_eq_empty.mp hempty] at this
  obtain ⟨a0, _⟩ := hA
  have hB : 0 ≤ B := (abs_nonneg (f a0)).trans (hf a0)
  have hm2_nonneg : 0 ≤ m2 := by
    dsimp [m2]
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hw0 a) (sq_nonneg _)
  have hm2 : m2 ≤ B ^ 2 := by
    dsimp [m2]
    calc
      (∑ a, w a * f a ^ 2) ≤ ∑ a, w a * B ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hw0 a)
        exact (sq_le_sq).2 (by simpa [abs_of_nonneg hB] using hf a)
      _ = B ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]
  have hm4 : m4 ≤ B ^ 4 := by
    dsimp [m4]
    calc
      (∑ a, w a * f a ^ 4) ≤ ∑ a, w a * B ^ 4 := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hw0 a)
        have hs : f a ^ 2 ≤ B ^ 2 := by
          exact (sq_le_sq).2 (by simpa [abs_of_nonneg hB] using hf a)
        calc
          f a ^ 4 = (f a ^ 2) ^ 2 := by ring
          _ ≤ (B ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg (f a)) hs 2
          _ = B ^ 4 := by ring
      _ = B ^ 4 := by rw [← Finset.sum_mul, hw, one_mul]
  have hm2sq : m2 ^ 2 ≤ B ^ 4 := by
    calc
      m2 ^ 2 ≤ (B ^ 2) ^ 2 := pow_le_pow_left₀ hm2_nonneg hm2 2
      _ = B ^ 4 := by ring
  have hexact := (finiteIID_sum_second_fourth N w f hw hc).2
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hNr.le
  have hscale : ((Real.sqrt (N : ℝ))⁻¹) ^ 4 = ((N : ℝ)⁻¹) ^ 2 := by
    calc
      ((Real.sqrt (N : ℝ))⁻¹) ^ 4 =
          (((Real.sqrt (N : ℝ)) ^ 2)⁻¹) ^ 2 := by ring
      _ = _ := by rw [hsqrt]
  have hexp : (N : ℝ) * m4 +
      3 * (N : ℝ) * ((N : ℝ) - 1) * m2 ^ 2 ≤
      4 * (N : ℝ) ^ 2 * B ^ 4 := by
    have hNminus : 0 ≤ (N : ℝ) - 1 := by linarith
    have hB4 : 0 ≤ B ^ 4 := by positivity
    have hfirst := mul_le_mul_of_nonneg_left hm4 hNr.le
    have hpairs := mul_le_mul_of_nonneg_left hm2sq
      (show 0 ≤ 3 * (N : ℝ) * ((N : ℝ) - 1) by positivity)
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hNle hB4]
  calc
    (∑ v : Fin N → A, (∏ j, w (v j)) *
        ((Real.sqrt (N : ℝ))⁻¹ * ∑ j, f (v j)) ^ 4) =
        ((N : ℝ)⁻¹) ^ 2 * ((N : ℝ) * m4 +
          3 * (N : ℝ) * ((N : ℝ) - 1) * m2 ^ 2) := by
      rw [← hexact]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [mul_pow, hscale]
      ring
    _ ≤ ((N : ℝ)⁻¹) ^ 2 * (4 * (N : ℝ) ^ 2 * B ^ 4) :=
      mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    _ = 4 * B ^ 4 := by field_simp
private lemma pilot_scaledError_fourth_lintegral_eq_encoded
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n)
    (hlocal : InteriorMeans (localAlternative θ h n)) :
    (∫⁻ z, ENNReal.ofReal
      ((scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z) ^ 4)
      ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε)
        (localAlternative θ h n) p n) =
      ENNReal.ofReal
        (∑ u : Fin (m n) → Fin 4,
          (∏ j : Fin (m n), ∑ a : Fin 4,
            piTheta (localAlternative θ h n) p a *
              rrPilotProbability ε a (u j)) *
          ∑ v : Fin (n - m n) → Fin 14,
            (∏ j, adaptiveMainMass select (localAlternative θ h n)
              (pilotAdaptivePrefixTheta p ε m
                (Nat.le_of_lt (hsub.2 n hn).2) u)
              p ε (v j)) *
            (Real.sqrt (n : ℝ) *
              (contrast (pilotAdaptivePrefixTheta p ε m
                  (Nat.le_of_lt (hsub.2 n hn).2) u) +
                ((n - m n : ℕ) : ℝ)⁻¹ *
                  (∑ j, adaptiveSelectedScore select
                    (pilotAdaptivePrefixTheta p ε m
                      (Nat.le_of_lt (hsub.2 n hn).2) u)
                    p ε (v j)) -
                contrast (localAlternative θ h n))) ^ 4) := by
  classical
  unfold PilotSublinear at hsub
  let θn := localAlternative θ h n
  let P := pilotEstimator p ε m select hselect hp hε
  let μ := transcriptLaw P θn p n
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let e := fun uv : (Fin (m n) → Fin 4) × (Fin (n - m n) → Fin 14) =>
    pilotAdaptiveEncode hmn uv.1 uv.2
  rw [MeasureTheory.lintegral_fintype]
  change (∑ z : Transcript (pilotOutputFamily n),
    ENNReal.ofReal ((scaledError P θ h n z) ^ 4) * μ {z}) = _
  rw [sum_eq_sum_image_of_zero_off_range e
    (pilotAdaptiveEncode_pair_injective hmn)]
  · rw [Fintype.sum_prod_type]
    have hpilot_nonneg (u : Fin (m n) → Fin 4) :
        0 ≤ ∏ j : Fin (m n), ∑ a : Fin 4,
          piTheta θn p a * rrPilotProbability ε a (u j) := by
      apply Finset.prod_nonneg
      intro j _
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (piTheta_pos_interior θn p hp hlocal a).le (by
        unfold rrPilotProbability
        split_ifs <;> positivity)
    have hmain_nonneg (u : Fin (m n) → Fin 4)
        (v : Fin (n - m n) → Fin 14) :
        0 ≤ ∏ j : Fin (n - m n),
          adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j) := by
      apply Finset.prod_nonneg
      intro j _
      exact adaptiveMainMass_nonneg select θn _ p ε hselect hp hlocal
        (pilotTheta_interior p ε m
          (pilotAdaptiveEncode hmn u (fun _ => 0))) hε (v j)
    have hatom (u : Fin (m n) → Fin 4)
        (v : Fin (n - m n) → Fin 14) :
        μ {e (u, v)} = ENNReal.ofReal
          ((∏ j : Fin (m n), ∑ a : Fin 4,
              piTheta θn p a * rrPilotProbability ε a (u j)) *
            ∏ j : Fin (n - m n),
              adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (v j)) := by
      rw [pilotAdaptive_joint_singleton_eq_prefix_mul_mainProduct
        select θn p ε m hselect hp hlocal hε hmn u v]
      rw [← ENNReal.ofReal_mul (hpilot_nonneg u)]
    have herr (u : Fin (m n) → Fin 4)
        (v : Fin (n - m n) → Fin 14) :
        scaledError P θ h n (e (u, v)) =
          Real.sqrt (n : ℝ) *
            (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
              ((n - m n : ℕ) : ℝ)⁻¹ *
                (∑ j, adaptiveSelectedScore select
                  (pilotAdaptivePrefixTheta p ε m hmn u)
                  p ε (v j)) - contrast θn) := by
      unfold scaledError P
      change Real.sqrt (n : ℝ) *
        (tauStar p ε m (select) (e (u, v)) -
          contrast θn) = _
      rw [tauStar_pilotAdaptiveEncode select p ε m hp hε hmn u v]
    simp_rw [hatom, herr]
    let q : (Fin (m n) → Fin 4) → (Fin (n - m n) → Fin 14) → ℝ :=
      fun u v => (Real.sqrt (n : ℝ) *
        (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
          ((n - m n : ℕ) : ℝ)⁻¹ *
            (∑ j, adaptiveSelectedScore select
              (pilotAdaptivePrefixTheta p ε m hmn u)
              p ε (v j)) - contrast θn)) ^ 4
    let r : (Fin (m n) → Fin 4) → (Fin (n - m n) → Fin 14) → ℝ :=
      fun u v =>
        (∏ j : Fin (m n), ∑ a : Fin 4,
          piTheta θn p a * rrPilotProbability ε a (u j)) *
        ∏ j : Fin (n - m n),
          adaptiveMainMass select θn (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j)
    change (∑ u, ∑ v, ENNReal.ofReal (q u v) * ENNReal.ofReal (r u v)) = _
    rw [show (∑ u, ∑ v, ENNReal.ofReal (q u v) * ENNReal.ofReal (r u v)) =
        ∑ u, ∑ v, ENNReal.ofReal (q u v * r u v) by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      exact (ENNReal.ofReal_mul (show 0 ≤ q u v by
        dsimp [q]
        positivity)).symm]
    have hofReal_sum {A : Type} [Fintype A] (q : A → ℝ)
        (hq : ∀ a, 0 ≤ q a) :
        (∑ a, ENNReal.ofReal (q a)) = ENNReal.ofReal (∑ a, q a) := by
      simpa using (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ) (fun a _ => hq a)).symm
    calc
      (∑ u, ∑ v, ENNReal.ofReal (q u v * r u v)) =
          ∑ u, ENNReal.ofReal (∑ v, q u v * r u v) := by
        apply Finset.sum_congr rfl
        intro u _
        exact hofReal_sum _ (fun v => mul_nonneg (by
          dsimp [q]
          positivity) (by
          dsimp only [r]
          exact mul_nonneg (hpilot_nonneg u) (hmain_nonneg u v)))
      _ = ENNReal.ofReal (∑ u, ∑ v, q u v * r u v) := by
        exact hofReal_sum _ (fun u => Finset.sum_nonneg fun v _ =>
          mul_nonneg (by dsimp [q]; positivity) (by
            dsimp only [r]
            exact mul_nonneg (hpilot_nonneg u) (hmain_nonneg u v)))
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        dsimp only [q, r, θn, hmn]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
  · intro z hz
    have hzμ := pilotAdaptive_singleton_zero_of_not_range
      select θn p ε m hselect hp hε hmn z hz
    apply mul_eq_zero.mpr
    right
    simpa only [μ, P] using hzμ
private lemma pilot_scaledError_fourth_lintegral_le
    (θ h : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n)
    (hlocal : InteriorMeans (localAlternative θ h n))
    (hnN : (n : ℝ) / (adaptiveMainSize m n : ℝ) ≤ 2) :
    (∫⁻ z, ENNReal.ofReal
      ((scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z) ^ 4)
      ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε)
        (localAlternative θ h n) p n) ≤
      ENNReal.ofReal (16 * (2 * pilotPhiUpper p ε) ^ 4) := by
  classical
  rw [pilot_scaledError_fourth_lintegral_eq_encoded
    select θ h p ε m hselect hp hε hsub n hn hlocal]
  apply ENNReal.ofReal_le_ofReal
  let hmn : m n ≤ n := Nat.le_of_lt (hsub.2 n hn).2
  let C : ℝ := 16 * (2 * pilotPhiUpper p ε) ^ 4
  let wp : (Fin (m n) → Fin 4) → ℝ := fun u =>
    ∏ j : Fin (m n), ∑ a : Fin 4,
      piTheta (localAlternative θ h n) p a *
        rrPilotProbability ε a (u j)
  have hwp0 (u : Fin (m n) → Fin 4) : 0 ≤ wp u := by
    apply Finset.prod_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg
      (piTheta_pos_interior (localAlternative θ h n) p hp hlocal a).le
      (by unfold rrPilotProbability; split_ifs <;> positivity)
  have hwpsum : ∑ u, wp u = 1 := by
    dsimp only [wp]
    calc
      _ = ∏ _j : Fin (m n), ∑ k : Fin 4, ∑ a : Fin 4,
          piTheta (localAlternative θ h n) p a *
            rrPilotProbability ε a k := by
        simpa using (Fintype.prod_sum (fun _j : Fin (m n) =>
          fun k : Fin 4 => ∑ a : Fin 4,
            piTheta (localAlternative θ h n) p a *
              rrPilotProbability ε a k)).symm
      _ = 1 := by simp [rrPilot_marginal_sum_eq_one]
  have hmain : adaptiveMainSize m n = n - m n := by
    simp [adaptiveMainSize, adaptivePilotSize_eq m hsub hn]
  have hN : 0 < adaptiveMainSize m n := by
    rw [hmain]
    exact Nat.sub_pos_of_lt (hsub.2 n hn).2
  have htrue : adaptiveTrueParam θ h n = localAlternative θ h n :=
    adaptiveTrueParam_eq_localAlternative θ h n hlocal
  have hcond (u : Fin (m n) → Fin 4) :
      (∑ v : Fin (n - m n) → Fin 14,
        (∏ j, adaptiveMainMass select (localAlternative θ h n)
          (pilotAdaptivePrefixTheta p ε m hmn u)
          p ε (v j)) *
        (Real.sqrt (n : ℝ) *
          (contrast (pilotAdaptivePrefixTheta p ε m hmn u) +
            ((n - m n : ℕ) : ℝ)⁻¹ *
              (∑ j, adaptiveSelectedScore select
                (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (v j)) -
            contrast (localAlternative θ h n))) ^ 4) ≤ C := by
    let η0 := pilotAdaptivePrefixTheta p ε m hmn u
    have hη0 : InteriorMeans η0 :=
      pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0))
    let N := n - m n
    let w : Fin 14 → ℝ := adaptiveMainMass select
      (localAlternative θ h n) η0 p ε
    let f : Fin 14 → ℝ := fun s =>
      adaptiveSelectedScore select η0 p ε s -
        (contrast (localAlternative θ h n) - contrast η0)
    let B := 2 * pilotPhiUpper p ε
    have hN' : 0 < N := by
      dsimp [N]
      exact Nat.sub_pos_of_lt (hsub.2 n hn).2
    have hw0 : ∀ s, 0 ≤ w s := by
      intro s
      exact adaptiveMainMass_nonneg select _ _ p ε hselect hp hlocal hη0 hε s
    have hw : ∑ s, w s = 1 :=
      adaptiveMainMass_sum select _ _ p ε hselect hp hη0 hε
    have hf0 : ∑ s, w s * f s = 0 := by
      let η : ℕ → TrialParameter := fun k => if k = n then η0 else θ
      have hη : ∀ k, InteriorMeans (η k) := by
        intro k
        simp only [η]
        split_ifs <;> assumption
      simpa only [w, f, η, if_pos, adaptivePilotRowMass,
        adaptivePilotRowScore, htrue] using
        (adaptivePilotRowScore_centered select θ h η p ε hselect hp hη hε n)
    have hfB : ∀ s, |f s| ≤ B := by
      intro s
      let η : ℕ → TrialParameter := fun k => if k = n then η0 else θ
      have hη : ∀ k, InteriorMeans (η k) := by
        intro k
        simp only [η]
        split_ifs <;> assumption
      simpa only [B, w, f, η, if_pos, adaptivePilotRowScore, htrue] using
        (adaptivePilotRowScore_abs_le select θ h η p ε hselect hp hθ hη hε n s)
    have hnorm := finiteIID_normalized_fourth_le N w f B hN' hw0 hw hf0 hfB
    have herr (v : Fin N → Fin 14) :
        contrast η0 + (N : ℝ)⁻¹ *
            (∑ j, adaptiveSelectedScore select η0 p ε (v j)) -
            contrast (localAlternative θ h n) =
          (N : ℝ)⁻¹ * ∑ j, f (v j) := by
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN'
      simp only [f, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
      rw [hcard]
      field_simp
      ring
    have hratio : (n : ℝ) / (N : ℝ) ≤ 2 := by
      simpa only [N, hmain] using hnN
    have hratio0 : 0 ≤ (n : ℝ) / (N : ℝ) := by positivity
    have hratioSq : ((n : ℝ) / (N : ℝ)) ^ 2 ≤ 4 := by nlinarith
    have heq (v : Fin N → Fin 14) :
        (Real.sqrt (n : ℝ) *
          (contrast η0 + (N : ℝ)⁻¹ *
              (∑ j, adaptiveSelectedScore select η0 p ε (v j)) -
            contrast (localAlternative θ h n))) ^ 4 =
          ((n : ℝ) / (N : ℝ)) ^ 2 *
            ((Real.sqrt (N : ℝ))⁻¹ * ∑ j, f (v j)) ^ 4 := by
      rw [herr]
      have hsqrtn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg n)
      have hsqrtN : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hsqrtN_ne : Real.sqrt (N : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (by positivity))
      field_simp
      rw [show (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 by
          calc
            _ = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
            _ = _ := by rw [hsqrtn],
        show (Real.sqrt (N : ℝ)) ^ 4 = (N : ℝ) ^ 2 by
          calc
            _ = ((Real.sqrt (N : ℝ)) ^ 2) ^ 2 := by ring
            _ = _ := by rw [hsqrtN]]
      ring
    change (∑ v : Fin N → Fin 14, (∏ j : Fin N, w (v j)) *
      (Real.sqrt (n : ℝ) *
        (contrast η0 + (N : ℝ)⁻¹ *
            (∑ j, adaptiveSelectedScore select η0 p ε (v j)) -
          contrast (localAlternative θ h n))) ^ 4) ≤ C
    rw [show (∑ v : Fin N → Fin 14, (∏ j : Fin N, w (v j)) *
        (Real.sqrt (n : ℝ) *
          (contrast η0 + (N : ℝ)⁻¹ *
              (∑ j, adaptiveSelectedScore select η0 p ε (v j)) -
            contrast (localAlternative θ h n))) ^ 4) =
        ∑ v : Fin N → Fin 14, (∏ j : Fin N, w (v j)) *
        (((n : ℝ) / (N : ℝ)) ^ 2 *
          ((Real.sqrt (N : ℝ))⁻¹ * ∑ j, f (v j)) ^ 4) by
      apply Finset.sum_congr rfl
      intro v _
      rw [heq v],
      show (∑ v : Fin N → Fin 14, (∏ j : Fin N, w (v j)) *
        (((n : ℝ) / (N : ℝ)) ^ 2 *
          ((Real.sqrt (N : ℝ))⁻¹ * ∑ j, f (v j)) ^ 4)) =
        ((n : ℝ) / (N : ℝ)) ^ 2 *
          ∑ v : Fin N → Fin 14, (∏ j : Fin N, w (v j)) *
            ((Real.sqrt (N : ℝ))⁻¹ * ∑ j, f (v j)) ^ 4 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring]
    calc
      _ ≤ 4 * (4 * B ^ 4) := by
        apply mul_le_mul hratioSq hnorm
        · exact Finset.sum_nonneg fun v _ =>
            mul_nonneg (Finset.prod_nonneg fun j _ => hw0 (v j)) (by positivity)
        · norm_num
      _ = C := by simp [B, C]; ring
  change (∑ u, wp u * _) ≤ C
  calc
    (∑ u, wp u * _) ≤ ∑ u, wp u * C := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left (hcond u) (hwp0 u)
    _ = C := by rw [← Finset.sum_mul, hwpsum, one_mul]
private lemma squaredTail_lintegral_le_of_fourth {Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    (μ : MeasureTheory.Measure Ω) (X : Ω → ℝ) (T C : ℝ) (hT : 0 < T)
    (hfour : (∫⁻ z, ENNReal.ofReal ((X z) ^ 4) ∂μ) ≤ ENNReal.ofReal C) :
    (∫⁻ z, ENNReal.ofReal
      ((X z) ^ 2 * if T < |X z| then 1 else 0) ∂μ) ≤
      ENNReal.ofReal C / ENNReal.ofReal (T ^ 2) := by
  have hpoint (z : Ω) :
      ENNReal.ofReal ((X z) ^ 2 * if T < |X z| then 1 else 0) ≤
        ENNReal.ofReal ((X z) ^ 4) / ENNReal.ofReal (T ^ 2) := by
    rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hT)]
    apply ENNReal.ofReal_le_ofReal
    split_ifs with hz
    · have hsq : T ^ 2 < (X z) ^ 2 := by
        have := (sq_lt_sq₀ hT.le (abs_nonneg (X z))).2 hz
        simpa [sq_abs] using this
      apply (le_div_iff₀ (sq_pos_of_pos hT)).2
      have hmul := mul_le_mul_of_nonneg_left hsq.le (sq_nonneg (X z))
      nlinarith
    · simp only [mul_zero]
      exact div_nonneg (by positivity) (sq_nonneg T)
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ((X z) ^ 4) /
        ENNReal.ofReal (T ^ 2) ∂μ := MeasureTheory.lintegral_mono hpoint
    _ = (∫⁻ z, ENNReal.ofReal ((X z) ^ 4) ∂μ) /
        ENNReal.ofReal (T ^ 2) := by
      change (∫⁻ z, ENNReal.ofReal ((X z) ^ 4) *
        (ENNReal.ofReal (T ^ 2))⁻¹ ∂μ) = _
      rw [MeasureTheory.lintegral_mul_const _ (measurable_of_countable _)]
      rfl
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal (T ^ 2) :=
      ENNReal.div_le_div_right hfour _
/-- The private-pilot scaled error has uniformly vanishing squared tails over bounded local directions. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub), [the pilot scaled Error uniform squared tails](goal).

Under the stated assumptions, the pilot scaled Error uniform squared tails. -/
lemma pilot_scaledError_uniform_squared_tails
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hε : 0 < ε) (hsub : PilotSublinear m) :
    ∀ H : ℝ, 0 < H →
      Filter.Tendsto (fun M : ℕ =>
        Filter.limsup (fun n =>
          sSup {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ n H,
            u = ∫⁻ z, ENNReal.ofReal
              ((scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z) ^ 2 *
                if M < |scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z|
                then 1 else 0)
              ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε)
                (localAlternative θ h n) p n})
          Filter.atTop) Filter.atTop (nhds 0) := by
  intro H _hH
  let C : ℝ := 16 * (2 * pilotPhiUpper p ε) ^ 4
  let F : ℕ → ℝ≥0∞ := fun M =>
    Filter.limsup (fun n =>
      sSup {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ n H,
        u = ∫⁻ z, ENNReal.ofReal
          ((scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z) ^ 2 *
            if M < |scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z|
            then 1 else 0)
          ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε)
            (localAlternative θ h n) p n}) Filter.atTop
  let D : ℕ → ℝ≥0∞ := fun M =>
    ENNReal.ofReal C / ENNReal.ofReal ((M : ℝ) ^ 2)
  have hratio : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) / (adaptiveMainSize m n : ℝ) ≤ 2 := by
    have ht := adaptive_mainScale_tendsto_one m hsub
    exact ((tendsto_order.1 ht).2 2 (by norm_num)).mono fun _ hn => hn.le
  have hn2 : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  have hFD : ∀ᶠ M : ℕ in Filter.atTop, F M ≤ D M := by
    filter_upwards [Filter.eventually_gt_atTop 0] with M hM
    dsimp only [F, D]
    apply Filter.limsup_le_of_le (hf := by
      change ∃ b : ℝ≥0∞, ∀ a, (∀ᶠ n : ℕ in Filter.atTop,
        sSup {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ n H,
          u = ∫⁻ z, ENNReal.ofReal
            ((scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z) ^ 2 *
              if M < |scaledError (pilotEstimator p ε m select hselect hp hε) θ h n z|
              then 1 else 0)
            ∂transcriptLaw (pilotEstimator p ε m select hselect hp hε)
              (localAlternative θ h n) p n} ≤ a) → b ≤ a
      exact ⟨0, fun _ _ => bot_le⟩)
    filter_upwards [hratio, hn2] with n hnratio hn
    apply sSup_le
    intro u hu
    obtain ⟨h, hh, rfl⟩ := hu
    have hfour := pilot_scaledError_fourth_lintegral_le
      select θ h p ε m hselect hp hθ hε hsub n hn hh.2 hnratio
    exact squaredTail_lintegral_le_of_fourth
      (transcriptLaw (pilotEstimator p ε m select hselect hp hε)
        (localAlternative θ h n) p n)
      (scaledError (pilotEstimator p ε m select hselect hp hε) θ h n)
      (M : ℝ) C (by exact_mod_cast hM) hfour
  have hD : Filter.Tendsto D Filter.atTop (nhds 0) := by
    have hcast : Filter.Tendsto (fun M : ℕ => (M : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    have hden : Filter.Tendsto (fun M : ℕ => (M : ℝ) * (M : ℝ))
        Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      filter_upwards [(Filter.tendsto_atTop.1 hcast) b,
        Filter.eventually_gt_atTop 0] with M hb hM
      have hMreal : 1 ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    have hreal : Filter.Tendsto (fun M : ℕ => C / ((M : ℝ) ^ 2))
        Filter.atTop (nhds 0) := by
      simpa only [pow_two] using tendsto_const_nhds.div_atTop hden
    have heq : (fun M : ℕ => ENNReal.ofReal (C / ((M : ℝ) ^ 2))) =ᶠ[
        Filter.atTop] D := by
      filter_upwards [Filter.eventually_gt_atTop 0] with M hM
      dsimp only [D]
      rw [ENNReal.ofReal_div_of_pos]
      positivity
    simpa using (ENNReal.tendsto_ofReal hreal).congr' heq
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hD (Filter.Eventually.of_forall fun _ => bot_le) hFD
end CausalSmith.Stat.LdpAteEfficiencySurface
