module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalRiskIdentity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotLocalization

/-! # Uniform finite-prefix control for private-pilot local risk -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

/-- The literal probability mass of a released pilot prefix. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Prefix Weight](goal) is determined by [the displayed parameters](hyp:θ,p,ε,m,n,u). -/
def pilotPrefixWeight (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (n : ℕ) (u : Fin (m n) → Fin 4) : ℝ :=
  ∏ j : Fin (m n), ∑ a : Fin 4,
    piTheta θ p a * rrPilotProbability ε a (u j)

/-- Prefix mass on which the clipped pilot selector leaves a coordinatewise `r`-neighborhood of the row parameter. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Prefix Bad Mass](goal) is determined by [the displayed parameters](hyp:θ,p,ε,r,m,hmn). -/
def pilotPrefixBadMass (θ : TrialParameter) (p ε r : ℝ) (m : ℕ → ℕ)
    {n : ℕ} (hmn : m n ≤ n) : ℝ :=
  ∑ u : Fin (m n) → Fin 4, pilotPrefixWeight θ p ε m n u *
    if r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
      r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1| then 1 else 0

/-- The selected-score variance averaged over the genuine pilot-prefix law. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Prefix Variance Average](goal) is determined by [the displayed parameters](hyp:select,θ,p,ε,m,hmn,hselect,hp,hε). -/
def pilotPrefixVarianceAverage (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) {n : ℕ} (hmn : m n ≤ n)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) : ℝ :=
  ∑ u : Fin (m n) → Fin 4, pilotPrefixWeight θ p ε m n u *
    adaptiveScoreVariance select θ (pilotAdaptivePrefixTheta p ε m hmn u)
      p ε

/-- Under the supplied quantities and conditions, the pilot prefix weight nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the pilot Prefix Weight nonneg](goal).

Under the stated assumptions, the pilot Prefix Weight nonneg. -/
lemma pilotPrefixWeight_nonneg (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (n : ℕ) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (u : Fin (m n) → Fin 4) :
    0 ≤ pilotPrefixWeight θ p ε m n u := by
  apply Finset.prod_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (piTheta_pos_interior θ p hp hθ a).le (by
    unfold rrPilotProbability
    split_ifs <;> positivity)

/-- Under [the supplied quantities and conditions](hyp:p), [the pilot prefix weight sum assertion](goal) holds. For [the displayed quantities and conditions](hyp:m,n), these specify the stated inputs. -/
lemma pilotPrefixWeight_sum (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (n : ℕ) :
    ∑ u : Fin (m n) → Fin 4, pilotPrefixWeight θ p ε m n u = 1 := by
  unfold pilotPrefixWeight
  calc
    _ = ∏ _j : Fin (m n), ∑ k : Fin 4,
        ∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a k := by
      simpa using (Fintype.prod_sum (fun _j : Fin (m n) => fun k : Fin 4 =>
        ∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a k)).symm
    _ = 1 := by simp [rrPilot_marginal_sum_eq_one]

/-- The real bad-prefix mass is exactly the corresponding event probability under the full transcript law. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn), [the transcript Law pilot Theta bad eq of Real prefix Bad Mass](goal).

Under the stated assumptions, the transcript Law pilot Theta bad eq of Real prefix Bad Mass. -/
lemma transcriptLaw_pilotTheta_bad_eq_ofReal_prefixBadMass
    (θ : TrialParameter) (p ε r : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    {n : ℕ} (hmn : m n ≤ n) :
    (transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n)
        {z | r ≤ |pilotTheta p ε m z 0 - θ 0| ∨
          r ≤ |pilotTheta p ε m z 1 - θ 1|} =
      ENNReal.ofReal (pilotPrefixBadMass θ p ε r m hmn) := by
  classical
  let μ := transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
  let A : Set (Transcript (pilotOutputFamily n)) :=
    {z | r ≤ |pilotTheta p ε m z 0 - θ 0| ∨
      r ≤ |pilotTheta p ε m z 1 - θ 1|}
  let e := fun uv : (Fin (m n) → Fin 4) × (Fin (n - m n) → Fin 14) =>
    pilotAdaptiveEncode hmn uv.1 uv.2
  have hmainSum (u : Fin (m n) → Fin 4) :
      ∑ v : Fin (n - m n) → Fin 14,
        ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
          p ε (v j) = 1 := by
    calc
      _ = ∏ _j : Fin (n - m n), ∑ s : Fin 14,
          adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε s := by
        simpa using (Fintype.prod_sum (fun _j : Fin (n - m n) => fun s : Fin 14 =>
          adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε s)).symm
      _ = ∏ _j : Fin (n - m n), (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro j _
        have hη : InteriorMeans (pilotAdaptivePrefixTheta p ε m hmn u) := by
          exact pilotTheta_interior p ε m
            (pilotAdaptiveEncode hmn u (fun _ => 0))
        exact adaptiveMainMass_sum select θ _ p ε hselect hp hη hε
      _ = 1 := by simp
  have hw (u : Fin (m n) → Fin 4) :
      0 ≤ pilotPrefixWeight θ p ε m n u :=
    pilotPrefixWeight_nonneg θ p ε m n hp hθ u
  have hm (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
      0 ≤ ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
        p ε (v j) := by
    apply Finset.prod_nonneg
    intro j _
    exact adaptiveMainMass_nonneg select θ _ p ε hselect hp hθ
      (pilotTheta_interior p ε m (pilotAdaptiveEncode hmn u (fun _ => 0))) hε (v j)
  have hatom (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
      μ {e (u, v)} = ENNReal.ofReal
        (pilotPrefixWeight θ p ε m n u *
          ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j)) := by
    rw [pilotAdaptive_joint_singleton_eq_prefix_mul_mainProduct
      select θ p ε m hselect hp hθ hε hmn u v]
    change ENNReal.ofReal (pilotPrefixWeight θ p ε m n u) *
      ENNReal.ofReal (∏ j, adaptiveMainMass select θ
        (pilotAdaptivePrefixTheta p ε m hmn u) p ε (v j)) = _
    exact (ENNReal.ofReal_mul (hw u)).symm
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  rw [show μ A = ∫⁻ z, A.indicator (fun _ => (1 : ENNReal)) z ∂μ by
    rw [lintegral_indicator hA, setLIntegral_one]]
  rw [MeasureTheory.lintegral_fintype]
  rw [sum_eq_sum_image_of_zero_off_range e
    (pilotAdaptiveEncode_pair_injective hmn)]
  · rw [Fintype.sum_prod_type]
    simp_rw [hatom]
    change (∑ u, ∑ v,
      A.indicator (fun _ => (1 : ENNReal)) (e (u, v)) *
        ENNReal.ofReal (pilotPrefixWeight θ p ε m n u *
          ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j))) = _
    have hind (u : Fin (m n) → Fin 4) (v : Fin (n - m n) → Fin 14) :
        A.indicator (fun _ => (1 : ENNReal)) (e (u, v)) =
          if r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
            r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1| then 1 else 0 := by
      rw [Set.indicator_apply]
      simp only [A, Set.mem_ofPred_eq, e,
        pilotTheta_pilotAdaptiveEncode p ε m hmn u v]
    simp_rw [hind]
    unfold pilotPrefixBadMass
    have hofReal_sum {B : Type} [Fintype B] (f : B → ℝ)
        (hf : ∀ b, 0 ≤ f b) :
        (∑ b, ENNReal.ofReal (f b)) = ENNReal.ofReal (∑ b, f b) := by
      simpa using (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ) (fun b _ => hf b)).symm
    have hinner (u : Fin (m n) → Fin 4) :
        (∑ v : Fin (n - m n) → Fin 14,
          (if r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
              r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1| then 1 else 0) *
            ENNReal.ofReal (pilotPrefixWeight θ p ε m n u *
              ∏ j, adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
                p ε (v j))) =
          ENNReal.ofReal (pilotPrefixWeight θ p ε m n u *
            if r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ 0| ∨
              r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ 1| then 1 else 0) := by
      split_ifs with hu
      · simp only [one_mul, mul_one]
        rw [hofReal_sum]
        · congr 1
          rw [← Finset.mul_sum, hmainSum u, mul_one]
        · intro v
          exact mul_nonneg (hw u) (hm u v)
      · simp
    simp_rw [hinner]
    apply hofReal_sum
    intro u
    exact mul_nonneg (hw u) (by split_ifs <;> positivity)
  · intro z hz
    have hzμ := pilotAdaptive_singleton_zero_of_not_range
      select θ p ε m hselect hp hε hmn z hz
    apply mul_eq_zero.mpr
    right
    simpa only [μ] using hzμ

/-- Uniform Chebyshev control of the bad prefix mass. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hr,hmn,hmpos,hδ0l,hδ0r,hδ1l,hδ1r), [the pilot Prefix Bad Mass le](goal).

Under the stated assumptions, the pilot Prefix Bad Mass le. -/
lemma pilotPrefixBadMass_le
    (θ : TrialParameter) (p ε r : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hr : 0 < r) {n : ℕ} (hmn : m n ≤ n) (hmpos : 0 < m n)
    (hδ0l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 0)
    (hδ0r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 0)
    (hδ1l : (m n + 2 : ℝ)⁻¹ + r ≤ θ 1)
    (hδ1r : (m n + 2 : ℝ)⁻¹ + r ≤ 1 - θ 1) :
    pilotPrefixBadMass θ p ε r m hmn ≤
      1 / ((m n : ℝ) *
        (r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2) +
      1 / ((m n : ℝ) *
        (r * p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2) := by
  have hmeasure := pilotTheta_deviation_le select θ p ε r m hselect hp hθ hε hr hmn hmpos
    hδ0l hδ0r hδ1l hδ1r
  rw [transcriptLaw_pilotTheta_bad_eq_ofReal_prefixBadMass
    select θ p ε r m hselect hp hθ hε hmn] at hmeasure
  let x := 1 / ((m n : ℝ) *
    (r * controlProb p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2)
  let y := 1 / ((m n : ℝ) *
    (r * p * (Real.exp ε - 1) / (Real.exp ε + 3)) ^ 2)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  change ENNReal.ofReal (pilotPrefixBadMass θ p ε r m hmn) ≤
    ENNReal.ofReal x + ENNReal.ofReal y at hmeasure
  rw [← ENNReal.ofReal_add hx hy] at hmeasure
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hx hy)).mp hmeasure

/-- A deterministic good/bad decomposition for the prefix-averaged variance. It uses the exact prefix weights and leaves only the genuine bad-prefix mass. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hθ',hε,hδ,hmn,hgood), [the pilot Prefix Variance Average error le](goal).

Under the stated assumptions, the pilot Prefix Variance Average error le. -/
lemma pilotPrefixVarianceAverage_error_le
    (θ θ' : TrialParameter) (p ε r δ : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hθ' : InteriorMeans θ') (hε : 0 < ε)
    (hδ : 0 ≤ δ) {n : ℕ} (hmn : m n ≤ n)
    (hgood : ∀ η : TrialParameter, InteriorMeans η →
      (∀ k : Fin 2, |η k - θ' k| < r) →
      |adaptiveScoreVariance select θ' η p ε - Vstar θ p ε| ≤ δ) :
    |pilotPrefixVarianceAverage select θ' p ε m hmn hselect hp hε - Vstar θ p ε| ≤
      δ + ((pilotPhiUpper p ε) ^ 2 + |Vstar θ p ε|) *
        pilotPrefixBadMass θ' p ε r m hmn := by
  let good : (Fin (m n) → Fin 4) → Prop := fun u =>
    |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ' 0| < r ∧
      |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ' 1| < r
  let w : (Fin (m n) → Fin 4) → ℝ := pilotPrefixWeight θ' p ε m n
  let g : (Fin (m n) → Fin 4) → ℝ := fun u =>
    adaptiveScoreVariance select θ' (pilotAdaptivePrefixTheta p ε m hmn u)
      p ε
  have hw (u : Fin (m n) → Fin 4) : 0 ≤ w u :=
    pilotPrefixWeight_nonneg θ' p ε m n hp hθ' u
  have hsum : ∑ u, w u = 1 := pilotPrefixWeight_sum θ' p ε m n
  have hgood' (u : Fin (m n) → Fin 4) (hu : good u) :
      |g u - Vstar θ p ε| ≤ δ := by
    apply hgood _
    · exact pilotTheta_interior p ε m
        (pilotAdaptiveEncode hmn u (fun _ => 0))
    · intro k
      fin_cases k
      · exact hu.1
      · exact hu.2
  have hdecomp := finitePilot_good_bad_average_error_le
    w g good (Vstar θ p ε) δ hw hsum
      (le_of_lt (inv_pos.mpr (Jstar_pos_interior θ p ε hp hθ hε))) hδ hgood'
  calc
    |pilotPrefixVarianceAverage select θ' p ε m hmn hselect hp hε - Vstar θ p ε| ≤
        δ + ∑ u, w u * if good u then 0 else |g u - Vstar θ p ε| := by
      simpa [pilotPrefixVarianceAverage, w, g] using hdecomp
    _ ≤ δ + ∑ u, w u * if good u then 0 else
          ((pilotPhiUpper p ε) ^ 2 + |Vstar θ p ε|) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro u _
      apply mul_le_mul_of_nonneg_left _ (hw u)
      split_ifs with hu
      · exact le_rfl
      · calc
          |g u - Vstar θ p ε| ≤ |g u| + |Vstar θ p ε| := abs_sub _ _
          _ ≤ (pilotPhiUpper p ε) ^ 2 + |Vstar θ p ε| := by
            gcongr
            have hη : InteriorMeans (pilotAdaptivePrefixTheta p ε m hmn u) := by
              exact pilotTheta_interior p ε m
                (pilotAdaptiveEncode hmn u (fun _ => 0))
            have hv0 : 0 ≤ g u :=
              adaptiveScoreVariance_nonneg select θ' _ p ε hselect hp hθ' hη hε
            rw [abs_of_nonneg hv0]
            exact adaptiveScoreVariance_le select θ' _ p ε hselect hp hθ' hη hε
    _ = δ + ((pilotPhiUpper p ε) ^ 2 + |Vstar θ p ε|) *
          pilotPrefixBadMass θ' p ε r m hmn := by
      unfold pilotPrefixBadMass good w
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hbad : r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ' 0| ∨
          r ≤ |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ' 1|
      · have hngood : ¬(|pilotAdaptivePrefixTheta p ε m hmn u 0 - θ' 0| < r ∧
            |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ' 1| < r) := by
          intro hg
          exact hbad.elim (fun h => (not_le_of_gt hg.1) h)
            (fun h => (not_le_of_gt hg.2) h)
        simp [hbad, hngood]
        ring
      · have hgood : |pilotAdaptivePrefixTheta p ε m hmn u 0 - θ' 0| < r ∧
            |pilotAdaptivePrefixTheta p ε m hmn u 1 - θ' 1| < r := by
          push Not at hbad
          exact hbad
        simp [hbad, hgood]

/-- Continuity at the diagonal gives one common neighborhood controlling both the local row parameter and the selected pilot parameter. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε), [the adaptive Score Variance uniform near diag](goal).

Under the stated assumptions, the adaptive Score Variance uniform near diag. -/
lemma adaptiveScoreVariance_uniform_near_diag
    (θ : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select) (hp : InteriorAssignment p)
    (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ θ' η : TrialParameter,
        dist θ' θ < r → dist η θ < r →
          |adaptiveScoreVariance select θ' η p ε - Vstar θ p ε| < δ := by
  intro δ hδ
  have hc := continuousAt_adaptiveScoreVariance_diag select θ p ε hselect hp hθ hε
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨r, hr, hcontrol⟩ := hc δ hδ
  refine ⟨r, hr, ?_⟩
  intro θ' η hθ' hη
  have hpair : dist (θ', η) (θ, θ) < r := by
    simpa only [Prod.dist_eq, max_lt_iff] using And.intro hθ' hη
  simpa only [Real.dist_eq, adaptiveScoreVariance_diag select θ p ε hselect hp hθ hε] using
    hcontrol hpair

/-- Compact notation for the exact local-risk identity on the local index set. For the displayed inputs and conditions, the stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hsub,hn,hh), [the pilot Estimator local Risk eq scaled prefix Variance Average](goal).

Under the stated assumptions, the pilot Estimator local Risk eq scaled prefix Variance Average. -/
lemma pilotEstimator_localRisk_eq_scaled_prefixVarianceAverage
    (θ h : TrialParameter) (p ε H : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hsub : PilotSublinear m) (n : ℕ) (hn : 2 ≤ n)
    (hh : h ∈ localIndexSet θ n H) :
    localRisk (pilotEstimator p ε m select hselect hp hε) θ h p n =
      ENNReal.ofReal ((n : ℝ) / (adaptiveMainSize m n : ℝ) *
        pilotPrefixVarianceAverage select (localAlternative θ h n) p ε m
          (Nat.le_of_lt (hsub.2 n hn).2) hselect hp hε) := by
  simpa only [pilotPrefixVarianceAverage, pilotPrefixWeight] using
    pilotEstimator_localRisk_eq_prefixVariance_of_mem_localIndexSet
      select θ h p ε H m hselect hp hθ hε hsub n hn hh


end CausalSmith.Stat.LdpAteEfficiencySurface
