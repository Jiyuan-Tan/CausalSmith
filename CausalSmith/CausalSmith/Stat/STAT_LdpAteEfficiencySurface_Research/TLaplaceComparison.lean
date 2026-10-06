module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Laplace
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.LaplaceMoments
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.LaplaceRatio
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OAConsistency
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotRates
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TBalancedReduction
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TPilotAttainment
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Comparison with the published custom Laplace release

The custom known-assignment sample mean has the displayed asymptotic variance.
Its Wald half-length constant exceeds the private-pilot oracle's at the
balanced binary-trial point. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter Causalean.Stat

/-- For [the supplied quantities and conditions](hyp:variance,n), the [asymptotic wald half length](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:γ), these specify the stated inputs. -/
def asymptoticWaldHalfLength (γ variance : ℝ) (n : ℕ) : ℝ :=
  waldCriticalValue γ * Real.sqrt (variance / n)

-- @node: Vstar_nonneg
/-- Under the supplied quantities and conditions, the vstar nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε), [the Vstar nonneg](goal).

Under the stated assumptions, the Vstar nonneg. -/
lemma Vstar_nonneg (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (θ : TrialParameter) (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    0 ≤ Vstar θ p ε := by
  have hπ (j : Fin 4) : 0 ≤ piTheta θ p j := by
    rcases hp with ⟨hp0, hp1⟩
    rcases hθ with ⟨h0, h0', h1, h1'⟩
    fin_cases j <;> simp only [piTheta, controlProb] <;>
      apply mul_nonneg <;> linarith
  have hr (s : Fin 14) (j : Fin 4) : 0 ≤ patternRay ε s j := by
    have he : 1 ≤ Real.exp ε := (Real.one_le_exp_iff).2 (le_of_lt hε)
    unfold patternRay privacyIncrement privacyRatio
    split_ifs <;> simp_all <;> linarith [Real.exp_pos ε]
  have hm (s : Fin 14) : 0 ≤ patternMass θ p ε s := by
    unfold patternMass
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hr s j)
  have hF (α : StaircaseWeight) (hα : staircaseFeasible ε α) (t : ℝ) :
      0 ≤ informationObjective θ p ε α t := by
    unfold informationObjective
    exact Finset.sum_nonneg fun s _ =>
      mul_nonneg (hα.1 s) (div_nonneg (sq_nonneg _) (hm s))
  have hJ : 0 ≤ Jstar θ p ε := by
    unfold Jstar
    apply Real.sSup_nonneg
    intro z hz
    rcases hz with ⟨α, hα, rfl⟩
    apply Real.sInf_nonneg
    intro y hy
    rcases hy with ⟨t, rfl⟩
    exact hF α hα t
  exact inv_nonneg.mpr hJ

-- @node: VOA_balanced_value
/-- [the voa balanced value assertion](goal) holds. -/
lemma VOA_balanced_value :
    VOA (fun _ => (1 / 2 : ℝ)) (1 / 2) 1 = 34 := by
  norm_num [VOA, sensitivity, contrast, controlProb]

-- @node: balanced_coth_sq_lt_34
/-- [the balanced coth sq lt 34 assertion](goal) holds. -/
lemma balanced_coth_sq_lt_34 :
    (Real.cosh (1 / 2) / Real.sinh (1 / 2)) ^ 2 < (34 : ℝ) := by
  have hs : (1 / 2 : ℝ) < Real.sinh (1 / 2) :=
    Real.self_lt_sinh_iff.mpr (by norm_num)
  have hspos : 0 < Real.sinh (1 / 2) := by linarith
  have hsq := Real.cosh_sq_sub_sinh_sq (1 / 2 : ℝ)
  rw [div_pow]
  apply (div_lt_iff₀ (sq_pos_of_pos hspos)).2
  nlinarith [sq_nonneg (Real.sinh (1 / 2) - 1 / 2)]

-- @node: thm:laplace-comparison
/-- the laplace comparison assertion holds. For the displayed quantities and conditions, these specify the stated inputs. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hpublic,hrep,hnoise,hε,hγ,hcritical,hselect), [the laplace comparison](goal).

Under the stated assumptions, the laplace comparison. -/
theorem laplace_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 W Y L : ℕ → Ω → ℝ)
    (θ : TrialParameter) (p ε γ : ℝ)
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (P : (n : PositiveSampleSize) → Measure (Fin n.val → PrivateAlphabet))
    (hpublic : P = BinaryTrialModel θ p hmodel.meansInterior hmodel.assignmentInterior)
    (hrep : ∀ n, μ.map (fun ω => fun i : Fin n.val => privateRecord W Y i ω) = P n)
    (hnoise : ComparatorNoise μ W Y L p ε)
    (hε : 0 < ε) (hγ : 0 < γ ∧ γ < 1)
    (hcritical : 0 < waldCriticalValue γ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    (hselect : StrongSaddleSelection p ε select) :
    (P = BinaryTrialModel θ p hmodel.meansInterior hmodel.assignmentInterior ∧
      ∀ n, μ.map (fun ω => fun i : Fin n.val => privateRecord W Y i ω) = P n) ∧
    Modes.TendstoInLaw (fun _ : ℕ => μ)
      (fun n ω => Real.sqrt n *
        (tauOA W Y L p n ω - contrast θ))
      atTop (gaussianMeasure 0 (VOA θ p ε)) ∧
    Tendsto (fun n =>
      asymptoticWaldHalfLength γ (VOA θ p ε) n /
      asymptoticWaldHalfLength γ (Vstar θ p ε) n)
      atTop (nhds (Real.sqrt (VOA θ p ε / Vstar θ p ε))) ∧
    (∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μ {ω | δ <
        |VhatOA W Y L p n ω - VOA θ p ε|})
        atTop (nhds 0)) ∧
    (∃ m : ℕ → ℕ, m = Nat.sqrt ∧ PilotDiverges m ∧ PilotSublinear m ∧
      ∀ δ : ℝ, 0 < δ →
      ∀ ν : (n : ℕ) →
          Measure (Ω × Transcript (pilotOutputFamily n)),
        (∀ n, (ν n).map Prod.fst = μ ∧
          (ν n).map Prod.snd =
            transcriptLaw
              (pilotEstimator p ε m select hselect hmodel.assignmentInterior hε)
              θ p n) →
        Tendsto (fun n => (ν n)
          {u | δ < |Real.sqrt
            (VhatOA W Y L p n u.1 /
              VhatStar p ε m
                (select)
                u.2) -
            Real.sqrt (VOA θ p ε / Vstar θ p ε)|})
          atTop (nhds 0)) ∧
    VOA (fun _ => (1 / 2 : ℝ)) (1 / 2) 1 = 34 ∧
    Vstar (fun _ => (1 / 2 : ℝ)) (1 / 2) 1 =
      (Real.cosh (1 / 2) / Real.sinh (1 / 2)) ^ 2 ∧
    Vstar (fun _ => (1 / 2 : ℝ)) (1 / 2) 1 <
      VOA (fun _ => (1 / 2 : ℝ)) (1 / 2) 1 := by
  have hbalanced :
      Vstar (fun _ => (1 / 2 : ℝ)) (1 / 2) 1 =
        (Real.cosh (1 / 2) / Real.sinh (1 / 2)) ^ 2 := by
    have h := (balanced_reduction μ Y0 Y1 W Y
      (fun _ => (1 / 2 : ℝ)) 1
      (by norm_num [InteriorMeans]) (by norm_num) (by norm_num)).1
    simpa [contrast] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, VOA_balanced_value, hbalanced, ?_⟩
  · exact ⟨hpublic, hrep⟩
  · exact oaRelease_clt hmodel hnoise hε
  · have hV : 0 ≤ Vstar θ p ε :=
      Vstar_nonneg select θ p ε hselect hmodel.assignmentInterior hmodel.meansInterior hε
    have hpoint (n : ℕ) (hn : 0 < n) :
        asymptoticWaldHalfLength γ (VOA θ p ε) n /
          asymptoticWaldHalfLength γ (Vstar θ p ε) n =
          Real.sqrt (VOA θ p ε / Vstar θ p ε) := by
      have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnreal)
      rw [asymptoticWaldHalfLength, asymptoticWaldHalfLength,
        Real.sqrt_div' _ (le_of_lt hnreal),
        Real.sqrt_div' _ (le_of_lt hnreal), Real.sqrt_div' _ hV]
      field_simp
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (hpoint n hn).symm
  · exact oaVariance_consistency hmodel hnoise hε
  · refine ⟨Nat.sqrt, rfl, natSqrt_pilotDiverges, natSqrt_pilotSublinear, ?_⟩
    intro δ hδ ν hν
    have hfixed : FixedPrivacy (fun _ => ε) ε := ⟨hε, fun _ => rfl⟩
    have hpilot := pilot_attainment θ p ε γ
      hmodel.assignmentInterior hmodel.meansInterior (fun _ => ε) hfixed select hselect
      hγ Nat.sqrt natSqrt_pilotDiverges natSqrt_pilotSublinear
    have hpilotVar := hpilot.2.2.2.1
    have hcoupling (n : ℕ) : IsCoupling (ν n) μ
        (transcriptLaw
          (pilotEstimator p ε Nat.sqrt select hselect hmodel.assignmentInterior hε) θ p n) := by
      letI : IsProbabilityMeasure (ν n) := by
        letI : IsProbabilityMeasure (Measure.map Prod.fst (ν n)) :=
          (hν n).1 ▸ inferInstance
        exact Measure.isProbabilityMeasure_of_map Prod.fst
      exact ⟨inferInstance, (hν n).1, (hν n).2⟩
    have hVpos : 0 < Vstar θ p ε := by
      unfold Vstar
      exact inv_pos.mpr (Jstar_pos_interior θ p ε
        hmodel.assignmentInterior hmodel.meansInterior hε)
    exact Modes.coupled_sqrtRatio_tendsto_strict_abs
      (fun _ : ℕ => μ)
      (fun n => transcriptLaw
        (pilotEstimator p ε Nat.sqrt select hselect hmodel.assignmentInterior hε) θ p n)
      ν hcoupling
      (fun n ω => VhatOA W Y L p n ω)
      (fun _ z => VhatStar p ε Nat.sqrt
        (select) z)
      (VOA θ p ε) (Vstar θ p ε) hVpos atTop
      (fun _ z => VhatStar_nonneg p ε Nat.sqrt
        (select) z)
      (oaVariance_consistency hmodel hnoise hε) hpilotVar δ hδ
  · rw [hbalanced, VOA_balanced_value]
    exact balanced_coth_sq_lt_34

end CausalSmith.Stat.LdpAteEfficiencySurface
