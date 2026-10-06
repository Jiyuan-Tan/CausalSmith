module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.ScoreIdentity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Score-threshold overlap regret — welfare and regularization

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

-- @node: regularization_pointwise
/-- The deterministic comparison behind the regularization inequality, including ties. -/
lemma regularization_pointwise (t g : ℝ) (retained π : Bool)
    (htlo : -2 ≤ t) (hthi : t ≤ 2) (hg0 : 0 ≤ g)
    (hdel : retained = false → g = 1) :
    ((if π then (0:ℝ) else 1) - (if decide (0 ≤ t) then (0:ℝ) else 1)) *
      ((if retained then t else 0) + g) ≥
      (|t|+g)/4 * (if π = decide (0 ≤ t) then (0:ℝ) else 1) -
      2*(if retained = false ∧ t < 0 then (1:ℝ) else 0) -
      2*g*(if retained = true ∧ 0 < |t| ∧ |t| ≤ 2*g then (1:ℝ) else 0) := by
  by_cases ht : 0 ≤ t
  · cases retained <;> cases π <;>
      simp_all [abs_of_nonneg ht] <;> split_ifs at * <;> nlinarith
  · have ht' : t < 0 := lt_of_not_ge ht
    cases retained <;> cases π <;>
      simp_all [abs_of_neg ht'] <;> split_ifs at * <;> nlinarith

-- @node: offsetG_retention_cases
/-- On retained observations the offset is the inverse-overlap weight;
on deleted observations it is one and the contrast vanishes. -/
lemma offsetG_retention_cases (a : ℝ) (e : ℝ → ℝ) (o : Observation)
    (hp : 0 < min (e o.X) (1-e o.X)) :
    (a ≤ min (e o.X) (1-e o.X) →
      offsetG a e o.X = a / min (e o.X) (1-e o.X)) ∧
    (¬ a ≤ min (e o.X) (1-e o.X) →
      offsetG a e o.X = 1 ∧ gammaScore a e o = 0) := by
  constructor
  · intro hret
    have hle : a / min (e o.X) (1-e o.X) ≤ 1 :=
      (div_le_one hp).2 hret
    simp [offsetG, min_eq_right hle]
  · intro hdel
    have hle : min (e o.X) (1-e o.X) ≤ a := le_of_lt (lt_of_not_ge hdel)
    have hone : 1 ≤ a / min (e o.X) (1-e o.X) :=
      (one_le_div hp).2 hle
    constructor
    · simp [offsetG, min_eq_left hone]
    · simp [gammaScore, hdel]

-- @node: lem:regularization-inequality
/-- Objective comparison plus absolute, second, and fourth score moments. -/
lemma regularization_inequality (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hClass : LawClass α γ θ n P e)
    (a : ℝ) (π : ℝ → Bool)
    (ha : 0 < a ∧ a ≤ 1/4) -- @realizes a(0<a≤1/4)
    (hπ : π ∈ thresholdClass) :
    popObjective P a π - popObjective P a (canonicalPolicy P) ≥
      regularizedLoss P a π/4 - 2*biasFunctional P a ∧
    (∀ᵐ o ∂P.obsLaw, |zScore a P.logger o| ≤ 2/a) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      ∫ o in {o | o.X ∈ B}, (zScore a P.logger o)^2 ∂P.obsLaw ≤
        ∫ x in B, 6*offsetG a P.logger x/a ∂P.PX) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      ∫ o in {o | o.X ∈ B}, (zScore a P.logger o)^4 ∂P.obsLaw ≤
        ∫ x in B, 24*offsetG a P.logger x/a^3 ∂P.PX) := by
  have hconsistent : Consistency P := hClass.consistent
  have hexchangeable : Exchangeability P := hClass.exchangeable
  have hbounded : BoundedPotentials P := hClass.bounded
  have hknown : KnownLogging P e := hClass.known
  have hpositive : Positivity P e := hClass.positive
  have hpositiveLogger : Positivity P P.logger := by
    have hsupport : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 :=
      ae_iff.mpr hClass.score.2
    filter_upwards [hpositive, hsupport] with x hx hX
    simpa only [hknown hX] using hx
  have hcanonical : CanonicalThreshold P := hClass.canonical
  have hloggerSpace : ∀ x ∈ Set.Icc (0:ℝ) 1,
      P.logger x ∈ Set.Ioo (0:ℝ) 1 := by
    intro x hx
    simpa only [hknown hx] using hClass.loggerSpace x hx
  refine ⟨?_, zScore_abs_ae P a ha hClass.wf hloggerSpace, ?_, ?_⟩
  · letI : IsProbabilityMeasure P.PX := hClass.score.1
    have hπb := thresholdClass_mem_binaryPolicyClass π hπ
    have hπm := score_policy_aemeasurable P hClass.wf π hπb
    have hstar := score_canonical_aemeasurable P hClass.wf
    have ht := score_tau_aemeasurable P hClass.wf
    have hl := logger_aemeasurable P hClass.wf
    have hg : AEMeasurable (offsetG a P.logger) P.PX := by
      unfold offsetG; fun_prop
    have hp : AEMeasurable (overlap P) P.PX := by
      change AEMeasurable (fun x => min (P.logger x) (1-P.logger x)) P.PX
      fun_prop
    have hmag : AEMeasurable (effectMagnitude P) P.PX := by
      change AEMeasurable (fun x => |P.tau x|) P.PX
      fun_prop
    have hret : NullMeasurableSet {x | a ≤ overlap P x} P.PX :=
      nullMeasurableSet_le aemeasurable_const hp
    have hdel : NullMeasurableSet {x | overlap P x < a ∧ P.tau x < 0} P.PX :=
      (nullMeasurableSet_lt hp aemeasurable_const).inter
        (nullMeasurableSet_lt ht aemeasurable_const)
    have hsmall : NullMeasurableSet {x | a ≤ overlap P x ∧
        0 < effectMagnitude P x ∧ effectMagnitude P x ≤ 2*offsetG a P.logger x} P.PX :=
      hret.inter ((nullMeasurableSet_lt aemeasurable_const hmag).inter
        (nullMeasurableSet_le hmag (aemeasurable_const.mul hg)))
    let d : ℝ → ℝ := fun x => if π x = canonicalPolicy P x then 0 else 1
    let b : ℝ → ℝ := fun x => if overlap P x < a ∧ P.tau x < 0 then 1 else 0
    let k : ℝ → ℝ := fun x => offsetG a P.logger x *
      (if a ≤ overlap P x ∧ 0 < effectMagnitude P x ∧
        effectMagnitude P x ≤ 2*offsetG a P.logger x then 1 else 0)
    let m : ℝ → ℝ := fun x => (if a ≤ overlap P x then P.tau x else 0) + offsetG a P.logger x
    let N : (ℝ → Bool) → ℝ → ℝ := fun ψ x => if ψ x then 0 else 1
    have hd : AEMeasurable d P.PX := by
      convert (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1:ℝ)) P.PX).indicator₀
        (nullMeasurableSet_eq_fun hπm hstar).compl using 1
      ext x; simp [d, Set.indicator]
    have hbm : AEMeasurable b P.PX := by
      convert (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1:ℝ)) P.PX).indicator₀
        hdel using 1
      ext x; simp [b, Set.indicator]
    have hkm : AEMeasurable k P.PX := by
      convert hg.indicator₀ hsmall using 1
      ext x; simp [k, Set.indicator]
    have hm : AEMeasurable m P.PX := by
      have hr : AEMeasurable (fun x => if a ≤ overlap P x then P.tau x else 0) P.PX := by
        convert ht.indicator₀ hret using 1
        ext x; simp [Set.indicator]
      exact hr.add hg
    have hgb : ∀ᵐ x ∂P.PX, 0 ≤ offsetG a P.logger x ∧ offsetG a P.logger x ≤ 1 := by
      filter_upwards [hpositiveLogger] with x hx
      have hpo : 0 < min (P.logger x) (1-P.logger x) :=
        lt_min hx.1 (by linarith [hx.2])
      exact ⟨le_min (by norm_num) (div_nonneg ha.1.le hpo.le), min_le_left _ _⟩
    have hmb : ∀ᵐ x ∂P.PX, |m x| ≤ 3 := by
      filter_upwards [hClass.effectBound, hgb] with x hx hgx
      have hrt : |(if a ≤ overlap P x then P.tau x else 0)| ≤ 2 := by
        split_ifs <;> simp_all
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hgx.1]; linarith)
    have hNm (ψ : ℝ → Bool) (hψ : AEMeasurable ψ P.PX) :
        Integrable (fun x => N ψ x * m x) P.PX := by
      apply score_bounded_integrable 3 ((score_negative_action_aemeasurable ψ hψ).mul hm)
      filter_upwards [hmb] with x hx
      change |N ψ x * m x| ≤ 3
      cases hψx : ψ x <;> simp [N, hψx, hx]
    have htd : Integrable (fun x => effectMagnitude P x * d x) P.PX := by
      apply score_bounded_integrable 2 (hmag.mul hd)
      filter_upwards [hClass.effectBound] with x hx
      change |effectMagnitude P x * d x| ≤ 2
      dsimp [d]; split_ifs <;> simp [effectMagnitude, hx]
    have hgd : Integrable (fun x => offsetG a P.logger x * d x) P.PX := by
      apply score_bounded_integrable 1 (hg.mul hd)
      filter_upwards [hgb] with x hx
      change |offsetG a P.logger x * d x| ≤ 1
      dsimp [d]; split_ifs <;> simp [abs_of_nonneg hx.1, hx.2]
    have hbint : Integrable b P.PX := by
      apply score_bounded_integrable 1 hbm
      exact ae_of_all _ fun x => by dsimp [b]; split_ifs <;> norm_num
    have hkint : Integrable k P.PX := by
      apply score_bounded_integrable 1 hkm
      filter_upwards [hgb] with x hx
      dsimp [k]; split_ifs <;> simp [abs_of_nonneg hx.1, hx.2]
    have hLint : Integrable (fun x => (effectMagnitude P x + offsetG a P.logger x)*d x) P.PX := by
      exact (htd.add hgd).congr (ae_of_all _ fun x => by dsimp; ring)
    have hRint : Integrable (fun x =>
        (effectMagnitude P x + offsetG a P.logger x)*d x/4 - 2*b x - 2*k x) P.PX :=
      ((hLint.div_const 4).sub (hbint.const_mul 2)).sub (hkint.const_mul 2)
    have hpoint : ∀ᵐ x ∂P.PX,
        (effectMagnitude P x + offsetG a P.logger x)*d x/4 - 2*b x - 2*k x ≤
          N π x*m x - N (canonicalPolicy P) x*m x := by
      filter_upwards [hClass.effectBound, hgb, hpositiveLogger] with x hx hgx hpx
      have hpo : 0 < min (P.logger x) (1-P.logger x) := lt_min hpx.1 (by linarith [hpx.2])
      have hdeleted : decide (a ≤ overlap P x) = false → offsetG a P.logger x = 1 := by
        intro hd
        have hr : ¬ a ≤ min (P.logger x) (1-P.logger x) := by
          simpa [overlap] using hd
        exact ((offsetG_retention_cases a P.logger ⟨x,false,0⟩ hpo).2 hr).1
      have h := regularization_pointwise (P.tau x) (offsetG a P.logger x)
        (decide (a ≤ overlap P x)) (π x) (abs_le.mp hx).1 (abs_le.mp hx).2 hgx.1 hdeleted
      have heq : (decide (a ≤ overlap P x) = false ∧ P.tau x < 0) ↔
          (overlap P x < a ∧ P.tau x < 0) := by simp
      simp only [Bool.decide_iff, Bool.decide_eq_true, heq, canonicalPolicy,
        effectMagnitude, d, b, k, m, N, mul_sub, sub_mul] at h ⊢
      -- Only the equality converting the pointwise lemma needs indicator simplification.
      convert h using 1 <;> split_ifs <;> simp_all <;> ring
    have hint : (∫ x, (effectMagnitude P x + offsetG a P.logger x)*d x/4 - 2*b x - 2*k x ∂P.PX) ≤
        ∫ x, N π x*m x - N (canonicalPolicy P) x*m x ∂P.PX :=
      integral_mono_ae hRint ((hNm π hπm).sub (hNm (canonicalPolicy P) hstar)) hpoint
    have hobj : (∫ x, N π x*m x - N (canonicalPolicy P) x*m x ∂P.PX) =
        popObjective P a π - popObjective P a (canonicalPolicy P) := by
      rw [integral_sub (hNm π hπm) (hNm (canonicalPolicy P) hstar)]
      rw [score_popObjective_identity α γ θ n P e hClass a ha π hπm,
        score_popObjective_identity α γ θ n P e hClass a ha (canonicalPolicy P) hstar]
    have hL : (∫ x, (effectMagnitude P x + offsetG a P.logger x)*d x ∂P.PX) =
        regularizedLoss P a π := by
      have hwelfare := regret_eq_effect_disagreement α γ θ n P e hClass π hπb
      change rawRegret P π = ∫ x, effectMagnitude P x * d x ∂P.PX at hwelfare
      rw [regularizedLoss, hwelfare]
      have hadd : (fun x => (effectMagnitude P x + offsetG a P.logger x)*d x) =
          (fun x => effectMagnitude P x*d x + offsetG a P.logger x*d x) := by
        funext x; ring
      rw [hadd, integral_add htd hgd]
      rfl
    have hbMass : (∫ x, b x ∂P.PX) =
        P.PX.real {x | overlap P x < a ∧ P.tau x < 0} := by
      have hbeq : b = {x | overlap P x < a ∧ P.tau x < 0}.indicator (fun _ => (1:ℝ)) := by
        funext x; simp [b, Set.indicator]
      rw [hbeq]
      change (∫ x, {x | overlap P x < a ∧ P.tau x < 0}.indicator (fun _ => (1:ℝ)) x ∂P.PX) = _
      rw [integral_indicator₀ hdel, setIntegral_one_eq_measureReal]
    have hR : (∫ x, (effectMagnitude P x + offsetG a P.logger x)*d x/4 - 2*b x - 2*k x ∂P.PX) =
        regularizedLoss P a π/4 - 2*biasFunctional P a := by
      rw [integral_sub
        (f := fun x => (effectMagnitude P x + offsetG a P.logger x)*d x/4 - 2*b x)
        (g := fun x => 2*k x) ((hLint.div_const 4).sub (hbint.const_mul 2)) (hkint.const_mul 2),
        integral_sub (f := fun x => (effectMagnitude P x + offsetG a P.logger x)*d x/4)
          (g := fun x => 2*b x) (hLint.div_const 4) (hbint.const_mul 2), integral_div,
        integral_const_mul, integral_const_mul, hL, hbMass]
      change regularizedLoss P a π/4 - 2*P.PX.real {x | overlap P x < a ∧ P.tau x < 0} -
          2*(∫ x, k x ∂P.PX) = regularizedLoss P a π/4 -
          2*(P.PX.real {x | overlap P x < a ∧ P.tau x < 0} + ∫ x, k x ∂P.PX)
      ring
    rw [hobj, hR] at hint
    exact hint
  · exact (zScore_moment_bounds P a ha hClass.wf hbounded
      hpositiveLogger hloggerSpace).2.1
  · exact (zScore_moment_bounds P a ha hClass.wf hbounded
      hpositiveLogger hloggerSpace).2.2

end CausalSmith.Stat.ScorethresholdOverlapRegret
