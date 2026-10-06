module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerDenseRisk

/-! # Legal observed laws for the dense lower experiment

Construct the boundary-propensity law in (45) and identify its target with
(46), the target used by the proved dense concentration and testing bounds.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.Minimax.FuzzyHypotheses
open scoped BigOperators ENNReal

/-- Four observed atom masses for uniform cells, boundary propensity ε,
untreated mean one half and treated mean one half plus a θ. -/
-- @node: denseObservedMass
noncomputable def denseObservedMass {d : ℕ} (ε a : ℝ)
    (θ : Fin d → ℝ) (o : Obs d) : ℝ :=
  if o.2.1 then
    ε * (1 / 2 + if o.2.2 then a * θ o.1 else -(a * θ o.1)) / d
  else (1 - ε) / (2 * d)

/-- Legal amplitudes make every observed atom nonnegative. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseObservedMass_nonneg
lemma denseObservedMass_nonneg {d : ℕ} {ε a : ℝ} (hε : 0 ≤ ε)
    (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) (o : Obs d) :
    0 ≤ denseObservedMass ε a θ o := by
  have hat : |a * θ o.1| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (hθ o.1) ha).trans (by simpa using hahi)
  have hb := abs_le.mp hat
  unfold denseObservedMass
  split_ifs <;> apply div_nonneg <;>
    first | positivity | apply mul_nonneg hε <;> linarith | linarith

/-- The four atom masses sum to one over the uniform finite alphabet. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd), the [stated conclusion](goal) holds. -/
-- @node: denseObservedMass_sum
lemma denseObservedMass_sum {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (θ : Fin d → ℝ) : (∑ o : Obs d, denseObservedMass ε a θ o) = 1 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  calc
    _ = ∑ x : Fin d, (1 / (d : ℝ)) := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      simp [denseObservedMass]
      ring
    _ = 1 := by simp [hdR]

/-- The dense construction is an actual probability law, including the
endpoint amplitudes where a Bernoulli atom can vanish. -/
-- @node: denseObservedLaw
noncomputable def denseObservedLaw {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) : DiscreteLaw d :=
  ⟨PMF.ofFintype (fun o => ENNReal.ofReal (denseObservedMass ε a θ o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ =>
      denseObservedMass_nonneg hε.le hεhi ha hahi θ hθ o),
      denseObservedMass_sum hd]
    simp)⟩

/-- The probability-law construction preserves the specified real masses. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseObservedLaw_jointMass
lemma denseObservedLaw_jointMass {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) (x : Fin d) (b y : Bool) :
    jointMass (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ) x b y =
      denseObservedMass ε a θ (x, b, y) := by
  simp [jointMass, denseObservedLaw, ENNReal.toReal_ofReal
    (denseObservedMass_nonneg hε.le hεhi ha hahi θ hθ (x, b, y))]

/-- Uniform cells, boundary propensity and the two specified outcome means hold exactly; thus the dense construction belongs to the observed class. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseObservedLaw_parameters
lemma denseObservedLaw_parameters {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) :
    let P := denseObservedLaw hd ε a hε hεhi ha hahi θ hθ
    ObservedClass ε P ∧ ∀ x,
      cellMass P x = 1 / d ∧ propensity P x = ε ∧
      outcomeMean P false x = 1 / 2 ∧ outcomeMean P true x = 1 / 2 + a * θ x := by
  dsimp only
  let P := denseObservedLaw hd ε a hε hεhi ha hahi θ hθ
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hεne : ε ≠ 0 := hε.ne'
  have hone : 1 - ε ≠ 0 := by linarith
  have hcell (x : Fin d) : cellMass P x = 1 / d := by
    simp [P, cellMass, denseObservedLaw_jointMass, denseObservedMass]
    ring
  have harm (x : Fin d) : armMass P true x = ε / d := by
    simp [P, armMass, denseObservedLaw_jointMass, denseObservedMass]
    ring
  have hprop (x : Fin d) : propensity P x = ε := by
    rw [propensity, harm, hcell]
    field_simp
  refine ⟨⟨fun x _ => ⟨?_, ?_⟩⟩, fun x => ⟨hcell x, hprop x, ?_, ?_⟩⟩
  · rw [hprop]
  · rw [hprop]; linarith
  · simp [outcomeMean, armMass, denseObservedLaw_jointMass, denseObservedMass]
    field_simp
  · rw [outcomeMean, harm]
    simp [denseObservedLaw_jointMass, denseObservedMass]
    field_simp

/-- The legal dense observed target is precisely the target already used in the dense Bayes-risk bound, rather than an auxiliary surrogate. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseObservedLaw_value
lemma denseObservedLaw_value {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) :
    observedValue (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ) =
      densePriorTarget d a θ := by
  have hp := (denseObservedLaw_parameters hd ε a hε hεhi ha hahi θ hθ).2
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hmax (x : Fin d) : max (1 / 2 : ℝ) (1 / 2 + a * θ x) =
      1 / 2 + a * densePositivePart (θ x) := by
    rw [densePositivePart, min_eq_right
      (max_le ((le_abs_self _).trans (hθ x)) (by norm_num))]
    by_cases ht : 0 ≤ θ x
    · rw [max_eq_left ht, max_eq_right (by nlinarith)]
    · rw [max_eq_right (le_of_not_ge ht), max_eq_left (by nlinarith)]
      ring
  unfold observedValue
  simp_rw [(hp _).1, (hp _).2.2.1, (hp _).2.2.2, hmax]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [densePriorTarget, hdR]
  ring

/-- In the full observed Poisson experiment the treated intensities are exactly those in the proved dense likelihood calculation (47), and the untreated intensities are common to every parameter vector. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseObservedLaw_poissonMeans
lemma denseObservedLaw_poissonMeans {d : ℕ} (hd : 0 < d) (ε a B : ℝ) (n : ℕ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) (x : Fin d) (y : Bool) :
    B * n * jointMass (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ) x true y =
      denseTreatedMean (B * n * ε / d) a (θ x) (if y then 1 else 0) ∧
    B * n * jointMass (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ) x false y =
      B * n * (1 - ε) / (2 * d) := by
  rw [denseObservedLaw_jointMass, denseObservedLaw_jointMass]
  cases y <;> constructor <;> simp [denseObservedMass, denseTreatedMean] <;> ring

/-- The full dense Poisson experiment has total mean Bn, with no random normalizer penalty, as required in the transfer following (49). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hθ), the [stated conclusion](goal) holds. -/
-- @node: denseObservedLaw_poissonTotal
lemma denseObservedLaw_poissonTotal {d : ℕ} (hd : 0 < d) (ε a B : ℝ) (n : ℕ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) (hθ : ∀ x, |θ x| ≤ 1) :
    (∑ o : Obs d, B * n *
      jointMass (denseObservedLaw hd ε a hε hεhi ha hahi θ hθ) o.1 o.2.1 o.2.2) =
      B * n := by
  simp_rw [denseObservedLaw_jointMass]
  rw [← Finset.mul_sum]
  have hmass : (∑ o : Obs d, denseObservedMass ε a θ (o.1, o.2.1, o.2.2)) = 1 :=
    denseObservedMass_sum hd ε a θ
  rw [hmass, mul_one]

/-- Clip only outside the supported dense prior interval. -/
-- @node: denseClippedParameter
noncomputable def denseClippedParameter (t : ℝ) : ℝ := min 1 (max (-1) t)

/-- Every extended parameter gives a legal Bernoulli mean. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: denseClippedParameter_abs_le
lemma denseClippedParameter_abs_le (t : ℝ) : |denseClippedParameter t| ≤ 1 := by
  apply abs_le.mpr
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- Clipping leaves all prior-supported parameters unchanged. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:ht), the [stated conclusion](goal) holds. -/
-- @node: denseClippedParameter_eq
lemma denseClippedParameter_eq {t : ℝ} (ht : |t| ≤ 1) : denseClippedParameter t = t := by
  rw [denseClippedParameter, max_eq_right (abs_le.mp ht).1,
    min_eq_right (abs_le.mp ht).2]

/-- Clipping the negative tail does not change the bounded positive part. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: densePositivePart_clipped
lemma densePositivePart_clipped (t : ℝ) :
    densePositivePart (denseClippedParameter t) = densePositivePart t := by
  unfold densePositivePart denseClippedParameter
  by_cases hlo : t ≤ -1
  · rw [max_eq_left hlo]
    norm_num
    rw [max_eq_right (by linarith : t ≤ 0)]
    norm_num
  · rw [max_eq_right (le_of_lt (lt_of_not_ge hlo))]
    by_cases hhi : 1 ≤ t
    · rw [min_eq_left hhi, max_eq_left (by linarith : 0 ≤ t)]
      norm_num
      exact hhi
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hhi))]

/-- A legal dense observed law for every parameter vector; on the prior
support this is exactly (45). -/
-- @node: denseObservedModel
noncomputable def denseObservedModel {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) : ModelLaw d ε :=
  ⟨denseObservedLaw hd ε a hε hεhi ha hahi
      (fun x => denseClippedParameter (θ x)) (fun _ => denseClippedParameter_abs_le _),
    (denseObservedLaw_parameters hd ε a hε hεhi ha hahi
      (fun x => denseClippedParameter (θ x)) (fun _ => denseClippedParameter_abs_le _)).1⟩

/-- The all-parameter legal model has exactly the measurable target used in the testing theorem. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi), the [stated conclusion](goal) holds. -/
-- @node: denseObservedModel_value
lemma denseObservedModel_value {d : ℕ} (hd : 0 < d) (ε a : ℝ)
    (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2)
    (θ : Fin d → ℝ) :
    observedValue (denseObservedModel hd ε a hε hεhi ha hahi θ).1 =
      densePriorTarget d a θ := by
  rw [denseObservedModel, denseObservedLaw_value]
  simp only [densePriorTarget, densePositivePart_clipped]

/-- The dense testing bound applies to the actual legal observed value. The Fejér priors and their separation, target concentration, and Poisson mixture TV bound are all supplied by the proved dense lower theorem. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
-- @node: dense_observed_logDegree_bayesRisk_lower
lemma dense_observed_logDegree_bayesRisk_lower :
    ∃ (η C : ℝ) (D : ℕ), 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (d : ℕ) (r a ε : ℝ) (hd : 0 < d)
        (hε : 0 < ε) (hεhi : ε ≤ 1 / 2) (ha : 0 ≤ a) (hahi : a ≤ 1 / 2),
        D ≤ d → 0 < r → 0 < a →
        r * a ^ 2 ≤ η * lowerLogDegree C d →
        ∃ P : AbsMomentMatchedPriors (lowerLogDegree C d),
          ∀ est : (Fin d → (Fin 2 → ℕ)) → ℝ, Measurable est →
            ENNReal.ofReal ((5 / 2560000 : ℝ) * a ^ 2 /
              (lowerLogDegree C d : ℝ) ^ 2) ≤
              max (bayesSquaredRisk (productPrior d P.ν₀)
                    (denseProductPoissonKernel d r a)
                    (fun θ => observedValue (denseObservedModel hd ε a hε hεhi ha hahi θ).1) est)
                  (bayesSquaredRisk (productPrior d P.ν₁)
                    (denseProductPoissonKernel d r a)
                    (fun θ => observedValue (denseObservedModel hd ε a hε hεhi ha hahi θ).1) est) := by
  obtain ⟨η, C, D, hη, hC, hD, hbound⟩ := dense_logDegree_bayesRisk_lower
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro d r a ε hd hε hεhi ha hahi hcut hr hapos hband
  obtain ⟨P, hP⟩ := hbound d r a hcut hr hapos hahi hband
  refine ⟨P, ?_⟩
  intro est hest
  have htarget :
      (fun θ => observedValue (denseObservedModel hd ε a hε hεhi ha hahi θ).1) =
      densePriorTarget d a := by
    funext θ
    exact denseObservedModel_value hd ε a hε hεhi ha hahi θ
  rw [htarget]
  exact hP est hest

end CausalSmith.Stat.OptvalueVanishingoverlapRate
