module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Basic
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.SharedDesignConstruction
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.ZeroInflated
public import Mathlib.MeasureTheory.Constructions.Pi

/-! The radius-indexed signed-score prior and its fixed-sample mixture.  The
dual pair is selected once for both signs from the same degree and interval. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open SharedDesignConstruction
open scoped BigOperators ENNReal


abbrev LatentCell := Bool × ℝ × ℝ × ℝ

def latentSign (z : LatentCell) : Bool := z.1
def latentIntensity (z : LatentCell) : ℝ := z.2.1
def latentPropensity (z : LatentCell) : ℝ := z.2.2.1
def latentScore (z : LatentCell) : ℝ := z.2.2.2

noncomputable def zeroLatent (h : Bool) : LatentCell := (h, 0, 1 / 4, 0)
noncomputable def referenceLatent : LatentCell := (false, 4, 1 / 2, 0)

noncomputable def dualSide (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) : Measure ℝ :=
  ∑ i : Fin (3 * J + 2),
    ENNReal.ofReal (2 * (if h then max (D.weights i) 0
      else max (-D.weights i) 0)) • Measure.dirac (D.nodes i)

noncomputable def tiltedSide (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) : Measure ℝ :=
  (∑ i : Fin (3 * J + 2),
    ENNReal.ofReal (2 * (if h then max (D.weights i) 0
      else max (-D.weights i) 0) * a / D.nodes i) •
        Measure.dirac (D.nodes i)) +
  ENNReal.ofReal (1 - ∑ i : Fin (3 * J + 2),
    2 * (if h then max (D.weights i) 0 else max (-D.weights i) 0) *
      a / D.nodes i) • Measure.dirac 0

noncomputable def latentFromIntensity (h : Bool) (a x : ℝ) : LatentCell :=
  if x = 0 then zeroLatent h
  else (h, x, 1 / 4 + a / (4 * x), x / (x + a))

-- @node: oneCellPrior
noncomputable def oneCellPrior (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) : Measure LatentCell :=
  ENNReal.ofReal (1 / (J : ℝ)) • Measure.dirac referenceLatent +
  ENNReal.ofReal (1 - 1 / (J : ℝ)) •
    ((1 / 2 : ENNReal) •
      Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h)) +
     (1 / 2 : ENNReal) •
      Measure.map (latentFromIntensity true a) (tiltedSide a J D h))

noncomputable def dualDegree (n : ℕ) (rho : ℝ) : ℕ :=
  max 2 (Nat.ceil (64 * Hrho n rho))

noncomputable def dualInterval (n : ℕ) (rho : ℝ) : ℝ :=
  1 / (100 * (dualDegree n rho : ℝ) ^ 2)

lemma radiusDual_exists (n : ℕ) (rho : ℝ) :
    Nonempty (FiniteMomentDual (rationalTarget (dualInterval n rho))
      (dualInterval n rho) 1 (3 * dualDegree n rho)) := by
  have hJ : 2 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_max_left _ _
  have hJr : (2 : ℝ) ≤ dualDegree n rho := by exact_mod_cast hJ
  have hden : 0 < (100 : ℝ) * (dualDegree n rho : ℝ) ^ 2 := by positivity
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    positivity
  have ha1 : dualInterval n rho < 1 := by
    unfold dualInterval
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_nonneg ((dualDegree n rho : ℝ) - 2)]
  apply exists_rationalFiniteMomentDual ha1
  simp only [Set.mem_Icc, not_and]
  intro h
  linarith

noncomputable def radiusDual (n : ℕ) (rho : ℝ) :
    FiniteMomentDual (rationalTarget (dualInterval n rho))
      (dualInterval n rho) 1 (3 * dualDegree n rho) :=
  Classical.choice (radiusDual_exists n rho)

noncomputable def latentProductPrior (n : ℕ) (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h : Bool) : Measure (Fin (n - 1) → LatentCell) :=
  -- @realizes h(hypothesis sign)
  Measure.pi (fun _ => oneCellPrior a J D h)
  -- @realizes Pi_{n,h}(product shared-design latent prior)

lemma latentProductPrior_eq_pi (n : ℕ) (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool) :
    latentProductPrior n a J D h =
      Measure.pi (fun _ : Fin (n - 1) => oneCellPrior a J D h) := by
  rfl

noncomputable def rawRareMass (n : ℕ) (J : ℕ) (kappa : ℝ)
    (theta : Fin (n - 1) → LatentCell)
    (k : Fin n) : ℝ :=
  if hk : k.val < n - 1 then
    kappa * (J : ℝ) / (2 * (n : ℝ)) * latentIntensity (theta ⟨k.val, hk⟩)
  else 1

noncomputable def rawMassTotal (n J : ℕ) (kappa : ℝ)
    (theta : Fin (n - 1) → LatentCell) : ℝ :=
  ∑ k : Fin n, rawRareMass n J kappa theta k

def LatentLawSpec (n : ℕ) (M rho kappa gamma : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell) (P : Law n) : Prop :=
  (∀ k, P.cellMass k =
    rawRareMass n J kappa theta k / rawMassTotal n J kappa theta) ∧
  (∀ k, P.propensity k =
    if hk : k.val < n - 1 then latentPropensity (theta ⟨k.val, hk⟩)
    else 1 / 2) ∧
  (∀ k, P.outcomeMean false k = 0) ∧
  (∀ k, P.outcomeMean true k =
    if hk : k.val < n - 1 then
      gamma * M * rho * latentScore (theta ⟨k.val, hk⟩) /
        4 * (if latentSign (theta ⟨k.val, hk⟩) then 1 else -1)
    else 0) ∧
  (∀ a k, P.outcomeLaw a k
    (({-(M / 2), M / 2} : Set ℝ)ᶜ) = 0) ∧
  P.fullLaw {z | z.y0 ∉ ({-(M / 2), M / 2} : Set ℝ) ∨
    z.y1 ∉ ({-(M / 2), M / 2} : Set ℝ)} = 0 ∧
  Consistency P ∧ ConditionalExchangeability P

lemma latentLaw_exists (n : ℕ) (M rho kappa gamma : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell)
    (hn : 0 < n) (hJ : 0 < J)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (he : ∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1) :
    ∃ P : Law n, LatentLawSpec n M rho kappa gamma J theta P := by
  classical
  have hraw (k : Fin n) : 0 ≤ rawRareMass n J kappa theta k := by
    unfold rawRareMass
    split_ifs with hk
    · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hJR : 0 ≤ (J : ℝ) := by positivity
      exact mul_nonneg (div_nonneg (mul_nonneg hkappa hJR) (by positivity))
        (hq ⟨k.val, hk⟩)
    · norm_num
  let reservoir : Fin n := ⟨n - 1, by omega⟩
  have hreservoir : rawRareMass n J kappa theta reservoir = 1 := by
    simp only [rawRareMass]
    split_ifs with hk
    · exact (Nat.lt_irrefl (n - 1) hk).elim
    · rfl
  have htotal : 0 < rawMassTotal n J kappa theta := by
    unfold rawMassTotal
    calc
      0 < rawRareMass n J kappa theta reservoir := by rw [hreservoir]; norm_num
      _ ≤ ∑ k : Fin n, rawRareMass n J kappa theta k :=
        Finset.single_le_sum (fun k _ => hraw k) (Finset.mem_univ reservoir)
  let p : Fin n → ℝ := fun k =>
    rawRareMass n J kappa theta k / rawMassTotal n J kappa theta
  let pi : Fin n → ℝ := fun k =>
    if hk : k.val < n - 1 then latentPropensity (theta ⟨k.val, hk⟩) else 1 / 2
  let mu : Bool → Fin n → ℝ := fun a k =>
    if a then
      if hk : k.val < n - 1 then
        1 / 2 + gamma * rho * latentScore (theta ⟨k.val, hk⟩) / 4 *
          (if latentSign (theta ⟨k.val, hk⟩) then 1 else -1)
      else 1 / 2
    else 1 / 2
  have hp : ∀ k, p k ∈ Icc (0 : ℝ) 1 := by
    intro k
    constructor
    · exact div_nonneg (hraw k) htotal.le
    · apply (div_le_one htotal).2
      unfold rawMassTotal
      exact Finset.single_le_sum (fun l _ => hraw l) (Finset.mem_univ k)
  have hp_sum : ∑ k, p k = 1 := by
    simp only [p, ← Finset.sum_div, rawMassTotal]
    exact div_self htotal.ne'
  have hpi : ∀ k, pi k ∈ Icc (0 : ℝ) 1 := by
    intro k
    simp only [pi]
    split_ifs with hk
    · constructor <;> linarith [(he ⟨k.val, hk⟩).1, (he ⟨k.val, hk⟩).2]
    · norm_num
  have hpi0 : ∀ k, 0 < pi k := by
    intro k
    simp only [pi]
    split_ifs with hk
    · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (he ⟨k.val, hk⟩).1
    · norm_num
  have hpi1 : ∀ k, pi k < 1 := by
    intro k
    simp only [pi]
    split_ifs with hk
    · exact lt_of_le_of_lt (he ⟨k.val, hk⟩).2 (by norm_num : (3 / 4 : ℝ) < 1)
    · norm_num
  have hmu : ∀ a k, mu a k ∈ Icc (0 : ℝ) 1 := by
    intro a k
    cases a
    · change (1 / 2 : ℝ) ∈ Icc 0 1
      norm_num
    · simp only [mu, if_true]
      split_ifs with hk hs
      all_goals try norm_num
      all_goals
        have hscore := hu ⟨k.val, hk⟩
        have hprod0 : 0 ≤ gamma * rho * latentScore (theta ⟨k.val, hk⟩) :=
          mul_nonneg (mul_nonneg hgamma.1 hrho.1) hscore.1
        have hgammaScore :
            gamma * latentScore (theta ⟨k.val, hk⟩) ≤ 1 := by
          calc
            gamma * latentScore (theta ⟨k.val, hk⟩) ≤
                1 * latentScore (theta ⟨k.val, hk⟩) :=
              mul_le_mul_of_nonneg_right hgamma.2 hscore.1
            _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hscore.2 (by norm_num)
            _ = 1 := one_mul 1
        have hprod2 : gamma * rho * latentScore (theta ⟨k.val, hk⟩) ≤ 2 := by
          calc
            gamma * rho * latentScore (theta ⟨k.val, hk⟩) =
                rho * (gamma * latentScore (theta ⟨k.val, hk⟩)) := by ring
            _ ≤ rho * 1 := mul_le_mul_of_nonneg_left hgammaScore hrho.1
            _ ≤ 2 := by simpa using hrho.2
        constructor <;> nlinarith
  let P : Law n :=
    prescribedFiniteRealLaw M p pi mu hp hpi hpi0 hpi1 hmu hp_sum
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [prescribedFiniteRealLaw_cellMass M p pi mu hp hpi hpi0 hpi1 hmu hp_sum]
  · intro k
    rfl
  · intro k
    simp [P, prescribedFiniteRealLaw, mu]
  · intro k
    simp only [P, prescribedFiniteRealLaw, mu, if_true]
    split_ifs <;> ring
  · intro a k
    exact prescribedFiniteRealLaw_support M p pi mu hp hpi hpi0 hpi1 hmu hp_sum a k
  · exact prescribedFiniteRealLaw_fullSupport M p pi mu hp hpi hpi0 hpi1 hmu hp_sum
  · exact prescribedFiniteRealLaw_consistency M p pi mu hp hpi hpi0 hpi1 hmu hp_sum
  · apply separate_exchangeability_of_joint
    exact prescribedFiniteRealLaw_exchangeability M p pi mu hp hpi hpi0 hpi1 hmu hp_sum

noncomputable def defaultLatentLaw (n : ℕ) (M rho kappa gamma : ℝ) (J : ℕ)
    (hn : 0 < n) (hJ : 0 < J)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1) : Law n :=
  Classical.choose (latentLaw_exists n M rho kappa gamma J (fun _ => zeroLatent false)
    hn hJ hM hrho hkappa hgamma
    (by intro k; simp [zeroLatent, latentIntensity])
    (by intro k; simp [zeroLatent, latentPropensity, Set.mem_Icc]; norm_num)
    (by intro k; simp [zeroLatent, latentScore, Set.mem_Icc]))

noncomputable def latentToLaw (n : ℕ) (M rho kappa gamma : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell)
    (hn : 0 < n) (hJ : 0 < J)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1) : Law n :=
  if hq : ∀ k, 0 ≤ latentIntensity (theta k) then
    if he : ∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4) then
      if hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1 then
        Classical.choose (latentLaw_exists n M rho kappa gamma J theta hn hJ hM hrho
          hkappa hgamma hq he hu)
      else defaultLatentLaw n M rho kappa gamma J hn hJ hM hrho hkappa hgamma
    else defaultLatentLaw n M rho kappa gamma J hn hJ hM hrho hkappa hgamma
  else defaultLatentLaw n M rho kappa gamma J hn hJ hM hrho hkappa hgamma

noncomputable def mixtureSampleLaw (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    Measure (Fin n → SampleObs n) :=
  (latentProductPrior n a J D h).bind
    (fun theta => DiscreteAteHeterogeneityFrontier.productLaw n
      (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma))
  -- @realizes overline Q_{n,h}(mixture of fixed-sample observed laws)

-- @node: def:shared-design-handle
noncomputable def sharedDesignPrior (n : ℕ) (M rho kappa gamma : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    Measure (Fin (n - 1) → LatentCell) ×
      Measure (Fin n → SampleObs n) :=
  let J := dualDegree n rho
  let a := dualInterval n rho
  let D := radiusDual n rho
  (latentProductPrior n a J D h,
    mixtureSampleLaw n M rho kappa gamma a J D h (by omega)
      (by change 0 < dualDegree n rho
          unfold dualDegree
          exact lt_of_lt_of_le (by decide) (le_max_left _ _))
      (by linarith) hrho hkappa hgamma)
  -- @realizes Pi_{n,h}(selected latent product prior)
  -- @realizes overline Q_{n,h}(common-reservoir normalized fixed-sample mixture)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
