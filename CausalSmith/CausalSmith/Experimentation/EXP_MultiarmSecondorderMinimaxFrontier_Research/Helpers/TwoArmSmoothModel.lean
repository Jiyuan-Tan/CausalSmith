import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmScheduleKernel
import Causalean.Stat.Limit.ObservationDependentVanTrees.Main
import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.DesignBased.ProductVariance

/-!
Paper-local analytic identities for the smooth two-arm prior.  These isolate the
bandwidth and observation-dependent posterior-target calculations needed by the
finite van Trees assembly.
-/

open scoped BigOperators
open Finset Set MeasureTheory

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: twoArmBandwidth
/-- The bandwidth used in the coarse two-arm converse. -/
noncomputable def twoArmBandwidth (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 3 : ℝ))

-- @node: twoArmBandwidth_pos
/-- [the population size is positive](hyp:hn), [A positive population size gives a positive converse bandwidth.](goal) -/
lemma twoArmBandwidth_pos {n : ℕ} (hn : 0 < n) : 0 < twoArmBandwidth n := by
  unfold twoArmBandwidth
  positivity

-- @node: twoArmBandwidth_le_half
/-- [the population size is positive](hyp:hn), [For `n ≥ 8`, the converse bandwidth is at most one half.](goal) -/
lemma twoArmBandwidth_le_half {n : ℕ} (hn : 8 ≤ n) :
    twoArmBandwidth n ≤ 1 / 2 := by
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by positivity
  let a := twoArmBandwidth n
  have ha_pos : 0 < a := twoArmBandwidth_pos hnpos
  have ha3 : a ^ 3 = (n : ℝ)⁻¹ := by
    dsimp [a, twoArmBandwidth]
    rw [← Real.rpow_mul_natCast hnR.le (-(1 / 3 : ℝ)) 3]
    norm_num
    exact Real.rpow_neg_one (n : ℝ)
  have hninv : (n : ℝ)⁻¹ ≤ (8 : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hnR (by norm_num)).2 (by exact_mod_cast hn)
  by_contra h
  have ha_gt : 1 / 2 < a := lt_of_not_ge h
  have ha_sq : (1 / 4 : ℝ) < a ^ 2 := by
    nlinarith [sq_nonneg (a - 1 / 2)]
  have ha_cube : (1 / 8 : ℝ) < a ^ 3 := by
    have ha_gt' : (2 : ℝ)⁻¹ < a := by simpa [one_div] using ha_gt
    calc
      (1 / 8 : ℝ) < a ^ 2 / 2 := by linarith
      _ < a ^ 2 * a := by
        exact mul_lt_mul_of_pos_left ha_gt' (sq_pos_of_pos ha_pos)
      _ = a ^ 3 := by ring
  norm_num at hninv
  rw [ha3] at ha_cube
  linarith

-- @node: twoArmBandwidth_sq
/-- [the population size is positive](hyp:hn), [Squaring the converse bandwidth gives the displayed `n^(-2/3)` term.](goal) -/
lemma twoArmBandwidth_sq {n : ℕ} (hn : 0 < n) :
    twoArmBandwidth n ^ 2 = (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hnR : 0 ≤ (n : ℝ) := by positivity
  unfold twoArmBandwidth
  rw [← Real.rpow_mul_natCast hnR (-(1 / 3 : ℝ)) 2]
  congr 1
  ring

-- @node: twoArmPosteriorWeight
/-- The coefficient of the centered observed score in the posterior target. -/
noncomputable def twoArmPosteriorWeight (a θ : ℝ) : ℝ :=
  (a - θ ^ 2) / (1 - θ ^ 2)

-- @node: twoArmPosteriorWeight_bounds
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [On the smooth-prior support, the posterior weight lies between zero and the bandwidth.](goal) -/
lemma twoArmPosteriorWeight_bounds {a θ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hθ : |θ| ≤ a / 2) :
    0 ≤ twoArmPosteriorWeight a θ ∧ twoArmPosteriorWeight a θ ≤ a := by
  have hθsq : θ ^ 2 ≤ a ^ 2 / 4 := by
    have ha2 : 0 ≤ a / 2 := by positivity
    have hh : |θ| ^ 2 ≤ (a / 2) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg θ) ha2).2 hθ
    rw [sq_abs] at hh
    nlinarith
  have ha_sq_le : a ^ 2 ≤ a := by nlinarith
  have hnum : 0 ≤ a - θ ^ 2 := by nlinarith
  have hden : 0 < 1 - θ ^ 2 := by nlinarith
  constructor
  · exact div_nonneg hnum hden.le
  · unfold twoArmPosteriorWeight
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg θ]

-- @node: twoArmScoreAverage
/-- The average signed score corresponding to a binary score vector. -/
noncomputable def twoArmScoreAverage {n : ℕ} (s : Unit n → Bool) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if s i then 1 else -1

-- @node: twoArmPosteriorTarget
/-- Posterior mean of the finite-population effect given the signed score vector. -/
noncomputable def twoArmPosteriorTarget {n : ℕ} (a θ : ℝ)
    (s : Unit n → Bool) : ℝ :=
  θ + twoArmPosteriorWeight a θ * (twoArmScoreAverage s - θ)

-- @node: twoArmPosteriorWeight_hasDerivAt
/-- [the parameter lies in the stated interior interval](hyp:hθ), [Derivative of the posterior-weight coefficient inside the regular Bernoulli region.](goal) -/
lemma twoArmPosteriorWeight_hasDerivAt {a θ : ℝ} (hθ : θ ^ 2 ≠ 1) :
    HasDerivAt (twoArmPosteriorWeight a)
      (2 * θ * (a - 1) / (1 - θ ^ 2) ^ 2) θ := by
  have hden : 1 - θ ^ 2 ≠ 0 := sub_ne_zero.mpr hθ.symm
  have h := ((hasDerivAt_const θ a).sub ((hasDerivAt_id θ).pow 2)).div
    ((hasDerivAt_const θ 1).sub ((hasDerivAt_id θ).pow 2)) hden
  have heq : (((fun _ : ℝ ↦ a) - id ^ 2) / ((fun _ : ℝ ↦ 1) - id ^ 2)) =
      twoArmPosteriorWeight a := by
    funext x
    rfl
  rw [heq] at h
  have hcoef :
      ((0 - 2 * θ) * (1 - θ ^ 2) - (a - θ ^ 2) * (0 - 2 * θ)) /
          (1 - θ ^ 2) ^ 2 =
        2 * θ * (a - 1) / (1 - θ ^ 2) ^ 2 := by ring
  simpa only [id_eq, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, hcoef] using h

-- @node: twoArmPosteriorTarget_hasDerivAt
/-- [the parameter lies in the stated interior interval](hyp:hθ), [Derivative identity for the observation-dependent posterior target.](goal) -/
lemma twoArmPosteriorTarget_hasDerivAt {n : ℕ} {a θ : ℝ}
    (s : Unit n → Bool) (hθ : θ ^ 2 ≠ 1) :
    HasDerivAt (fun t ↦ twoArmPosteriorTarget a t s)
      (1 - twoArmPosteriorWeight a θ +
        (2 * θ * (a - 1) / (1 - θ ^ 2) ^ 2) *
          (twoArmScoreAverage s - θ)) θ := by
  have h := (hasDerivAt_id θ).add
    ((twoArmPosteriorWeight_hasDerivAt (a := a) hθ).mul
      ((hasDerivAt_const θ (twoArmScoreAverage s)).sub (hasDerivAt_id θ)))
  change HasDerivAt (fun t ↦ twoArmPosteriorTarget a t s)
    (1 + ((2 * θ * (a - 1) / (1 - θ ^ 2) ^ 2) *
      (twoArmScoreAverage s - θ) + twoArmPosteriorWeight a θ * (0 - 1))) θ at h
  convert h using 1 <;> ring

-- @node: twoArmSmoothResponseTypeDesign
/-- One response type under the smooth two-arm prior at fixed scalar parameter.
The two nonzero-effect types have masses `(a±θ)/2`, while each zero-effect
type has mass `(1-a)/2`. -/
noncomputable def twoArmSmoothResponseTypeDesign (a θ : ℝ)
    (ha1 : a ≤ 1) (hθ : |θ| ≤ a) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Bool × Bool) where
  p t := if t.1 && !(t.2) then (a + θ) / 2
    else if !(t.1) && t.2 then (a - θ) / 2 else (1 - a) / 2
  p_nonneg t := by
    have hb := abs_le.mp hθ
    split_ifs <;> linarith
  p_sum := by
    rw [Fintype.sum_prod_type]
    simp
    ring

-- @node: twoArmObservedScore
/-- The signed Bernoulli score extracted from one response type at a fixed arm. -/
def twoArmObservedScore (A : Fin 2) (t : Bool × Bool) : Bool :=
  if A = 0 then t.1 else !t.2

-- @node: twoArmResponseEffect
/-- The signed unit-level treatment effect carried by a two-arm response type. -/
def twoArmResponseEffect (t : Bool × Bool) : ℝ :=
  (if t.1 then 1 else 0) - (if t.2 then 1 else 0)

-- @node: twoArmBernoulliUnitDesign
/-- One signed Bernoulli score with mean `θ`. -/
noncomputable def twoArmBernoulliUnitDesign (θ : ℝ) (hθ : |θ| ≤ 1) :
    Causalean.Experimentation.DesignBased.FiniteDesign Bool where
  p s := if s then (1 + θ) / 2 else (1 - θ) / 2
  p_nonneg s := by
    have hb := abs_le.mp hθ
    cases s <;> simp <;> linarith
  p_sum := by
    simp [Fintype.sum_bool]
    ring

-- @node: twoArmSmoothResponseType_effect_score_mass
/-- [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [The joint score/effect numerator under one smooth response type equals the Bernoulli score mass times its posterior mean effect, for either assigned arm.](goal) -/
lemma twoArmSmoothResponseType_effect_score_mass (a θ : ℝ) (ha1 : a ≤ 1)
    (hθ : |θ| ≤ a / 2) (A : Fin 2) (s : Bool) :
    ∑ t : Bool × Bool,
        (twoArmSmoothResponseTypeDesign a θ ha1
          (hθ.trans (by nlinarith [abs_nonneg θ]))).p t *
          (if twoArmObservedScore A t = s then twoArmResponseEffect t else 0) =
      (twoArmBernoulliUnitDesign θ
        (hθ.trans (by nlinarith [abs_nonneg θ, ha1]))).p s *
        (if s then (a + θ) / (1 + θ) else -(a - θ) / (1 - θ)) := by
  have hp : 1 + θ ≠ 0 := by
    have hlow := (abs_le.mp hθ).1
    linarith
  have hm : 1 - θ ≠ 0 := by
    have hupp := (abs_le.mp hθ).2
    linarith
  by_cases hA : A = 0
  · subst A
    cases s <;>
      norm_num [twoArmSmoothResponseTypeDesign, twoArmObservedScore,
        twoArmBernoulliUnitDesign, twoArmResponseEffect, Fintype.sum_prod_type] <;>
      field_simp [hp, hm] <;> ring
  · have hA1 : A = 1 := Fin.eq_one_of_ne_zero A hA
    subst A
    cases s <;>
      norm_num [twoArmSmoothResponseTypeDesign, twoArmObservedScore,
        twoArmBernoulliUnitDesign, twoArmResponseEffect, Fintype.sum_prod_type] <;>
      field_simp [hp, hm] <;> ring

-- @node: twoArmSmoothResponseType_score_mass
/-- [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [Pushing the smooth response-type law through either assigned arm gives the same Bernoulli score mass `(1±θ)/2`; this is the one-unit ancillarity identity used by the continuous-to-finite mixture bridge.](goal) -/
lemma twoArmSmoothResponseType_score_mass (a θ : ℝ) (ha1 : a ≤ 1)
    (hθ : |θ| ≤ a) (A : Fin 2) (s : Bool) :
    ((twoArmSmoothResponseTypeDesign a θ ha1 hθ).map
      (twoArmObservedScore A)).p s =
      (twoArmBernoulliUnitDesign θ (hθ.trans (by linarith))).p s := by
  by_cases hA : A = 0
  · subst A
    cases s <;> norm_num [twoArmSmoothResponseTypeDesign, twoArmObservedScore,
      Fintype.sum_prod_type,
      Causalean.Experimentation.DesignBased.FiniteDesign.map,
      twoArmBernoulliUnitDesign] <;> ring
  · have hA1 : A = 1 := Fin.eq_one_of_ne_zero A hA
    subst A
    cases s <;> norm_num [twoArmSmoothResponseTypeDesign, twoArmObservedScore,
      Fintype.sum_prod_type,
      Causalean.Experimentation.DesignBased.FiniteDesign.map,
      twoArmBernoulliUnitDesign] <;> ring

-- @node: responseVectorEffectTriple
/-- Effect-class counts induced by a vector of four two-arm response types. -/
def responseVectorEffectTriple {n : ℕ} (r : Unit n → Bool × Bool) : EffectTriple n := by
  let pp := (Finset.univ.filter fun i => (r i).1 && !((r i).2)).card
  let pm := (Finset.univ.filter fun i => !((r i).1) && (r i).2).card
  let pz := (Finset.univ.filter fun i => (r i).1 = (r i).2).card
  refine ⟨⟨⟨pp, ?_⟩, ⟨⟨pm, ?_⟩, ⟨pz, ?_⟩⟩⟩, ?_⟩
  · apply Nat.lt_succ_of_le
    simpa [pp] using Finset.card_le_card
      (Finset.filter_subset (fun i : Unit n => (r i).1 && !((r i).2)) Finset.univ)
  · apply Nat.lt_succ_of_le
    simpa [pm] using Finset.card_le_card
      (Finset.filter_subset (fun i : Unit n => !((r i).1) && (r i).2) Finset.univ)
  · apply Nat.lt_succ_of_le
    simpa [pz] using Finset.card_le_card
      (Finset.filter_subset (fun i : Unit n => (r i).1 = (r i).2) Finset.univ)
  · dsimp [pp, pm, pz]
    calc
      _ = (Finset.univ : Finset (Unit n)).card := by
        repeat rw [Finset.card_eq_sum_ones]
        simp_rw [Finset.sum_filter]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        cases (r i).1 <;> cases (r i).2 <;> simp
      _ = n := by simp

-- @node: effectTarget_responseVectorEffectTriple
/-- [The target of the response-vector effect counts is its positive-minus-negative effect count divided by the population size.](goal) -/
lemma effectTarget_responseVectorEffectTriple {n : ℕ} (r : Unit n → Bool × Bool) :
    effectTarget (responseVectorEffectTriple r) =
      (((((Finset.univ.filter fun i => (r i).1 && !((r i).2)).card : ℕ) : ℝ) -
        (((Finset.univ.filter fun i => !((r i).1) && (r i).2).card : ℕ) : ℝ)) / n) := by
  rfl

-- @node: twoArmClampedParameter
/-- Projection of a scalar parameter onto the response-design validity interval. -/
noncomputable def twoArmClampedParameter (a θ : ℝ) : ℝ :=
  max (-a / 2 : ℝ) (min θ (a / 2))

-- @node: twoArmClampedParameter_abs_le
/-- [the parameter lies in the stated interval](hyp:ha), [the two arm clamped parameter abs is at most property holds](goal). -/
lemma twoArmClampedParameter_abs_le {a θ : ℝ} (ha : 0 ≤ a) :
    |twoArmClampedParameter a θ| ≤ a / 2 := by
  rw [abs_le]
  unfold twoArmClampedParameter
  constructor
  · convert le_max_left (-a / 2 : ℝ) (min θ (a / 2)) using 1 <;> ring
  · exact max_le (by linarith) (min_le_right θ (a / 2))

-- @node: twoArmClampedParameter_eq
/-- [the parameter lies in the stated interior interval](hyp:hθ), [the two arm clamped parameter equals property holds](goal). -/
lemma twoArmClampedParameter_eq {a θ : ℝ} (hθ : |θ| ≤ a / 2) :
    twoArmClampedParameter a θ = θ := by
  rw [abs_le] at hθ
  unfold twoArmClampedParameter
  rw [min_eq_left hθ.2]
  exact max_eq_right (by linarith)

-- @node: twoArmSmoothEffectDesign
/-- The smooth scalar model's independent response vector, pushed to its
finite effect-class counts. -/
noncomputable def twoArmSmoothEffectDesign (n : ℕ) (a θ : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Causalean.Experimentation.DesignBased.FiniteDesign (EffectTriple n) :=
  (Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit n => twoArmSmoothResponseTypeDesign a
      (twoArmClampedParameter a θ) ha1
      ((twoArmClampedParameter_abs_le ha0).trans (by linarith)))).map
        responseVectorEffectTriple

-- @node: twoArmBernoulliVectorDesign
/-- Independent signed Bernoulli scores for the `n` labeled units. -/
noncomputable def twoArmBernoulliVectorDesign (n : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Unit n → Bool) :=
  Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit n ↦ twoArmBernoulliUnitDesign θ hθ)

-- @node: twoArmBernoulliUnit_signed_mean
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The one-unit signed score has expectation `θ`.](goal) -/
lemma twoArmBernoulliUnit_signed_mean (θ : ℝ) (hθ : |θ| ≤ 1) :
    (twoArmBernoulliUnitDesign θ hθ).E
      (fun s ↦ if s then 1 else -1) = θ := by
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  simp [twoArmBernoulliUnitDesign, Fintype.sum_bool]
  ring

-- @node: twoArmScoreAverage_mean
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interior interval](hyp:hθ), [The average signed score in the finite Bernoulli experiment has expectation `θ`.](goal) -/
lemma twoArmScoreAverage_mean {n : ℕ} (hn : 0 < n) (θ : ℝ) (hθ : |θ| ≤ 1) :
    (twoArmBernoulliVectorDesign n θ hθ).E twoArmScoreAverage = θ := by
  let D := fun _ : Unit n ↦ twoArmBernoulliUnitDesign θ hθ
  change (Causalean.Experimentation.DesignBased.prodDesign D).E
    (fun s ↦ (n : ℝ)⁻¹ * ∑ i, if s i then 1 else -1) = θ
  rw [(Causalean.Experimentation.DesignBased.prodDesign D).E_const_mul]
  rw [(Causalean.Experimentation.DesignBased.prodDesign D).E_sum]
  have hi (i : Unit n) :
      (Causalean.Experimentation.DesignBased.prodDesign D).E
        (fun s ↦ if s i then 1 else -1) = θ := by
    let g : Bool → ℝ := fun b ↦ if b then 1 else -1
    change (Causalean.Experimentation.DesignBased.prodDesign D).E
      (fun s ↦ g (s i)) = θ
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_prod_apply D i]
    exact twoArmBernoulliUnit_signed_mean θ hθ
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

-- @node: twoArmPosteriorTargetDeriv
/-- The supplied derivative field for the observation-dependent posterior target. -/
noncomputable def twoArmPosteriorTargetDeriv {n : ℕ} (a θ : ℝ)
    (s : Unit n → Bool) : ℝ :=
  1 - twoArmPosteriorWeight a θ +
    (2 * θ * (a - 1) / (1 - θ ^ 2) ^ 2) * (twoArmScoreAverage s - θ)

-- @node: twoArmPosteriorTargetDeriv_mean
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interior interval](hyp:hθ), [Averaging the target derivative removes its centered-score term.](goal) -/
lemma twoArmPosteriorTargetDeriv_mean {n : ℕ} (hn : 0 < n) (a θ : ℝ)
    (hθ : |θ| ≤ 1) :
    (twoArmBernoulliVectorDesign n θ hθ).E
        (twoArmPosteriorTargetDeriv a θ) = 1 - twoArmPosteriorWeight a θ := by
  let D := twoArmBernoulliVectorDesign n θ hθ
  unfold twoArmPosteriorTargetDeriv
  rw [D.E_add, D.E_sub, D.E_const, D.E_const (twoArmPosteriorWeight a θ)]
  rw [D.E_const_mul]
  rw [D.E_sub, twoArmScoreAverage_mean hn θ hθ, D.E_const θ]
  ring

-- @node: twoArmBernoulliLikelihood
/-- Product likelihood of the signed Bernoulli score vector. -/
noncomputable def twoArmBernoulliLikelihood {n : ℕ} (θ : ℝ)
    (s : Unit n → Bool) : ℝ :=
  ∏ i, if s i then (1 + θ) / 2 else (1 - θ) / 2

-- @node: twoArmBernoulliLikelihoodDeriv
/-- The product-rule derivative of the signed Bernoulli likelihood. -/
noncomputable def twoArmBernoulliLikelihoodDeriv {n : ℕ} (θ : ℝ)
    (s : Unit n → Bool) : ℝ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i,
      if s j then (1 + θ) / 2 else (1 - θ) / 2) *
        (if s i then (1 : ℝ) / 2 else -1 / 2)

-- @node: twoArmBernoulliLikelihood_eq_design
/-- [the parameter lies in the stated interior interval](hyp:hθ), [On the Bernoulli parameter space, the explicit likelihood is the product-design mass.](goal) -/
lemma twoArmBernoulliLikelihood_eq_design {n : ℕ} (θ : ℝ) (hθ : |θ| ≤ 1)
    (s : Unit n → Bool) :
    twoArmBernoulliLikelihood θ s = (twoArmBernoulliVectorDesign n θ hθ).p s := by
  simp only [twoArmBernoulliLikelihood, twoArmBernoulliVectorDesign,
    Causalean.Experimentation.DesignBased.prodDesign_p, twoArmBernoulliUnitDesign]

-- @node: twoArmBernoulliLikelihood_nonneg
/-- [the parameter lies in the stated interior interval](hyp:hθ), [Every signed Bernoulli vector has nonnegative mass for `|θ| ≤ 1`.](goal) -/
lemma twoArmBernoulliLikelihood_nonneg {n : ℕ} {θ : ℝ} (hθ : |θ| ≤ 1)
    (s : Unit n → Bool) : 0 ≤ twoArmBernoulliLikelihood θ s := by
  rw [twoArmBernoulliLikelihood_eq_design θ hθ]
  exact (twoArmBernoulliVectorDesign n θ hθ).p_nonneg s

-- @node: twoArmBernoulliLikelihood_sum
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The signed Bernoulli vector likelihood is normalized.](goal) -/
lemma twoArmBernoulliLikelihood_sum {n : ℕ} {θ : ℝ} (hθ : |θ| ≤ 1) :
    ∑ s : Unit n → Bool, twoArmBernoulliLikelihood θ s = 1 := by
  simp_rw [twoArmBernoulliLikelihood_eq_design θ hθ]
  exact (twoArmBernoulliVectorDesign n θ hθ).p_sum

-- @node: twoArmBernoulliLikelihood_hasDerivAt
/-- [The displayed product-rule field is the likelihood derivative.](goal) -/
lemma twoArmBernoulliLikelihood_hasDerivAt {n : ℕ} (θ : ℝ)
    (s : Unit n → Bool) :
    HasDerivAt (fun t => twoArmBernoulliLikelihood t s)
      (twoArmBernoulliLikelihoodDeriv θ s) θ := by
  let q : Unit n → ℝ → ℝ := fun i t =>
    if s i then (1 + t) / 2 else (1 - t) / 2
  let dq : Unit n → ℝ := fun i => if s i then 1 / 2 else -1 / 2
  have hq : ∀ i ∈ (Finset.univ : Finset (Unit n)),
      HasDerivAt (q i) (dq i) θ := by
    intro i hi
    by_cases hs : s i
    · simp only [q, dq, hs, if_true]
      simpa using ((hasDerivAt_const θ 1).add (hasDerivAt_id θ)).div_const 2
    · simp only [q, dq, hs, if_false]
      simpa using ((hasDerivAt_const θ 1).sub (hasDerivAt_id θ)).div_const 2
  have h := HasDerivAt.finset_prod hq
  unfold twoArmBernoulliLikelihood twoArmBernoulliLikelihoodDeriv
  rw [show (fun t ↦ ∏ i, if s i then (1 + t) / 2 else (1 - t) / 2) =
      ∏ i, q i by
    funext t
    simp [q]]
  simpa only [q, dq, smul_eq_mul] using h

-- @node: twoArmBernoulliRawScore
/-- The ordinary score of the signed Bernoulli product likelihood in its positive region. -/
noncomputable def twoArmBernoulliRawScore {n : ℕ} (θ : ℝ)
    (s : Unit n → Bool) : ℝ :=
  ∑ i, if s i then 1 / (1 + θ) else -1 / (1 - θ)

-- @node: twoArmBernoulliLikelihoodDeriv_eq_mul_score
/-- [the parameter lies in the stated interior interval](hyp:hθ), [In the regular Bernoulli region, likelihood derivative equals likelihood times score.](goal) -/
lemma twoArmBernoulliLikelihoodDeriv_eq_mul_score {n : ℕ} {θ : ℝ}
    (hθ : |θ| < 1) (s : Unit n → Bool) :
    twoArmBernoulliLikelihoodDeriv θ s =
      twoArmBernoulliLikelihood θ s * twoArmBernoulliRawScore θ s := by
  have hp : 0 < 1 + θ := by rw [abs_lt] at hθ; linarith
  have hm : 0 < 1 - θ := by rw [abs_lt] at hθ; linarith
  unfold twoArmBernoulliLikelihoodDeriv twoArmBernoulliLikelihood
    twoArmBernoulliRawScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.prod_erase_mul (Finset.univ : Finset (Unit n))
    (fun j ↦ if s j then (1 + θ) / 2 else (1 - θ) / 2) hi]
  by_cases hs : s i
  · simp [hs]
    field_simp [hp.ne']
  · simp [hs]
    field_simp [hm.ne']

-- @node: twoArmBernoulliUnit_rawScore_mean
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The one-coordinate Bernoulli likelihood score is centered.](goal) -/
lemma twoArmBernoulliUnit_rawScore_mean {θ : ℝ} (hθ : |θ| < 1) :
    (twoArmBernoulliUnitDesign θ hθ.le).E
      (fun s ↦ if s then 1 / (1 + θ) else -1 / (1 - θ)) = 0 := by
  have hp : 1 + θ ≠ 0 := by rw [abs_lt] at hθ; linarith
  have hm : 1 - θ ≠ 0 := by rw [abs_lt] at hθ; linarith
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  simp [twoArmBernoulliUnitDesign, Fintype.sum_bool]
  field_simp [hp, hm]
  ring

-- @node: twoArmBernoulliUnit_rawScore_var
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The one-coordinate Bernoulli likelihood score has information `1/(1-θ²)`.](goal) -/
lemma twoArmBernoulliUnit_rawScore_var {θ : ℝ} (hθ : |θ| < 1) :
    (twoArmBernoulliUnitDesign θ hθ.le).Var
      (fun s ↦ if s then 1 / (1 + θ) else -1 / (1 - θ)) =
        1 / (1 - θ ^ 2) := by
  have hp : 1 + θ ≠ 0 := by rw [abs_lt] at hθ; linarith
  have hm : 1 - θ ≠ 0 := by rw [abs_lt] at hθ; linarith
  have hden : 1 - θ ^ 2 ≠ 0 := by
    rw [show 1 - θ ^ 2 = (1 + θ) * (1 - θ) by ring]
    exact mul_ne_zero hp hm
  rw [Causalean.Experimentation.DesignBased.FiniteDesign.Var_eq,
    twoArmBernoulliUnit_rawScore_mean hθ]
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  simp [twoArmBernoulliUnitDesign, Fintype.sum_bool]
  field_simp [hp, hm, hden]
  ring

-- @node: twoArmBernoulliRawScore_sq_mean
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The independent `n`-coordinate score has Fisher information `n/(1-θ²)`.](goal) -/
lemma twoArmBernoulliRawScore_sq_mean {n : ℕ} {θ : ℝ} (hθ : |θ| < 1) :
    (twoArmBernoulliVectorDesign n θ hθ.le).E
        (fun s ↦ twoArmBernoulliRawScore θ s ^ 2) =
      (n : ℝ) / (1 - θ ^ 2) := by
  let D := fun _ : Unit n ↦ twoArmBernoulliUnitDesign θ hθ.le
  let g : Bool → ℝ := fun s ↦ if s then 1 / (1 + θ) else -1 / (1 - θ)
  have hmean : (Causalean.Experimentation.DesignBased.prodDesign D).E
      (fun s ↦ ∑ i, g (s i)) = 0 := by
    rw [(Causalean.Experimentation.DesignBased.prodDesign D).E_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_prod_apply]
    exact twoArmBernoulliUnit_rawScore_mean hθ
  have hvar := Causalean.Experimentation.DesignBased.FiniteDesign.Var_prod_linear_comb
    D (fun _ ↦ (1 : ℝ)) (fun _ ↦ g)
  have hvar' : (Causalean.Experimentation.DesignBased.prodDesign D).Var
      (fun s ↦ ∑ i, g (s i)) = ∑ i, (D i).Var g := by
    simpa only [one_mul, one_pow] using hvar
  dsimp [D, g] at hvar'
  simp_rw [twoArmBernoulliUnit_rawScore_var hθ] at hvar'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hvar'
  rw [Causalean.Experimentation.DesignBased.FiniteDesign.Var_eq, hmean] at hvar'
  norm_num at hvar'
  simpa [twoArmBernoulliVectorDesign, twoArmBernoulliRawScore, D, g, div_eq_mul_inv]
    using hvar'

-- @node: twoArmBernoulliLikelihood_pos
/-- [the parameter lies in the stated interior interval](hyp:hθ), [Every score vector has strictly positive likelihood in the open Bernoulli region.](goal) -/
lemma twoArmBernoulliLikelihood_pos {n : ℕ} {θ : ℝ} (hθ : |θ| < 1)
    (s : Unit n → Bool) : 0 < twoArmBernoulliLikelihood θ s := by
  rw [abs_lt] at hθ
  unfold twoArmBernoulliLikelihood
  apply Finset.prod_pos
  intro i hi
  split <;> linarith

-- @node: twoArmBernoulli_guardedScore_eq_rawScore
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The promoted guarded likelihood score agrees with the ordinary product score.](goal) -/
lemma twoArmBernoulli_guardedScore_eq_rawScore {n : ℕ} {θ : ℝ}
    (hθ : |θ| < 1) (s : Unit n → Bool) :
    Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
        twoArmBernoulliLikelihood twoArmBernoulliLikelihoodDeriv θ s =
      twoArmBernoulliRawScore θ s := by
  unfold Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
  rw [if_pos (twoArmBernoulliLikelihood_pos hθ s)]
  rw [twoArmBernoulliLikelihoodDeriv_eq_mul_score hθ]
  field_simp [(twoArmBernoulliLikelihood_pos hθ s).ne']

-- @node: twoArmBernoulli_fisherInformation
/-- [the parameter lies in the stated interior interval](hyp:hθ), [The exact finite counting-measure Fisher information is `n/(1-θ²)`.](goal) -/
lemma twoArmBernoulli_fisherInformation {n : ℕ} {θ : ℝ} (hθ : |θ| < 1) :
    Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation
        (X := Unit n → Bool) Measure.count (twoArmBernoulliLikelihood (n := n))
          (twoArmBernoulliLikelihoodDeriv (n := n)) θ =
      (n : ℝ) / (1 - θ ^ 2) := by
  rw [Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation_count_eq_sum]
  simp_rw [twoArmBernoulli_guardedScore_eq_rawScore hθ]
  rw [← twoArmBernoulliRawScore_sq_mean hθ]
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  apply Finset.sum_congr rfl
  intro s hs
  rw [← twoArmBernoulliLikelihood_eq_design θ hθ.le]

-- @node: twoArmPosteriorTargetDeriv_mean_lower
/-- [the population size is positive](hyp:hn), [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [On the smooth-prior support, the averaged posterior-target derivative is at least `1-a`.](goal) -/
lemma twoArmPosteriorTargetDeriv_mean_lower {n : ℕ} (hn : 0 < n)
    {a θ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hθ : |θ| ≤ a / 2) :
    1 - a ≤ (twoArmBernoulliVectorDesign n θ
      ((hθ.trans (by nlinarith : a / 2 ≤ 1)))).E
        (twoArmPosteriorTargetDeriv a θ) := by
  have hθone : |θ| ≤ 1 := hθ.trans (by nlinarith : a / 2 ≤ 1)
  rw [twoArmPosteriorTargetDeriv_mean hn a θ hθone]
  exact sub_le_sub_left (twoArmPosteriorWeight_bounds ha0 ha1 hθ).2 1

-- @node: twoArmBernoulli_fisherInformation_upper
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [the parameter lies in the stated interior interval](hyp:hθ), [On `|θ| ≤ a/2`, Bernoulli product information is bounded by its value at the edge of that interval.](goal) -/
lemma twoArmBernoulli_fisherInformation_upper {n : ℕ} {a θ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hθ : |θ| ≤ a / 2) :
    Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation
        (X := Unit n → Bool) Measure.count (twoArmBernoulliLikelihood (n := n))
          (twoArmBernoulliLikelihoodDeriv (n := n)) θ ≤
      (n : ℝ) / (1 - a ^ 2 / 4) := by
  have hθlt : |θ| < 1 := lt_of_le_of_lt hθ (by nlinarith)
  rw [twoArmBernoulli_fisherInformation hθlt]
  have hθsq : θ ^ 2 ≤ a ^ 2 / 4 := by
    have hs := sq_le_sq₀ (abs_nonneg θ) (by positivity : 0 ≤ a / 2) |>.2 hθ
    rw [sq_abs] at hs
    nlinarith
  have hdenθ : 0 < 1 - θ ^ 2 := by
    have := sq_lt_sq₀ (abs_nonneg θ) (by norm_num : (0 : ℝ) ≤ 1) |>.2 hθlt
    rw [sq_abs] at this
    nlinarith
  have hdena : 0 < 1 - a ^ 2 / 4 := by nlinarith [sq_nonneg a]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hdena
    (by nlinarith : 1 - a ^ 2 / 4 ≤ 1 - θ ^ 2)

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
