module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Separation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.PalmSplit

/-!
The actual finite core/filler mixture for one rare cell in the raw Poisson
experiment, with singleton readback and exact signed outcome cancellation.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
open NormalizedFiniteSignedMomentCertificate
attribute [local instance] Classical.propDecidable

/-- The four counts retain both treated outcome marks, auxiliary treated counts,
and the combined control count. The filler has zero treated outcome mean. -/
-- @node: affineCellPoissonLaw
noncomputable def affineCellPoissonLaw {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (z : Latent L) :
    Measure MarkedPoissonObservation :=
  let alpha := B / (100 * (L : Real) ^ 2)
  let s1 := alpha + (1 - eps) * latentNode sigma z
  let s0 := (1 - eps) * (alpha / eps) + eps * latentNode sigma z
  let mean := match z with
    | none => 0
    | some i => (1 + (if hyp then 1 else -1) * latentPolar sigma (some i)) / 2
  ((poissonMeasure (Real.toNNReal (u * s1 * mean))).prod
    (poissonMeasure (Real.toNNReal (u * s1 * (1 - mean))))).prod
    ((poissonMeasure (Real.toNNReal (w * s1))).prod
      (poissonMeasure (Real.toNNReal ((u + w) * s0))))

/-- Each conditional raw cell law is a probability measure. -/
-- @node: affineCellPoissonLaw_isProbabilityMeasure
instance affineCellPoissonLaw_isProbabilityMeasure {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (z : Latent L) :
    IsProbabilityMeasure (affineCellPoissonLaw sigma u w hyp z) := by
  unfold affineCellPoissonLaw
  infer_instance

/-- Mix the conditional raw count law over the specified finite latent PMF. -/
-- @node: affineCellPoissonPredictive
noncomputable def affineCellPoissonPredictive {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) :
    Measure MarkedPoissonObservation :=
  ∑ z : Latent L, latentPMF sigma z • affineCellPoissonLaw sigma u w hyp z

/-- The finite latent mixture has total mass one. -/
-- @node: affineCellPoissonPredictive_isProbabilityMeasure
instance affineCellPoissonPredictive_isProbabilityMeasure {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) :
    IsProbabilityMeasure (affineCellPoissonPredictive sigma u w hyp) := by
  constructor
  simp only [affineCellPoissonPredictive, Measure.finsetSum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact (tsum_fintype _).symm.trans (latentPMF sigma).tsum_coe

/-- [Under the stated inputs and conditions](hyp:L,sigma,hyp,o,B,eps,u,w), Singleton masses of the finite mixture are the finite weighted sums of
conditional singleton masses.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_real_singleton
lemma affineCellPoissonPredictive_real_singleton {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (o : MarkedPoissonObservation) :
    (affineCellPoissonPredictive sigma u w hyp).real {o} =
      ∑ z : Latent L, (latentPMF sigma z).toReal *
        (affineCellPoissonLaw sigma u w hyp z).real {o} := by
  simp only [affineCellPoissonPredictive, measureReal_def, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun z _ => by
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul]

/-- [Under the stated inputs and conditions](hyp:L,sigma,B,eps,u,w), The filler is identical under the two hypotheses.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonLaw_filler_eq
lemma affineCellPoissonLaw_filler_eq {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) :
    affineCellPoissonLaw sigma u w true none =
      affineCellPoissonLaw sigma u w false none := by
  rfl

/-- [Under the stated inputs and conditions](hyp:L,sigma,i,first,B,eps,u,w,r,g,c), On core atoms, a nonzero treated count in one outcome channel has the
signed polar discrepancy times the three unmarked Poisson singleton masses.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonLaw_core_target_sub
lemma affineCellPoissonLaw_core_target_sub {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (i : Fin (L + 2))
    (first : Bool) (r g c : Nat) :
    (affineCellPoissonLaw sigma u w true (some i)).real
        {palmSplitTarget first r g c} -
      (affineCellPoissonLaw sigma u w false (some i)).real
        {palmSplitTarget first r g c} =
      (if first then latentPolar sigma (some i) else -latentPolar sigma (some i)) *
        (poissonMeasure (Real.toNNReal
          (u * (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i)))).real {r + 1} *
        (poissonMeasure (Real.toNNReal
          (w * (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i)))).real {g} *
        (poissonMeasure (Real.toNNReal ((u + w) *
          ((1 - eps) * (B / (100 * (L : Real) ^ 2) / eps) + eps * sigma.nodes i)))).real {c} := by
  cases first <;>
    simp only [affineCellPoissonLaw, latentNode, latentPolar, Bool.false_eq_true,
      if_false, if_true] <;> split_ifs <;>
    simp [palmSplitTarget, prod_real_singleton, poissonMeasure_real_singleton,
      zero_pow (by omega : 1 + r ≠ 0)] <;> ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,first,B,eps,u,w,r,g,c), Mixing the core atoms cancels the filler and restores the signed certificate
weights. This is the measure-level signed identity behind equation (6).  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_target_sub
lemma affineCellPoissonPredictive_target_sub {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : eps < 1)
    (first : Bool) (r g c : Nat) :
    (affineCellPoissonPredictive sigma u w true).real {palmSplitTarget first r g c} -
      (affineCellPoissonPredictive sigma u w false).real {palmSplitTarget first r g c} =
      (if first then 1 else -1) * ∑ i, sigma.weights i *
        ((B / (100 * (L : Real) ^ 2) /
          (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i)) *
        (poissonMeasure (Real.toNNReal
          (u * (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i)))).real {r + 1} *
        (poissonMeasure (Real.toNNReal
          (w * (B / (100 * (L : Real) ^ 2) + (1 - eps) * sigma.nodes i)))).real {g} *
        (poissonMeasure (Real.toNNReal ((u + w) *
          ((1 - eps) * (B / (100 * (L : Real) ^ 2) / eps) + eps * sigma.nodes i)))).real {c}) := by
  rw [affineCellPoissonPredictive_real_singleton, affineCellPoissonPredictive_real_singleton,
    ← Finset.sum_sub_distrib]
  simp only [Fintype.sum_option, affineCellPoissonLaw_filler_eq, sub_self, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_sub, affineCellPoissonLaw_core_target_sub,
    affine_latent_mass_readback sigma ha he]
  dsimp only [latentCoreMass]
  conv_rhs => rw [← affine_latent_polar_weight sigma i]
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,z,B,eps,u,w,g,c), With no complete treated observations, both core hypotheses have the same
likelihood, including the shared auxiliary and control counts.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonLaw_no_labeled_eq
lemma affineCellPoissonLaw_no_labeled_eq {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (z : Latent L) (g c : Nat) :
    (affineCellPoissonLaw sigma u w true z).real {((0, 0), (g, c))} =
      (affineCellPoissonLaw sigma u w false z).real {((0, 0), (g, c))} := by
  cases z with
  | none => rfl
  | some i =>
    simp only [affineCellPoissonLaw, latentNode, latentPolar, Bool.false_eq_true,
      if_false, if_true]
    split_ifs <;>
      simp [prod_real_singleton, poissonMeasure_real_singleton] <;> ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,B,eps,u,w,g,c), With zero treated complete counts, the predictive singleton masses agree.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_no_labeled_eq
lemma affineCellPoissonPredictive_no_labeled_eq {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (g c : Nat) :
    (affineCellPoissonPredictive sigma u w true).real {((0, 0), (g, c))} =
      (affineCellPoissonPredictive sigma u w false).real {((0, 0), (g, c))} := by
  simp only [affineCellPoissonPredictive_real_singleton,
    affineCellPoissonLaw_no_labeled_eq]

/-- [Under the stated inputs and conditions](hyp:L,sigma,hyp,z,B,eps,u,w,r,s,g,c), Deterministic marks forbid a positive count in both complete treated
outcome channels, under every core or filler draw.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonLaw_mixed_zero
lemma affineCellPoissonLaw_mixed_zero {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (z : Latent L)
    (r s g c : Nat) :
    (affineCellPoissonLaw sigma u w hyp z).real {((r + 1, s + 1), (g, c))} = 0 := by
  cases z with
  | none =>
    simp [affineCellPoissonLaw, prod_real_singleton, poissonMeasure_real_singleton,
      zero_pow (by omega : r + 1 ≠ 0)]
  | some i =>
    cases hyp <;>
      simp only [affineCellPoissonLaw, latentNode, latentPolar, Bool.false_eq_true,
        if_false, if_true] <;> split_ifs <;>
      simp [prod_real_singleton, poissonMeasure_real_singleton,
        zero_pow (by omega : r + 1 ≠ 0), zero_pow (by omega : s + 1 ≠ 0)]

/-- [Under the stated inputs and conditions](hyp:L,sigma,hyp,B,eps,u,w,r,s,g,c), Mixed positive complete treated outcome counts have zero predictive mass.  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_mixed_zero
lemma affineCellPoissonPredictive_mixed_zero {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real) (hyp : Bool) (r s g c : Nat) :
    (affineCellPoissonPredictive sigma u w hyp).real {((r + 1, s + 1), (g, c))} = 0 := by
  simp only [affineCellPoissonPredictive_real_singleton,
    affineCellPoissonLaw_mixed_zero, mul_zero, Finset.sum_const_zero]

/-- [Under the stated inputs and conditions](hyp:hb,he,he',hu,hw,hv,b0,eps,u,w,v,r,g,c), The three independent unmarked Poisson singleton masses give the
exponential times powers likelihood in equation (6).  This gives [the stated result](goal).-/
-- @node: affine_three_poisson_singleton_readback
lemma affine_three_poisson_singleton_readback (b0 eps u w v : Real)
    (hb : 0 ≤ b0) (he : 0 ≤ eps) (he' : eps ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hv : 0 ≤ v) (r g c : Nat) :
    (poissonMeasure (Real.toNNReal (u * (eps * b0 + (1 - eps) * v)))).real {r + 1} *
      (poissonMeasure (Real.toNNReal (w * (eps * b0 + (1 - eps) * v)))).real {g} *
      (poissonMeasure (Real.toNNReal ((u + w) * ((1 - eps) * b0 + eps * v)))).real {c} =
    Real.exp (-(u + w) * (b0 + v)) *
      (u * (eps * b0 + (1 - eps) * v)) ^ (r + 1) *
      (w * (eps * b0 + (1 - eps) * v)) ^ g *
      ((u + w) * ((1 - eps) * b0 + eps * v)) ^ c /
        (((r + 1).factorial : Real) * (g.factorial : Real) * (c.factorial : Real)) := by
  have hs1 : 0 ≤ eps * b0 + (1 - eps) * v := by positivity
  have hs0 : 0 ≤ (1 - eps) * b0 + eps * v := by positivity
  simp only [poissonMeasure_real_singleton,
    Real.coe_toNNReal _ (mul_nonneg hu hs1), Real.coe_toNNReal _ (mul_nonneg hw hs1),
    Real.coe_toNNReal _ (mul_nonneg (add_nonneg hu hw) hs0)]
  have hexp : Real.exp (-(u + w) * (b0 + v)) =
      Real.exp (-(u * (eps * b0 + (1 - eps) * v))) *
        Real.exp (-(w * (eps * b0 + (1 - eps) * v))) *
        Real.exp (-((u + w) * ((1 - eps) * b0 + eps * v))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- [Under the stated inputs and conditions](hyp:L,sigma,ha,he,he',hu,hw,first,B,eps,u,w,r,g,c), The actual predictive discrepancy at either nonzero deterministic outcome
pattern is exactly the signed count kernel from equation (6).  This gives [the stated result](goal).-/
-- @node: affineCellPoissonPredictive_equation_six
lemma affineCellPoissonPredictive_equation_six {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (u w : Real)
    (ha : 0 < B / (100 * (L : Real) ^ 2)) (he : 0 < eps) (he' : eps < 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (first : Bool) (r g c : Nat) :
    let b0 := B / (100 * (L : Real) ^ 2) / eps
    (affineCellPoissonPredictive sigma u w true).real {palmSplitTarget first r g c} -
      (affineCellPoissonPredictive sigma u w false).real {palmSplitTarget first r g c} =
      (if first then 1 else -1) * ∑ i, sigma.weights i *
        (Real.exp (-(u + w) * (b0 + sigma.nodes i)) *
          (u * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ (r + 1) *
          (w * (eps * b0 + (1 - eps) * sigma.nodes i)) ^ g *
          ((u + w) * ((1 - eps) * b0 + eps * sigma.nodes i)) ^ c /
            (((r + 1).factorial : Real) * (g.factorial : Real) * (c.factorial : Real)) *
          (eps * b0 / (eps * b0 + (1 - eps) * sigma.nodes i))) := by
  intro b0
  have hab : B / (100 * (L : Real) ^ 2) = eps * b0 := by
    dsimp [b0]
    field_simp
  rw [affineCellPoissonPredictive_target_sub sigma u w ha he']
  apply congrArg ((if first then 1 else -1) * ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [hab]
  simp only [mul_div_cancel_left₀ _ he.ne']
  have h := affine_three_poisson_singleton_readback b0 eps u w (sigma.nodes i)
    (div_pos ha he).le he.le he'.le hu hw (sigma.mem i).1 r g c
  linear_combination sigma.weights i *
    (eps * b0 / (eps * b0 + (1 - eps) * sigma.nodes i)) * h

end CausalSmith.Stat.AnnotationRarearmFrontier
