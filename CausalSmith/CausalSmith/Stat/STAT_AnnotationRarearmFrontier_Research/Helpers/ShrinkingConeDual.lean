module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.PriorHandle
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Reciprocal approximation gap on the shrinking overlap cone, using proved polynomial interfaces.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- [Under the stated inputs and conditions](hyp:L,hL,hB,heps',B,eps), The shrinking-cone reciprocal is continuous even at the zero endpoint.  This gives [the stated result](goal).-/
-- @node: cone_reciprocal_continuous
lemma cone_reciprocal_continuous (L : Nat) (B eps : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (heps' : eps ≤ 1 / 4) :
    ContinuousOn (fun v => (B / (100 * (L : Real) ^ 2)) /
      ((B / (100 * (L : Real) ^ 2)) + (1 - eps) * v)) (Set.Icc 0 B) := by
  have hLR : (0 : Real) < L := by exact_mod_cast (by omega : 0 < L)
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro v hv
  have : 0 < B / (100 * (L : Real) ^ 2) + (1 - eps) * v := by
    have : 0 ≤ (1 - eps) * v := mul_nonneg (by linarith) hv.1
    positivity
  exact this.ne'

/-- [Under the stated inputs and conditions](hyp:L,hL,hB,heps',Q,hQ,B,eps), Markov's derivative bound rules out error below one eighth on the shrinking cone.  This gives [the stated result](goal).-/
-- @node: cone_reciprocal_polynomial_gap
lemma cone_reciprocal_polynomial_gap (L : Nat) (B eps : Real)
    (hL : 2 ≤ L) (hB : 0 < B) (heps' : eps ≤ 1 / 4)
    (Q : Polynomial Real) (hQ : Q.natDegree ≤ L) :
    1 / 8 ≤ uniformApproxError (fun v => (B / (100 * (L : Real) ^ 2)) /
      ((B / (100 * (L : Real) ^ 2)) + (1 - eps) * v)) 0 B Q := by
  let alpha := B / (100 * (L : Real) ^ 2)
  let c := 1 - eps
  let g : Real → Real := fun v => alpha / (alpha + c * v)
  have hLR : (2 : Real) ≤ L := by exact_mod_cast hL
  have hsq : 0 < (L : Real) ^ 2 := by positivity
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hc : 3 / 4 ≤ c := by dsimp [c]; linarith
  have hcpos : 0 < c := by linarith
  have hg : ContinuousOn g (Set.Icc 0 B) :=
    cone_reciprocal_continuous L B eps hL hB heps'
  by_contra h
  have herr : uniformApproxError g 0 B Q < 1 / 8 := lt_of_not_ge h
  have hpoint (v : Real) (hv : v ∈ Set.Icc 0 B) : |g v - Q.eval v| < 1 / 8 :=
    lt_of_le_of_lt ((intervalSupNorm_le_iff (hg.sub Q.continuous.continuousOn)
      hB.le).mp (le_refl (uniformApproxError g 0 B Q)) v hv) herr
  have hgBounds (v : Real) (hv : v ∈ Set.Icc 0 B) : 0 ≤ g v ∧ g v ≤ 1 := by
    have hv' : 0 ≤ c * v := mul_nonneg hcpos.le hv.1
    have hden : 0 < alpha + c * v := by positivity
    dsimp [g]
    constructor
    · positivity
    · apply (div_le_iff₀ hden).2
      linarith
  have hnorm : intervalSupNorm (fun v => Q.eval v) 0 B ≤ 9 / 8 := by
    apply (intervalSupNorm_le_iff Q.continuous.continuousOn hB.le).mpr
    intro v hv
    have hp := hpoint v hv
    have hb := hgBounds v hv
    have htri := abs_add_le (Q.eval v - g v) (g v)
    rw [sub_add_cancel, abs_sub_comm, abs_of_nonneg hb.1] at htri
    linarith
  let z := alpha / c
  have hzpos : 0 < z := div_pos ha hcpos
  have hzB : z ≤ B := by
    apply (div_le_iff₀ hcpos).2
    have haeq : alpha * (100 * (L : Real) ^ 2) = B := by
      dsimp [alpha]
      field_simp
    have hs : (4 : Real) ≤ (L : Real) ^ 2 := by nlinarith
    nlinarith
  have hg0 : g 0 = 1 := by simp [g, ha.ne']
  have hgz : g z = 1 / 2 := by
    dsimp [g, z]
    field_simp
    ring
  have hp0 := hpoint 0 ⟨le_rfl, hB.le⟩
  have hpz := hpoint z ⟨hzpos.le, hzB⟩
  rw [hg0] at hp0
  rw [hgz] at hpz
  have hdrop : 1 / 4 < Q.eval 0 - Q.eval z := by
    have hp0' := (abs_lt.mp hp0).2
    have hpz' := (abs_lt.mp hpz).1
    linarith
  obtain ⟨v, hv, hslope⟩ := exists_deriv_eq_slope (fun x => Q.eval x) hzpos
    Q.continuous.continuousOn Q.differentiableOn
  have hMarkov := markov_derivative_Icc Q hB L hQ
  have hderiv : |Q.derivative.eval v| ≤ 9 * (L : Real) ^ 2 / (4 * B) := by
    have hp := (intervalSupNorm_le_iff Q.derivative.continuous.continuousOn hB.le).mp
      hMarkov v ⟨hv.1.le, hv.2.le.trans hzB⟩
    have hs := mul_le_mul_of_nonneg_left hnorm
      (by positivity : 0 ≤ 2 * (L : Real) ^ 2 / (B - 0))
    calc
      |Q.derivative.eval v| ≤ _ := hp
      _ ≤ (2 * (L : Real) ^ 2 / (B - 0)) * (9 / 8) := hs
      _ = _ := by ring
  rw [Polynomial.deriv, sub_zero] at hslope
  have hslope' : Q.derivative.eval v * z = Q.eval z - Q.eval 0 :=
    (eq_div_iff hzpos.ne').mp hslope
  have hprod := mul_le_mul_of_nonneg_right hderiv hzpos.le
  have hsmall : (9 * (L : Real) ^ 2 / (4 * B)) * z < 1 / 4 := by
    have hid : (9 * (L : Real) ^ 2 / (4 * B)) * z = 9 / (400 * c) := by
      dsimp [z, alpha]
      field_simp
      ring
    rw [hid]
    apply (div_lt_iff₀ (by positivity : 0 < 400 * c)).2
    linarith
  have habs : |Q.eval z - Q.eval 0| = |Q.derivative.eval v| * z := by
    rw [← hslope', abs_mul, abs_of_pos hzpos]
  have hlarge := le_abs_self (Q.eval 0 - Q.eval z)
  rw [abs_sub_comm] at hlarge
  rw [habs] at hlarge
  linarith

/--
[Under the stated inputs and conditions](hyp:L,hL,hB,heps,heps',B,eps), [The polynomial inequalities imply a variation-one finite signed moment certificate
with reciprocal gap at least one eighth](goal).
-/
-- @node: lem:shrinking-cone-dual
lemma shrinking_cone_dual (L : Nat) (B eps : Real) (hL : 2 ≤ L) (hB : 0 < B)
    (heps : 0 < eps) (heps' : eps ≤ 1 / 4) : Nonempty (ConeDual L B eps) := by
  let g : Real → Real := fun v => (B / (100 * (L : Real) ^ 2)) /
    ((B / (100 * (L : Real) ^ 2)) + (1 - eps) * v)
  have hg := cone_reciprocal_continuous L B eps hL hB heps'
  obtain ⟨Q, hQ, hbest⟩ := exists_bestPolynomial hB hg L
  have hgap : 1 / 8 ≤ bestUniformApproxError g 0 B L := by
    rw [← hbest]
    exact cone_reciprocal_polynomial_gap L B eps hL hB heps' Q hQ
  obtain ⟨nodes, w, hmono, hmem, habs, hmom, hvalue⟩ :=
    FinitePolynomialDuality g 0 B L hB hg
  exact ⟨⟨nodes, w, hmono, hmem, habs, hmom, hvalue.symm ▸ hgap⟩⟩

/-- [Under the stated inputs and conditions](hyp:eps,hn,heps,heps',n,m,d), The public affine schedule [admits the named shrinking-cone dual witness](goal). -/
lemma affine_schedule_dual (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    Nonempty (ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hS : 0 < (n : Real) * eps := mul_pos (by linarith) heps
  have hell : 1 < logScale n eps := by
    have h := Real.strictMonoOn_log (Real.exp_pos 1)
      (by positivity : 0 < Real.exp 1 + (n : Real) * eps) (by linarith)
    simpa only [Real.log_exp, logScale, labelScale] using h
  have hceil : 8 * logScale n eps ≤ ((affineTuning n m d eps).L : Real) :=
    Nat.le_ceil _
  have hL : 2 ≤ (affineTuning n m d eps).L := by
    have h : (2 : Real) ≤ (affineTuning n m d eps).L := by linarith
    exact_mod_cast h
  have hLpos : (0 : Real) < (affineTuning n m d eps).L := by
    exact_mod_cast (by omega : 0 < (affineTuning n m d eps).L)
  have hB : 0 < (affineTuning n m d eps).B := by
    change 0 < ((affineTuning n m d eps).L : Real) /
      (1000 * (128 * (n : Real) + 128 * ((n : Real) + m)))
    positivity
  exact shrinking_cone_dual _ _ _ hL hB heps heps'

-- @node: def:prior-handle
/-- The testing priors [use the displayed Dirac pair in the rare-label regime and choose
  the named dual witness only in the affine branch](goal). -/
noncomputable def affinePrior (hyp : Bool) (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4) :
    Measure (DiscreteLaw d) :=
  let S := labelScale n eps
  let x := (d : Real) / (((n : Real) + m) * eps * logScale n eps)
  if S < Real.exp 4096 ∨ x ^ 2 ≤ 1 / S then
    Measure.dirac (labelFloorLaw d eps (1 / (16 * Real.sqrt (max 1 S))) hyp hd
      (labelFloorAmplitude_scaled S))
  else
    let sigma := Classical.choice (affine_schedule_dual n m d eps hn heps heps')
    affineProductPrior hyp n m d eps hd sigma
  -- @realizes \Pi_0(piecewise prior at hyp=false; dual selected only in affine branch)
  -- @realizes \Pi_1(piecewise prior at hyp=true; dual selected only in affine branch)

end CausalSmith.Stat.AnnotationRarearmFrontier
