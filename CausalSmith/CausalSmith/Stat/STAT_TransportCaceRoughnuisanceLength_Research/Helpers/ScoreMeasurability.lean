module
public import Causalean.Stat.Inference.AffineInversion
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.IntegratedRemainder
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Measurability of the exact cubic score interval

Joint pilot measurability, measurable derivatives, and parameter integration
make the exact score measurable. An explicit affine witness characterizes the
nonempty inversion event, including its boundary, and justifies the fallback.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Given [the supplied inputs](hyp:c_f,C_f,n,A), [the stated result about measurable cubic estimator holds](goal). -/
@[fun_prop]
-- @node: measurable_cubicEstimator
lemma measurable_cubicEstimator (c_f C_f : ℝ) (n : ℕ) (A : Bool) :
    Measurable (fun ω : TwoSample n n => cubicEstimator c_f C_f ω A) := by
  have hd1 (i : Fin 7) : Measurable (fun v : Fin 7 → ℝ => dPhi1 A v i) := by
    unfold dPhi1
    fun_prop
  have hd2 (i j : Fin 7) : Measurable (fun v : Fin 7 → ℝ => dPhi2 A v i j) := by
    unfold dPhi2
    rw [iteratedFDeriv_succ_eq_comp_left]
    fun_prop
  have hd3 (i j k : Fin 7) : Measurable (fun v : Fin 7 → ℝ => dPhi3 A v i j k) := by
    unfold dPhi3
    rw [iteratedFDeriv_succ_eq_comp_left]
    fun_prop
  have hp : Measurable (fun ω : TwoSample n n => pilotIntegral c_f C_f ω A) := by
    have hj : Measurable (fun p : TwoSample n n × ℝ =>
        Phi A (pilot c_f C_f p.1 p.2)) := by
      unfold Phi
      fun_prop
    simp only [pilotIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hj.stronglyMeasurable.integral_prod_right.measurable
  have hi (i : Fin 7) : Measurable (fun ω : TwoSample n n => ∫ x in (0 : ℝ)..1,
      dPhi1 A (pilot c_f C_f ω x) i * pilot c_f C_f ω x i) := by
    have hj : Measurable (fun p : TwoSample n n × ℝ =>
        dPhi1 A (pilot c_f C_f p.1 p.2) i * pilot c_f C_f p.1 p.2 i) := by
      fun_prop
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hj.stronglyMeasurable.integral_prod_right.measurable
  unfold cubicEstimator linearTerm quadraticTerm cubicTerm residual
  dsimp only
  split_ifs <;> fun_prop

/-- The concrete affine inversion and its fallback have a measurable graph.  Under [the displayed assumptions and inputs](hyp:α,c_f,C_f,L,n,hα,hf,hF,hL), [the stated conclusion holds](goal). -/
-- @node: scoreInterval_measurableSet_graph
lemma scoreInterval_measurableSet_graph (α c_f C_f L : ℝ) (n : ℕ)
    (hα : 0 < α ∧ α < 1) (hf : 0 < c_f ∧ c_f < 1)
    (hF : 1 < C_f) (hL : 1 < L) :
    MeasurableSet {p : TwoSample n n × ℝ |
      p.2 ∈ scoreInterval α c_f C_f L p.1} := by
  classical
  have hnonempty : MeasurableSet {ω : TwoSample n n |
      (scoreInversion α c_f C_f L ω).Nonempty} := by
    simp only [scoreInversion, parameterSpace,
      Causalean.Stat.affineInterval_nonempty_iff]
    have ha := (measurable_cubicEstimator c_f C_f n true).norm
    have hb := (measurable_cubicEstimator c_f C_f n false).norm
    simpa only [Real.norm_eq_abs, Pi.add_apply, Set.inter_def, Set.mem_ofPred_eq] using (MeasurableSet.const (0 ≤
      2 * scoreRadius α c_f C_f L n)).inter
      (measurableSet_le ha (hb.add measurable_const))
  have hinversion : MeasurableSet {p : TwoSample n n × ℝ |
      p.2 ∈ scoreInversion α c_f C_f L p.1} := by
    unfold scoreInversion Causalean.Stat.affineInversionSet
    have hs : Measurable (fun p : TwoSample n n × ℝ =>
        |cubicEstimator c_f C_f p.1 true - p.2 * cubicEstimator c_f C_f p.1 false|) := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.mul_apply, Function.comp_apply] using
        (((measurable_cubicEstimator c_f C_f n true).comp measurable_fst).sub
          (measurable_snd.mul
            ((measurable_cubicEstimator c_f C_f n false).comp measurable_fst))).norm
    exact (measurableSet_Icc.preimage measurable_snd).inter
      (measurableSet_le hs measurable_const)
  by_cases hn : n < threshold
  · simp only [scoreInterval, if_pos hn]
    exact measurableSet_Icc.preimage measurable_snd
  · have heq : {p : TwoSample n n × ℝ |
        p.2 ∈ scoreInterval α c_f C_f L p.1} =
        ((Prod.fst ⁻¹' {ω | (scoreInversion α c_f C_f L ω).Nonempty}) ∩
          {p | p.2 ∈ scoreInversion α c_f C_f L p.1}) ∪
        ((Prod.fst ⁻¹' {ω | (scoreInversion α c_f C_f L ω).Nonempty})ᶜ ∩
          {p | p.2 = 0}) := by
      ext p
      simp only [Set.mem_ofPred_eq, scoreInterval, if_neg hn]
      split_ifs <;> simp_all
    rw [heq]
    exact ((hnonempty.preimage measurable_fst).inter hinversion).union
      ((hnonempty.preimage measurable_fst).compl.inter
        (measurableSet_eq_fun measurable_snd measurable_const))

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
