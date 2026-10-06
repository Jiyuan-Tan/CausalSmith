module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleIntegrability
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreExpectations
public import Mathlib.Probability.Independence.Integration

/-! Independent oracle blocks and their exact inner-product population mean. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The two public evaluation blocks use disjoint original records. [This is the stated conclusion](goal). -/
-- @node: oracle_evalBlock_disjoint
lemma oracle_evalBlock_disjoint (n : ℕ) :
    Disjoint (evalBlock n false) (evalBlock n true) := by
  rw [Finset.disjoint_left]
  intro i hi0 hi1
  simp only [evalBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    Bool.false_eq_true, if_false, if_true] at hi0 hi1
  omega

/-- Each oracle block has the same single-record population mean, including block size one. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_integral
lemma oracleBlockVec_integral (n : ℕ) (v : Params) (hn : 2 ≤ n) (f : Nuisance)
    (b : Bool) (law : ObservedLaw) :
    (∫ data, oracleBlockVec n v f b data ∂Measure.pi (fun _ : Fin n => law.P)) =
      ∫ o, ipwScore f (oracleT n v) o • centerVec (featureMap (oracleJ n v) (X o)) ∂law.P := by
  let h := fun o : Record => ipwScore f (oracleT n v) o •
    centerVec (featureMap (oracleJ n v) (X o))
  have hm : Measurable h := by
    dsimp [h]
    have hs : Measurable (fun o : Record => ipwScore f (oracleT n v) o) :=
      (measurable_ipwScore (oracleT n v)).comp (measurable_const.prodMk measurable_id)
    exact hs.smul ((continuous_centerVec _).measurable.comp
      ((measurable_featureMap _).comp (by unfold X; fun_prop)))
  have hL : MemLp h ∞ law.P :=
    (centeredFeature_memLp_top law.P _ X (by unfold X; fun_prop)).smul
      (ipwScore_memLp_top law.P f _ id measurable_id)
  have hi : Integrable h law.P := (memLp_one_iff_integrable).mp (hL.mono_exponent le_top)
  have his (i : Fin n) : Integrable (fun data : Dataset n => h (data i))
      (Measure.pi fun _ : Fin n => law.P) :=
    (measurePreserving_eval (fun _ : Fin n => law.P) i).integrable_comp_of_integrable hi
  change (∫ data, (blockSize n:ℝ)⁻¹ • ∑ i ∈ evalBlock n b, h (data i)
    ∂Measure.pi (fun _ : Fin n => law.P)) = ∫ o, h o ∂law.P
  rw [integral_smul, integral_finsetSum _ (fun i _ => his i)]
  simp_rw [score_single_coordinate_integral law h hm]
  rw [Finset.sum_const, evalBlock_card, ← Nat.cast_smul_eq_nsmul ℝ]
  have hs : (blockSize n:ℝ) ≠ 0 := by
    have : 0 < blockSize n := by unfold blockSize; omega
    exact_mod_cast this.ne'
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- The independent product sampling law makes the two oracle block vectors independent. [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_indep
lemma oracleBlockVec_indep (n : ℕ) (v : Params) (f : Nuisance) (law : ObservedLaw) :
    IndepFun (oracleBlockVec n v f false) (oracleBlockVec n v f true)
      (Measure.pi fun _ : Fin n => law.P) := by
  classical
  have hcoord : iIndepFun (fun i : Fin n => fun data : Dataset n => data i)
      (Measure.pi fun _ : Fin n => law.P) := by
    simpa using (iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id))
  have hb := hcoord.indepFun_finset (evalBlock n false) (evalBlock n true)
    (oracle_evalBlock_disjoint n) (fun i => measurable_pi_apply i)
  let H (b : Bool) (data : (evalBlock n b) → Record) : Vec (oracleJ n v) :=
    (blockSize n:ℝ)⁻¹ • ∑ i : (evalBlock n b),
      ipwScore f (oracleT n v) (data i) • centerVec (featureMap (oracleJ n v) (X (data i)))
  have hm (b : Bool) : Measurable (H b) := by
    dsimp [H]
    have hs (i : (evalBlock n b)) :
        Measurable (fun data : (evalBlock n b) → Record => ipwScore f (oracleT n v) (data i)) :=
      (measurable_ipwScore (oracleT n v)).comp
        (measurable_const.prodMk (measurable_pi_apply i))
    have hx (i : (evalBlock n b)) : Measurable (fun data : (evalBlock n b) → Record =>
        centerVec (featureMap (oracleJ n v) (X (data i)))) :=
      (continuous_centerVec _).measurable.comp
        ((measurable_featureMap _).comp (by unfold X; fun_prop))
    fun_prop
  have hc := hb.comp (hm false) (hm true)
  have he (b : Bool) : H b ∘ (fun data : Dataset n => fun i : (evalBlock n b) => data i.1) =
      oracleBlockVec n v f b := by
    funext data
    dsimp [H, Function.comp_def, oracleBlockVec]
    rw [Finset.sum_attach (evalBlock n b) (fun i : Fin n =>
      ipwScore f (oracleT n v) (data i) • centerVec (featureMap (oracleJ n v) (X (data i))))]

  simpa only [he false, he true] using hc

/-- The inner product of independent oracle blocks has exactly the squared population mean. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_inner_integral
lemma oracleBlockVec_inner_integral (n : ℕ) (v : Params) (hn : 2 ≤ n)
    (f : Nuisance) (law : ObservedLaw) :
    (∫ data, inner ℝ (oracleBlockVec n v f false data) (oracleBlockVec n v f true data)
      ∂Measure.pi (fun _ : Fin n => law.P)) =
      ‖∫ data, oracleBlockVec n v f false data ∂Measure.pi (fun _ : Fin n => law.P)‖^2 := by
  have hi (b : Bool) : Integrable (oracleBlockVec n v f b)
      (Measure.pi fun _ : Fin n => law.P) :=
    (memLp_one_iff_integrable).mp (oracleBlockVec_memLp n v f b _ 1)
  have he := (oracleBlockVec_indep n v f law).integral_bilin (hi false) (hi true) (innerSL ℝ)
  change (∫ data, inner ℝ (oracleBlockVec n v f false data) (oracleBlockVec n v f true data)
    ∂Measure.pi (fun _ : Fin n => law.P)) =
      inner ℝ (∫ data, oracleBlockVec n v f false data ∂Measure.pi (fun _ : Fin n => law.P))
        (∫ data, oracleBlockVec n v f true data ∂Measure.pi (fun _ : Fin n => law.P)) at he
  rw [he, oracleBlockVec_integral n v hn f false law, oracleBlockVec_integral n v hn f true law]
  exact real_inner_self_eq_norm_sq _

end CausalSmith.Stat.FinitepHomogeneityDensegamma

