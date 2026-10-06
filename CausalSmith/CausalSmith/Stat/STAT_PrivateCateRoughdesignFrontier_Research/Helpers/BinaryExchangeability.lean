module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.BinaryLaw
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.Independence
/-! Conditional exchangeability of the explicit independent Bernoulli construction. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign
open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

/-- Density coordinates are sent to full records by selecting the observed outcome. -/
-- @node: binaryRecordOfDensity
def binaryRecordOfDensity (z : DensityCoord Covariate) : Record :=
  (z.2.2, z.1, z.2.1, if z.1 then z.2.1.2 else z.2.1.1)

/-- The consistency selection map is measurable. [The displayed conclusion](goal) follows. -/
-- @node: measurable_binaryRecordOfDensity
@[fun_prop] lemma measurable_binaryRecordOfDensity : Measurable binaryRecordOfDensity := by
  unfold binaryRecordOfDensity
  have hy : Measurable (fun z : DensityCoord Covariate =>
      if z.1 then z.2.1.2 else z.2.1.1) :=
    Measurable.ite (measurable_fst (MeasurableSet.singleton true)) (by fun_prop) (by fun_prop)
  exact measurable_snd.snd.prodMk (measurable_fst.prodMk
    (measurable_snd.fst.prodMk hy))

/-- The paper's finite conditional law is the pushforward of the library's product density law.  [the theorem's stated inputs and assumptions](hyp:ha,hb,hc), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:a,b,c). -/
-- @node: binaryLaw_eq_map_densityLaw
lemma binaryLaw_eq_map_densityLaw (a b c : Covariate → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    binaryLaw a b c = (densityLaw volume a b c).map binaryRecordOfDensity := by
  classical
  have hbit (p : Covariate → ℝ) (hp : Measurable p)
      (f : DensityCoord Covariate → Bool) (hf : Measurable f) :
      Measurable (fun z : DensityCoord Covariate => bitMass (p z.2.2) (f z)) := by
    unfold bitMass
    exact Measurable.ite (hf (MeasurableSet.singleton true))
      (hp.comp (by fun_prop)) (measurable_const.sub (hp.comp (by fun_prop)))
  have hd : Measurable (density a b c) := by
    unfold density tripleMass
    exact ENNReal.measurable_ofReal.comp
      (((hbit a ha _ (by fun_prop)).mul (hbit b hb _ (by fun_prop))).mul
        (hbit c hc _ (by fun_prop)))
  ext s hs
  have hpre : MeasurableSet (binaryRecordOfDensity ⁻¹' s) := measurable_binaryRecordOfDensity hs
  rw [binaryLaw, Measure.bind_apply hs
    (measurable_binaryRecordLaw a b c ha hb hc).aemeasurable,
    Measure.map_apply measurable_binaryRecordOfDensity hs, densityLaw,
    withDensity_apply _ (measurable_binaryRecordOfDensity hs),
    ← lintegral_indicator (measurable_binaryRecordOfDensity hs), reference,
    lintegral_prod_symm' _ (hd.indicator (measurable_binaryRecordOfDensity hs))]
  simp only [lintegral_count, tsum_fintype]
  rw [lintegral_prod_symm' _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [lintegral_prod _ (by exact (measurable_of_finite _).aemeasurable)]
  simp only [lintegral_count, tsum_fintype, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Set.indicator_apply, density, tripleMass,
    bitMass, bernoulliMass, binaryRecordOfDensity, Set.mem_preimage,
    Bool.false_eq_true, if_false, if_true, Pi.one_apply, mul_ite, mul_zero, mul_one]
  ac_rfl

/-- Independent treatment and potential-outcome marks remain conditionally independent
when the observed consistency outcome is appended to the record.  [the theorem's stated inputs and assumptions](hyp:ha,hb,hc,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:a,b,c). -/
-- @node: binaryCausalLaw_exchangeability
lemma binaryCausalLaw_exchangeability (a b c : Covariate → ℝ)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hr : ∀ x, a x ∈ Icc 0 1 ∧ b x ∈ Icc 0 1 ∧ c x ∈ Icc 0 1) :
    Exchangeability (binaryCausalLaw a b c ha hb hc hr) := by
  letI : IsProbabilityMeasure (densityLaw volume a b c) :=
    densityLaw_probability volume a b c ha hb hc
      (fun x => (hr x).1) (fun x => (hr x).2.1) (fun x => (hr x).2.2)
  letI : IsProbabilityMeasure ((densityLaw volume a b c).map binaryRecordOfDensity) :=
    Measure.isProbabilityMeasure_map measurable_binaryRecordOfDensity.aemeasurable
  letI : IsProbabilityMeasure (binaryLaw a b c) := binaryLaw_probability a b c ha hb hc hr
  have hind : CondIndepFun (MeasurableSpace.comap X inferInstance)
      measurable_X.comap_le Ypot A
      ((densityLaw volume a b c).map binaryRecordOfDensity) := by
    apply Causalean.Mathlib.Probability.Independence.Conditional.condIndepFun_of_map
      measurable_binaryRecordOfDensity (by unfold Ypot; fun_prop)
      (by unfold A; fun_prop) measurable_X
    exact (densityLaw_condIndepFun volume a b c ha hb hc
      (fun x => (hr x).1) (fun x => (hr x).2.1) (fun x => (hr x).2.2)).symm
  simpa only [Exchangeability, binaryCausalLaw,
    ← binaryLaw_eq_map_densityLaw a b c ha hb hc] using hind

end CausalSmith.Stat.PrivateCateRoughdesign
