module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.DesignBridge
public import Causalean.Stat.Minimax.TotalVariation

/-!
# Independent false-edge OR transfer of full records

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The no-false-positive source retention for the calibrated target channel. -/
def channelSourceProb (q r : ℝ) : ℝ := if r < 1 then (q-r)/(1-r) else 0
/-- Independently OR each acquired coordinate with a fresh Bernoulli-r false-edge mark. -/
def channelRecordMap (o : Record V) (B : Acq V) : Record V :=
  (fun e => o.1 e || B e, o.2)
/-- The full-record transition preserves every assignment and real outcome coordinate. -/
def channelRecordKernel (r : ℝ) (o : Record V) : Measure (Record V) :=
  (Measure.pi (fun _ : OffDiag V => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw r)).map (channelRecordMap o)
/-- [The OR update is jointly Borel in the record and the fresh graph bits.](goal) -/
-- @node: channelRecordMap_measurable
@[fun_prop] lemma channelRecordMap_measurable :
    Measurable (fun x : Record V × Acq V => channelRecordMap x.1 x.2) := by
  unfold channelRecordMap
  fun_prop

/-- Given [the stated assumptions](hyp:hr), [For an admissible noise probability the record transition is a Borel kernel.](goal) -/
-- @node: channelRecordKernel_measurable
@[fun_prop] lemma channelRecordKernel_measurable (r : ℝ) (hr : r ∈ Set.Icc 0 1) :
    Measurable (channelRecordKernel (V := V) r) := by
  let := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability r hr
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm (o : Record V) : Measurable (channelRecordMap o) :=
    channelRecordMap_measurable.comp (measurable_const.prodMk measurable_id)
  simp only [channelRecordKernel, Measure.map_apply (hm _) hs]
  exact measurable_measure_prodMk_left (channelRecordMap_measurable hs)

/-- Given [the stated assumptions](hyp:hr), [The record transition has unit mass at every input.](goal) -/
-- @node: channelRecordKernel_probability
lemma channelRecordKernel_probability (r : ℝ) (hr : r ∈ Set.Icc 0 1) (o : Record V) :
    IsProbabilityMeasure (channelRecordKernel r o) := by
  let := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability r hr
  apply Measure.isProbabilityMeasure_map
  exact (channelRecordMap_measurable.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- Given [the stated assumptions](hyp:ha,hb), [OR of two independent Bernoulli bits has the union success probability.](goal) -/
-- @node: bernoulliLaw_or
lemma bernoulliLaw_or (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw a).prod
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw b)).map
      (fun x : Bool × Bool => x.1 || x.2) =
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (a+(1-a)*b) := by
  have hm : Measurable (fun x : Bool × Bool => x.1 || x.2) := by fun_prop
  apply Measure.ext_of_singleton
  intro x
  cases x <;>
    simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw,
      Measure.prod_add, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.dirac_prod_dirac, Measure.map_add _ _ hm, Measure.map_smul,
      Measure.map_dirac' hm]
  · rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hb.2)]
    congr 1
    ring
  · rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hb.2),
      ← ENNReal.ofReal_mul hb.1, ← ENNReal.ofReal_mul hb.1,
      ← ENNReal.ofReal_add (mul_nonneg hb.1 (sub_nonneg.mpr ha.2)) (mul_nonneg hb.1 ha.1),
      ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr hb.2) ha.1)
        (add_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr ha.2)) (mul_nonneg hb.1 ha.1))]
    congr 1
    ring

/-- Given [the stated assumptions](hyp:hqr), [The calibrated source probability is admissible and realizes the target success rate.](goal) -/
-- @node: channelSourceProb_spec
lemma channelSourceProb_spec (q r : ℝ) (hqr : ChannelDomain q r) :
    channelSourceProb q r ∈ Set.Icc 0 1 ∧
      channelSourceProb q r + (1-channelSourceProb q r)*r = q := by
  have hr1 : r ≤ 1 := hqr.2.1.trans hqr.2.2
  by_cases hr : r < 1
  · have hd : 0 < 1-r := by linarith
    simp only [channelSourceProb, if_pos hr]
    refine ⟨⟨div_nonneg (sub_nonneg.mpr hqr.2.1) hd.le,
      (div_le_one hd).mpr (by linarith [hqr.2.2])⟩, ?_⟩
    field_simp
    <;> ring
  · have hre : r = 1 := le_antisymm hr1 (le_of_not_gt hr)
    have hqe : q = 1 := le_antisymm hqr.2.2 (hre ▸ hqr.2.1)
    simp [channelSourceProb, hre, hqe]

/-- Given [the stated assumptions](hyp:ha,hb), [Coordinatewise OR preserves product independence and computes every success probability.](goal) -/
-- @node: pi_bernoulliLaw_or
lemma pi_bernoulliLaw_or {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc 0 1) (hb : ∀ i, b i ∈ Set.Icc 0 1) :
    ((Measure.pi (fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (a i))).prod
      (Measure.pi (fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (b i)))).map
      (fun x i => x.1 i || x.2 i) =
    Measure.pi (fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
      (a i+(1-a i)*b i)) := by
  letI := fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability (a i) (ha i)
  letI := fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability (b i) (hb i)
  rw [← (measurePreserving_arrowProdEquivProdArrow Bool Bool ι
    (fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (a i))
    (fun i => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (b i))).map_eq]
  rw [Measure.map_map (by fun_prop)
    (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool ι).measurable]
  change (Measure.pi (fun i =>
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (a i)).prod
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (b i)))).map
        (fun x i => (x i).1 || (x i).2) = _
  rw [Measure.pi_map_pi (f := fun (_ : ι) (x : Bool × Bool) => x.1 || x.2)
    (fun _ => (Measurable.of_discrete).aemeasurable)]
  congr 1
  funext i
  exact bernoulliLaw_or (a i) (b i) (ha i) (hb i)

/-- Given [the stated assumptions](hyp:hqr), [OR of the calibrated source graph and independent false bits gives the target graph law.](goal) -/
-- @node: acquisitionLaw_or
lemma acquisitionLaw_or (q r : ℝ) (hqr : ChannelDomain q r) (η : Schedule V) :
    ((acquisitionLaw η (channelSourceProb q r) 0).prod
      (Measure.pi (fun _ : OffDiag V =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw r))).map
      (fun x e => x.1 e || x.2 e) = acquisitionLaw η q r := by
  have hp := channelSourceProb_spec q r hqr
  unfold acquisitionLaw
  rw [pi_bernoulliLaw_or _ _ (fun e => by split_ifs; exact hp.1; norm_num)
    (fun _ => ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩)]
  congr 1
  funext e
  split_ifs
  · rw [hp.2]
  · simp

/-- Given [the stated assumptions](hyp:hqr), [Thinning at the source followed by independent OR realizes the target noisy record.](goal) -/
-- @node: channel_transfer_law
lemma channel_transfer_law (q r : ℝ) (hqr : ChannelDomain q r) (η : Schedule V) :
    ((noisyDesign (channelSourceProb q r) 0 η).map (recordOf η)).bind (channelRecordKernel r) =
      (noisyDesign q r η).map (recordOf η) := by
  have hr : r ∈ Set.Icc 0 1 := ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩
  have hp := (channelSourceProb_spec q r hqr).1
  letI := acquisitionLaw_probability (channelSourceProb q r) 0 ⟨by norm_num, hp.1, hp.2⟩ η
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability r hr
  have hm (o : Record V) : Measurable (channelRecordMap o) :=
    channelRecordMap_measurable.comp (measurable_const.prodMk measurable_id)
  have hOR : Measurable (fun x : Acq V × Acq V => fun e => x.1 e || x.2 e) := by fun_prop
  ext s hs
  have hk : Measurable (fun o : Record V => channelRecordKernel r o s) :=
    (Measure.measurable_coe hs).comp (channelRecordKernel_measurable r hr)
  rw [Measure.bind_apply hs (channelRecordKernel_measurable r hr).aemeasurable,
    lintegral_map hk
      (recordOf_measurable η),
    Measure.map_apply (recordOf_measurable η) hs]
  unfold noisyDesign
  rw [lintegral_prod (fun a => channelRecordKernel r (recordOf η a) s)
    (hk.comp (recordOf_measurable η)).aemeasurable,
    Measure.prod_apply ((recordOf_measurable η) hs)]
  apply lintegral_congr
  intro z
  have hz : MeasurableSet (Prod.mk z ⁻¹' recordOf η ⁻¹' s) :=
    (recordOf_measurable η |>.comp (measurable_const.prodMk measurable_id)) hs
  rw [← acquisitionLaw_or q r hqr η, Measure.map_apply hOR hz,
    Measure.prod_apply (hOR hz)]
  apply lintegral_congr
  intro H
  rw [channelRecordKernel, Measure.map_apply (hm _) hs]
  rfl
/-- Given [the stated assumptions](hyp:hr), [Appending the same independent graph-noise kernel contracts full-record total variation.](goal) -/
-- @node: channel_transfer_tv
lemma channel_transfer_tv (r : ℝ) (hr : r ∈ Set.Icc 0 1)
    (P Q : Measure (Record V)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    Causalean.Stat.tvDist (P.bind (channelRecordKernel r)) (Q.bind (channelRecordKernel r)) ≤
      Causalean.Stat.tvDist P Q := by
  let K : ProbabilityTheory.Kernel (Record V) (Record V) :=
    ⟨channelRecordKernel r, channelRecordKernel_measurable r hr⟩
  let : ProbabilityTheory.IsMarkovKernel K :=
    ⟨fun o => channelRecordKernel_probability r hr o⟩
  exact Causalean.Stat.tvDist_bind_le P Q K
/-- [At the all-one equality endpoint, the graph map produces every off-diagonal arrow.](goal) -/
-- @node: channel_endpoint_one
lemma channel_endpoint_one (o : Record V) :
    channelRecordKernel 1 o = Measure.dirac ((fun _ => true), o.2) := by
  have hb : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw 1 =
      Measure.dirac true := by
    simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw]
  have hp : Measure.pi (fun _ : OffDiag V => Measure.dirac true) =
      Measure.dirac (fun _ : OffDiag V => true) := by
    apply Measure.pi_eq
    intro s hs
    simp [Measure.dirac_apply, Set.indicator, Finset.prod_boole]
  unfold channelRecordKernel
  simp only [hb, hp]
  have hm : Measurable (channelRecordMap o) :=
    channelRecordMap_measurable.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_dirac' hm]
  simp [channelRecordMap]

end CausalSmith.Experimentation.NoisygraphTtePrecision
