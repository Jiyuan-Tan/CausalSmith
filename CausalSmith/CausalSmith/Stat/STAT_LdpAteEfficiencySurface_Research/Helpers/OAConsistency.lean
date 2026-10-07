module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.LaplaceMoments
public import Causalean.Stat.Inference.VarianceEstimation
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.Sample
public import Mathlib.Probability.Independence.Integration

/-! # IID and moment adapters for the custom Laplace release -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter Causalean.Stat
open scoped BigOperators ENNReal

/-- For [the supplied quantities and conditions](hyp:p,j), the [oa trial value](goal) is the mathematical object specified below. -/
def oaTrialValue (p : ℝ) (j : Fin 4) : ℝ :=
  if j = 0 then 0 else if j = 1 then -(controlProb p)⁻¹
  else if j = 2 then 0 else p⁻¹

/-- Under the supplied quantities and conditions, the oa trial value mean input law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the oa Trial Value mean input Law](goal).

Under the stated assumptions, the oa Trial Value mean input Law. -/
lemma oaTrialValue_mean_inputLaw (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    ∫ j, oaTrialValue p j ∂(inputLaw θ p) = contrast θ := by
  have hpi (j : Fin 4) : 0 ≤ piTheta θ p j := by
    rcases hp with ⟨hp0, hp1⟩
    rcases hθ with ⟨h00, h01, h10, h11⟩
    fin_cases j <;> simp only [piTheta, controlProb] <;>
      positivity
  have hpi0 : piTheta θ p (0 : Fin 4) = controlProb p * (1 - θ 0) := rfl
  have hpi1 : piTheta θ p (1 : Fin 4) = controlProb p * θ 0 := rfl
  have hpi2 : piTheta θ p (2 : Fin 4) = p * (1 - θ 1) := rfl
  have hpi3 : piTheta θ p (3 : Fin 4) = p * θ 1 := rfl
  rw [inputLaw, integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (hpi _), smul_eq_mul]
    rw [integral_count]
    simp +decide [oaTrialValue, hpi0, hpi1, hpi2, hpi3, controlProb, contrast,
      Fin.sum_univ_succ]
    field_simp [ne_of_gt hp.1, ne_of_gt (sub_pos.mpr hp.2)]
    ring
  · exact (measurable_of_finite _).ennreal_ofReal
  · exact ae_of_all _ fun _ => ENNReal.ofReal_lt_top

/-- Under the supplied quantities and conditions, the oa trial value sq mean input law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the oa Trial Value sq mean input Law](goal).

Under the stated assumptions, the oa Trial Value sq mean input Law. -/
lemma oaTrialValue_sq_mean_inputLaw (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    ∫ j, (oaTrialValue p j) ^ 2 ∂(inputLaw θ p) =
      θ 1 / p + θ 0 / controlProb p := by
  have hpi (j : Fin 4) : 0 ≤ piTheta θ p j := by
    rcases hp with ⟨hp0, hp1⟩
    rcases hθ with ⟨h00, h01, h10, h11⟩
    fin_cases j <;> simp only [piTheta, controlProb] <;>
      positivity
  have hpi0 : piTheta θ p (0 : Fin 4) = controlProb p * (1 - θ 0) := rfl
  have hpi1 : piTheta θ p (1 : Fin 4) = controlProb p * θ 0 := rfl
  have hpi2 : piTheta θ p (2 : Fin 4) = p * (1 - θ 1) := rfl
  have hpi3 : piTheta θ p (3 : Fin 4) = p * θ 1 := rfl
  rw [inputLaw, integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (hpi _), smul_eq_mul]
    rw [integral_count]
    simp +decide [oaTrialValue, hpi0, hpi1, hpi2, hpi3, controlProb,
      Fin.sum_univ_succ]
    field_simp [ne_of_gt hp.1, ne_of_gt (sub_pos.mpr hp.2)]
    ring
  · exact (measurable_of_finite _).ennreal_ofReal
  · exact ae_of_all _ fun _ => ENNReal.ofReal_lt_top

/-- For the supplied quantities and conditions, the oa trial part is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The oa Trial Part](goal) is determined by [the displayed parameters](hyp:W,Y,p,i,ω). -/
def oaTrialPart {Ω : Type*} (W Y : ℕ → Ω → ℝ) (p : ℝ)
    (i : ℕ) (ω : Ω) : ℝ :=
  W i ω * Y i ω / p - (1 - W i ω) * Y i ω / controlProb p

/-- [the private record measurable of model assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,i), these specify the stated inputs. -/
lemma privateRecord_measurable_of_model {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y : ℕ → Ω → ℝ} {p : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ) (i : ℕ) :
    Measurable (privateRecord W Y i) := by
  have hW : Measurable (W i) := (hmodel.measurable i).snd.snd
  have hY0 : Measurable (Y0 i) := (hmodel.measurable i).fst
  have hY1 : Measurable (Y1 i) := (hmodel.measurable i).snd.fst
  have hY : Measurable (Y i) := by
    rw [show Y i = fun ω => W i ω * Y1 i ω +
        (1 - W i ω) * Y0 i ω by funext ω; exact hmodel.consistent i ω]
    exact (hW.mul hY1).add ((measurable_const.sub hW).mul hY0)
  unfold privateRecord
  exact Measurable.ite (hW (measurableSet_singleton 0))
    (Measurable.ite (hY (measurableSet_singleton 0)) measurable_const measurable_const)
    (Measurable.ite (hY (measurableSet_singleton 0)) measurable_const measurable_const)

/-- [the oa trial part ae eq record assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,i), these specify the stated inputs. -/
lemma oaTrialPart_ae_eq_record {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y : ℕ → Ω → ℝ} {p : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ) (i : ℕ) :
    oaTrialPart W Y p i =ᵐ[μ]
      fun ω => oaTrialValue p (privateRecord W Y i ω) := by
  filter_upwards [(hmodel.assigned i).1, hmodel.binary i] with ω hW hY
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW hY
  rcases hW with hW | hW
  · rcases hY.1 with hY0 | hY0 <;>
      simp [oaTrialPart, oaTrialValue, privateRecord, hmodel.consistent i ω,
        hW, hY0]
  · rcases hY.2 with hY1 | hY1 <;>
      simp [oaTrialPart, oaTrialValue, privateRecord, hmodel.consistent i ω,
        hW, hY1]

/-- [the oa trial part integral assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,i), these specify the stated inputs. -/
lemma oaTrialPart_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y : ℕ → Ω → ℝ} {p : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ) (i : ℕ) :
    ∫ ω, oaTrialPart W Y p i ω ∂μ = contrast θ := by
  rw [integral_congr_ae (oaTrialPart_ae_eq_record hmodel i)]
  rw [← integral_map (privateRecord_measurable_of_model hmodel i).aemeasurable
    (measurable_of_finite _).aestronglyMeasurable,
    recordLaw_eq_piTheta μ Y0 Y1 W Y p θ hmodel i]
  exact oaTrialValue_mean_inputLaw θ p hmodel.assignmentInterior hmodel.meansInterior

/-- [the oa trial part sq integral assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,i), these specify the stated inputs. -/
lemma oaTrialPart_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y : ℕ → Ω → ℝ} {p : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ) (i : ℕ) :
    ∫ ω, (oaTrialPart W Y p i ω) ^ 2 ∂μ =
      θ 1 / p + θ 0 / controlProb p := by
  have hsq : (fun ω => (oaTrialPart W Y p i ω) ^ 2) =ᵐ[μ]
      fun ω => (oaTrialValue p (privateRecord W Y i ω)) ^ 2 := by
    filter_upwards [oaTrialPart_ae_eq_record hmodel i] with ω hω
    rw [hω]
  rw [integral_congr_ae hsq]
  rw [← integral_map (privateRecord_measurable_of_model hmodel i).aemeasurable
    ((measurable_of_finite _).pow_const 2).aestronglyMeasurable,
    recordLaw_eq_piTheta μ Y0 Y1 W Y p θ hmodel i]
  exact oaTrialValue_sq_mean_inputLaw θ p hmodel.assignmentInterior hmodel.meansInterior

private lemma oaTrialValue_abs_le (p : ℝ) (j : Fin 4) :
    |oaTrialValue p j| ≤ |(controlProb p)⁻¹| + |p⁻¹| := by
  fin_cases j <;> simp [oaTrialValue] <;> positivity

/-- [the oa trial part integrable assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,i), these specify the stated inputs. -/
lemma oaTrialPart_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y : ℕ → Ω → ℝ} {p : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ) (i : ℕ) :
    Integrable (oaTrialPart W Y p i) μ := by
  have hm : Measurable (fun ω => oaTrialValue p (privateRecord W Y i ω)) :=
    (show Measurable (oaTrialValue p) from measurable_of_finite _).comp
      (privateRecord_measurable_of_model hmodel i)
  have hi : Integrable (fun ω => oaTrialValue p (privateRecord W Y i ω)) μ :=
    Integrable.of_bound hm.aestronglyMeasurable
      (|(controlProb p)⁻¹| + |p⁻¹|)
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using oaTrialValue_abs_le p (privateRecord W Y i ω))
  exact hi.congr (oaTrialPart_ae_eq_record hmodel i).symm

/-- [the oa trial part sq integrable assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,i), these specify the stated inputs. -/
lemma oaTrialPart_sq_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y : ℕ → Ω → ℝ} {p : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ) (i : ℕ) :
    Integrable (fun ω => (oaTrialPart W Y p i ω) ^ 2) μ := by
  have hm : Measurable (fun ω => (oaTrialValue p (privateRecord W Y i ω)) ^ 2) :=
    ((show Measurable (oaTrialValue p) from measurable_of_finite _).comp
      (privateRecord_measurable_of_model hmodel i)).pow_const 2
  have hi : Integrable (fun ω => (oaTrialValue p (privateRecord W Y i ω)) ^ 2) μ :=
    Integrable.of_bound hm.aestronglyMeasurable
      ((|(controlProb p)⁻¹| + |p⁻¹|) ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        have h := oaTrialValue_abs_le p (privateRecord W Y i ω)
        rw [Real.norm_eq_abs, abs_sq]
        have hs := mul_self_le_mul_self (abs_nonneg _) h
        nlinarith [sq_abs (oaTrialValue p (privateRecord W Y i ω))])
  have hsq : (fun ω => (oaTrialValue p (privateRecord W Y i ω)) ^ 2) =ᵐ[μ]
      fun ω => (oaTrialPart W Y p i ω) ^ 2 := by
    filter_upwards [oaTrialPart_ae_eq_record hmodel i] with ω hω
    rw [hω]
  exact hi.congr hsq

/-- the comparator noise integral assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hnoise,hε), [the comparator Noise integral](goal).

Under the stated assumptions, the comparator Noise integral. -/
lemma comparatorNoise_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W Y L : ℕ → Ω → ℝ} {p ε : ℝ}
    (hp : InteriorAssignment p)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    ∫ ω, L i ω ∂μ = 0 := by
  have hL := hnoise.aemeasurable hp hε i
  have hscale : 0 < sensitivity p / ε := by
    apply div_pos _ hε
    unfold sensitivity controlProb
    exact add_pos (inv_pos.mpr hp.1) (inv_pos.mpr (sub_pos.mpr hp.2))
  change (∫ ω, id (L i ω) ∂μ) = 0
  rw [← integral_map hL measurable_id.aestronglyMeasurable, hnoise.2.1 i]
  exact laplaceMeasure_integral_id (sensitivity p / ε) hscale

/-- the comparator noise sq integral assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hnoise,hε), [the comparator Noise sq integral](goal).

Under the stated assumptions, the comparator Noise sq integral. -/
lemma comparatorNoise_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W Y L : ℕ → Ω → ℝ} {p ε : ℝ}
    (hp : InteriorAssignment p)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    ∫ ω, (L i ω) ^ 2 ∂μ = 2 * (sensitivity p) ^ 2 / ε ^ 2 := by
  have hL := hnoise.aemeasurable hp hε i
  have hscale : 0 < sensitivity p / ε := by
    apply div_pos _ hε
    unfold sensitivity controlProb
    exact add_pos (inv_pos.mpr hp.1) (inv_pos.mpr (sub_pos.mpr hp.2))
  change (∫ ω, (id (L i ω)) ^ 2 ∂μ) = _
  rw [← integral_map hL (measurable_id.pow_const 2).aestronglyMeasurable,
    hnoise.2.1 i]
  simp only [comparatorNoiseLaw, id_eq]
  rw [laplaceMeasure_integral_sq (sensitivity p / ε) hscale]
  ring

/-- the comparator noise sq integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hnoise,hε), [the comparator Noise sq integrable](goal).

Under the stated assumptions, the comparator Noise sq integrable. -/
lemma comparatorNoise_sq_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W Y L : ℕ → Ω → ℝ} {p ε : ℝ}
    (hp : InteriorAssignment p)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    Integrable (fun ω => (L i ω) ^ 2) μ := by
  have hL := hnoise.aemeasurable hp hε i
  have hscale : 0 < sensitivity p / ε := by
    apply div_pos _ hε
    unfold sensitivity controlProb
    exact add_pos (inv_pos.mpr hp.1) (inv_pos.mpr (sub_pos.mpr hp.2))
  have hmap : Integrable (fun x : ℝ => x ^ 2) (μ.map (L i)) := by
    rw [hnoise.2.1 i]
    exact laplaceMeasure_integrable_sq (sensitivity p / ε) hscale
  exact (integrable_map_measure (measurable_id.pow_const 2).aestronglyMeasurable hL).mp hmap

/-- the comparator noise integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hnoise,hε), [the comparator Noise integrable](goal).

Under the stated assumptions, the comparator Noise integrable. -/
lemma comparatorNoise_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W Y L : ℕ → Ω → ℝ} {p ε : ℝ}
    (hp : InteriorAssignment p)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    Integrable (L i) μ := by
  have hL := hnoise.aemeasurable hp hε i
  exact ((memLp_two_iff_integrable_sq hL.aestronglyMeasurable).2
    (comparatorNoise_sq_integrable hp hnoise hε i)).integrable (by norm_num)

/-- [the oa trial part indep noise assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,hnoise,i), these specify the stated inputs. -/
lemma oaTrialPart_indep_noise {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (i : ℕ) :
    IndepFun (L i) (oaTrialPart W Y p i) μ := by
  have h := (hnoise.2.2 i).comp measurable_id
    (show Measurable (oaTrialValue p) from measurable_of_finite _)
  apply h.congr (Filter.Eventually.of_forall fun _ => rfl)
  simpa [Function.comp_def] using (oaTrialPart_ae_eq_record hmodel i).symm

/-- [the oa release value eq trial add assertion](goal) holds. For [the displayed quantities and conditions](hyp:W,Y,L,p,i), these specify the stated inputs. -/
lemma oaReleaseValue_eq_trial_add {Ω : Type*}
    (W Y L : ℕ → Ω → ℝ) (p : ℝ) (i : ℕ) (ω : Ω) :
    oaReleaseValue W Y L p i ω = oaTrialPart W Y p i ω + L i ω := rfl

/-- the oa release value integral assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Release Value integral](goal).

Under the stated assumptions, the oa Release Value integral. -/
lemma oaReleaseValue_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    ∫ ω, oaReleaseValue W Y L p i ω ∂μ = contrast θ := by
  rw [show (fun ω => oaReleaseValue W Y L p i ω) =
      fun ω => oaTrialPart W Y p i ω + L i ω by funext ω; rfl,
    integral_add (oaTrialPart_integrable hmodel i)
      (comparatorNoise_integrable hmodel.assignmentInterior hnoise hε i),
    oaTrialPart_integral hmodel i,
    comparatorNoise_integral hmodel.assignmentInterior hnoise hε i, add_zero]

/-- the oa release value sq integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Release Value sq integrable](goal).

Under the stated assumptions, the oa Release Value sq integrable. -/
lemma oaReleaseValue_sq_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    Integrable (fun ω => (oaReleaseValue W Y L p i ω) ^ 2) μ := by
  have hb : MemLp (oaTrialPart W Y p i) 2 μ :=
    (memLp_two_iff_integrable_sq
      (oaTrialPart_integrable hmodel i).aestronglyMeasurable).2
      (oaTrialPart_sq_integrable hmodel i)
  have hn : MemLp (L i) 2 μ :=
    (memLp_two_iff_integrable_sq
      (hnoise.aemeasurable hmodel.assignmentInterior hε i).aestronglyMeasurable).2
      (comparatorNoise_sq_integrable hmodel.assignmentInterior hnoise hε i)
  have ha := hb.add hn
  have heq : (oaTrialPart W Y p i + L i) =
      fun ω => oaReleaseValue W Y L p i ω := by funext ω; rfl
  rw [heq] at ha
  exact ha.integrable_sq

/-- the oa release value sq integral assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Release Value sq integral](goal).

Under the stated assumptions, the oa Release Value sq integral. -/
lemma oaReleaseValue_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    ∫ ω, (oaReleaseValue W Y L p i ω) ^ 2 ∂μ =
      θ 1 / p + θ 0 / controlProb p +
        2 * (sensitivity p) ^ 2 / ε ^ 2 := by
  have hb2 := oaTrialPart_sq_integrable hmodel i
  have hn2 := comparatorNoise_sq_integrable hmodel.assignmentInterior hnoise hε i
  have hb : MemLp (oaTrialPart W Y p i) 2 μ :=
    (memLp_two_iff_integrable_sq
      (oaTrialPart_integrable hmodel i).aestronglyMeasurable).2 hb2
  have hn : MemLp (L i) 2 μ :=
    (memLp_two_iff_integrable_sq
      (hnoise.aemeasurable hmodel.assignmentInterior hε i).aestronglyMeasurable).2 hn2
  have hcrossInt : Integrable (fun ω => L i ω * oaTrialPart W Y p i ω) μ := by
    change Integrable (L i * oaTrialPart W Y p i) μ
    exact hn.integrable_mul hb
  have hcross : (∫ ω, L i ω * oaTrialPart W Y p i ω ∂μ) = 0 := by
    rw [IndepFun.integral_fun_mul_eq_mul_integral
      (oaTrialPart_indep_noise hmodel hnoise i)
      (hnoise.aemeasurable hmodel.assignmentInterior hε i).aestronglyMeasurable
      (oaTrialPart_integrable hmodel i).aestronglyMeasurable,
      comparatorNoise_integral hmodel.assignmentInterior hnoise hε i, zero_mul]
  calc
    _ = ∫ ω, ((oaTrialPart W Y p i ω) ^ 2 +
          2 * (L i ω * oaTrialPart W Y p i ω)) + (L i ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [oaReleaseValue_eq_trial_add]
      ring
    _ = (∫ ω, ((oaTrialPart W Y p i ω) ^ 2 +
          2 * (L i ω * oaTrialPart W Y p i ω)) ∂μ) +
          ∫ ω, (L i ω) ^ 2 ∂μ :=
      integral_add (hb2.add (hcrossInt.const_mul 2)) hn2
    _ = ((∫ ω, (oaTrialPart W Y p i ω) ^ 2 ∂μ) +
          ∫ ω, 2 * (L i ω * oaTrialPart W Y p i ω) ∂μ) +
          ∫ ω, (L i ω) ^ 2 ∂μ := by
      rw [integral_add hb2 (hcrossInt.const_mul 2)]
    _ = (∫ ω, (oaTrialPart W Y p i ω) ^ 2 ∂μ) +
          2 * (∫ ω, L i ω * oaTrialPart W Y p i ω ∂μ) +
          ∫ ω, (L i ω) ^ 2 ∂μ := by rw [integral_const_mul]
    _ = _ := by
      rw [hcross, oaTrialPart_sq_integral hmodel i,
        comparatorNoise_sq_integral hmodel.assignmentInterior hnoise hε i]
      ring

/-- the oa release value centered sq integral assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Release Value centered sq integral](goal).

Under the stated assumptions, the oa Release Value centered sq integral. -/
lemma oaReleaseValue_centered_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    ∫ ω, (oaReleaseValue W Y L p i ω - contrast θ) ^ 2 ∂μ = VOA θ p ε := by
  have hA2 := oaReleaseValue_sq_integrable hmodel hnoise hε i
  have hA : Integrable (fun ω => oaReleaseValue W Y L p i ω) μ := by
    change Integrable (oaTrialPart W Y p i + L i) μ
    exact (oaTrialPart_integrable hmodel i).add
      (comparatorNoise_integrable hmodel.assignmentInterior hnoise hε i)
  calc
    _ = (∫ ω, (oaReleaseValue W Y L p i ω) ^ 2 ∂μ) -
        2 * contrast θ * (∫ ω, oaReleaseValue W Y L p i ω ∂μ) +
        (contrast θ) ^ 2 := by
      rw [show (fun ω => (oaReleaseValue W Y L p i ω - contrast θ) ^ 2) =
          fun ω => (oaReleaseValue W Y L p i ω) ^ 2 -
            2 * contrast θ * oaReleaseValue W Y L p i ω + (contrast θ) ^ 2 by
        funext ω; ring]
      calc
        _ = (∫ ω, (oaReleaseValue W Y L p i ω) ^ 2 -
              2 * contrast θ * oaReleaseValue W Y L p i ω ∂μ) +
              ∫ _ : Ω, (contrast θ) ^ 2 ∂μ :=
          integral_add (hA2.sub (hA.const_mul (2 * contrast θ))) (integrable_const _)
        _ = ((∫ ω, (oaReleaseValue W Y L p i ω) ^ 2 ∂μ) -
              ∫ ω, 2 * contrast θ * oaReleaseValue W Y L p i ω ∂μ) +
              ∫ _ : Ω, (contrast θ) ^ 2 ∂μ := by
          rw [integral_sub hA2 (hA.const_mul (2 * contrast θ))]
        _ = _ := by rw [integral_const_mul, integral_const]; simp
    _ = _ := by
      rw [oaReleaseValue_sq_integral hmodel hnoise hε i,
        oaReleaseValue_integral hmodel hnoise hε i]
      unfold VOA
      ring

/-- For [the supplied quantities and conditions](hyp:p,x), the [oa combined value](goal) is the mathematical object specified below. -/
def oaCombinedValue (p : ℝ) (x : PrivateAlphabet × ℝ) : ℝ :=
  oaTrialValue p x.1 + x.2

/-- Under [the supplied quantities and conditions](hyp:p), [the oa combined value measurable assertion](goal) holds. -/
lemma oaCombinedValue_measurable (p : ℝ) : Measurable (oaCombinedValue p) := by
  unfold oaCombinedValue
  exact ((show Measurable (oaTrialValue p) from measurable_of_finite _).comp
    measurable_fst).add measurable_snd

/-- [the oa release value ae eq combined assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,i), these specify the stated inputs. -/
lemma oaReleaseValue_ae_eq_combined {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ) (i : ℕ) :
    oaReleaseValue W Y L p i =ᵐ[μ] fun ω =>
      oaCombinedValue p (privateRecord W Y i ω, L i ω) := by
  filter_upwards [oaTrialPart_ae_eq_record hmodel i] with ω hω
  rw [oaReleaseValue_eq_trial_add, hω]
  rfl

/-- [the oa release value i indep assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmodel,hnoise), these specify the stated inputs. -/
lemma oaReleaseValue_iIndep {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) :
    iIndepFun (fun i => oaReleaseValue W Y L p i) μ := by
  have hcomp := hnoise.1.comp
    (fun _ : ℕ => oaCombinedValue p)
    (fun _ => oaCombinedValue_measurable p)
  exact hcomp.congr fun i => (oaReleaseValue_ae_eq_combined hmodel i).symm

/-- the oa combined ident distrib assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Combined ident Distrib](goal).

Under the stated assumptions, the oa Combined ident Distrib. -/
lemma oaCombined_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    IdentDistrib
      (fun ω => (privateRecord W Y 0 ω, L 0 ω))
      (fun ω => (privateRecord W Y i ω, L i ω)) μ μ := by
  letI : IsProbabilityMeasure μ := hmodel.iid.1.isProbabilityMeasure
  let B : ℕ → Ω → PrivateAlphabet := privateRecord W Y
  have hB (k : ℕ) : Measurable (B k) := privateRecord_measurable_of_model hmodel k
  have hL (k : ℕ) : AEMeasurable (L k) μ :=
    hnoise.aemeasurable hmodel.assignmentInterior hε k
  have hprod (k : ℕ) : μ.map (fun ω => (B k ω, L k ω)) =
      (μ.map (B k)).prod (μ.map (L k)) := by
    exact (indepFun_iff_map_prod_eq_prod_map_map (hB k).aemeasurable (hL k)).mp
      (hnoise.2.2 k).symm
  refine ⟨(hB 0).aemeasurable.prodMk (hL 0),
    (hB i).aemeasurable.prodMk (hL i), ?_⟩
  change μ.map (fun ω => (B 0 ω, L 0 ω)) = μ.map (fun ω => (B i ω, L i ω))
  rw [hprod 0, hprod i,
    show μ.map (B 0) = inputLaw θ p from
      recordLaw_eq_piTheta μ Y0 Y1 W Y p θ hmodel 0,
    show μ.map (B i) = inputLaw θ p from
      recordLaw_eq_piTheta μ Y0 Y1 W Y p θ hmodel i,
    hnoise.2.1 0, hnoise.2.1 i]

/-- the oa release value ident distrib assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Release Value ident Distrib](goal).

Under the stated assumptions, the oa Release Value ident Distrib. -/
lemma oaReleaseValue_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    IdentDistrib (oaReleaseValue W Y L p 0) (oaReleaseValue W Y L p i) μ μ := by
  have hc := (oaCombined_identDistrib hmodel hnoise hε i).comp
    (oaCombinedValue_measurable p)
  refine ⟨oaReleaseValue_aemeasurable hmodel hnoise hε 0,
    oaReleaseValue_aemeasurable hmodel hnoise hε i, ?_⟩
  rw [Measure.map_congr (oaReleaseValue_ae_eq_combined hmodel 0),
    Measure.map_congr (oaReleaseValue_ae_eq_combined hmodel i)]
  exact hc.map_eq

/-- the oa release clt assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Release clt](goal).

Under the stated assumptions, the oa Release clt. -/
lemma oaRelease_clt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) :
    Modes.TendstoInLaw (fun _ : ℕ => μ)
      (fun n ω => Real.sqrt n * (tauOA W Y L p n ω - contrast θ))
      atTop (gaussianMeasure 0 (VOA θ p ε)) := by
  let A : ℕ → Ω → ℝ := fun i => oaReleaseValue W Y L p i
  have hA (i : ℕ) : AEMeasurable (A i) μ :=
    oaReleaseValue_aemeasurable hmodel hnoise hε i
  have hAI : iIndepFun A μ := oaReleaseValue_iIndep hmodel hnoise
  have hAD (i : ℕ) : IdentDistrib (A 0) (A i) μ μ :=
    oaReleaseValue_identDistrib hmodel hnoise hε i
  let Am : ℕ → Ω → ℝ := fun i => (hA i).mk (A i)
  have hAmMeas (i : ℕ) : Measurable (Am i) := (hA i).measurable_mk
  have hAmAE (i : ℕ) : Am i =ᵐ[μ] A i := (hA i).ae_eq_mk.symm
  have hAmI : iIndepFun Am μ := hAI.congr fun i => (hAmAE i).symm
  have hAmD (i : ℕ) : IdentDistrib (Am 0) (Am i) μ μ := by
    refine ⟨(hAmMeas 0).aemeasurable, (hAmMeas i).aemeasurable, ?_⟩
    rw [Measure.map_congr (hAmAE 0), Measure.map_congr (hAmAE i)]
    exact (hAD i).map_eq
  let S : IIDSample Ω ℝ μ (μ.map (A 0)) := {
    Z := Am
    meas := hAmMeas
    indep := hAmI
    identDist := hAmD
    law := Measure.map_congr (hAmAE 0) }
  let ψ : ℝ → ℝ := id - fun _ => contrast θ
  letI : IsProbabilityMeasure (μ.map (A 0)) := Measure.isProbabilityMeasure_map (hA 0)
  have hmean : ∫ x, ψ x ∂(μ.map (A 0)) = 0 := by
    change (∫ x, x - contrast θ ∂(μ.map (A 0))) = 0
    rw [integral_map (hA 0)
      (show AEStronglyMeasurable (fun x : ℝ => x - contrast θ) (μ.map (A 0)) by
        fun_prop)]
    have hAint : Integrable (A 0) μ := by
      change Integrable (oaTrialPart W Y p 0 + L 0) μ
      exact (oaTrialPart_integrable hmodel 0).add
        (comparatorNoise_integrable hmodel.assignmentInterior hnoise hε 0)
    rw [integral_sub hAint (integrable_const _),
      oaReleaseValue_integral hmodel hnoise hε 0,
      integral_const]
    simp
  have hsq : Integrable (fun x => (ψ x) ^ 2) (μ.map (A 0)) := by
    change Integrable (fun x : ℝ => (x - contrast θ) ^ 2) (μ.map (A 0))
    rw [integrable_map_measure
      (show AEStronglyMeasurable (fun x : ℝ => (x - contrast θ) ^ 2)
          (μ.map (A 0)) by fun_prop) (hA 0)]
    have hrel2 := oaReleaseValue_sq_integrable hmodel hnoise hε 0
    have hrel : Integrable (fun ω => oaReleaseValue W Y L p 0 ω) μ := by
      change Integrable (oaTrialPart W Y p 0 + L 0) μ
      exact (oaTrialPart_integrable hmodel 0).add
        (comparatorNoise_integrable hmodel.assignmentInterior hnoise hε 0)
    have hexpand : Integrable (fun ω =>
        (oaReleaseValue W Y L p 0 ω) ^ 2 -
          2 * contrast θ * oaReleaseValue W Y L p 0 ω + (contrast θ) ^ 2) μ :=
      (hrel2.sub (hrel.const_mul (2 * contrast θ))).add (integrable_const _)
    exact hexpand.congr (Filter.Eventually.of_forall fun ω => by
      change _ = (oaReleaseValue W Y L p 0 ω - contrast θ) ^ 2
      ring)
  have hvar : ∫ x, (ψ x) ^ 2 ∂(μ.map (A 0)) = VOA θ p ε := by
    change (∫ x : ℝ, (x - contrast θ) ^ 2 ∂(μ.map (A 0))) = VOA θ p ε
    rw [integral_map (hA 0)
      (show AEStronglyMeasurable (fun x : ℝ => (x - contrast θ) ^ 2)
          (μ.map (A 0)) by fun_prop)]
    simpa only [Function.comp_apply, A] using
      oaReleaseValue_centered_sq_integral hmodel hnoise hε 0
  have hclt0 := S.clt_normalized_sum (measurable_id.sub measurable_const) hmean hsq
  have hclt : Modes.TendstoInLaw (fun _ : ℕ => μ)
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m)) atTop
      (gaussianMeasure 0 (VOA θ p ε)) := by
    change Modes.TendstoInLaw (fun _ : ℕ => μ)
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m)) atTop
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂(μ.map (A 0)))) at hclt0
    rw [hvar] at hclt0
    exact hclt0
  have htargetMeas (n : ℕ) : AEMeasurable
      (fun ω => Real.sqrt n * (tauOA W Y L p n ω - contrast θ)) μ := by
    have hsum (s : Finset ℕ) : AEMeasurable (fun ω => ∑ i ∈ s, A i ω) μ := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          have heq : (fun ω => ∑ i ∈ insert a s, A i ω) =
              A a + fun ω => ∑ i ∈ s, A i ω := by
            funext ω
            rw [Finset.sum_insert ha]
            rfl
          rw [heq]
          change AEMeasurable (A a + fun ω => ∑ i ∈ s, A i ω) μ
          exact (hA a).add ih
    unfold tauOA
    exact aemeasurable_const.mul
      ((aemeasurable_const.mul (hsum (Finset.range n))).sub aemeasurable_const)
  have hnormMeas (n : ℕ) : AEMeasurable
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n) μ := by
    exact ((Finset.measurable_sum _ fun i _ =>
      (measurable_id.sub measurable_const).comp (S.meas i)).const_mul _).aemeasurable
  apply Modes.TendstoInLaw.congr_ae hclt htargetMeas
  filter_upwards with n
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, S.Z i ω = A i ω := by
    induction Finset.range n using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        filter_upwards [hAmAE a, ih] with ω haω hsω
        intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact haω
        · exact hsω i hi
  filter_upwards [hall] with ω hω
  unfold IsAsymLinear.normalizedSum tauOA ψ
  simp only [Finset.card_range, Pi.sub_apply, id_eq]
  change (Real.sqrt n)⁻¹ *
      (∑ i ∈ Finset.range n, (S.Z i ω - contrast θ)) =
    Real.sqrt n * ((n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, oaReleaseValue W Y L p i ω - contrast θ)
  have hsumEq : (∑ i ∈ Finset.range n, (S.Z i ω - contrast θ)) =
      ∑ i ∈ Finset.range n, (A i ω - contrast θ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hω i hi]
  rw [hsumEq]
  simp only [A]
  rcases n with _ | n
  · simp
  · have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hspos : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.2 hn
    have hrsq : (Real.sqrt (n + 1 : ℕ)) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
      Real.sq_sqrt hn.le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
    field_simp [ne_of_gt hspos, ne_of_gt hn]
    rw [hrsq]

/-- the oa variance consistency assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Variance consistency](goal).

Under the stated assumptions, the oa Variance consistency. -/
lemma oaVariance_consistency {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y0 Y1 W Y L : ℕ → Ω → ℝ} {p ε : ℝ} {θ : TrialParameter}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μ {ω | δ < |VhatOA W Y L p n ω - VOA θ p ε|})
        atTop (nhds 0) := by
  let A : ℕ → Ω → ℝ := fun i => oaReleaseValue W Y L p i
  have hA (i : ℕ) : AEMeasurable (A i) μ :=
    oaReleaseValue_aemeasurable hmodel hnoise hε i
  have hAI : iIndepFun A μ := oaReleaseValue_iIndep hmodel hnoise
  have hAD (i : ℕ) : IdentDistrib (A 0) (A i) μ μ :=
    oaReleaseValue_identDistrib hmodel hnoise hε i
  let Am : ℕ → Ω → ℝ := fun i => (hA i).mk (A i)
  have hAmMeas (i : ℕ) : Measurable (Am i) := (hA i).measurable_mk
  have hAmAE (i : ℕ) : Am i =ᵐ[μ] A i := (hA i).ae_eq_mk.symm
  have hAmI : iIndepFun Am μ := hAI.congr fun i => (hAmAE i).symm
  have hAmD (i : ℕ) : IdentDistrib (Am 0) (Am i) μ μ := by
    refine ⟨(hAmMeas 0).aemeasurable, (hAmMeas i).aemeasurable, ?_⟩
    rw [Measure.map_congr (hAmAE 0), Measure.map_congr (hAmAE i)]
    exact (hAD i).map_eq
  let S : IIDSample Ω ℝ μ (μ.map (A 0)) := {
    Z := Am
    meas := hAmMeas
    indep := hAmI
    identDist := hAmD
    law := Measure.map_congr (hAmAE 0) }
  let ψ : ℝ → ℝ := fun x => x - contrast θ
  letI : IsProbabilityMeasure (μ.map (A 0)) := Measure.isProbabilityMeasure_map (hA 0)
  have hψmean : ∫ x, ψ x ∂(μ.map (A 0)) = 0 := by
    change (∫ x, x - contrast θ ∂(μ.map (A 0))) = 0
    rw [integral_map (hA 0)
      (show AEStronglyMeasurable (fun x : ℝ => x - contrast θ) (μ.map (A 0)) by
        fun_prop)]
    have hAint : Integrable (A 0) μ := by
      change Integrable (oaTrialPart W Y p 0 + L 0) μ
      exact (oaTrialPart_integrable hmodel 0).add
        (comparatorNoise_integrable hmodel.assignmentInterior hnoise hε 0)
    rw [integral_sub hAint (integrable_const _),
      oaReleaseValue_integral hmodel hnoise hε 0, integral_const]
    simp
  have hψint : Integrable (fun ω => ψ (S.Z 0 ω)) μ := by
    have hAint : Integrable (A 0) μ := by
      change Integrable (oaTrialPart W Y p 0 + L 0) μ
      exact (oaTrialPart_integrable hmodel 0).add
        (comparatorNoise_integrable hmodel.assignmentInterior hnoise hε 0)
    have hi : Integrable (fun ω => A 0 ω - contrast θ) μ :=
      hAint.sub (integrable_const _)
    exact hi.congr (by
      filter_upwards [hAmAE 0] with ω hω
      simp only [ψ, S]
      rw [hω])
  have hψsq : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ := by
    have hi : Integrable (fun ω => (A 0 ω - contrast θ) ^ 2) μ := by
      have hrel2 := oaReleaseValue_sq_integrable hmodel hnoise hε 0
      have hrel : Integrable (A 0) μ := by
        change Integrable (oaTrialPart W Y p 0 + L 0) μ
        exact (oaTrialPart_integrable hmodel 0).add
          (comparatorNoise_integrable hmodel.assignmentInterior hnoise hε 0)
      exact ((hrel2.sub (hrel.const_mul (2 * contrast θ))).add
        (integrable_const ((contrast θ) ^ 2))).congr
          (Filter.Eventually.of_forall fun ω => by
            change (A 0 ω) ^ 2 - 2 * contrast θ * A 0 ω + (contrast θ) ^ 2 =
              (A 0 ω - contrast θ) ^ 2
            ring)
    exact hi.congr (by
      filter_upwards [hAmAE 0] with ω hω
      simp only [ψ, S]
      rw [hω])
  have hpop : ∫ x, (ψ x) ^ 2 ∂(μ.map (A 0)) = VOA θ p ε := by
    change (∫ x : ℝ, (x - contrast θ) ^ 2 ∂(μ.map (A 0))) = VOA θ p ε
    rw [integral_map (hA 0)
      (show AEStronglyMeasurable (fun x : ℝ => (x - contrast θ) ^ 2)
          (μ.map (A 0)) by fun_prop)]
    simpa only [Function.comp_apply, A] using
      oaReleaseValue_centered_sq_integral hmodel hnoise hε 0
  have hcons := S.empiricalVar_tendsto_inProb
    (measurable_id.sub measurable_const) hψint hψsq hψmean
  change Modes.TendstoInProbability (fun _ : ℕ => μ) (S.empiricalVar ψ) atTop
    (fun _ _ => ∫ x, (ψ x) ^ 2 ∂(μ.map (A 0))) at hcons
  rw [hpop] at hcons
  have hemp (n : ℕ) : S.empiricalVar ψ n =ᵐ[μ] VhatOA W Y L p n := by
    have hall : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range n, S.Z i ω = A i ω := by
      induction Finset.range n using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          filter_upwards [hAmAE a, ih] with ω haω hsω
          intro i hi
          simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · exact haω
          · exact hsω i hi
    filter_upwards [hall] with ω hω
    rcases n with _ | n
    · simp [IIDSample.empiricalVar, IIDSample.sampleMean, VhatOA, tauOA]
    · rw [VhatOA_eq_second_moment_sub_sq W Y L p (n + 1) (by omega)]
      unfold IIDSample.empiricalVar IIDSample.sampleMean ψ tauOA
      have hsum1 : (∑ i ∈ Finset.range (n + 1), (S.Z i ω - contrast θ)) =
          ∑ i ∈ Finset.range (n + 1), (A i ω - contrast θ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hω i hi]
      have hsum2 : (∑ i ∈ Finset.range (n + 1), (S.Z i ω - contrast θ) ^ 2) =
          ∑ i ∈ Finset.range (n + 1), (A i ω - contrast θ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hω i hi]
      have hsqexpand : (∑ i ∈ Finset.range (n + 1),
          (A i ω - contrast θ) ^ 2) =
          (∑ i ∈ Finset.range (n + 1), (A i ω) ^ 2) -
            2 * contrast θ * (∑ i ∈ Finset.range (n + 1), A i ω) +
            (n + 1 : ℝ) * (contrast θ) ^ 2 := by
        have hpoint (x : ℝ) : (x - contrast θ) ^ 2 =
            x ^ 2 - (2 * contrast θ) * x + (contrast θ) ^ 2 := by ring
        simp_rw [hpoint]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        norm_num [Nat.cast_add, Nat.cast_one]
      rw [hsum1, hsum2, hsqexpand, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range]
      simp only [nsmul_eq_mul, A]
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hn]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
  intro δ hδ
  have htail := (Modes.tendstoInProbability_iff_norm
    (fun _ : ℕ => μ) (S.empiricalVar ψ) atTop (fun _ _ => VOA θ p ε)).mp hcons δ hδ
  have htail' : Tendsto (fun n => μ {ω | δ ≤
      |VhatOA W Y L p n ω - VOA θ p ε|}) atTop (nhds 0) := by
    apply htail.congr'
    filter_upwards with n
    apply measure_congr
    filter_upwards [hemp n] with ω hω
    simp only [Real.norm_eq_abs]
    change (δ ≤ |S.empiricalVar ψ n ω - VOA θ p ε|) =
      (δ ≤ |VhatOA W Y L p n ω - VOA θ p ε|)
    rw [hω]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail'
    (fun n => (bot_le : (0 : ENNReal) ≤ μ {ω | δ <
      |VhatOA W Y L p n ω - VOA θ p ε|}))
    (fun n => measure_mono (by
      intro ω hω
      change δ < |VhatOA W Y L p n ω - VOA θ p ε| at hω
      change δ ≤ |VhatOA W Y L p n ω - VOA θ p ε|
      exact le_of_lt hω))

end CausalSmith.Stat.LdpAteEfficiencySurface
