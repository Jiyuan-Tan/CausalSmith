module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Bridge.Protocol

/-!
# Causal bridge identification

Causal value identities and deterministic signed-input transcript preprocessing.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology Classical
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- Fix [the probability law P](hyp:P) and [the coordinate index](hyp:j). [Conditional signed cell mean](goal). -/
def signedCellMean (P : Measure (FullRecord d)) (j : Fin d) : ℝ :=
  (∫ w, if cell w = j then obsSign (observe w) else 0 ∂P) / P.real {w | cell w = j}

/-- Assume [the causal-model conditions for the data law](hyp:hP). [Interior arm means put the causal contrast in the declared cube](goal). -/
-- @node: contrast_mem_parameterCube
lemma contrast_mem_parameterCube (P : Measure (FullRecord d)) (hP : CausalModel P) :
    contrast P ∈ parameterCube d := by
  intro j
  obtain ⟨h0l, h0u⟩ := hP.interior false j
  obtain ⟨h1l, h1u⟩ := hP.interior true j
  constructor <;> dsimp [contrast] <;> linarith

/-- [The armwise maximum splits into the arm average and half the absolute contrast](goal). -/
-- @node: value_arm_average_decomposition
lemma value_arm_average_decomposition (P : Measure (FullRecord d)) :
    value P = (d : ℝ)⁻¹ * ∑ j, (armMean P false j + armMean P true j)/2 +
      signedNorm (contrast P)/2 := by
  have hmax (a b : ℝ) : max a b = (a+b)/2 + |b-a|/2 := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [max_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  simp only [value, signedNorm, contrast, hmax, Finset.sum_add_distrib,
    ← Finset.sum_div]
  ring

/-- [A finite event partitions into its two Boolean marks](goal). -/
-- @node: fullRecord_real_split_bool
lemma fullRecord_real_split_bool (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (E : Set (FullRecord d)) (f : FullRecord d → Bool) :
    P.real E = ∑ b : Bool, P.real {w | w ∈ E ∧ f w = b} := by
  rw [Fintype.sum_bool, ← measureReal_union]
  · congr 1
    ext w
    cases h : f w <;> simp [h]
  · rw [Set.disjoint_left]
    intro w ha hb
    simp only [Set.mem_setOf_eq] at ha hb
    simp [ha.2] at hb
  · exact MeasurableSet.of_discrete

/-- Assume [the causal-model conditions for the data law](hyp:hP). [Fair randomization also holds after marginalizing either potential outcome](goal). -/
-- @node: fair_potential_event
lemma fair_potential_event (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (j : Fin d) (a y : Bool) :
    P.real {w | cell w = j ∧ arm w = a ∧ potential a w = y} =
      (1/2 : ℝ) * P.real {w | cell w = j ∧ potential a w = y} := by
  cases a
  · simp only [potential, Bool.false_eq_true, ↓reduceIte]
    rw [fullRecord_real_split_bool P _ outcome1,
      fullRecord_real_split_bool P {w | cell w = j ∧ outcome0 w = y} outcome1,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y1 _
    convert hP.fair j false y y1 using 1 <;> congr 2 <;> ext w <;>
      simp only [Set.mem_setOf_eq] <;> tauto
  · simp only [potential, ↓reduceIte]
    rw [fullRecord_real_split_bool P _ outcome0,
      fullRecord_real_split_bool P {w | cell w = j ∧ outcome1 w = y} outcome0,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y0 _
    convert hP.fair j true y0 y using 1 <;> congr 2 <;> ext w <;>
      simp only [Set.mem_setOf_eq] <;> tauto

/-- Assume [the causal-model conditions for the data law](hyp:hP). [Consistency in the model gives the corresponding almost-everywhere identity](goal). -/
-- @node: causal_consistency_ae
lemma causal_consistency_ae (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) : ∀ᵐ w ∂P, outcome w = potential (arm w) w := by
  apply (ae_iff_prob_eq_one (Measurable.of_discrete)).2
  have hh : P.real {w | outcome w = potential (arm w) w} = P.real Set.univ := by
    simpa [Consistency] using hP.consistent
  exact ((measureReal_eq_measureReal_iff).1 hh).trans (measure_univ)

/-- Assume [the causal-model conditions for the data law](hyp:hP). [Marginalizing the potential outcome leaves a fair assignment in each cell](goal). -/
-- @node: fair_arm_event
lemma fair_arm_event (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (j : Fin d) (a : Bool) :
    P.real {w | cell w = j ∧ arm w = a} =
      (1/2 : ℝ) * P.real {w | cell w = j} := by
  rw [fullRecord_real_split_bool P {w | cell w = j ∧ arm w = a} (potential a)]
  simp only [Set.mem_setOf_eq, and_assoc]
  simp_rw [fair_potential_event P hP j a]
  rw [← Finset.mul_sum]
  simpa only [Set.mem_setOf_eq] using congrArg (fun x : ℝ => (1/2 : ℝ) * x)
    (fullRecord_real_split_bool P {w | cell w = j} (potential a)).symm

/-- [Integrating a finite event's unit indicator recovers its real probability](goal). -/
-- @node: integral_fullRecord_event
lemma integral_fullRecord_event (P : Measure (FullRecord d)) (E : Set (FullRecord d)) :
    (∫ w, if w ∈ E then (1 : ℝ) else 0 ∂P) = P.real E := by
  classical
  simpa [Set.indicator] using integral_indicator_one (μ := P)
    (s := E) MeasurableSet.of_discrete

/-- Assume [the causal-model conditions for the data law](hyp:hP). [Signed cell means identify the causal contrast by fair assignment and consistency](goal). -/
-- @node: signedCellMean_eq_contrast
lemma signedCellMean_eq_contrast (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (j : Fin d) : signedCellMean P j = contrast P j := by
  classical
  have heq : (fun w => if cell w = j then obsSign (observe w) else 0) =ᵐ[P]
      (fun w =>
        2 * (if cell w = j ∧ arm w = true ∧ potential true w = true then (1 : ℝ) else 0) -
        (if cell w = j ∧ arm w = true then (1 : ℝ) else 0) -
        2 * (if cell w = j ∧ arm w = false ∧ potential false w = true then (1 : ℝ) else 0) +
        (if cell w = j ∧ arm w = false then (1 : ℝ) else 0)) := by
    filter_upwards [causal_consistency_ae P hP] with w hw
    by_cases hj : cell w = j
    · cases ha : arm w <;> cases hy0 : potential false w <;> cases hy1 : potential true w <;>
        norm_num [obsSign, observe, hw, ha, hy0, hy1, hj, signVal]
    · simp [hj]
  have hnum : (∫ w, if cell w = j then obsSign (observe w) else 0 ∂P) =
      P.real {w | cell w = j ∧ potential true w = true} -
        P.real {w | cell w = j ∧ potential false w = true} := by
    rw [integral_congr_ae heq]
    have hlin : (∫ w,
        2 * (if cell w = j ∧ arm w = true ∧ potential true w = true then (1 : ℝ) else 0) -
        (if cell w = j ∧ arm w = true then (1 : ℝ) else 0) -
        2 * (if cell w = j ∧ arm w = false ∧ potential false w = true then (1 : ℝ) else 0) +
        (if cell w = j ∧ arm w = false then (1 : ℝ) else 0) ∂P) =
      2 * P.real {w | cell w = j ∧ arm w = true ∧ potential true w = true} -
        P.real {w | cell w = j ∧ arm w = true} -
        2 * P.real {w | cell w = j ∧ arm w = false ∧ potential false w = true} +
        P.real {w | cell w = j ∧ arm w = false} := by
      simp only [← integral_fullRecord_event]
      integral_linearity
      simp only [Set.mem_setOf_eq]
    rw [hlin, fair_potential_event P hP j true true,
      fair_potential_event P hP j false true, fair_arm_event P hP j true,
      fair_arm_event P hP j false]
    ring
  simp only [signedCellMean, contrast, armMean, hnum, sub_div]

/-- [A signed cell indicator is the difference of its positive and negative atoms](goal). -/
-- @node: signed_cell_integral_atoms
lemma signed_cell_integral_atoms (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (j : Fin d) :
    (∫ w, if cell w = j then obsSign (observe w) else 0 ∂P) =
      P.real {w | signedObserve (observe w) = (j,true)} -
        P.real {w | signedObserve (observe w) = (j,false)} := by
  have heq : (fun w : FullRecord d => if cell w = j then obsSign (observe w) else 0) =
      (fun w => (if signedObserve (observe w) = (j,true) then (1 : ℝ) else 0) -
        (if signedObserve (observe w) = (j,false) then (1 : ℝ) else 0)) := by
    funext w
    rcases w with ⟨j', a, y, y0, y1⟩
    by_cases hj : j' = j <;> cases a <;> cases y <;>
      simp [cell, obsSign, observe, signedObserve, signVal, arm, outcome, hj]
  rw [heq]
  simp only [← integral_fullRecord_event]
  integral_linearity
  simp only [Set.mem_setOf_eq]

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [positive dimension](hyp:hd). [A sign-valued conditional mean determines both signed atom probabilities](goal). -/
-- @node: causal_signed_atom
lemma causal_signed_atom (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 0 < d) (j : Fin d) (s : Bool) :
    P.real {w | signedObserve (observe w) = (j,s)} =
      (1 + signVal s * contrast P j)/(2*d) := by
  have hsplit := fullRecord_real_split_bool P {w | cell w = j}
    (fun w => (signedObserve (observe w)).2)
  have hatom (b : Bool) : {w : FullRecord d | cell w = j ∧
      (signedObserve (observe w)).2 = b} =
      {w | signedObserve (observe w) = (j,b)} := by
    ext w
    simp [signedObserve, observe, cell]
  simp only [Set.mem_setOf_eq, hatom, Fintype.sum_bool] at hsplit
  rw [hP.uniform j] at hsplit
  have hmean := signedCellMean_eq_contrast P hP j
  simp only [signedCellMean, signed_cell_integral_atoms, hP.uniform j] at hmean
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hdiff := (div_eq_iff (inv_ne_zero hdR)).mp hmean
  calc
    _ = ((d : ℝ)⁻¹ + signVal s *
        (P.real {w | signedObserve (observe w) = (j,true)} -
          P.real {w | signedObserve (observe w) = (j,false)}))/2 := by
      cases s <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte] <;>
        linarith [hsplit]
    _ = _ := by rw [hdiff]; field_simp <;> ring

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [positive dimension](hyp:hd). [The observed signed marginal is the paired law identified by the causal contrast](goal). -/
-- @node: causal_signed_law
lemma causal_signed_law (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 0 < d) :
    (observedLaw P).map signedObserve = pairedLaw (contrast P) := by
  have hprob : IsProbabilityMeasure (pairedLaw (contrast P)) :=
    pairedFamily_subset_simplex hd
      (Set.mem_image_of_mem pairedLaw (contrast_mem_parameterCube P hP))
  letI := hprob
  haveI : IsProbabilityMeasure (observedLaw P) := by
    unfold observedLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure ((observedLaw P).map signedObserve) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_singleton
  rintro ⟨j,s⟩
  apply (measureReal_eq_measureReal_iff).mp
  rw [observedLaw, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.real, Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
  change P.real {w | signedObserve (observe w) = (j,s)} = _
  rw [causal_signed_atom P hP hd]
  unfold pairedLaw
  rw [atomLaw_real_singleton]
  intro v
  have h := contrast_mem_parameterCube P hP v.1
  apply div_nonneg _ (by positivity)
  cases v.2 <;> simp only [signVal, Bool.false_eq_true, ↓reduceIte] <;> linarith [h.1, h.2]

/-- Assume [the causal-model conditions for the data law](hyp:hP). [The observed outcome in each cell averages the two potential-outcome marginals](goal). -/
-- @node: causal_cell_outcome_integral
lemma causal_cell_outcome_integral (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (j : Fin d) :
    (∫ w, if cell w = j then bitVal (outcome w) else 0 ∂P) =
      (P.real {w | cell w = j ∧ potential false w = true} +
        P.real {w | cell w = j ∧ potential true w = true})/2 := by
  classical
  have heq : (fun w => if cell w = j then bitVal (outcome w) else 0) =ᵐ[P]
      (fun w =>
        (if cell w = j ∧ arm w = false ∧ potential false w = true then (1 : ℝ) else 0) +
        (if cell w = j ∧ arm w = true ∧ potential true w = true then (1 : ℝ) else 0)) := by
    filter_upwards [causal_consistency_ae P hP] with w hw
    by_cases hj : cell w = j
    · cases ha : arm w <;> cases hy0 : potential false w <;> cases hy1 : potential true w <;>
        norm_num [bitVal, hw, ha, hy0, hy1, hj]
    · simp [hj]
  rw [integral_congr_ae heq]
  integral_linearity
  have hfalse := integral_fullRecord_event P
    {w | cell w = j ∧ arm w = false ∧ potential false w = true}
  have htrue := integral_fullRecord_event P
    {w | cell w = j ∧ arm w = true ∧ potential true w = true}
  simp only [Set.mem_setOf_eq] at hfalse htrue
  rw [hfalse, htrue, fair_potential_event P hP j false true,
    fair_potential_event P hP j true true]
  ring

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [dimension at least two](hyp:hd). [Uniform cells and randomization identify the outcome baseline with the mean arm average](goal). -/
-- @node: baseline_eq_arm_average
lemma baseline_eq_arm_average (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 2 ≤ d) :
    baseline P = (d : ℝ)⁻¹ * ∑ j, (armMean P false j + armMean P true j)/2 := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hcell (a : Bool) (j : Fin d) :
      P.real {w | cell w = j ∧ potential a w = true} = (d : ℝ)⁻¹ * armMean P a j := by
    simp only [armMean, hP.uniform j]
    field_simp
  have hsum : (fun w => bitVal (outcome w)) =
      (fun w => ∑ j : Fin d, if cell w = j then bitVal (outcome w) else 0) := by
    funext w
    simp
  have hbase : baseline P = ∫ w, bitVal (outcome w) ∂P := by
    simpa only [baseline, bitVal, Set.mem_setOf_eq] using (integral_fullRecord_event P {w | outcome w = true}).symm
  rw [hbase, hsum]
  integral_linearity
  simp_rw [causal_cell_outcome_integral P hP, hcell]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Assume [the causal-model conditions for the data law](hyp:hP) and [dimension at least two](hyp:hd). [The causal value equals the observed baseline plus half the signed contrast norm](goal). -/
-- @node: causal_value_decomposition
lemma causal_value_decomposition (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (hd : 2 ≤ d) :
    value P = baseline P + signedNorm (contrast P)/2 := by
  rw [value_arm_average_decomposition, baseline_eq_arm_average P hP hd]

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [The symmetric arm means give contrast theta and average welfare one half](goal). -/
-- @node: symmetricLaw_value
lemma symmetricLaw_value (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d)
    (hd : 0 < d) : value (symmetricLaw theta) = 1/2 + signedNorm theta/2 := by
  have hcontrast : contrast (symmetricLaw theta) = theta := by
    funext j
    simp only [contrast, symmetricLaw_armMean theta htheta hd, signVal,
      Bool.false_eq_true, ↓reduceIte]
    ring
  rw [value_arm_average_decomposition, hcontrast]
  have havg : ∀ j : Fin d,
      (armMean (symmetricLaw theta) false j + armMean (symmetricLaw theta) true j)/2 =
        (1/2 : ℝ) := by
    intro j
    simp only [symmetricLaw_armMean theta htheta hd, signVal,
      Bool.false_eq_true, ↓reduceIte]
    ring
  simp_rw [havg]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp [hdR]

/-- Assume [order no larger than the sample size](hyp:hk). [Deterministic preprocessing preserves every recursively constructed prefix law](goal). -/
-- @node: pulledProtocol_prefixLaw
lemma pulledProtocol_prefixLaw (K : LocalProtocol n (PairedSymbol d))
    (o : Fin n → ObsRecord d) (r : K.Seed) (k : ℕ) (hk : k ≤ n) :
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw
      (pulledProtocol K).kernels (fun i => (o i,r)) k hk =
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw
      K.kernels (fun i => (signedObserve (o i),r)) k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw_succ,
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw_succ, ih]
    congr 2
/-- [Fixed transcripts under signed preprocessing are exactly paired-input transcripts](goal). -/
-- @node: pulledProtocol_fixedTranscriptLaw
lemma pulledProtocol_fixedTranscriptLaw (K : LocalProtocol n (PairedSymbol d))
    (o : Fin n → ObsRecord d) (r : K.Seed) :
    fixedTranscriptLaw (pulledProtocol K) o r =
      fixedTranscriptLaw K (fun i => signedObserve (o i)) r :=
  pulledProtocol_prefixLaw K o r n le_rfl

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [dimension at least two](hyp:hd), and [the stated htheta condition](hyp:htheta). [Signed preprocessing pushes the full iid decision experiment to the paired one](goal). -/
-- @node: pulledProtocol_decisionLaw
lemma pulledProtocol_decisionLaw (S : SamplingScheme n d) (hIID : IidPeople S)
    (hRandom : IndependentRandomness S) (hd : 2 ≤ d)
    (K : LocalProtocol n (PairedSymbol d)) (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) :
    decisionLaw S (pulledProtocol K) (symmetricLaw theta) =
      canonicalDecisionLaw K (pairedLaw theta) := by
  haveI := symmetricLaw_probability theta htheta (by omega)
  have hmodel := symmetricLaw_causalModel theta htheta (by omega)
  have hcontrast : contrast (symmetricLaw theta) = theta := by
    funext j
    simp only [contrast, symmetricLaw_armMean theta htheta (by omega), signVal,
      Bool.false_eq_true, ↓reduceIte]
    ring
  have hsigned : (observedLaw (symmetricLaw theta)).map signedObserve = pairedLaw theta := by
    rw [causal_signed_law _ hmodel (by omega), hcontrast]
  let f : ((Fin n → ObsRecord d) × K.Seed × ℝ) →
      ((Fin n → PairedSymbol d) × K.Seed × ℝ) :=
    fun w => (fun i => signedObserve (w.1 i), w.2)
  have hf : Measurable f := by fun_prop
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) := by
    exact Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  haveI : IsProbabilityMeasure ((observedLaw (symmetricLaw theta)).map signedObserve) :=
    Measure.isProbabilityMeasure_map (show Measurable signedObserve by fun_prop).aemeasurable
  have hpi : (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).map
      (fun o i => signedObserve (o i)) = Measure.pi (fun _ : Fin n => pairedLaw theta) := by
    rw [Measure.pi_map_pi (fun _ => (show Measurable signedObserve by fun_prop).aemeasurable)]
    simp only [hsigned]
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  have hinput : ((Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta))).prod
      (K.seedLaw.prod uniform01)).map f =
      (Measure.pi (fun _ : Fin n => pairedLaw theta)).prod (K.seedLaw.prod uniform01) := by
    rw [← hpi]
    have hmap := (Measure.map_prod_map
      (Measure.pi (fun _ : Fin n => observedLaw (symmetricLaw theta)))
      (K.seedLaw.prod uniform01)
      (show Measurable (fun o : Fin n → ObsRecord d => fun i => signedObserve (o i))
        by fun_prop) (measurable_id : Measurable (id : K.Seed × ℝ → K.Seed × ℝ))).symm
    have hfun : Prod.map (fun o : Fin n → ObsRecord d => fun i => signedObserve (o i))
        (id : K.Seed × ℝ → K.Seed × ℝ) = f := by
      funext w
      cases w
      rfl
    rw [hfun, Measure.map_id] at hmap
    exact hmap
  unfold decisionLaw canonicalDecisionLaw
  change ((S K.Seed K.seedLaw (symmetricLaw theta)).bind (fun w =>
    (fixedTranscriptLaw (pulledProtocol K) w.1 w.2.1).map
      (fun z => (z,w.2.1,w.2.2)))) = _
  rw [hRandom K.Seed K.seedLaw (symmetricLaw theta) hmodel,
    hIID K.Seed K.seedLaw (symmetricLaw theta) hmodel]
  simp only [pulledProtocol_fixedTranscriptLaw]
  rw [← hinput]
  unfold Measure.bind
  rw [Measure.map_map (measurable_protocol_decisionRows K) hf]
  rfl


end CausalSmith.Stat.LdpOptvalueUniformFrontier
