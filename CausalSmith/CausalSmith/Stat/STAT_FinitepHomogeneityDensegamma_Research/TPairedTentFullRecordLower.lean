module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryTentMixture

/-! Finite-moment homogeneity testing: TPairedTentFullRecordLower. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A normalized finite mixture of identical laws equals their full iid record law. This statement assumes [the hπ condition](hyp:hπ), [the hconst condition](hyp:hconst). [This is the stated conclusion](goal). -/
-- @node: priorMixture_eq_iid_of_constant
lemma priorMixture_eq_iid_of_constant (n : ℕ) (π : FinitePrior) (P0 : ObservedLaw)
    (hπ : PriorNormalized π) (hconst : ∀ i, priorLaw π i = P0) :
    priorMixture n π = Measure.pi (fun _ : Fin n => P0.P) := by
  unfold priorMixture
  simp_rw [hconst]
  rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hπ.1 i), hπ.2]
  simp

/-- All sign indices of the paired null enumerate the same zero-effect law. [This is the stated conclusion](goal). -/
-- @node: tentPrior_false_mixture
lemma tentPrior_false_mixture (n : ℕ) (v : Params) :
    priorMixture n (tentPrior false n v) =
      Measure.pi (fun _ : Fin n => (tentLaw false n v (fun _ => false)).P) := by
  apply priorMixture_eq_iid_of_constant _ _ _ (tentPrior_normalized false n v).1
  intro i
  change tentLaw false n v _ = tentLaw false n v _
  rw [tentLaw_false_eq_zero_table, tentLaw_false_eq_zero_table]

/-- The explicit paired-tent receipt retains the canonical null and alternative priors. The complete-record likelihood comparison uses the actual null density in all six categories. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: tent_canonical_lower_receipt
lemma tent_canonical_lower_receipt (v : Params) (hv : v.Valid) (n : ℕ) (hn : 2 ≤ n) :
    0 < tentMagnitude n v ∧ InNull v (tentLaw false n v (fun _ => false)) ∧
    (∀ x, (tentLaw false n v (fun _ => false)).e x = 1/2) ∧
    ArmSupport (tentLaw false n v (fun _ => false)) (tentMagnitude n v) ∧
    (∀ a : Bool, ∀ᵐ x ∂design,
      ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂(tentLaw false n v (fun _ => false)).Q a x ≤ 1) ∧
    PriorNormalized (tentPrior true n v) ∧ (∃ i, 0 < priorWeight (tentPrior true n v) i) ∧
    PriorSupported (tentPrior true n v) {law | InModel v law ∧ (∀ x, law.e x = 1/2) ∧
      ArmSupport law (tentMagnitude n v) ∧ cOracle v*rhoOracle n v ≤ hetDist law ∧
      hetDist law < d0 ∧
      ∀ a : Bool, ∀ᵐ x ∂design, ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂law.Q a x ≤ 1} ∧
    d0 ≤ maxDist v ∧
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n =>
      (tentLaw false n v (fun _ => false)).P)) (priorMixture n (tentPrior true n v)) < 1/2 ∧
    2/5 ≤ oracleTestingRisk n v (cOracle v*rhoOracle n v) ∧
    2/5 ≤ testingRisk n v (cOracle v*rhoOracle n v) := by
  let P0 := tentLaw false n v (fun _ => false)
  have hπ := tentPrior_normalized true n v
  have hconstruction : InNull v P0 ∧ (∀ x, P0.e x = 1/2) ∧ ArmSupport P0 (tentMagnitude n v) ∧
      (∀ a : Bool, ∀ᵐ x ∂design, ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂P0.Q a x ≤ 1) ∧
      PriorSupported (tentPrior true n v) {law | InModel v law ∧ (∀ x, law.e x = 1/2) ∧
        ArmSupport law (tentMagnitude n v) ∧ cOracle v*rhoOracle n v ≤ hetDist law ∧ hetDist law < d0 ∧
        ∀ a : Bool, ∀ᵐ x ∂design, ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂law.Q a x ≤ 1} ∧
      Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n (tentPrior true n v)) < 1/2 := by
    have harms := tentLaw_false_arm_properties v hv n hn (fun _ => false)
    refine ⟨tentLaw_false_inNull v hv n hn (fun _ => false), ?_, harms.1, ?_, ?_⟩
    · intro x
      have ht := zero_table_valid _ _ (tent_mark_parameters v hv n hn).1
        (tent_mark_parameters v hv n hn).2
      simp [P0, tentLaw_false_eq_zero_table, pairedTentObservedLaw, ht, tableProp]
    · intro a
      filter_upwards [] with x
      exact (harms.2 a x).le.trans (by cases a <;> norm_num)
    · constructor
      · intro i hi
        let σ := (Fintype.equivFin (Fin (tentRank n v/2) → Bool)).symm i
        change InModel v (tentLaw true n v σ) ∧ _
        have harms := tentLaw_true_arm_properties v hv n hn σ
        refine ⟨?_, (fun x => (tentLaw_true_primitives v hv n hn σ x).1), harms.1, ?_, ?_, ?_⟩
        · have ht := tentLaw_true_table_valid v hv n hn σ
          have he := fun x => (tentLaw_true_primitives v hv n hn σ x).1
          have hb := fun x => (tentLaw_true_primitives v hv n hn σ x).2.1
          constructor
          · unfold UniformDesign covariateLaw
            simp only [tentLaw, if_true, pairedTentObservedLaw, dif_pos ht]
            rw [pairedTentRecordLaw_eq_compProd _ _ _ ht]
            letI := pairedTentArm_markov _ _ _ ht
            letI := recordKernel_markov _ (measurable_tableProp _ _ _ _ _ ht) _
              (show ∀ x, 0 ≤ tableProp (fun _ => 0) x ∧ tableProp (fun _ => 0) x ≤ 1
                from fun x => by norm_num [tableProp]) (pairedTentArm_markov _ _ _ ht)
            letI : IsProbabilityMeasure design := by
              change IsProbabilityMeasure (volume : Measure unitInterval)
              infer_instance
            exact Measure.fst_compProd _ _
          · intro x; rw [he]; norm_num
          · refine ⟨ContinuousMap.continuous _, ?_, ?_⟩
            · intro x; rw [he]; norm_num
            · intro x z; rw [he, he]; simp only [sub_self, abs_zero]; positivity
          · refine ⟨ContinuousMap.continuous _, ?_, ?_⟩
            · intro x; rw [hb]; norm_num
            · intro x z; rw [hb, hb]; simp only [sub_self, abs_zero]; positivity
          · have hτ : (fun x => (tentLaw true n v σ).tau x) = tentEffect n v σ :=
              funext (fun x => (tentLaw_true_primitives v hv n hn σ x).2.2)
            change holderBall v.γ (fun x => (tentLaw true n v σ).tau x)
            rw [hτ]
            exact tentEffect_holderBall n v hv
              (by have := (tentRank_bounds v hv n hn).1; omega)
              (tentH_bounds v hv n hn).2.le σ
          · intro x; rw [hb]; norm_num
          · intro x
            rw [(tentLaw_true_primitives v hv n hn σ x).2.2, tentEffect,
              abs_mul, abs_mul, abs_of_nonneg (by norm_num [kappa0] : 0 ≤ kappa0),
              abs_of_nonneg (Real.rpow_nonneg (tentH_bounds v hv n hn).1.le _)]
            have hh : tentH n v^v.γ ≤ 1 := Real.rpow_le_one
              (tentH_bounds v hv n hn).1.le (tentH_bounds v hv n hn).2.le
              (by linarith [hv.2.2.2.1])
            have hg := coarseTent_abs_le_one (tentRank n v) σ x
            calc
              _ ≤ kappa0*1*1 := by gcongr <;> norm_num [kappa0]
              _ ≤ 1/2 := by norm_num [kappa0]
          · intro a
            filter_upwards [] with x
            rw [harms.2 a x]
            cases a <;> norm_num
        · exact paired_effect_distance_lower v hv n hn σ _
            (fun x => (tentLaw_true_primitives v hv n hn σ x).2.2)
        · change hetDist (tentLaw true n v σ) < d0
          exact tentLaw_true_distance_lt_d0 v hv n hn σ
        · intro a
          filter_upwards [] with x
          exact (harms.2 a x).le.trans (by cases a <;> norm_num)
      · exact tentMixture_tv_lt_half v hv n hn
  obtain ⟨hnull, he0, hs0, hm0, halt, htv⟩ := hconstruction
  have halt' : PriorSupported (tentPrior true n v)
      {law | InModel v law ∧ cOracle v*rhoOracle n v ≤ hetDist law} := by
    intro i hi
    exact ⟨(halt i hi).1, (halt i hi).2.2.2.1⟩
  have he : ∀ i, 0 < priorWeight (tentPrior true n v) i →
      (priorLaw (tentPrior true n v) i).e = P0.e := by
    intro i hi
    ext x
    exact ((halt i hi).2.1 x).trans (he0 x).symm
  exact ⟨(tent_mark_parameters v hv n hn).2,
    hnull, he0, hs0, hm0, hπ.1, hπ.2, halt, model_distance_lower v hv, htv,
    single_null_oracleTestingRisk_lower n v _ P0 _ hnull hπ.1 hπ.2 halt' he htv,
    single_null_testingRiskOn_lower n _ _ _ P0 _ hnull hπ.1 hπ.2 halt' htv⟩

/-- The bounded paired-tent receipt retains the prescribed signed-binary null and prior. Its complete-record likelihood comparison integrates both arms and both binary signs. This statement assumes [the hw condition](hyp:hw), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: binary_tent_canonical_lower_receipt
lemma binary_tent_canonical_lower_receipt (w : Smooth3) (hw : w.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    let P0 := binaryTentLaw false n w (fun _ => false)
    let π1 := binaryTentPrior true n w
    InBinaryNull w P0 ∧ (∀ x, P0.e x = 1/2) ∧
    PriorNormalized π1 ∧ (∃ i, 0 < priorWeight π1 i) ∧
    PriorSupported π1 {law | InBinaryModel w law ∧ (∀ x, law.e x = 1/2) ∧
      cOracle (Params.ofBounded w)*rhoOracle n (Params.ofBounded w) ≤ hetDist law ∧
      hetDist law < d0} ∧ d0 ≤ maxDistBounded w ∧
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π1) < 1/2 ∧
    2/5 ≤ boundedTestingRisk n w
      (cOracle (Params.ofBounded w)*rhoOracle n (Params.ofBounded w)) := by
  let P0 := binaryTentLaw false n w (fun _ => false)
  have hπ := binaryTentPrior_normalized true n w
  have hconstruction : InBinaryNull w P0 ∧ (∀ x, P0.e x = 1/2) ∧
      PriorSupported (binaryTentPrior true n w) {law | InBinaryModel w law ∧ (∀ x, law.e x = 1/2) ∧
        cOracle (Params.ofBounded w)*rhoOracle n (Params.ofBounded w) ≤ hetDist law ∧ hetDist law < d0} ∧
      Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n (binaryTentPrior true n w)) < 1/2 := by
    refine ⟨binaryTentLaw_false_inBinaryNull w hw n hn (fun _ => false), ?_, ?_, ?_⟩
    · intro x
      rw [(binaryTentLaw_primitives w hw n hn false (fun _ => false)).1]
      rfl
    · intro i hi
      let σ := (Fintype.equivFin (Fin (tentRank n (Params.ofBounded w)/2) → Bool)).symm i
      change InBinaryModel w (binaryTentLaw true n w σ) ∧ _
      refine ⟨binaryTentLaw_inBinaryModel w hw n hn true σ, ?_, ?_,
        binaryTentLaw_true_distance_lt_d0 w hw n hn σ⟩
      · intro x
        change (binaryTentLaw true n w σ).e x = 1/2
        rw [(binaryTentLaw_primitives w hw n hn true σ).1]
        rfl
      · apply paired_effect_distance_lower (Params.ofBounded w)
          ⟨by norm_num [Params.ofBounded], hw⟩ n hn σ (binaryTentLaw true n w σ)
        intro x
        rw [(binaryTentLaw_primitives w hw n hn true σ).2.2]
        rfl
    · exact binaryTentMixture_tv_lt_half w hw n hn
  obtain ⟨hnull, he0, halt, htv⟩ := hconstruction
  have hm0 : InBinaryModel w P0 :=
    ⟨hnull.uniform, hnull.overlap, hnull.propensitySmooth, hnull.baselineSmooth,
      hnull.effectSmooth, hnull.baselineCap, hnull.effectCap, hnull.rawMoment, hnull.signedBinaryOutcome⟩
  have hbm0 := binaryModel_inBoundedModel w P0 hm0
  have hbnull : InBoundedNull w P0 :=
    ⟨hbm0.uniform, hbm0.overlap, hbm0.propensitySmooth, hbm0.baselineSmooth,
      hbm0.effectSmooth, hbm0.baselineCap, hbm0.effectCap, hbm0.rawMoment, hbm0.boundedOutcome,
      hnull.nullConstancy⟩
  have halt' : PriorSupported (binaryTentPrior true n w)
      {law | InBoundedModel w law ∧ cOracle (Params.ofBounded w)*rhoOracle n (Params.ofBounded w) ≤ hetDist law} := by
    intro i hi
    exact ⟨binaryModel_inBoundedModel w _ (halt i hi).1, (halt i hi).2.2.1⟩
  have hd : d0 ≤ maxDistBounded w := by
    change d0 ≤ maxDistBounded (Params.ofBounded w).toSmooth3
    rw [maxDistBounded_eq_maxDist]
    exact model_distance_lower (Params.ofBounded w) ⟨by norm_num [Params.ofBounded], hw⟩
  exact ⟨hnull, he0, hπ.1, hπ.2, halt, hd, htv,
    single_null_testingRiskOn_lower n _ _ _ P0 _ hbnull hπ.1 hπ.2 halt' htv⟩

/-- [Paired tent full record lower](goal).
For every \(v\in\mathcal V\), put \(q=(p-1)/p\), \(E_0=2\gamma q/(2\gamma+q)\), and \(c^{\mathrm
e}_v=4^{-\gamma}/(16\sqrt3)\). For every \(n\ge2\) there is a legal null law and a finite
mixture of legal alternatives, all with the same entire propensity \(e_P\equiv1/2\), such that
every alternative has \[  c^{\mathrm e}_vn^{-E_0}\le d(P)<d_0\le D_v,  \qquad
\operatorname{TV}(P_0^{\otimes n},\overline P_1^{(n)})<1/2. \] Their arm outcomes have support
\(\{0,-L,L\}\), with \(L\to\infty\), and raw conditional \(p\)-moment at most one. Consequently
\[  B_n^{\mathrm e}(v,c^{\mathrm e}_vn^{-E_0})\ge2/5>1/10,  \qquad B_n(v,c^{\mathrm
e}_vn^{-E_0})\ge2/5. \] A separate signed-binary construction gives the analogous bounded lower
at \(c^{\mathrm b}_w n^{-2\gamma/(4\gamma+1)}\), with \(c^{\mathrm
b}_w=4^{-\gamma}/(16\sqrt3)\). All these alternatives are nonempty for every \(n\ge2\).
-/
-- @node: lem:paired-tent-full-record-lower
lemma paired_tent_full_record_lower :
    (∀ v : Params, v.Valid → ∃ L : ℕ → ℝ,
      Filter.Tendsto L Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, 2 ≤ n → ∃ P0 : ObservedLaw, ∃ π1 : FinitePrior,
        0 < L n ∧ InNull v P0 ∧ (∀ x, P0.e x = 1/2) ∧ ArmSupport P0 (L n) ∧
        (∀ a : Bool, ∀ᵐ x ∂design, ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂P0.Q a x ≤ 1) ∧
        PriorNormalized π1 ∧ (∃ i, 0 < priorWeight π1 i) ∧
        PriorSupported π1 {law | InModel v law ∧ (∀ x, law.e x = 1/2) ∧
          ArmSupport law (L n) ∧ cOracle v*rhoOracle n v ≤ hetDist law ∧ hetDist law < d0 ∧
          ∀ a : Bool, ∀ᵐ x ∂design, ∫⁻ y, ENNReal.ofReal (|y|^v.p) ∂law.Q a x ≤ 1} ∧
        d0 ≤ maxDist v ∧
        Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π1) < 1/2 ∧
        2/5 ≤ oracleTestingRisk n v (cOracle v*rhoOracle n v) ∧
        2/5 ≤ testingRisk n v (cOracle v*rhoOracle n v)) ∧
    (∀ w : Smooth3, w.Valid → ∀ n : ℕ, 2 ≤ n → ∃ P0 : ObservedLaw, ∃ π1 : FinitePrior,
      InBinaryNull w P0 ∧ (∀ x, P0.e x = 1/2) ∧
      PriorNormalized π1 ∧ (∃ i, 0 < priorWeight π1 i) ∧
      PriorSupported π1 {law | InBinaryModel w law ∧ (∀ x, law.e x = 1/2) ∧
        cOracle (Params.ofBounded w)*rhoOracle n (Params.ofBounded w) ≤ hetDist law ∧ hetDist law < d0} ∧
      d0 ≤ maxDistBounded w ∧
      Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π1) < 1/2 ∧
      2/5 ≤ boundedTestingRisk n w (cOracle (Params.ofBounded w)*rhoOracle n (Params.ofBounded w))) := by
  constructor
  · intro v hv
    refine ⟨fun n => tentMagnitude n v, ?_, ?_⟩
    · exact tentMagnitude_tendsto_atTop v hv
    · intro n hn
      exact ⟨tentLaw false n v (fun _ => false), tentPrior true n v,
        tent_canonical_lower_receipt v hv n hn⟩
  · intro w hw n hn
    exact ⟨binaryTentLaw false n w (fun _ => false), binaryTentPrior true n w,
      binary_tent_canonical_lower_receipt w hw n hn⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
