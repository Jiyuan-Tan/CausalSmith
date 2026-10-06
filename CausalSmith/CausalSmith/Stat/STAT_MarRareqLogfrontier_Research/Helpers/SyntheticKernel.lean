module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.SyntheticCompletion
public import Causalean.Mathlib.MeasureTheory.IntegralBind

/-! Law-independent fair-coin completion of a discrete observational record. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

/-- For [the specified inputs and assumptions](hyp:d,r,u), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
def syntheticRecord {d : ℕ} (r : ZengRecord d) (u : Bool) : ObsRecord d :=
  ⟨r.1, u, false, r.2.1 == u, (r.2.1 == u) && r.2.2⟩

/-- For [the specified inputs and assumptions](hyp:d,r), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def syntheticOneRecord {d : ℕ} (r : ZengRecord d) :
    Measure (ObsRecord d) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (syntheticRecord r false) +
    (1 / 2 : ℝ≥0∞) • Measure.dirac (syntheticRecord r true)

-- @node: syntheticOneRecord_eq_coin_map
/-- Given [the specified inputs and assumptions](hyp:d,r), [the stated mathematical conclusion holds](goal). -/
lemma syntheticOneRecord_eq_coin_map {d : ℕ} (r : ZengRecord d) :
    syntheticOneRecord r =
      Measure.map (syntheticRecord r)
        ((1 / 2 : ℝ≥0∞) • Measure.dirac false +
          (1 / 2 : ℝ≥0∞) • Measure.dirac true) := by
  rw [Measure.map_add _ _ (by fun_prop)]
  simp [syntheticOneRecord, Measure.map_smul]

/-- Given [the specified inputs and assumptions](hyp:d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma SyntheticCompletion.observedLaw_eq_bind {d : ℕ} {q : ℝ} (P : ZengLaw d)
    (hP : P ∈ zengDiscreteClass d q) :
    (fullMeasure P).map obs =
      P.1.bind (fun r : ZengRecord d => syntheticOneRecord r) := by
  let L := (parameters P).fullLaw
  haveI : IsProbabilityMeasure L := (parameters P).fullLaw_probability
  have hobs (z : FullCoord (Fin d) × Bool) :
      obs (toFullRecord z) = syntheticRecord (selectMark z.1) z.2 := by
    rcases z with ⟨⟨x, b, y₀, y₁⟩, a⟩
    cases a <;> cases b <;> cases y₀ <;> cases y₁ <;> rfl
  have hpair :
      (L.prod fairCoin).map
          (fun z : FullCoord (Fin d) × Bool => (selectMark z.1, z.2)) =
        P.1.prod fairCoin := by
    change Measure.map (Prod.map selectMark id) (L.prod fairCoin) = _
    rw [← Measure.map_prod_map (f := selectMark) (g := id) L fairCoin
      (by fun_prop) measurable_id]
    rw [(parameters P).selectMark_map, selected_eq P hP]
    simp
  calc
    (fullMeasure P).map obs =
        (L.prod fairCoin).map
          (fun z => syntheticRecord (selectMark z.1) z.2) := by
      rw [fullMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext z
      exact hobs z
    _ = (P.1.prod fairCoin).map (fun z => syntheticRecord z.1 z.2) := by
      rw [← hpair, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = P.1.bind (fun r => fairCoin.map (syntheticRecord r)) := by
      exact (bind_map_eq_prod_map P.1 fairCoin syntheticRecord (by fun_prop)).symm
    _ = P.1.bind (fun r : ZengRecord d => syntheticOneRecord r) := by
      apply Measure.bind_congr_right
      filter_upwards [] with r
      simpa [fairCoin] using (syntheticOneRecord_eq_coin_map r).symm

/-- For [the specified inputs and assumptions](hyp:n,d,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def syntheticProductLaw {n d : ℕ}
    (s : Fin n → ZengRecord d) : Measure (Fin n → ObsRecord d) :=
  Measure.pi (fun i => syntheticOneRecord (s i))

-- @node: syntheticProductLaw_eq_coin_map
/-- Given [the specified inputs and assumptions](hyp:n,d,s), [the stated mathematical conclusion holds](goal). -/
lemma syntheticProductLaw_eq_coin_map {n d : ℕ}
    (s : Fin n → ZengRecord d) :
    syntheticProductLaw s =
      Measure.map (fun u : Fin n → Bool => fun i => syntheticRecord (s i) (u i))
        (Measure.pi (fun _ : Fin n =>
          (1 / 2 : ℝ≥0∞) • Measure.dirac false +
            (1 / 2 : ℝ≥0∞) • Measure.dirac true)) := by
  let coin : Measure Bool :=
    (1 / 2 : ℝ≥0∞) • Measure.dirac false +
      (1 / 2 : ℝ≥0∞) • Measure.dirac true
  haveI : IsProbabilityMeasure coin := by
    refine ⟨?_⟩
    simp [coin, ENNReal.inv_two_add_inv_two]
  letI (i : Fin n) : IsProbabilityMeasure (coin.map (syntheticRecord (s i))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  change syntheticProductLaw s =
    (Measure.pi (fun _ : Fin n => coin)).map
      (fun u i => syntheticRecord (s i) (u i))
  rw [Measure.pi_map_pi (fun i => by fun_prop)]
  unfold syntheticProductLaw
  congr 1
  funext i
  exact syntheticOneRecord_eq_coin_map (s i)

/-- Given [the specified inputs and assumptions](hyp:n,d,P), [the stated mathematical conclusion holds](goal). -/
lemma syntheticSample_bind_eq_pi {n d : ℕ} (P : ZengLaw d) :
    (zengSampleLaw n P).bind syntheticProductLaw =
      Measure.pi (fun _ : Fin n => P.1.bind syntheticOneRecord) := by
  let coinPi := Measure.pi (fun _ : Fin n => SyntheticCompletion.fairCoin)
  haveI : IsProbabilityMeasure P.1 := P.2
  haveI : IsProbabilityMeasure coinPi := by
    dsimp [coinPi]
    infer_instance
  have hkernel : syntheticProductLaw =
      fun s : Fin n → ZengRecord d =>
        coinPi.map (fun u i => syntheticRecord (s i) (u i)) := by
    funext s
    simpa [coinPi, SyntheticCompletion.fairCoin] using
      syntheticProductLaw_eq_coin_map s
  rw [hkernel]
  rw [SyntheticCompletion.bind_map_eq_prod_map _ _ _ (measurable_of_finite _)]
  let e := MeasurableEquiv.arrowProdEquivProdArrow (ZengRecord d) Bool (Fin n)
  have hpair :
      ((zengSampleLaw n P).prod coinPi).map e.symm =
        Measure.pi (fun _ : Fin n => P.1.prod SyntheticCompletion.fairCoin) := by
    exact (measurePreserving_arrowProdEquivProdArrow
      (ZengRecord d) Bool (Fin n) (fun _ => P.1)
      (fun _ => SyntheticCompletion.fairCoin)).symm.map_eq
  calc
    ((zengSampleLaw n P).prod coinPi).map
        (fun z i => syntheticRecord (z.1 i) (z.2 i)) =
        (((zengSampleLaw n P).prod coinPi).map e.symm).map
          (fun w i => syntheticRecord (w i).1 (w i).2) := by
      rw [Measure.map_map (by fun_prop) e.symm.measurable]
      rfl
    _ = (Measure.pi (fun _ : Fin n =>
          P.1.prod SyntheticCompletion.fairCoin)).map
          (fun w i => syntheticRecord (w i).1 (w i).2) := by rw [hpair]
    _ = Measure.pi (fun _ : Fin n =>
          (P.1.prod SyntheticCompletion.fairCoin).map
            (fun z => syntheticRecord z.1 z.2)) := by
      exact Measure.pi_map_pi (μ := fun _ : Fin n =>
        P.1.prod SyntheticCompletion.fairCoin)
        (f := fun _ z => syntheticRecord z.1 z.2)
        (fun _ => (measurable_of_finite _).aemeasurable)
    _ = Measure.pi (fun _ : Fin n => P.1.bind syntheticOneRecord) := by
      congr 1
      funext i
      rw [← SyntheticCompletion.bind_map_eq_prod_map P.1
        SyntheticCompletion.fairCoin syntheticRecord (measurable_of_finite _)]
      apply Measure.bind_congr_right
      filter_upwards [] with r
      simpa [SyntheticCompletion.fairCoin] using
        (syntheticOneRecord_eq_coin_map r).symm

-- @node: syntheticOneRecord_probability
/-- Given [the specified inputs and assumptions](hyp:d,r), [the stated mathematical conclusion holds](goal). -/
lemma syntheticOneRecord_probability {d : ℕ} (r : ZengRecord d) :
    IsProbabilityMeasure (syntheticOneRecord r) := by
  refine ⟨?_⟩
  simp [syntheticOneRecord]
  exact ENNReal.inv_two_add_inv_two

-- @node: syntheticProductLaw_probability
/-- Given [the specified inputs and assumptions](hyp:n,d,s), [the stated mathematical conclusion holds](goal). -/
lemma syntheticProductLaw_probability {n d : ℕ}
    (s : Fin n → ZengRecord d) : IsProbabilityMeasure (syntheticProductLaw s) := by
  unfold syntheticProductLaw
  letI (i : Fin n) : IsProbabilityMeasure (syntheticOneRecord (s i)) :=
    syntheticOneRecord_probability (s i)
  infer_instance

-- @node: syntheticProductKernel
/-- For [the specified inputs and assumptions](hyp:n,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def syntheticProductKernel (n d : ℕ) :
    Kernel (Fin n → ZengRecord d) (Fin n → ObsRecord d) :=
  Kernel.ofFunOfCountable syntheticProductLaw

-- @node: syntheticProductKernel_isMarkovKernel
/-- For [the specified inputs and assumptions](hyp:n,d), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
instance syntheticProductKernel_isMarkovKernel (n d : ℕ) :
    IsMarkovKernel (syntheticProductKernel n d) where
  isProbabilityMeasure s := syntheticProductLaw_probability s

-- @node: syntheticPullbackEstimator
/-- For [the specified inputs and assumptions](hyp:n,d,T), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def syntheticPullbackEstimator {n d : ℕ} (T : Estimator n d) :
    ZengEstimator n d := by
  let K := syntheticProductKernel n d
  letI : IsMarkovKernel T.toBoundedKernel.1 := T.toBoundedKernel.2.1
  refine ⟨T.toBoundedKernel.1 ∘ₖ K, inferInstance, ?_⟩
  intro s
  rw [Kernel.comp_apply' _ _ _ (by simp)]
  simp only [T.toBoundedKernel.2.2]
  simp

/-- For [the specified inputs and assumptions](hyp:n,d,ε,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def thetaPoly (n d : ℕ) (ε : ℝ)
    (s : Fin n → ZengRecord d) : ℝ :=
  (∑ u : Fin n → Bool,
    mixedCountEstimator n d ε (fun i => syntheticRecord (s i) (u i))) / (2 : ℝ) ^ n
  -- @realizes \(\widehat\theta^{\mathrm{poly}}_{n,d,\epsilon}\)(fair-coin average)

-- @node: sampleLaw_iid
/-- Given [the specified inputs and assumptions](hyp:n,d,P), [the stated mathematical conclusion holds](goal). -/
lemma sampleLaw_iid (n : ℕ) {d : ℕ} (P : FullLaw d) :
    IIDSampling n (sampleLaw n P)
      (fun (i : Fin n) (s : Fin n → ObsRecord d) => s i) P := by
  let μ : Measure (ObsRecord d) := P.1.map obs
  letI : IsProbabilityMeasure P.1 := P.2
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable obs P.1)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fun_prop
  · simpa [sampleLaw, μ] using
      (iIndepFun_pi (μ := fun _ : Fin n => μ)
        (X := fun _ : Fin n => id) (by intro i; fun_prop))
  · intro i
    simpa [sampleLaw, μ] using
      (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq

-- @node: lem:synthetic-randomization-kernel
/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hq,hqhalf,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma synthetic_randomization_kernel {n d : ℕ} {q : ℝ}
    (hn : 1 ≤ n) (hq : 0 < q) (hqhalf : q < 1 / 2)
    (P : ZengLaw d) (hP : P ∈ zengDiscreteClass d q) :
    ∃ Pstar : FullLaw d,
      UnrestrictedArrivalModelClass n d q Pstar ∧
      IIDSampling n (sampleLaw n Pstar)
        (fun (i : Fin n) (s : Fin n → ObsRecord d) => s i) Pstar ∧
      (zengSampleLaw n P).bind syntheticProductLaw = sampleLaw n Pstar ∧
      ate Pstar = zengATE P := by
  refine ⟨SyntheticCompletion.fullLaw P, ?_, sampleLaw_iid n _, ?_, ?_⟩
  · exact
      { n_pos := hn
        d_pos := hP.2.2.1
        q_pos := hq
        q_le_one := by linarith
        randomized := SyntheticCompletion.fullLaw_randomized P
        balanced := SyntheticCompletion.fullLaw_balanced P
        surrogate := SyntheticCompletion.fullLaw_surrogate P
        outcome := SyntheticCompletion.fullLaw_outcome P
        mar := SyntheticCompletion.fullLaw_mar P
        arrival := SyntheticCompletion.fullLaw_arrival P hP }
  · rw [sampleLaw, syntheticSample_bind_eq_pi]
    congr 1
    funext i
    exact (SyntheticCompletion.observedLaw_eq_bind P hP).symm
  · exact SyntheticCompletion.fullLaw_ate hn hq hqhalf P hP

-- @node: syntheticPullbackEstimator_risk_eq
/-- Given [the specified inputs and assumptions](hyp:n,d,T,P,Pstar,hsample,htarget), [the stated mathematical conclusion holds](goal). -/
lemma syntheticPullbackEstimator_risk_eq {n d : ℕ}
    (T : Estimator n d) (P : ZengLaw d) (Pstar : FullLaw d)
    (hsample : (zengSampleLaw n P).bind syntheticProductLaw = sampleLaw n Pstar)
    (htarget : ate Pstar = zengATE P) :
    zengSquaredRisk (syntheticPullbackEstimator T) P =
      squaredRisk T Pstar := by
  letI : IsProbabilityMeasure Pstar.1 := Pstar.2
  letI : IsProbabilityMeasure (Pstar.1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (sampleLaw n Pstar) := by
    unfold sampleLaw
    infer_instance
  have hF : Integrable
      (fun s : Fin n → ObsRecord d =>
        ∫ t, (t - ate Pstar) ^ 2 ∂T.toBoundedKernel.1 s)
      (sampleLaw n Pstar) := Integrable.of_finite
  unfold zengSquaredRisk squaredRisk
  rw [← htarget]
  rw [← hsample]
  have hmeas : Measurable (syntheticProductLaw (n := n) (d := d)) :=
    (syntheticProductKernel n d).measurable
  have hFbind : Integrable
      (fun s : Fin n → ObsRecord d =>
        ∫ t, (t - ate Pstar) ^ 2 ∂T.toBoundedKernel.1 s)
      ((zengSampleLaw n P).bind syntheticProductLaw) := by
    rw [hsample]
    exact hF
  rw [Causalean.Mathlib.MeasureTheory.integral_bind hmeas hFbind]
  congr 1
  funext s
  letI : IsMarkovKernel T.toBoundedKernel.1 := T.toBoundedKernel.2.1
  letI : IsProbabilityMeasure (syntheticProductLaw s) :=
    syntheticProductLaw_probability s
  letI : IsProbabilityMeasure (T.toBoundedKernel.1 ∘ₘ syntheticProductLaw s) := by
    infer_instance
  have hsupp : (T.toBoundedKernel.1 ∘ₘ syntheticProductLaw s) (Set.Icc (-1 : ℝ) 1) = 1 := by
    rw [Measure.bind_apply measurableSet_Icc T.toBoundedKernel.1.measurable.aemeasurable]
    simp only [T.toBoundedKernel.2.2]
    simp
  have hlossInt : Integrable (fun t : ℝ => (t - ate Pstar) ^ 2)
      (T.toBoundedKernel.1 ∘ₘ syntheticProductLaw s) := by
    refine (integrable_const ((1 + |ate Pstar|) ^ 2)).mono'
      ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [(mem_ae_iff_prob_eq_one measurableSet_Icc).2 hsupp] with t ht
    rcases ht with ⟨htlo, hthi⟩
    have htAbs : |t| ≤ 1 := abs_le.mpr ⟨htlo, hthi⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq]
    have hnonneg : 0 ≤ (1 : ℝ) + |ate Pstar| := by positivity
    rw [abs_of_nonneg hnonneg]
    calc
      |t - ate Pstar| ≤ |t| + |ate Pstar| := abs_sub _ _
      _ ≤ 1 + |ate Pstar| := add_le_add_left htAbs _
  simpa [syntheticPullbackEstimator, syntheticProductKernel,
    Kernel.comp_apply, Kernel.ofFunOfCountable] using
    (ProbabilityTheory.Kernel.integral_comp
      (κ := Kernel.ofFunOfCountable syntheticProductLaw) (η := T.toBoundedKernel.1)
      (a := s) (f := fun t : ℝ => (t - ate Pstar) ^ 2) hlossInt)

end CausalSmith.Stat.MarRareqLogfrontier
