import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Estimator
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.UniformGuardBounds
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.TSharpExactMassThresholdInterval
import Causalean.PO.ID.Partial.Inference.Basic
import Causalean.Stat.EmpiricalProcess.CrossFitRate

/-!
# Uniform deterministic guard

Finite-support concentration and deterministic Lipschitz bounds yield uniform
endpoint consistency and conservative containment of the entire identified
interval, without a direction-separation condition or any cited gate.
-/

open MeasureTheory Filter Topology
open Causalean PO Causalean.Stat

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

variable {Λ 𝒳 Ω : Type*} [Nonempty Λ] [Fintype 𝒳] [DecidableEq 𝒳] [Nonempty 𝒳]
  [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [MeasurableSpace Ω]
variable {K : ℕ}

/-- The uniform slate family condition is the stated property of the slate-benefit partial-transport model. -/
def UniformSlateFamily (Psys : Λ → POSystem)
    (Sys : ∀ law, POSlateSystem (Psys law) 𝒳 K)
    (μ : Λ → Measure Ω)
    (O : Λ → ℕ → Ω → ObservedDatum 𝒳 K)
    (εZ mstar : ℝ) (d : Λ → 𝒳 → Bool) : Prop :=
  ∀ law n, ∀ hn : 1 ≤ n,
    let _ : StandardBorelSpace (Psys law).Ω := (Sys law).borel
    PositiveUniformInferenceLawClass (μ := μ law) (Sys law) εZ mstar (d law) n hn
      (O law)
  -- @realizes \mathcal P_n(fixed-constant margin-free triangular-array law class)

private noncomputable def endpointError (target : ℝ × ℝ)
    (O : ℕ → Ω → ObservedDatum 𝒳 K) (η : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  max |(plugInEndpoints O η n ω).1 - target.1|
    |(plugInEndpoints O η n ω).2 - target.2|

/-- The alpha-indexed capped guard gives every-sample uniform coverage, fixed-alpha uniform endpoint consistency, its deterministic rate, and the stated slowly diverging screening specialization. Given [the stated hypotheses](hyp:Sys,hAlpha,_hOverlapDomain,_hmstar,_hEtaPositive,_hSqrtEta), [the stated conclusion follows](goal). -/
-- @node: thm:uniform-deterministic-guard
theorem uniform_deterministic_guard
    (Psys : Λ → POSystem) (Sys : ∀ law, POSlateSystem (Psys law) 𝒳 K)
    (μ : Λ → Measure Ω)
    (O : Λ → ℕ → Ω → ObservedDatum 𝒳 K)
    (ξ : Λ → ℕ → Ω → ℝ)
    (η : ℕ → ℝ) (εZ mstar α : ℝ) (d : Λ → 𝒳 → Bool)
    (hAlpha : 0 < α ∧ α < 1)
    (_hOverlapDomain : 0 < εZ ∧ εZ < (1 : ℝ) / 2) (_hmstar : 0 < mstar)
    (_hEtaPositive : ∀ n, 0 < η n)
    (_hEtaZero : Tendsto η atTop (𝓝 0))
    (_hSqrtEta : Tendsto (fun n : ℕ => Real.sqrt n * η n) atTop atTop)
    (_hUniformClass : UniformSlateFamily Psys Sys μ O εZ mstar d) :
    let hK : 3 ≤ K := (Sys (Classical.choice inferInstance)).hK
    (∀ n, (hn : 1 ≤ n) →
      1 - α ≤ sInf {q : ℝ | ∃ law,
        let _ : StandardBorelSpace (Psys law).Ω := (Sys law).borel
        let cls := _hUniformClass law n hn
        let c := observableCapacities (Sys law).observedLaw
        let ident := capacity_identification (Sys law) εZ (d law) cls.ivIndependence
          cls.treatmentConsistency cls.selectionExclusion cls.outcomeExclusion
          cls.instrumentOverlap cls.noDefiers cls.weakSelectionMonotonicity
        let hValid : ValidCapacities c := ident.1.2
        let hp : ∀ x, 0 ≤ (Sys law).p x := ident.2.1
        let hMass : 0 < c.aggregateMass (Sys law).p := lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2
        q = (μ law).real {ω |
          c.identifiedIcc (Sys law).p (Sys law).observedLaw rfl
            (p_eq_observedCellWeights (Sys law)) hValid hp hMass
            (observedLawDomain (Sys law)) ⊆
            guardedConfidenceInterval (O law) (ξ law) η mstar εZ α hAlpha
              _hmstar _hOverlapDomain n hK hn (_hEtaPositive n) ω}}) ∧
    Tendsto
      (fun n => if hn : 1 ≤ n then sSup {q : ℝ | ∃ law,
          let _ : StandardBorelSpace (Psys law).Ω := (Sys law).borel
          let cls := _hUniformClass law n hn
          let c := observableCapacities (Sys law).observedLaw
          let ident := capacity_identification (Sys law) εZ (d law) cls.ivIndependence
            cls.treatmentConsistency cls.selectionExclusion cls.outcomeExclusion
            cls.instrumentOverlap cls.noDefiers cls.weakSelectionMonotonicity
          let hValid : ValidCapacities c := ident.1.2
          let hp : ∀ x, 0 ≤ (Sys law).p x := ident.2.1
          let hMass : 0 < c.aggregateMass (Sys law).p := lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2
          q = (μ law).real {ω |
            guardRadius 𝒳 K n η mstar εZ α hK hn (_hEtaPositive n) _hmstar
              _hOverlapDomain hAlpha <
              endpointError (c.endpointMap (Sys law).p (Sys law).observedLaw rfl
                (p_eq_observedCellWeights (Sys law)) hValid hp hMass
                (observedLawDomain (Sys law))).endpoints
                (O law) η n ω}} else 0)
      atTop (𝓝 0) ∧
    (fun n : ℕ => if hn : 1 ≤ n then
      guardRadius 𝒳 K n η mstar εZ α hK hn (_hEtaPositive n)
        _hmstar _hOverlapDomain hAlpha else 1) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) + η n) ∧
    (∀ L : ℕ → ℝ, (hLPositive : ∀ n, 0 < L n) → Tendsto L atTop atTop →
      L =o[atTop] (fun n : ℕ => Real.sqrt n) →
      let ηL := fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * L n
      (∀ n, 1 ≤ n → 0 < ηL n) ∧ Tendsto ηL atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.sqrt n * ηL n) atTop atTop ∧
      (fun n : ℕ => if hn : 1 ≤ n then
          guardRadius 𝒳 K n ηL mstar εZ α hK hn (by
            dsimp [ηL]
            have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
            have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnNat
            exact mul_pos (Real.rpow_pos_of_pos hnReal _) (hLPositive n))
            _hmstar _hOverlapDomain hAlpha
        else 1) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * L n)) := by
  dsimp only
  have hdet (law : Λ) (n : ℕ) (hn : 1 ≤ n)
      (hprob : IsProbabilityMeasure (Sys law).observedLaw)
      (hvalidE : ValidCapacities (observableCapacities (Sys law).observedLaw))
      (hpE : ∀ x, 0 ≤ (Sys law).p x)
      (hpObsE : (Sys law).p =
        Capacities.observedCellWeights (Sys law).observedLaw)
      (hmassE : 0 < (observableCapacities (Sys law).observedLaw).aggregateMass
        (Sys law).p)
      (ω : Ω) (δ : ℝ) (hδ : 0 ≤ δ)
      (hdev : maxDeviation (O law) (Sys law).observedLaw n ω ≤ δ) :
      (endpointError ((observableCapacities (Sys law).observedLaw).endpointMap
          (Sys law).p (Sys law).observedLaw rfl
          hpObsE hvalidE hpE hmassE (observedLawDomain (Sys law))).endpoints
          (O law) η n ω ≤
        min 1 (4 * (64 * (K : ℝ) * Fintype.card 𝒳 / εZ ^ 2 * δ +
          Fintype.card 𝒳 * η n) / mstar)) ∧
      (4 * (64 * (K : ℝ) * Fintype.card 𝒳 / εZ ^ 2 * δ +
          Fintype.card 𝒳 * η n) < mstar →
        endpointError ((observableCapacities (Sys law).observedLaw).endpointMap
          (Sys law).p (Sys law).observedLaw rfl
          hpObsE hvalidE hpE hmassE (observedLawDomain (Sys law))).endpoints
          (O law) η n ω ≤
        3 * (64 * (K : ℝ) * Fintype.card 𝒳 / εZ ^ 2 * δ +
          Fintype.card 𝒳 * η n) / mstar) := by
    letI : StandardBorelSpace (Psys law).Ω := (Sys law).borel
    letI : IsProbabilityMeasure (Sys law).observedLaw := hprob
    let cls := _hUniformClass law n hn
    have ident := capacity_identification (Sys law) εZ (d law) cls.ivIndependence
      cls.treatmentConsistency cls.selectionExclusion cls.outcomeExclusion
      cls.instrumentOverlap cls.noDefiers cls.weakSelectionMonotonicity
    have hpEq : (Sys law).p = fun x => (Sys law).observedLaw.real {o | o.cell = x} := by
      funext x
      exact (observedLaw_cell_real (Sys law) x).symm
    have hover : ∀ x z, εZ * (Sys law).observedLaw.real {o | o.cell = x} ≤
        (Sys law).observedLaw.real {o | o.cell = x ∧ o.instrument = z} := by
      intro x z
      rw [observedLaw_cell_real (Sys law) x]
      exact observedLaw_arm_ge_overlap (Sys law) cls.instrumentOverlap x z
    have hcore := plugInEndpoints_error_le_of_maxDeviation
      (O law) (Sys law).observedLaw (observedLawDomain (Sys law))
      n ω (η n) mstar εZ δ
      (_hEtaPositive n) _hmstar _hOverlapDomain.1 _hOverlapDomain.2
      hover ident.1.2 (by simpa [hpEq] using cls.uniformAggregateSurvivorBound.2)
      hδ hdev
    have hplug : plugInEndpoints (O law) η n ω =
        plugInEndpoints (O law) (fun _ => η n) n ω := by
      unfold plugInEndpoints screenedCell
      rfl
    unfold endpointError Capacities.endpointMap
    rw [hplug, hpEq]
    exact hcore
  let targetEndpoint (law : Λ) (n : ℕ) (hn : 1 ≤ n) : ℝ × ℝ :=
    let _ : StandardBorelSpace (Psys law).Ω := (Sys law).borel
    let cls := _hUniformClass law n hn
    let ident := capacity_identification (Sys law) εZ (d law) cls.ivIndependence
      cls.treatmentConsistency cls.selectionExclusion cls.outcomeExclusion
      cls.instrumentOverlap cls.noDefiers cls.weakSelectionMonotonicity
    ((observableCapacities (Sys law).observedLaw).endpointMap (Sys law).p
      (Sys law).observedLaw rfl (p_eq_observedCellWeights (Sys law))
      ident.1.2 ident.2.1
      (lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2)
      (observedLawDomain (Sys law))).endpoints
  refine ⟨?_, ?_⟩
  · intro n hn
    apply le_csInf
    · let law : Λ := Classical.choice inferInstance
      letI : StandardBorelSpace (Psys law).Ω := (Sys law).borel
      refine ⟨(μ law).real {ω |
        let cls := _hUniformClass law n hn
        let c := observableCapacities (Sys law).observedLaw
        let ident := capacity_identification (Sys law) εZ (d law) cls.ivIndependence
          cls.treatmentConsistency cls.selectionExclusion cls.outcomeExclusion
          cls.instrumentOverlap cls.noDefiers cls.weakSelectionMonotonicity
        let hValid : ValidCapacities c := ident.1.2
        let hp : ∀ x, 0 ≤ (Sys law).p x := ident.2.1
        let hMass : 0 < c.aggregateMass (Sys law).p :=
          lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2
        c.identifiedIcc (Sys law).p (Sys law).observedLaw rfl
          (p_eq_observedCellWeights (Sys law)) hValid hp hMass
          (observedLawDomain (Sys law)) ⊆
          guardedConfidenceInterval (O law) (ξ law) η mstar εZ α hAlpha
            _hmstar _hOverlapDomain n (Sys (Classical.choice inferInstance)).hK hn
            (_hEtaPositive n) ω}, law, rfl⟩
    · intro q hq
      rcases hq with ⟨law, rfl⟩
      letI : StandardBorelSpace (Psys law).Ω := (Sys law).borel
      let cls := _hUniformClass law n hn
      have ident := capacity_identification (Sys law) εZ (d law) cls.ivIndependence
        cls.treatmentConsistency cls.selectionExclusion cls.outcomeExclusion
        cls.instrumentOverlap cls.noDefiers cls.weakSelectionMonotonicity
      letI : IsProbabilityMeasure (Sys law).observedLaw := ident.1.1
      letI : IsProbabilityMeasure (μ law) := cls.iidSampling.isProbabilityMeasure
      let b := unionThreshold 𝒳 K n α
      have hb0 : 0 ≤ b := Real.sqrt_nonneg _
      have htail : (μ law).real {ω |
          b < maxDeviation (O law) (Sys law).observedLaw n ω} ≤ α := by
        exact maxDeviation_unionThreshold_tail_le (O law) (Sys law).observedLaw
          cls.iidSampling hn hAlpha.1
      have hO : ∀ i, i < n → Measurable (O law i) := by
        intro i hi
        exact cls.iidSampling.measurable i hi
      have hmaxmeas := measurable_maxDeviation_of_prefix (O law)
        (Sys law).observedLaw hO
      have hsubset : {ω | maxDeviation (O law) (Sys law).observedLaw n ω ≤ b} ⊆
          {ω |
            let c := observableCapacities (Sys law).observedLaw
            let hValid : ValidCapacities c := ident.1.2
            let hp : ∀ x, 0 ≤ (Sys law).p x := ident.2.1
            let hMass : 0 < c.aggregateMass (Sys law).p :=
              lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2
            c.identifiedIcc (Sys law).p (Sys law).observedLaw rfl
              (p_eq_observedCellWeights (Sys law)) hValid hp hMass
              (observedLawDomain (Sys law)) ⊆
              guardedConfidenceInterval (O law) (ξ law) η mstar εZ α hAlpha
                _hmstar _hOverlapDomain n (Sys (Classical.choice inferInstance)).hK
                hn (_hEtaPositive n) ω} := by
        intro ω hgood
        dsimp only
        have herr := (hdet law n hn ident.1.1 ident.1.2 ident.2.1
          (p_eq_observedCellWeights (Sys law))
          (lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2)
          ω b hb0 hgood).1
        have hguard : min 1 (4 * (64 * (K : ℝ) * Fintype.card 𝒳 /
            εZ ^ 2 * b + Fintype.card 𝒳 * η n) / mstar) =
            guardRadius 𝒳 K n η mstar εZ α
              (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
              _hmstar _hOverlapDomain hAlpha := by
          rfl
        rw [hguard] at herr
        have hbds := endpointMap_bounds (Sys law).observedLaw (Sys law).p
          (observableCapacities (Sys law).observedLaw) rfl
          (p_eq_observedCellWeights (Sys law)) ident.2.1 ident.1.2
          (lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2)
          (observedLawDomain (Sys law))
        intro y hy
        unfold Capacities.identifiedIcc Capacities.endpointMap at hy
        unfold guardedConfidenceInterval guardedConfidenceSet
        dsimp only [GuardedInferenceHandle.confidenceSet]
        let ψ := plugInEndpoints (O law) η n ω
        let θ := ((observableCapacities (Sys law).observedLaw).endpointMap
          (Sys law).p (Sys law).observedLaw rfl
          (p_eq_observedCellWeights (Sys law)) ident.1.2 ident.2.1
          (lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2)
          (observedLawDomain (Sys law))).endpoints
        let g := guardRadius 𝒳 K n η mstar εZ α
          (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
          _hmstar _hOverlapDomain hAlpha
        have hL : |ψ.1 - θ.1| ≤ g :=
          (le_max_left _ _).trans herr
        have hU : |ψ.2 - θ.2| ≤ g :=
          (le_max_right _ _).trans herr
        change max 0 (ψ.1 - g) ≤ y ∧ y ≤ min 1 (ψ.2 + g)
        change θ.1 ≤ y ∧ y ≤ θ.2 at hy
        change 0 ≤ θ.1 ∧ θ.1 ≤ 1 ∧ 0 ≤ θ.2 ∧ θ.2 ≤ 1 at hbds
        constructor
        · apply max_le
          · exact hbds.1.trans hy.1
          · rw [abs_le] at hL
            linarith
        · apply le_min
          · exact hy.2.trans hbds.2.2.2
          · rw [abs_le] at hU
            linarith
      have hmeasure : (μ law).real
          {ω | maxDeviation (O law) (Sys law).observedLaw n ω ≤ b} ≤
          (μ law).real {ω |
            let c := observableCapacities (Sys law).observedLaw
            let hValid : ValidCapacities c := ident.1.2
            let hp : ∀ x, 0 ≤ (Sys law).p x := ident.2.1
            let hMass : 0 < c.aggregateMass (Sys law).p :=
              lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2
            c.identifiedIcc (Sys law).p (Sys law).observedLaw rfl
              (p_eq_observedCellWeights (Sys law)) hValid hp hMass
              (observedLawDomain (Sys law)) ⊆
              guardedConfidenceInterval (O law) (ξ law) η mstar εZ α hAlpha
                _hmstar _hOverlapDomain n (Sys (Classical.choice inferInstance)).hK
                hn (_hEtaPositive n) ω} := by
        apply measureReal_mono
        · exact hsubset
        · exact measure_ne_top _ _
      have hbadmeas : MeasurableSet {ω |
          b < maxDeviation (O law) (Sys law).observedLaw n ω} :=
        measurableSet_lt measurable_const hmaxmeas
      have hcomp : {ω | maxDeviation (O law) (Sys law).observedLaw n ω ≤ b} =
          ({ω | b < maxDeviation (O law) (Sys law).observedLaw n ω})ᶜ := by
        ext ω
        simp
      rw [hcomp, measureReal_compl hbadmeas, probReal_univ] at hmeasure
      linarith
  refine ⟨?_, ?_, ?_⟩
  · let R : ℝ := 64 * (K : ℝ) * Fintype.card 𝒳 / εZ ^ 2
    let S : ℝ := Fintype.card 𝒳
    let c0 : ℝ := S / (4 * R)
    let t : ℕ → ℝ := fun n => c0 * η n
    let r : ℕ → ℝ := fun n => (guardEvents 𝒳 K).card /
      (4 * (n : ℝ) * (t n) ^ 2)
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) (Sys (Classical.choice inferInstance)).hK)
    have hS : 0 < S := by
      dsimp [S]
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hR : 0 < R := by
      dsimp [R]
      exact div_pos (mul_pos (mul_pos (by norm_num) hKpos) hS)
        (sq_pos_of_pos _hOverlapDomain.1)
    have hc0 : 0 < c0 := by dsimp [c0]; positivity
    have htpos : ∀ n, 0 < t n := fun n => mul_pos hc0 (_hEtaPositive n)
    have hAtZero : Tendsto
        (fun n => 4 * (R * t n + S * η n)) atTop (𝓝 0) := by
      have heq : (fun n => 4 * (R * t n + S * η n)) =
          fun n => (5 * S) * η n := by
        funext n
        dsimp [t, c0]
        field_simp [hR.ne']
        ring
      rw [heq]
      simpa using tendsto_const_nhds.mul _hEtaZero
    have hsmall : ∀ᶠ n in atTop, 4 * (R * t n + S * η n) < mstar :=
      (tendsto_order.1 hAtZero).2 _ _hmstar
    have hr0 : Tendsto r atTop (𝓝 0) := by
      exact inverse_sqrtEta_tail_tendsto_zero η hc0 _hSqrtEta
    apply squeeze_zero'
    · apply Filter.Eventually.of_forall
      intro n
      by_cases hn : 1 ≤ n
      · simp only [dif_pos hn]
        let law : Λ := Classical.choice inferInstance
        let q : ℝ := (μ law).real {ω |
            guardRadius 𝒳 K n η mstar εZ α
              (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
              _hmstar _hOverlapDomain hAlpha <
            endpointError (targetEndpoint law n hn) (O law) η n ω}
        have hbounded : BddAbove {q : ℝ | ∃ law,
            q = (μ law).real {ω |
              guardRadius 𝒳 K n η mstar εZ α
                (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
                _hmstar _hOverlapDomain hAlpha <
              endpointError (targetEndpoint law n hn) (O law) η n ω}} := by
          refine ⟨1, ?_⟩
          intro q hq
          rcases hq with ⟨law, rfl⟩
          letI : StandardBorelSpace (Psys law).Ω := (Sys law).borel
          let cls := _hUniformClass law n hn
          letI : IsProbabilityMeasure (μ law) := cls.iidSampling.isProbabilityMeasure
          exact measureReal_le_one
        exact measureReal_nonneg.trans (le_csSup hbounded (show q ∈ {q : ℝ | ∃ law,
          q = (μ law).real {ω |
            guardRadius 𝒳 K n η mstar εZ α
              (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
              _hmstar _hOverlapDomain hAlpha <
            endpointError (targetEndpoint law n hn) (O law) η n ω}} by exact ⟨law, rfl⟩))
      · simp [hn]
    · filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hnsmall
      simp only [dif_pos hn]
      apply csSup_le
      · let law : Λ := Classical.choice inferInstance
        exact ⟨(μ law).real {ω |
          guardRadius 𝒳 K n η mstar εZ α
            (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
            _hmstar _hOverlapDomain hAlpha <
          endpointError (targetEndpoint law n hn) (O law) η n ω}, ⟨law, rfl⟩⟩
      · intro q hq
        rcases hq with ⟨law, rfl⟩
        letI : StandardBorelSpace (Psys law).Ω := (Sys law).borel
        let cls := _hUniformClass law n hn
        have ident := capacity_identification (Sys law) εZ (d law) cls.ivIndependence
          cls.treatmentConsistency cls.selectionExclusion cls.outcomeExclusion
          cls.instrumentOverlap cls.noDefiers cls.weakSelectionMonotonicity
        letI : IsProbabilityMeasure (Sys law).observedLaw := ident.1.1
        letI : IsProbabilityMeasure (μ law) := cls.iidSampling.isProbabilityMeasure
        have hsub : {ω |
            guardRadius 𝒳 K n η mstar εZ α
              (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
              _hmstar _hOverlapDomain hAlpha <
              endpointError (targetEndpoint law n hn) (O law) η n ω} ⊆
            {ω | t n < maxDeviation (O law) (Sys law).observedLaw n ω} := by
          intro ω hviol
          by_contra hnot
          have hgood : maxDeviation (O law) (Sys law).observedLaw n ω ≤ t n :=
            le_of_not_gt hnot
          have hd := hdet law n hn ident.1.1 ident.1.2 ident.2.1
            (p_eq_observedCellWeights (Sys law))
            (lt_of_lt_of_le _hmstar cls.uniformAggregateSurvivorBound.2)
            ω (t n) (htpos n).le hgood
          have hs := hd.2 (by simpa [R, S] using hnsmall)
          have hweak := hd.1
          have hb0 : 0 ≤ unionThreshold 𝒳 K n α := Real.sqrt_nonneg _
          have hcompare : 3 * (R * t n + S * η n) / mstar ≤
              4 * (R * unionThreshold 𝒳 K n α + S * η n) / mstar := by
            apply (div_le_div_iff_of_pos_right _hmstar).2
            have htEq : R * t n = S * η n / 4 := by
              dsimp [t, c0]
              field_simp [hR.ne']
            rw [htEq]
            nlinarith [mul_nonneg hR.le hb0, mul_pos hS (_hEtaPositive n)]
          have herrGuard : endpointError (targetEndpoint law n hn) (O law) η n ω ≤
              min 1 (4 * (R * unionThreshold 𝒳 K n α + S * η n) / mstar) := by
            exact le_min (hweak.trans (min_le_left _ _)) (hs.trans hcompare)
          have hguardEq : min 1
              (4 * (R * unionThreshold 𝒳 K n α + S * η n) / mstar) =
              guardRadius 𝒳 K n η mstar εZ α
                (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
                _hmstar _hOverlapDomain hAlpha := by
            rfl
          rw [hguardEq] at herrGuard
          exact (not_lt_of_ge herrGuard) hviol
        have hmeasure : (μ law).real {ω |
            guardRadius 𝒳 K n η mstar εZ α
              (Sys (Classical.choice inferInstance)).hK hn (_hEtaPositive n)
              _hmstar _hOverlapDomain hAlpha <
              endpointError (targetEndpoint law n hn) (O law) η n ω} ≤
            (μ law).real {ω | t n <
              maxDeviation (O law) (Sys law).observedLaw n ω} := by
          apply measureReal_mono
          · exact hsub
          · exact measure_ne_top _ _
        exact hmeasure.trans (by
          exact maxDeviation_tail_le (O law) (Sys law).observedLaw cls.iidSampling
            (lt_of_lt_of_le Nat.zero_lt_one hn) (t n) (htpos n))
    · exact hr0
  · let R : ℝ := 64 * (K : ℝ) * Fintype.card 𝒳 / εZ ^ 2
    let S : ℝ := Fintype.card 𝒳
    let B : ℝ := Real.sqrt ((guardEvents 𝒳 K).card / (4 * α))
    let C : ℝ := 4 * (R * B + S) / mstar
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnNat
    have hrate : 0 < (n : ℝ) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hnR _
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    have hKpos : 0 < (K : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3)
        (Sys (Classical.choice inferInstance)).hK)
    have hS : 0 < S := by
      dsimp [S]
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hR : 0 < R := by
      dsimp [R]
      exact div_pos (mul_pos (mul_pos (by norm_num) hKpos) hS)
        (sq_pos_of_pos _hOverlapDomain.1)
    have hthreshold : unionThreshold 𝒳 K n α =
        B * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      have hα0 := hAlpha.1
      unfold unionThreshold
      rw [show ((guardEvents 𝒳 K).card : ℝ) / (4 * (n : ℝ) * α) =
          ((guardEvents 𝒳 K).card : ℝ) / (4 * α) / (n : ℝ) by field_simp]
      rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [div_eq_mul_inv]
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hnR.le]
      change _ = Real.sqrt ((guardEvents 𝒳 K).card / (4 * α)) * _
      rw [Real.sqrt_eq_rpow]
    simp only [dif_pos hn]
    unfold guardRadius errorEnvelope
    rw [hthreshold]
    have henv : 0 ≤ R * (B * (n : ℝ) ^ (-(1 : ℝ) / 2)) + S * η n :=
      add_nonneg (mul_nonneg hR.le (mul_nonneg hB hrate.le))
        (mul_nonneg hS.le (_hEtaPositive n).le)
    change |min 1 (4 * (R * (B * (n : ℝ) ^ (-(1 : ℝ) / 2)) + S * η n) /
      mstar)| ≤ C * |(n : ℝ) ^ (-(1 : ℝ) / 2) + η n|
    rw [abs_of_nonneg (le_min zero_le_one (div_nonneg (mul_nonneg (by norm_num) henv)
      _hmstar.le)), abs_of_pos (add_pos hrate (_hEtaPositive n))]
    apply (min_le_right _ _).trans
    change (4 * (R * (B * (n : ℝ) ^ (-(1 : ℝ) / 2)) + S * η n)) / mstar ≤
      C * ((n : ℝ) ^ (-(1 : ℝ) / 2) + η n)
    calc
      _ ≤ (4 * (R * B + S) * ((n : ℝ) ^ (-(1 : ℝ) / 2) + η n)) / mstar := by
        apply (div_le_div_iff_of_pos_right _hmstar).2
        nlinarith [mul_nonneg (mul_nonneg hR.le hB) (_hEtaPositive n).le,
          mul_nonneg hS.le hrate.le]
      _ = _ := by dsimp [C]; ring
  · intro L hLPositive hLTop hLittle
    let ηL : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 : ℝ) / 2) * L n
    have hηLPositive : ∀ n, 1 ≤ n → 0 < ηL n := by
      intro n hn
      have hnR : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      exact mul_pos (Real.rpow_pos_of_pos hnR _) (hLPositive n)
    refine ⟨hηLPositive, ?_, ?_, ?_⟩
    · have hdiv := hLittle.tendsto_div_nhds_zero
      apply hdiv.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm]
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hnR.le]
    · apply hLTop.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      rw [Real.sqrt_eq_rpow]
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hnR.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hnR _)]
    · let R : ℝ := 64 * (K : ℝ) * Fintype.card 𝒳 / εZ ^ 2
      let S : ℝ := Fintype.card 𝒳
      let B : ℝ := Real.sqrt ((guardEvents 𝒳 K).card / (4 * α))
      let C : ℝ := 4 * (R * B + S) / mstar
      rw [Asymptotics.isBigO_iff]
      refine ⟨2 * C, ?_⟩
      filter_upwards [eventually_ge_atTop 1, hLTop.eventually_ge_atTop 1] with n hn hLn
      have hnNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hnNat
      have hrate : 0 < (n : ℝ) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_pos_of_pos hnR _
      have hηpos : 0 < ηL n := hηLPositive n hn
      have hB : 0 ≤ B := Real.sqrt_nonneg _
      have hKpos : 0 < (K : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3)
          (Sys (Classical.choice inferInstance)).hK)
      have hS : 0 < S := by
        dsimp [S]
        exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
      have hR : 0 < R := by
        dsimp [R]
        exact div_pos (mul_pos (mul_pos (by norm_num) hKpos) hS)
          (sq_pos_of_pos _hOverlapDomain.1)
      have hC : 0 < C := by
        dsimp [C]
        exact div_pos (mul_pos (by norm_num)
          (add_pos_of_nonneg_of_pos (mul_nonneg hR.le hB) hS)) _hmstar
      have hα0 : 0 < α := hAlpha.1
      have hthreshold : unionThreshold 𝒳 K n α =
          B * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
        unfold unionThreshold
        rw [show ((guardEvents 𝒳 K).card : ℝ) / (4 * (n : ℝ) * α) =
            ((guardEvents 𝒳 K).card : ℝ) / (4 * α) / (n : ℝ) by field_simp]
        rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        rw [div_eq_mul_inv]
        rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hnR.le]
        change _ = Real.sqrt ((guardEvents 𝒳 K).card / (4 * α)) * _
        rw [Real.sqrt_eq_rpow]
      simp only [dif_pos hn]
      unfold guardRadius errorEnvelope
      rw [hthreshold]
      have henv : 0 ≤ R * (B * (n : ℝ) ^ (-(1 : ℝ) / 2)) + S * ηL n :=
        add_nonneg (mul_nonneg hR.le (mul_nonneg hB hrate.le))
          (mul_nonneg hS.le hηpos.le)
      change |min 1 (4 * (R * (B * (n : ℝ) ^ (-(1 : ℝ) / 2)) + S * ηL n) /
        mstar)| ≤ (2 * C) * |ηL n|
      rw [abs_of_nonneg (le_min zero_le_one (div_nonneg (mul_nonneg (by norm_num) henv)
        _hmstar.le)), abs_of_pos hηpos]
      apply (min_le_right _ _).trans
      calc
        _ ≤ C * ((n : ℝ) ^ (-(1 : ℝ) / 2) + ηL n) := by
          change (4 * (R * (B * (n : ℝ) ^ (-(1 : ℝ) / 2)) + S * ηL n)) /
            mstar ≤ C * ((n : ℝ) ^ (-(1 : ℝ) / 2) + ηL n)
          calc
            _ ≤ (4 * (R * B + S) *
                ((n : ℝ) ^ (-(1 : ℝ) / 2) + ηL n)) / mstar := by
              apply (div_le_div_iff_of_pos_right _hmstar).2
              nlinarith [mul_nonneg (mul_nonneg hR.le hB) hηpos.le,
                mul_nonneg hS.le hrate.le]
            _ = _ := by dsimp [C]; ring
        _ ≤ (2 * C) * ηL n := by
          have hrate_le : (n : ℝ) ^ (-(1 : ℝ) / 2) ≤ ηL n := by
            dsimp [ηL]
            nlinarith
          nlinarith [hC.le]

end CausalSmith.PartialID.SlateBenefitPartialTransport
