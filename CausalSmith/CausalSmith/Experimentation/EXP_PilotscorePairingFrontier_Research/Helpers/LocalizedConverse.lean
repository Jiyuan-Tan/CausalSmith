module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Converse

/-! # Cell-localized losses for the arbitrary-pairing converse -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open Causalean.Stat.Nonparametric.HistogramRegression

lemma measurableSet_of_isSideCube {d : ℕ} {h : ℝ} {Q : Set (XSpace d)}
    (hQ : IsSideCube h Q) : MeasurableSet Q := by
  rcases hQ with ⟨a, ha, rfl⟩
  unfold cube
  measurability

/-- The part of the matching loss whose first endpoint lies in a fixed cell. -/
@[no_expose]
noncomputable def localizedPairLoss {d N : ℕ} (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (x : MainCovariates N d) (M : Match N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N,
    Q.indicator (fun _ => (g (x i) - g (x (M.val i))) ^ 2) (x i)

lemma localizedPairLoss_nonneg {d N : ℕ} (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (x : MainCovariates N d) (M : Match N) :
    0 ≤ localizedPairLoss g Q x M := by
  unfold localizedPairLoss
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  by_cases hmem : x i ∈ Q
  · simp [Set.indicator_of_mem hmem, sq_nonneg]
  · simp [Set.indicator_of_notMem hmem]

lemma localizedPairLoss_le_pairLoss {d N : ℕ} (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (x : MainCovariates N d) (M : Match N) :
    localizedPairLoss g Q x M ≤ pairLoss g x M := by
  unfold localizedPairLoss pairLoss
  gcongr with i
  by_cases hi : x i ∈ Q
  · simp [Set.indicator_of_mem hi]
  · simp [Set.indicator_of_notMem hi, sq_nonneg]

/-- Pairwise-disjoint cells partition the localized summands, so their sum
never exceeds the full matching loss. -/
lemma sum_localizedPairLoss_le_pairLoss {d N K : ℕ}
    (g : XSpace d → ℝ) (Q : Fin K → Set (XSpace d))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (x : MainCovariates N d) (M : Match N) :
    (∑ j : Fin K, localizedPairLoss g (Q j) x M) ≤ pairLoss g x M := by
  classical
  unfold localizedPairLoss pairLoss
  rw [← Finset.mul_sum, Finset.sum_comm]
  gcongr with i
  by_cases hex : ∃ j : Fin K, x i ∈ Q j
  · obtain ⟨j, hj⟩ := hex
    have hzero : ∀ k : Fin K, k ≠ j →
        (Q k).indicator (fun _ => (g (x i) - g (x (M.val i))) ^ 2) (x i) = 0 := by
      intro k hkj
      apply Set.indicator_of_notMem
      intro hk
      exact Set.disjoint_left.mp (hdisj k j hkj) hk hj
    rw [Finset.sum_eq_single j]
    · simp [Set.indicator_of_mem hj]
    · intro k hk hkj
      exact hzero k hkj
    · simp
  · have hnone : ∀ j : Fin K, x i ∉ Q j := by
      intro j hj
      exact hex ⟨j, hj⟩
    simp [Set.indicator_of_notMem, hnone, sq_nonneg]

/-- On a singleton-core configuration, the two adjacent hypercube members
pay at least one squared amplitude in the localized cell losses. -/
lemma hypercube_flip_singleton_localizedPairLoss {d N K : ℕ}
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (Q S : Fin K → Set (XSpace d))
    (hSQ : ∀ j, S j ⊆ Q j)
    (hsupport : ∀ j y, y ∉ Q j → ψ j y = 0)
    (hcore : ∀ j y, y ∈ S j → ψ j y = 1)
    (θ : Fin K → Bool) (j : Fin K) (x : MainCovariates N d) (M : Match N)
    (i : Fin N) (hi : x i ∈ S j)
    (hunique : ∀ k : Fin N, x k ∈ Q j → k = i) :
    amplitude ^ 2 ≤ localizedPairLoss (g θ) (Q j) x M +
      localizedPairLoss (g (flipCoordinate θ j)) (Q j) x M := by
  classical
  let p : Fin N := M.val i
  have hip : i ≠ p := fun h => M.property.2 i h.symm
  have hpQ : x p ∉ Q j := by
    intro hp
    exact hip (hunique p hp).symm
  have hψi : ψ j (x i) = 1 := hcore j (x i) hi
  have hiQ : x i ∈ Q j := hSQ j hi
  have hψp : ψ j (x p) = 0 := hsupport j (x p) hpQ
  have hedge := hypercube_flip_edge_sq g base amplitude ψ hg θ j (x i) (x p)
  rw [hψi, hψp] at hedge
  have hθ : (1 / 2 : ℝ) *
      (g θ (x i) - g θ (x ((M.val i)))) ^ 2 ≤
      localizedPairLoss (g θ) (Q j) x M := by
    unfold localizedPairLoss
    let F : Fin N → ℝ := fun k => (Q j).indicator
      (fun _ => (g θ (x k) - g θ (x (M.val k))) ^ 2) (x k)
    have hF (k : Fin N) : 0 ≤ F k := by
      dsimp [F]
      by_cases hk : x k ∈ Q j
      · rw [Set.indicator_of_mem hk]
        exact sq_nonneg _
      · rw [Set.indicator_of_notMem hk]
    have hsum : F i ≤ ∑ k : Fin N, F k :=
      Finset.single_le_sum (fun k _ => hF k) (Finset.mem_univ i)
    dsimp [F] at hsum ⊢
    rw [Set.indicator_of_mem hiQ] at hsum
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hflip : (1 / 2 : ℝ) *
      (g (flipCoordinate θ j) (x i) -
        g (flipCoordinate θ j) (x ((M.val i)))) ^ 2 ≤
      localizedPairLoss (g (flipCoordinate θ j)) (Q j) x M := by
    unfold localizedPairLoss
    let F : Fin N → ℝ := fun k => (Q j).indicator (fun _ =>
      (g (flipCoordinate θ j) (x k) -
        g (flipCoordinate θ j) (x (M.val k))) ^ 2) (x k)
    have hF (k : Fin N) : 0 ≤ F k := by
      dsimp [F]
      by_cases hk : x k ∈ Q j
      · rw [Set.indicator_of_mem hk]
        exact sq_nonneg _
      · rw [Set.indicator_of_notMem hk]
    have hsum : F i ≤ ∑ k : Fin N, F k :=
      Finset.single_le_sum (fun k _ => hF k) (Finset.mem_univ i)
    dsimp [F] at hsum ⊢
    rw [Set.indicator_of_mem hiQ] at hsum
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  nlinarith

lemma localizedDesignRiskIntegrand_aestronglyMeasurable {d m N : ℕ}
    {L β cX CX cg Cg : ℝ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (hQ : MeasurableSet Q) (D : Design m N d)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg)
    (hX : P.map Prod.fst = cubeMeasure d) (hD : MatchingDesignClass D) :
    AEStronglyMeasurable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        localizedPairLoss g Q z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hmodel.covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hX]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  let target := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hcube : MeasurableSet (cube d) := by unfold cube; measurability
  let clamp : XSpace d → Cube d := fun x =>
    ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩
  have hclamp : Measurable clamp := by dsimp [clamp]; fun_prop
  let g' : XSpace d → ℝ := fun x => g (clamp x).val.ofLp
  have hg' : Measurable g' :=
    (measurable_paperCubeScore g hmodel.parameters.2.2.2.1
      hmodel.parameters.2.1 hmodel.holder_score).comp hclamp
  have hg'eq (x : XSpace d) (hx : x ∈ cube d) : g' x = g x := by
    dsimp [g']
    apply congrArg g
    funext i
    simp [clamp, max_eq_right (hx i).1, min_eq_right (hx i).2]
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem hcube
  have hmain : ∀ᵐ xs ∂Measure.pi (fun _ : Fin N => cubeMeasure d),
      ∀ i, xs i ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcubeae
  have htargetMain : ∀ᵐ z ∂target, ∀ i, z.2.1 i ∈ cube d := by
    dsimp [target]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with p
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmain] with xs hxs
    filter_upwards [] with u
    exact hxs
  have hinput : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  have hmap := latentTwoWaveLaw_map_designInput (m := m) (N := N) P
    hmodel.covariate_density.1 hX
  have hdom := latentTwoWaveLaw_designDomain_ae (m := m) (N := N) P g hmodel
  have htargetDom : ∀ᵐ z ∂target, z ∈ designDomain m N d := by
    change ∀ᵐ z ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)),
        z ∈ designDomain m N d
    rw [← hmap]
    exact (ae_map_iff hinput.aemeasurable
      (by unfold designDomain cube; measurability)).2 hdom
  have hDAE : AEMeasurable D target := by
    rw [← Measure.restrict_eq_self_of_ae_mem htargetDom]
    exact aemeasurable_restrict_of_measurable_subtype
      (by unfold designDomain cube; measurability) hD.2.1
  let scores : PilotSample m d × MainCovariates N d × ℝ → Fin N → ℝ :=
    fun z i => g' (z.2.1 i)
  have hscores : Measurable scores := by
    rw [measurable_pi_iff]
    intro i
    exact hg'.comp ((measurable_pi_apply i).comp
      (measurable_fst.comp measurable_snd))
  let main : PilotSample m d × MainCovariates N d × ℝ → MainCovariates N d :=
    fun z => z.2.1
  have hmainMeas : Measurable main := measurable_fst.comp measurable_snd
  have hPairMap : Measurable
      (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
        ((1 / 2 : ℝ) * ∑ i : Fin N,
          Q.indicator (fun _ => (t.1.1 i - t.1.1 (t.2.val i)) ^ 2)
            (t.1.2 i)) / (N : ℝ)) := by
    classical
    have hEval (i : Fin N) : Measurable
        (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
          t.1.1 (t.2.val i)) := by
      have heq : (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
          t.1.1 (t.2.val i)) =
          fun t => ∑ j : Fin N, if t.2.val i = j then t.1.1 j else 0 := by
        funext t
        simp
      rw [heq]
      apply Finset.measurable_sum
      intro j hj
      exact Measurable.ite
        ((measurableSet_singleton j).preimage
          ((measurable_from_top : Measurable (fun M : Match N => M.val i)).comp
            measurable_snd))
        ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
        measurable_const
    apply Measurable.div_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    have hterm : Measurable
        (fun t : ((Fin N → ℝ) × MainCovariates N d) × Match N =>
          (t.1.1 i - t.1.1 (t.2.val i)) ^ 2) :=
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).sub
        (hEval i)).pow_const 2
    exact hterm.indicator (hQ.preimage
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)))
  have hmeas' : AEMeasurable
      (fun z => localizedPairLoss g' Q z.2.1 (D z) / (N : ℝ)) target := by
    have hp := ((hscores.prodMk hmainMeas).aemeasurable.prodMk hDAE)
    convert hPairMap.comp_aemeasurable hp using 1
    funext z
    simp [scores, main, localizedPairLoss]
  refine hmeas'.aestronglyMeasurable.congr ?_
  filter_upwards [htargetMain] with z hz
  unfold localizedPairLoss
  apply congrArg (fun t : ℝ => t / (N : ℝ))
  apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hiQ : z.2.1 i ∈ Q
  · simp only [Set.indicator_of_mem hiQ]
    rw [hg'eq _ (hz i), hg'eq _ (hz ((D z).val i))]
  · simp [Set.indicator_of_notMem hiQ]

lemma localizedDesignRiskIntegrand_integrable {d m N : ℕ}
    {L β cX CX cg Cg : ℝ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (hQ : MeasurableSet Q) (D : Design m N d)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg)
    (hX : P.map Prod.fst = cubeMeasure d) (hD : MatchingDesignClass D)
    (hN : 1 ≤ N) :
    Integrable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        localizedPairLoss g Q z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  have hfull := designRiskIntegrand_integrable P g D hmodel hX hD hN
  refine Integrable.mono' hfull
    (localizedDesignRiskIntegrand_aestronglyMeasurable P g Q hQ D hmodel hX hD) ?_
  filter_upwards [] with z
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hloc0 := localizedPairLoss_nonneg g Q z.2.1 (D z)
  have hle := localizedPairLoss_le_pairLoss g Q z.2.1 (D z)
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg hloc0 hNpos.le)]
  exact div_le_div_of_nonneg_right hle hNpos.le

/-- Expected normalized matching loss charged to one hypercube cell, under
the common iid cube representation of the main wave. -/
@[no_expose]
noncomputable def localizedCubeRisk {d m N : ℕ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (Q : Set (XSpace d)) (D : Design m N d) : ℝ :=
  ∫ z, localizedPairLoss g Q z.2.1 (D z) / (N : ℝ)
    ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw))

/-- Disjoint cell-localized risks sum to at most the full design risk. -/
lemma sum_localizedCubeRisk_le_risk {d m N K : ℕ}
    {L β cX CX cg Cg : ℝ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ)
    (Q : Fin K → Set (XSpace d)) (hQ : ∀ j, MeasurableSet (Q j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (D : Design m N d) (hmodel : RegularScoreModel P g L β cX CX cg Cg)
    (hX : P.map Prod.fst = cubeMeasure d) (hD : MatchingDesignClass D)
    (hN : 1 ≤ N) :
    (∑ j : Fin K, localizedCubeRisk P g (Q j) D) ≤ risk P g D := by
  let μ := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hj (j : Fin K) : Integrable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        localizedPairLoss g (Q j) z.2.1 (D z) / (N : ℝ)) μ :=
    localizedDesignRiskIntegrand_integrable P g (Q j) (hQ j) D
      hmodel hX hD hN
  have hfull : Integrable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        pairLoss g z.2.1 (D z) / (N : ℝ)) μ :=
    designRiskIntegrand_integrable P g D hmodel hX hD hN
  rw [risk_eq_pilot_cube_integral P g D hmodel hX hD]
  unfold localizedCubeRisk
  rw [← integral_finset_sum _ (fun j _ => hj j)]
  apply integral_mono (integrable_finset_sum _ fun j _ => hj j) hfull
  intro z
  change (∑ j : Fin K, localizedPairLoss g (Q j) z.2.1 (D z) / (N : ℝ)) ≤
    pairLoss g z.2.1 (D z) / (N : ℝ)
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (sum_localizedPairLoss_le_pairLoss g Q hdisj z.2.1 (D z))
    (Nat.cast_nonneg N)

/-- A pilot coupling and a unique-core event lower-bound the two localized
risks on one hypercube edge. -/
lemma hypercube_flip_localizedRisk_edge_of_coupling {d m N K : ℕ}
    {L β cX CX cg Cg : ℝ}
    (D : Design m N d) (hD : MatchingDesignClass D) (hN : 1 ≤ N)
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (Q S : Fin K → Set (XSpace d))
    (hQ : ∀ j, MeasurableSet (Q j)) (hS : ∀ j, MeasurableSet (S j))
    (hSQ : ∀ j, S j ⊆ Q j)
    (hsupport : ∀ j y, y ∉ Q j → ψ j y = 0)
    (hcore : ∀ j y, y ∈ S j → ψ j y = 1)
    (hmodel : ∀ θ,
      RegularScoreModel (bernoulliUnitLaw (g θ)) (g θ) L β cX CX cg Cg)
    (hcov : ∀ θ, (bernoulliUnitLaw (g θ)).map Prod.fst = cubeMeasure d)
    (θ : Fin K → Bool) (j : Fin K)
    (Γ : Measure (PilotSample m d × PilotSample m d))
    (hΓ : Causalean.Stat.IsCoupling Γ
      (Measure.pi fun _ : Fin m => pilotUnitLaw (bernoulliUnitLaw (g θ)))
      (Measure.pi fun _ : Fin m =>
        pilotUnitLaw (bernoulliUnitLaw (g (flipCoordinate θ j)))))
    (hsmall : (N : ℝ) * (cubeMeasure d).real (Q j) ≤ 1 / 2) :
    (amplitude ^ 2 / (N : ℝ)) *
        (Γ.real {p | p.1 = p.2} *
          ((N : ℝ) * (cubeMeasure d).real (S j) / 2)) ≤
      localizedCubeRisk (bernoulliUnitLaw (g θ)) (g θ) (Q j) D +
        localizedCubeRisk (bernoulliUnitLaw (g (flipCoordinate θ j)))
          (g (flipCoordinate θ j)) (Q j) D := by
  let P₀ := bernoulliUnitLaw (g θ)
  let P₁ := bernoulliUnitLaw (g (flipCoordinate θ j))
  let μ₀ := Measure.pi fun _ : Fin m => pilotUnitLaw P₀
  let μ₁ := Measure.pi fun _ : Fin m => pilotUnitLaw P₁
  let ν := Measure.pi fun _ : Fin N => cubeMeasure d
  let η := ν.prod randomizerLaw
  let E : Set (MainCovariates N d × ℝ) :=
    {z | z.1 ∈ ⋃ i : Fin N,
      {x | x i ∈ S j ∧ ∀ k, k ≠ i → x k ∉ Q j}}
  let A : Set ((PilotSample m d × PilotSample m d) ×
      (MainCovariates N d × ℝ)) := {z | z.1.1 = z.1.2 ∧ z.2 ∈ E}
  let f₀ : PilotSample m d × (MainCovariates N d × ℝ) → ℝ :=
    fun z => localizedPairLoss (g θ) (Q j) z.2.1
      (D (z.1, z.2.1, z.2.2)) / (N : ℝ)
  let f₁ : PilotSample m d × (MainCovariates N d × ℝ) → ℝ :=
    fun z => localizedPairLoss (g (flipCoordinate θ j)) (Q j) z.2.1
      (D (z.1, z.2.1, z.2.2)) / (N : ℝ)
  letI : IsProbabilityMeasure P₀ := (hmodel θ).covariate_density.1
  letI : IsProbabilityMeasure P₁ :=
    (hmodel (flipCoordinate θ j)).covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P₀) :=
    histogram_pilotUnitLaw_probability P₀ (hmodel θ).covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P₁) :=
    histogram_pilotUnitLaw_probability P₁
      (hmodel (flipCoordinate θ j)).covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov θ]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  letI : IsProbabilityMeasure Γ := hΓ.isProbabilityMeasure
  have hE : MeasurableSet E := by
    dsimp [E]
    exact (MeasurableSet.iUnion fun i =>
      measurableSet_singleton_core_event (S j) (Q j) (hS j) (hQ j) i).preimage
        measurable_fst
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun
      (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst)).inter (hE.preimage measurable_snd)
  have hf₀ : Integrable f₀ (μ₀.prod η) := by
    exact localizedDesignRiskIntegrand_integrable P₀ (g θ) (Q j) (hQ j) D
      (hmodel θ) (hcov θ) hD hN
  have hf₁ : Integrable f₁ (μ₁.prod η) := by
    exact localizedDesignRiskIntegrand_integrable P₁
      (g (flipCoordinate θ j)) (Q j) (hQ j) D
      (hmodel (flipCoordinate θ j)) (hcov (flipCoordinate θ j)) hD hN
  have hedge : (amplitude ^ 2 / (N : ℝ)) * (Γ.prod η).real A ≤
      (∫ z, f₀ z ∂μ₀.prod η) + ∫ z, f₁ z ∂μ₁.prod η := by
    apply coupling_integral_add_lower_of_event μ₀ μ₁ η Γ hΓ f₀ f₁ A
      (amplitude ^ 2 / (N : ℝ)) hf₀ hf₁ hA
    · intro z
      dsimp [f₀]
      exact div_nonneg (localizedPairLoss_nonneg _ _ _ _) (Nat.cast_nonneg N)
    · intro z
      dsimp [f₁]
      exact div_nonneg (localizedPairLoss_nonneg _ _ _ _) (Nat.cast_nonneg N)
    · intro z hz
      rcases Set.mem_iUnion.mp hz.2 with ⟨i, hi⟩
      have hp := hypercube_flip_singleton_localizedPairLoss g base amplitude ψ hg
        Q S hSQ hsupport hcore θ j z.2.1
        (D (z.1.1, z.2.1, z.2.2)) i hi.1
        (fun k hk => by by_contra hki; exact hi.2 k hki hk)
      dsimp [f₀, f₁]
      rw [← hz.1]
      have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      rw [← add_div]
      exact (div_le_div_iff_of_pos_right hNr).2 hp
  have hmain := pi_exists_unique_core_event_real_lower (cubeMeasure d)
    (S j) (Q j) (hS j) (hQ j) (hSQ j) hN hsmall
  have hη : ((N : ℝ) * (cubeMeasure d).real (S j) / 2) ≤ η.real E := by
    dsimp [η, E, ν]
    rw [show {z : MainCovariates N d × ℝ |
          z.1 ∈ ⋃ i : Fin N, {x | x i ∈ S j ∧ ∀ k, k ≠ i → x k ∉ Q j}} =
        (⋃ i : Fin N, {x | x i ∈ S j ∧ ∀ k, k ≠ i → x k ∉ Q j}) ×ˢ
          Set.univ by ext z; simp]
    rw [measureReal_prod_prod, probReal_univ, mul_one]
    exact hmain
  have hmass : Γ.real {p | p.1 = p.2} *
      ((N : ℝ) * (cubeMeasure d).real (S j) / 2) ≤ (Γ.prod η).real A := by
    rw [coupling_agreement_prod_event_mass Γ η E hE]
    exact mul_le_mul_of_nonneg_left hη measureReal_nonneg
  have hcoef : 0 ≤ amplitude ^ 2 / (N : ℝ) := by positivity
  calc
    (amplitude ^ 2 / (N : ℝ)) *
        (Γ.real {p | p.1 = p.2} *
          ((N : ℝ) * (cubeMeasure d).real (S j) / 2)) ≤
        (amplitude ^ 2 / (N : ℝ)) * (Γ.prod η).real A :=
      mul_le_mul_of_nonneg_left hmass hcoef
    _ ≤ (∫ z, f₀ z ∂μ₀.prod η) + ∫ z, f₁ z ∂μ₁.prod η := hedge
    _ = localizedCubeRisk P₀ (g θ) (Q j) D +
        localizedCubeRisk P₁ (g (flipCoordinate θ j)) (Q j) D := rfl

private lemma exists_vertex_large_of_localized_edges_aux {K : ℕ}
    (r : (Fin K → Bool) → ℝ)
    (ell : (Fin K → Bool) → Fin K → ℝ) (a : Fin K → ℝ)
    (hsum : ∀ θ, (∑ j, ell θ j) ≤ r θ)
    (hedge : ∀ θ j, a j ≤ ell θ j + ell (flipCoordinate θ j) j) :
    ∃ θ, (∑ j, a j) ≤ 2 * r θ := by
  by_contra h
  push_neg at h
  have hleft : ∑ θ : Fin K → Bool, ∑ j : Fin K, a j ≤
      ∑ θ : Fin K → Bool, ∑ j : Fin K,
        (ell θ j + ell (flipCoordinate θ j) j) :=
    Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun j _ => hedge θ j
  have hreindex : (∑ θ : Fin K → Bool, ∑ j : Fin K,
      ell (flipCoordinate θ j) j) =
      ∑ θ : Fin K → Bool, ∑ j : Fin K, ell θ j := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact sum_flipCoordinate (fun θ => ell θ j) j
  have hlocal : (∑ θ : Fin K → Bool, ∑ j : Fin K,
      (ell θ j + ell (flipCoordinate θ j) j)) ≤
      ∑ θ : Fin K → Bool, 2 * r θ := by
    rw [show (∑ θ : Fin K → Bool, ∑ j : Fin K,
        (ell θ j + ell (flipCoordinate θ j) j)) =
        (∑ θ : Fin K → Bool, ∑ j : Fin K, ell θ j) +
          ∑ θ : Fin K → Bool, ∑ j : Fin K,
            ell (flipCoordinate θ j) j by
      simp only [Finset.sum_add_distrib]]
    rw [hreindex, ← two_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun θ _ =>
      mul_le_mul_of_nonneg_left (hsum θ) (by norm_num)
  have hstrict : (∑ θ : Fin K → Bool, 2 * r θ) <
      ∑ θ : Fin K → Bool, ∑ j : Fin K, a j :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun θ _ => h θ
  exact (not_lt_of_ge (hleft.trans hlocal)) hstrict

/-- A regular-density hypercube at a mesh satisfying the occupancy and pilot-KL
budgets contains a member whose matching risk is of order `h^(2β)`. -/
lemma hypercube_localized_risk_witness {d m N : ℕ}
    {β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst : ℝ}
    (hfam : HypercubeFamily d β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst)
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hC2 : 0 < C2)
    (hh : 0 < h) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hocc : (N : ℝ) * h ^ (d : ℝ) ≤ 1 / 2)
    (hklbudget : C2 * (m : ℝ) * h ^ ((d : ℝ) + 2 * β) ≤ 1)
    (D : Design m N d) (hD : MatchingDesignClass D) :
    ∃ P : Measure (UnitRecord d), ∃ score : XSpace d → ℝ,
      RegularScoreModel P score L β cX CX cg Cg ∧
      (c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8) * h ^ (2 * β) ≤
        risk P score D := by
  classical
  obtain ⟨K, Q, ψ, B, g, base, amplitude, hKlo, hKhi, hQside, hdisj,
    hB, hψ, hamp, hg, hflip, hfold, hmodel, hcov, hkl⟩ := hfam
  have hamp_pos : 0 < amplitude := by
    have hhβ : 0 < h ^ β := Real.rpow_pos_of_pos hh _
    exact lt_of_lt_of_le (mul_pos hc1 hhβ) hamp
  have hQmeas : ∀ j, MeasurableSet (Q j) :=
    fun j => measurableSet_of_isSideCube (hQside j)
  have hψmeas : ∀ j, Measurable (fun x : Cube d => ψ j x.val.ofLp) := by
    intro j
    exact measurable_hypercube_bump_on_cube g base amplitude L β ψ hg hamp_pos
      (hmodel (fun _ => false)).parameters.2.2.2.1
      (hmodel (fun _ => false)).parameters.2.1
      (fun θ => (hmodel θ).holder_score) (fun _ => false) j
  have hcore_exists (j : Fin K) :
      ∃ S : Set (XSpace d), MeasurableSet S ∧ B j ⊆ S ∧ S ⊆ Q j ∧
        (∀ x ∈ S, ψ j x = 1) ∧ cubeMeasure d (B j) ≤ cubeMeasure d S := by
    exact exists_measurable_bump_core (Q j) (B j) (ψ j) (hQside j)
      (hB j).1 (fun x hx => (hψ j x).2.2.1 hx)
      (fun x hx => (hψ j x).2.2.2 hx) (hψmeas j)
  choose S hS hBS hSQ hcore hmass using hcore_exists
  letI : IsProbabilityMeasure (bernoulliUnitLaw (g (fun _ => false))) :=
    (hmodel (fun _ => false)).covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov (fun _ => false)]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hSmass (j : Fin K) : c0 * h ^ (d : ℝ) ≤ (cubeMeasure d).real (S j) := by
    exact (hB j).2.trans (ENNReal.toReal_mono (by finiteness) (hmass j))
  have hQmass (j : Fin K) : (cubeMeasure d).real (Q j) ≤ h ^ (d : ℝ) := by
    simpa [measureReal_def] using
      sideCube_cubeMeasure_toReal_le (hQside j) hh.le
  have hsmall (j : Fin K) :
      (N : ℝ) * (cubeMeasure d).real (Q j) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hQmass j) (Nat.cast_nonneg N)).trans hocc
  let r : (Fin K → Bool) → ℝ := fun θ =>
    risk (bernoulliUnitLaw (g θ)) (g θ) D
  let ell : (Fin K → Bool) → Fin K → ℝ := fun θ j =>
    localizedCubeRisk (bernoulliUnitLaw (g θ)) (g θ) (Q j) D
  let a : Fin K → ℝ := fun _ =>
    (c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)
  have hellsum (θ : Fin K → Bool) : (∑ j, ell θ j) ≤ r θ := by
    exact sum_localizedCubeRisk_le_risk (bernoulliUnitLaw (g θ)) (g θ)
      Q hQmeas hdisj D (hmodel θ) (hcov θ) hD hN
  have hedge (θ : Fin K → Bool) (j : Fin K) :
      a j ≤ ell θ j + ell (flipCoordinate θ j) j := by
    let P₀ := bernoulliUnitLaw (g θ)
    let P₁ := bernoulliUnitLaw (g (flipCoordinate θ j))
    let μ₀ := Measure.pi fun _ : Fin m => pilotUnitLaw P₀
    let μ₁ := Measure.pi fun _ : Fin m => pilotUnitLaw P₁
    letI : IsProbabilityMeasure P₀ := (hmodel θ).covariate_density.1
    letI : IsProbabilityMeasure P₁ :=
      (hmodel (flipCoordinate θ j)).covariate_density.1
    letI : IsProbabilityMeasure (pilotUnitLaw P₀) :=
      histogram_pilotUnitLaw_probability P₀ (hmodel θ).covariate_density.1
    letI : IsProbabilityMeasure (pilotUnitLaw P₁) :=
      histogram_pilotUnitLaw_probability P₁
        (hmodel (flipCoordinate θ j)).covariate_density.1
    have hbudget0 : 0 ≤ C2 * (m : ℝ) * h ^ ((d : ℝ) + 2 * β) := by positivity
    obtain ⟨Γ, hΓ, hoverlap⟩ := exists_pilot_overlap_coupling μ₀ μ₁ hbudget0
      (hkl m hm θ j)
    letI : IsProbabilityMeasure Γ := hΓ.isProbabilityMeasure
    have hΓtop : Γ {p | p.1 = p.2} ≠ ⊤ := by finiteness
    have hoverlapReal : (1 / 2 : ℝ) *
        Real.exp (-(C2 * (m : ℝ) * h ^ ((d : ℝ) + 2 * β))) ≤
        Γ.real {p | p.1 = p.2} := by
      have ht := ENNReal.toReal_mono hΓtop hoverlap
      simpa [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using ht
    have hexp : Real.exp (-1) ≤
        Real.exp (-(C2 * (m : ℝ) * h ^ ((d : ℝ) + 2 * β))) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hoverlapConst : (1 / 2 : ℝ) * Real.exp (-1) ≤
        Γ.real {p | p.1 = p.2} :=
      (mul_le_mul_of_nonneg_left hexp (by norm_num)).trans hoverlapReal
    have hedge0 := hypercube_flip_localizedRisk_edge_of_coupling D hD hN g base
      amplitude ψ hg Q S hQmeas hS hSQ
      (fun k y hy => (hψ k y).2.2.1 hy) hcore hmodel hcov θ j Γ hΓ (hsmall j)
    have hamp_sq : c1 ^ 2 * h ^ (2 * β) ≤ amplitude ^ 2 := by
      have hs := (sq_le_sq₀ (mul_nonneg hc1.le (Real.rpow_nonneg hh.le β))
        hamp_pos.le).2 hamp
      rw [mul_pow] at hs
      have hp : (h ^ β) ^ 2 = h ^ (2 * β) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
        congr 1
        ring
      simpa [hp] using hs
    have hmassprod : ((1 / 2 : ℝ) * Real.exp (-1)) *
        ((N : ℝ) * (c0 * h ^ (d : ℝ)) / 2) ≤
        Γ.real {p | p.1 = p.2} *
          ((N : ℝ) * (cubeMeasure d).real (S j) / 2) := by
      gcongr
      exact hSmass j
    have hcoef : c1 ^ 2 * h ^ (2 * β) / (N : ℝ) ≤
        amplitude ^ 2 / (N : ℝ) :=
      div_le_div_of_nonneg_right hamp_sq (Nat.cast_nonneg N)
    have hnonnegmass : 0 ≤ Γ.real {p | p.1 = p.2} *
        ((N : ℝ) * (cubeMeasure d).real (S j) / 2) := by positivity
    have hlower := (mul_le_mul hcoef hmassprod
      (by positivity) (by positivity)).trans hedge0
    dsimp [a, ell]
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hrpow : h ^ (2 * β) * h ^ (d : ℝ) = h ^ (2 * β + d) :=
      (Real.rpow_add hh _ _).symm
    calc
      (c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d) =
          (c1 ^ 2 * h ^ (2 * β) / (N : ℝ)) *
            (((1 / 2 : ℝ) * Real.exp (-1)) *
              ((N : ℝ) * (c0 * h ^ (d : ℝ)) / 2)) := by
        field_simp
        rw [← hrpow]
        ring
      _ ≤ _ := hlower
  obtain ⟨θ, hθ⟩ := exists_vertex_large_of_localized_edges_aux r ell a hellsum hedge
  refine ⟨bernoulliUnitLaw (g θ), g θ, hmodel θ, ?_⟩
  have hK : c0 * h ^ (-(d : ℝ)) ≤ (K : ℝ) := hKlo
  have hsum : (∑ j : Fin K, a j) =
      (K : ℝ) * ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)) := by
    simp [a]
  rw [hsum] at hθ
  have hconst0 : 0 ≤ c1 ^ 2 * c0 * Real.exp (-1) / 4 := by positivity
  have hprod : c0 * h ^ (-(d : ℝ)) *
      ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)) ≤
      (K : ℝ) * ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)) := by
    exact mul_le_mul_of_nonneg_right hK (by positivity)
  have hrpow_cancel : h ^ (-(d : ℝ)) * h ^ (2 * β + d) = h ^ (2 * β) := by
    rw [← Real.rpow_add hh]
    congr 1
    ring
  dsimp [r] at hθ
  calc
    (c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8) * h ^ (2 * β) =
        (1 / 2 : ℝ) * (c0 * h ^ (-(d : ℝ)) *
          ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d))) := by
      rw [← hrpow_cancel]
      ring
    _ ≤ (1 / 2 : ℝ) * ((K : ℝ) *
        ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d))) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ risk (bernoulliUnitLaw (g θ)) (g θ) D := by linarith

/-- Assouad averaging for cell-localized risks.  The cell sum is charged only
once to the total risk, so the number of hypercube coordinates does not appear
on the right-hand side. -/
lemma exists_vertex_large_of_localized_edges {K : ℕ}
    (r : (Fin K → Bool) → ℝ)
    (ell : (Fin K → Bool) → Fin K → ℝ) (a : Fin K → ℝ)
    (hsum : ∀ θ, (∑ j, ell θ j) ≤ r θ)
    (hedge : ∀ θ j, a j ≤ ell θ j + ell (flipCoordinate θ j) j) :
    ∃ θ, (∑ j, a j) ≤ 2 * r θ := by
  exact exists_vertex_large_of_localized_edges_aux r ell a hsum hedge

/-- A reciprocal-integer mesh can satisfy both sampling budgets while retaining
the smaller of the main-wave and pilot nonparametric rates. -/
lemma exists_reciprocal_mesh_for_joint_rate (d : ℕ) (β h0 C2 : ℝ)
    (hd : 0 < d) (hβ : 0 < β) (hh0 : 0 < h0) (hC2 : 0 < C2) :
    ∃ cmesh : ℝ, 0 < cmesh ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        ∃ q : ℕ, 0 < q ∧ (q : ℝ)⁻¹ ≤ h0 ∧
          (N : ℝ) * ((q : ℝ)⁻¹) ^ (d : ℝ) ≤ 1 / 2 ∧
          C2 * (m : ℝ) * ((q : ℝ)⁻¹) ^ ((d : ℝ) + 2 * β) ≤ 1 ∧
          cmesh * min ((N : ℝ) ^ (-2 * β / d))
              ((m : ℝ) ^ (-2 * β / (2 * β + d))) ≤
            ((q : ℝ)⁻¹) ^ (2 * β) := by
  let D : ℝ := d + 2 * β
  have hD : 0 < D := by dsimp [D]; positivity
  let s : ℝ := min h0 (min 1
    (min ((1 / 2 : ℝ) ^ (1 / (d : ℝ))) (C2⁻¹ ^ (1 / D))))
  have hs : 0 < s := by dsimp [s]; positivity
  refine ⟨(s / 2) ^ (2 * β), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro m N hm hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let u : ℝ := (N : ℝ) ^ (-(1 / (d : ℝ)))
  let v : ℝ := (m : ℝ) ^ (-(1 / D))
  let w : ℝ := min u v
  let b : ℝ := s * w
  have hu : 0 < u := Real.rpow_pos_of_pos hNR _
  have hv : 0 < v := Real.rpow_pos_of_pos hmR _
  have hw : 0 < w := lt_min hu hv
  have hb : 0 < b := mul_pos hs hw
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hw1 : w ≤ 1 := (min_le_left _ _).trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN)
      (neg_nonpos.mpr (div_nonneg zero_le_one (Nat.cast_nonneg d))))
  have hb1 : b ≤ 1 := by
    dsimp [b]
    calc
      s * w ≤ 1 * w := mul_le_mul_of_nonneg_right hs1 hw.le
      _ ≤ 1 := by simpa using hw1
  let q := meshCount b
  have hq : 0 < q := meshCount_pos b
  obtain ⟨hqlow, hqup, -⟩ := mesh_bounds b hb hb1
  refine ⟨q, hq, ?_, ?_, ?_, ?_⟩
  · calc
      (q : ℝ)⁻¹ ≤ b := hqup
      _ ≤ h0 := by
        dsimp [b]
        exact (mul_le_of_le_one_right hs.le hw1).trans (min_le_left _ _)
  · have hsocc : s ^ (d : ℝ) ≤ (1 / 2 : ℝ) := by
      have hp := Real.rpow_le_rpow hs.le
        ((min_le_right h0 _).trans ((min_le_right 1 _).trans (min_le_left _ _)))
        (by positivity : 0 ≤ (d : ℝ))
      calc
        s ^ (d : ℝ) ≤ (((1 / 2 : ℝ) ^ (1 / (d : ℝ))) ^ (d : ℝ)) := hp
        _ = 1 / 2 := by
          rw [← Real.rpow_mul (by positivity)]
          convert Real.rpow_one (1 / 2 : ℝ) using 2 <;> field_simp
    have hwN : w ^ (d : ℝ) ≤ (N : ℝ)⁻¹ := by
      have hp := Real.rpow_le_rpow hw.le (min_le_left u v)
        (by positivity : 0 ≤ (d : ℝ))
      calc
        w ^ (d : ℝ) ≤ u ^ (d : ℝ) := hp
        _ = (N : ℝ)⁻¹ := by
          dsimp [u]
          rw [← Real.rpow_mul hNR.le]
          rw [show -(1 / (d : ℝ)) * (d : ℝ) = (-1 : ℝ) by field_simp]
          simp [Real.rpow_neg_one]
    have hhpow : ((q : ℝ)⁻¹) ^ (d : ℝ) ≤ b ^ (d : ℝ) :=
      Real.rpow_le_rpow (by positivity) hqup (by positivity)
    rw [Real.mul_rpow hs.le hw.le] at hhpow
    calc
      (N : ℝ) * ((q : ℝ)⁻¹) ^ (d : ℝ) ≤
          (N : ℝ) * (s ^ (d : ℝ) * w ^ (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hhpow hNR.le
      _ ≤ (N : ℝ) * ((1 / 2 : ℝ) * (N : ℝ)⁻¹) := by gcongr
      _ = 1 / 2 := by field_simp
  · have hspilot : C2 * s ^ D ≤ 1 := by
      have hp := Real.rpow_le_rpow hs.le
        ((min_le_right h0 _).trans ((min_le_right 1 _).trans (min_le_right _ _)))
        hD.le
      have hroot : (C2⁻¹ ^ (1 / D)) ^ D = C2⁻¹ := by
        rw [← Real.rpow_mul (by positivity)]
        convert Real.rpow_one C2⁻¹ using 2 <;> field_simp
      rw [hroot] at hp
      nlinarith [mul_inv_cancel₀ hC2.ne']
    have hwM : w ^ D ≤ (m : ℝ)⁻¹ := by
      have hp := Real.rpow_le_rpow hw.le (min_le_right u v) hD.le
      calc
        w ^ D ≤ v ^ D := hp
        _ = (m : ℝ)⁻¹ := by
          dsimp [v]
          rw [← Real.rpow_mul hmR.le]
          rw [show -(1 / D) * D = (-1 : ℝ) by field_simp]
          simp [Real.rpow_neg_one]
    have hhpow : ((q : ℝ)⁻¹) ^ D ≤ b ^ D :=
      Real.rpow_le_rpow (by positivity) hqup hD.le
    rw [Real.mul_rpow hs.le hw.le] at hhpow
    calc
      C2 * (m : ℝ) * ((q : ℝ)⁻¹) ^ D ≤
          C2 * (m : ℝ) * (s ^ D * w ^ D) :=
        mul_le_mul_of_nonneg_left hhpow (by positivity)
      _ ≤ (C2 * s ^ D) * ((m : ℝ) * (m : ℝ)⁻¹) := by
        calc
          C2 * (m : ℝ) * (s ^ D * w ^ D) =
              (C2 * s ^ D) * ((m : ℝ) * w ^ D) := by ring
          _ ≤ (C2 * s ^ D) * ((m : ℝ) * (m : ℝ)⁻¹) := by
            gcongr
      _ ≤ 1 := by rw [mul_inv_cancel₀ hmR.ne']; simpa using hspilot
  · have hrate := (reciprocal_mesh_rpow_bounds b (2 * β) hb hb1
      (by positivity)).1
    have hwRate : w ^ (2 * β) = min ((N : ℝ) ^ (-2 * β / d))
        ((m : ℝ) ^ (-2 * β / (2 * β + d))) := by
      have huRate : u ^ (2 * β) = (N : ℝ) ^ (-2 * β / d) := by
        dsimp [u]
        rw [← Real.rpow_mul hNR.le]
        congr 1
        field_simp
      have hvRate : v ^ (2 * β) =
          (m : ℝ) ^ (-2 * β / (2 * β + d)) := by
        dsimp [v, D]
        rw [← Real.rpow_mul hmR.le]
        congr 1
        field_simp
        ring
      dsimp [w]
      by_cases huv : u ≤ v
      · rw [min_eq_left huv, huRate]
        symm
        apply min_eq_left
        rw [← huRate, ← hvRate]
        exact Real.rpow_le_rpow hu.le huv (by positivity)
      · have hvu : v ≤ u := le_of_not_ge huv
        rw [min_eq_right hvu, hvRate]
        symm
        apply min_eq_right
        rw [← huRate, ← hvRate]
        exact Real.rpow_le_rpow hv.le hvu (by positivity)
    rw [Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow hs.le hw.le,
      hwRate] at hrate
    dsimp [q]
    rw [Real.div_rpow (by positivity) (by norm_num)]
    simpa [b, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hrate
end CausalSmith.Experimentation.PilotscorePairingFrontier
