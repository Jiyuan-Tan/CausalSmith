module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.LeftAdapter
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperIntegrability

/-! # Construction of the five-chain fourth-moment adapters -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

lemma localizedProcess_fourth_integral_le_of_dom
    {ι : Type} [Countable ι] [Nonempty ι]
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (hn : 0 < n)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (hz : 0 < z)
    (πstar : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P)
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation ι)
    (hdom : ∀ x : Fin n → SupportedObservation,
      supportedWitnessLocalizedProcess P a z πstar x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x)
    [IsProbabilityMeasure P.obsLaw]
    [IsProbabilityMeasure (supportedObsLaw P)] :
    (∫ d, localizedProcess P a z d ^ 4 ∂sampleLaw P n) ≤
      ∫ d, Causalean.Stat.EmpiricalProcess.Countable.centeredSup
        (supportedObsLaw P) F.f d ^ 4
        ∂Measure.pi (fun _ : Fin n => supportedObsLaw P) := by
  have hm := localizedProcess_measurable (n := n) P a z hP.wf ha.1 hz
  have horig := upperIntegrability_process_fourth α γ θ n P e hP
    a z ha hn hm
  rw [← integral_supportedSampleLaw P hP.wf n
    (fun d => localizedProcess P a z d ^ 4) horig.aestronglyMeasurable]
  have hle := localizedProcess_fourth_ae_le_fiveChain_of_ae
    P hP.wf a z πstar hstar F hdom (n := n)
  have hg := (Causalean.Stat.EmpiricalProcess.Countable.centeredSup_legal
    (supportedObsLaw P) F n).2.2
  have hf : Integrable (fun x : Fin n → SupportedObservation =>
      localizedProcess P a z (fun i => (x i).1) ^ 4)
      (Measure.pi (fun _ : Fin n => supportedObsLaw P)) := by
    apply hg.mono' (hm.pow_const 4).aestronglyMeasurable
    filter_upwards [hle] with x hx
    let q := localizedProcess P a z (fun i => (x i).1)
    have hq : |q ^ 4| = q ^ 4 :=
      abs_of_nonneg ((by decide : Even 4).pow_nonneg q)
    change ‖q ^ 4‖ ≤ _
    rw [Real.norm_eq_abs, hq]
    exact hx
  exact integral_mono_ae hf hg hle

@[no_expose]
noncomputable def localizedProcessL4Adapter_of_cover
    {ι : Type} [Countable ι] [Nonempty ι]
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (hn : 0 < n)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (hz : 0 < z)
    (πstar : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P)
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation ι)
    (cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F 5)
    (hdom : ∀ x : Fin n → SupportedObservation,
      supportedWitnessLocalizedProcess P a z πstar x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x)
    (hw : ∀ b, Measurable (cover.weight b))
    (hwK : ∀ b o, |cover.weight b o| ≤ 2 / a)
    (hgeom : ∀ b, ∃ B : Set ℝ, MeasurableSet B ∧
      (∫ x in B, offsetG a P.logger x ∂P.PX) ≤ z ∧
      cover.containing b = {o | o.1.X ∈ B} ∧
      ∀ o, cover.weight b o ^ 2 = zScore a P.logger o.1 ^ 2)
    [IsProbabilityMeasure P.obsLaw]
    [IsProbabilityMeasure (supportedObsLaw P)] :
    LocalizedProcessL4Adapter (n := n) P a z := by
  refine {
    Index := ι
    countableIndex := inferInstance
    nonemptyIndex := inferInstance
    probability := inferInstance
    F := F
    cover := cover
    moment_le := localizedProcess_fourth_integral_le_of_dom
      α γ θ n P e hP hn a z ha hz πstar hstar F hdom
    energy_integrable := ?_
    energy_le := ?_ }
  · intro b
    obtain ⟨B, hB, hmass, hcont, hweight⟩ := hgeom b
    apply coverEnergy_sq_integrable (supportedObsLaw P) cover b
      (hcont ▸ supportedObservation_X_measurable hB) (hw b)
      (2 / a) (div_nonneg (by norm_num) ha.1.le) (hwK b)
  · intro b
    obtain ⟨B, hB, hmass, hcont, hweight⟩ := hgeom b
    exact coverEnergy_second_moment_le α γ θ n P e hP hn a z ha cover b B
      hB hmass hcont hweight

lemma rightZero_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a)
    (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (fun _ => false) ≤ z) :
    (∫ x in Set.Icc c 1, offsetG a P.logger x ∂P.PX) ≤ z := by
  apply (rightOracle_disagreement_mass_le_loss α γ θ n P e hP a c ha
    (fun _ => false) (Or.inl fun _ _ => rfl) hstar (Set.Icc c 1)
    measurableSet_Icc ?_).trans hloss
  intro x hx
  by_cases hcx : c ≤ x <;> simp [rightThr, hcx, hx.2]

lemma leftZero_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a)
    (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (fun _ => false) ≤ z) :
    (∫ x in Set.Icc 0 c, offsetG a P.logger x ∂P.PX) ≤ z := by
  apply (oracle_disagreement_mass_le_loss α γ θ n P e hP a ha
    (leftThr c) (fun _ => false) (Or.inl fun _ _ => rfl) hstar
    (Set.Icc 0 c) measurableSet_Icc ?_).trans hloss
  intro x hx
  by_cases hxc : x ≤ c <;> simp [leftThr, hxc, hx.1]

@[no_expose]
noncomputable def buildRightOracleAdapter
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (hn : 0 < n)
    (a c z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (hz : 0 < z)
    (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P) :
    LocalizedProcessL4Adapter (n := n) P a z := by
  letI : IsProbabilityMeasure P.full := hP.wf.1
  letI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  letI : IsProbabilityMeasure (supportedObsLaw P) :=
    supportedObsLaw_isProbabilityMeasure P hP.wf
  have hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simpa only [hP.known hx] using hP.loggerSpace x hx
  let S := exists_rightOracle_localizedSkeletons α γ θ n P e hP a c z ha
  let Sright := S.1
  let Sleft := S.2
  letI : Countable Sright.D := Sright.countable
  letI : Countable Sleft.D := Sleft.countable
  let R := exists_rightOracle_skeleton_fiveChain P a c z hP.wf ha hlogger
    Sright Sleft
  let F := Classical.choose R
  let R₁ := Classical.choose_spec R
  let cover := Classical.choose R₁
  have hs := Classical.choose_spec R₁
  have hdomPair := hs.1
  have hfour := hs.2.1
  have hw := hs.2.2.1
  have hU₀ := hs.2.2.2.1
  have hU₁ := hs.2.2.2.2.1
  have hU₂ := hs.2.2.2.2.2.1
  have hU₃ := hs.2.2.2.2.2.2.1
  have hU₄ := hs.2.2.2.2.2.2.2
  have hzero : regularizedLoss P a (fun _ => false) ≤ z →
      F.f .branch4 = fun o =>
        witnessComparisonIntegrand P a (rightThr c) (fun _ => false) o.1 := by
    intro hloss
    have hd : decide (regularizedLoss P a (fun _ => false) ≤ z) = true :=
      decide_eq_true hloss
    simpa only [F, hd, if_true] using hfour
  have hdom : ∀ x : Fin n → SupportedObservation,
      supportedWitnessLocalizedProcess P a z (rightThr c) x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x := fun x =>
    supportedWitnessLocalizedProcess_le_fiveChain P a c z hP.wf ha hlogger F
      hzero (fun y => (hdomPair _ y).1) (fun y => (hdomPair _ y).2) x
  apply localizedProcessL4Adapter_of_cover α γ θ n P e hP hn a z ha hz
    (rightThr c) hstar F cover hdom
  · intro b
    dsimp only [cover]
    rw [hw b]
    exact rightOracleWeight_measurable P a c hP.wf
  · intro b o
    dsimp only [cover]
    rw [hw b]
    exact rightOracleWeight_abs_le P a c ha hlogger o
  · intro b
    fin_cases b
    · let B : Set ℝ := ⋃ i : {t : Sright.D // t.1 < c}, Set.Ico i.1.1 c
      have hmass := rightBelowSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sright
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 0 = {o | o.1.X ∈ B}
        rw [hU₀]
        ext o
        simp [B, rightBelowSet]
      · intro o
        dsimp only [cover]
        change cover.weight 0 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 0]
        unfold rightOracleWeight
        split_ifs <;> ring
    · let B : Set ℝ := ⋃ i : {t : Sright.D // c ≤ t.1}, Set.Ico c i.1.1
      have hmass := rightAboveSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sright
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 1 = {o | o.1.X ∈ B}
        rw [hU₁]
        ext o
        simp [B, rightAboveSet]
      · intro o
        dsimp only [cover]
        change cover.weight 1 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 1]
        unfold rightOracleWeight
        split_ifs <;> ring
    · let B : Set ℝ := ⋃ i : {t : Sleft.D // t.1 < c},
        Set.Icc 0 i.1.1 ∪ Set.Icc c 1
      have hmass := leftBelowSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sleft
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 2 = {o | o.1.X ∈ B}
        rw [hU₂]
        ext o
        simp [B, leftBelowSet]
      · intro o
        dsimp only [cover]
        change cover.weight 2 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 2]
        unfold rightOracleWeight
        split_ifs <;> ring
    · let B : Set ℝ := ⋃ i : {t : Sleft.D // c ≤ t.1},
        Set.Ico 0 c ∪ Set.Ioc i.1.1 1
      have hmass := leftAboveSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sleft
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 3 = {o | o.1.X ∈ B}
        rw [hU₃]
        ext o
        simp [B, leftAboveSet]
      · intro o
        dsimp only [cover]
        change cover.weight 3 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 3]
        unfold rightOracleWeight
        split_ifs <;> ring
    · by_cases hloss : regularizedLoss P a (fun _ => false) ≤ z
      · refine ⟨Set.Icc c 1, measurableSet_Icc,
          rightZero_mass_le α γ θ n P e hP a c z ha.1 hstar hloss, ?_, ?_⟩
        · dsimp only [cover]
          change cover.containing 4 = {o | o.1.X ∈ Set.Icc c 1}
          rw [hU₄]
          simp [hloss, zeroBranchSet]
        · intro o
          dsimp only [cover]
          change cover.weight 4 o ^ 2 = zScore a P.logger o.1 ^ 2
          rw [hw 4]
          unfold rightOracleWeight
          split_ifs <;> ring
      · refine ⟨∅, MeasurableSet.empty, by simp [hz.le], ?_, ?_⟩
        · dsimp only [cover]
          change cover.containing 4 = {o | o.1.X ∈ (∅ : Set ℝ)}
          rw [hU₄]
          simp [hloss]
        · intro o
          dsimp only [cover]
          change cover.weight 4 o ^ 2 = zScore a P.logger o.1 ^ 2
          rw [hw 4]
          unfold rightOracleWeight
          split_ifs <;> ring

@[no_expose]
noncomputable def buildLeftOracleAdapter
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (hn : 0 < n)
    (a c z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (hz : 0 < z)
    (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P) :
    LocalizedProcessL4Adapter (n := n) P a z := by
  letI : IsProbabilityMeasure P.full := hP.wf.1
  letI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  letI : IsProbabilityMeasure (supportedObsLaw P) :=
    supportedObsLaw_isProbabilityMeasure P hP.wf
  have hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simpa only [hP.known hx] using hP.loggerSpace x hx
  let S := exists_leftOracle_localizedSkeletons α γ θ n P e hP a c z ha
  let Sright := S.1
  let Sleft := S.2
  letI : Countable Sright.D := Sright.countable
  letI : Countable Sleft.D := Sleft.countable
  let R := exists_leftOracle_skeleton_fiveChain P a c z hP.wf ha hlogger
    Sright Sleft
  let F := Classical.choose R
  let R₁ := Classical.choose_spec R
  let cover := Classical.choose R₁
  have hs := Classical.choose_spec R₁
  have hdomPair := hs.1
  have hfour := hs.2.1
  have hw := hs.2.2.1
  have hU₀ := hs.2.2.2.1
  have hU₁ := hs.2.2.2.2.1
  have hU₂ := hs.2.2.2.2.2.1
  have hU₃ := hs.2.2.2.2.2.2.1
  have hU₄ := hs.2.2.2.2.2.2.2
  have hzero : regularizedLoss P a (fun _ => false) ≤ z →
      F.f .branch4 = fun o =>
        witnessComparisonIntegrand P a (leftThr c) (fun _ => false) o.1 := by
    intro hloss
    have hd : decide (regularizedLoss P a (fun _ => false) ≤ z) = true :=
      decide_eq_true hloss
    simpa only [F, hd, if_true] using hfour
  have hdom : ∀ x : Fin n → SupportedObservation,
      supportedWitnessLocalizedProcess P a z (leftThr c) x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x := fun x =>
    supportedWitnessLocalizedProcess_le_leftFiveChain P a c z hP.wf ha
      hlogger F hzero (fun y => (hdomPair _ y).1)
      (fun y => (hdomPair _ y).2) x
  apply localizedProcessL4Adapter_of_cover α γ θ n P e hP hn a z ha hz
    (leftThr c) hstar F cover hdom
  · intro b
    dsimp only [cover]
    rw [hw b]
    exact leftOracleWeight_measurable P a c hP.wf
  · intro b o
    dsimp only [cover]
    rw [hw b]
    exact leftOracleWeight_abs_le P a c ha hlogger o
  · intro b
    fin_cases b
    · let B : Set ℝ := ⋃ i : {t : Sleft.D // t.1 < c}, Set.Ioc i.1.1 c
      have hmass := leftSameBelowSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sleft
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 0 = {o | o.1.X ∈ B}
        rw [hU₀]
        ext o
        simp [B]
      · intro o
        dsimp only [cover]
        change cover.weight 0 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 0]
        unfold leftOracleWeight
        split_ifs <;> ring
    · let B : Set ℝ := ⋃ i : {t : Sleft.D // c ≤ t.1}, Set.Ioc c i.1.1
      have hmass := leftSameAboveSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sleft
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 1 = {o | o.1.X ∈ B}
        rw [hU₁]
        ext o
        simp [B]
      · intro o
        dsimp only [cover]
        change cover.weight 1 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 1]
        unfold leftOracleWeight
        split_ifs <;> ring
    · let B : Set ℝ := ⋃ i : {t : Sright.D // t.1 ≤ c},
        Set.Ico 0 i.1.1 ∪ Set.Ioc c 1
      have hmass := leftOppBelowSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sright
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 2 = {o | o.1.X ∈ B}
        rw [hU₂]
        ext o
        simp [B]
      · intro o
        dsimp only [cover]
        change cover.weight 2 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 2]
        unfold leftOracleWeight
        split_ifs <;> ring
    · let B : Set ℝ := ⋃ i : {t : Sright.D // c < t.1},
        Set.Icc 0 c ∪ Set.Icc i.1.1 1
      have hmass := leftOppAboveSkeleton_union_mass_le α γ θ n P e hP
        a c z ha.1 hz.le hstar Sright
      refine ⟨B, hmass.1, hmass.2, ?_, ?_⟩
      · dsimp only [cover]
        change cover.containing 3 = {o | o.1.X ∈ B}
        rw [hU₃]
        ext o
        simp [B]
      · intro o
        dsimp only [cover]
        change cover.weight 3 o ^ 2 = zScore a P.logger o.1 ^ 2
        rw [hw 3]
        unfold leftOracleWeight
        split_ifs <;> ring
    · by_cases hloss : regularizedLoss P a (fun _ => false) ≤ z
      · refine ⟨Set.Icc 0 c, measurableSet_Icc,
          leftZero_mass_le α γ θ n P e hP a c z ha.1 hstar hloss, ?_, ?_⟩
        · dsimp only [cover]
          change cover.containing 4 = {o | o.1.X ∈ Set.Icc 0 c}
          rw [hU₄]
          simp [hloss, leftZeroSet]
        · intro o
          dsimp only [cover]
          change cover.weight 4 o ^ 2 = zScore a P.logger o.1 ^ 2
          rw [hw 4]
          unfold leftOracleWeight
          split_ifs <;> ring
      · refine ⟨∅, MeasurableSet.empty, by simp [hz.le], ?_, ?_⟩
        · dsimp only [cover]
          change cover.containing 4 = {o | o.1.X ∈ (∅ : Set ℝ)}
          rw [hU₄]
          simp [hloss]
        · intro o
          dsimp only [cover]
          change cover.weight 4 o ^ 2 = zScore a P.logger o.1 ^ 2
          rw [hw 4]
          unfold leftOracleWeight
          split_ifs <;> ring

lemma nonempty_localizedProcessL4Adapter
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (hn : 0 < n)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) (hz : 0 < z) :
    Nonempty (LocalizedProcessL4Adapter (n := n) P a z) := by
  obtain ⟨πstar, hπclass, hstar⟩ := hP.canonical
  rcases hπclass with hfalse | htrue | hleft | hright
  · have hright : rightThr 2 =ᵐ[P.PX] canonicalPolicy P := by
      filter_upwards [hstar, ae_iff.mpr hP.score.2] with x hx hs
      rw [← hx, hfalse x hs]
      simp [rightThr]
      linarith [hs.2]
    exact ⟨buildRightOracleAdapter α γ θ n P e hP hn a 2 z ha hz hright⟩
  · have hright : rightThr 0 =ᵐ[P.PX] canonicalPolicy P := by
      filter_upwards [hstar, ae_iff.mpr hP.score.2] with x hx hs
      rw [← hx, htrue x hs]
      simp [rightThr, hs.1]
    exact ⟨buildRightOracleAdapter α γ θ n P e hP hn a 0 z ha hz hright⟩
  · obtain ⟨c, hc, hπ⟩ := hleft
    have hleftStar : leftThr c =ᵐ[P.PX] canonicalPolicy P := by
      filter_upwards [hstar, ae_iff.mpr hP.score.2] with x hx hs
      rw [← hx, hπ x hs]
    exact ⟨buildLeftOracleAdapter α γ θ n P e hP hn a c z ha hz hleftStar⟩
  · obtain ⟨c, hc, hπ⟩ := hright
    have hrightStar : rightThr c =ᵐ[P.PX] canonicalPolicy P := by
      filter_upwards [hstar, ae_iff.mpr hP.score.2] with x hx hs
      rw [← hx, hπ x hs]
    exact ⟨buildRightOracleAdapter α γ θ n P e hP hn a c z ha hz hrightStar⟩

@[no_expose]
noncomputable def buildLocalizedProcessL4Adapter
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (_hα : 0 < α) (_hγ : 0 < γ) (_hθ : 0 < θ) (hn : 0 < n)
    (hP : LawClass α γ θ n P e) (a z : ℝ)
    (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hz : 0 < z) :
    LocalizedProcessL4Adapter (n := n) P a z :=
  Classical.choice
    (nonempty_localizedProcessL4Adapter α γ θ n P e hP hn a z ⟨ha, ha4⟩ hz)

end CausalSmith.Stat.ScorethresholdOverlapRegret
