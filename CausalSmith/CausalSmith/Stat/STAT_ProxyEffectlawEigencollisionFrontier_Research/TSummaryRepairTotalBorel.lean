import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Inference
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TGapFreePositiveMeasureModulus
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TSummaryClosureCompact

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

abbrev SummaryRepairCoordIndex (dx dz : ℕ) :=
  (Fin 4 × Fin dz × Fin dx) ⊕ Fin dx

-- @node: summaryRepairToEuc
def summaryRepairToEuc {dx dz : ℕ} (s : SummarySpace dx dz) :
    EuclideanSpace ℝ (SummaryRepairCoordIndex dx dz) :=
  WithLp.toLp 2 fun i => match i with
  | Sum.inl (b, a, j) => match b.val with
    | 0 => s.M0 a j | 1 => s.M1 a j | 2 => s.N0 a j | _ => s.N1 a j
  | Sum.inr j => s.mX j

-- @node: summaryRepairOfEuc
def summaryRepairOfEuc {dx dz : ℕ}
    (x : EuclideanSpace ℝ (SummaryRepairCoordIndex dx dz)) : SummarySpace dx dz where
  M0 a j := x (Sum.inl (0, a, j)); M1 a j := x (Sum.inl (1, a, j))
  N0 a j := x (Sum.inl (2, a, j)); N1 a j := x (Sum.inl (3, a, j))
  mX j := x (Sum.inr j)

-- @node: summaryRepairSpaceHomeomorph
def summaryRepairSpaceHomeomorph (dx dz : ℕ) :
    SummarySpace dx dz ≃ₜ EuclideanSpace ℝ (SummaryRepairCoordIndex dx dz) where
  toFun := summaryRepairToEuc
  invFun := summaryRepairOfEuc
  left_inv := by intro s; cases s; simp [summaryRepairToEuc, summaryRepairOfEuc]
  right_inv := by
    intro x; ext i; rcases i with ⟨b, a, j⟩ | j
    · fin_cases b <;> simp [summaryRepairToEuc, summaryRepairOfEuc]
    · simp [summaryRepairToEuc, summaryRepairOfEuc]
  continuous_toFun := by
    have hc : Continuous (@SummarySpace.toCoordinates dx dz) := continuous_induced_dom
    have h0 : Continuous (fun s : SummarySpace dx dz => s.M0) := continuous_fst.comp hc
    have h1 : Continuous (fun s : SummarySpace dx dz => s.M1) :=
      (continuous_fst.comp continuous_snd).comp hc
    have h2 : Continuous (fun s : SummarySpace dx dz => s.N0) :=
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).comp hc
    have h3 : Continuous (fun s : SummarySpace dx dz => s.N1) :=
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hc
    have h4 : Continuous (fun s : SummarySpace dx dz => s.mX) :=
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hc
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i; rcases i with ⟨b, a, j⟩ | j
    · fin_cases b
      · change Continuous ((fun p => p a j) ∘ fun s : SummarySpace dx dz => s.M0)
        exact (continuous_apply_apply a j).comp h0
      · change Continuous ((fun p => p a j) ∘ fun s : SummarySpace dx dz => s.M1)
        exact (continuous_apply_apply a j).comp h1
      · change Continuous ((fun p => p a j) ∘ fun s : SummarySpace dx dz => s.N0)
        exact (continuous_apply_apply a j).comp h2
      · change Continuous ((fun p => p a j) ∘ fun s : SummarySpace dx dz => s.N1)
        exact (continuous_apply_apply a j).comp h3
    · change Continuous ((fun p => p j) ∘ fun s : SummarySpace dx dz => s.mX)
      exact (continuous_apply j).comp h4
  continuous_invFun := by
    rw [continuous_induced_rng]
    repeat' apply Continuous.prodMk
    all_goals first | (apply continuous_pi; intro; apply continuous_pi; intro; fun_prop) |
      (apply continuous_pi; intro; fun_prop)

-- @node: euclideanReindexHomeomorph
def euclideanReindexHomeomorph {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ κ where
  toFun x := WithLp.toLp 2 fun j => x (e.symm j)
  invFun x := WithLp.toLp 2 fun i => x (e i)
  left_inv := by intro x; ext i; simp
  right_inv := by intro x; ext j; simp
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 _).comp; apply continuous_pi; intro j
    exact PiLp.continuous_apply 2 (fun _ : ι => ℝ) (e.symm j)
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 _).comp; apply continuous_pi; intro i
    exact PiLp.continuous_apply 2 (fun _ : κ => ℝ) (e i)

-- @node: compactLoss_selector_of_homeomorph
lemma compactLoss_selector_of_homeomorph {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (d : ℕ) (e : X ≃ₜ Euc d)
    (K : Set X) (hKne : K.Nonempty) (hK : IsCompact K)
    (loss : X → X → ℝ) (hloss : Continuous (Function.uncurry loss)) :
    ∃ Pi : X → X, Measurable Pi ∧ (∀ s, Pi s ∈ K) ∧
      ∀ s q, q ∈ K → loss (Pi s) s ≤ loss q s := by
  let KE : Set (Euc d) := e '' K
  have hKEc : IsCompact KE := hK.image e.continuous
  have hKEn : KE.Nonempty := hKne.image e
  have hf : Continuous (Function.uncurry
      (fun x y : Euc d => loss (e.symm y) (e.symm x))) := by
    exact hloss.comp ((e.symm.continuous.comp continuous_snd).prodMk
      (e.symm.continuous.comp continuous_fst))
  obtain ⟨pi, hpm, hp⟩ := borelMeasurable_compactLoss_selector d KE
    (fun x y => loss (e.symm y) (e.symm x)) hKEn hKEc hf
  let Pi : X → X := fun s => e.symm (pi (e s))
  refine ⟨Pi, e.symm.continuous.measurable.comp
    (hpm.comp e.continuous.measurable), ?_, ?_⟩
  · intro s
    rcases (hp (e s)).1 with ⟨q, hq, heq⟩
    change e.symm (pi (e s)) ∈ K
    rw [← heq, e.symm_apply_apply]
    exact hq
  · intro s q hq
    simpa [Pi] using (hp (e s)).2 (e q) ⟨q, hq, rfl⟩

/-- The nearest-summary repair has a total Borel positive-law realization, with the stated
zero-law fallback and a nonempty theoretical confidence set. -/
-- @node: prop:summary-repair-total-borel
theorem summary_repair_total_borel
    (k dx dz n : ℕ) (L pi0 sigma0 alpha C0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) (hn : 1 ≤ n)
    (hAlpha : MiscoverageDomain alpha) (hC0 : ConcentrationConstantDomain C0) :
    Measurable (@empSummary n dx dz) →
    ∃ R : SummaryRepairData k dx dz n L pi0 sigma0,
      Measurable (summaryRepair R) ∧
      (∀ sample, summaryClosure k dx dz L pi0 sigma0 = ∅ →
        summaryRepair R sample =
          AtomicLaw.LawModulo.deltaZeroLaw R.k_pos R.radius_nonneg) ∧
      ∀ sample, (theoreticalConfidenceSet R sample alpha C0).Nonempty := by
  intro hemp
  obtain ⟨halpha, halphaMax⟩ := hAlpha
  let K := summaryClosure k dx dz L pi0 sigma0
  have hKc : IsCompact K := (summary_closure_compact k dx dz L pi0 sigma0 hk hkx hkz hL
    hpi hpiMax hsigma hsigmaMax).2.1
  obtain ⟨C, hC, hmod, Fbar, hFc, hFm, hFlip, hFext, huniq⟩ :=
    gap_free_positive_measure_modulus k dx dz L pi0 sigma0 hk hkx hkz hL hpi hpiMax
      hsigma hsigmaMax
  have hkp : 0 < k := by omega
  have hr : 0 ≤ effectRadius dz L sigma0 := by unfold effectRadius; positivity
  by_cases he : K = ∅
  · let R : SummaryRepairData k dx dz n L pi0 sigma0 := {
      k_pos := hkp, radius_nonneg := hr, Fbar := Fbar, Pi := fun _ => 0
      continuousFbar := hFc
      extendsOnModel := by
        intro Q
        exfalso
        have hmem : Q.summary ∈ summaryClosure k dx dz L pi0 sigma0 :=
          subset_closure (show Q.summary ∈ admissibleImage k dx dz L pi0 sigma0 from ⟨Q, rfl⟩)
        rw [show summaryClosure k dx dz L pi0 sigma0 = ∅ by simpa [K] using he] at hmem
        exact hmem
      measurablePi := measurable_const
      nearest := by intro s hn; exact False.elim (hn (by simpa [K] using he))
      empty_fallback := by intro _ s; rfl
      measurableRepair := by
        have he' : summaryClosure k dx dz L pi0 sigma0 = ∅ := by simpa [K] using he
        simp only [he', dite_true]; exact measurable_const }
    refine ⟨R, R.measurableRepair, ?_, ?_⟩
    · intro sample hs; simp [summaryRepair, hs]
    · intro sample; rw [theoreticalConfidenceSet, if_pos (by simpa [K] using he)]
      exact singleton_nonempty _
  · have hne : K.Nonempty := nonempty_iff_ne_empty.mpr he
    let d := Fintype.card (SummaryRepairCoordIndex dx dz)
    let e : SummarySpace dx dz ≃ₜ Euc d := (summaryRepairSpaceHomeomorph dx dz).trans
      (euclideanReindexHomeomorph (Fintype.equivFin (SummaryRepairCoordIndex dx dz)))
    obtain ⟨Pi, hPm, hPK, hPmin⟩ := compactLoss_selector_of_homeomorph d e K hne hKc dS
      (dS_continuous dx dz)
    let R : SummaryRepairData k dx dz n L pi0 sigma0 := {
      k_pos := hkp, radius_nonneg := hr, Fbar := Fbar, Pi := Pi
      continuousFbar := hFc, extendsOnModel := hFext, measurablePi := hPm
      nearest := fun s _ => ⟨hPK s, hPmin s⟩
      empty_fallback := by intro hs; exact False.elim (he (by simpa [K] using hs))
      measurableRepair := by
        have he' : summaryClosure k dx dz L pi0 sigma0 ≠ ∅ := by simpa [K] using he
        simp only [he', dite_false]
        have hsubmem : ∀ s, Pi s ∈ summaryClosure k dx dz L pi0 sigma0 := by
          intro s
          simpa [K] using hPK s
        have hsub : Measurable (fun s =>
            (⟨Pi s, hsubmem s⟩ : {q // q ∈ summaryClosure k dx dz L pi0 sigma0})) :=
          hPm.subtype_mk
        simpa [Function.comp_def] using hFm.comp (hsub.comp hemp) }
    refine ⟨R, R.measurableRepair, fun sample hs => False.elim (he (by simpa [K] using hs)), ?_⟩
    intro sample
    rw [theoreticalConfidenceSet, if_neg (by simpa [K] using he)]
    refine ⟨summaryRepair R sample, ⟨⟨R.Pi (empSummary sample), (R.nearest _ ?_).1⟩, ?_, ?_⟩⟩
    · simpa [K] using he
    · have hrpos := summaryRadius_pos n alpha C0 L (by omega) halpha halphaMax hC0 hL
      have hz : 0 ≤ 2 * summaryRadius n alpha C0 L := by positivity
      simpa [dS, matrixCLM] using hz
    · have he' : summaryClosure k dx dz L pi0 sigma0 ≠ ∅ := by simpa [K] using he
      simp only [summaryRepair, he', dite_false]

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
