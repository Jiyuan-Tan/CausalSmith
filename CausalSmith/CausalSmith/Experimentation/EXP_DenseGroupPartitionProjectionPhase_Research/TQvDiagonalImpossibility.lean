import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.QVDiagonalAssembly
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Stat.Minimax.MinimaxRisk

/-!
# One-realization diagonal impossibility

The lower bound is encoded in witness form: explicit high-prior-probability
finite supports, conditioned-mixture separation, uniform support-wise variance
limits, and a worst-case risk bound for every one-realization statistic.
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

/-- Conditioned common-sign expectation, written as a finite weighted ratio. -/
noncomputable def conditionedSameExpectation {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (Γ : Finset (Fin (A.popSize r) → Bool))
    (φ : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ) : ℝ :=
  (priorSame (A.popSize r)).E (fun u =>
    if u ∈ Γ then (A.design r).E (fun w => φ (observe (A.popSize r) M
      (A.groups r) (A.treated r) (samePriorSchedule (A.popSize r) M u) w)) else 0) /
    (priorSame (A.popSize r)).Pr (fun u => u ∈ Γ)

/-- Conditioned independent-arm expectation, written as a finite weighted ratio. -/
noncomputable def conditionedIndependentExpectation {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (Γ : Finset (Fin (A.popSize r) × Bool → Bool))
    (φ : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ) : ℝ :=
  (priorIndependent (A.popSize r)).E (fun u =>
    if u ∈ Γ then (A.design r).E (fun w => φ (observe (A.popSize r) M
      (A.groups r) (A.treated r) (independentPriorSchedule (A.popSize r) M u) w)) else 0) /
    (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γ)

/-- Total variation of the two conditioned finite mixtures, in its bounded-test form. -/
noncomputable def conditionedMixtureTV {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (Γsame : Finset (Fin (A.popSize r) → Bool))
    (Γind : Finset (Fin (A.popSize r) × Bool → Bool)) : ℝ :=
  sSup {d : ℝ | ∃ φ : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ,
    (∀ o, 0 ≤ φ o ∧ φ o ≤ 1) ∧
    d = |conditionedSameExpectation A r Γsame φ -
      conditionedIndependentExpectation A r Γind φ|}

/-- The support-wise diagonal certificate used by the fuzzy-hypothesis argument. -/
noncomputable def QVDiagonalCertificate {M : ℕ} (A : ScheduleArray M)
    (p rho B cSigma dSame dInd : ℝ) : Prop :=
  ∃ (Γsame : ∀ r, Finset (Fin (A.popSize r) → Bool))
    (Γind : ∀ r, Finset (Fin (A.popSize r) × Bool → Bool)),
    Tendsto (fun r => (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame r))
      atTop (nhds 1) ∧
    Tendsto (fun r => (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind r))
      atTop (nhds 1) ∧
    (∀ u : ∀ r, Fin (A.popSize r) → Bool,
      (∀ r, u r ∈ Γsame r) →
      DenseScheduleClass
        (A.withSchedule fun r => samePriorSchedule (A.popSize r) M (u r))
        p rho B cSigma) ∧
    (∀ u : ∀ r, Fin (A.popSize r) × Bool → Bool,
      (∀ r, u r ∈ Γind r) →
      DenseScheduleClass
        (A.withSchedule fun r => independentPriorSchedule (A.popSize r) M (u r))
        p rho B cSigma) ∧
    Tendsto (fun r => conditionedMixtureTV A r (Γsame r) (Γind r)) atTop (nhds 0) ∧
    Tendsto (fun r => sSup {x : ℝ | ∃ u ∈ Γsame r,
      x = |sameScaledVariance A r u - dSame|}) atTop (nhds 0) ∧
    Tendsto (fun r => sSup {x : ℝ | ∃ u ∈ Γind r,
      x = |independentScaledVariance A r u - dInd|}) atTop (nhds 0)

/-- Worst-case rowwise relative-error probability over the dense class with the
fixed design skeleton `A`. -/
noncomputable def worstCaseRatioError {M : ℕ} (A : ScheduleArray M)
    (p rho B cSigma : ℝ)
    (S : ∀ r, VarianceStatistic (A.popSize r) M (A.groups r) (A.treated r))
    (ε : ℝ) (r : ℕ) : ℝ :=
  sSup {q : ℝ | ∃ Y : ∀ r, PotentialOutcome (A.popSize r) M,
    DenseScheduleClass (A.withSchedule Y) p rho B cSigma ∧
    q = (A.design r).Pr (fun w =>
      |S r (observe (A.popSize r) M (A.groups r) (A.treated r) (Y r) w) /
        sigmaSq (Y r) (A.grouped_le r) (A.treated_pos r) (A.treated_lt r) - 1| > ε)}

-- @node: conditionedFiniteExpectation_nonneg
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,f,hf), [the stated expectation identity holds](goal). -/
lemma conditionedFiniteExpectation_nonneg {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (D : FiniteDesign Ω) (Γ : Finset Ω) (f : Ω → ℝ)
    (hf : ∀ w, 0 ≤ f w) :
    0 ≤ D.E (fun w => if w ∈ Γ then f w else 0) /
      D.Pr (fun w => w ∈ Γ) := by
  exact div_nonneg (D.E_nonneg fun w => by split <;> simp_all) (D.Pr_nonneg _)

-- @node: conditionedFiniteExpectation_le
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,f,c,hq,hf), [the stated expectation identity holds](goal). -/
lemma conditionedFiniteExpectation_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (D : FiniteDesign Ω) (Γ : Finset Ω) (f : Ω → ℝ) (c : ℝ)
    (hq : 0 < D.Pr (fun w => w ∈ Γ)) (hf : ∀ w, w ∈ Γ → f w ≤ c) :
    D.E (fun w => if w ∈ Γ then f w else 0) /
        D.Pr (fun w => w ∈ Γ) ≤ c := by
  rw [div_le_iff₀ hq]
  unfold FiniteDesign.E FiniteDesign.Pr FiniteDesign.ind
  calc
    (∑ w, D.p w * if w ∈ Γ then f w else 0) ≤
        ∑ w, D.p w * if w ∈ Γ then c else 0 := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : w ∈ Γ
      · simpa [hw] using mul_le_mul_of_nonneg_left (hf w hw) (D.p_nonneg w)
      · simp [hw]
    _ = c * ∑ w, D.p w * if w ∈ Γ then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w ∈ Γ <;> simp [hw]; ring

-- @node: conditionedFiniteExpectation_compl
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:D,f,hq), [the stated expectation identity holds](goal). -/
lemma conditionedFiniteExpectation_compl {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (D : FiniteDesign Ω) (Γ : Finset Ω) (f : Ω → ℝ)
    (hq : 0 < D.Pr (fun w => w ∈ Γ)) :
    D.E (fun w => if w ∈ Γ then 1 - f w else 0) /
        D.Pr (fun w => w ∈ Γ) =
      1 - D.E (fun w => if w ∈ Γ then f w else 0) /
        D.Pr (fun w => w ∈ Γ) := by
  have hnum : D.E (fun w => if w ∈ Γ then 1 - f w else 0) =
      D.Pr (fun w => w ∈ Γ) - D.E (fun w => if w ∈ Γ then f w else 0) := by
    change (∑ w, D.p w * (if w ∈ Γ then 1 - f w else 0)) =
      (∑ w, D.p w * (if w ∈ Γ then 1 else 0)) -
        ∑ w, D.p w * (if w ∈ Γ then f w else 0)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w ∈ Γ <;> simp [hw]; ring
  rw [hnum]
  field_simp [hq.ne']

-- @node: tendsto_of_eventually_uniform_support_error
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:X,c,Γ,e,he,hbound,u,hu), [the indicated sequence converges to its stated limit](goal). -/
lemma tendsto_of_eventually_uniform_support_error {Ω : ℕ → Type*}
    (X : ∀ r, Ω r → ℝ) (c : ℝ) (Γ : ∀ r, Finset (Ω r)) (e : ℕ → ℝ)
    (he : Tendsto e atTop (nhds 0))
    (hbound : ∀ r w, w ∈ Γ r → |X r w - c| < e r)
    (u : ∀ r, Ω r) (hu : ∀ᶠ r in atTop, u r ∈ Γ r) :
    Tendsto (fun r => X r (u r)) atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ r in atTop, e r < ε := (tendsto_order.1 he).2 ε hε
  apply eventually_atTop.1
  filter_upwards [hu, hev] with r hur hr
  simpa [Real.dist_eq] using (hbound r (u r) hur).trans hr

-- @node: ratio_good_implies_same_decision
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:hb,hab,hη,hε,hg,hσ0,hv,hr), [the ratio good implies same decision result holds](goal). -/
lemma ratio_good_implies_same_decision {a b η ε g σ s : ℝ}
    (hb : 0 < b) (hab : b < a) (hη : η = (a - b) / 8)
    (hε : ε = (a - b) / (8 * a)) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hv : |g * σ - a| < η) (hr : |s / σ - 1| ≤ ε) :
    (a + b) / 2 < g * s := by
  have ha : 0 < a := hb.trans hab
  have hgap : 0 < a - b := sub_pos.mpr hab
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηgap : η < a - b := by rw [hη]; nlinarith
  have hvlow : a - η < g * σ := by linarith [(abs_lt.mp hv).1]
  have hvpos : 0 < g * σ := by nlinarith
  have hσ : 0 < σ := by nlinarith
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεone : ε < 1 := by
    rw [hε, div_lt_one (by positivity : 0 < 8 * a)]
    nlinarith
  have hrlow : 1 - ε ≤ s / σ := by
    have := (abs_le.mp hr).1
    linarith
  have hbasepos : 0 < a - η := by rw [hη]; nlinarith
  have hmul : (1 - ε) * (a - η) < (s / σ) * (g * σ) :=
    (mul_lt_mul_of_pos_left hvlow (by linarith)).trans_le
      (mul_le_mul_of_nonneg_right hrlow hvpos.le)
  have hid : (s / σ) * (g * σ) = g * s := by field_simp
  rw [hid] at hmul
  have hmargin : (a + b) / 2 < (1 - ε) * (a - η) := by
    rw [hη, hε]
    field_simp [ha.ne']
    nlinarith
  exact hmargin.trans hmul

-- @node: ratio_good_implies_independent_decision
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:hb,hab,hη,hε,hg,hσ0,hv,hr), [the ratio good implies independent decision result holds](goal). -/
lemma ratio_good_implies_independent_decision {a b η ε g σ s : ℝ}
    (hb : 0 < b) (hab : b < a) (hη : η = (a - b) / 8)
    (hε : ε = (a - b) / (8 * a)) (hg : 0 < g) (hσ0 : 0 ≤ σ)
    (hv : |g * σ - b| < η) (hr : |s / σ - 1| ≤ ε) :
    g * s < (a + b) / 2 := by
  have ha : 0 < a := hb.trans hab
  have hgap : 0 < a - b := sub_pos.mpr hab
  have hηpos : 0 < η := by rw [hη]; positivity
  have hvup : g * σ < b + η := by linarith [(abs_lt.mp hv).2]
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεone : ε < 1 := by
    rw [hε, div_lt_one (by positivity : 0 < 8 * a)]
    nlinarith
  have hσ : 0 < σ := by
    rcases hσ0.eq_or_lt with hσeq | hσlt
    · subst σ
      simp at hr
      linarith
    · exact hσlt
  have hvpos : 0 < g * σ := mul_pos hg hσ
  have hrup : s / σ ≤ 1 + ε := by
    have := (abs_le.mp hr).2
    linarith
  have hupperpos : 0 < b + η := hvpos.trans hvup
  have hmul : (s / σ) * (g * σ) < (1 + ε) * (b + η) :=
    (mul_le_mul_of_nonneg_right hrup hvpos.le).trans_lt
      (mul_lt_mul_of_pos_left hvup (by positivity))
  have hid : (s / σ) * (g * σ) = g * s := by field_simp
  rw [hid] at hmul
  have hmargin : (1 + ε) * (b + η) < (a + b) / 2 := by
    rw [hη, hε]
    field_simp [ha.ne']
    nlinarith
  exact hmul.trans hmargin

-- @node: conditionedMixtureTV_le_complements
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,r,hs,hi), [the stated bound holds](goal). -/
lemma conditionedMixtureTV_le_complements {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (Γsame : Finset (Fin (A.popSize r) → Bool))
    (Γind : Finset (Fin (A.popSize r) × Bool → Bool))
    (hs : 0 < (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame))
    (hi : 0 < (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind)) :
    conditionedMixtureTV A r Γsame Γind ≤
      2 * (1 - (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame)) +
      2 * (1 - (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind)) := by
  let C := 2 * (1 - (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame)) +
    2 * (1 - (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind))
  have hbound : ∀ d ∈ {d : ℝ | ∃ φ : ObservedData (A.popSize r) M
      (A.groups r) (A.treated r) → ℝ,
      (∀ o, 0 ≤ φ o ∧ φ o ≤ 1) ∧
      d = |conditionedSameExpectation A r Γsame φ -
        conditionedIndependentExpectation A r Γind φ|}, d ≤ C := by
    rintro d ⟨φ, hφ, rfl⟩
    have hsu := abs_conditionedExpectation_sub_le_two_compl
      (priorSame (A.popSize r)) Γsame
      (fun u => (A.design r).E (fun w => φ (observe (A.popSize r) M
        (A.groups r) (A.treated r) (samePriorSchedule (A.popSize r) M u) w)))
      (fun u => ⟨(A.design r).E_nonneg (fun w => (hφ (observe
          (A.popSize r) M (A.groups r) (A.treated r)
          (samePriorSchedule (A.popSize r) M u) w)).1),
        (A.design r).E_le_one (fun w => (hφ (observe
          (A.popSize r) M (A.groups r) (A.treated r)
          (samePriorSchedule (A.popSize r) M u) w)).2)⟩) hs
    have hiu := abs_conditionedExpectation_sub_le_two_compl
      (priorIndependent (A.popSize r)) Γind
      (fun u => (A.design r).E (fun w => φ (observe (A.popSize r) M
        (A.groups r) (A.treated r) (independentPriorSchedule (A.popSize r) M u) w)))
      (fun u => ⟨(A.design r).E_nonneg (fun w => (hφ (observe
          (A.popSize r) M (A.groups r) (A.treated r)
          (independentPriorSchedule (A.popSize r) M u) w)).1),
        (A.design r).E_le_one (fun w => (hφ (observe
          (A.popSize r) M (A.groups r) (A.treated r)
          (independentPriorSchedule (A.popSize r) M u) w)).2)⟩) hi
    have hsu' : |conditionedSameExpectation A r Γsame φ -
        sameObservedExpectation A r φ| ≤
        2 * (1 - (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame)) := by
      simpa [conditionedSameExpectation, sameObservedExpectation] using hsu
    have hiu' : |independentObservedExpectation A r φ -
        conditionedIndependentExpectation A r Γind φ| ≤
        2 * (1 - (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind)) := by
      simpa [conditionedIndependentExpectation, independentObservedExpectation,
        abs_sub_comm] using hiu
    have htri := abs_sub_le (conditionedSameExpectation A r Γsame φ)
      (sameObservedExpectation A r φ) (conditionedIndependentExpectation A r Γind φ)
    have hiu'' : |sameObservedExpectation A r φ -
        conditionedIndependentExpectation A r Γind φ| ≤
        2 * (1 - (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind)) := by
      rw [sameObservedExpectation_eq_independent A r φ]
      exact hiu'
    exact htri.trans (by dsimp [C]; exact add_le_add hsu' hiu'')
  unfold conditionedMixtureTV
  apply csSup_le
  · refine ⟨0, ?_⟩
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro o
      norm_num
    · simp [conditionedSameExpectation, conditionedIndependentExpectation]
  · intro d hd
    exact hbound d hd

-- @node: thm:qv-diagonal-impossibility
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,rho,B,cSigma,hrho,hB,hGroupCountGrowth,hStableTreatmentFraction,hSamplingFractionLimit,J,hJohnsonOrthogonalDecomposition_of_gate,hKneserAdjacencySpectrum_of_gate,hcSigma), [the qv diagonal impossibility result holds](goal). -/
theorem qv_diagonal_impossibility {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p rho B cSigma : ℝ) (hrho : 0 < rho) (hB : 1 ≤ B)
    (hGroupCountGrowth : GroupCountGrowth A)
    (hStableTreatmentFraction : StableTreatmentFraction A p)
    (hSamplingFractionLimit : SamplingFractionLimit A rho)
    (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hJohnsonOrthogonalDecomposition_of_gate :
      ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneserAdjacencySpectrum_of_gate :
      ∀ r, KneserAdjacencySpectrum (A.popSize r) M)
    (hcSigma : 0 < cSigma ∧
      cSigma < 1 / ((M : ℝ) * p * (1 - p)) - 2 * rho / (M : ℝ)) :
    let dSame := 1 / ((M : ℝ) * p * (1 - p))
    let dInd := dSame - 2 * rho / (M : ℝ)
    QVDiagonalCertificate A p rho B cSigma dSame dInd ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ S,
      (1 : ℝ) / 2 ≤ Filter.liminf
        (fun r => worstCaseRatioError A p rho B cSigma S ε r) atTop := by
  dsimp only
  let dSame : ℝ := 1 / ((M : ℝ) * p * (1 - p))
  let dInd : ℝ := dSame - 2 * rho / (M : ℝ)
  obtain ⟨heq, _, _, _, _, hsame, hind, hgap, _, _⟩ :=
    rademacher_mixture_separation hM A p rho hrho J hGroupCountGrowth
      hStableTreatmentFraction hSamplingFractionLimit
      hJohnsonOrthogonalDecomposition_of_gate hKneserAdjacencySpectrum_of_gate
  obtain ⟨Γsame, es, hΓsame, hes, hes0, hsameBound, hsameSup⟩ :=
    FiniteDesign.TendstoInProb.exists_uniform_support hsame
  obtain ⟨Γind, ei, hΓind, hei, hei0, hindBound, hindSup⟩ :=
    FiniteDesign.TendstoInProb.exists_uniform_support hind
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hdInd : cSigma < dInd := by simpa [dInd, dSame] using hcSigma.2
  have hdSame : cSigma < dSame := by
    have := hgap
    dsimp [dSame, dInd] at hdInd ⊢
    linarith
  have hclassSame : ∀ u : ∀ r, Fin (A.popSize r) → Bool,
      (∀ r, u r ∈ Γsame r) →
      DenseScheduleClass
        (A.withSchedule fun r => samePriorSchedule (A.popSize r) M (u r))
        p rho B cSigma := by
    intro u hu
    apply denseClass_withSchedule_of_scaled_tendsto A p rho B cSigma dSame
      hGroupCountGrowth hStableTreatmentFraction hSamplingFractionLimit
      hB0 hcSigma.1 hdSame
    · intro r S i z
      cases h : u r i.1 <;> simp [samePriorSchedule, rademacherSign, h, hB]
    · exact tendsto_of_uniform_support_error (sameScaledVariance A) dSame
        Γsame es hes hes0 hsameBound u hu
  have hclassInd : ∀ u : ∀ r, Fin (A.popSize r) × Bool → Bool,
      (∀ r, u r ∈ Γind r) →
      DenseScheduleClass
        (A.withSchedule fun r => independentPriorSchedule (A.popSize r) M (u r))
        p rho B cSigma := by
    intro u hu
    apply denseClass_withSchedule_of_scaled_tendsto A p rho B cSigma dInd
      hGroupCountGrowth hStableTreatmentFraction hSamplingFractionLimit
      hB0 hcSigma.1 hdInd
    · intro r S i z
      cases h : u r (i.1, z) <;>
        simp [independentPriorSchedule, rademacherSign, h, hB]
    · exact tendsto_of_uniform_support_error (independentScaledVariance A) dInd
        Γind ei hei hei0 hindBound u hu
  have hTV : Tendsto (fun r => conditionedMixtureTV A r (Γsame r) (Γind r))
      atTop (nhds 0) := by
    have hspos : ∀ᶠ r in atTop,
        0 < (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame r) :=
      (tendsto_order.1 hΓsame).1 0 (by norm_num)
    have hipos : ∀ᶠ r in atTop,
        0 < (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind r) :=
      (tendsto_order.1 hΓind).1 0 (by norm_num)
    have hupp : Tendsto (fun r =>
        2 * (1 - (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame r)) +
        2 * (1 - (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind r)))
        atTop (nhds 0) := by
      convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub hΓsame)).add
        (tendsto_const_nhds.mul (tendsto_const_nhds.sub hΓind)) using 1; norm_num
    apply squeeze_zero' _ _ hupp
    · filter_upwards [hspos, hipos] with r hsr hir
      unfold conditionedMixtureTV
      have hmem : (0 : ℝ) ∈ {d : ℝ | ∃ φ : ObservedData (A.popSize r) M
          (A.groups r) (A.treated r) → ℝ,
          (∀ o, 0 ≤ φ o ∧ φ o ≤ 1) ∧
          d = |conditionedSameExpectation A r (Γsame r) φ -
            conditionedIndependentExpectation A r (Γind r) φ|} := by
        refine ⟨fun _ => 0, (by norm_num), ?_⟩
        simp [conditionedSameExpectation, conditionedIndependentExpectation]
      by_cases hb : BddAbove {d : ℝ | ∃ φ : ObservedData (A.popSize r) M
          (A.groups r) (A.treated r) → ℝ,
          (∀ o, 0 ≤ φ o ∧ φ o ≤ 1) ∧
          d = |conditionedSameExpectation A r (Γsame r) φ -
            conditionedIndependentExpectation A r (Γind r) φ|}
      · exact le_csSup hb hmem
      · rw [csSup_of_not_bddAbove hb]
        simp
    · filter_upwards [hspos, hipos] with r hsr hir
      exact conditionedMixtureTV_le_complements A r (Γsame r) (Γind r) hsr hir
  refine ⟨⟨Γsame, Γind, hΓsame, hΓind, hclassSame, hclassInd,
    hTV, hsameSup, hindSup⟩, ?_⟩
  classical
  have hdIndPos : 0 < dInd := hcSigma.1.trans hdInd
  have hdOrder : dInd < dSame := by simpa [dInd] using hgap
  let ε : ℝ := (dSame - dInd) / (8 * dSame)
  let η : ℝ := (dSame - dInd) / 8
  have hεpos : 0 < ε := by
    exact div_pos (sub_pos.mpr hdOrder) (mul_pos (by norm_num) (hdIndPos.trans hdOrder))
  have hηpos : 0 < η := by exact div_pos (sub_pos.mpr hdOrder) (by norm_num)
  refine ⟨ε, hεpos, fun S => ?_⟩
  have hspos : ∀ᶠ r in atTop,
      0 < (priorSame (A.popSize r)).Pr (fun u => u ∈ Γsame r) :=
    (tendsto_order.1 hΓsame).1 0 (by norm_num)
  have hipos : ∀ᶠ r in atTop,
      0 < (priorIndependent (A.popSize r)).Pr (fun u => u ∈ Γind r) :=
    (tendsto_order.1 hΓind).1 0 (by norm_num)
  have hsnonempty : ∀ᶠ r in atTop, (Γsame r).Nonempty := by
    filter_upwards [hspos] with r hr
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp [hn, FiniteDesign.Pr, FiniteDesign.E, FiniteDesign.ind] at hr
  have hinonempty : ∀ᶠ r in atTop, (Γind r).Nonempty := by
    filter_upwards [hipos] with r hr
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp [hn, FiniteDesign.Pr, FiniteDesign.E, FiniteDesign.ind] at hr
  have hessmall : ∀ᶠ r in atTop, es r < η :=
    (tendsto_order.1 hes).2 η hηpos
  have heismall : ∀ᶠ r in atTop, ei r < η :=
    (tendsto_order.1 hei).2 η hηpos
  have hrow : ∀ᶠ r in atTop,
      (1 - conditionedMixtureTV A r (Γsame r) (Γind r)) / 2 ≤
        worstCaseRatioError A p rho B cSigma S ε r := by
    filter_upwards [hspos, hipos, hsnonempty, hinonempty, hessmall, heismall]
      with r hsp hip hsne hine hse hie
    let threshold : ℝ := (dSame + dInd) / 2
    let sameWrong : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ :=
      fun o => if (A.groups r : ℝ) * S r o > threshold then 0 else 1
    let indWrong : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ :=
      fun o => if (A.groups r : ℝ) * S r o > threshold then 1 else 0
    have hsameWrong_le : conditionedSameExpectation A r (Γsame r) sameWrong ≤
        worstCaseRatioError A p rho B cSigma S ε r := by
      apply conditionedFiniteExpectation_le _ _ _ _ hsp
      intro u hu
      have hsubset : ∀ w, sameWrong (observe (A.popSize r) M (A.groups r)
          (A.treated r) (samePriorSchedule (A.popSize r) M u) w) = 1 →
          |S r (observe (A.popSize r) M (A.groups r) (A.treated r)
            (samePriorSchedule (A.popSize r) M u) w) /
            sigmaSq (samePriorSchedule (A.popSize r) M u) (A.grouped_le r)
              (A.treated_pos r) (A.treated_lt r) - 1| > ε := by
        intro w hw
        by_contra hgood
        have hgood' : |S r (observe (A.popSize r) M (A.groups r) (A.treated r)
            (samePriorSchedule (A.popSize r) M u) w) /
            sigmaSq (samePriorSchedule (A.popSize r) M u) (A.grouped_le r)
              (A.treated_pos r) (A.treated_lt r) - 1| ≤ ε := le_of_not_gt hgood
        have hvar := ratio_good_implies_same_decision hdIndPos hdOrder rfl rfl
          (by exact_mod_cast A.groups_pos r)
          ((A.design r).Var_nonneg (pameHat (samePriorSchedule (A.popSize r) M u)
            (A.treated_pos r) (A.treated_lt r)))
          (lt_trans (hsameBound r u hu) hse) hgood'
        simp [sameWrong, threshold, hvar] at hw
      have hpr : (A.design r).Pr (fun w => sameWrong (observe (A.popSize r) M
          (A.groups r) (A.treated r) (samePriorSchedule (A.popSize r) M u) w) = 1) ≤
          (A.design r).Pr (fun w =>
            |S r (observe (A.popSize r) M (A.groups r) (A.treated r)
              (samePriorSchedule (A.popSize r) M u) w) /
              sigmaSq (samePriorSchedule (A.popSize r) M u) (A.grouped_le r)
                (A.treated_pos r) (A.treated_lt r) - 1| > ε) :=
        (A.design r).Pr_mono _ _ hsubset
      have hclass : ∃ Y : ∀ k, PotentialOutcome (A.popSize k) M,
          DenseScheduleClass (A.withSchedule Y) p rho B cSigma ∧
          Y r = samePriorSchedule (A.popSize r) M u := by
        let base : ∀ k, Fin (A.popSize k) → Bool := fun k =>
          if hk : (Γsame k).Nonempty then hk.choose else fun _ => false
        let us : ∀ k, Fin (A.popSize k) → Bool := fun k =>
          if hkr : k = r then hkr ▸ u else base k
        have humem : ∀ᶠ k in atTop, us k ∈ Γsame k := by
          filter_upwards [hsnonempty] with k hk
          by_cases hkr : k = r
          · subst k
            simpa [us] using hu
          · simp [us, hkr, base, hk, hk.choose_spec]
        refine ⟨fun k => samePriorSchedule (A.popSize k) M (us k), ?_, by simp [us]⟩
        apply denseClass_withSchedule_of_scaled_tendsto A p rho B cSigma dSame
          hGroupCountGrowth hStableTreatmentFraction hSamplingFractionLimit
          hB0 hcSigma.1 hdSame
        · intro k T i z
          cases h : us k i.1 <;> simp [samePriorSchedule, rademacherSign, h, hB]
        · exact tendsto_of_eventually_uniform_support_error
            (sameScaledVariance A) dSame Γsame es hes hsameBound us humem
      obtain ⟨Y, hYclass, hYr⟩ := hclass
      calc
        (A.design r).E (fun w => sameWrong (observe (A.popSize r) M
            (A.groups r) (A.treated r) (samePriorSchedule (A.popSize r) M u) w)) =
            (A.design r).Pr (fun w => sameWrong (observe (A.popSize r) M
              (A.groups r) (A.treated r) (samePriorSchedule (A.popSize r) M u) w) = 1) := by
              apply (A.design r).E_congr
              intro w
              simp only [FiniteDesign.ind]
              by_cases hw : (A.groups r : ℝ) * S r (observe (A.popSize r) M
                (A.groups r) (A.treated r) (samePriorSchedule (A.popSize r) M u) w) > threshold <;>
                simp [sameWrong, hw]
        _ ≤ (A.design r).Pr (fun w =>
            |S r (observe (A.popSize r) M (A.groups r) (A.treated r)
              (samePriorSchedule (A.popSize r) M u) w) /
              sigmaSq (samePriorSchedule (A.popSize r) M u) (A.grouped_le r)
                (A.treated_pos r) (A.treated_lt r) - 1| > ε) := hpr
        _ ≤ worstCaseRatioError A p rho B cSigma S ε r := by
          unfold worstCaseRatioError
          apply le_csSup
          · refine ⟨1, ?_⟩
            rintro q ⟨Y', _, rfl⟩
            exact (A.design r).Pr_le_one _
          · refine ⟨Y, hYclass, ?_⟩
            rw [hYr]
    have hindWrong_le : conditionedIndependentExpectation A r (Γind r) indWrong ≤
        worstCaseRatioError A p rho B cSigma S ε r := by
      apply conditionedFiniteExpectation_le _ _ _ _ hip
      intro u hu
      have hsubset : ∀ w, indWrong (observe (A.popSize r) M (A.groups r)
          (A.treated r) (independentPriorSchedule (A.popSize r) M u) w) = 1 →
          |S r (observe (A.popSize r) M (A.groups r) (A.treated r)
            (independentPriorSchedule (A.popSize r) M u) w) /
            sigmaSq (independentPriorSchedule (A.popSize r) M u) (A.grouped_le r)
              (A.treated_pos r) (A.treated_lt r) - 1| > ε := by
        intro w hw
        by_contra hgood
        have hgood' := le_of_not_gt hgood
        have hvar := ratio_good_implies_independent_decision hdIndPos hdOrder rfl rfl
          (by exact_mod_cast A.groups_pos r)
          ((A.design r).Var_nonneg (pameHat (independentPriorSchedule (A.popSize r) M u)
            (A.treated_pos r) (A.treated_lt r)))
          (lt_trans (hindBound r u hu) hie) hgood'
        simp [indWrong, threshold, not_lt_of_ge hvar.le] at hw
      have hpr := (A.design r).Pr_mono _ _ hsubset
      let base : ∀ k, Fin (A.popSize k) × Bool → Bool := fun k =>
        if hk : (Γind k).Nonempty then hk.choose else fun _ => false
      let ui : ∀ k, Fin (A.popSize k) × Bool → Bool := fun k =>
        if hkr : k = r then hkr ▸ u else base k
      have humem : ∀ᶠ k in atTop, ui k ∈ Γind k := by
        filter_upwards [hinonempty] with k hk
        by_cases hkr : k = r
        · subst k
          simpa [ui] using hu
        · simp [ui, hkr, base, hk, hk.choose_spec]
      let Y : ∀ k, PotentialOutcome (A.popSize k) M := fun k =>
        independentPriorSchedule (A.popSize k) M (ui k)
      have hYclass : DenseScheduleClass (A.withSchedule Y) p rho B cSigma := by
        apply denseClass_withSchedule_of_scaled_tendsto A p rho B cSigma dInd
          hGroupCountGrowth hStableTreatmentFraction hSamplingFractionLimit
          hB0 hcSigma.1 hdInd
        · intro k T i z
          cases h : ui k (i.1, z) <;>
            simp [Y, independentPriorSchedule, rademacherSign, h, hB]
        · exact tendsto_of_eventually_uniform_support_error
            (independentScaledVariance A) dInd Γind ei hei hindBound ui humem
      calc
        (A.design r).E (fun w => indWrong (observe (A.popSize r) M
            (A.groups r) (A.treated r) (independentPriorSchedule (A.popSize r) M u) w)) ≤
            (A.design r).Pr (fun w =>
              |S r (observe (A.popSize r) M (A.groups r) (A.treated r)
                (independentPriorSchedule (A.popSize r) M u) w) /
                sigmaSq (independentPriorSchedule (A.popSize r) M u) (A.grouped_le r)
                  (A.treated_pos r) (A.treated_lt r) - 1| > ε) := by
              rw [show (A.design r).E (fun w => indWrong (observe (A.popSize r) M
                (A.groups r) (A.treated r) (independentPriorSchedule (A.popSize r) M u) w)) =
                (A.design r).Pr (fun w => indWrong (observe (A.popSize r) M
                  (A.groups r) (A.treated r) (independentPriorSchedule (A.popSize r) M u) w) = 1) by
                apply (A.design r).E_congr
                intro w
                simp only [FiniteDesign.ind]
                by_cases hw : (A.groups r : ℝ) * S r (observe (A.popSize r) M
                  (A.groups r) (A.treated r) (independentPriorSchedule (A.popSize r) M u) w) > threshold <;>
                  simp [indWrong, hw]]
              exact hpr
        _ ≤ worstCaseRatioError A p rho B cSigma S ε r := by
          unfold worstCaseRatioError
          apply le_csSup
          · refine ⟨1, ?_⟩
            rintro q ⟨Y', _, rfl⟩
            exact (A.design r).Pr_le_one _
          · refine ⟨Y, hYclass, ?_⟩
            simp [Y, ui]
    have htest : 1 - conditionedMixtureTV A r (Γsame r) (Γind r) ≤
        conditionedSameExpectation A r (Γsame r) sameWrong +
          conditionedIndependentExpectation A r (Γind r) indWrong := by
      have hcomp : conditionedIndependentExpectation A r (Γind r) sameWrong =
          1 - conditionedIndependentExpectation A r (Γind r) indWrong := by
        unfold conditionedIndependentExpectation
        convert conditionedFiniteExpectation_compl (priorIndependent (A.popSize r))
          (Γind r) (fun u => (A.design r).E (fun w => indWrong (observe
            (A.popSize r) M (A.groups r) (A.treated r)
            (independentPriorSchedule (A.popSize r) M u) w))) hip using 1
        congr 1
        apply (priorIndependent (A.popSize r)).E_congr
        intro u
        split
        · rw [← (A.design r).E_const 1, ← (A.design r).E_sub]
          apply (A.design r).E_congr
          intro w
          by_cases hw : (A.groups r : ℝ) * S r (observe (A.popSize r) M
            (A.groups r) (A.treated r) (independentPriorSchedule (A.popSize r) M u) w) > threshold <;>
            simp [sameWrong, indWrong, hw]
        · rfl
      have hbdd : BddAbove {d : ℝ | ∃ φ : ObservedData (A.popSize r) M
          (A.groups r) (A.treated r) → ℝ, (∀ o, 0 ≤ φ o ∧ φ o ≤ 1) ∧
          d = |conditionedSameExpectation A r (Γsame r) φ -
            conditionedIndependentExpectation A r (Γind r) φ|} := by
        refine ⟨1, ?_⟩
        rintro d ⟨φ, hφ, rfl⟩
        have hs0 : 0 ≤ conditionedSameExpectation A r (Γsame r) φ :=
          conditionedFiniteExpectation_nonneg _ _ _ fun u =>
            (A.design r).E_nonneg fun w => (hφ _).1
        have hs1 : conditionedSameExpectation A r (Γsame r) φ ≤ 1 := by
          apply conditionedFiniteExpectation_le _ _ _ _ hsp
          intro u _
          exact (A.design r).E_le_one fun w => (hφ _).2
        have hi0 : 0 ≤ conditionedIndependentExpectation A r (Γind r) φ :=
          conditionedFiniteExpectation_nonneg _ _ _ fun u =>
            (A.design r).E_nonneg fun w => (hφ _).1
        have hi1 : conditionedIndependentExpectation A r (Γind r) φ ≤ 1 := by
          apply conditionedFiniteExpectation_le _ _ _ _ hip
          intro u _
          exact (A.design r).E_le_one fun w => (hφ _).2
        rw [abs_le]
        constructor <;> linarith
      have hmember : |conditionedSameExpectation A r (Γsame r) sameWrong -
          conditionedIndependentExpectation A r (Γind r) sameWrong| ≤
          conditionedMixtureTV A r (Γsame r) (Γind r) := by
        unfold conditionedMixtureTV
        apply le_csSup hbdd
        refine ⟨sameWrong, ?_, rfl⟩
        intro o
        by_cases ho : (A.groups r : ℝ) * S r o > threshold <;>
          simp [sameWrong, ho]
      rw [hcomp] at hmember
      have hsigned := neg_le_of_abs_le hmember
      linarith
    linarith
  have ht : Tendsto (fun r =>
      (1 - conditionedMixtureTV A r (Γsame r) (Γind r)) / 2)
      atTop (nhds ((1 : ℝ) / 2)) := by
    convert (tendsto_const_nhds.sub hTV).div_const 2 using 1; norm_num
  have hWle : ∀ r, worstCaseRatioError A p rho B cSigma S ε r ≤ 1 := by
    intro r
    unfold worstCaseRatioError
    by_cases hn : {q : ℝ | ∃ Y : ∀ k, PotentialOutcome (A.popSize k) M,
        DenseScheduleClass (A.withSchedule Y) p rho B cSigma ∧
        q = (A.design r).Pr (fun w =>
          |S r (observe (A.popSize r) M (A.groups r) (A.treated r) (Y r) w) /
            sigmaSq (Y r) (A.grouped_le r) (A.treated_pos r) (A.treated_lt r) - 1| > ε)}.Nonempty
    · apply csSup_le hn
      rintro q ⟨Y, _, rfl⟩
      exact (A.design r).Pr_le_one _
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      norm_num
  have hlim := Filter.liminf_le_liminf hrow ht.isBoundedUnder_ge
    (isCoboundedUnder_ge_of_le atTop hWle)
  rw [ht.liminf_eq] at hlim
  exact hlim

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
