module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.AnchorLocalizedMeasurability

/-!
# Localized Assouad converse for arbitrary anchor laws

This file proves the localized coupling edge inequality and Assouad witness for
an arbitrary hypercube of unit laws.  The laws need only belong to `AnchorClass`,
share the cube covariate marginal, and obey a one-flip pilot KL budget; the
supplied geometric hypercube scores determine the risk being lower-bounded.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open Causalean.Stat.Nonparametric.HistogramRegression

private lemma sum_anchorLocalizedPairLoss_le_pairLoss {d N K : ℕ}
    (g : XSpace d → ℝ) (Q : Fin K → Set (XSpace d))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (x : MainCovariates N d) (M : Match N) :
    (∑ j : Fin K, anchorLocalizedPairLoss g (Q j) x M) ≤ pairLoss g x M := by
  classical
  unfold anchorLocalizedPairLoss pairLoss
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

private lemma anchor_hypercube_flip_singleton_localizedPairLoss {d N K : ℕ}
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (Q S : Fin K → Set (XSpace d)) (hSQ : ∀ j, S j ⊆ Q j)
    (hsupport : ∀ j y, y ∉ Q j → ψ j y = 0)
    (hcore : ∀ j y, y ∈ S j → ψ j y = 1)
    (θ : Fin K → Bool) (j : Fin K) (x : MainCovariates N d) (M : Match N)
    (i : Fin N) (hi : x i ∈ S j)
    (hunique : ∀ k : Fin N, x k ∈ Q j → k = i) :
    amplitude ^ 2 ≤ anchorLocalizedPairLoss (g θ) (Q j) x M +
      anchorLocalizedPairLoss (g (flipCoordinate θ j)) (Q j) x M := by
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
  have hθ : (1 / 2 : ℝ) * (g θ (x i) - g θ (x (M.val i))) ^ 2 ≤
      anchorLocalizedPairLoss (g θ) (Q j) x M := by
    unfold anchorLocalizedPairLoss
    let F : Fin N → ℝ := fun k => (Q j).indicator
      (fun _ => (g θ (x k) - g θ (x (M.val k))) ^ 2) (x k)
    have hF (k : Fin N) : 0 ≤ F k := by
      dsimp [F]
      by_cases hk : x k ∈ Q j
      · rw [Set.indicator_of_mem hk]; exact sq_nonneg _
      · rw [Set.indicator_of_notMem hk]
    have hsum : F i ≤ ∑ k : Fin N, F k :=
      Finset.single_le_sum (fun k _ => hF k) (Finset.mem_univ i)
    dsimp [F] at hsum ⊢
    rw [Set.indicator_of_mem hiQ] at hsum
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hflip : (1 / 2 : ℝ) *
      (g (flipCoordinate θ j) (x i) - g (flipCoordinate θ j) (x (M.val i))) ^ 2 ≤
      anchorLocalizedPairLoss (g (flipCoordinate θ j)) (Q j) x M := by
    unfold anchorLocalizedPairLoss
    let F : Fin N → ℝ := fun k => (Q j).indicator (fun _ =>
      (g (flipCoordinate θ j) (x k) -
        g (flipCoordinate θ j) (x (M.val k))) ^ 2) (x k)
    have hF (k : Fin N) : 0 ≤ F k := by
      dsimp [F]
      by_cases hk : x k ∈ Q j
      · rw [Set.indicator_of_mem hk]; exact sq_nonneg _
      · rw [Set.indicator_of_notMem hk]
    have hsum : F i ≤ ∑ k : Fin N, F k :=
      Finset.single_le_sum (fun k _ => hF k) (Finset.mem_univ i)
    dsimp [F] at hsum ⊢
    rw [Set.indicator_of_mem hiQ] at hsum
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  nlinarith

/-- For [arbitrary adjacent anchor laws](hyp:hanchor) with supplied [Hölder
hypercube scores](hyp:hL,hβ,hholder), a [pilot coupling](hyp:hΓ)
and the [small-cell occupancy condition](hyp:hsmall) force the [sum of their
localized risks to dominate the overlap-weighted singleton-core loss](goal).
The geometric hypotheses](hyp:hg,hSQ,hsupport,hcore) identify that loss, while
the [cube marginal](hyp:hcov) and [admissible design](hyp:hD) transport it to
the common main-wave law. -/
lemma anchor_hypercube_flip_localizedRisk_edge_of_coupling {d m N K : ℕ}
    {L β cX CX : ℝ}
    (D : Design m N d) (hD : MatchingDesignClass D) (hN : 1 ≤ N)
    (P : (Fin K → Bool) → Measure (UnitRecord d))
    (hanchor : ∀ θ, AnchorClass (P θ) β cX CX)
    (g : (Fin K → Bool) → XSpace d → ℝ)
    (hL : 0 < L) (hβ : 0 < β) (hholder : ∀ θ, HolderScore (g θ) L β)
    (hcov : ∀ θ, (P θ).map Prod.fst = cubeMeasure d)
    (base : XSpace d → ℝ) (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (Q S : Fin K → Set (XSpace d))
    (hQ : ∀ j, MeasurableSet (Q j)) (hS : ∀ j, MeasurableSet (S j))
    (hSQ : ∀ j, S j ⊆ Q j)
    (hsupport : ∀ j y, y ∉ Q j → ψ j y = 0)
    (hcore : ∀ j y, y ∈ S j → ψ j y = 1)
    (θ : Fin K → Bool) (j : Fin K)
    (Γ : Measure (PilotSample m d × PilotSample m d))
    (hΓ : Causalean.Stat.IsCoupling Γ
      (Measure.pi fun _ : Fin m => pilotUnitLaw (P θ))
      (Measure.pi fun _ : Fin m => pilotUnitLaw (P (flipCoordinate θ j))))
    (hsmall : (N : ℝ) * (cubeMeasure d).real (Q j) ≤ 1 / 2) :
    (amplitude ^ 2 / (N : ℝ)) *
        (Γ.real {p | p.1 = p.2} *
          ((N : ℝ) * (cubeMeasure d).real (S j) / 2)) ≤
      anchorLocalizedCubeRisk (P θ) (g θ) (Q j) D +
        anchorLocalizedCubeRisk (P (flipCoordinate θ j))
          (g (flipCoordinate θ j)) (Q j) D := by
  let P₀ := P θ
  let P₁ := P (flipCoordinate θ j)
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
    fun z => anchorLocalizedPairLoss (g θ) (Q j) z.2.1
      (D (z.1, z.2.1, z.2.2)) / (N : ℝ)
  let f₁ : PilotSample m d × (MainCovariates N d × ℝ) → ℝ :=
    fun z => anchorLocalizedPairLoss (g (flipCoordinate θ j)) (Q j) z.2.1
      (D (z.1, z.2.1, z.2.2)) / (N : ℝ)
  letI : IsProbabilityMeasure P₀ := (hanchor θ).covariate_density.1
  letI : IsProbabilityMeasure P₁ :=
    (hanchor (flipCoordinate θ j)).covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P₀) :=
    histogram_pilotUnitLaw_probability P₀ (hanchor θ).covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P₁) :=
    histogram_pilotUnitLaw_probability P₁
      (hanchor (flipCoordinate θ j)).covariate_density.1
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
    exact anchorLocalizedDesignRiskIntegrand_integrable P₀ (hanchor θ) (g θ)
      hL hβ (hholder θ) (hcov θ) (Q j) (hQ j) D hD hN
  have hf₁ : Integrable f₁ (μ₁.prod η) := by
    exact anchorLocalizedDesignRiskIntegrand_integrable P₁
      (hanchor (flipCoordinate θ j)) (g (flipCoordinate θ j))
      hL hβ (hholder (flipCoordinate θ j)) (hcov (flipCoordinate θ j))
      (Q j) (hQ j) D hD hN
  have hedge : (amplitude ^ 2 / (N : ℝ)) * (Γ.prod η).real A ≤
      (∫ z, f₀ z ∂μ₀.prod η) + ∫ z, f₁ z ∂μ₁.prod η := by
    apply coupling_integral_add_lower_of_event μ₀ μ₁ η Γ hΓ f₀ f₁ A
      (amplitude ^ 2 / (N : ℝ)) hf₀ hf₁ hA
    · intro z
      dsimp [f₀]
      exact div_nonneg (anchorLocalizedPairLoss_nonneg _ _ _ _) (Nat.cast_nonneg N)
    · intro z
      dsimp [f₁]
      exact div_nonneg (anchorLocalizedPairLoss_nonneg _ _ _ _) (Nat.cast_nonneg N)
    · intro z hz
      rcases Set.mem_iUnion.mp hz.2 with ⟨i, hi⟩
      have hp := anchor_hypercube_flip_singleton_localizedPairLoss g base amplitude ψ hg
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
    _ = anchorLocalizedCubeRisk P₀ (g θ) (Q j) D +
        anchorLocalizedCubeRisk P₁ (g (flipCoordinate θ j)) (Q j) D := rfl

/-- If [localized cell risks sum below each anchor risk](hyp:hdisj), then the
[finite Assouad edge bounds](hyp:hedge) imply that [one anchor hypercube member
has risk at least half the total edge charge](goal).  The conclusion uses the
[Hölder score bounds](hyp:hL,hβ,hholder), [cube marginals](hyp:hcov), and
[anchor-class laws](hyp:hanchor). -/
lemma exists_anchor_vertex_large_of_localized_edges {d m N K : ℕ} {L β cX CX : ℝ}
    (P : (Fin K → Bool) → Measure (UnitRecord d))
    (hanchor : ∀ θ, AnchorClass (P θ) β cX CX)
    (g : (Fin K → Bool) → XSpace d → ℝ)
    (hL : 0 < L) (hβ : 0 < β) (hholder : ∀ θ, HolderScore (g θ) L β)
    (hcov : ∀ θ, (P θ).map Prod.fst = cubeMeasure d)
    (Q : Fin K → Set (XSpace d)) (hQ : ∀ j, MeasurableSet (Q j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (D : Design m N d) (hD : MatchingDesignClass D) (hN : 1 ≤ N)
    (a : Fin K → ℝ)
    (hedge : ∀ θ j, a j ≤
      anchorLocalizedCubeRisk (P θ) (g θ) (Q j) D +
      anchorLocalizedCubeRisk (P (flipCoordinate θ j))
        (g (flipCoordinate θ j)) (Q j) D) :
    ∃ θ, (∑ j, a j) ≤ 2 * risk (P θ) (g θ) D := by
  let r : (Fin K → Bool) → ℝ := fun θ => risk (P θ) (g θ) D
  let ell : (Fin K → Bool) → Fin K → ℝ := fun θ j =>
    anchorLocalizedCubeRisk (P θ) (g θ) (Q j) D
  have hsum (θ : Fin K → Bool) : (∑ j, ell θ j) ≤ r θ := by
    have hfull := anchorDesignRiskIntegrand_integrable (P θ) (hanchor θ) (g θ)
      hL hβ (hholder θ) (hcov θ) D hD hN
    let μ := (Measure.pi fun _ : Fin m => pilotUnitLaw (P θ)).prod
      ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
    have hj (j : Fin K) : Integrable
        (fun z : PilotSample m d × MainCovariates N d × ℝ =>
          anchorLocalizedPairLoss (g θ) (Q j) z.2.1 (D z) / (N : ℝ)) μ :=
      anchorLocalizedDesignRiskIntegrand_integrable (P θ) (hanchor θ) (g θ)
        hL hβ (hholder θ) (hcov θ) (Q j) (hQ j) D hD hN
    have hrisk := risk_eq_pilot_covariate_integral (P θ) (g θ) D
      (hanchor θ).covariate_density.1 (hcov θ)
      (anchorDesignRiskIntegrand_aestronglyMeasurable
        (P θ) (hanchor θ) (g θ) hL hβ (hholder θ) (hcov θ) D hD)
    dsimp [ell, r]
    rw [hrisk]
    unfold anchorLocalizedCubeRisk
    rw [← integral_finset_sum _ (fun j _ => hj j)]
    apply integral_mono (integrable_finset_sum _ fun j _ => hj j) hfull
    intro z
    change (∑ j : Fin K, anchorLocalizedPairLoss (g θ) (Q j) z.2.1 (D z) /
      (N : ℝ)) ≤ pairLoss (g θ) z.2.1 (D z) / (N : ℝ)
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (sum_anchorLocalizedPairLoss_le_pairLoss (g θ) Q hdisj z.2.1 (D z))
      (Nat.cast_nonneg N)
  exact exists_vertex_large_of_localized_edges r ell a hsum hedge

/-- Given [hypercube geometry](hyp:hKlo,hQside,hdisj,hB,hψ,hamp,hg),
[measurable bumps on the cube](hyp:hψmeas), an [arbitrary anchor-law
realization](hyp:hanchor,hcov), supplied [Hölder bounds](hyp:hL,hβ,hholder),
and [unit one-flip pilot KL](hyp:hkl),
the [small-cell occupancy condition](hyp:hocc) guarantees [a member whose
anchor risk is at least a fixed multiple of the squared Hölder amplitude](goal).
-/
lemma anchor_hypercube_localized_risk_witness {d m N K : ℕ}
    {L β cX CX h c0 c1 : ℝ}
    (Q : Fin K → Set (XSpace d)) (ψ : Fin K → XSpace d → ℝ)
    (B : Fin K → Set (XSpace d))
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ)
    (hKlo : c0 * h ^ (-(d : ℝ)) ≤ K)
    (hQside : ∀ j, IsSideCube h (Q j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hB : ∀ j, B j ⊆ Q j ∧ c0 * h ^ (d : ℝ) ≤ ((cubeMeasure d) (B j)).toReal)
    (hψ : ∀ j x, 0 ≤ ψ j x ∧ ψ j x ≤ 1 ∧ (x ∉ Q j → ψ j x = 0) ∧
      (x ∈ B j → ψ j x = 1))
    (hamp : c1 * h ^ β ≤ amplitude)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (hL : 0 < L) (hβ : 0 < β) (hholder : ∀ θ, HolderScore (g θ) L β)
    (hψmeas : ∀ j, Measurable (fun x : Cube d => ψ j x.val.ofLp))
    (P : (Fin K → Bool) → Measure (UnitRecord d))
    (hanchor : ∀ θ, AnchorClass (P θ) β cX CX)
    (hcov : ∀ θ, (P θ).map Prod.fst = cubeMeasure d)
    (hkl : ∀ θ j, InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw (P θ))
      (Measure.pi fun _ : Fin m => pilotUnitLaw (P (flipCoordinate θ j))) ≤
        ENNReal.ofReal 1)
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hh : 0 < h) (hN : 1 ≤ N)
    (hocc : (N : ℝ) * h ^ (d : ℝ) ≤ 1 / 2)
    (D : Design m N d) (hD : MatchingDesignClass D) :
    ∃ θ, (c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8) * h ^ (2 * β) ≤
      risk (P θ) (g θ) D := by
  classical
  have hamp_pos : 0 < amplitude :=
    lt_of_lt_of_le (mul_pos hc1 (Real.rpow_pos_of_pos hh _)) hamp
  have hQmeas : ∀ j, MeasurableSet (Q j) :=
    fun j => measurableSet_of_isSideCube (hQside j)
  have hcore_exists (j : Fin K) :
      ∃ S : Set (XSpace d), MeasurableSet S ∧ B j ⊆ S ∧ S ⊆ Q j ∧
        (∀ x ∈ S, ψ j x = 1) ∧ cubeMeasure d (B j) ≤ cubeMeasure d S := by
    exact exists_measurable_bump_core (Q j) (B j) (ψ j) (hQside j)
      (hB j).1 (fun x hx => (hψ j x).2.2.1 hx)
      (fun x hx => (hψ j x).2.2.2 hx) (hψmeas j)
  choose S hS hBS hSQ hcore hmass using hcore_exists
  letI : IsProbabilityMeasure (P (fun _ => false)) :=
    (hanchor (fun _ => false)).covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov (fun _ => false)]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hSmass (j : Fin K) : c0 * h ^ (d : ℝ) ≤ (cubeMeasure d).real (S j) :=
    (hB j).2.trans (ENNReal.toReal_mono (by finiteness) (hmass j))
  have hQmass (j : Fin K) : (cubeMeasure d).real (Q j) ≤ h ^ (d : ℝ) := by
    simpa [measureReal_def] using sideCube_cubeMeasure_toReal_le (hQside j) hh.le
  have hsmall (j : Fin K) : (N : ℝ) * (cubeMeasure d).real (Q j) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hQmass j) (Nat.cast_nonneg N)).trans hocc
  let a : Fin K → ℝ := fun _ =>
    (c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)
  have hedge (θ : Fin K → Bool) (j : Fin K) :
      a j ≤ anchorLocalizedCubeRisk (P θ) (g θ) (Q j) D +
        anchorLocalizedCubeRisk (P (flipCoordinate θ j))
          (g (flipCoordinate θ j)) (Q j) D := by
    let μ₀ := Measure.pi fun _ : Fin m => pilotUnitLaw (P θ)
    let μ₁ := Measure.pi fun _ : Fin m => pilotUnitLaw (P (flipCoordinate θ j))
    letI : IsProbabilityMeasure (P θ) := (hanchor θ).covariate_density.1
    letI : IsProbabilityMeasure (P (flipCoordinate θ j)) :=
      (hanchor (flipCoordinate θ j)).covariate_density.1
    letI : IsProbabilityMeasure (pilotUnitLaw (P θ)) :=
      histogram_pilotUnitLaw_probability _ (hanchor θ).covariate_density.1
    letI : IsProbabilityMeasure (pilotUnitLaw (P (flipCoordinate θ j))) :=
      histogram_pilotUnitLaw_probability _
        (hanchor (flipCoordinate θ j)).covariate_density.1
    obtain ⟨Γ, hΓ, hoverlap⟩ := exists_pilot_overlap_coupling μ₀ μ₁
      (by norm_num : (0 : ℝ) ≤ 1) (hkl θ j)
    letI : IsProbabilityMeasure Γ := hΓ.isProbabilityMeasure
    have hoverlapReal : (1 / 2 : ℝ) * Real.exp (-1) ≤
        Γ.real {p | p.1 = p.2} := by
      have ht := ENNReal.toReal_mono (by finiteness : Γ {p | p.1 = p.2} ≠ ⊤) hoverlap
      simpa [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using ht
    have hedge0 := anchor_hypercube_flip_localizedRisk_edge_of_coupling D hD hN
      P hanchor g hL hβ hholder hcov base amplitude ψ hg Q S hQmeas hS hSQ
      (fun k y hy => (hψ k y).2.2.1 hy) hcore θ j Γ hΓ (hsmall j)
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
    have hlower := (mul_le_mul hcoef hmassprod (by positivity) (by positivity)).trans hedge0
    dsimp [a]
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
  obtain ⟨θ, hθ⟩ := exists_anchor_vertex_large_of_localized_edges
    P hanchor g hL hβ hholder hcov Q hQmeas hdisj D hD hN a hedge
  refine ⟨θ, ?_⟩
  have hK : c0 * h ^ (-(d : ℝ)) ≤ (K : ℝ) := hKlo
  have hsum : (∑ j : Fin K, a j) =
      (K : ℝ) * ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)) := by
    simp [a]
  rw [hsum] at hθ
  have hprod : c0 * h ^ (-(d : ℝ)) *
      ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)) ≤
      (K : ℝ) * ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d)) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  have hrpow_cancel : h ^ (-(d : ℝ)) * h ^ (2 * β + d) = h ^ (2 * β) := by
    rw [← Real.rpow_add hh]
    congr 1
    ring
  calc
    (c0 ^ 2 * c1 ^ 2 * Real.exp (-1) / 8) * h ^ (2 * β) =
        (1 / 2 : ℝ) * (c0 * h ^ (-(d : ℝ)) *
          ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d))) := by
      rw [← hrpow_cancel]
      ring
    _ ≤ (1 / 2 : ℝ) * ((K : ℝ) *
        ((c1 ^ 2 * c0 * Real.exp (-1) / 4) * h ^ (2 * β + d))) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ risk (P θ) (g θ) D := by linarith

end CausalSmith.Experimentation.PilotscorePairingFrontier
