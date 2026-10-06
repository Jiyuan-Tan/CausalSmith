module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Anchor.Inverse

/-! Support of the total signed-score law construction in the centered binary
known-radius class, and inverse translation into the binary anchor class. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The total construction always selects a law with a legal propensity and score,
including the zero-score fallback outside the legal latent parameter domain. -/
-- @node: latentToLaw_legal_spec
lemma latentToLaw_legal_spec (n : ℕ) (M rho kappa gamma : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell)
    (hn : 0 < n) (hJ : 0 < J) (hM : 0 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) (hkappa : 0 ≤ kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    ∃ eta : Fin (n - 1) → LatentCell,
      (∀ k, latentPropensity (eta k) ∈ Icc (1 / 4 : ℝ) (3 / 4)) ∧
      (∀ k, latentScore (eta k) ∈ Icc (0 : ℝ) 1) ∧
      LatentLawSpec n M rho kappa gamma J eta
        (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma) := by
  classical
  have hfallback : ∃ eta : Fin (n - 1) → LatentCell,
      (∀ k, latentPropensity (eta k) ∈ Icc (1 / 4 : ℝ) (3 / 4)) ∧
      (∀ k, latentScore (eta k) ∈ Icc (0 : ℝ) 1) ∧
      LatentLawSpec n M rho kappa gamma J eta
        (defaultLatentLaw n M rho kappa gamma J hn hJ hM hrho hkappa hgamma) := by
    refine ⟨fun _ => zeroLatent false, ?_, ?_, ?_⟩
    · intro k; norm_num [zeroLatent, latentPropensity]
    · intro k; norm_num [zeroLatent, latentScore]
    · exact Classical.choose_spec (latentLaw_exists n M rho kappa gamma J
        (fun _ => zeroLatent false) hn hJ hM hrho hkappa hgamma
        (by intro k; simp [zeroLatent, latentIntensity])
        (by intro k; simp [zeroLatent, latentPropensity, Set.mem_Icc]; norm_num)
        (by intro k; simp [zeroLatent, latentScore, Set.mem_Icc]))
  unfold latentToLaw
  split_ifs with hq he hu
  · exact ⟨theta, he, hu, Classical.choose_spec
      (latentLaw_exists n M rho kappa gamma J theta hn hJ hM hrho
        hkappa hgamma hq he hu)⟩
  all_goals exact hfallback

/-- Equation (62) bounds every signed-score cell effect by one quarter of the
supplied radius, including the reservoir cell. -/
-- @node: latentLawSpec_effect_bound
lemma latentLawSpec_effect_bound {n J : ℕ} {rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell} {P : Law n}
    (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1)
    (hs : LatentLawSpec n 1 rho kappa gamma J theta P) (k : Fin n) :
    |DiscreteAteHeterogeneityFrontier.cellEffect P k| ≤ rho / 4 := by
  simpa [one_mul] using
    (latentLawSpec_effect_bound_general (M := 1) (kappa := kappa)
      (gamma := gamma) (by norm_num) hrho hgamma hu hs k)

/-- The normalized target shares the cell-effect envelope, as in (75)--(76). -/
-- @node: latentLawSpec_target_bound
lemma latentLawSpec_target_bound {n J : ℕ} {rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell} {P : Law n}
    (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1)
    (hs : LatentLawSpec n 1 rho kappa gamma J theta P) :
    |ateTarget P| ≤ rho / 4 := by
  unfold ateTarget DiscreteAteHeterogeneityFrontier.rawAteFormula
  calc
    |∑ k : Fin n, P.cellMass k * DiscreteAteHeterogeneityFrontier.cellEffect P k| ≤
        ∑ k : Fin n, |P.cellMass k * DiscreteAteHeterogeneityFrontier.cellEffect P k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, P.cellMass k * (rho / 4) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (P.cellMass_range k).1]
      exact mul_le_mul_of_nonneg_left
        (latentLawSpec_effect_bound hrho hgamma hu hs k) (P.cellMass_range k).1
    _ = rho / 4 := by
      rw [← Finset.sum_mul, DiscreteAteHeterogeneityFrontier.sum_cellMass_eq_one,
        one_mul]

/-- Binary support supplies integrability and the variance envelope directly;
no outcome-moment premise is added to the converse construction. -/
-- @node: latentLawSpec_varianceEnvelope
lemma latentLawSpec_varianceEnvelope {n J : ℕ} {rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell} {P : Law n}
    (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1)
    (hs : LatentLawSpec n 1 rho kappa gamma J theta P) : VarianceEnvelope 1 P := by
  intro a k hk
  letI := P.outcome_isProbability a k
  have hm : |P.outcomeMean a k| ≤ (1 : ℝ) / 2 := by
    cases a with
    | false => rw [hs.2.2.1 k]; norm_num
    | true =>
      have he := latentLawSpec_effect_bound hrho hgamma hu hs k
      unfold DiscreteAteHeterogeneityFrontier.cellEffect at he
      rw [hs.2.2.1 k, sub_zero] at he
      linarith [hrho.2]
  have hb : ∀ᵐ y ∂P.outcomeLaw a k, y ∈ ({-1 / 2, 1 / 2} : Set ℝ) := by
    rw [ae_iff]
    convert hs.2.2.2.2.1 a k using 1 <;> norm_num
    congr 1
    ext y
    simp
  have hbound : ∀ᵐ y ∂P.outcomeLaw a k,
      (y - P.outcomeMean a k) ^ 2 ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hb] with y hy
    have hm' := abs_le.mp hm
    refine ⟨sq_nonneg _, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> nlinarith [hm'.1, hm'.2]
  have hi : Integrable (fun y => (y - P.outcomeMean a k) ^ 2)
      (P.outcomeLaw a k) := Integrable.of_mem_Icc 0 1 (by fun_prop) hbound
  refine ⟨hi, ?_⟩
  have hle := integral_mono_ae hi (integrable_const (1 : ℝ))
    (hbound.mono (fun y hy => hy.2))
  simpa using hle

/-- The supportwise envelope verification (76) places each legal selected law in
the full radius class and records its centered binary support. -/
-- @node: latentLawSpec_class_embedding
lemma latentLawSpec_class_embedding {n J : ℕ} {rho kappa gamma : ℝ}
    {theta : Fin (n - 1) → LatentCell} {P : Law n}
    (hn : 3 ≤ n) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (he : ∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1)
    (hs : LatentLawSpec n 1 rho kappa gamma J theta P) :
    ∃ Q : KnownRadiusClass n 1 rho, Q.law = P ∧ CenteredBinary P := by
  classical
  refine ⟨{ law := P
            n_ge_three := hn
            M_ge_one := by norm_num
            consistency := hs.2.2.2.2.2.2.1
            exchangeability := hs.2.2.2.2.2.2.2
            overlap := ?_
            mean_envelope := ?_
            variance_envelope := latentLawSpec_varianceEnvelope hrho hgamma hu hs
            radius := ?_ }, rfl, ?_⟩
  · intro k hk
    rw [hs.2.1 k]
    split_ifs with h
    · have hb := he ⟨k.val, h⟩
      constructor
      · exact hb.1
      · linarith [hb.2]
    · norm_num
  · intro a k hk
    cases a with
    | false => rw [hs.2.2.1 k]; norm_num
    | true =>
      have hb := latentLawSpec_effect_bound hrho hgamma hu hs k
      unfold DiscreteAteHeterogeneityFrontier.cellEffect at hb
      rw [hs.2.2.1 k, sub_zero] at hb
      linarith [hrho.2]
  · refine ⟨hrho, ?_⟩
    intro k hk
    change |DiscreteAteHeterogeneityFrontier.cellEffect P k - ateTarget P| ≤ rho * 1
    calc
      _ ≤ |DiscreteAteHeterogeneityFrontier.cellEffect P k| + |ateTarget P| :=
        abs_sub _ _
      _ ≤ rho / 4 + rho / 4 := add_le_add
        (latentLawSpec_effect_bound hrho hgamma hu hs k)
        (latentLawSpec_target_bound hrho hgamma hu hs)
      _ ≤ rho * 1 := by linarith [hrho.1]
  · constructor
    · convert hs.2.2.2.2.2.1 using 1 <;> norm_num
    · intro a k hk
      convert hs.2.2.2.2.1 a k using 1 <;> norm_num

/-- The total construction, including its fallback, always has an inverse-centered
representative in the binary anchor class. -/
-- @node: latentToLaw_anchor_embedding
lemma latentToLaw_anchor_embedding (n : ℕ) (rho kappa gamma : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell) (hn : 3 ≤ n) (hJ : 0 < J)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) (hkappa : 0 ≤ kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    ∃ P : ZengAnchorClass n rho,
      (centerLaw P).fullLaw =
        (latentToLaw n 1 rho kappa gamma J theta (by omega) hJ (by norm_num)
          hrho hkappa hgamma).fullLaw := by
  obtain ⟨eta, he, hu, hs⟩ := latentToLaw_legal_spec n 1 rho kappa gamma J theta
    (by omega) hJ (by norm_num) hrho hkappa hgamma
  obtain ⟨Q, hQ, hb⟩ := latentLawSpec_class_embedding hn hrho hgamma he hu hs
  obtain ⟨P, hP⟩ := centerLaw_inverse_embedding Q (hQ.symm ▸ hb)
  exact ⟨P, hP.trans (congrArg (fun R : Law n => R.fullLaw) hQ)⟩

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
