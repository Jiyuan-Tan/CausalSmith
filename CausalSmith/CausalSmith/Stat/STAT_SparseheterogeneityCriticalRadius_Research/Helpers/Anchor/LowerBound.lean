module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Anchor.PriorSupport

/-! Transport of arbitrary estimators through inverse centering and assembly of
 the binary-class minimax lower bound from the supported converse certificate. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open scoped ENNReal

/-- Inverse translation is measurable on observed records. -/
-- @node: uncenterObs_measurable
@[fun_prop] lemma uncenterObs_measurable (n : ℕ) :
    Measurable (uncenterObs (n := n)) := by
  rw [measurable_comap_iff]
  change Measurable (fun o : SampleObs n => (o.x, o.a, o.y + 1 / 2))
  have ht : Measurable (fun o : SampleObs n => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact ht.fst.prodMk (ht.snd.fst.prodMk (ht.snd.snd.add measurable_const))

/-- Inverse translation commutes with independent sampling. -/
-- @node: uncenterLaw_productLaw
lemma uncenterLaw_productLaw {n : ℕ} {rho : ℝ} (Q : KnownRadiusClass n 1 rho) :
    DiscreteAteHeterogeneityFrontier.productLaw n (uncenterLaw Q) =
      Measure.map (fun sample i => uncenterObs (sample i))
        (DiscreteAteHeterogeneityFrontier.productLaw n Q.law) := by
  have h := Classical.choose_spec (uncenterLaw_exists Q)
  change UncenterLawSpec Q.law (uncenterLaw Q) at h
  unfold DiscreteAteHeterogeneityFrontier.productLaw
  rw [h.1]
  letI : IsProbabilityMeasure (Measure.map (uncenterObs (n := n)) Q.law.observedLaw) :=
    Measure.isProbabilityMeasure_map (uncenterObs_measurable n).aemeasurable
  exact (Measure.pi_map_pi (fun _ => (uncenterObs_measurable n).aemeasurable)).symm

/-- An arbitrary measurable estimator has the same risk after inverse translation. -/
-- @node: uncenterLaw_mse_eq
lemma uncenterLaw_mse_eq {n : ℕ} {rho : ℝ} (Q : KnownRadiusClass n 1 rho)
    (T : (Fin n → SampleObs n) → ℝ) (hT : Measurable T) :
    DiscreteAteHeterogeneityFrontier.mse (uncenterLaw Q) T =
      DiscreteAteHeterogeneityFrontier.mse Q.law
        (fun sample => T (fun i => uncenterObs (sample i))) := by
  unfold DiscreteAteHeterogeneityFrontier.mse
  have ht : DiscreteAteHeterogeneityFrontier.rawAteFormula (uncenterLaw Q) =
      DiscreteAteHeterogeneityFrontier.rawAteFormula Q.law := uncenterLaw_ateTarget Q
  rw [uncenterLaw_productLaw Q, ht]
  have hm : Measurable (fun sample : Fin n → SampleObs n =>
      fun i => uncenterObs (sample i)) := by fun_prop
  rw [integral_map hm.aemeasurable (by fun_prop)]

/-- Centering bounds the target, hence every clipped estimator's binary-class risk. -/
-- @node: anchorClass_mse_bound
lemma anchorClass_mse_bound {n : ℕ} {rho : ℝ} (P : ZengAnchorClass n rho)
    (est : DiscreteAteHeterogeneityFrontier.Estimator n n 1) :
    DiscreteAteHeterogeneityFrontier.mse P.law est.1 ≤ 4 := by
  obtain ⟨Q, hQ⟩ := centerLaw_class_embedding P
  have ht : |ateTarget P.law| ≤ 1 := by
    rw [← centerLaw_ateTarget P, ← hQ]
    exact knownRadiusClass_ate_bound Q
  have hb (x : Fin n → SampleObs n) : (est.1 x - ateTarget P.law) ^ 2 ≤ 4 := by
    have he : |est.1 x| ≤ 1 := abs_le.mpr (est.2.2 x)
    have hd := (abs_sub (est.1 x) (ateTarget P.law)).trans (add_le_add he ht)
    have hs : (est.1 x - ateTarget P.law) ^ 2 ≤ (2 : ℝ) ^ 2 :=
      sq_le_sq.mpr (by norm_num at hd ⊢; exact hd)
    norm_num at hs ⊢
    exact hs
  have hi : Integrable (fun x => (est.1 x - ateTarget P.law) ^ 2)
      (DiscreteAteHeterogeneityFrontier.productLaw n P.law) := by
    have hm : Measurable (fun x => (est.1 x - ateTarget P.law) ^ 2) :=
      (est.2.1.sub measurable_const).pow_const 2
    apply Integrable.of_bound (C := 4) hm.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb x
  calc
    _ ≤ ∫ _, (4 : ℝ) ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law :=
      integral_mono hi (integrable_const _) hb
    _ = 4 := by simp

/-- The binary-supported converse laws transport the lower bound to the anchor
class for every estimator, as in roadmap (6)--(7). The statistical certificate
itself remains unfinished in `known_radius_converse_laws`. -/
-- @node: anchor_minimax_lower_bound
lemma anchor_minimax_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n rho, 3 ≤ n → 0 ≤ rho → rho ≤ 2 →
      c * rate n rho ≤ anchorMinimaxRisk n rho := by
  obtain ⟨c, hc, hcertificate⟩ := known_radius_converse_laws
  refine ⟨c, hc, ?_⟩
  intro n rho hn hr0 hr2
  letI : Nonempty (DiscreteAteHeterogeneityFrontier.Estimator n n 1) :=
    ⟨knownRadiusEstimatorAsEstimator n 1 rho (by norm_num)⟩
  apply Causalean.Stat.le_minimaxValue
    (risk := fun (est : DiscreteAteHeterogeneityFrontier.Estimator n n 1)
      (P : ZengAnchorClass n rho) => DiscreteAteHeterogeneityFrontier.mse P.law est.1)
  intro est
  let shifted : DiscreteAteHeterogeneityFrontier.Estimator n n 1 :=
    ⟨fun sample => est.1 (fun i => uncenterObs (sample i)),
      est.2.1.comp (by fun_prop), fun sample => est.2.2 _⟩
  obtain ⟨Q, hbound, hbinary⟩ :=
    hcertificate n 1 rho hn (by norm_num) hr0 hr2 shifted.1 shifted.2.1
  obtain ⟨P, hP⟩ := uncenterLaw_class_embedding Q (hbinary rfl)
  rw [← knownRadiusClass_ofReal_mse Q shifted] at hbound
  have hl : c * rate n rho ≤ DiscreteAteHeterogeneityFrontier.mse P.law est.1 := by
    rw [hP, uncenterLaw_mse_eq Q est.1 est.2.1]
    have hb := (ENNReal.ofReal_le_ofReal_iff
      (integral_nonneg (fun _ => sq_nonneg _))).mp hbound
    simpa [shifted, DiscreteAteHeterogeneityFrontier.mse] using hb
  have hbdd : BddAbove (Set.range (fun P : ZengAnchorClass n rho =>
      DiscreteAteHeterogeneityFrontier.mse P.law est.1)) := by
    refine ⟨4, ?_⟩
    rintro r ⟨P, rfl⟩
    exact anchorClass_mse_bound P est
  exact hl.trans (le_ciSup hbdd P)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
