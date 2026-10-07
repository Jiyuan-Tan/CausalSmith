module
public import Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump.CrossSubject

/-!
# Full-sample finite recurrent-event isometry

The subject conditional-increment premise gives predictable compensation and
subject isometry. Cross-prefix compensation gives distinct-subject
orthogonality under the iid path law, even for a common integrand depending on
all subject histories. Finite-sum algebra then gives the aggregate isometry.

This interface covers payoffs depending on the whole sample, for which
independence of the subject integrals themselves is not valid; the
coordinate-only `copy*` definitions cover only integrands of a subject's own path.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Compensated integrals from distinct subjects are orthogonal in expectation
for a bounded predictable payoff depending on every subject history. -/
theorem SampleModel.distinct_subject_integrals_orthogonal (S : SampleModel n Ω μ)
    [IsProbabilityMeasure μ]
    (H : ℝ → (Fin n → Ω) → ℝ) (hPredictable : S.LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × (Fin n → Ω) => H p.1 p.2))
    (hbound : ∃ C : ℝ, ∀ t x, |H t x| ≤ C)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ x, S.subjectIntegral H i x * S.subjectIntegral H j x
      ∂finiteSampleLaw n μ) = 0 := by
  -- Component predictability already implies ordinary joint measurability.
  have _ := hMeasurable
  classical
  let E : Fin n → Fin n → (Fin n → Ω) → ℝ := fun k l =>
    (S.process k).jumpIntegral (S.crossPayoff H l) (S.process k).horizon
  let C : Fin n → Fin n → (Fin n → Ω) → ℝ := fun k l =>
    (S.process k).energyIntegral (S.crossPayoff H l) (S.process k).horizon
  have hPair (k l : Fin n) :
      Integrable (E k l) (finiteSampleLaw n μ) ∧
      Integrable (C k l) (finiteSampleLaw n μ) ∧
      (∫ x, E k l x ∂finiteSampleLaw n μ) =
        ∫ x, C k l x ∂finiteSampleLaw n μ := by
    have hp := S.crossPayoff_predictable H hPredictable k l
    have hm := (S.process k).predictable_joint_measurable _ hp
    obtain ⟨hjAbs, heAbs⟩ := S.crossPayoff_integrable H hPredictable hbound k l
    have hj : Integrable (E k l) (finiteSampleLaw n μ) := by
      apply hjAbs.mono'
        ((S.process k).measurable_jumpIntegral _ hm).aestronglyMeasurable
      filter_upwards [] with x
      simp only [Model.jumpIntegral, Real.norm_eq_abs]
      exact Finset.abs_sum_le_sum_abs _ _
    have he : Integrable (C k l) (finiteSampleLaw n μ) := by
      apply heAbs.mono'
        ((S.process k).measurable_energyIntegral _ hm).aestronglyMeasurable
      filter_upwards [] with x
      change ‖∫ t in Set.Ioc 0 (S.process k).horizon,
        S.crossPayoff H l t x *
          ((S.process k).atRisk t x * (S.process k).intensity t x)‖ ≤ _
      calc
        _ ≤ ∫ t in Set.Ioc 0 (S.process k).horizon,
            ‖S.crossPayoff H l t x *
              ((S.process k).atRisk t x * (S.process k).intensity t x)‖ :=
          norm_integral_le_integral_norm _
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
            (mul_nonneg ((S.process k).atRisk_nonneg t x)
              ((S.process k).intensity_nonneg t x))]
    exact ⟨hj, he, (S.process k).predictable_compensator _ hp hjAbs⟩
  have hi := hPair i j
  have hj := hPair j i
  have hPath : ∀ᵐ x ∂finiteSampleLaw n μ,
      S.subjectIntegral H i x * S.subjectIntegral H j x =
        E i j x + E j i x - C i j x - C j i x := by
    filter_upwards [S.no_common_jumps i j hij] with x hx
    exact S.subject_product_pathwise H hPredictable hbound i j x hx
  calc
    (∫ x, S.subjectIntegral H i x * S.subjectIntegral H j x
        ∂finiteSampleLaw n μ) =
        ∫ x, E i j x + E j i x - C i j x - C j i x ∂finiteSampleLaw n μ :=
      integral_congr_ae hPath
    _ = 0 := by
      change (∫ x, (E i j + E j i - C i j - C j i) x
        ∂finiteSampleLaw n μ) = 0
      rw [integral_sub' ((hi.1.add hj.1).sub hi.2.1) hj.2.1,
        integral_sub' (hi.1.add hj.1) hi.2.1,
        integral_add' hi.1 hj.1, hi.2.2, hj.2.2]
      ring

/-- The aggregate finite-multiple-jump integral has second moment equal to
its expected predictable quadratic energy. The integrand may use all sample
histories. Quadratic-energy finiteness and Bochner energy integrability are
explicit; the second moment is derived from conditional intensities rather
than supplied as a bracket or isometry premise. [The sample model and
full-sample payoff](hyp:S,H), [left predictability and joint measurability](hyp:hPredictable,hMeasurable),
[boundedness](hyp:hbound), [quadratic-energy finiteness](hyp:hQuadratic), and
[Bochner integrability of the energy](hyp:hEnergy) give [the aggregate
second-moment isometry and integrability](goal). -/
theorem SampleModel.aggregate_integral_isometry (S : SampleModel n Ω μ)
    [IsProbabilityMeasure μ]
    (H : ℝ → (Fin n → Ω) → ℝ) (hPredictable : S.LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × (Fin n → Ω) => H p.1 p.2))
    (hbound : ∃ C : ℝ, ∀ t x, |H t x| ≤ C)
    (hQuadratic : S.QuadraticEnergyFinite H)
    (hEnergy : Integrable (S.predictableEnergy H) (finiteSampleLaw n μ)) :
    Integrable (fun x => (S.aggregateIntegral H x) ^ 2) (finiteSampleLaw n μ) ∧
    (∫ x, (S.aggregateIntegral H x) ^ 2 ∂finiteSampleLaw n μ) =
      ∫ x, S.predictableEnergy H x ∂finiteSampleLaw n μ := by
  -- Bounded payoffs and rates supply the stronger component integrability
  -- facts below. Retain the explicit energy hypotheses at the API boundary.
  have _ := hQuadratic
  have _ := hEnergy
  classical
  let J : Fin n → (Fin n → Ω) → ℝ := S.subjectIntegral H
  let Q : Fin n → (Fin n → Ω) → ℝ := S.subjectEnergy H
  have hLp (i : Fin n) : MemLp (J i) 2 (finiteSampleLaw n μ) :=
    (memLp_two_iff_integrable_sq
      ((S.process i).measurable_stochasticIntegral H
        (S.process_predictable H hPredictable i)).aestronglyMeasurable).2
      (S.subject_square_integrable H hPredictable hbound i)
  have hProd (i j : Fin n) :
      Integrable (fun x => J i x * J j x) (finiteSampleLaw n μ) :=
    (hLp i).integrable_mul (hLp j)
  have hQ (i : Fin n) : Integrable (Q i) (finiteSampleLaw n μ) :=
    (S.process i).integrable_quadratic_energy H
      (S.process_predictable H hPredictable i) hbound
  have hIso (i : Fin n) :
      (∫ x, (J i x) ^ 2 ∂finiteSampleLaw n μ) =
        ∫ x, Q i x ∂finiteSampleLaw n μ :=
    S.subject_integral_isometry H hPredictable hbound i
  constructor
  · exact (memLp_finsetSum Finset.univ (fun i _ => hLp i)).integrable_sq
  · calc
      (∫ x, (S.aggregateIntegral H x) ^ 2 ∂finiteSampleLaw n μ) =
          ∫ x, ∑ i : Fin n, ∑ j : Fin n, J i x * J j x
            ∂finiteSampleLaw n μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [SampleModel.aggregateIntegral, J, pow_two, Finset.sum_mul_sum]
      _ = ∑ i : Fin n, ∑ j : Fin n,
          ∫ x, J i x * J j x ∂finiteSampleLaw n μ := by
        rw [integral_finsetSum Finset.univ (fun i _ =>
          integrable_finsetSum Finset.univ (fun j _ => hProd i j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum Finset.univ (fun j _ => hProd i j)]
      _ = ∑ i : Fin n, ∫ x, Q i x ∂finiteSampleLaw n μ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · simpa only [pow_two] using hIso i
        · intro j _ hji
          exact S.distinct_subject_integrals_orthogonal H hPredictable hMeasurable
            hbound i j (Ne.symm hji)
        · simp
      _ = ∫ x, S.predictableEnergy H x ∂finiteSampleLaw n μ := by
        exact (integral_finsetSum Finset.univ (fun i _ => hQ i)).symm

end Causalean.Stat.RecurrentEvent.CountingProcess.FiniteJump
