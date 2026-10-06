module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.PilotEvents

/-! Cellwise expectation and scalar bias of the capped Jackson statistic. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory

/-- The ideal, uncapped Poisson pilot and evaluation counts. -/
noncomputable def idealCountLaw {n d : ℕ} (P : DiscreteLaw d) :
    Measure ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) :=
  let onePool : Measure (Fin d → Cell → ℕ) :=
    Measure.pi (fun j : Fin d =>
      Measure.pi (fun zeta : Cell =>
        ProbabilityTheory.poissonMeasure
          ⟨max 0 (((n : ℝ) / 8) * cellVector P j zeta),
            le_max_left 0 _⟩))
  onePool.prod onePool

/-- Uncapped cellwise expectation in the ideal Poisson count experiment. -/
noncomputable def expectedUncappedJacksonCell {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (j : Fin d) : ℝ :=
  ∫ counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ),
    jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
      (counts.1 j) (counts.2 j) ∂idealCountLaw (n := n) P

/-- Scalar bias before the finite-sample Poisson cap transfer. -/
noncomputable def uncappedJacksonCellBias {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (j : Fin d) : ℝ :=
  |expectedUncappedJacksonCell (n := n) epsilon lambda P j -
    thresholdFunReal epsilon lambda (cellVector P j)|

/-- Mean of a single capped cell statistic under data and auxiliary randomization. -/
noncomputable def expectedJacksonCell {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (j : Fin d) : ℝ :=
  ∫ sample : Fin n → Obs d,
    auxiliaryAverage n (fun M perm marks =>
      jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
        (fun zeta => markedCellCount sample perm M marks false j zeta)
        (fun zeta => markedCellCount sample perm M marks true j zeta))
      ∂productLaw P n

/-- Absolute cellwise scalar bias of the same polynomial used by the estimator. -/
noncomputable def jacksonCellBias {n d : ℕ} (epsilon lambda : ℝ)
    (P : DiscreteLaw d) (j : Fin d) : ℝ :=
  |expectedJacksonCell (n := n) epsilon lambda P j -
    thresholdFunReal epsilon lambda (cellVector P j)|

end CausalSmith.Stat.DiscreteBudgetvalueCurve
