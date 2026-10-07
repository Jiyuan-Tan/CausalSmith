module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Finite samples of latent failure and censor times, their observable counting
processes, and pathwise integrals against the censor compensator. Times live in
`ℝ`. The convention at a simultaneous event assigns the event to failure;
an absolutely continuous censor law has zero probability of such ties under
independent failure and censor times.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- [A finite sample](goal) of [n subjects](hyp:n) records one real failure time and one real
censor time for each subject. -/
abbrev Sample (n : ℕ) := Fin n → ℝ × ℝ

/-- [The sample law](goal) of [n subjects](hyp:n) makes the subjects independent, each with a
failure time drawn from [the failure-time law](hyp:failureLaw) and an independent censor time
drawn from [the censor-time law](hyp:censorLaw). -/
noncomputable def sampleLaw (n : ℕ) (failureLaw censorLaw : Measure ℝ) :
    Measure (Sample n) := Measure.pi (fun _ : Fin n => failureLaw.prod censorLaw)

/-- [A law on event times](hyp:law) is [a nonnegative time law](goal) when it is a probability
measure that puts all its mass on nonnegative times. -/
def NonnegativeTimeLaw (law : Measure ℝ) : Prop :=
  law Set.univ = 1 ∧ law (Set.Ici 0) = 1

/-- [The observed censor-event count](goal) of [subject i](hyp:i) by [time u](hyp:u) in
[a sample](hyp:x) is one exactly when that subject's censoring occurs by u and strictly before
its failure, and zero otherwise. -/
noncomputable def censorCount {n : ℕ} (i : Fin n) (u : ℝ) (x : Sample n) : ℝ :=
  if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then 1 else 0

/-- [The observed failure-event count](goal) of [subject i](hyp:i) by [time u](hyp:u) in
[a sample](hyp:x) is one exactly when that subject's failure occurs by u and no later than its
censoring, and zero otherwise. -/
noncomputable def failureCount {n : ℕ} (i : Fin n) (u : ℝ) (x : Sample n) : ℝ :=
  if (x i).1 ≤ u ∧ (x i).1 ≤ (x i).2 then 1 else 0

/-- [The left-continuous at-risk indicator](goal) of [subject i](hyp:i) at [time s](hyp:s) in
[a sample](hyp:x) is one when s is nonnegative and the subject has had neither failure nor
censoring strictly before s, and zero otherwise. -/
noncomputable def riskIndicator {n : ℕ} (i : Fin n) (s : ℝ) (x : Sample n) : ℝ :=
  if 0 ≤ s ∧ s ≤ (x i).1 ∧ s ≤ (x i).2 then 1 else 0

/-- [The risk-set size](goal) at [time s](hyp:s) in [a sample](hyp:x) is the number of subjects
at risk at s: zero when s is negative, and otherwise the number of subjects with neither failure
nor censoring strictly before s. -/
noncomputable def riskSet {n : ℕ} (s : ℝ) (x : Sample n) : ℕ :=
  ∑ i : Fin n, if 0 ≤ s ∧ s ≤ (x i).1 ∧ s ≤ (x i).2 then 1 else 0

/-- [A time-indexed process on samples](hyp:H) is [left predictable](goal) when its value at
each time is the same for any two samples whose observed censor and failure counts agree for
every subject at all strictly earlier times.

Joint measurability is kept separate from this nonanticipation condition. -/
def LeftPredictable {n : ℕ} (H : ℝ → Sample n → ℝ) : Prop :=
  ∀ s x y, (∀ (i : Fin n) t, t < s →
    censorCount i t x = censorCount i t y ∧
    failureCount i t x = failureCount i t y) → H s x = H s y

/-- [A censor-time law](hyp:censorLaw) [has the given censor hazard](goal) when it is a
probability law on nonnegative times and [the hazard function](hyp:hazard) is measurable,
nonnegative, integrable on every interval from 0 to u, and the law has Lebesgue density equal at
each time s to the hazard at s times the probability of censoring at or after s.

Local integrability makes the finite-horizon compensator well defined. Because the density
equation holds on the whole real line while the law sits on nonnegative times, the condition
forces the hazard to vanish at almost every negative time. -/
def HasCensorHazard (censorLaw : Measure ℝ) (hazard : ℝ → ℝ) : Prop :=
  NonnegativeTimeLaw censorLaw ∧ Measurable hazard ∧ (∀ s, 0 ≤ hazard s) ∧
  (∀ u, Integrable hazard (volume.restrict (Set.Icc 0 u))) ∧
  censorLaw = (volume : Measure ℝ).withDensity
    (fun s => ENNReal.ofReal (hazard s * (censorLaw (Set.Ici s)).toReal))

/-- [The compensated censor count](goal) of [subject i](hyp:i) by [time u](hyp:u) in
[a sample](hyp:x) is the observed censor-event count by u minus the integral over times from 0
to u of [the censor hazard](hyp:hazard) times the subject's at-risk indicator. -/
noncomputable def compensatedCensor {n : ℕ} (hazard : ℝ → ℝ)
    (i : Fin n) (u : ℝ) (x : Sample n) : ℝ :=
  censorCount i u x - ∫ s in Set.Icc 0 u, hazard s * riskIndicator i s x ∂volume

/-- [The pathwise integral](goal) of [a process](hyp:H) against the compensated censor count of
[subject i](hyp:i) up to [time u](hyp:u) in [a sample](hyp:x) is the process's value at the
subject's censor time when an observed censor event occurs by u (zero otherwise), minus the
integral over times from 0 to u of the process times [the censor hazard](hyp:hazard) times the
subject's at-risk indicator. -/
noncomputable def subjectIntegral {n : ℕ} (hazard : ℝ → ℝ)
    (H : ℝ → Sample n → ℝ) (i : Fin n) (u : ℝ)
    (x : Sample n) : ℝ :=
  (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) -
    ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume

/-- [The pathwise integral](goal) of [a process](hyp:H) against the sum of all subjects'
compensated censor counts, with [censor hazard](hyp:hazard), up to [time u](hyp:u) in
[a sample](hyp:x), is the sum over subjects of the subjectwise integrals. -/
noncomputable def aggregateIntegral {n : ℕ} (hazard : ℝ → ℝ)
    (H : ℝ → Sample n → ℝ) (u : ℝ) (x : Sample n) : ℝ :=
  ∑ i : Fin n, subjectIntegral hazard H i u x

/-- [The zero-safe inverse risk-set size](goal), the Nelson–Aalen integrand, at [time s](hyp:s)
in [a sample](hyp:x) is zero when the risk set is empty and the reciprocal of the risk-set size
otherwise. -/
noncomputable def inverseRisk {n : ℕ} (s : ℝ) (x : Sample n) : ℝ :=
  if riskSet s x = 0 then 0 else 1 / (riskSet s x : ℝ)

/-- [The compensated Nelson–Aalen estimation error](goal) up to [time u](hyp:u) in
[a sample](hyp:x) is the integral of the zero-safe inverse risk-set size against the sum of all
compensated censor counts with [censor hazard](hyp:hazard). -/
noncomputable def nelsonAalenError {n : ℕ} (hazard : ℝ → ℝ)
    (u : ℝ) (x : Sample n) : ℝ :=
  aggregateIntegral hazard inverseRisk u x

end Causalean.Stat.RecurrentEvent.CountingProcess
