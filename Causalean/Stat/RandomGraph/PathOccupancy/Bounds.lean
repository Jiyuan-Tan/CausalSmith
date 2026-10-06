module
public import Causalean.Stat.RandomGraph.PathOccupancy.Arithmetic
public import Causalean.Stat.RandomGraph.PathOccupancy.PairedExpectation
public import Causalean.Stat.RandomGraph.PathOccupancy.SingleExpectation

/-!
# Fixed-sample marked connected-component occupancy bounds

The main results apply to every measurable random local subrelation, with exact
iid uniform fine-cell draws and independent Bernoulli marks. The relation need
not include all eligible edges and may depend on the marks or extra randomness.

The proof chain exposes fixed-subset event bounds, then labelled-subset union
bounds, then elementary finite exponential majorants. Both headline bounds keep
the requested finite sums; the paired bound retains the essential size-two cutoff.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.RandomGraph.PathOccupancy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- With [n at least two](hyp:hn), [M at least two, even, and dividing K](hyp:hM,heven,hdiv), [K at
least 16 M](hyp:hKM), [density n / K at most 2 to the power −40](hyp:hdensity), [iid uniform
fine-cell draws and independent Bernoulli marks](hyp:h), and [any measurable local
subrelation](hyp:R,hR,hlocal), [the expected two-mark component weight is at most ε² K times the
order-eleven finite occupancy series](goal). -/
theorem single_component_occupancy {n M K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (hn : 2 ≤ n) (hM : 2 ≤ M)
    (heven : 2 ∣ M) (hdiv : M ∣ K) (hKM : 16 * M ≤ K)
    (hdensity : (n : ℝ) / K ≤ (2 : ℝ) ^ (-40 : ℤ))
    (R : Ω → Fin n → Fin n → Prop)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j})
    (hlocal : ∀ ω, Admissible M (fun i => X i ω) (R ω)) :
    (∫ ω, singleScore (R ω) (fun i => B i ω) ∂μ) ≤
      ε ^ 2 * K * occupancySeries 11 n K := by
  have hK : 0 < K := by omega
  calc
    _ ≤ ε ^ 2 * K * ∑ m ∈ Finset.Icc 2 n,
        (n.choose m : ℝ) * (m : ℝ) ^ 10 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m :=
      single_expectation_labelled_le h M hK hn R hR hlocal
    _ ≤ ε ^ 2 * K * occupancySeries 11 n K :=
      mul_le_mul_of_nonneg_left (finite_labelled_weight_majorant 10 n K hn hK)
        (by positivity)

/-- With [n at least two, even M at least two dividing K, K at least 16M,
and small density](hyp:hn,hM,heven,hdiv,hKM,hdensity), [iid uniform cells and
independent Bernoulli marks](hyp:h), and [any measurable local subrelation](hyp:R,hR,hlocal),
[the expected unordered score of distinct components of size at least two,
marked in each and sharing a coarse pair, obeys the requested squared
order-six finite-series bound](goal).
-/
theorem paired_component_occupancy {n M K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (hn : 2 ≤ n) (hM : 2 ≤ M)
    (heven : 2 ∣ M) (hdiv : M ∣ K) (hKM : 16 * M ≤ K)
    (hdensity : (n : ℝ) / K ≤ (2 : ℝ) ^ (-40 : ℤ))
    (R : Ω → Fin n → Fin n → Prop)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j})
    (hlocal : ∀ ω, Admissible M (fun i => X i ω) (R ω)) :
    (∫ ω, pairedScore M (R ω) (fun i => X i ω) (fun i => B i ω) ∂μ) ≤
      2 * ε ^ 2 * (K : ℝ) ^ 2 / M * (occupancySeries 6 n K) ^ 2 := by
  have hK : 0 < K := by omega
  have hMp : 0 < M := by omega
  have hsum_nonneg : 0 ≤ (∑ m ∈ Finset.Icc 2 n,
      (n.choose m : ℝ) * (m : ℝ) ^ 5 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m) := by
    exact Finset.sum_nonneg (fun m _ => by positivity)
  have hmajorant := finite_labelled_weight_majorant 5 n K hn hK
  calc
    _ ≤ 2 * ε ^ 2 * (K : ℝ) ^ 2 / M *
        (∑ m ∈ Finset.Icc 2 n,
          (n.choose m : ℝ) * (m : ℝ) ^ 5 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m) ^ 2 :=
      paired_expectation_labelled_le h M hMp hK heven hdiv hn R hR hlocal
    _ ≤ 2 * ε ^ 2 * (K : ℝ) ^ 2 / M * (occupancySeries 6 n K) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ hsum_nonneg hmajorant 2

end Causalean.Stat.RandomGraph.PathOccupancy
