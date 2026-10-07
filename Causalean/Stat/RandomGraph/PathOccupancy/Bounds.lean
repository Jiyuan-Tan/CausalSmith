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

/-- With [n at least two](hyp:hn), [M at least two and even](hyp:hM,heven), [K at least 16
M](hyp:hKM), [iid uniform fine-cell draws and independent Bernoulli marks](hyp:h), and [any
measurable local subrelation](hyp:R,hR,hlocal), [the expected two-mark component weight is at most ε² K times the
order-eleven finite occupancy series](goal). -/
theorem single_component_occupancy {n M K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (hn : 2 ≤ n) (hM : 2 ≤ M)
    (heven : 2 ∣ M) (hKM : 16 * M ≤ K)
    (R : Ω → Fin n → Fin n → Prop)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j})
    (hlocal : ∀ ω, Admissible M (fun i => X i ω) (R ω)) :
    (∫ ω, singleScore (R ω) (fun i => B i ω) ∂μ) ≤
      ε ^ 2 * K * occupancySeries 11 n K := by
  have hK : 0 < K := by omega
  calc
    _ ≤ ε ^ 2 * K * ∑ m ∈ Finset.Icc 2 n,
        (n.choose m : ℝ) * (m : ℝ) ^ 10 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m :=
      single_expectation_labelled_le h M hK R hR hlocal
    _ ≤ ε ^ 2 * K * occupancySeries 11 n K :=
      mul_le_mul_of_nonneg_left (finite_labelled_weight_majorant 10 n K hn hK)
        (by positivity)

/-- Place [n ≥ 2 sample points](hyp:hn) in K fine cells on a path, grouped into M consecutive
coarse cells, where [M ≥ 2](hyp:hM), [M is even](hyp:heven), [M divides K](hyp:hdiv)
and [K ≥ 16 M](hyp:hKM). Suppose [the points'
cells are independent and uniform over the K fine cells, each point is marked with probability
ε ∈ [0, 1] independently of the other points, and the marks are independent of the
cells](hyp:h). Let [a random relation on the points](hyp:R) be such that [each of its edge events
is measurable](hyp:hR) and [in every outcome each edge joins two points whose fine cells are equal
or neighbouring and lie in the same coarse cell](hyp:hlocal). Then [the expected paired score —
half the sum, over ordered pairs of distinct connected components C and D of the relation that
each have at least two points, each contain at least one marked point, and together lie in one
consecutive pair of coarse cells, of |C|⁴ 8^|C| · |D|⁴ 8^|D| — is at most 2 ε² K² / M times the
square of the finite occupancy series Σ_{m=2}^{n} m⁶ (8 e n / K)^m](goal).
-/
theorem paired_component_occupancy {n M K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (hn : 2 ≤ n) (hM : 2 ≤ M)
    (heven : 2 ∣ M) (hdiv : M ∣ K) (hKM : 16 * M ≤ K)
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
      paired_expectation_labelled_le h M hMp hK heven hdiv R hR hlocal
    _ ≤ 2 * ε ^ 2 * (K : ℝ) ^ 2 / M * (occupancySeries 6 n K) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ hsum_nonneg hmajorant 2

end Causalean.Stat.RandomGraph.PathOccupancy
