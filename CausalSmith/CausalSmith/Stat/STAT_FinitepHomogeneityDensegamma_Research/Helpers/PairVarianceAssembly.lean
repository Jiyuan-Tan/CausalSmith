module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairCanonicalMoments

/-! Exact Hoeffding variance assembly. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma
variable {Ω : Type*} [MeasurableSpace Ω]

/-- For [a measurable kernel](hyp:hg) that is [symmetric](hyp:hsym), [square
integrable](hyp:hL2), and based on [at least two observations](hyp:hs), [the kernel energy
and ordered-pair variance have the stated Hoeffding decompositions](goal). -/
-- @node: hoeffding_pair_variance
lemma hoeffding_pair_variance (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → Ω → ℝ)
    (hg : Measurable (fun z : Ω × Ω => g z.1 z.2)) (hsym : ∀ x y, g x y=g y x)
    (hL2 : MemLp (fun z : Ω × Ω => g z.1 z.2) 2 (P.prod P)) (s : ℕ) (hs : 2 ≤ s) :
    (∫ z : Ω × Ω, g z.1 z.2^2 ∂P.prod P) = pairMean P g^2+
      2*(∫ x, singletonProjection P g x^2 ∂P)+(∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P) ∧
    variance (orderedPairAverage s g) (Measure.pi fun _ : Fin s => P) =
      4/(s:ℝ)*variance (singletonProjection P g) P+
      2/((s:ℝ)*((s:ℝ)-1))*(∫ z : Ω × Ω, canonicalProjection P g z.1 z.2^2 ∂P.prod P) := by
  refine ⟨hoeffding_pair_energy P g hg hsym hL2, ?_⟩
  have hp := singletonProjection_memLp P g hg hL2
  have hpm : Measurable (singletonProjection P g) := by
    have hm : Measurable (fun x => ∫ y, g x y ∂P) :=
      hg.stronglyMeasurable.integral_prod_right.measurable
    exact hm.sub measurable_const
  have hcoord (i : Fin s) : MemLp (fun data : Fin s → Ω =>
      singletonProjection P g (data i)) 2 (Measure.pi fun _ : Fin s => P) :=
    hp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin s => P) i)
  have hlin : MemLp (fun data : Fin s → Ω => 2/(s : ℝ)*
      ∑ i : Fin s, singletonProjection P g (data i)) 2 (Measure.pi fun _ : Fin s => P) :=
    (memLp_finsetSum _ (fun i _ => hcoord i)).const_mul _
  have hcan := orderedPairAverage_memLp P _ (canonicalProjection_memLp P g hg hL2) s
  have he : orderedPairAverage s g = fun data : Fin s → Ω =>
      (2/(s : ℝ)*(∑ i : Fin s, singletonProjection P g (data i))+
        orderedPairAverage s (canonicalProjection P g) data)+pairMean P g := by
    funext data
    rw [orderedPairAverage_hoeffding_decomposition P g s hs data]
    ring
  have hcov : covariance (fun data : Fin s → Ω => 2/(s : ℝ)*
      ∑ i : Fin s, singletonProjection P g (data i))
      (orderedPairAverage s (canonicalProjection P g)) (Measure.pi fun _ : Fin s => P) = 0 := by
    rw [covariance_const_mul_left,
      canonicalPairAverage_singleton_covariance P g hg hsym hL2 _ hp hpm, mul_zero]
  have hv := variance_add_const (hlin.add hcan).aestronglyMeasurable (pairMean P g)
  have hv2 := variance_add hlin hcan
  simp only [Pi.add_apply] at hv hv2
  rw [he, hv, hv2, hcov, pair_linear_variance P g hg hL2 s (by omega),
    canonicalPairAverage_variance P g hg hsym hL2 s hs]
  ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
