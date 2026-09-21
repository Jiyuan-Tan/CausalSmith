module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderRepresentation
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CondIndepIntersection

/-!
# Rank-coordinate conditional-independence transport

This module records the measurable-embedding invariance used to pass between
the decoder's signed CDF ranks and the corresponding latent coordinates.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory Set ProbabilityTheory

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: condIndepGiven_measurableEmbedding_comp
/-- Applying measurable embeddings separately to both variables and the conditioning
variable preserves and reflects conditional independence.  [the stated conclusion](goal) follows. -/
lemma condIndepGiven_measurableEmbedding_comp
    {Ω X Y Z X' Y' Z' : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace Z']
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    {μ : Measure Ω} (UX : Ω → X) (UY : Ω → Y) (UZ : Ω → Z)
    {fX : X → X'} {fY : Y → Y'} {fZ : Z → Z'}
    (eX : MeasurableEmbedding fX) (eY : MeasurableEmbedding fY)
    (eZ : MeasurableEmbedding fZ) :
    CondIndepGiven μ (fX ∘ UX) (fY ∘ UY) (fZ ∘ UZ) ↔
      CondIndepGiven μ UX UY UZ := by
  constructor
  · rintro ⟨hμ, hX, hY, hZ, hCI⟩
    letI := hμ
    have hUX : Measurable UX := by
      convert eX.measurable_invFun.comp hX using 1
      funext ω
      exact (eX.leftInverse_invFun (UX ω)).symm
    have hUY : Measurable UY := by
      convert eY.measurable_invFun.comp hY using 1
      funext ω
      exact (eY.leftInverse_invFun (UY ω)).symm
    have hUZ : Measurable UZ := by
      convert eZ.measurable_invFun.comp hZ using 1
      funext ω
      exact (eZ.leftInverse_invFun (UZ ω)).symm
    refine ⟨hμ, hUX, hUY, hUZ, ?_⟩
    have hraw := hCI.comp eX.measurable_invFun eY.measurable_invFun
    have hs : CondIndepFun (MeasurableSpace.comap (fZ ∘ UZ) inferInstance)
        hZ.comap_le UX UY μ := by
      convert hraw using 1 <;> funext ω
      · exact (eX.leftInverse_invFun (UX ω)).symm
      · exact (eY.leftInverse_invFun (UY ω)).symm
    simpa only [← MeasurableSpace.comap_comp, eZ.comap_eq] using hs
  · rintro ⟨hμ, hX, hY, hZ, hCI⟩
    letI := hμ
    refine ⟨hμ, eX.measurable.comp hX, eY.measurable.comp hY,
      eZ.measurable.comp hZ, ?_⟩
    have hraw := hCI.comp eX.measurable eY.measurable
    simpa only [← MeasurableSpace.comap_comp, eZ.comap_eq] using hraw

-- @node: signedInterventionCDFChart
/-- The signed intervention CDF restricted to the unit interval, with its range proof. -/
def signedInterventionCDFChart
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ) (i : Fin n) :
    Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := fun z =>
  ⟨signedInterventionCDF s θ i z,
    by
      unfold signedInterventionCDF
      have hQ := interventionCDF_mem_Icc θ hpos i z z.2
      split
      · exact hQ
      · constructor <;> linarith [hQ.1, hQ.2]⟩

-- @node: continuous_signedInterventionCDFChart
/-- The signed intervention CDF chart is continuous on the closed unit interval.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma continuous_signedInterventionCDFChart
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ) (i : Fin n) :
    Continuous (signedInterventionCDFChart s θ hpos i) := by
  have hqint : IntegrableOn (θ.q i) (Set.Icc (0 : ℝ) 1) :=
    (hpos.2.2.2.1 i).continuousOn.integrableOn_compact isCompact_Icc
  have hcset := intervalIntegral.continuousOn_primitive hqint
  have hcdf : Continuous (fun z : Set.Icc (0 : ℝ) 1 => interventionCDF θ i z) := by
    have h := hcset.restrict
    convert h using 1
    funext z
    change (∫ u in (0 : ℝ)..(z : ℝ), θ.q i u) =
      ∫ u in Set.Ioc (0 : ℝ) (z : ℝ), θ.q i u
    exact intervalIntegral.integral_of_le z.2.1
  have hsigned : Continuous (fun z : Set.Icc (0 : ℝ) 1 =>
      signedInterventionCDF s θ i z) := by
    unfold signedInterventionCDF
    split
    · exact hcdf
    · fun_prop
  exact hsigned.subtype_mk _

-- @node: signedInterventionCDFChart_measurableEmbedding
/-- The positive-density signed CDF chart is a measurable embedding of the unit interval.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma signedInterventionCDFChart_measurableEmbedding
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    (θ : Mechanism n G) (hpos : PositiveNormalizedSmoothMechanisms G θ) (i : Fin n) :
    MeasurableEmbedding (signedInterventionCDFChart s θ hpos i) := by
  apply (continuous_signedInterventionCDFChart s θ hpos i).measurableEmbedding
  intro a b hab
  apply Subtype.ext
  exact signedInterventionCDF_injOn s θ hpos i a.2 b.2 (congrArg Subtype.val hab)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
