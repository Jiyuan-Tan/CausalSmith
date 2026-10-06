module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OracleGeometry
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OracleValue
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PostprocessCardinality

/-! # Directional equality and postprocessing nonmerger

Variance attainment forces equality in every certified information direction.
After staircase refinement, distinct projected scores then force the active
postprocessing rows to be pairwise mutually singular, giving an output
cardinality lower bound for arbitrary measurable output spaces.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- If a stationary channel attains the oracle variance, its Fisher information in every affine contrast direction is at least the oracle information. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hQ,hattain), [the attainment forces direction lower](goal).

Under the stated assumptions, the attainment forces direction lower. -/
-- @node: attainment_forces_direction_lower
lemma attainment_forces_direction_lower
    {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p ε t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q)
    (hattain : contrastVariance (channelFisherInfo θ p Q) =
      ENNReal.ofReal (Vstar θ p ε)) :
    Jstar θ p ε ≤
      informationQuadratic (channelFisherInfo θ p Q) (direction t) := by
  let I := channelFisherInfo θ p Q
  have hI : I.PosSemidef :=
    channelFisherInfo_posSemidef p θ hp hθ ε Q hQ
  have hJ : 0 < Jstar θ p ε :=
    Jstar_pos_interior θ p ε hp hθ hε
  have hrange : contrastInRange I := by
    by_contra hn
    have htop : contrastVariance I = ⊤ := by simp [contrastVariance, hn]
    rw [htop, Vstar] at hattain
    exact ENNReal.top_ne_ofReal hattain
  obtain ⟨w, hw⟩ := hrange
  let r := ∑ k : Fin 2, contrastVector k * w k
  have hr : 0 < r := contrastSolution_value_pos I hI w hw
  have her : ENNReal.ofReal r = ENNReal.ofReal (Jstar θ p ε)⁻¹ := by
    rw [← contrastVariance_eq_solution_value I hI w hw]
    simpa [I, Vstar] using hattain
  have hr_eq : r = (Jstar θ p ε)⁻¹ :=
    (ENNReal.ofReal_eq_ofReal_iff hr.le (inv_nonneg.mpr hJ.le)).mp her
  have hc := contrastInformation_cauchy I hI w hw t
  dsimp [r] at hr_eq
  rw [hr_eq] at hc
  calc
    Jstar θ p ε = 1 * Jstar θ p ε := by ring
    _ ≤ (informationQuadratic I (direction t) * (Jstar θ p ε)⁻¹) *
        Jstar θ p ε := mul_le_mul_of_nonneg_right hc hJ.le
    _ = informationQuadratic I (direction t) := by
      field_simp [ne_of_gt hJ]

/-- Under a uniform directional upper bound, an attaining channel has a staircase refinement with equality in that direction, so the refinement's equality-rigidity conclusion is available. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hQ,hattain,hupper), [the attaining staircase refinement direction eq](goal).

Under the stated assumptions, the attaining staircase refinement direction eq. -/
-- @node: attaining_staircase_refinement_direction_eq
lemma attaining_staircase_refinement_direction_eq
    {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p ε t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q)
    (hattain : contrastVariance (channelFisherInfo θ p Q) =
      ENNReal.ofReal (Vstar θ p ε))
    (hupper : ∀ β : StaircaseWeight, staircaseFeasible ε β →
      informationObjective θ p ε β t ≤ Jstar θ p ε) :
    ∃ α : StaircaseWeight, ∃ K : Kernel (Fin 14) Z,
      staircaseFeasible ε α ∧ IsMarkovKernel K ∧
      Q = K.comp (staircaseChannel ε α) ∧
      informationObjective θ p ε α t = Jstar θ p ε ∧
      informationQuadratic (informationMatrix θ p ε α) (direction t) =
        informationQuadratic (channelFisherInfo θ p Q) (direction t) ∧
      (∀ s u : Fin 14, α s ≠ 0 → α u ≠ 0 → ¬ (K s) ⟂ₘ (K u) →
        projectedScore θ p ε s t = projectedScore θ p ε u t) := by
  let epsSeq : ℕ → ℝ := fun _ ↦ ε
  have hfixed : FixedPrivacy epsSeq ε := ⟨hε, fun _ ↦ rfl⟩
  obtain ⟨α, K, hα, hK, hfactor, hdiff, hrigid⟩ :=
    staircase_refinement_interior p θ ε hp hθ epsSeq hfixed Q hQ
  have horder :
      informationQuadratic (channelFisherInfo θ p Q) (direction t) ≤
        informationQuadratic (informationMatrix θ p ε α) (direction t) := by
    have hn := hdiff.dotProduct_mulVec_nonneg (direction t)
    simp [informationQuadratic, dotProduct, Matrix.mulVec, star_trivial] at hn ⊢
    linarith
  have hαupper :
      informationQuadratic (informationMatrix θ p ε α) (direction t) ≤
        Jstar θ p ε := by
    have heq : informationObjective θ p ε α t =
        informationQuadratic (informationMatrix θ p ε α) (direction t) := by
      rw [informationObjective_eq_informationQuadratic θ p ε α t]
      rfl
    rw [← heq]
    exact hupper α hα
  have hQlower : Jstar θ p ε ≤
      informationQuadratic (channelFisherInfo θ p Q) (direction t) :=
    attainment_forces_direction_lower θ p ε t hp hθ hε Q hQ hattain
  have hQeq :
      informationQuadratic (channelFisherInfo θ p Q) (direction t) =
        Jstar θ p ε := le_antisymm (horder.trans hαupper) hQlower
  have hαeq :
      informationQuadratic (informationMatrix θ p ε α) (direction t) =
        Jstar θ p ε := le_antisymm hαupper (hQlower.trans horder)
  refine ⟨α, K, hα, hK, hfactor, ?_, hαeq.trans hQeq.symm, ?_⟩
  · calc
      informationObjective θ p ε α t =
          informationQuadratic (informationMatrix θ p ε α) (direction t) := by
            rw [informationObjective_eq_informationQuadratic θ p ε α t]
            rfl
      _ = Jstar θ p ε := hαeq
  · exact hrigid t (hαeq.trans hQeq.symm)

/-- A certified attaining direction with positive, pairwise distinct active scores requires at least as many output atoms as active staircase rays. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hupper,hpositive,hdistinct,hQ,hattain), [the output Cardinality ge of attainment direction](goal).

Under the stated assumptions, the output Cardinality ge of attainment direction. -/
-- @node: outputCardinality_ge_of_attainment_direction
lemma outputCardinality_ge_of_attainment_direction
    {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p ε t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (A : Finset (Fin 14))
    (hupper : ∀ β : StaircaseWeight, staircaseFeasible ε β →
      informationObjective θ p ε β t ≤ Jstar θ p ε)
    (hpositive : ∀ β : StaircaseWeight, staircaseFeasible ε β →
      informationObjective θ p ε β t = Jstar θ p ε →
      ∀ s ∈ A, 0 < β s)
    (hdistinct : ∀ s ∈ A, ∀ u ∈ A, s ≠ u →
      projectedScore θ p ε s t ≠ projectedScore θ p ε u t)
    (Q : Kernel (Fin 4) Z) (hQ : StationaryLDP ε Q)
    (hattain : contrastVariance (channelFisherInfo θ p Q) =
      ENNReal.ofReal (Vstar θ p ε)) :
    (A.card : ℕ∞) ≤ outputCardinality θ p Q := by
  obtain ⟨α, K, hα, hK, hfactor, hαeq, heq, hrigid⟩ :=
    attaining_staircase_refinement_direction_eq θ p ε t hp hθ hε Q hQ
      hattain hupper
  have hpos : ∀ s ∈ A, 0 < α s := hpositive α hα hαeq
  have hsing : ∀ s ∈ A, ∀ u ∈ A, s ≠ u → K s ⟂ₘ K u := by
    intro s hs u hu hne
    by_contra hn
    exact hdistinct s hs u hu hne
      (hrigid s u (ne_of_gt (hpos s hs)) (ne_of_gt (hpos u hu)) hn)
  exact active_card_le_outputCardinality_of_pairwise_singular θ p ε hp hθ
    A α hpos K hK Q hfactor hsing

end CausalSmith.Stat.LdpAteEfficiencySurface
