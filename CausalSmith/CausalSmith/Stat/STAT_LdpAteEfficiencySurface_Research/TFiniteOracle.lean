module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OracleValue
public import Mathlib.Topology.Sion

/-! # Exact finite staircase oracle -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

-- @node: finiteOracle_minimax
/-- Under the supplied quantities and conditions, the finite oracle minimax assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the finite Oracle minimax](goal).

Under the stated assumptions, the finite Oracle minimax. -/
lemma finiteOracle_minimax (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    Jstar θ p ε =
      sInf {u : ℝ | ∃ t : ℝ, u = upperEnvelope θ p ε t} := by
  let S := feasibleSet ε
  let f : StaircaseWeight → ℝ → ℝ :=
    fun α t => -informationObjective θ p ε α t
  have hS : S.Nonempty := staircaseFeasible_nonempty ε
  have hcS : IsCompact S := staircaseFeasible_compact ε hε.le
  have hconvS : Convex ℝ S := staircaseFeasible_convex ε
  have hcontα (t : ℝ) : Continuous (fun α => f α t) := by
    dsimp [f]
    exact (informationObjective_continuous_weight θ p ε t).neg
  have hquasiα (t : ℝ) : QuasiconvexOn ℝ S (fun α => f α t) := by
    apply ConvexOn.quasiconvexOn
    refine ⟨hconvS, ?_⟩
    intro α hα β hβ a b ha hb hab
    change -(informationObjective θ p ε (a • α + b • β) t) ≤
      a * -informationObjective θ p ε α t +
        b * -informationObjective θ p ε β t
    rw [informationObjective_affine_weights]
    simp
  have hcontT (α : StaircaseWeight) :
      Continuous (fun t => f α t) := by
    dsimp [f]
    unfold informationObjective patternInformation projectedGradient direction
    simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, ite_true,
      ite_false, add_zero]
    fun_prop
  have hquasiT (α : StaircaseWeight) (hα : α ∈ S) :
      QuasiconcaveOn ℝ Set.univ (f α) := by
    have hc := informationObjective_convexOn_time θ p ε α hα.1
      (patternMass_pos_interior θ p ε hp hθ hε.le)
    apply ConcaveOn.quasiconcaveOn
    exact hc.neg
  let M : StaircaseWeight → ℝ := fun α =>
    sInf {u : ℝ | ∃ t : ℝ, u = informationObjective θ p ε α t}
  let H : ℝ → ℝ := upperEnvelope θ p ε
  have hM (α : StaircaseWeight) (hα : α ∈ S) :
      ∃ t : ℝ, M α = informationObjective θ p ε α t ∧
        ∀ u, informationObjective θ p ε α t ≤
          informationObjective θ p ε α u := by
    obtain ⟨t, ht⟩ := informationObjective_exists_minimizer θ p ε
      hp hθ hε.le α hα
    refine ⟨t, ?_, ht⟩
    apply IsLeast.csInf_eq
    exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact ht u⟩
  have hH (t : ℝ) :
      ∃ α ∈ S, H t = informationObjective θ p ε α t ∧
        ∀ β ∈ S, informationObjective θ p ε β t ≤
          informationObjective θ p ε α t := by
    obtain ⟨α, hα, hmax⟩ :=
      informationObjective_exists_maximizer θ p ε t hε.le
    refine ⟨α, hα, ?_, hmax⟩
    unfold H upperEnvelope
    apply IsGreatest.csSup_eq
    exact ⟨⟨α, hα, rfl⟩, by
      rintro _ ⟨β, hβ, rfl⟩
      exact hmax β hβ⟩
  have hsup_y (α : StaircaseWeight) (hα : α ∈ S) :
      IsLUB {u : ℝ | ∃ t ∈ (Set.univ : Set ℝ), f α t = u} (-M α) := by
    obtain ⟨t, hMt, hmin⟩ := hM α hα
    apply IsGreatest.isLUB
    constructor
    · exact ⟨t, Set.mem_univ _, by dsimp [f]; rw [hMt]⟩
    · rintro u ⟨v, _, rfl⟩
      dsimp [f]
      rw [hMt]
      exact neg_le_neg (hmin v)
  have hinf_sup :
      IsGLB {u : ℝ | ∃ α ∈ S, -M α = u} (-Jstar θ p ε) := by
    obtain ⟨γ, hγ, hmax⟩ :=
      informationObjective_profile_exists_maximizer θ p ε hp hθ hε.le
    have hprofile (β : StaircaseWeight) :
        (⨅ t : ℝ, informationObjective θ p ε β t) = M β := by
      change (⨅ t : ℝ, informationObjective θ p ε β t) =
        sInf {u : ℝ | ∃ t : ℝ, u = informationObjective θ p ε β t}
      rw [show {u : ℝ | ∃ t : ℝ,
          u = informationObjective θ p ε β t} =
        Set.range (informationObjective θ p ε β) from by ext u; simp [eq_comm]]
      rfl
    have hJ : Jstar θ p ε = M γ := by
      apply IsGreatest.csSup_eq
      exact ⟨⟨γ, hγ, rfl⟩, by
        rintro _ ⟨β, hβ, rfl⟩
        change M β ≤ M γ
        rw [← hprofile β, ← hprofile γ]
        exact hmax β hβ⟩
    apply IsLeast.isGLB
    constructor
    · exact ⟨γ, hγ, by rw [hJ]⟩
    · rintro _ ⟨β, hβ, rfl⟩
      rw [hJ, ← hprofile γ, ← hprofile β]
      exact neg_le_neg (hmax β hβ)
  have hinf_x (t : ℝ) :
      IsGLB {u : ℝ | ∃ α ∈ S, f α t = u} (-H t) := by
    obtain ⟨α, hα, hHt, hmax⟩ := hH t
    apply IsLeast.isGLB
    constructor
    · exact ⟨α, hα, by dsimp [f]; rw [hHt]⟩
    · rintro _ ⟨β, hβ, rfl⟩
      dsimp [f]
      rw [hHt]
      exact neg_le_neg (hmax β hβ)
  have hsup_inf :
      IsLUB {u : ℝ | ∃ t ∈ (Set.univ : Set ℝ), -H t = u}
        (-sInf {u : ℝ | ∃ t : ℝ, u = H t}) := by
    obtain ⟨t, ht⟩ := upperEnvelope_exists_minimizer θ p ε hp hθ hε
    have hleast : sInf {u : ℝ | ∃ v : ℝ, u = H v} = H t := by
      apply IsLeast.csInf_eq
      exact ⟨⟨t, rfl⟩, by rintro _ ⟨v, rfl⟩; exact ht v⟩
    apply IsGreatest.isLUB
    constructor
    · exact ⟨t, Set.mem_univ _, by rw [hleast]⟩
    · rintro _ ⟨v, _, rfl⟩
      rw [hleast]
      exact neg_le_neg (ht v)
  have hsion := Sion.minimax
    (X := S) (Y := Set.univ) (f := f)
    hS hcS
    (fun t _ => (hcontα t).continuousOn.lowerSemicontinuousOn)
    (fun t _ => hquasiα t)
    convex_univ
    (fun α hα => (hcontT α).continuousOn.upperSemicontinuousOn)
    (fun α hα => hquasiT α hα)
    hconvS
    (fun α => -M α) hsup_y (-Jstar θ p ε) hinf_sup
    (fun t => -H t) (fun t _ => hinf_x t)
    (-sInf {u : ℝ | ∃ t : ℝ, u = H t}) hsup_inf
  exact neg_injective hsion

-- @node: thm:finite-oracle
/-- Under [the supplied quantities and conditions](hyp:p), [the finite oracle assertion](goal) holds. For [the displayed quantities and conditions](hyp:hassignment,hmeans,epsSeq,hfixed), these specify the stated inputs. -/
theorem finite_oracle (θ : TrialParameter) (p ε : ℝ)
    (hassignment : InteriorAssignment p)
    (hmeans : InteriorMeans θ)
    (epsSeq : ℕ → ℝ) (hfixed : FixedPrivacy epsSeq ε) :
    (∀ (Z : Type*) [MeasurableSpace Z] (Q : Kernel (Fin 4) Z),
      StationaryLDP ε Q →
      ENNReal.ofReal (Vstar θ p ε) ≤
        contrastVariance (channelFisherInfo θ p Q)) ∧
    (∃ α : StaircaseWeight, staircaseFeasible ε α ∧
      StationaryLDP ε (staircaseChannel ε α) ∧
      contrastVariance (channelFisherInfo θ p (staircaseChannel ε α)) =
        ENNReal.ofReal (Vstar θ p ε) ∧
      contrastVariance (informationMatrix θ p ε α) =
        ENNReal.ofReal (Vstar θ p ε)) ∧
    Jstar θ p ε =
      sInf {u : ℝ | ∃ t : ℝ, u = upperEnvelope θ p ε t} ∧
    Jstar θ p ε =
      sInf {u : ℝ | ∃ t : ℝ, u = vertexEnvelope θ p ε t} ∧
    (∃ t : ℝ, upperEnvelope θ p ε t = Jstar θ p ε) := by
  have hminimax : Jstar θ p ε =
      sInf {u : ℝ | ∃ t : ℝ, u = upperEnvelope θ p ε t} :=
    finiteOracle_minimax θ p ε hassignment hmeans hfixed.1
  have henvelopes :
      {u : ℝ | ∃ t : ℝ, u = upperEnvelope θ p ε t} =
      {u : ℝ | ∃ t : ℝ, u = vertexEnvelope θ p ε t} := by
    ext u
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, upperEnvelope_eq_vertexEnvelope θ p ε t hfixed.1.le⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, (upperEnvelope_eq_vertexEnvelope θ p ε t hfixed.1.le).symm⟩
  refine ⟨?_, ?_, hminimax, hminimax.trans (congrArg sInf henvelopes), ?_⟩
  · intro Z _ Q hQ
    obtain ⟨α, K, hα, hK, hfactor, hdiff, hrigid⟩ :=
      staircase_refinement_interior p θ ε hassignment hmeans epsSeq hfixed Q hQ
    obtain ⟨t, ht⟩ := informationObjective_exists_minimizer θ p ε
      hassignment hmeans hfixed.1.le α hα
    have hleast :
        sInf {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε α v} =
          informationObjective θ p ε α t := by
      apply IsLeast.csInf_eq
      exact ⟨⟨t, rfl⟩, by rintro u ⟨v, rfl⟩; exact ht v⟩
    have hprofile_le : informationObjective θ p ε α t ≤ Jstar θ p ε := by
      obtain ⟨γ, hγ, hmax⟩ :=
        informationObjective_profile_exists_maximizer θ p ε
          hassignment hmeans hfixed.1.le
      have hprofile (β : StaircaseWeight) :
          (⨅ v : ℝ, informationObjective θ p ε β v) =
            sInf {u : ℝ | ∃ v : ℝ,
              u = informationObjective θ p ε β v} := by
        rw [show {u : ℝ | ∃ v : ℝ,
            u = informationObjective θ p ε β v} =
          Set.range (informationObjective θ p ε β) from by
            ext u
            simp [eq_comm]]
        rfl
      rw [Jstar, ← hleast]
      apply le_csSup
      · refine ⟨sInf {u : ℝ | ∃ v : ℝ,
          u = informationObjective θ p ε γ v}, ?_⟩
        rintro u ⟨β, hβ, rfl⟩
        rw [← hprofile β, ← hprofile γ]
        exact hmax β hβ
      · exact ⟨α, hα, rfl⟩
    have horder : informationQuadratic (channelFisherInfo θ p Q) (direction t) ≤
        informationQuadratic (informationMatrix θ p ε α) (direction t) := by
      have hn := hdiff.dotProduct_mulVec_nonneg (direction t)
      simp [informationQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
        Finset.sum_sub_distrib, star_trivial] at hn ⊢
      linarith
    have htQ : informationQuadratic (channelFisherInfo θ p Q) (direction t) ≤
        Jstar θ p ε := by
      refine horder.trans ?_
      have heq : informationObjective θ p ε α t =
          informationQuadratic (informationMatrix θ p ε α) (direction t) := by
        rw [informationObjective_eq_informationQuadratic θ p ε α t]
        rfl
      rw [← heq]
      exact hprofile_le
    have hJ : 0 < Jstar θ p ε :=
      Jstar_pos_interior θ p ε hassignment hmeans hfixed.1
    simpa [Vstar] using reciprocal_le_contrastVariance
      (channelFisherInfo θ p Q)
      (channelFisherInfo_posSemidef p θ hassignment hmeans ε Q hQ)
      (Jstar θ p ε) hJ t htQ
  · obtain ⟨α, hα, hopt⟩ :=
      Jstar_exists_optimal_weight θ p ε hassignment hmeans hfixed.1.le
    obtain ⟨t, ht⟩ := informationObjective_exists_minimizer θ p ε
      hassignment hmeans hfixed.1.le α hα
    have hleast :
        sInf {u : ℝ | ∃ v : ℝ, u = informationObjective θ p ε α v} =
          informationObjective θ p ε α t := by
      apply IsLeast.csInf_eq
      exact ⟨⟨t, rfl⟩, by rintro u ⟨v, rfl⟩; exact ht v⟩
    have hvalue : informationObjective θ p ε α t = Jstar θ p ε := by
      rw [← hleast, ← hopt]
    have hqmin : ∀ u : ℝ,
        informationQuadratic (informationMatrix θ p ε α) (direction t) ≤
          informationQuadratic (informationMatrix θ p ε α) (direction u) := by
      intro u
      have heqt : informationObjective θ p ε α t =
          informationQuadratic (informationMatrix θ p ε α) (direction t) := by
        rw [informationObjective_eq_informationQuadratic θ p ε α t]
        rfl
      have hequ : informationObjective θ p ε α u =
          informationQuadratic (informationMatrix θ p ε α) (direction u) := by
        rw [informationObjective_eq_informationQuadratic θ p ε α u]
        rfl
      rw [← heqt, ← hequ]
      exact ht u
    have hqpos : 0 <
        informationQuadratic (informationMatrix θ p ε α) (direction t) := by
      have heq : informationObjective θ p ε α t =
          informationQuadratic (informationMatrix θ p ε α) (direction t) := by
        rw [informationObjective_eq_informationQuadratic θ p ε α t]
        rfl
      rw [← heq, hvalue]
      exact Jstar_pos_interior θ p ε hassignment hmeans hfixed.1
    have hattain : contrastVariance (informationMatrix θ p ε α) =
        ENNReal.ofReal (Vstar θ p ε) := by
      rw [contrastVariance_eq_reciprocal_of_minimizer
        (informationMatrix θ p ε α)
        (informationMatrix_posSemidef_interior θ p ε hassignment hmeans
          hfixed.1.le α hα) t hqmin hqpos]
      congr 1
      have heq : informationObjective θ p ε α t =
          informationQuadratic (informationMatrix θ p ε α) (direction t) := by
        rw [informationObjective_eq_informationQuadratic θ p ε α t]
        rfl
      rw [← heq, hvalue]
      rfl
    refine ⟨α, hα, staircaseChannel_stationaryLDP ε hfixed.1 α hα, ?_, hattain⟩
    rw [channelFisherInfo_staircase_eq_informationMatrix θ p ε
      hassignment hmeans hfixed.1 α hα]
    exact hattain
  · obtain ⟨t, ht⟩ :=
      upperEnvelope_exists_minimizer θ p ε hassignment hmeans hfixed.1
    have hleast : sInf {u : ℝ | ∃ v : ℝ, u = upperEnvelope θ p ε v} =
        upperEnvelope θ p ε t := by
      apply IsLeast.csInf_eq
      exact ⟨⟨t, rfl⟩, by
        rintro u ⟨v, rfl⟩
        exact ht v⟩
    exact ⟨t, (hminimax.trans hleast).symm⟩


end CausalSmith.Stat.LdpAteEfficiencySurface
