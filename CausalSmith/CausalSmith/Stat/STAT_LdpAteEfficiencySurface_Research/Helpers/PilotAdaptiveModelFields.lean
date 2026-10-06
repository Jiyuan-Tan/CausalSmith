module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveRegularization

/-! # Routine model fields for adaptive pilot asymptotics

This file packages the finite pilot sample, its selected parameter, and fixed compact
interior neighborhoods used by the adaptive asymptotic model.  It does not depend on
the generic adaptive limit theorem.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory Filter
open scoped Topology BigOperators

/-- For the supplied quantities and conditions, the adaptive pilot sample is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Adaptive Pilot Sample](goal) is determined by [the displayed parameters](hyp:m,n). -/
abbrev AdaptivePilotSample (m : ℕ → ℕ) (n : ℕ) :=
  Fin (adaptivePilotSize m n) → Fin 4

/-- For the supplied quantities and conditions, the adaptive pilot selector is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The adaptive Pilot Selector](goal) is determined by [the displayed parameters](hyp:p,ε,m,n,u). -/
def adaptivePilotSelector (p ε : ℝ) (m : ℕ → ℕ) (n : ℕ)
    (u : AdaptivePilotSample m n) : TrialParameter :=
  pilotAdaptivePrefixTheta p ε (adaptivePilotSize m)
    (adaptivePilotSize_le m n) u

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under [the supplied quantities and conditions](hyp:p,m,n), [the adaptive pilot selector interior assertion](goal) holds. For [the displayed quantities and conditions](hyp:u), these specify the stated inputs. -/
lemma adaptivePilotSelector_interior (p ε : ℝ) (m : ℕ → ℕ) (n : ℕ)
    (u : AdaptivePilotSample m n) :
    InteriorMeans (adaptivePilotSelector p ε m n u) := by
  exact pilotTheta_interior p ε (adaptivePilotSize m)
    (pilotAdaptiveEncode (adaptivePilotSize_le m n) u (fun _ => 0))

/-- Under [the supplied quantities and conditions](hyp:p,m,n), [the measurable adaptive pilot selector assertion](goal) holds. -/
lemma measurable_adaptivePilotSelector (p ε : ℝ) (m : ℕ → ℕ) (n : ℕ) :
    Measurable (adaptivePilotSelector p ε m n) := by
  exact measurable_of_finite _

private lemma measurable_patternMass_arg (p ε : ℝ) (s : Fin 14) :
    Measurable (fun θ => patternMass θ p ε s) := by
  unfold patternMass
  apply Finset.measurable_sum Finset.univ
  intro j _
  fin_cases j <;> simp [piTheta] <;> fun_prop

private lemma measurable_projectedGradient_comp (p ε : ℝ) (s : Fin 14)
    {X : Type*} [MeasurableSpace X] (t : X → ℝ) (ht : Measurable t) :
    Measurable (fun x => projectedGradient p ε s (t x)) := by
  unfold projectedGradient
  apply Finset.measurable_sum Finset.univ
  intro k _
  fin_cases k <;> simp [direction] <;> fun_prop

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the measurable adaptive selected score pair assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε), [the measurable adaptive Selected Score pair](goal).

Under the stated assumptions, the measurable adaptive Selected Score pair. -/
lemma measurable_adaptiveSelectedScore_pair (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    Measurable (fun pair : TrialParameter × Fin 14 =>
      adaptiveSelectedScore select pair.1 p ε pair.2) := by
  have hs : Measurable (select) :=
    (hselect.1).1
  apply measurable_from_prod_countable_left
  intro s
  have ht : Measurable (fun η => (select η).2.1) :=
    measurable_fst.comp (measurable_snd.comp hs)
  have hJ : Measurable (fun η => (select η).2.2) :=
    measurable_snd.comp (measurable_snd.comp hs)
  have hg : Measurable (fun η =>
      projectedGradient p ε s (select η).2.1) := by
    exact measurable_projectedGradient_comp p ε s _ ht
  have hm : Measurable (fun η => patternMass η p ε s) :=
    measurable_patternMass_arg p ε s
  unfold adaptiveSelectedScore phiTilde
  exact hg.div (hJ.mul hm)

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the measurable adaptive main mass pair assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε), [the measurable adaptive Main Mass pair](goal).

Under the stated assumptions, the measurable adaptive Main Mass pair. -/
lemma measurable_adaptiveMainMass_pair (p ε : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) :
    Measurable (fun pair : (TrialParameter × TrialParameter) × Fin 14 =>
      adaptiveMainMass select pair.1.1 pair.1.2 p ε pair.2) := by
  have hs : Measurable (select) :=
    (hselect.1).1
  apply measurable_from_prod_countable_left
  intro s
  have hα : Measurable (fun η => (select η).1 s) :=
    measurable_pi_apply s |>.comp (measurable_fst.comp hs)
  have hm : Measurable (fun θ => patternMass θ p ε s) :=
    measurable_patternMass_arg p ε s
  unfold adaptiveMainMass
  exact (hα.comp measurable_snd).mul (hm.comp measurable_fst)

/-- the adaptive interior margin is the mathematical object specified below. [The adaptive Interior Margin](goal) is determined by [the displayed parameters](hyp:θ). -/
def adaptiveInteriorMargin (θ : TrialParameter) : ℝ :=
  min (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1))

/-- the [adaptive neighborhood](goal) is the mathematical object specified below. -/
def adaptiveNeighborhood : Set TrialParameter :=
  {η | InteriorMeans η}

/-- the adaptive compact values is the mathematical object specified below. [The adaptive Compact Values](goal) is determined by [the displayed parameters](hyp:θ). -/
def adaptiveCompactValues (θ : TrialParameter) : Set TrialParameter :=
  Metric.closedBall θ (adaptiveInteriorMargin θ / 2)

/-- Under the supplied quantities and conditions, the adaptive interior margin pos assertion holds. Under [the stated assumptions](hyp:hθ), [the adaptive Interior Margin pos](goal).

Under the stated assumptions, the adaptive Interior Margin pos. -/
lemma adaptiveInteriorMargin_pos (θ : TrialParameter) (hθ : InteriorMeans θ) :
    0 < adaptiveInteriorMargin θ := by
  simp only [adaptiveInteriorMargin, lt_min_iff]
  exact ⟨⟨hθ.1, sub_pos.mpr hθ.2.1⟩,
    ⟨hθ.2.2.1, sub_pos.mpr hθ.2.2.2⟩⟩

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- [the adaptive neighborhood is open assertion](goal) holds. -/
lemma adaptiveNeighborhood_isOpen : IsOpen adaptiveNeighborhood := by
  change IsOpen { η : TrialParameter |
    0 < η 0 ∧ η 0 < 1 ∧ 0 < η 1 ∧ η 1 < 1 }
  have h0l : IsOpen { η : TrialParameter | (0 : ℝ) < η 0 } :=
    isOpen_lt continuous_const (continuous_apply 0)
  have h0r : IsOpen { η : TrialParameter | η 0 < (1 : ℝ) } :=
    isOpen_lt (continuous_apply 0) continuous_const
  have h1l : IsOpen { η : TrialParameter | (0 : ℝ) < η 1 } :=
    isOpen_lt continuous_const (continuous_apply 1)
  have h1r : IsOpen { η : TrialParameter | η 1 < (1 : ℝ) } :=
    isOpen_lt (continuous_apply 1) continuous_const
  convert ((h0l.inter h0r).inter h1l).inter h1r using 1 <;>
    ext η <;> simp [and_assoc]

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- [the adaptive compact values is compact assertion](goal) holds. -/
lemma adaptiveCompactValues_isCompact (θ : TrialParameter) :
    IsCompact (adaptiveCompactValues θ) := by
  exact isCompact_closedBall _ _

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the adaptive compact values mem assertion holds. Under [the stated assumptions](hyp:hθ), [the adaptive Compact Values mem](goal).

Under the stated assumptions, the adaptive Compact Values mem. -/
lemma adaptiveCompactValues_mem (θ : TrialParameter) (hθ : InteriorMeans θ) :
    θ ∈ adaptiveCompactValues θ := by
  exact Metric.mem_closedBall_self
    (div_nonneg (adaptiveInteriorMargin_pos θ hθ).le (by norm_num))

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- the adaptive compact values mem interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ), [the adaptive Compact Values mem interior](goal).

Under the stated assumptions, the adaptive Compact Values mem interior. -/
lemma adaptiveCompactValues_mem_interior (θ : TrialParameter)
    (hθ : InteriorMeans θ) :
    θ ∈ interior (adaptiveCompactValues θ) := by
  rw [mem_interior_iff_mem_nhds]
  apply mem_of_superset
    (Metric.ball_mem_nhds θ (half_pos (adaptiveInteriorMargin_pos θ hθ)))
  exact Metric.ball_subset_closedBall

/-- the adaptive compact values interior means assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hθ), [the adaptive Compact Values interior Means](goal).

Under the stated assumptions, the adaptive Compact Values interior Means. -/
lemma adaptiveCompactValues_interiorMeans (θ : TrialParameter)
    (hθ : InteriorMeans θ) :
    adaptiveCompactValues θ ⊆ adaptiveNeighborhood := by
  intro η hη
  have hmpos := adaptiveInteriorMargin_pos θ hθ
  have hrnonneg : 0 ≤ adaptiveInteriorMargin θ / 2 := by positivity
  have hd := (dist_pi_le_iff hrnonneg).mp (Metric.mem_closedBall.mp hη)
  have hd0 := hd 0
  have hd1 := hd 1
  rw [Real.dist_eq] at hd0 hd1
  have hm0l : adaptiveInteriorMargin θ ≤ θ 0 := by
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hm0r : adaptiveInteriorMargin θ ≤ 1 - θ 0 := by
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hm1l : adaptiveInteriorMargin θ ≤ θ 1 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hm1r : adaptiveInteriorMargin θ ≤ 1 - θ 1 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  change 0 < η 0 ∧ η 0 < 1 ∧ 0 < η 1 ∧ η 1 < 1
  have habs0 := abs_le.mp hd0
  have habs1 := abs_le.mp hd1
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- For the supplied quantities and conditions, the adaptive good pilot is the mathematical object specified below. [The adaptive Good Pilot](goal) is determined by [the displayed parameters](hyp:θ,p,ε,m,n). -/
def adaptiveGoodPilot (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ) (n : ℕ) :
    Set (AdaptivePilotSample m n) :=
  {u | adaptivePilotSelector p ε m n u ∈ adaptiveCompactValues θ}

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under [the supplied quantities and conditions](hyp:p), [the adaptive good pilot measurable assertion](goal) holds. For [the displayed quantities and conditions](hyp:m,n), these specify the stated inputs. -/
lemma adaptiveGoodPilot_measurable (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (n : ℕ) :
    MeasurableSet (adaptiveGoodPilot θ p ε m n) := by
  change MeasurableSet
    ((adaptivePilotSelector p ε m n) ⁻¹' Metric.closedBall θ
      (adaptiveInteriorMargin θ / 2))
  exact Metric.isClosed_closedBall.measurableSet.preimage
    (measurable_adaptivePilotSelector p ε m n)

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under [the supplied quantities and conditions](hyp:p), [the adaptive good pilot selector mem assertion](goal) holds. For [the displayed quantities and conditions](hyp:m,n,hu), these specify the stated inputs. -/
lemma adaptiveGoodPilot_selector_mem (θ : TrialParameter) (p ε : ℝ)
    (m : ℕ → ℕ) (n : ℕ) {u : AdaptivePilotSample m n}
    (hu : u ∈ adaptiveGoodPilot θ p ε m n) :
    adaptivePilotSelector p ε m n u ∈ adaptiveCompactValues θ := by
  exact hu

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the adaptive score moment uniform on compact assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hr), [the adaptive Score Moment uniform on compact](goal).

Under the stated assumptions, the adaptive Score Moment uniform on compact. -/
lemma adaptiveScoreMoment_uniform_on_compact (θ : TrialParameter) (p ε r : ℝ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ' η,
      θ' ∈ adaptiveNeighborhood → η ∈ adaptiveCompactValues θ →
        adaptiveScoreMoment select r θ' η p ε ≤ C := by
  refine ⟨(pilotPhiUpper p ε) ^ r,
    Real.rpow_nonneg (pilotPhiUpper_nonneg p ε hp hε) r, ?_⟩
  intro θ' η hθ' hη
  exact adaptiveScoreMoment_le select θ' η p ε r hselect hp hθ'
    (adaptiveCompactValues_interiorMeans θ hθ hη) hε hr

end CausalSmith.Stat.LdpAteEfficiencySurface
