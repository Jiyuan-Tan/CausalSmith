module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OracleGeometry

/-! # Staircase information envelope -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

-- @node: informationObjective_affine_weights
/-- Under [the supplied quantities and conditions](hyp:p,t,a,b), [the information objective affine weights assertion](goal) holds. -/
lemma informationObjective_affine_weights (θ : TrialParameter) (p ε t a b : ℝ)
    (α β : StaircaseWeight) :
    informationObjective θ p ε (a • α + b • β) t =
      a * informationObjective θ p ε α t +
        b * informationObjective θ p ε β t := by
  unfold informationObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  change (a * α s + b * β s) * patternInformation θ p ε s t =
    a * (α s * patternInformation θ p ε s t) +
      b * (β s * patternInformation θ p ε s t)
  ring

-- @node: informationObjective_exists_maximizer
/-- the information objective exists maximizer assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the information Objective exists maximizer](goal).

Under the stated assumptions, the information Objective exists maximizer. -/
lemma informationObjective_exists_maximizer (θ : TrialParameter)
    (p ε t : ℝ) (hε : 0 ≤ ε) :
    ∃ α ∈ feasibleSet ε, ∀ β ∈ feasibleSet ε,
      informationObjective θ p ε β t ≤ informationObjective θ p ε α t := by
  obtain ⟨α, hα, hmax⟩ :=
    (staircaseFeasible_compact ε hε).exists_isMaxOn
      (staircaseFeasible_nonempty ε)
      (informationObjective_continuous_weight θ p ε t).continuousOn
  exact ⟨α, hα, fun β hβ => hmax hβ⟩

-- @node: upperEnvelope_attained
/-- Under the supplied quantities and conditions, the upper envelope attained assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the upper Envelope attained](goal).

Under the stated assumptions, the upper Envelope attained. -/
lemma upperEnvelope_attained (θ : TrialParameter) (p ε t : ℝ)
    (hε : 0 ≤ ε) :
    ∃ α ∈ feasibleSet ε,
      upperEnvelope θ p ε t = informationObjective θ p ε α t := by
  obtain ⟨α, hα, hmax⟩ :=
    informationObjective_exists_maximizer θ p ε t hε
  refine ⟨α, hα, ?_⟩
  unfold upperEnvelope
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨α, hα, rfl⟩
  · rintro u ⟨β, hβ, rfl⟩
    exact hmax β hβ

-- @node: upperEnvelope_quadratic_lower_bound
/-- Under the supplied quantities and conditions, the upper envelope quadratic lower bound assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the upper Envelope quadratic lower bound](goal).

Under the stated assumptions, the upper Envelope quadratic lower bound. -/
lemma upperEnvelope_quadratic_lower_bound (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * t ^ 2 ≤ upperEnvelope θ p ε t := by
  obtain ⟨α, hα, hα0⟩ := staircaseFeasible_positive_first_pattern ε
  let c := α 0 * ((privacyIncrement ε * controlProb p) ^ 2 /
    patternMass θ p ε 0)
  have hc : 0 < c := by
    have hd : 0 < privacyIncrement ε := privacyIncrement_pos hε
    have hq : 0 < controlProb p := by dsimp [controlProb]; linarith [hp.2]
    have hm := patternMass_pos_interior θ p ε hp hθ hε.le 0
    dsimp [c]
    positivity
  refine ⟨c, hc, fun t => ?_⟩
  obtain ⟨β, hβ, hmax⟩ :=
    informationObjective_exists_maximizer θ p ε t hε.le
  have hterm : α 0 * patternInformation θ p ε 0 t ≤
      informationObjective θ p ε α t := by
    unfold informationObjective
    exact Finset.single_le_sum
      (fun s _ => show 0 ≤ α s * patternInformation θ p ε s t from
        mul_nonneg (hα.1 s)
          (by unfold patternInformation
              exact div_nonneg (sq_nonneg _)
                (le_of_lt (patternMass_pos_interior θ p ε hp hθ hε.le s))))
      (Finset.mem_univ 0)
  calc
    c * t ^ 2 = α 0 * patternInformation θ p ε 0 t := by
      rw [first_pattern_information_quadratic]
      dsimp [c]
      ring
    _ ≤ informationObjective θ p ε α t := hterm
    _ ≤ upperEnvelope θ p ε t := by
      unfold upperEnvelope
      exact le_csSup ⟨informationObjective θ p ε β t, by
        rintro u ⟨γ, hγ, rfl⟩
        exact hmax γ hγ⟩ ⟨α, hα, rfl⟩

-- @node: upperEnvelope_continuous
/-- Under the supplied quantities and conditions, the upper envelope continuous assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the upper Envelope continuous](goal).

Under the stated assumptions, the upper Envelope continuous. -/
lemma upperEnvelope_continuous (θ : TrialParameter) (p ε : ℝ)
    (hε : 0 ≤ ε) :
    Continuous (fun t : ℝ => upperEnvelope θ p ε t) := by
  have hf : Continuous (fun z : ℝ × StaircaseWeight =>
      informationObjective θ p ε z.2 z.1) := by
    unfold informationObjective
    apply continuous_finsetSum
    intro s _
    unfold patternInformation projectedGradient direction
    simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, ite_true,
      ite_false, add_zero]
    fun_prop
  have hc := (staircaseFeasible_compact ε hε).continuous_sSup
    (f := fun t α => informationObjective θ p ε α t) hf
  simpa [upperEnvelope, Set.image, eq_comm] using hc

/-- For the supplied quantities and conditions, the vertex envelope is the mathematical object specified below. [The vertex Envelope](goal) is determined by [the displayed parameters](hyp:θ,p,ε,t). -/
def vertexEnvelope (θ : TrialParameter) (p ε t : ℝ) : ℝ :=
  sSup {u : ℝ | ∃ α ∈ (feasibleSet ε).extremePoints ℝ,
    u = informationObjective θ p ε α t}

-- @node: upperEnvelope_eq_vertexEnvelope
/-- Under the supplied quantities and conditions, the upper envelope eq vertex envelope assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hε), [the upper Envelope eq vertex Envelope](goal).

Under the stated assumptions, the upper Envelope eq vertex Envelope. -/
lemma upperEnvelope_eq_vertexEnvelope (θ : TrialParameter) (p ε t : ℝ)
    (hε : 0 ≤ ε) :
    upperEnvelope θ p ε t = vertexEnvelope θ p ε t := by
  let S := feasibleSet ε
  let f : StaircaseWeight → ℝ := fun α => informationObjective θ p ε α t
  have hcompact : IsCompact S := staircaseFeasible_compact ε hε
  have hconvex : Convex ℝ S := staircaseFeasible_convex ε
  have hne : S.Nonempty := staircaseFeasible_nonempty ε
  obtain ⟨v, hv⟩ := hcompact.extremePoints_nonempty hne
  obtain ⟨a, ha, hmax⟩ :=
    informationObjective_exists_maximizer θ p ε t hε
  have hsup : upperEnvelope θ p ε t = f a := by
    unfold upperEnvelope
    apply IsGreatest.csSup_eq
    exact ⟨⟨a, ha, rfl⟩, by
      rintro z ⟨b, hb, rfl⟩
      exact hmax b hb⟩
  have hvBound : ∀ x ∈ S.extremePoints ℝ, f x ≤ f a := by
    intro x hx
    exact hmax x (extremePoints_subset hx)
  have hvertex : vertexEnvelope θ p ε t ≤ f a := by
    unfold vertexEnvelope
    apply csSup_le
    · exact ⟨f v, v, hv, rfl⟩
    · rintro z ⟨x, hx, rfl⟩
      exact hvBound x hx
  have hsub : S.extremePoints ℝ ⊆ {x | f x ≤ vertexEnvelope θ p ε t} := by
    intro x hx
    unfold vertexEnvelope
    exact le_csSup ⟨f a, by
      rintro z ⟨y, hy, rfl⟩
      exact hvBound y hy⟩ ⟨x, hx, rfl⟩
  have hclosed : IsClosed {x : StaircaseWeight | f x ≤ vertexEnvelope θ p ε t} :=
    isClosed_le (informationObjective_continuous_weight θ p ε t) continuous_const
  have hconvexBound : Convex ℝ {x : StaircaseWeight | f x ≤ vertexEnvelope θ p ε t} := by
    intro x hx y hy a b ha hb hab
    change f (a • x + b • y) ≤ vertexEnvelope θ p ε t
    rw [show f (a • x + b • y) = a * f x + b * f y from
      informationObjective_affine_weights θ p ε t a b x y]
    calc
      a * f x + b * f y ≤ a * vertexEnvelope θ p ε t +
          b * vertexEnvelope θ p ε t :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha)
          (mul_le_mul_of_nonneg_left hy hb)
      _ = vertexEnvelope θ p ε t := by rw [← add_mul, hab, one_mul]
  have hclosure : S ⊆ {x | f x ≤ vertexEnvelope θ p ε t} := by
    rw [← closure_convexHull_extremePoints hcompact hconvex]
    exact closure_minimal (convexHull_min hsub hconvexBound) hclosed
  exact le_antisymm (hsup ▸ hclosure ha) (hsup ▸ hvertex)

-- @node: Jstar_le_upperEnvelope
/-- Under the supplied quantities and conditions, the jstar le upper envelope assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the Jstar le upper Envelope](goal).

Under the stated assumptions, the Jstar le upper Envelope. -/
lemma Jstar_le_upperEnvelope (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 ≤ ε) (t : ℝ) :
    Jstar θ p ε ≤ upperEnvelope θ p ε t := by
  obtain ⟨β, hβ, hmax⟩ :=
    informationObjective_exists_maximizer θ p ε t hε
  have hH : upperEnvelope θ p ε t = informationObjective θ p ε β t := by
    unfold upperEnvelope
    apply IsGreatest.csSup_eq
    exact ⟨⟨β, hβ, rfl⟩, by
      rintro u ⟨γ, hγ, rfl⟩
      exact hmax γ hγ⟩
  unfold Jstar
  apply csSup_le
  · obtain ⟨α, hα⟩ := staircaseFeasible_nonempty ε
    exact ⟨_, α, hα, rfl⟩
  · rintro z ⟨α, hα, rfl⟩
    have hbdd : BddBelow {y : ℝ | ∃ u : ℝ,
        y = informationObjective θ p ε α u} := by
      refine ⟨0, ?_⟩
      rintro y ⟨u, rfl⟩
      exact informationObjective_nonneg_interior θ p ε hp hθ hε α hα u
    exact (csInf_le hbdd ⟨t, rfl⟩).trans (hH ▸ hmax α hα)

-- @node: upperEnvelope_exists_minimizer
/-- Under the supplied quantities and conditions, the upper envelope exists minimizer assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the upper Envelope exists minimizer](goal).

Under the stated assumptions, the upper Envelope exists minimizer. -/
lemma upperEnvelope_exists_minimizer (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) :
    ∃ t : ℝ, ∀ u : ℝ, upperEnvelope θ p ε t ≤ upperEnvelope θ p ε u := by
  obtain ⟨c, hc, hbound⟩ :=
    upperEnvelope_quadratic_lower_bound θ p ε hp hθ hε
  have hnonneg : 0 ≤ upperEnvelope θ p ε 0 := by
    have h := hbound 0
    simpa using h
  have hbounded : Bornology.IsBounded
      {t : ℝ | upperEnvelope θ p ε t ≤ upperEnvelope θ p ε 0} := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨Real.sqrt (upperEnvelope θ p ε 0 / c), ?_⟩
    intro t ht
    have hs : t ^ 2 ≤ upperEnvelope θ p ε 0 / c :=
      (le_div_iff₀ hc).2 (by rw [mul_comm]; exact (hbound t).trans ht)
    have hdiv : 0 ≤ upperEnvelope θ p ε 0 / c := div_nonneg hnonneg hc.le
    rw [Real.norm_eq_abs]
    nlinarith [Real.sq_sqrt hdiv, sq_abs t, abs_nonneg t,
      Real.sqrt_nonneg (upperEnvelope θ p ε 0 / c)]
  exact (upperEnvelope_continuous θ p ε hε.le).exists_forall_le_of_isBounded
    0 hbounded


end CausalSmith.Stat.LdpAteEfficiencySurface
