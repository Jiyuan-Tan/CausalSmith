module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Projection
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.IntermediateValue

/-!
Deterministic geometry of the external projection confidence set.

The results here use only the clipping, convex-hull, closure, and singleton-fallback
operations in `sievedTotalizedProjectionCI`. They do not impose or derive statistical coverage.
-/

public section

open Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

-- @node: projectionArmProb_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,e), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionArmProb_bounds {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (e : ScoreSpace ε) :
    ε ≤ armProb a e ∧ armProb a e ≤ 1 := by
  rcases e.property with ⟨he₁, he₂⟩
  rcases hOverlap with ⟨hε, hε'⟩
  cases a <;> simp only [armProb, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith

-- @node: projectionArmProb_diff_abs
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,a,e,e'), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionArmProb_diff_abs {ε : ℝ} (a : ArmSpace)
    (e e' : ScoreSpace ε) :
    |armProb a e - armProb a e'| = |(e : ℝ) - (e' : ℝ)| := by
  cases a
  · simp only [armProb, Bool.false_eq_true, ↓reduceIte]
    have h : (1 - (e : ℝ)) - (1 - (e' : ℝ)) =
        -((e : ℝ) - (e' : ℝ)) := by ring
    rw [h, abs_neg]
  · rfl

-- @node: projectionInverseArmProb_lipschitz
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,e,e'), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionInverseArmProb_lipschitz {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (e e' : ScoreSpace ε) :
    |(armProb a e)⁻¹ - (armProb a e')⁻¹| ≤
      (ε ^ 2)⁻¹ * |(e : ℝ) - (e' : ℝ)| := by
  have hp := (projectionArmProb_bounds hOverlap a e).1
  have hq := (projectionArmProb_bounds hOverlap a e').1
  have hε : 0 < ε := hOverlap.1
  have hpp : 0 < armProb a e := lt_of_lt_of_le hε hp
  have hqq : 0 < armProb a e' := lt_of_lt_of_le hε hq
  rw [inv_sub_inv (ne_of_gt hpp) (ne_of_gt hqq), abs_div,
    abs_mul, abs_of_pos hpp, abs_of_pos hqq]
  rw [abs_sub_comm, projectionArmProb_diff_abs]
  have hden : ε ^ 2 ≤ armProb a e * armProb a e' := by nlinarith
  have hnum : 0 ≤ |(e : ℝ) - (e' : ℝ)| := abs_nonneg _
  have hfrac : |(e : ℝ) - (e' : ℝ)| / (armProb a e * armProb a e') ≤
      |(e : ℝ) - (e' : ℝ)| / ε ^ 2 :=
    div_le_div_of_nonneg_left hnum (sq_pos_of_pos hε) hden
  calc
    |(e : ℝ) - (e' : ℝ)| / (armProb a e * armProb a e') ≤
        |(e : ℝ) - (e' : ℝ)| / ε ^ 2 := hfrac
    _ = (ε ^ 2)⁻¹ * |(e : ℝ) - (e' : ℝ)| := by ring

-- @node: projectionCost_bounds
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,a,e,e',y,y'), this result [establishes the stated mathematical conclusion](goal). -/
lemma projectionCost_bounds {ε : ℝ} (hOverlap : Overlap ε)
    (a : ArmSpace) (e e' : ScoreSpace ε) (y y' : OutcomeSpace) :
    0 ≤ (y : ℝ) / armProb a e ∧
    (y : ℝ) / armProb a e ≤ ε⁻¹ ∧
    |(y : ℝ) / armProb a e - (y' : ℝ) / armProb a e'| ≤
      ε⁻¹ * |(y : ℝ) - (y' : ℝ)| +
        (ε ^ 2)⁻¹ * |(e : ℝ) - (e' : ℝ)| := by
  have hp := (projectionArmProb_bounds hOverlap a e).1
  have hq := (projectionArmProb_bounds hOverlap a e').1
  have hε : 0 < ε := hOverlap.1
  have hpp : 0 < armProb a e := lt_of_lt_of_le hε hp
  have hqq : 0 < armProb a e' := lt_of_lt_of_le hε hq
  have hpinv : (armProb a e)⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hpp hε).2 hp
  have hdiff := projectionInverseArmProb_lipschitz hOverlap a e e'
  refine ⟨div_nonneg y.property.1 (le_of_lt hpp), ?_, ?_⟩
  · calc
      (y : ℝ) / armProb a e = (y : ℝ) * (armProb a e)⁻¹ := div_eq_mul_inv _ _
      _ ≤ 1 * (armProb a e)⁻¹ :=
        mul_le_mul_of_nonneg_right y.property.2 (le_of_lt (inv_pos.mpr hpp))
      _ ≤ ε⁻¹ := by simpa using hpinv
  · have hrewrite : (y : ℝ) / armProb a e - (y' : ℝ) / armProb a e' =
        ((y : ℝ) - y') * (armProb a e)⁻¹ +
          (y' : ℝ) * ((armProb a e)⁻¹ - (armProb a e')⁻¹) := by
      simp only [div_eq_mul_inv]
      ring
    rw [hrewrite]
    have hfirst : |((y : ℝ) - y') * (armProb a e)⁻¹| ≤
        ε⁻¹ * |(y : ℝ) - y'| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hpp)]
      calc
        |(y : ℝ) - y'| * (armProb a e)⁻¹ ≤
            |(y : ℝ) - y'| * ε⁻¹ :=
          mul_le_mul_of_nonneg_left hpinv (abs_nonneg _)
        _ = ε⁻¹ * |(y : ℝ) - y'| := mul_comm _ _
    have hsecond : |(y' : ℝ) * ((armProb a e)⁻¹ - (armProb a e')⁻¹)| ≤
        (ε ^ 2)⁻¹ * |(e : ℝ) - (e' : ℝ)| := by
      rw [abs_mul, abs_of_nonneg y'.property.1]
      calc
        (y' : ℝ) * |(armProb a e)⁻¹ - (armProb a e')⁻¹| ≤
            1 * |(armProb a e)⁻¹ - (armProb a e')⁻¹| :=
          mul_le_mul_of_nonneg_right y'.property.2 (abs_nonneg _)
        _ = |(armProb a e)⁻¹ - (armProb a e')⁻¹| := one_mul _
        _ ≤ (ε ^ 2)⁻¹ * |(e : ℝ) - (e' : ℝ)| := hdiff
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Given [the stated mathematical inputs and assumptions](hyp:S,lo,hi,hS), this result [establishes the stated mathematical conclusion](goal). -/
lemma closure_convexHull_subset_Icc {S : Set ℝ} {lo hi : ℝ}
    (hS : S ⊆ Icc lo hi) :
    closure (convexHull ℝ S) ⊆ Icc lo hi :=
  closure_minimal (convexHull_min hS (convex_Icc lo hi)) isClosed_Icc

/-- Given [the stated mathematical inputs and assumptions](hyp:S,lo,hi,hS), this result [establishes the stated mathematical conclusion](goal). -/
lemma clippedClosureConvexHull_subset_Icc {S : Set ℝ} {lo hi : ℝ}
    (hS : S ⊆ Icc lo hi) :
    Icc (-1 : ℝ) 1 ∩ closure (convexHull ℝ S) ⊆
      Icc (max (-1) lo) (min 1 hi) := by
  intro z hz
  have hzEnvelope := closure_convexHull_subset_Icc hS hz.2
  exact ⟨max_le hz.1.1 hzEnvelope.1, le_min hz.1.2 hzEnvelope.2⟩

-- @node: projection_strictBalls_closure_of_dense
/-- Given [the stated mathematical inputs and assumptions](hyp:X,D,hD,f,h,hf,hh,rn,rm,x,hfn,hhm), this result [establishes the stated mathematical conclusion](goal). -/
lemma projection_strictBalls_closure_of_dense {X : Type*} [TopologicalSpace X]
    {D : Set X} (hD : Dense D) {f h : X → ℝ}
    (hf : Continuous f) (hh : Continuous h) {rn rm : ℝ} {x : X}
    (hfn : f x < rn) (hhm : h x < rm) :
    x ∈ closure {y : X | y ∈ D ∧ f y ≤ rn ∧ h y ≤ rm} := by
  let U : Set X := {y | f y < rn ∧ h y < rm}
  have hU : IsOpen U := (isOpen_lt hf continuous_const).inter
    (isOpen_lt hh continuous_const)
  have hxU : x ∈ U := ⟨hfn, hhm⟩
  have hsub : U ∩ D ⊆ {y : X | y ∈ D ∧ f y ≤ rn ∧ h y ≤ rm} := by
    intro y hy
    exact ⟨hy.2, hy.1.1.le, hy.1.2.le⟩
  exact closure_mono hsub (hD.open_subset_closure_inter hU hxU)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_nonempty {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    (sievedTotalizedProjectionCI g α x).Nonempty := by
  classical
  rw [sievedTotalizedProjectionCI]
  split_ifs with h
  · exact h.2
  · exact singleton_nonempty 0

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_subset_Icc {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    sievedTotalizedProjectionCI g α x ⊆ Icc (-1 : ℝ) 1 := by
  classical
  rw [sievedTotalizedProjectionCI]
  split_ifs
  · exact inter_subset_left
  · simp

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma isClosed_externalProjectionCI {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    IsClosed (sievedTotalizedProjectionCI g α x) := by
  classical
  rw [sievedTotalizedProjectionCI]
  split_ifs
  · exact isClosed_Icc.inter isClosed_closure
  · exact isClosed_singleton

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma convex_externalProjectionCI {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    Convex ℝ (sievedTotalizedProjectionCI g α x) := by
  classical
  rw [sievedTotalizedProjectionCI]
  split_ifs
  · exact (convex_Icc (-1 : ℝ) 1).inter (convex_convexHull ℝ _).closure
  · exact convex_singleton 0

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_eq_Icc {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) :
    ∃ lo hi : ℝ,
      -1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1 ∧
        sievedTotalizedProjectionCI g α x = Icc lo hi := by
  let S := sievedTotalizedProjectionCI g α x
  have hne : S.Nonempty := externalProjectionCI_nonempty g α x
  have hclosed : IsClosed S := isClosed_externalProjectionCI g α x
  have hconvex : Convex ℝ S := convex_externalProjectionCI g α x
  have hclip : S ⊆ Icc (-1 : ℝ) 1 := externalProjectionCI_subset_Icc g α x
  have hbelow : BddBelow S := ⟨-1, fun z hz => (hclip hz).1⟩
  have habove : BddAbove S := ⟨1, fun z hz => (hclip hz).2⟩
  have hloMem : sInf S ∈ S := hclosed.csInf_mem hne hbelow
  have hhiMem : sSup S ∈ S := hclosed.csSup_mem hne habove
  have hconnected : IsConnected S := ⟨hne, hconvex.isPreconnected⟩
  refine ⟨sInf S, sSup S, (hclip hloMem).1, ?_, (hclip hhiMem).2, ?_⟩
  · exact csInf_le hbelow hhiMem
  · exact eq_Icc_csInf_csSup_of_connected_bdd_closed
      hconnected hbelow habove hclosed

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,L,U,δ,hδ,henv), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_excessLength_le_of_envelope
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) {L U δ : ℝ}
    (hδ : 0 ≤ δ)
    (henv : sievedTotalizedProjectionCI g α x ⊆ Set.Icc (L - δ) (U + δ)) :
    ∃ lo hi : ℝ, sievedTotalizedProjectionCI g α x = Set.Icc lo hi ∧
      max 0 ((hi - lo) - (U - L)) ≤ 2 * δ := by
  obtain ⟨lo, hi, _, hlohi, _, heq⟩ := externalProjectionCI_eq_Icc g α x
  have hlo : L - δ ≤ lo := (henv (heq ▸ Set.left_mem_Icc.mpr hlohi)).1
  have hhi : hi ≤ U + δ := (henv (heq ▸ Set.right_mem_Icc.mpr hlohi)).2
  refine ⟨lo, hi, heq, ?_⟩
  apply max_le (by linarith)
  linarith

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,L,U,hB,hC,hEach), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_subset_envelope_of_candidates
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) {L U : ℝ}
    (hB : (sievedProjectionCandidates g α x).Nonempty)
    (hC : (Set.Icc (-1 : ℝ) 1 ∩
      closure (convexHull ℝ
        (⋃ b ∈ sievedProjectionCandidates g α x,
          projectedATEInterval b.1 b.2))).Nonempty)
    (hEach : ∀ b ∈ sievedProjectionCandidates g α x,
      projectedATEInterval b.1 b.2 ⊆ Set.Icc L U) :
    sievedTotalizedProjectionCI g α x ⊆ Set.Icc (max (-1) L) (min 1 U) := by
  have hUnion :
      (⋃ b ∈ sievedProjectionCandidates g α x,
        projectedATEInterval b.1 b.2) ⊆ Set.Icc L U := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨b, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hb, hz⟩
    exact hEach b hb hz
  unfold sievedTotalizedProjectionCI
  dsimp
  rw [if_pos ⟨hB, hC⟩]
  exact clippedClosureConvexHull_subset_Icc hUnion

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,J,n,m,g,α,x,L,U,δ,hLU,hδ,hclip,hEach), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalProjectionCI_excessLength_le_of_candidate_envelopes
    {ε : ℝ} {J n m : ℕ}
    (g : ScoreSpace ε → LabelSpace J) (α : ℝ)
    (x : ExternalSample ε J n m) {L U δ : ℝ}
    (hLU : L ≤ U) (hδ : 0 ≤ δ)
    (hclip : (sievedProjectionCandidates g α x).Nonempty →
      (Set.Icc (-1 : ℝ) 1 ∩
      closure (convexHull ℝ
        (⋃ b ∈ sievedProjectionCandidates g α x,
          projectedATEInterval b.1 b.2))).Nonempty)
    (hEach : ∀ b ∈ sievedProjectionCandidates g α x,
      projectedATEInterval b.1 b.2 ⊆ Set.Icc (L - δ) (U + δ)) :
    ∃ lo hi : ℝ, sievedTotalizedProjectionCI g α x = Set.Icc lo hi ∧
      max 0 ((hi - lo) - (U - L)) ≤ 2 * δ := by
  classical
  by_cases hB : (sievedProjectionCandidates g α x).Nonempty
  · have henv := externalProjectionCI_subset_envelope_of_candidates
      g α x hB (hclip hB) hEach
    have henv' : sievedTotalizedProjectionCI g α x ⊆ Set.Icc (L - δ) (U + δ) := by
      intro z hz
      have hz' := henv hz
      exact ⟨le_trans (le_max_right _ _) hz'.1,
        le_trans hz'.2 (min_le_right _ _)⟩
    exact externalProjectionCI_excessLength_le_of_envelope g α x hδ henv'
  · have heq : sievedTotalizedProjectionCI g α x = {0} := by
      unfold sievedTotalizedProjectionCI
      simp [hB]
    refine ⟨0, 0, ?_, ?_⟩
    · simpa only [Set.Icc_self] using heq
    · simp only [sub_self, zero_sub]
      apply max_le (by linarith) (by linarith)

end
end CausalSmith.PartialID.UnlinkedPropensityAte
