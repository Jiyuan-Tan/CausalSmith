module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Rank
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Maximal
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Bias
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Measurability

/-! # Selected-mesh coefficient envelope -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.RandomDesignWeightedHoeffding
open scoped Classical

/-- A positive selected width comes from a feasible dyadic index. [For the stated inputs and conditions](hyp:d,n,m,β,ω,hpos), [the asserted conclusion holds](goal). -/
lemma selectedMesh_feasible_of_pos {d n : ℕ} (m : ℕ) (β : ℝ)
    (ω : Fin n → Obs d)
    (hpos : 0 < countSelectedMesh m β ω) :
    meshFeasible m β ω ((feasibleIndices m β ω).sup id) := by
  classical
  let F := feasibleIndices m β ω
  have hF : F.Nonempty := by
    by_contra h
    have hzero : countSelectedMesh m β ω = 0 := by
      simp [countSelectedMesh, F, h]
    linarith
  have hmem : F.sup id ∈ F := by
    rw [← Finset.sup'_eq_sup hF id, ← Finset.max'_eq_sup' F hF]
    exact Finset.max'_mem F hF
  exact (Finset.mem_filter.mp hmem).2

/-- On the nonempty feasible event, the selected width is the width of the
selected dyadic index. [For the stated inputs and conditions](hyp:d,n,m,β,ω,hpos), [the asserted conclusion holds](goal). -/
lemma selectedMesh_width_of_pos {d n : ℕ} (m : ℕ) (β : ℝ)
    (ω : Fin n → Obs d)
    (hpos : 0 < countSelectedMesh m β ω) :
    countSelectedMesh m β ω =
      meshWidth ((feasibleIndices m β ω).sup id) := by
  classical
  have hF : (feasibleIndices m β ω).Nonempty := by
    by_contra h
    have hzero : countSelectedMesh m β ω = 0 := by
      simp [countSelectedMesh, h]
    linarith
  simp [countSelectedMesh, hF]

/-- Intersect a measurable count event with an almost-sure conditional
coefficient assertion without increasing its failure probability. [For the stated inputs and conditions](hyp:Ω,Q,E,hE,ε,hbad,R,hR), [the asserted conclusion holds](goal). -/
lemma selectedMesh_measurable_event_intersect_ae
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (E : Set Ω) (hE : MeasurableSet E) (ε : ℝ)
    (hbad : Q.real Eᶜ ≤ ε) {R : Ω → Prop}
    (hR : ∀ᵐ ω ∂Q, R ω) :
    ∃ F : Set Ω, MeasurableSet F ∧ Q.real Fᶜ ≤ ε ∧
      ∀ ω ∈ F, ω ∈ E ∧ R ω := by
  obtain ⟨G, hGae, hGmeas, hGR⟩ := hR.exists_measurable_mem
  refine ⟨E ∩ G, hE.inter hGmeas, ?_, ?_⟩
  · have hGnull : Q Gᶜ = 0 := (ae_iff.mp hGae)
    have hGreal : Q.real Gᶜ = 0 := by simp [MeasureTheory.measureReal_def, hGnull]
    rw [Set.compl_inter]
    calc
      Q.real (Eᶜ ∪ Gᶜ) ≤ Q.real Eᶜ + Q.real Gᶜ :=
        measureReal_union_le _ _
      _ = Q.real Eᶜ := by rw [hGreal, add_zero]
      _ ≤ ε := hbad
  · intro ω hω
    exact ⟨hω.1, hGR ω hω.2⟩

/-- The selected count event and the actual conditional coefficient MGF hold
simultaneously on one measurable event with the count-event failure budget. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma selectedMesh_count_and_raw_mgf (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
        (hP : P ∈ ModelClass d β B L C c_f γ)
        (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q],
        IIDSampleLaw Q P →
        ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
          Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
          ∀ ω ∈ E,
            let m := polynomialDegree β
            let j := (feasibleIndices m β ω).sup id
            let h := countSelectedMesh m β ω
            0 < h ∧ h ≤ K * oracleMesh d n β γ ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)),
              (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ) ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              mgf (fun ξ => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
                (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
                Real.exp (B ^ 2 *
                  ((tensorCount d m : ℝ) *
                    ((tensorCount d m : ℝ)⁻¹ *
                      ((2 / templateLambda d m) *
                        Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
                    ((tensorCount d m : ℝ) *
                      min (meshWidth j ^ (2 * β))
                        (5 / ((n : ℝ) *
                          (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
                            (c_f * templateEta d m ^ d) ^ (γ / (γ - 1))) *
                          meshWidth j ^ effectiveDimension d γ *
                          (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1)))))) * t ^ 2 / 2)) ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              Integrable (fun ξ => Real.exp (t *
                (coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)))
                (condDistrib id sampleDesign Q (sampleDesign ω))) := by
  obtain ⟨K, hK, n₀, hcount⟩ :=
    selectedCountEvent_uniform d β B L C c_f γ_min γ_max
      hd hβ hB hL hC hcf hγmin hγrange
  refine ⟨K, hK, max 1 n₀, ?_⟩
  intro n hn γ hγ P _ hP Q _ hIID
  have hn₀ : n₀ ≤ n := (Nat.le_max_right _ _).trans hn
  obtain ⟨E, hE, hbad, hbounds⟩ := hcount n hn₀ γ hγ P hP Q hIID
  have hres : BoundedMeanSubGaussianResidual P B := by
    rcases hP with ⟨_, _, Pc, hPc, μ₁, e, hEq, hmodel⟩
    subst P
    exact hmodel.outcome
  have hmgf := modelClass_conditionalCoefficient_mgf_rank_bound
    P Q hIID hres
  have hint := conditionalCoefficient_integrable_exp P Q hIID hres
  obtain ⟨F, hF, hFbad, hFproperty⟩ :=
    selectedMesh_measurable_event_intersect_ae Q E hE
      ((n : ℝ) ^ (-2 : ℝ)) hbad (hmgf.and hint)
  refine ⟨F, hF, hFbad, ?_⟩
  intro ω hω
  obtain ⟨hωE, hωMGF, hωInt⟩ := hFproperty ω hω
  let m := polynomialDegree β
  let j := (feasibleIndices m β ω).sup id
  let h := countSelectedMesh m β ω
  obtain ⟨hh, hmesh, hcounts⟩ := hbounds ω hωE
  refine ⟨hh, hmesh, hcounts, ?_, ?_⟩
  · intro k α t
    have hnpos : 0 < n := by
      have : 1 ≤ n := (Nat.le_max_left _ _).trans hn
      omega
    have hfeasible : meshFeasible m β ω j :=
      selectedMesh_feasible_of_pos m β ω hh
    exact hωMGF m j hP k α hnpos hfeasible (hcounts k) t
  · intro k α t
    exact hωInt m j k α t

/-- Convert the actual conditional coefficient MGF to the ordered variance
proxy. The finite template factor and the uniform mass coefficient are
absorbed into one constant. [For the stated inputs and conditions](hyp:d,n,m,j,N,β,B,C,c_f,γ,κ,P,Q,ω,σ,hκ,hκle,hγ,hn,hrank,hraw), [the asserted conclusion holds](goal). -/
lemma selectedMesh_raw_coefficient_mgf_ordered
    {d n m j N : ℕ} (β B C c_f γ κ : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (ω : Fin n → Obs d)
    (σ : Fin N → Fin d → Fin (2 ^ j))
    (hκ : 0 < κ)
    (hκle : κ ≤ ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)))
    (hγ : 1 < γ) (hn : 0 < n)
    (hrank : ∀ k : Fin N, k.val + 1 ≤ cubeMassRank P m j (σ k))
    (hraw : ∀ (k : Fin N) (α : MonoIndex d m) (t : ℝ),
      mgf (fun ξ => coefHat m j ξ (σ k) α -
        conditionalCoefCentre Q m j ω (σ k) α)
        (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
      Real.exp (B ^ 2 *
        ((tensorCount d m : ℝ) *
          ((tensorCount d m : ℝ)⁻¹ *
            ((2 / templateLambda d m) *
              Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
          ((tensorCount d m : ℝ) *
            min (meshWidth j ^ (2 * β))
              (5 / ((n : ℝ) *
                (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
                  (c_f * templateEta d m ^ d) ^ (γ / (γ - 1))) *
                meshWidth j ^ effectiveDimension d γ *
                (cubeMassRank P m j (σ k) : ℝ) ^ (1 / (γ - 1)))))) * t ^ 2 / 2)) :
    ∀ (k : Fin N) (α : MonoIndex d m) (t : ℝ),
      mgf (fun ξ => coefHat m j ξ (σ k) α -
        conditionalCoefCentre Q m j ω (σ k) α)
        (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
      Real.exp ((B ^ 2 *
        ((tensorCount d m : ℝ) *
          ((tensorCount d m : ℝ)⁻¹ *
            ((2 / templateLambda d m) *
              Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
          (tensorCount d m : ℝ)) * max 1 (5 / κ)) *
        min (meshWidth j ^ (2 * β))
          ((n : ℝ)⁻¹ * meshWidth j ^ (-effectiveDimension d γ) *
            (k.val + 1 : ℝ) ^ (-(1 : ℝ) / (γ - 1))) * t ^ 2 / 2) := by
  intro k α t
  have hα : 0 < 1 / (γ - 1) := by positivity
  have hA : 0 ≤ B ^ 2 *
      ((tensorCount d m : ℝ) *
        ((tensorCount d m : ℝ)⁻¹ *
          ((2 / templateLambda d m) *
            Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
        (tensorCount d m : ℝ)) := by positivity
  have hx : 0 ≤ meshWidth j ^ (2 * β) := by
    apply Real.rpow_nonneg
    unfold meshWidth
    positivity
  have hr : 0 < (cubeMassRank P m j (σ k) : ℝ) := by
    exact_mod_cast cubeMassRank_pos P m j (σ k)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmgf := selectedMesh_uniform_ranked_mgf
    (condDistrib id sampleDesign Q (sampleDesign ω))
    (fun ξ => coefHat m j ξ (σ k) α -
      conditionalCoefCentre Q m j ω (σ k) α)
    (B ^ 2 *
      ((tensorCount d m : ℝ) *
        ((tensorCount d m : ℝ)⁻¹ *
          ((2 / templateLambda d m) *
            Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
        (tensorCount d m : ℝ)))
    (meshWidth j ^ (2 * β)) (n : ℝ) (meshWidth j)
    (cubeMassRank P m j (σ k) : ℝ) κ
    (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)))
    (effectiveDimension d γ) (1 / (γ - 1)) k.val t
    hA hx hn' (by unfold meshWidth; positivity) hr hκ hκle hα
    (by exact_mod_cast hrank k)
  have hconcl := hmgf (by simpa only [mul_assoc] using hraw k α t)
  simpa only [neg_div] using hconcl

/-- Normalize the conditional MGF at its own cube-mass rank before
reindexing cubes for the maximal inequality. [For the stated inputs and conditions](hyp:d,n,m,j,β,B,C,c_f,γ,κ,P,Q,ω,k,hκ,hκle,hγ,hn,hraw), [the asserted conclusion holds](goal). -/
lemma selectedMesh_raw_coefficient_mgf_rank
    {d n m j : ℕ} (β B C c_f γ κ : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hκ : 0 < κ)
    (hκle : κ ≤ ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)))
    (hγ : 1 < γ) (hn : 0 < n)
    (hraw : ∀ (α : MonoIndex d m) (t : ℝ),
      mgf (fun ξ => coefHat m j ξ k α -
        conditionalCoefCentre Q m j ω k α)
        (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
      Real.exp (B ^ 2 *
        ((tensorCount d m : ℝ) *
          ((tensorCount d m : ℝ)⁻¹ *
            ((2 / templateLambda d m) *
              Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
          ((tensorCount d m : ℝ) *
            min (meshWidth j ^ (2 * β))
              (5 / ((n : ℝ) *
                (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
                  (c_f * templateEta d m ^ d) ^ (γ / (γ - 1))) *
                meshWidth j ^ effectiveDimension d γ *
                (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1)))))) * t ^ 2 / 2)) :
    ∀ (α : MonoIndex d m) (t : ℝ),
      mgf (fun ξ => coefHat m j ξ k α -
        conditionalCoefCentre Q m j ω k α)
        (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
      Real.exp ((B ^ 2 *
        ((tensorCount d m : ℝ) *
          ((tensorCount d m : ℝ)⁻¹ *
            ((2 / templateLambda d m) *
              Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
          (tensorCount d m : ℝ)) * max 1 (5 / κ)) *
        min (meshWidth j ^ (2 * β))
          ((n : ℝ)⁻¹ * meshWidth j ^ (-effectiveDimension d γ) *
            (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) * t ^ 2 / 2) := by
  intro α t
  have hα : 0 < 1 / (γ - 1) := by positivity
  have hA : 0 ≤ B ^ 2 *
      ((tensorCount d m : ℝ) *
        ((tensorCount d m : ℝ)⁻¹ *
          ((2 / templateLambda d m) *
            Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
        (tensorCount d m : ℝ)) := by positivity
  have hx : 0 ≤ meshWidth j ^ (2 * β) := by
    apply Real.rpow_nonneg
    unfold meshWidth
    positivity
  have hr : 0 < (cubeMassRank P m j k : ℝ) := by
    exact_mod_cast cubeMassRank_pos P m j k
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hproxy := selectedMesh_uniform_ordered_proxy
    (B ^ 2 *
      ((tensorCount d m : ℝ) *
        ((tensorCount d m : ℝ)⁻¹ *
          ((2 / templateLambda d m) *
            Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
        (tensorCount d m : ℝ)))
    (meshWidth j ^ (2 * β)) (n : ℝ) (meshWidth j)
    (cubeMassRank P m j k : ℝ) κ
    (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)))
    (effectiveDimension d γ) (1 / (γ - 1))
    hA hx hn' (by unfold meshWidth; positivity) hr hκ hκle
  have hraw' := (hraw α t)
  have hraw'' : mgf (fun ξ => coefHat m j ξ k α -
      conditionalCoefCentre Q m j ω k α)
      (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
      Real.exp ((B ^ 2 *
        ((tensorCount d m : ℝ) *
          ((tensorCount d m : ℝ)⁻¹ *
            ((2 / templateLambda d m) *
              Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
          (tensorCount d m : ℝ))) *
        min (meshWidth j ^ (2 * β))
          (5 / ((n : ℝ) *
            (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
              (c_f * templateEta d m ^ d) ^ (γ / (γ - 1))) *
            meshWidth j ^ effectiveDimension d γ *
            (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1)))) * t ^ 2 / 2) := by
    simpa only [mul_assoc] using hraw'
  exact hraw''.trans (Real.exp_le_exp.mpr (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
    simpa only [neg_div] using hproxy))

/-- One event controls the selected counts and the actual conditional
coefficient MGF with a uniform rank proxy. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma selectedMesh_count_and_rank_mgf (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
        (hP : P ∈ ModelClass d β B L C c_f γ)
        (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q],
        IIDSampleLaw Q P →
        ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
          Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
          ∀ ω ∈ E,
            let m := polynomialDegree β
            let j := (feasibleIndices m β ω).sup id
            let h := countSelectedMesh m β ω
            0 < h ∧ h ≤ K * oracleMesh d n β γ ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)),
              (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ) ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              mgf (fun ξ => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
                (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
                Real.exp (K * min (h ^ (2 * β))
                  ((n : ℝ)⁻¹ * h ^ (-effectiveDimension d γ) *
                    (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) * t ^ 2 / 2)) ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              Integrable (fun ξ => Real.exp (t *
                (coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)))
                (condDistrib id sampleDesign Q (sampleDesign ω))) := by
  let m := polynomialDegree β
  let a := c_f * templateEta d m ^ d
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos hcf.1 (pow_pos (templateEta_pos d m) d)
  obtain ⟨κ, hκ, hκle⟩ := orderedMass_uniform_coefficient C a γ_min γ_max
    (lt_of_lt_of_le zero_lt_one hC) ha hγmin hγrange
  obtain ⟨Kcount, hKcountPos, n₀, hcountRaw⟩ :=
    selectedMesh_count_and_raw_mgf d β B L C c_f γ_min γ_max
      hd hβ hB hL hC hcf hγmin hγrange
  let A : ℝ := B ^ 2 *
    ((tensorCount d m : ℝ) *
      ((tensorCount d m : ℝ)⁻¹ *
        ((2 / templateLambda d m) *
          Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
      (tensorCount d m : ℝ))
  let K := max Kcount (A * max 1 (5 / κ)) + 1
  have hKcount : Kcount ≤ K := by
    dsimp [K]
    linarith [le_max_left Kcount (A * max 1 (5 / κ))]
  have hKbase : A * max 1 (5 / κ) ≤ K := by
    dsimp [K]
    linarith [le_max_right Kcount (A * max 1 (5 / κ))]
  have hK : 0 < K := lt_of_lt_of_le hKcountPos hKcount
  refine ⟨K, hK, max 1 n₀, ?_⟩
  intro n hn γ hγ P _ hP Q _ hIID
  obtain ⟨E, hE, hbad, hbounds⟩ :=
    hcountRaw n ((Nat.le_max_right _ _).trans hn) γ hγ P hP Q hIID
  refine ⟨E, hE, hbad, ?_⟩
  intro ω hω
  obtain ⟨hh, hmesh, hcounts, hraw, hint⟩ := hbounds ω hω
  let j := (feasibleIndices m β ω).sup id
  have hwidth : countSelectedMesh m β ω = meshWidth j :=
    selectedMesh_width_of_pos m β ω hh
  have horacle : 0 ≤ oracleMesh d n β γ := by
    unfold oracleMesh
    positivity
  refine ⟨hh, hmesh.trans (mul_le_mul_of_nonneg_right hKcount horacle),
    hcounts, ?_, hint⟩
  intro k α t
  have hγIcc : γ ∈ Set.Icc γ_min γ_max := by
    simpa only [adaptationRange] using hγ
  have hγgt : 1 < γ := hγmin.trans_le hγIcc.1
  have hnpos : 0 < n := by
    have : 1 ≤ n := (Nat.le_max_left _ _).trans hn
    omega
  have hκbound : κ ≤ ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) := by
    simpa only [a] using hκle γ hγIcc
  have hrank := selectedMesh_raw_coefficient_mgf_rank β B C c_f γ κ
    P Q ω k hκ hκbound hγgt hnpos (hraw k)
  rw [hwidth]
  apply (hrank α t).trans
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
  have hmin : 0 ≤ min (meshWidth j ^ (2 * β))
      ((n : ℝ)⁻¹ * meshWidth j ^ (-effectiveDimension d γ) *
        (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) := by
    have hwpos : 0 < meshWidth j := by unfold meshWidth; positivity
    have hrpos : 0 < (cubeMassRank P m j k : ℝ) := by
      exact_mod_cast cubeMassRank_pos P m j k
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    exact le_min (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right hKbase hmin

/- A uniform vector maximal bound in the variance normalization supplied by
the selected count event. -/

/-- [For the stated inputs and conditions](hyp:αmin,αmax,hαmin,hαmax,K,hK), [the asserted conclusion holds](goal). -/

lemma selectedMesh_ranked_vector_maximal
    (αmin αmax : ℝ) (hαmin : 0 < αmin) (hαmax : αmin ≤ αmax)
    (K : ℝ) (hK : 0 < K) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (α : ℝ), α ∈ Set.Icc αmin αmax →
      ∀ {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (N : ℕ) [Nonempty (Fin N)]
        (σ : Fin N ≃ κ) (Z : κ → Ω → ι → ℝ)
        (x y a b : ℝ), 0 < a → 0 < b →
        a ^ 2 = K * x → b ^ 2 = K * y →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          Integrable (fun ω => Real.exp (t * Z (σ k) ω i)) μ) →
        (∀ k : Fin N, ∀ i : ι, ∀ t : ℝ,
          mgf (fun ω => Z (σ k) ω i) μ t ≤ Real.exp
            (K * min x (y * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2)) →
        (∫ ω, sSup ((fun k : κ => ‖Z k ω‖) '' Set.univ) ∂μ) ≤
          (Fintype.card ι : ℝ) * M * a *
            Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨M, hM, hmax⟩ :=
    orderedSubGaussianMaximal_vector_equiv_uniform_of_exp
      αmin αmax hαmin hαmax
  refine ⟨M, hM, ?_⟩
  intro α hα Ω κ ι _ _ μ _ N _ σ Z x y a b ha hb ha2 hb2 hexp hmgf
  apply hmax α hα μ N σ Z a b ha hb hexp
  intro k i t
  convert hmgf k i t using 1
  congr 1
  rw [ha2, hb2, mul_assoc,
    ← mul_min_of_nonneg x (y * (k.val + 1 : ℝ) ^ (-α)) hK.le]

/- The exponent in the ordered maximal inequality converts the stochastic
scale into the selected-to-oracle mesh ratio. -/
/-- [For the stated inputs and conditions](hyp:d,n,β,γ,h,α,hn,hden,hh,hα), [the asserted conclusion holds](goal). -/
lemma selectedMesh_maximal_oracle_log_ratio (d n : ℕ) (β γ h α : ℝ)
    (hn : 0 < n) (hden : 0 < 2 * β + effectiveDimension d γ)
    (hh : 0 < h) (hα : 0 < α) :
    1 + max 0 (Real.log
      ((((n : ℝ) ^ (-(1 : ℝ) / 2) *
          h ^ (-(effectiveDimension d γ) / 2)) / h ^ β) ^ (2 / α))) ≤
      max 1 ((β + effectiveDimension d γ / 2) * (2 / α)) *
        (1 + max 0 (Real.log (oracleMesh d n β γ / h))) := by
  have ho : 0 < oracleMesh d n β γ := by
    unfold oracleMesh
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  rw [selectedMesh_stochastic_bias_ratio d n β γ h hn hden hh]
  rw [← Real.rpow_mul (div_pos ho hh).le]
  exact selectedMesh_maximal_log_scale
    (oracleMesh d n β γ) h
    ((β + effectiveDimension d γ / 2) * (2 / α)) ho hh
    (by have : 0 ≤ β + effectiveDimension d γ / 2 := by linarith
        positivity)

/-- The logarithmic exponent has a fixed upper bound over the adaptation
range; its apparent reciprocal dependence on the overlap exponent cancels. [For the stated inputs and conditions](hyp:d,β,γ,γmax,hβ,hγ,hmax), [the asserted conclusion holds](goal). -/
lemma selectedMesh_maximal_exponent_uniform (d : ℕ) (β γ γmax : ℝ)
    (hβ : 0 < β) (hγ : 1 < γ) (hmax : γ ≤ γmax) :
    0 ≤ (β + effectiveDimension d γ / 2) * (2 / (1 / (γ - 1))) ∧
      (β + effectiveDimension d γ / 2) * (2 / (1 / (γ - 1))) ≤
        2 * β * (γmax - 1) + (d : ℝ) * γmax := by
  have hγden : γ - 1 ≠ 0 := ne_of_gt (by linarith : 0 < γ - 1)
  have hform :
      (β + effectiveDimension d γ / 2) * (2 / (1 / (γ - 1))) =
        2 * β * (γ - 1) + (d : ℝ) * γ := by
    unfold effectiveDimension
    field_simp
  rw [hform]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  constructor
  · positivity
  · nlinarith

/-- The ordered maximal exponent stays in a fixed positive interval. [For the stated inputs and conditions](hyp:γmin,γmax,γ,hmin,hrange,hγ), [the asserted conclusion holds](goal). -/
lemma selectedMesh_alpha_in_compact_range (γmin γmax γ : ℝ)
    (hmin : 1 < γmin) (hrange : γmin ≤ γmax)
    (hγ : γ ∈ Set.Icc γmin γmax) :
    1 / (γmax - 1) ≤ 1 / (γ - 1) ∧
      1 / (γ - 1) ≤ 1 / (γmin - 1) := by
  have h₁ : 0 < γmin - 1 := by linarith
  have h₂ : 0 < γ - 1 := by linarith [hγ.1]
  have h₃ : 0 < γmax - 1 := by linarith
  constructor
  · exact one_div_le_one_div_of_le h₂ (by linarith [hγ.2])
  · exact one_div_le_one_div_of_le h₁ (by linarith [hγ.1])

/-- Apply the vector maximal inequality to cubes whose coefficient proxy is
expressed through their mass rank. [For the stated inputs and conditions](hyp:αmin,αmax,K,hαmin,hαmax,hK), [the asserted conclusion holds](goal). -/
lemma selectedMesh_cube_rank_vector_maximal
    (αmin αmax K : ℝ)
    (hαmin : 0 < αmin) (hαmax : αmin ≤ αmax)
    (hK : 0 < K) :
    ∃ M : ℝ, 0 < M ∧
      ∀ {d : ℕ} (P : Measure (Obs d)) [IsProbabilityMeasure P]
        (m j : ℕ) (α x y a b : ℝ),
      α ∈ Set.Icc αmin αmax → 0 ≤ y → 0 < a → 0 < b →
      a ^ 2 = K * x → b ^ 2 = K * y →
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Z : (Fin d → Fin (2 ^ j)) → Ω → ι → ℝ),
      (∀ k i t, Integrable (fun ω => Real.exp (t * Z k ω i)) μ) →
      (∀ k i t, mgf (fun ω => Z k ω i) μ t ≤
        Real.exp (K * min x
          (y * (cubeMassRank P m j k : ℝ) ^ (-α)) * t ^ 2 / 2)) →
      (∫ ω, sSup ((fun k : Fin d → Fin (2 ^ j) =>
          ‖Z k ω‖) '' Set.univ) ∂μ) ≤
        (Fintype.card ι : ℝ) * M * a *
          Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α)))) := by
  obtain ⟨M, hM, hmax⟩ :=
    selectedMesh_ranked_vector_maximal αmin αmax hαmin hαmax K hK
  refine ⟨M, hM, ?_⟩
  intro d P _ m j α x y a b hα hy ha hb ha2 hb2 Ω ι _ _ μ _ Z hexp hmgf
  obtain ⟨σ, -, hrank⟩ := cubeMass_ordered_equiv P m j
  apply hmax α hα μ _ σ Z x y a b ha hb ha2 hb2
  · intro k i t
    exact hexp (σ k) i t
  · intro k i t
    calc
      mgf (fun ω => Z (σ k) ω i) μ t ≤
          Real.exp (K * min x
            (y * (cubeMassRank P m j (σ k) : ℝ) ^ (-α)) * t ^ 2 / 2) :=
        hmgf (σ k) i t
      _ ≤ Real.exp (K * min x
            (y * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
        apply mul_le_mul_of_nonneg_left _ hK.le
        exact selectedMesh_rank_proxy_to_ordered x y α
          (cubeMassRank P m j (σ k) : ℝ) k.val hy
          (lt_of_lt_of_le hαmin hα.1) (by exact_mod_cast hrank k)

/-- The selected mesh obeys the count event, ordered conditional coefficient
variance proxies, and [a logarithm-free expected coefficient envelope](goal)
under [the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange). -/
-- @node: lem:selected-mesh
lemma selectedMesh_envelope (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K K' : ℝ, 0 < K ∧ 0 < K' ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
        (hP : P ∈ ModelClass d β B L C c_f γ)
        (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q],
        IIDSampleLaw Q P →
        ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
          Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
          (∀ ω ∈ E,
            let m := polynomialDegree β
            let j := (feasibleIndices m β ω).sup id
            let h := countSelectedMesh m β ω
            0 < h ∧ h ≤ K * oracleMesh d n β γ ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)),
              (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ) ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              mgf (fun ξ => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
                (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
                Real.exp (K * min (h ^ (2 * β))
                  ((n : ℝ)⁻¹ * h ^ (-effectiveDimension d γ) *
                    (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) * t ^ 2 / 2)) ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              Integrable (fun ξ => Real.exp (t *
                (coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)))
                (condDistrib id sampleDesign Q (sampleDesign ω))) ∧
            Integrable (fun ξ => sSup ((fun k : Fin d → Fin (2 ^ j) =>
                ‖fun α : MonoIndex d m => coefHat m j ξ k α -
                    conditionalCoefCentre Q m j ω k α‖) '' Set.univ))
              (condDistrib id sampleDesign Q (sampleDesign ω)) ∧
            (∫ ξ, sSup ((fun k : Fin d → Fin (2 ^ j) =>
                ‖fun α : MonoIndex d m => coefHat m j ξ k α -
                    conditionalCoefCentre Q m j ω k α‖) '' Set.univ)
                  ∂condDistrib id sampleDesign Q (sampleDesign ω)) ≤
              K * h ^ β * Real.sqrt
                (1 + max 0 (Real.log (oracleMesh d n β γ / h))) ∧
            K * h ^ β * Real.sqrt
                (1 + max 0 (Real.log (oracleMesh d n β γ / h))) ≤
              K' * oracleRate d n β γ) ∧
        (∀ (α : ℝ), 0 < α → ∃ Kα : ℝ, 0 < Kα ∧
          ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (N : ℕ) (Z : Fin N → Ω → ℝ)
          (a b : ℝ), 0 < a → 0 < b →
          (∀ k : Fin N, ∀ t : ℝ,
            Integrable (fun ξ => Real.exp (t * Z k ξ)) μ) →
          (∀ k : Fin N, ∀ t : ℝ,
            mgf (Z k) μ t ≤ Real.exp
              (min (a ^ 2) (b ^ 2 * (k.val + 1 : ℝ) ^ (-α)) * t ^ 2 / 2)) →
          ∫ ξ, sSup ((fun k : Fin N => |Z k ξ|) '' Set.univ) ∂μ ≤
            Kα * a * Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / α))))) := by
  have hOutcomeFromModel :
      ∀ (γ : ℝ) (P : Measure (Obs d)) [IsProbabilityMeasure P],
        P ∈ ModelClass d β B L C c_f γ →
          BoundedMeanSubGaussianResidual P B := by
    intro γ P _ hP
    rcases hP with ⟨_, _, Pc, hPc, μ₁, e, hEq, hmodel⟩
    subst P
    exact hmodel.outcome
  have hSelected :
      ∃ K K' : ℝ, 0 < K ∧ 0 < K' ∧ ∃ n₀ : ℕ,
        ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
        ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
          (hP : P ∈ ModelClass d β B L C c_f γ)
          (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q],
          IIDSampleLaw Q P →
          ∃ E : Set (Fin n → Obs d), MeasurableSet E ∧
            Q.real Eᶜ ≤ (n : ℝ) ^ (-2 : ℝ) ∧
            (∀ ω ∈ E,
              let m := polynomialDegree β
              let j := (feasibleIndices m β ω).sup id
              let h := countSelectedMesh m β ω
              0 < h ∧ h ≤ K * oracleMesh d n β γ ∧
              (∀ (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)),
                (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ) ∧
              (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
                mgf (fun ξ => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
                  (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
                  Real.exp (K * min (h ^ (2 * β))
                    ((n : ℝ)⁻¹ * h ^ (-effectiveDimension d γ) *
                      (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) * t ^ 2 / 2)) ∧
              (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
                Integrable (fun ξ => Real.exp (t *
                  (coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)))
                  (condDistrib id sampleDesign Q (sampleDesign ω))) ∧
              Integrable (fun ξ => sSup ((fun k : Fin d → Fin (2 ^ j) =>
                  ‖fun α : MonoIndex d m => coefHat m j ξ k α -
                      conditionalCoefCentre Q m j ω k α‖) '' Set.univ))
                (condDistrib id sampleDesign Q (sampleDesign ω)) ∧
              (∫ ξ, sSup ((fun k : Fin d → Fin (2 ^ j) =>
                  ‖fun α : MonoIndex d m => coefHat m j ξ k α -
                    conditionalCoefCentre Q m j ω k α‖) '' Set.univ)
                    ∂condDistrib id sampleDesign Q (sampleDesign ω)) ≤
                K * h ^ β * Real.sqrt
                  (1 + max 0 (Real.log (oracleMesh d n β γ / h))) ∧
              K * h ^ β * Real.sqrt
                (1 + max 0 (Real.log (oracleMesh d n β γ / h))) ≤
                K' * oracleRate d n β γ) := by
    obtain ⟨Kcount, hKcount, ncount, hcountRank⟩ :=
      selectedMesh_count_and_rank_mgf d β B L C c_f γ_min γ_max
        hd hβ hB hL hC hcf hγmin hγrange
    let αmin := 1 / (γ_max - 1)
    let αmax := 1 / (γ_min - 1)
    have hαmin : 0 < αmin := by
      have : 0 < γ_max - 1 := by linarith
      dsimp [αmin]
      positivity
    have hαmax : αmin ≤ αmax :=
      (selectedMesh_alpha_in_compact_range γ_min γ_max γ_min
        hγmin hγrange.le ⟨le_refl _, hγrange.le⟩).1
    obtain ⟨M, hM, hmax⟩ :=
      selectedMesh_cube_rank_vector_maximal αmin αmax Kcount
        hαmin hαmax hKcount
    let Eexp : ℝ := max 1 (2 * β * (γ_max - 1) + (d : ℝ) * γ_max)
    have hEexp : 0 < Eexp := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    let p : ℝ := Fintype.card (MonoIndex d (polynomialDegree β))
    let K : ℝ := max Kcount (p * M * Real.sqrt Kcount * Real.sqrt Eexp) + 1
    have hKcountLe : Kcount ≤ K := by dsimp [K]; linarith [le_max_left Kcount (p * M * Real.sqrt Kcount * Real.sqrt Eexp)]
    have hKcoef : p * M * Real.sqrt Kcount * Real.sqrt Eexp ≤ K := by
      dsimp [K]
      linarith [le_max_right Kcount (p * M * Real.sqrt Kcount * Real.sqrt Eexp)]
    have hK : 0 < K := lt_of_lt_of_le hKcount hKcountLe
    let K' := K * max 1 (K ^ β)
    have hK' : 0 < K' := mul_pos hK (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    refine ⟨K, K', hK, hK', max 1 ncount, ?_⟩
    intro n hn γ hγ P _ hP Q _ hIID
    obtain ⟨E, hE, hbad, hbounds⟩ :=
      hcountRank n ((Nat.le_max_right _ _).trans hn) γ hγ P hP Q hIID
    refine ⟨E, hE, hbad, ?_⟩
    intro ω hω
    obtain ⟨hh, hmesh, hcounts, hmgf, hexp⟩ := hbounds ω hω
    let m := polynomialDegree β
    let j := (feasibleIndices m β ω).sup id
    let h := countSelectedMesh m β ω
    have hwidth : h = meshWidth j := selectedMesh_width_of_pos m β ω hh
    have hγIcc : γ ∈ Set.Icc γ_min γ_max := by
      simpa only [adaptationRange] using hγ
    have hγgt : 1 < γ := hγmin.trans_le hγIcc.1
    have hnpos : 0 < n := by
      have : 1 ≤ n := (Nat.le_max_left _ _).trans hn
      omega
    have hγpos : 0 < γ - 1 := by linarith
    have hD : 0 < effectiveDimension d γ := by
      unfold effectiveDimension
      have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
      positivity
    have hden : 0 < 2 * β + effectiveDimension d γ := by positivity
    have hα : 1 / (γ - 1) ∈ Set.Icc αmin αmax :=
      selectedMesh_alpha_in_compact_range γ_min γ_max γ
        hγmin hγrange.le hγIcc
    let a : ℝ := Real.sqrt Kcount * h ^ β
    let b : ℝ := Real.sqrt Kcount * (n : ℝ) ^ (-(1 : ℝ) / 2) *
      h ^ (-(effectiveDimension d γ) / 2)
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by
      dsimp [b]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
      positivity
    have ha2 : a ^ 2 = Kcount * h ^ (2 * β) := by
      have hpow : (h ^ β) ^ 2 = h ^ (2 * β) := by
        rw [← Real.rpow_natCast (x := h ^ β) (n := 2)]
        rw [← Real.rpow_mul hh.le]
        congr 1
        ring
      simp only [a, mul_pow, Real.sq_sqrt hKcount.le, hpow]
    have hb2 : b ^ 2 = Kcount * ((n : ℝ)⁻¹ *
        h ^ (-effectiveDimension d γ)) := by
      have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hnpos.le
      have hnpow : ((n : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (n : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast (x := (n : ℝ) ^ (-(1 : ℝ) / 2)) (n := 2)]
        rw [← Real.rpow_mul hn']
        norm_num
        exact Real.rpow_neg_one (n : ℝ)
      have hhp : (h ^ (-(effectiveDimension d γ) / 2)) ^ 2 =
          h ^ (-effectiveDimension d γ) := by
        rw [← Real.rpow_natCast (x := h ^ (-(effectiveDimension d γ) / 2)) (n := 2)]
        rw [← Real.rpow_mul hh.le]
        congr 1
        ring
      simp only [b, mul_pow, Real.sq_sqrt hKcount.le, hnpow, hhp]
      ring
    have hvec := hmax P m j (1 / (γ - 1))
      (h ^ (2 * β)) ((n : ℝ)⁻¹ * h ^ (-effectiveDimension d γ))
      a b hα (by positivity) ha hb ha2 hb2
      (condDistrib id sampleDesign Q (sampleDesign ω))
      (fun k ξ α => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
      hexp (by simpa only [neg_div] using hmgf)
    have hintMax := selectedMesh_integrable_vector_max_of_exp_moments
      (condDistrib id sampleDesign Q (sampleDesign ω))
      (fun k ξ α => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
      hexp
    have hratio : b / a =
        (((n : ℝ) ^ (-(1 : ℝ) / 2) *
          h ^ (-(effectiveDimension d γ) / 2)) / h ^ β) := by
      dsimp [a, b]
      have hsqrt : Real.sqrt Kcount ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hKcount)
      have hpow : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
      field_simp
    have hlogRatio := selectedMesh_maximal_oracle_log_ratio
      d n β γ h (1 / (γ - 1)) hnpos hden hh (by positivity)
    have hexponent := selectedMesh_maximal_exponent_uniform
      d β γ γ_max (by linarith) hγgt hγIcc.2
    have hlog :
        Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / (1 / (γ - 1)))))) ≤
          Real.sqrt Eexp *
            Real.sqrt (1 + max 0 (Real.log (oracleMesh d n β γ / h))) := by
      rw [hratio]
      have hH : 0 ≤ 1 + max 0 (Real.log (oracleMesh d n β γ / h)) := by positivity
      have hfactor : max 1 ((β + effectiveDimension d γ / 2) *
          (2 / (1 / (γ - 1)))) ≤ Eexp := by
        dsimp [Eexp]
        exact max_le_max_left _ hexponent.2
      have hbound := hlogRatio.trans (mul_le_mul_of_nonneg_right hfactor hH)
      calc
        _ ≤ Real.sqrt (Eexp * (1 + max 0
              (Real.log (oracleMesh d n β γ / h)))) := Real.sqrt_le_sqrt hbound
        _ = _ := by rw [Real.sqrt_mul hEexp.le]
    have hstoch :
        (∫ ξ, sSup ((fun k : Fin d → Fin (2 ^ j) =>
            ‖fun α : MonoIndex d m => coefHat m j ξ k α -
              conditionalCoefCentre Q m j ω k α‖) '' Set.univ)
            ∂condDistrib id sampleDesign Q (sampleDesign ω)) ≤
          K * h ^ β * Real.sqrt
            (1 + max 0 (Real.log (oracleMesh d n β γ / h))) := by
      have hnonneg : 0 ≤ h ^ β * Real.sqrt
          (1 + max 0 (Real.log (oracleMesh d n β γ / h))) := by positivity
      calc
        _ ≤ p * M * a * Real.sqrt
            (1 + max 0 (Real.log ((b / a) ^ (2 / (1 / (γ - 1)))))) := hvec
        _ ≤ p * M * a * (Real.sqrt Eexp * Real.sqrt
            (1 + max 0 (Real.log (oracleMesh d n β γ / h)))) := by
          gcongr
        _ = (p * M * Real.sqrt Kcount * Real.sqrt Eexp) *
            (h ^ β * Real.sqrt
              (1 + max 0 (Real.log (oracleMesh d n β γ / h)))) := by
          dsimp [a]; ring
        _ ≤ K * (h ^ β * Real.sqrt
            (1 + max 0 (Real.log (oracleMesh d n β γ / h)))) :=
          mul_le_mul_of_nonneg_right hKcoef hnonneg
        _ = _ := by ring
    have hdet := selectedMesh_oracle_rate_log_bound
      d n β γ h K hnpos (by linarith) hh
      (hmesh.trans (mul_le_mul_of_nonneg_right hKcountLe
        (by unfold oracleMesh; positivity)))
    refine ⟨hh, hmesh.trans (mul_le_mul_of_nonneg_right hKcountLe
      (by unfold oracleMesh; positivity)), hcounts, ?_, hexp, hintMax.1, hstoch, ?_⟩
    · intro k α t
      exact (hmgf k α t).trans (Real.exp_le_exp.mpr (by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
        have hx : 0 ≤ min (h ^ (2 * β))
            ((n : ℝ)⁻¹ * h ^ (-effectiveDimension d γ) *
              (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) := by
          have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
          have hr : 0 < (cubeMassRank P m j k : ℝ) := by
            exact_mod_cast cubeMassRank_pos P m j k
          exact le_min (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hKcountLe hx))
    · simpa only [K', mul_assoc] using
        (mul_le_mul_of_nonneg_left hdet hK.le)
  obtain ⟨K, K', hK, hK', n₀, hselected⟩ := hSelected
  refine ⟨K, K', hK, hK', n₀, ?_⟩
  intro n hn γ hγ P _ hP Q _ hIID
  obtain ⟨E, hE, hbad, hbounds⟩ := hselected n hn γ hγ P hP Q hIID
  refine ⟨E, hE, hbad, hbounds, ?_⟩
  intro α hα
  exact Causalean.Mathlib.Probability.SubGaussian.orderedSubGaussianMaximal α hα

/-- A design-saturated event has conditional probability one on the entire
conditional sample fibre whenever the conditioning sample belongs to it. [For the stated inputs and conditions](hyp:d,n,Q,E,hE,hsat), [the asserted conclusion holds](goal). -/
lemma countDesignSaturated_condDistrib_one {d n : ℕ}
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (E : Set (Fin n → Obs d)) (hE : MeasurableSet E)
    (hsat : CountDesignSaturated E) :
    ∀ᵐ ω ∂Q, ω ∈ E →
      condDistrib id sampleDesign Q (sampleDesign ω) E = 1 := by
  filter_upwards [sampleDesign_condDistrib_fibre Q] with ω hfibre
  intro hω
  rw [← mem_ae_iff_prob_eq_one hE]
  filter_upwards [hfibre] with ξ hξ
  exact (hsat ω ξ hξ).mp hω

/-- [For the stated inputs and conditions](hyp:d,n,β,γ,hn,hβ,hγ), [the asserted conclusion holds](goal). -/

lemma inverseSquare_le_oracleRate (d n : ℕ) (β γ : ℝ)
    (hn : 1 ≤ n) (hβ : 0 < β) (hγ : 1 < γ) :
    (n : ℝ) ^ (-2 : ℝ) ≤ oracleRate d n β γ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 ≤ effectiveDimension d γ := by
    unfold effectiveDimension
    positivity
  have hden : 0 < 2 * β + effectiveDimension d γ := by positivity
  have hexp : (-2 : ℝ) ≤ (-(1 : ℝ) / (2 * β + effectiveDimension d γ)) * β := by
    have hfrac : β / (2 * β + effectiveDimension d γ) ≤ 1 := by
      apply (div_le_one hden).2
      linarith
    rw [show (-(1 : ℝ) / (2 * β + effectiveDimension d γ)) * β =
      -(β / (2 * β + effectiveDimension d γ)) by ring]
    linarith
  unfold oracleRate oracleMesh
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  exact Real.rpow_le_rpow_of_exponent_le hn' hexp

/-- The explicit design-saturated count event supports the ranked coefficient
MGF bounds almost everywhere. Auxiliary fibre facts remain in the ambient
almost-everywhere filter rather than being added to the event. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma selectedMesh_saturated_rank_mgf
    (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
        (hP : P ∈ ModelClass d β B L C c_f γ)
        (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q],
        IIDSampleLaw Q P →
        ∃ E, SaturatedSelectedCountEvent β K γ P Q E ∧
          ∀ᵐ ω ∂Q, ω ∈ E →
            let m := polynomialDegree β
            let j := (feasibleIndices m β ω).sup id
            let h := countSelectedMesh m β ω
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              mgf (fun ξ => coefHat m j ξ k α -
                conditionalCoefCentre Q m j ω k α)
                (condDistrib id sampleDesign Q (sampleDesign ω)) t ≤
                Real.exp (K * min (h ^ (2 * β))
                  ((n : ℝ)⁻¹ * h ^ (-effectiveDimension d γ) *
                    (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) *
                    t ^ 2 / 2)) ∧
            (∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m) (t : ℝ),
              Integrable (fun ξ => Real.exp (t *
                (coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)))
                (condDistrib id sampleDesign Q (sampleDesign ω))) := by
  let m := polynomialDegree β
  let a := c_f * templateEta d m ^ d
  have ha : 0 < a := by
    dsimp [a, m]
    exact mul_pos hcf.1 (pow_pos (templateEta_pos d (polynomialDegree β)) d)
  obtain ⟨κ, hκ, hκle⟩ := orderedMass_uniform_coefficient C a γ_min γ_max
    (lt_of_lt_of_le zero_lt_one hC) ha hγmin hγrange
  obtain ⟨Kcount, hKcount, n₀, hcount⟩ :=
    selectedCountEvent_uniform_design_saturated d β B L C c_f γ_min γ_max
      hd hβ hB hL hC hcf hγmin hγrange
  let A : ℝ := B ^ 2 *
    ((tensorCount d m : ℝ) *
      ((tensorCount d m : ℝ)⁻¹ *
        ((2 / templateLambda d m) *
          Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
      (tensorCount d m : ℝ))
  let K := max Kcount (A * max 1 (5 / κ)) + 1
  have hKcountLe : Kcount ≤ K := by
    dsimp [K]
    linarith [le_max_left Kcount (A * max 1 (5 / κ))]
  have hKbase : A * max 1 (5 / κ) ≤ K := by
    dsimp [K]
    linarith [le_max_right Kcount (A * max 1 (5 / κ))]
  have hK : 0 < K := lt_of_lt_of_le hKcount hKcountLe
  refine ⟨K, hK, max 1 n₀, ?_⟩
  intro n hn γ hγ P _ hP Q _ hIID
  obtain ⟨E, hEmeas, hEbad, hEbounds, hEsat⟩ :=
    hcount n ((Nat.le_max_right _ _).trans hn) γ hγ P hP Q hIID
  have horacle : 0 ≤ oracleMesh d n β γ := by
    unfold oracleMesh
    positivity
  have hEbounds' : ∀ ω ∈ E,
      0 < countSelectedMesh (polynomialDegree β) β ω ∧
      countSelectedMesh (polynomialDegree β) β ω ≤
        K * oracleMesh d n β γ ∧
      ∀ (k : Fin d → Fin
          (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
        (ℓ : Fin d → Fin (polynomialDegree β + 1)),
        (n : ℝ) * microcellMass P (polynomialDegree β)
          ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
          treatedCount (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ := by
    intro ω hω
    obtain ⟨hh, hmesh, hcounts⟩ := hEbounds ω hω
    exact ⟨hh, hmesh.trans (mul_le_mul_of_nonneg_right hKcountLe horacle), hcounts⟩
  refine ⟨E, ⟨hEmeas, hEbad, hEbounds', hEsat⟩, ?_⟩
  have hres : BoundedMeanSubGaussianResidual P B := by
    rcases hP with ⟨_, _, Pc, hPc, μ₁, e, hEq, hmodel⟩
    subst P
    exact hmodel.outcome
  filter_upwards [modelClass_conditionalCoefficient_mgf_rank_bound P Q hIID hres,
    conditionalCoefficient_integrable_exp P Q hIID hres] with ω hraw hint
  intro hω
  obtain ⟨hh, _hmesh, hcounts⟩ := hEbounds' ω hω
  let j := (feasibleIndices m β ω).sup id
  let h := countSelectedMesh m β ω
  have hwidth : h = meshWidth j := selectedMesh_width_of_pos m β ω hh
  have hwidth' : countSelectedMesh (polynomialDegree β) β ω =
      meshWidth ((feasibleIndices (polynomialDegree β) β ω).sup id) := by
    simpa [m, j, h] using hwidth
  have hfeasible : meshFeasible m β ω j := selectedMesh_feasible_of_pos m β ω hh
  have hγIcc : γ ∈ Set.Icc γ_min γ_max := by
    simpa only [adaptationRange] using hγ
  have hγgt : 1 < γ := hγmin.trans_le hγIcc.1
  have hnpos : 0 < n := by
    have : 1 ≤ n := (Nat.le_max_left _ _).trans hn
    omega
  have hκbound : κ ≤ ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) := by
    simpa only [a] using hκle γ hγIcc
  constructor
  · intro k α t
    have hrank := selectedMesh_raw_coefficient_mgf_rank β B C c_f γ κ
      P Q ω k hκ hκbound hγgt hnpos (fun α t => hraw m j hP k α
        hnpos hfeasible (hcounts k) t)
    rw [hwidth']
    exact (hrank α t).trans (Real.exp_le_exp.mpr (by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg t)
      have hx : 0 ≤ min (meshWidth j ^ (2 * β))
          ((n : ℝ)⁻¹ * meshWidth j ^ (-effectiveDimension d γ) *
            (cubeMassRank P m j k : ℝ) ^ (-(1 : ℝ) / (γ - 1))) := by
        have hr : 0 < (cubeMassRank P m j k : ℝ) := by
          exact_mod_cast cubeMassRank_pos P m j k
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
        have hw : 0 < meshWidth j := by unfold meshWidth; positivity
        exact le_min (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hKbase hx))
  · exact hint m j

/-- On the explicit design-saturated event, the conditional expected maximal
coefficient fluctuation has the oracle-rate bound almost everywhere. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma selectedMesh_saturated_conditional_envelope
    (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K K' : ℝ, 0 < K ∧ 0 < K' ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (P : Measure (Obs d)) [IsProbabilityMeasure P]
        (hP : P ∈ ModelClass d β B L C c_f γ)
        (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q],
        IIDSampleLaw Q P →
        ∃ E, SaturatedSelectedCountEvent β K γ P Q E ∧
          ∀ᵐ ω ∂Q, ω ∈ E →
            let m := polynomialDegree β
            let j := (feasibleIndices m β ω).sup id
            let h := countSelectedMesh m β ω
            Integrable (fun ξ => sSup ((fun k : Fin d → Fin (2 ^ j) =>
                ‖fun α : MonoIndex d m => coefHat m j ξ k α -
                  conditionalCoefCentre Q m j ω k α‖) '' Set.univ))
                (condDistrib id sampleDesign Q (sampleDesign ω)) ∧
            (∫ ξ, sSup ((fun k : Fin d → Fin (2 ^ j) =>
                ‖fun α : MonoIndex d m => coefHat m j ξ k α -
                  conditionalCoefCentre Q m j ω k α‖) '' Set.univ)
                ∂condDistrib id sampleDesign Q (sampleDesign ω)) ≤
              K' * oracleRate d n β γ := by
  obtain ⟨Kbase, hKbase, nbase, hbase⟩ :=
    selectedMesh_saturated_rank_mgf d β B L C c_f γ_min γ_max
      hd hβ hB hL hC hcf hγmin hγrange
  let αmin := 1 / (γ_max - 1)
  let αmax := 1 / (γ_min - 1)
  have hαmin : 0 < αmin := by
    have : 0 < γ_max - 1 := by linarith
    dsimp [αmin]
    positivity
  have hαmax : αmin ≤ αmax :=
    (selectedMesh_alpha_in_compact_range γ_min γ_max γ_min
      hγmin hγrange.le ⟨le_refl _, hγrange.le⟩).1
  obtain ⟨M, hM, hmax⟩ :=
    selectedMesh_cube_rank_vector_maximal αmin αmax Kbase
      hαmin hαmax hKbase
  let Eexp : ℝ := max 1 (2 * β * (γ_max - 1) + (d : ℝ) * γ_max)
  have hEexp : 0 < Eexp := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let p : ℝ := Fintype.card (MonoIndex d (polynomialDegree β))
  let K : ℝ := max Kbase (p * M * Real.sqrt Kbase * Real.sqrt Eexp) + 1
  have hKbaseLe : Kbase ≤ K := by
    dsimp [K]
    linarith [le_max_left Kbase (p * M * Real.sqrt Kbase * Real.sqrt Eexp)]
  have hKcoef : p * M * Real.sqrt Kbase * Real.sqrt Eexp ≤ K := by
    dsimp [K]
    linarith [le_max_right Kbase (p * M * Real.sqrt Kbase * Real.sqrt Eexp)]
  have hK : 0 < K := lt_of_lt_of_le hKbase hKbaseLe
  let K' := K * max 1 (K ^ β)
  have hK' : 0 < K' := mul_pos hK
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨K, K', hK, hK', max 1 nbase, ?_⟩
  intro n hn γ hγ P _ hP Q _ hIID
  obtain ⟨E, hE, hAE⟩ :=
    hbase n ((Nat.le_max_right _ _).trans hn) γ hγ P hP Q hIID
  rcases hE with ⟨hEmeas, hEbad, hEbounds, hEsat⟩
  have horacle : 0 ≤ oracleMesh d n β γ := by unfold oracleMesh; positivity
  have hEbounds' : ∀ ω ∈ E,
      0 < countSelectedMesh (polynomialDegree β) β ω ∧
      countSelectedMesh (polynomialDegree β) β ω ≤ K * oracleMesh d n β γ ∧
      ∀ (k : Fin d → Fin
          (2 ^ ((feasibleIndices (polynomialDegree β) β ω).sup id)))
        (ℓ : Fin d → Fin (polynomialDegree β + 1)),
        (n : ℝ) * microcellMass P (polynomialDegree β)
          ((feasibleIndices (polynomialDegree β) β ω).sup id) k ℓ / 5 ≤
          treatedCount (polynomialDegree β)
            ((feasibleIndices (polynomialDegree β) β ω).sup id) ω k ℓ := by
    intro ω hω
    obtain ⟨hh, hmesh, hcounts⟩ := hEbounds ω hω
    exact ⟨hh, hmesh.trans (mul_le_mul_of_nonneg_right hKbaseLe horacle), hcounts⟩
  refine ⟨E, ⟨hEmeas, hEbad, hEbounds', hEsat⟩, ?_⟩
  filter_upwards [hAE] with ω hmgfAE
  intro hω
  obtain ⟨hh, hmesh, _hcounts⟩ := hEbounds' ω hω
  obtain ⟨hmgf, hexp⟩ := hmgfAE hω
  let m := polynomialDegree β
  let j := (feasibleIndices m β ω).sup id
  let h := countSelectedMesh m β ω
  have hγIcc : γ ∈ Set.Icc γ_min γ_max := by
    simpa only [adaptationRange] using hγ
  have hγgt : 1 < γ := hγmin.trans_le hγIcc.1
  have hnpos : 0 < n := by
    have : 1 ≤ n := (Nat.le_max_left _ _).trans hn
    omega
  have hden : 0 < 2 * β + effectiveDimension d γ := by
    unfold effectiveDimension
    positivity
  have hα : 1 / (γ - 1) ∈ Set.Icc αmin αmax :=
    selectedMesh_alpha_in_compact_range γ_min γ_max γ
      hγmin hγrange.le hγIcc
  let a : ℝ := Real.sqrt Kbase * h ^ β
  let b : ℝ := Real.sqrt Kbase * (n : ℝ) ^ (-(1 : ℝ) / 2) *
    h ^ (-(effectiveDimension d γ) / 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by
    dsimp [b]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
    positivity
  have ha2 : a ^ 2 = Kbase * h ^ (2 * β) := by
    have hpow : (h ^ β) ^ 2 = h ^ (2 * β) := by
      rw [← Real.rpow_natCast (x := h ^ β) (n := 2)]
      rw [← Real.rpow_mul hh.le]
      congr 1
      ring
    simp only [a, mul_pow, Real.sq_sqrt hKbase.le, hpow]
  have hb2 : b ^ 2 = Kbase * ((n : ℝ)⁻¹ *
      h ^ (-effectiveDimension d γ)) := by
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hnpos.le
    have hnpow : ((n : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (n : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast (x := (n : ℝ) ^ (-(1 : ℝ) / 2)) (n := 2)]
      rw [← Real.rpow_mul hn']
      norm_num
      exact Real.rpow_neg_one (n : ℝ)
    have hhp : (h ^ (-(effectiveDimension d γ) / 2)) ^ 2 =
        h ^ (-effectiveDimension d γ) := by
      rw [← Real.rpow_natCast
        (x := h ^ (-(effectiveDimension d γ) / 2)) (n := 2)]
      rw [← Real.rpow_mul hh.le]
      congr 1
      ring
    simp only [b, mul_pow, Real.sq_sqrt hKbase.le, hnpow, hhp]
    ring
  have hvec := hmax P m j (1 / (γ - 1))
    (h ^ (2 * β)) ((n : ℝ)⁻¹ * h ^ (-effectiveDimension d γ))
    a b hα (by positivity) ha hb ha2 hb2
    (condDistrib id sampleDesign Q (sampleDesign ω))
    (fun k ξ α => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
    hexp (by simpa only [neg_div] using hmgf)
  have hintMax := selectedMesh_integrable_vector_max_of_exp_moments
    (condDistrib id sampleDesign Q (sampleDesign ω))
    (fun k ξ α => coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)
    hexp
  have hratio : b / a =
      (((n : ℝ) ^ (-(1 : ℝ) / 2) *
        h ^ (-(effectiveDimension d γ) / 2)) / h ^ β) := by
    dsimp [a, b]
    have hsqrt : Real.sqrt Kbase ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hKbase)
    have hpow : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
    field_simp
  have hlogRatio := selectedMesh_maximal_oracle_log_ratio
    d n β γ h (1 / (γ - 1)) hnpos hden hh (by positivity)
  have hexponent := selectedMesh_maximal_exponent_uniform
    d β γ γ_max (by linarith) hγgt hγIcc.2
  have hlog :
      Real.sqrt (1 + max 0 (Real.log ((b / a) ^ (2 / (1 / (γ - 1)))))) ≤
        Real.sqrt Eexp *
          Real.sqrt (1 + max 0 (Real.log (oracleMesh d n β γ / h))) := by
    rw [hratio]
    have hH : 0 ≤ 1 + max 0 (Real.log (oracleMesh d n β γ / h)) := by
      positivity
    have hfactor : max 1 ((β + effectiveDimension d γ / 2) *
        (2 / (1 / (γ - 1)))) ≤ Eexp := by
      dsimp [Eexp]
      exact max_le_max_left _ hexponent.2
    have hbound := hlogRatio.trans (mul_le_mul_of_nonneg_right hfactor hH)
    calc
      _ ≤ Real.sqrt (Eexp * (1 + max 0
            (Real.log (oracleMesh d n β γ / h)))) := Real.sqrt_le_sqrt hbound
      _ = _ := by rw [Real.sqrt_mul hEexp.le]
  have hnonneg : 0 ≤ h ^ β * Real.sqrt
      (1 + max 0 (Real.log (oracleMesh d n β γ / h))) := by positivity
  have hstoch :
      (∫ ξ, sSup ((fun k : Fin d → Fin (2 ^ j) =>
          ‖fun α : MonoIndex d m => coefHat m j ξ k α -
            conditionalCoefCentre Q m j ω k α‖) '' Set.univ)
          ∂condDistrib id sampleDesign Q (sampleDesign ω)) ≤
        K * h ^ β * Real.sqrt
          (1 + max 0 (Real.log (oracleMesh d n β γ / h))) := by
    calc
      _ ≤ p * M * a * Real.sqrt
          (1 + max 0 (Real.log ((b / a) ^ (2 / (1 / (γ - 1)))))) := hvec
      _ ≤ p * M * a * (Real.sqrt Eexp * Real.sqrt
          (1 + max 0 (Real.log (oracleMesh d n β γ / h)))) := by gcongr
      _ = (p * M * Real.sqrt Kbase * Real.sqrt Eexp) *
          (h ^ β * Real.sqrt
            (1 + max 0 (Real.log (oracleMesh d n β γ / h)))) := by
        dsimp [a]; ring
      _ ≤ K * (h ^ β * Real.sqrt
          (1 + max 0 (Real.log (oracleMesh d n β γ / h)))) :=
        mul_le_mul_of_nonneg_right hKcoef hnonneg
      _ = _ := by ring
  have hdet := selectedMesh_oracle_rate_log_bound
    d n β γ h K hnpos (by linarith) hh hmesh
  refine ⟨hintMax.1, hstoch.trans ?_⟩
  simpa only [K', mul_assoc] using
    (mul_le_mul_of_nonneg_left hdet hK.le)

/-- [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/

lemma selectedMesh_saturated_conditional_cubeLoss
    (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ K A : ℝ, 0 < K ∧ 0 < A ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
        (μ e : (Fin d → ℝ) → ℝ)
        (hmodel : GlobalTailModel β B L C c_f γ Pc μ e)
        (P : Measure (Obs d)) [IsProbabilityMeasure P]
        (hPobs : P = Pc.map observed)
        (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q],
        IIDSampleLaw Q P →
        ∃ E, SaturatedSelectedCountEvent β K γ P Q E ∧
          ∀ᵐ ω ∂Q, ω ∈ E →
            ∫ ξ, equalCellCubeLossReal β B μ ξ
              ∂condDistrib id sampleDesign Q (sampleDesign ω) ≤
                A * oracleRate d n β γ := by
  obtain ⟨Cb, hCb, hBiasUniform⟩ :=
    exists_uniform_conditionalCoefCentre_holder_cell_bias
      d β L (by linarith) hL
  obtain ⟨K, Kc, hK, hKc, n₀, hEnvelope⟩ :=
    selectedMesh_saturated_conditional_envelope
      d β B L C c_f γ_min γ_max hd hβ hB hL hC hcf hγmin hγrange
  let p : ℝ := Fintype.card (MonoIndex d (polynomialDegree β))
  let q : ℝ := (2 / templateLambda d (polynomialDegree β)) * Real.sqrt p
  let Db : ℝ := p * (q * (Cb * L)) + Cb * L
  let A : ℝ := p * Kc + Db * max 1 (K ^ β) + 1
  have hp : 0 < p := by
    dsimp [p]
    let α₀ : MonoIndex d (polynomialDegree β) :=
      ⟨fun _ => 0, by simp [monoIdx]⟩
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨α₀⟩ :
      0 < Fintype.card (MonoIndex d (polynomialDegree β)))
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (div_nonneg (by norm_num) (templateLambda_pos d _).le)
      (Real.sqrt_nonneg _)
  have hDb : 0 ≤ Db := by dsimp [Db]; positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨K, A, hK, hA, max 1 n₀, ?_⟩
  intro n hn γ hγ Pc _ μ e hmodel P _ hPobs Q _ hIID
  have hIIDc : IIDSampleLaw Q (Pc.map observed) := by
    simpa only [← hPobs] using hIID
  have hparams : ModelParameterDomain d β B L C c_f :=
    ⟨hd, hβ, hB, hL, hC, hcf⟩
  have hγgt : 1 < γ := by
    have hI : γ ∈ Set.Icc γ_min γ_max := by simpa [adaptationRange] using hγ
    exact hγmin.trans_le hI.1
  have hP : P ∈ ModelClass d β B L C c_f γ :=
    ⟨hparams, hγgt, Pc, inferInstance, μ, e, hPobs, hmodel⟩
  obtain ⟨E, hE, hEnvAE⟩ :=
    hEnvelope n ((Nat.le_max_right _ _).trans hn) γ hγ P hP Q hIID
  rcases hE with ⟨hEmeas, hEbad, hEbounds, hEsat⟩
  refine ⟨E, ⟨hEmeas, hEbad, hEbounds, hEsat⟩, ?_⟩
  have hBiasAE := hBiasUniform Pc μ e hparams hγgt hmodel Q hIIDc
  have hFibre := sampleDesign_condDistrib_fibre Q
  have hCondE := countDesignSaturated_condDistrib_one Q E hEmeas hEsat
  have hμB := holderResponse_abs_le_on_cube Pc μ e hparams hγgt hmodel
  filter_upwards [hEnvAE, hBiasAE, hFibre, hCondE]
    with ω hEnv hBias hFibreω hCondEω
  intro hωE
  obtain ⟨hSint, hSbound⟩ := hEnv hωE
  obtain ⟨hh, hmesh, hcounts⟩ := hEbounds ω hωE
  let m := polynomialDegree β
  let j := (feasibleIndices m β ω).sup id
  let h := countSelectedMesh m β ω
  let S : (Fin n → Obs d) → ℝ := fun ξ =>
    sSup ((fun k : Fin d → Fin (2 ^ j) =>
      ‖fun α : MonoIndex d m => coefHat m j ξ k α -
        conditionalCoefCentre Q m j ω k α‖) '' Set.univ)
  have hwidth : h = meshWidth j := selectedMesh_width_of_pos m β ω hh
  have hposCounts : ∀ (k : Fin d → Fin (2 ^ j))
      (ℓ : Fin d → Fin (m + 1)), 0 < treatedCount m j ω k ℓ := by
    intro k ℓ
    have hmass : 0 < microcellMass P m j k ℓ :=
      model_microcellMass_pos P hP m j k ℓ
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by
        have : 1 ≤ n := (Nat.le_max_left _ _).trans hn
        omega)
    have hreal : (0 : ℝ) < treatedCount m j ω k ℓ :=
      lt_of_lt_of_le (div_pos (mul_pos hnpos hmass) (by norm_num)) (hcounts k ℓ)
    exact_mod_cast hreal
  have hcell : ∀ k : Fin d → Fin (2 ^ j),
      ∃ θ : MonoIndex d m → ℝ,
        (∀ x ∈ dyadicCube d j k,
          |μ x - ∑ α, monoVec d m
            (fun a => (x a - cubeCorner d j k a) / h) α * θ α| ≤
              Cb * L * h ^ β) ∧
        ∀ α,
          |conditionalCoefCentre Q m j ω k α - θ α| ≤
            q * (Cb * L * h ^ β) := by
    intro k
    have hb := hBias j k (hposCounts k)
    rw [hwidth]
    simpa [m, j, h, q, p, mul_assoc] using hb
  let ν := condDistrib id sampleDesign Q (sampleDesign ω)
  have hνE : ∀ᵐ ξ ∂ν, ξ ∈ E := by
    change E ∈ ae ν
    exact (mem_ae_iff_prob_eq_one hEmeas).2 (hCondEω hωE)
  have hpoint : ∀ᵐ ξ ∂ν,
      equalCellCubeLossReal β B μ ξ ≤ p * (S ξ + q * (Cb * L * h ^ β)) +
        Cb * L * h ^ β := by
    filter_upwards [hνE, hFibreω] with ξ hξE hdesign
    have hdet := equalCellEstimator_error_le_conditional_envelope_of_design_eq
      (β := β) (B := B) (r := Cb * L * h ^ β)
      (εb := q * (Cb * L * h ^ β)) Q μ ω ξ hdesign hh hwidth
      hB.le hμB (by positivity) (by positivity) hcell
    have hfi := feasibleIndices_eq_of_design_eq m β ω ξ hdesign
    rw [hfi] at hdet
    have hdet' : ∀ x ∈ cube d,
        |equalCellEstimator β B ξ x - μ x| ≤
          p * (S ξ + q * (Cb * L * h ^ β)) + Cb * L * h ^ β := by
      simpa only [p, S, m, j] using hdet
    have hSnonneg : 0 ≤ S ξ := by
      apply Real.sSup_nonneg
      rintro z ⟨k, -, rfl⟩
      exact norm_nonneg _
    have hRnonneg : 0 ≤
        p * (S ξ + q * (Cb * L * h ^ β)) + Cb * L * h ^ β := by
      positivity
    have hsup := cube_iSup_ofReal_loss_le
      (fun x => equalCellEstimator β B ξ x - μ x)
      (p * (S ξ + q * (Cb * L * h ^ β)) + Cb * L * h ^ β)
      hRnonneg hdet'
    unfold equalCellCubeLossReal
    exact ENNReal.toReal_le_of_le_ofReal hRnonneg hsup
  have hZmeas := equalCellCubeLossReal_measurable (n := n) β B μ
    hmodel.smooth.1.regularity.continuousOn
  have hZint : Integrable (equalCellCubeLossReal β B μ) ν :=
    Integrable.of_bound hZmeas.aestronglyMeasurable (2 * B) <|
      ae_of_all ν fun ξ => by
        rw [Real.norm_eq_abs]
        unfold equalCellCubeLossReal
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        exact equalCellCubeLossReal_le_two_mul β B μ hB.le hμB ξ
  have hRint : Integrable (fun ξ =>
      p * (S ξ + q * (Cb * L * h ^ β)) + Cb * L * h ^ β) ν := by
    exact ((hSint.add (integrable_const _)).const_mul p).add (integrable_const _)
  calc
    ∫ ξ, equalCellCubeLossReal β B μ ξ ∂ν ≤
        ∫ ξ, (p * (S ξ + q * (Cb * L * h ^ β)) +
          Cb * L * h ^ β) ∂ν := integral_mono_ae hZint hRint hpoint
    _ = p * (∫ ξ, S ξ ∂ν) + Db * h ^ β := by
      have hνprob : ν.real Set.univ = 1 := by
        dsimp [ν]
        simp
      calc
        ∫ ξ, p * (S ξ + q * (Cb * L * h ^ β)) + Cb * L * h ^ β ∂ν =
            (∫ ξ, p * (S ξ + q * (Cb * L * h ^ β)) ∂ν) +
              ∫ _ξ, Cb * L * h ^ β ∂ν :=
          integral_add ((hSint.add (integrable_const _)).const_mul p)
            (integrable_const _)
        _ = p * (∫ ξ, S ξ + q * (Cb * L * h ^ β) ∂ν) +
              ∫ _ξ, Cb * L * h ^ β ∂ν := by
          rw [integral_const_mul]
        _ = p * ((∫ ξ, S ξ ∂ν) +
              ∫ _ξ, q * (Cb * L * h ^ β) ∂ν) +
              ∫ _ξ, Cb * L * h ^ β ∂ν := by
          rw [integral_add hSint (integrable_const _)]
        _ = p * (∫ ξ, S ξ ∂ν) + Db * h ^ β := by
          rw [integral_const, integral_const, hνprob]
          simp only [one_smul]
          dsimp [Db]
          ring
    _ ≤ p * (Kc * oracleRate d n β γ) + Db * h ^ β := by gcongr
    _ ≤ A * oracleRate d n β γ := by
      have hrate : 0 ≤ oracleRate d n β γ := by unfold oracleRate oracleMesh; positivity
      have hmeshPow : h ^ β ≤ max 1 (K ^ β) * oracleRate d n β γ := by
        have horacle : 0 ≤ oracleMesh d n β γ := by unfold oracleMesh; positivity
        have hpw := Real.rpow_le_rpow hh.le hmesh (by linarith : 0 ≤ β)
        rw [Real.mul_rpow hK.le horacle] at hpw
        change h ^ β ≤ K ^ β * oracleRate d n β γ at hpw
        exact hpw.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrate)
      dsimp [A]
      nlinarith [mul_nonneg hp.le hrate, mul_nonneg hDb hrate,
        mul_le_mul_of_nonneg_left hmeshPow hDb]

/-- The saturated conditional bound integrates to the desired uniform risk
bound for every displayed model witness.  This version keeps the response
representative explicit, so it is usable below the `responseOf` choice layer. [For the stated inputs and conditions](hyp:d,β,B,L,C,c_f,γ_min,γ_max,hd,hβ,hB,hL,hC,hcf,hγmin,hγrange), [the asserted conclusion holds](goal). -/
lemma selectedMesh_uniform_equalCellCubeRisk
    (d : ℕ) (β B L C c_f γ_min γ_max : ℝ)
    (hd : 1 ≤ d) (hβ : 1 < β) (hB : 0 < B) (hL : 0 < L)
    (hC : 1 ≤ C) (hcf : 0 < c_f ∧ c_f ≤ 1)
    (hγmin : 1 < γ_min) (hγrange : γ_min < γ_max) :
    ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ γ ∈ adaptationRange γ_min γ_max ⟨hγmin, hγrange⟩,
      ∀ (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
        (μ e : (Fin d → ℝ) → ℝ)
        (hmodel : GlobalTailModel β B L C c_f γ Pc μ e)
        (P : Measure (Obs d)) [IsProbabilityMeasure P],
        P = Pc.map observed →
        (∫⁻ ω, ⨆ x, ⨆ (_hx : x ∈ cube d),
            ENNReal.ofReal |equalCellEstimator β B ω x - μ x|
          ∂Measure.pi (fun _ : Fin n => P)) ≤
          ENNReal.ofReal (A * oracleRate d n β γ) := by
  obtain ⟨K, A₀, hK, hA₀, n₀, hcond⟩ :=
    selectedMesh_saturated_conditional_cubeLoss
      d β B L C c_f γ_min γ_max hd hβ hB hL hC hcf hγmin hγrange
  let A : ℝ := A₀ + 2 * B
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, max 1 n₀, ?_⟩
  intro n hn γ hγ Pc _ μ e hmodel P _ hPobs
  let Q : Measure (Fin n → Obs d) := Measure.pi (fun _ : Fin n => P)
  letI : IsProbabilityMeasure Q := inferInstance
  have hIID : IIDSampleLaw Q P := rfl
  obtain ⟨E, hE, hgood⟩ := hcond n ((Nat.le_max_right _ _).trans hn)
    γ hγ Pc μ e hmodel P hPobs Q hIID
  rcases hE with ⟨hEmeas, hEbad, -, -⟩
  have hparams : ModelParameterDomain d β B L C c_f :=
    ⟨hd, hβ, hB, hL, hC, hcf⟩
  have hγgt : 1 < γ := by
    have hI : γ ∈ Set.Icc γ_min γ_max := by
      simpa [adaptationRange] using hγ
    exact hγmin.trans_le hI.1
  have hμB := holderResponse_abs_le_on_cube Pc μ e hparams hγgt hmodel
  let Z : (Fin n → Obs d) → ℝ := equalCellCubeLossReal β B μ
  have hZm : Measurable Z :=
    equalCellCubeLossReal_measurable β B μ
      hmodel.smooth.1.regularity.continuousOn
  have hZle : ∀ ω, Z ω ≤ 2 * B :=
    fun ω => equalCellCubeLossReal_le_two_mul β B μ hB.le hμB ω
  have hZint : Integrable Z Q :=
    Integrable.of_bound hZm.aestronglyMeasurable (2 * B) <|
      ae_of_all Q fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hZle ω
        · exact ENNReal.toReal_nonneg
  have hall : ∀ᵐ ω ∂Q,
      ∫ ξ, Z ξ ∂condDistrib id sampleDesign Q (sampleDesign ω) ≤ 2 * B := by
    apply ae_of_all
    intro ω
    let ν := condDistrib id sampleDesign Q (sampleDesign ω)
    have hZintν : Integrable Z ν :=
      Integrable.of_bound hZm.aestronglyMeasurable (2 * B) <|
        ae_of_all ν fun ξ => by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · exact hZle ξ
          · exact ENNReal.toReal_nonneg
    calc
      ∫ ξ, Z ξ ∂ν ≤ ∫ _ξ, 2 * B ∂ν :=
        integral_mono_ae hZintν (integrable_const _) (ae_of_all ν hZle)
      _ = 2 * B := by simp
  have hrate : 0 ≤ oracleRate d n β γ := by
    unfold oracleRate oracleMesh
    positivity
  have hreal : ∫ ω, Z ω ∂Q ≤ A * oracleRate d n β γ := by
    have hsplit := integral_le_of_condDistrib_event_bounds Q sampleDesign
      sampleDesign_measurable Z hZm.stronglyMeasurable hZint E hEmeas
      (A₀ * oracleRate d n β γ) (2 * B) ((n : ℝ) ^ (-2 : ℝ))
      (mul_nonneg hA₀.le hrate) (by positivity) (by positivity)
      hgood hall hEbad
    have hn1 : 1 ≤ n := (Nat.le_max_left _ _).trans hn
    have hsquare := inverseSquare_le_oracleRate d n β γ hn1
      (by linarith) hγgt
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 2 * B)]
  rw [equalCellCubeLoss_lintegral_eq_ofReal_integral β B μ hB.le
    hmodel.smooth.1.regularity.continuousOn hμB Q]
  exact ENNReal.ofReal_le_ofReal hreal
end CausalSmith.Stat.WeakOverlap
