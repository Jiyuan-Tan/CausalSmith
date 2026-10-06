module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Fibre

/-! # Selected-mesh mass ranks and coefficient proxies -/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.RandomDesignWeightedHoeffding
open scoped Classical

/-- Rank by weakest-cell mass; ties receive their largest available rank. For [the stated inputs and conditions](hyp:P,m,j,k), [the `cubeMassRank` object being defined](goal). -/
noncomputable def cubeMassRank {d : ℕ} (P : Measure (Obs d)) [IsProbabilityMeasure P] (m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k' : Fin d → Fin (2 ^ j) =>
    cubeMass P m j k' ≤ cubeMass P m j k)).card

/-- Mass ranks respect the order of cube masses, including tied masses. [For the stated inputs and conditions](hyp:d,P,m,j,k,k',h), [the asserted conclusion holds](goal). -/
lemma cubeMassRank_mono {d : ℕ} (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (m j : ℕ) (k k' : Fin d → Fin (2 ^ j))
    (h : cubeMass P m j k ≤ cubeMass P m j k') :
    cubeMassRank P m j k ≤ cubeMassRank P m j k' := by
  classical
  unfold cubeMassRank
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  exact hq.trans h

/-- Each cube contributes itself to its mass rank. [For the stated inputs and conditions](hyp:d,P,m,j,k), [the asserted conclusion holds](goal). -/
lemma cubeMassRank_pos {d : ℕ} (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (m j : ℕ) (k : Fin d → Fin (2 ^ j)) :
    0 < cubeMassRank P m j k := by
  classical
  unfold cubeMassRank
  exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, le_refl _⟩⟩

/-- An injective list of cubes in increasing mass order has at least its
position in the mass rank. This is the index conversion for the ordered
maximal inequality. [For the stated inputs and conditions](hyp:d,N,P,m,j,σ,hσ,horder,b), [the asserted conclusion holds](goal). -/
lemma cubeMassRank_lower_of_ordered {d N : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (m j : ℕ)
    (σ : Fin N → Fin d → Fin (2 ^ j)) (hσ : Function.Injective σ)
    (horder : ∀ a b : Fin N, a ≤ b →
      cubeMass P m j (σ a) ≤ cubeMass P m j (σ b))
    (b : Fin N) : b.val + 1 ≤ cubeMassRank P m j (σ b) := by
  classical
  have hsub : (Finset.Iic b).image σ ⊆
      Finset.univ.filter (fun q : Fin d → Fin (2 ^ j) =>
        cubeMass P m j q ≤ cubeMass P m j (σ b)) := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, horder a b (Finset.mem_Iic.mp ha)⟩
  calc
    b.val + 1 = (Finset.Iic b).card := (Fin.card_Iic b).symm
    _ = ((Finset.Iic b).image σ).card :=
      (Finset.card_image_of_injective _ hσ).symm
    _ ≤ cubeMassRank P m j (σ b) := by
      unfold cubeMassRank
      exact Finset.card_le_card hsub

/-- Enumerate all cubes in nondecreasing weakest-cell mass, breaking ties by
an arbitrary fixed finite index. [For the stated inputs and conditions](hyp:d,P,m,j), [the asserted conclusion holds](goal). -/
lemma cubeMass_ordered_equiv {d : ℕ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P] (m j : ℕ) :
    ∃ σ : Fin (Fintype.card (Fin d → Fin (2 ^ j))) ≃
        (Fin d → Fin (2 ^ j)),
      Monotone (fun i => cubeMass P m j (σ i)) ∧
      ∀ b, b.val + 1 ≤ cubeMassRank P m j (σ b) := by
  classical
  let e : (Fin d → Fin (2 ^ j)) ≃
      Fin (Fintype.card (Fin d → Fin (2 ^ j))) :=
    (Fintype.truncEquivFinOfCardEq (α := Fin d → Fin (2 ^ j)) rfl).out
  let order : LinearOrder (Fin d → Fin (2 ^ j)) :=
    LinearOrder.lift'
      (fun k => toLex (cubeMass P m j k, e k))
      (by
        intro a b hab
        apply e.injective
        exact congrArg (fun x : Lex (ℝ × Fin (Fintype.card (Fin d → Fin (2 ^ j)))) =>
          (ofLex x).2) hab)
  letI := order
  letI : LE (Fin d → Fin (2 ^ j)) := order.toLE
  let τ := Fintype.orderIsoFinOfCardEq (Fin d → Fin (2 ^ j)) rfl
  have hmono : Monotone (fun i => cubeMass P m j (τ i)) := by
    intro a b hab
    have h : τ a ≤ τ b := by
      exact (τ.le_iff_le).2 hab
    change (toLex (cubeMass P m j (τ a), e (τ a))) ≤
      toLex (cubeMass P m j (τ b), e (τ b)) at h
    exact Prod.Lex.monotone_fst _ _ h
  refine ⟨τ.toEquiv, hmono, ?_⟩
  intro b
  exact cubeMassRank_lower_of_ordered P m j τ.toEquiv
    τ.toEquiv.injective (fun a b hab => hmono hab) b

/-- The rank counting all cubes with mass no larger than a given cube gives
that cube the same ordered lower bound, including when masses tie. [For the stated inputs and conditions](hyp:d,m,j,β,B,L,C,c_f,γ,Pc,μ₁,e,hmodel,hC,hγ,hcf,k), [the asserted conclusion holds](goal). -/
lemma model_cubeMassRank_lower {d : ℕ} (m j : ℕ)
    (β B L C c_f γ : ℝ)
    (Pc : Measure (Completion d)) [IsProbabilityMeasure Pc]
    (μ₁ e : (Fin d → ℝ) → ℝ)
    (hmodel : GlobalTailModel β B L C c_f γ Pc μ₁ e)
    (hC : 1 ≤ C) (hγ : 1 < γ) (hcf : 0 < c_f)
    (k : Fin d → Fin (2 ^ j)) :
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) *
      meshWidth j ^ effectiveDimension d γ *
      (@cubeMassRank d (Pc.map observed)
        (Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)) m j k : ℝ) ^
        (1 / (γ - 1)) ≤
        @cubeMass d (Pc.map observed)
          (Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)) m j k := by
  classical
  letI : IsProbabilityMeasure (Pc.map observed) :=
    Measure.isProbabilityMeasure_map (by unfold observed; fun_prop)
  let S : Finset (Fin d → Fin (2 ^ j)) := Finset.univ.filter
    (fun q => cubeMass (Pc.map observed) m j q ≤ cubeMass (Pc.map observed) m j k)
  have hcard : S.card = cubeMassRank (Pc.map observed) m j k := rfl
  have hr : 0 < S.card := Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, le_refl _⟩⟩
  have hmin : ∀ q : Fin d → Fin (2 ^ j),
      ∃ ℓ : Fin d → Fin (m + 1),
        cubeMass (Pc.map observed) m j q = microcellMass (Pc.map observed) m j q ℓ :=
    fun q => orderedMass_cubeMass_attained (Pc.map observed) m j q
  choose ℓ hℓ using hmin
  have hlower := orderedMass_selectedMicrocells_treated_lower d m j
    β B L C c_f γ Pc μ₁ e hmodel hC hγ hcf.le S ℓ
  have hupper := orderedMass_selectedMicrocells_treated_le_card_mul
    (Pc.map observed) m j S ℓ (cubeMass (Pc.map observed) m j k)
    (fun q _ => (hℓ q).symm)
    (fun q hq => (Finset.mem_filter.mp hq).2)
  have hη : 0 ≤ templateEta d m := (templateEta_pos d m).le
  rw [orderedMass_microcell_volume_toReal d m j hη] at hlower
  have ha : 0 ≤ c_f * templateEta d m ^ d := by positivity
  have hh : 0 ≤ meshWidth j := by unfold meshWidth; positivity
  have hr' : 0 < (S.card : ℝ) := by exact_mod_cast hr
  have hbase : c_f * (templateEta d m * meshWidth j) ^ d =
      (c_f * templateEta d m ^ d) * meshWidth j ^ d := by
    rw [mul_pow]
    ring
  rw [hbase] at hlower
  have hidentity := orderedMass_rank_power_identity d S.card
    (c_f * templateEta d m ^ d) (meshWidth j) γ hr ha hh hγ
  have hmass :
      ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
        (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) *
        meshWidth j ^ effectiveDimension d γ *
        (S.card : ℝ) ^ (1 / (γ - 1)) ≤
          cubeMass (Pc.map observed) m j k := by
    have hfactor :
        ((S.card : ℝ) * ((c_f * templateEta d m ^ d) * meshWidth j ^ d)) ^
            (γ / (γ - 1)) / (S.card : ℝ) =
          (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) *
            meshWidth j ^ effectiveDimension d γ *
            (S.card : ℝ) ^ (1 / (γ - 1)) := by
      simpa only [effectiveDimension, div_eq_mul_inv, mul_assoc] using hidentity
    have hdiv :
        (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
          ((S.card : ℝ) * ((c_f * templateEta d m ^ d) * meshWidth j ^ d)) ^
            (γ / (γ - 1))) / (S.card : ℝ) ≤
          cubeMass (Pc.map observed) m j k :=
      (div_le_iff₀ hr').2 (by simpa [mul_comm] using (hlower.trans hupper))
    rw [mul_div_assoc, hfactor] at hdiv
    simpa only [mul_assoc] using hdiv
  simpa only [← hcard] using hmass

/-- The concrete mass-rank profile for any observed law in the model class. [For the stated inputs and conditions](hyp:d,m,j,β,B,L,C,c_f,γ,P,hP,k), [the asserted conclusion holds](goal). -/
lemma modelClass_cubeMassRank_lower {d : ℕ} (m j : ℕ)
    {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (k : Fin d → Fin (2 ^ j)) :
    ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) *
      meshWidth j ^ effectiveDimension d γ *
      (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1)) ≤ cubeMass P m j k := by
  obtain ⟨hparams, hγ, Pc, hPc, μ₁, e, rfl, hmodel⟩ := hP
  letI : IsProbabilityMeasure Pc := hPc
  exact model_cubeMassRank_lower m j β B L C c_f γ Pc μ₁ e hmodel
    hparams.2.2.2.2.1 hγ hparams.2.2.2.2.2.1 k

/-- Feasibility and the selected event give the ordered inverse-count factor
with the model's explicit mass constant. [For the stated inputs and conditions](hyp:d,n,m,j,β,B,L,C,c_f,γ,P,hP,ω,k,hn,hfeasible,hselected), [the asserted conclusion holds](goal). -/
lemma modelClass_selectedCount_inverse_rank_bounds {d n : ℕ} (m j : ℕ)
    {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (hn : 0 < n) (hfeasible : meshFeasible m β ω j)
    (hselected : ∀ ℓ : Fin d → Fin (m + 1),
      (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ) :
    (∑ ℓ : Fin d → Fin (m + 1),
        (treatedCount m j ω k ℓ : ℝ)⁻¹) ≤
      (tensorCount d m : ℝ) *
        min (meshWidth j ^ (2 * β))
          (5 / ((n : ℝ) *
            (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
              (c_f * templateEta d m ^ d) ^ (γ / (γ - 1))) *
            meshWidth j ^ effectiveDimension d γ *
            (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1)))) := by
  classical
  have hγ : 1 < γ := hP.2.1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hP.1.2.2.2.2.1
  have hcf : 0 < c_f := hP.1.2.2.2.2.2.1
  have hκ : 0 < ((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)) := by
    have hη := templateEta_pos d m
    positivity
  have hr : 0 < cubeMassRank P m j k := cubeMassRank_pos P m j k
  exact selectedCount_cube_inverse_rank_bounds m j β
    (effectiveDimension d γ) (1 / (γ - 1))
    (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
      (c_f * templateEta d m ^ d) ^ (γ / (γ - 1)))
    (cubeMassRank P m j k) P ω k hn hκ hr hfeasible hselected
    (modelClass_cubeMassRank_lower m j P hP k)

/-- On the selected count event, the coefficient weights have both the
feasibility and ordered-mass variance scales. [For the stated inputs and conditions](hyp:d,n,m,j,β,B,L,C,c_f,γ,P,hP,ω,k,α,R,hn,hfeasible,hselected,hrow), [the asserted conclusion holds](goal). -/
lemma modelClass_coefResidualWeight_square_rank_bounds {d n : ℕ} (m j : ℕ)
    {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (R : ℝ)
    (hn : 0 < n) (hfeasible : meshFeasible m β ω j)
    (hselected : ∀ ℓ : Fin d → Fin (m + 1),
      (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ)
    (hrow : ∀ (ℓ : Fin d → Fin (m + 1)) (i : Fin n),
      (ω i).2.1 = true ∧ (ω i).1 ∈ scaledMicroCell d m j k ℓ →
      |(tensorCount d m : ℝ)⁻¹ *
        ∑ α' : MonoIndex d m,
          (gramHat m j ω k)⁻¹ α α' *
            monoVec d m
              (fun a => ((ω i).1 a - cubeCorner d j k a) / meshWidth j) α'| ≤ R) :
    (∑ i : Fin n, (coefResidualWeight m j ω k α i) ^ 2) ≤
      (tensorCount d m : ℝ) * R ^ 2 *
        ((tensorCount d m : ℝ) *
          min (meshWidth j ^ (2 * β))
            (5 / ((n : ℝ) *
              (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
                (c_f * templateEta d m ^ d) ^ (γ / (γ - 1))) *
              meshWidth j ^ effectiveDimension d γ *
              (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1))))) := by
  calc
    _ ≤ (tensorCount d m : ℝ) * R ^ 2 *
        ∑ ℓ : Fin d → Fin (m + 1),
          (treatedCount m j ω k ℓ : ℝ)⁻¹ :=
      coefResidualWeight_square_sum_le m j ω k α R hrow
    _ ≤ _ := by
      gcongr
      exact modelClass_selectedCount_inverse_rank_bounds m j P hP ω k
        hn hfeasible hselected

/-- The equal-cell conditioning theorem supplies the uniform row constant in
the ordered squared-weight bound; no separate row assumption is needed. [For the stated inputs and conditions](hyp:d,n,m,j,β,B,L,C,c_f,γ,P,hP,ω,k,α,hn,hfeasible,hselected), [the asserted conclusion holds](goal). -/
lemma modelClass_coefResidualWeight_square_rank_bounds_of_feasible
    {d n : ℕ} (m j : ℕ) {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (hn : 0 < n)
    (hfeasible : meshFeasible m β ω j)
    (hselected : ∀ ℓ : Fin d → Fin (m + 1),
      (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ) :
    (∑ i : Fin n, (coefResidualWeight m j ω k α i) ^ 2) ≤
      (tensorCount d m : ℝ) *
        ((tensorCount d m : ℝ)⁻¹ *
          ((2 / templateLambda d m) *
            Real.sqrt (Fintype.card (MonoIndex d m) : ℝ))) ^ 2 *
        ((tensorCount d m : ℝ) *
          min (meshWidth j ^ (2 * β))
            (5 / ((n : ℝ) *
              (((γ - 1) / γ) * C ^ (-(1 : ℝ) / (γ - 1)) *
                (c_f * templateEta d m ^ d) ^ (γ / (γ - 1))) *
              meshWidth j ^ effectiveDimension d γ *
              (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1))))) := by
  have hcount : ∀ ℓ : Fin d → Fin (m + 1),
      0 < treatedCount m j ω k ℓ := by
    intro ℓ
    have hthreshold : 0 < meshWidth j ^ (-2 * β) := by
      unfold meshWidth
      positivity
    have hpositive : (0 : ℝ) < treatedCount m j ω k ℓ :=
      lt_of_lt_of_le hthreshold (hfeasible.2 k ℓ)
    exact_mod_cast hpositive
  exact modelClass_coefResidualWeight_square_rank_bounds m j P hP ω k α _
    hn hfeasible hselected
    (inverseGram_row_bound_on_scaledMicroCell m j ω k α hcount)

/-- Once the outcome residuals are independent under the fixed-design law,
the selected count event gives both ordered coefficient MGF proxies. [For the stated inputs and conditions](hyp:d,n,m,j,β,B,L,C,c_f,γ,P,hP,ω,k,α,hn,hfeasible,hselected,Ω,μ,Y,hindep,hmeas,hmgf,t), [the asserted conclusion holds](goal). -/
lemma modelClass_selectedCoefficientResidual_mgf_rank_bound
    {d n : ℕ} (m j : ℕ) {β B L C c_f γ : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (hP : P ∈ ModelClass d β B L C c_f γ)
    (ω : Fin n → Obs d) (k : Fin d → Fin (2 ^ j))
    (α : MonoIndex d m) (hn : 0 < n)
    (hfeasible : meshFeasible m β ω j)
    (hselected : ∀ ℓ : Fin d → Fin (m + 1),
      (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → ℝ)
    (hindep : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hmgf : ∀ i t, mgf (Y i) μ t ≤ Real.exp (B ^ 2 * t ^ 2 / 2))
    (t : ℝ) :
    mgf (∑ i : Fin n, fun ξ => coefResidualWeight m j ω k α i * Y i ξ) μ t ≤
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
                (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1)))))) * t ^ 2 / 2) := by
  have hweight := modelClass_coefResidualWeight_square_rank_bounds_of_feasible
    m j P hP ω k α hn hfeasible hselected
  calc
    mgf (∑ i : Fin n, fun ξ => coefResidualWeight m j ω k α i * Y i ξ) μ t ≤
      Real.exp (B ^ 2 *
        (∑ i : Fin n, (coefResidualWeight m j ω k α i) ^ 2) * t ^ 2 / 2) :=
      independentWeightedResidual_mgf_le μ Y
        (coefResidualWeight m j ω k α) B hindep hmeas hmgf t
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      gcongr

/-- On almost every complete-design fibre, a coefficient centred by its
conditional integral obeys the selected ordered mass-rank MGF bound. [For the stated inputs and conditions](hyp:d,n,B,P,Q,hIID,hres), [the asserted conclusion holds](goal). -/
lemma modelClass_conditionalCoefficient_mgf_rank_bound
    {d n : ℕ} {B : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P)
    (hres : BoundedMeanSubGaussianResidual P B) :
    ∀ᵐ ω ∂Q, ∀ (m j : ℕ) {β L C c_f γ : ℝ},
      P ∈ ModelClass d β B L C c_f γ →
      ∀ (k : Fin d → Fin (2 ^ j)) (α : MonoIndex d m),
      0 < n → meshFeasible m β ω j →
      (∀ ℓ : Fin d → Fin (m + 1),
        (n : ℝ) * microcellMass P m j k ℓ / 5 ≤ treatedCount m j ω k ℓ) →
      ∀ t : ℝ,
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
                  (cubeMassRank P m j k : ℝ) ^ (1 / (γ - 1)))))) * t ^ 2 / 2) := by
  filter_upwards [conditionalCoefCentre_eq_conditionalMeanSample P Q hIID hres,
    sampleDesign_condDistrib_fibre Q,
    sampleDesign_conditional_residual_family P Q hIID hres]
    with ω hcentre hfibre hfamily
  intro m j β L C c_f γ hP k α hn hfeasible hselected t
  let μ := condDistrib id sampleDesign Q (sampleDesign ω)
  have heq : (fun ξ => coefHat m j ξ k α -
      conditionalCoefCentre Q m j ω k α) =ᵐ[μ]
      (∑ i : Fin n, fun ξ => coefResidualWeight m j ω k α i *
        conditionalTreatedResidual P ω i ξ) := by
    filter_upwards [hfibre] with ξ hdesign
    rw [hcentre m j k α]
    simpa only [Finset.sum_apply] using
      coefHat_sub_conditionalMeanSample_eq_residual_sum
        m j P ω ξ k α hdesign
  rw [mgf_congr heq]
  exact modelClass_selectedCoefficientResidual_mgf_rank_bound
    m j P hP ω k α hn hfeasible hselected μ
      (conditionalTreatedResidual P ω) hfamily.1
      (by
        intro i
        by_cases hi : (ω i).2.1 = true
        · have hfun : conditionalTreatedResidual P ω i =
              fun ξ => (ξ i).2.2 - treatedRegression P (ω i).1 := by
            funext ξ
            simp [conditionalTreatedResidual, hi]
          rw [hfun]
          fun_prop
        · have hfun : conditionalTreatedResidual P ω i = fun _ => 0 := by
            funext ξ
            simp [conditionalTreatedResidual, hi]
          rw [hfun]
          fun_prop)
      (fun i t => (hfamily.2 i t).2) t

/-- The centered coefficient has every exponential moment on almost every
complete-design fibre. This supplies the integrability premise of the
ordered maximal inequality separately from its MGF upper bound. [For the stated inputs and conditions](hyp:d,n,B,P,Q,hIID,hres), [the asserted conclusion holds](goal). -/
lemma conditionalCoefficient_integrable_exp
    {d n : ℕ} {B : ℝ}
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (Q : Measure (Fin n → Obs d)) [IsProbabilityMeasure Q]
    (hIID : IIDSampleLaw Q P)
    (hres : BoundedMeanSubGaussianResidual P B) :
    ∀ᵐ ω ∂Q, ∀ (m j : ℕ) (k : Fin d → Fin (2 ^ j))
      (α : MonoIndex d m) (t : ℝ),
      Integrable (fun ξ => Real.exp (t *
        (coefHat m j ξ k α - conditionalCoefCentre Q m j ω k α)))
        (condDistrib id sampleDesign Q (sampleDesign ω)) := by
  filter_upwards [conditionalCoefCentre_eq_conditionalMeanSample P Q hIID hres,
    sampleDesign_condDistrib_fibre Q,
    sampleDesign_conditional_residual_family P Q hIID hres]
    with ω hcentre hfibre hfamily
  intro m j k α t
  let μ := condDistrib id sampleDesign Q (sampleDesign ω)
  have heq : (fun ξ => coefHat m j ξ k α -
      conditionalCoefCentre Q m j ω k α) =ᵐ[μ]
      (∑ i : Fin n, fun ξ => coefResidualWeight m j ω k α i *
        conditionalTreatedResidual P ω i ξ) := by
    filter_upwards [hfibre] with ξ hdesign
    rw [hcentre m j k α]
    simpa only [Finset.sum_apply] using
      coefHat_sub_conditionalMeanSample_eq_residual_sum
        m j P ω ξ k α hdesign
  have hsum := independentWeightedResidual_integrable_exp_sum μ
    (conditionalTreatedResidual P ω)
    (coefResidualWeight m j ω k α) hfamily.1
    (by
      intro i
      by_cases hi : (ω i).2.1 = true
      · have hfun : conditionalTreatedResidual P ω i =
            fun ξ => (ξ i).2.2 - treatedRegression P (ω i).1 := by
          funext ξ
          simp [conditionalTreatedResidual, hi]
        rw [hfun]
        fun_prop
      · have hfun : conditionalTreatedResidual P ω i = fun _ => 0 := by
          funext ξ
          simp [conditionalTreatedResidual, hi]
        rw [hfun]
        fun_prop)
    (fun i u => (hfamily.2 i u).1) t
  exact hsum.congr (heq.fun_comp
    (fun x : ℝ => Real.exp (t * x)) |>.symm)

end CausalSmith.Stat.WeakOverlap
