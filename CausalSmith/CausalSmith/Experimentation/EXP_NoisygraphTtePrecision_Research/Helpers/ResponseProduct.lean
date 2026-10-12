module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.MatchingSupport
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.ReferenceLaw
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTransport
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Conditional recipient product densities

For a fixed matching and assignment, the independent translated recipient laws
are the balanced product response law tilted by the matching likelihood product.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

/-- Given [the stated assumptions](hyp:h0,hi), [Integrable nonnegative coordinate densities tensorize into a product density.](goal) -/
-- @node: responseProduct_pi_withDensity
lemma responseProduct_pi_withDensity {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : ι → α → ℝ) (hi : ∀ i, Integrable (f i) (μ i))
    (h0 : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i => (hi i).restrict))
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => h0 i (x i))))]
  rw [integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (h0 i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi i).restrict
    (Filter.Eventually.of_forall (h0 i))

/-- An unmatched recipient contributes one; a matched recipient contributes its donor mark. -/
-- @node: matchingResponseFactor
def matchingResponseFactor (n m : ℕ) (hfit : 2 * m ≤ n) (M : Matching m)
    (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) (y : ℝ) : ℝ :=
  match M.1 c with
  | none => 1
  | some j => 1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
      responseMark δ y *
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (z (donorOf n m hfit j))

/-- Given [the stated assumptions](hyp:hfit), [Each conditional recipient likelihood is Borel.](goal) -/
-- @node: matchingResponseFactor_measurable
@[fun_prop] lemma matchingResponseFactor_measurable (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) :
    Measurable (matchingResponseFactor n m hfit M z σ δ c) := by
  unfold matchingResponseFactor
  split <;> fun_prop

/-- Given [the stated assumptions](hyp:hfit), [Each conditional likelihood factor lies between zero and two.](goal) -/
-- @node: matchingResponseFactor_mem_Icc
lemma matchingResponseFactor_mem_Icc (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) (y : ℝ) :
    matchingResponseFactor n m hfit M z σ δ c y ∈ Set.Icc 0 2 := by
  have hh := responseMark_mem_Icc δ y
  unfold matchingResponseFactor
  split
  · norm_num
  · rename_i j hj
    cases σ <;> cases z (donorOf n m hfit j) <;>
      simp only [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf,
        Bool.false_eq_true, ↓reduceIte] <;> constructor <;> nlinarith [hh.1, hh.2]

/-- Given [the stated assumptions](hyp:hfit), [Bounded conditional likelihood factors are integrable under the balanced probability law.](goal) -/
-- @node: matchingResponseFactor_integrable
lemma matchingResponseFactor_integrable (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) :
    Integrable (matchingResponseFactor n m hfit M z σ δ c)
      (volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))) := by
  letI := balancedResponseLaw_probability δ
  apply (integrable_const (2 : ℝ)).mono' ?_ (Filter.Eventually.of_forall ?_)
  · fun_prop
  · intro y
    have hh := matchingResponseFactor_mem_Icc n m hfit M z σ δ c y
    simpa only [Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2

/-- The conditional response density uses the actual donor's assignment at matched rows. -/
-- @node: matchingResponseLaw
def matchingResponseLaw (n m : ℕ) (hfit : 2 * m ≤ n) (M : Matching m)
    (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) : Measure ℝ :=
  match M.1 c with
  | none => volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))
  | some j => volume.withDensity (fun y => ENNReal.ofReal
      (baselineDensity (y - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
          (z (donorOf n m hfit j)) * δ)))

/-- Given [the stated assumptions](hyp:hfit), [The scalar translated-law identity also holds with the product of causal and donor signs.](goal) -/
-- @node: matchingResponseLaw_eq_withDensity
lemma matchingResponseLaw_eq_withDensity (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) :
    matchingResponseLaw n m hfit M z σ δ c =
      (volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y))).withDensity
        (fun y => ENNReal.ofReal (matchingResponseFactor n m hfit M z σ δ c y)) := by
  unfold matchingResponseLaw matchingResponseFactor
  cases hc : M.1 c with
  | none => simp
  | some j =>
    cases σ <;> cases hz : z (donorOf n m hfit j)
    all_goals
      first
      | simpa [hz, baselineDensity,
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf] using
          shiftedResponseLaw_eq_withDensity δ true
      | simpa [hz, baselineDensity,
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf] using
          shiftedResponseLaw_eq_withDensity δ false

/-- Given [the stated assumptions](hyp:hfit), [Independent recipient tilts multiply, without removing any observed response coordinate.](goal) -/
-- @node: matchingResponseProduct_eq_withDensity
lemma matchingResponseProduct_eq_withDensity (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) :
    Measure.pi (matchingResponseLaw n m hfit M z σ δ) =
      (Measure.pi (fun _ : Fin m =>
        volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y)))).withDensity
      (fun y => ENNReal.ofReal (∏ c, matchingResponseFactor n m hfit M z σ δ c (y c))) := by
  change Measure.pi (fun c => matchingResponseLaw n m hfit M z σ δ c) = _
  simp_rw [matchingResponseLaw_eq_withDensity]
  exact responseProduct_pi_withDensity _ _
    (matchingResponseFactor_integrable n m hfit M z σ δ)
    (fun c y => (matchingResponseFactor_mem_Icc n m hfit M z σ δ c y).1)

/-- [The independent fair baseline shift generates the unmatched balanced response density.](goal) -/
-- @node: baseline_fairShiftLaw
lemma baseline_fairShiftLaw (δ : ℝ) :
    ((volume.withDensity (fun w => ENNReal.ofReal (baselineDensity w))).prod
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2))).map
      (fun p => p.1 + δ * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf p.2) =
    volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y)) := by
  have hm : Measurable (fun p : ℝ × Bool => p.1 + δ *
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf p.2) := by fun_prop
  unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.map_add _ _ hm, Measure.map_smul, Measure.map_smul,
    Measure.prod_dirac, Measure.prod_dirac,
    Measure.map_map hm measurable_prodMk_right, Measure.map_map hm measurable_prodMk_right]
  simp only [Function.comp_def,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf,
    Bool.false_eq_true, ↓reduceIte, mul_neg_one, mul_one]
  simp_rw [baselineDensity, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baseline_map_add_density]
  ext s hs
  have hp := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized δ
  have hn := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.translated_cosSqDensity_integrable_normalized (-δ)
  simp only [sub_neg_eq_add] at hn
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    withDensity_apply _ hs, withDensity_apply _ hs, withDensity_apply _ hs]
  simp only [sub_neg_eq_add]
  rw [← ofReal_integral_eq_lintegral_ofReal hn.1.restrict
      (Filter.Eventually.of_forall (fun y =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hp.1.restrict
      (Filter.Eventually.of_forall (fun y =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (balancedDensity_probability δ).2.2.1.restrict
      (Filter.Eventually.of_forall ((balancedDensity_probability δ).2.1))]
  simp only [balancedDensity, integral_div, integral_add hp.1.restrict hn.1.restrict,
    smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - 1/2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2),
    ← ENNReal.ofReal_add
      (mul_nonneg (by norm_num) (integral_nonneg (fun y =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg _)))
      (mul_nonneg (by norm_num) (integral_nonneg (fun y =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg _)))]
  congr 1
  ring

/-- The actual recipient response from its baseline and independent fair sign, conditional
on the matching and assignment. -/
-- @node: matchingResponseDraw
def matchingResponseDraw (n m : ℕ) (hfit : 2 * m ≤ n) (M : Matching m)
    (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) (p : ℝ × Bool) : ℝ :=
  match M.1 c with
  | none => p.1 + δ * CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf p.2
  | some j => p.1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
        (z (donorOf n m hfit j)) * δ

/-- Given [the stated assumptions](hyp:hfit), [Each conditional prior response draw is a measurable map.](goal) -/
-- @node: matchingResponseDraw_measurable
@[fun_prop] lemma matchingResponseDraw_measurable (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) :
    Measurable (matchingResponseDraw n m hfit M z σ δ c) := by
  unfold matchingResponseDraw
  split <;> fun_prop

/-- Given [the stated assumptions](hyp:hfit), [Pushing the scalar construction draws forward gives the declared conditional response law.](goal) -/
-- @node: matchingResponseDraw_law
lemma matchingResponseDraw_law (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) :
    ((volume.withDensity (fun w => ENNReal.ofReal (baselineDensity w))).prod
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2))).map
      (matchingResponseDraw n m hfit M z σ δ c) =
      matchingResponseLaw n m hfit M z σ δ c := by
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
    (1 / 2) (by constructor <;> norm_num)
  unfold matchingResponseDraw matchingResponseLaw
  cases hc : M.1 c with
  | none => exact baseline_fairShiftLaw δ
  | some j =>
    rw [show (fun p : ℝ × Bool => p.1 +
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
        (z (donorOf n m hfit j)) * δ) =
      (fun w : ℝ => w + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf
          (z (donorOf n m hfit j)) * δ) ∘ Prod.fst from rfl,
      ← Measure.map_map (by fun_prop) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
    exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baseline_map_add_density _

/-- Given [the stated assumptions](hyp:hfit), [The whole vector of actual independent prior draws has the product conditional response law.](goal) -/
-- @node: matchingResponseDraw_vector_law
lemma matchingResponseDraw_vector_law (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) :
    ((Measure.pi (fun _ : Fin m => volume.withDensity
        (fun w => ENNReal.ofReal (baselineDensity w)))).prod
      (Measure.pi (fun _ : Fin m =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2)))).map
      (fun p c => matchingResponseDraw n m hfit M z σ δ c (p.1 c, p.2 c)) =
    Measure.pi (matchingResponseLaw n m hfit M z σ δ) := by
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability
    (1 / 2) (by constructor <;> norm_num)
  letI : ∀ c : Fin m, SigmaFinite
      (((volume.withDensity (fun w => ENNReal.ofReal (baselineDensity w))).prod
        (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2))).map
        (matchingResponseDraw n m hfit M z σ δ c)) := fun c => by
    rw [matchingResponseDraw_law]
    unfold matchingResponseLaw
    split <;> infer_instance
  have ht := (measurePreserving_arrowProdEquivProdArrow ℝ Bool (Fin m)
    (fun _ => volume.withDensity (fun w => ENNReal.ofReal (baselineDensity w)))
    (fun _ => CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2))).symm.map_eq
  have hd : Measurable (fun p : Fin m → ℝ × Bool =>
      fun c => matchingResponseDraw n m hfit M z σ δ c (p c)) := by fun_prop
  rw [show (fun p : (Fin m → ℝ) × (Fin m → Bool) =>
      fun c => matchingResponseDraw n m hfit M z σ δ c (p.1 c, p.2 c)) =
      (fun p : Fin m → ℝ × Bool => fun c => matchingResponseDraw n m hfit M z σ δ c (p c)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ Bool (Fin m)).symm from rfl,
    ← Measure.map_map hd (MeasurableEquiv.measurable _), ht,
    Measure.pi_map_pi (fun c => (matchingResponseDraw_measurable n m hfit M z σ δ c).aemeasurable)]
  congr 1
  funext c
  exact matchingResponseDraw_law n m hfit M z σ δ c

/-- [A product over all recipients equals the product over their unique matching arrows.](goal) -/
-- @node: matching_option_product
lemma matching_option_product {m : ℕ} (M : Matching m) (f : Fin m × Fin m → ℝ) :
    (∏ c : Fin m, (M.1 c).elim 1 (fun j => f (j, c))) = ∏ e ∈ M.edges, f e := by
  have hinj : Set.InjOn Prod.snd (M.edges : Set (Fin m × Fin m)) := by
    intro e he e' he' h
    have ha := (Finset.mem_filter.mp he).2
    have hb := (Finset.mem_filter.mp he').2
    exact Prod.ext (Option.some.inj (ha.symm.trans (h ▸ hb))) h
  have hunit (c : Fin m) (hc : c ∉ M.edges.image Prod.snd) :
      (M.1 c).elim 1 (fun j => f (j,c)) = 1 := by
    cases h : M.1 c with
    | none => rfl
    | some j =>
      exact False.elim (hc (Finset.mem_image.mpr
        ⟨(j,c), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩))
  calc
    _ = ∏ c ∈ M.edges.image Prod.snd, (M.1 c).elim 1 (fun j => f (j,c)) :=
      (Finset.prod_subset (Finset.subset_univ _) (fun c _ hc => hunit c hc)).symm
    _ = ∏ e ∈ M.edges, (M.1 e.2).elim 1 (fun j => f (j,e.2)) :=
      Finset.prod_image hinj
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e he
      simp only [(Finset.mem_filter.mp he).2, Option.elim_some, Prod.eta]

/-- Given [the stated assumptions](hyp:hfit), [The recipient product is exactly the arrow-indexed polynomial factor in the paper.](goal) -/
-- @node: matchingResponseFactor_product
lemma matchingResponseFactor_product (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (y : Fin m → ℝ) :
    (∏ c, matchingResponseFactor n m hfit M z σ δ c (y c)) =
      ∏ e ∈ M.edges, (1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
        responseMark δ (y e.2) *
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (z (donorOf n m hfit e.1))) := by
  rw [← matching_option_product]
  apply Finset.prod_congr rfl
  intro c _
  cases hc : M.1 c <;> simp [matchingResponseFactor, hc]

/-- Given [the stated assumptions](hyp:hfit), [Conditional independent responses have the exact arrow-product likelihood against the
balanced reference, for all matchings and every actual donor assignment.](goal) -/
-- @node: matchingResponseProduct_arrow_density
lemma matchingResponseProduct_arrow_density (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) :
    Measure.pi (matchingResponseLaw n m hfit M z σ δ) =
      (Measure.pi (fun _ : Fin m =>
        volume.withDensity (fun y => ENNReal.ofReal (balancedDensity δ y)))).withDensity
      (fun y => ENNReal.ofReal (∏ e ∈ M.edges,
        (1 + CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ *
          responseMark δ (y e.2) *
          CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (z (donorOf n m hfit e.1))))) := by
  rw [matchingResponseProduct_eq_withDensity]
  simp_rw [matchingResponseFactor_product]

/-- Given [the stated assumptions](hyp:hfit), [A recipient's observed affine outcome is its scalar conditional construction draw.](goal) -/
-- @node: balancedSchedule_recipient_response
lemma balancedSchedule_recipient_response (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (w : Fin m → ℝ) (ε : Fin m → Bool)
    (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (c : Fin m) :
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome
      (balancedSchedule n m hfit σ δ (M,w,ε)) (recipientOf n m hfit c) z =
      matchingResponseDraw n m hfit M z σ δ c (w c, ε c) := by
  have ha : (balancedSchedule n m hfit σ δ (M,w,ε)).a (recipientOf n m hfit c) =
      if M.1 c = none then w c + δ *
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf (ε c)
      else w c - CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf σ * δ := by
    simp only [balancedSchedule, (recipientOf_injective n m hfit).eq_iff,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hedge (j : Fin n) : matchingEdge n m hfit M j (recipientOf n m hfit c) ↔
      ∃ a, j = donorOf n m hfit a ∧ M.1 c = some a := by
    constructor
    · rintro ⟨c',a,hc,hj,hM⟩
      have he := recipientOf_injective n m hfit hc
      subst c'
      exact ⟨a,hj,hM⟩
    · rintro ⟨a,hj,hM⟩
      exact ⟨c,a,rfl,hj,hM⟩
  unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome
  rw [ha]
  simp only [balancedSchedule, zero_mul, add_zero,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd]
  cases hc : M.1 c with
  | none =>
    have hnb : Finset.univ.filter (fun j => matchingEdge n m hfit M j (recipientOf n m hfit c)) = ∅ := by
      ext j
      simp [hedge, hc]
    simp [hnb, matchingResponseDraw, hc]
  | some a =>
    have hnb : Finset.univ.filter (fun j => matchingEdge n m hfit M j (recipientOf n m hfit c)) =
        {donorOf n m hfit a} := by
      ext j
      simp [hedge, hc]
    simp only [hnb, Finset.sum_singleton, hc, Option.some_ne_none, ↓reduceIte,
      matchingResponseDraw]
    cases σ <;> cases hz : z (donorOf n m hfit a) <;>
      simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.treatment,
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf] <;> ring

/-- Given [the stated assumptions](hyp:hfit,hi), [Donor and padding responses remain deterministically zero under the balanced schedule.](goal) -/
-- @node: balancedSchedule_nonrecipient_response
lemma balancedSchedule_nonrecipient_response (n m : ℕ) (hfit : 2 * m ≤ n)
    (ξ : PriorParam m) (z : Assign (Fin n)) (σ : Bool) (δ : ℝ) (i : Fin n)
    (hi : ∀ c, i ≠ recipientOf n m hfit c) :
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome
      (balancedSchedule n m hfit σ δ ξ) i z = 0 := by
  have he (j : Fin n) : ¬ matchingEdge n m hfit ξ.1 j i := by
    rintro ⟨c,a,hc,hj,hM⟩
    exact hi c hc
  simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome,
    balancedSchedule, hi, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd, he]

/-- Given [the stated assumptions](hyp:hfit), [The conditional response vector embeds back into the complete original record exactly.](goal) -/
-- @node: balancedRecord_eq_referenceRecord_responseDraw
lemma balancedRecord_eq_referenceRecord_responseDraw (n m : ℕ) (hfit : 2 * m ≤ n)
    (ξ : PriorParam m) (z : Assign (Fin n)) (H : Acq (Fin n)) (σ : Bool) (δ : ℝ) :
    recordOf (balancedSchedule n m hfit σ δ ξ) (z,H) =
      referenceRecordOf n m hfit (H,z,fun c =>
        matchingResponseDraw n m hfit ξ.1 z σ δ c (ξ.2.1 c, ξ.2.2 c)) := by
  refine Prod.ext (by rfl) ?_
  refine Prod.ext (by rfl) ?_
  funext i
  by_cases hi : ∃ c, i = recipientOf n m hfit c
  · obtain ⟨c,rfl⟩ := hi
    simp only [recordOf, referenceRecordOf,
      (recipientOf_injective n m hfit).eq_iff, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    exact balancedSchedule_recipient_response n m hfit ξ.1 ξ.2.1 ξ.2.2 z σ δ c
  · have hn : ∀ c, i ≠ recipientOf n m hfit c := fun c h => hi ⟨c,h⟩
    simp only [recordOf, referenceRecordOf, hn, ↓reduceIte, Finset.sum_const_zero]
    exact balancedSchedule_nonrecipient_response n m hfit ξ z σ δ i hn

/-- Given [the stated assumptions](hyp:hfit), [Conditioning on a matching and the complete fixed design leaves exactly the product
recipient law embedded in the full record, including all zero donor and padding responses.](goal) -/
-- @node: balancedRecord_fixedDesign_law
lemma balancedRecord_fixedDesign_law (n m : ℕ) (hfit : 2 * m ≤ n)
    (M : Matching m) (z : Assign (Fin n)) (H : Acq (Fin n)) (σ : Bool) (δ : ℝ) :
    ((Measure.pi (fun _ : Fin m => volume.withDensity
        (fun w => ENNReal.ofReal (baselineDensity w)))).prod
      (Measure.pi (fun _ : Fin m =>
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw (1 / 2)))).map
      (fun p => recordOf (balancedSchedule n m hfit σ δ (M,p)) (z,H)) =
    (Measure.pi (matchingResponseLaw n m hfit M z σ δ)).map
      (fun y => referenceRecordOf n m hfit (H,z,y)) := by
  rw [← matchingResponseDraw_vector_law n m hfit M z σ δ]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  exact balancedRecord_eq_referenceRecord_responseDraw n m hfit (M,p) z H σ δ

end CausalSmith.Experimentation.NoisygraphTtePrecision
