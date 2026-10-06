module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.Margins
public import Causalean.Stat.Minimax.Mixture.FiniteCells
public import Causalean.Stat.Minimax.Mixture.TwoChannel

/-! # Likelihood identities for the legal finite sign mixture -/

@[expose] public section
set_option linter.style.longLine false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- [The encoded cell set mass object](goal) is defined from [the supplied inputs](hyp:X,C,Ω,m,obs,A). -/

noncomputable def encodedCellSetMass {X C Ω : Type*}
    [MeasurableSpace X] [Fintype C] (ν : Measure X)
    (m : X → C → ℝ≥0∞) (obs : X → C → Ω) (A : Set Ω) : ℝ≥0∞ := by
  classical
  exact ∫⁻ x, ∑ c : C, if obs x c ∈ A then m x c else 0 ∂ν
/-- Given [the supplied inputs](hyp:X,C,Ω,Q,p,q,obs,L,hp,hobs,hL,hQ,hratio,hμ), [the encoded-cell measure is the stated density tilt of the base measure](goal). -/

lemma eq_withDensity_of_encodedCellSetMass {X C Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] [Fintype C]
    (ν : Measure X) (μ Q : Measure Ω) (p q : X → C → ℝ≥0∞)
    (obs : X → C → Ω) (L : Ω → ℝ)
    (hp : ∀ c, Measurable fun x => p x c)
    (hobs : ∀ c, Measurable fun x => obs x c)
    (hL : Measurable L)
    (hμ : ∀ A, MeasurableSet A →
      μ A = encodedCellSetMass ν p obs A)
    (hQ : ∀ A, MeasurableSet A →
      Q A = encodedCellSetMass ν q obs A)
    (hratio : ∀ x c,
      q x c = p x c * ENNReal.ofReal (L (obs x c))) :
    Q = μ.withDensity (fun z => ENNReal.ofReal (L z)) := by
  classical
  let k : X → Measure Ω :=
    fun x => ∑ c : C, p x c • Measure.dirac (obs x c)
  have hk : Measurable k := by
    unfold k
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply]
    apply Finset.measurable_fun_sum
    intro c hc
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hs]
    exact (hp c).mul (measurable_one.indicator (hs.preimage (hobs c)))
  have hμbind : μ = ν.bind k := by
    ext A hA
    rw [hμ A hA, Measure.bind_apply hA hk.aemeasurable]
    unfold encodedCellSetMass k
    apply lintegral_congr
    intro x
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ hA]
    apply Finset.sum_congr rfl
    intro c hc
    simp [Set.indicator]
  let f : Ω → ℝ≥0∞ := fun z => ENNReal.ofReal (L z)
  have hf : Measurable f := hL.ennreal_ofReal
  ext A hA
  have hg : Measurable (A.indicator f) := hf.indicator hA
  calc
    Q A = ∫⁻ x, ∑ c : C, if obs x c ∈ A then q x c else 0 ∂ν :=
      hQ A hA
    _ = ∫⁻ x, ∑ c : C,
        if obs x c ∈ A then p x c * f (obs x c) else 0 ∂ν := by
      apply lintegral_congr
      intro x
      apply Finset.sum_congr rfl
      intro c hc
      simp only [hratio]
      rfl
    _ = (μ.withDensity f) A := by
      rw [withDensity_apply _ hA, ← lintegral_indicator hA, hμbind]
      rw [Measure.lintegral_bind hk.aemeasurable hg.aemeasurable]
      apply lintegral_congr
      intro x
      change (∑ c : C,
        if obs x c ∈ A then p x c * f (obs x c) else 0) =
          ∫⁻ z, A.indicator f z ∂k x
      unfold k
      rw [lintegral_finsetSum_measure]
      simp_rw [lintegral_smul_measure, lintegral_dirac' _ hg]
      apply Finset.sum_congr rfl
      intro c hc
      simp [Set.indicator, smul_eq_mul]
/-- [The source cell object](goal) is defined without additional inputs. -/

abbrev SourceCell := Bool × Bool × Bool
/-- [The source cell mass object](goal) is defined from [the supplied inputs](hyp:a,u,v,c). -/

noncomputable def sourceCellMass (a u v : ℝ) (c : SourceCell) : ℝ :=
  assignmentWeight u c.1 * receiptOutcomeCell a c.1 c.2.1 c.2.2 +
    v * sign c.2.2 / 4
/-- [The source center mass object](goal) is defined from [the supplied inputs](hyp:a,c). -/

noncomputable def sourceCenterMass (a : ℝ) (c : SourceCell) : ℝ :=
  sourceCellMass a 0 0 c
/-- [The source direction object](goal) is defined from [the supplied inputs](hyp:a,c). -/

noncomputable def sourceDirection (a τ : ℝ) (c : SourceCell) : ℝ :=
  sign c.1 * receiptOutcomeCell a c.1 c.2.1 c.2.2 +
    τ * sign c.2.2 / 4
/-- [The source likelihood object](goal) is defined from [the supplied inputs](hyp:a,u,c). -/

noncomputable def sourceLikelihood (a τ u : ℝ) (c : SourceCell) : ℝ :=
  1 + u * sourceDirection a τ c / sourceCenterMass a c
/-- [The observed primitive mass object](goal) is defined from [the supplied inputs](hyp:a,u,v,z,d,y). -/

noncomputable def observedPrimitiveMass (a u v : ℝ)
    (z d y : Bool) : ℝ :=
  ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    if potentialReceipt (true, 0, d0, d1, boolReal y0, boolReal y1) z = d ∧
        potentialOutcome (true, 0, d0, d1, boolReal y0, boolReal y1) d = boolReal y then
      primitiveMass a u v d0 d1 y0 y1
    else 0
/-- Given [the supplied inputs](hyp:a,u,v,ha,hu,z,d,y), [the stated result about observed primitive mass eq holds](goal). -/

lemma observedPrimitiveMass_eq (a u v : ℝ) (ha : a ≠ 0)
    (hu : u ^ 2 ≠ 1 / 4) (z d y : Bool) :
    assignmentWeight u z * observedPrimitiveMass a u v z d y =
      sourceCellMass a u v (z, d, y) := by
  have hplus : 1 + u * 2 ≠ 0 := by
    intro h
    apply hu
    nlinarith
  have hminus : 1 - u * 2 ≠ 0 := by
    intro h
    apply hu
    nlinarith
  have hquad : 1 - u ^ 2 * 4 ≠ 0 := by
    intro h
    apply hu
    nlinarith
  have hplus' : 2 * u + 1 ≠ 0 := by
    intro h; apply hplus; linarith
  have hminus' : 1 - 2 * u ≠ 0 := by
    intro h; apply hminus; linarith
  have hminus'' : 2 * u - 1 ≠ 0 := by
    intro h; apply hminus; linarith
  have hquad' : 4 * u ^ 2 - 1 ≠ 0 := by
    intro h; apply hquad; linarith
  cases z <;> cases d <;> cases y <;>
    simp [observedPrimitiveMass, sourceCellMass, primitiveMass, potentialReceipt,
      potentialOutcome, receipt0, receipt1, outcome0, outcome1, boolReal,
      assignmentWeight, receiptOutcomeCell, receiptBase, complierMargin, sign] <;>
    field_simp [ha, hplus, hminus, hquad, hplus', hminus', hminus'', hquad'] <;>
    apply (mul_left_cancel₀ hplus) <;>
    field_simp [ha, hplus, hminus, hquad, hplus', hminus', hminus'', hquad'] <;>
    ring
/-- Given [the supplied inputs](hyp:a,u,c), [the stated result about source cell mass affine holds](goal). -/

lemma sourceCellMass_affine (a τ u : ℝ) (c : SourceCell) :
    sourceCellMass a u (τ * u) c =
      sourceCenterMass a c + u * sourceDirection a τ c := by
  rcases c with ⟨z, d, y⟩
  cases z <;> cases y <;> simp [sourceCellMass, sourceCenterMass, sourceDirection,
    assignmentWeight, sign] <;> ring
/-- Given [the supplied inputs](hyp:a,ha,c), [the stated result about source center mass pos holds](goal). -/

lemma sourceCenterMass_pos (a : ℝ) (ha : 0 < a ∧ a < 1)
    (c : SourceCell) : 0 < sourceCenterMass a c := by
  rcases c with ⟨z, d, y⟩
  cases z <;> cases d <;> cases y <;>
    simp [sourceCenterMass, sourceCellMass, assignmentWeight,
      receiptOutcomeCell, receiptBase, sign] <;> linarith
/-- Given [the supplied inputs](hyp:a), [the stated result about source center mass sum holds](goal). -/

lemma sourceCenterMass_sum (a : ℝ) :
    ∑ c : SourceCell, sourceCenterMass a c = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [sourceCenterMass, sourceCellMass, assignmentWeight,
    receiptOutcomeCell, receiptBase, sign]
  ring
/-- Given [the supplied inputs](hyp:a), [the stated result about source direction sum holds](goal). -/

lemma sourceDirection_sum (a τ : ℝ) :
    ∑ c : SourceCell, sourceDirection a τ c = 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [sourceDirection, receiptOutcomeCell, receiptBase, sign]
  ring
/-- [The source overlap coefficient object](goal) is defined from [the supplied inputs](hyp:a). -/

noncomputable def sourceOverlapCoefficient (a τ : ℝ) : ℝ :=
  4 + 4 * τ ^ 2 / (1 - a ^ 2)
/-- Given [the supplied inputs](hyp:a,ha,ha'), [the stated result about source direction sq sum holds](goal). -/

lemma sourceDirection_sq_sum (a τ : ℝ) (ha : a ≠ 1) (ha' : a ≠ -1) :
    (∑ c : SourceCell,
      sourceDirection a τ c ^ 2 / sourceCenterMass a c) =
      sourceOverlapCoefficient a τ := by
  have h₁ : 1 - a ≠ 0 := sub_ne_zero.mpr ha.symm
  have h₂ : 1 + a ≠ 0 := by
    intro h; apply ha'; linarith
  have h₃ : 1 - a ^ 2 ≠ 0 := by
    intro h
    apply mul_ne_zero h₁ h₂
    nlinarith
  have hinv₁ : (1 - a)⁻¹ = (1 + a) / (1 - a ^ 2) := by
    field_simp [h₁, h₃]
    ring
  have hinv₂ : (1 + a)⁻¹ = (1 - a) / (1 - a ^ 2) := by
    field_simp [h₂, h₃]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [sourceDirection, sourceCenterMass, sourceCellMass,
    assignmentWeight, receiptOutcomeCell, receiptBase, sign,
    sourceOverlapCoefficient]
  field_simp [h₁, h₂]
  ring_nf
  rw [hinv₁, hinv₂]
  field_simp [h₃]
  ring
/-- Given [the supplied inputs](hyp:a,u,w,ha), [the stated result about source likelihood pair sum holds](goal). -/

lemma sourceLikelihood_pair_sum (a τ u w : ℝ)
    (ha : 0 < a ∧ a < 1) :
    ∑ c : SourceCell, sourceCenterMass a c *
      (sourceLikelihood a τ u c * sourceLikelihood a τ w c) =
      1 + u * w * sourceOverlapCoefficient a τ := by
  have hpos (c : SourceCell) := sourceCenterMass_pos a ha c
  simp_rw [sourceLikelihood]
  have hexpand (c : SourceCell) :
      sourceCenterMass a c *
        ((1 + u * sourceDirection a τ c / sourceCenterMass a c) *
          (1 + w * sourceDirection a τ c / sourceCenterMass a c)) =
        sourceCenterMass a c + (u + w) * sourceDirection a τ c +
          u * w * (sourceDirection a τ c ^ 2 / sourceCenterMass a c) := by
    field_simp [ne_of_gt (hpos c)]
    ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sourceCenterMass_sum]
  simp_rw [← Finset.mul_sum]
  rw [sourceDirection_sum,
    sourceDirection_sq_sum a τ (ne_of_lt ha.2) (by linarith [ha.1])]
  ring
/-- [The source cell observation object](goal) is defined from [the supplied inputs](hyp:x,c). -/

noncomputable def sourceCellObservation (x : ℝ) (c : SourceCell) : SourceObs :=
  (x, c.1, c.2.1, boolReal c.2.2)
/-- [The explicit source law object](goal) is defined from [the supplied inputs](hyp:a,u,v). -/

noncomputable def explicitSourceLaw (a : ℝ) (u v : ℝ → ℝ) :
    Measure SourceObs :=
  (volume.restrict covariateSpace).bind fun x =>
    ∑ c : SourceCell, ENNReal.ofReal (sourceCellMass a (u x) (v x) c) •
      Measure.dirac (sourceCellObservation x c)
/-- Given [the supplied inputs](hyp:K,hK,i,j,x,hi,hj), [the stated result about cell mem unique holds](goal). -/

lemma cell_mem_unique (K : ℕ) (hK : 0 < K) (i j : Fin K) (x : ℝ)
    (hi : x ∈ cell K i) (hj : x ∈ cell K j) : i = j := by
  apply Fin.ext
  by_contra hne
  have hlt : i.val < j.val ∨ j.val < i.val := Nat.lt_or_gt_of_ne hne
  rcases hlt with hij | hji
  · have hinot : i.val + 1 ≠ K := by omega
    have hi' : (i.val : ℝ) / K ≤ x ∧
        x < ((i.val : ℝ) + 1) / K := by
      unfold cell at hi
      simp [hinot] at hi
      exact hi
    have hjlo : (j.val : ℝ) / K ≤ x := by
      unfold cell at hj
      split_ifs at hj <;> exact hj.1
    have hcast : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    have hKreal : (0 : ℝ) ≤ K := by exact_mod_cast Nat.zero_le K
    have hdiv : ((i.val : ℝ) + 1) / K ≤ (j.val : ℝ) / K :=
      div_le_div_of_nonneg_right hcast hKreal
    linarith
  · have hjnot : j.val + 1 ≠ K := by omega
    have hj' : (j.val : ℝ) / K ≤ x ∧
        x < ((j.val : ℝ) + 1) / K := by
      unfold cell at hj
      simp [hjnot] at hj
      exact hj
    have hilo : (i.val : ℝ) / K ≤ x := by
      unfold cell at hi
      split_ifs at hi <;> exact hi.1
    have hcast : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hji
    have hKreal : (0 : ℝ) ≤ K := by exact_mod_cast Nat.zero_le K
    have hdiv : ((j.val : ℝ) + 1) / K ≤ (i.val : ℝ) / K :=
      div_le_div_of_nonneg_right hcast hKreal
    linarith
/-- Given [the supplied inputs](hyp:cStar,n,sgn,x), [the stated result about tiled perturbation abs le abs lower height holds](goal). -/

lemma tiledPerturbation_abs_le_abs_lowerHeight (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (x : ℝ) :
    |tiledPerturbation cStar n sgn x| ≤ |lowerHeight cStar n| := by
  classical
  by_cases hKzero : lowerCells n = 0
  · have hempty : IsEmpty (Fin (lowerCells n)) :=
      Fintype.card_eq_zero_iff.mp (by simpa using hKzero)
    letI := hempty
    simp [tiledPerturbation]
  have hK : 0 < lowerCells n := Nat.pos_of_ne_zero hKzero
  by_cases hex : ∃ i : Fin (lowerCells n), x ∈ cell (lowerCells n) i
  · obtain ⟨i, hi⟩ := hex
    unfold tiledPerturbation
    rw [Finset.sum_eq_single i]
    · simp only [hi, ↓reduceIte]
      rw [abs_mul, abs_mul]
      have hs : |sign (sgn i)| = 1 := by cases sgn i <;> simp [sign]
      have hb : |bump ((lowerCells n : ℝ) * x - i.val)| ≤ 1 := by
        simpa [bump] using Real.abs_sin_le_one
          (2 * Real.pi * ((lowerCells n : ℝ) * x - i.val))
      rw [hs, mul_one]
      exact mul_le_of_le_one_right (abs_nonneg _) hb
    · intro j hj hji
      have hnot : x ∉ cell (lowerCells n) j := by
        intro hx
        exact hji (cell_mem_unique _ hK j i x hx hi)
      simp [hnot]
    · simp
  · have hnone (i : Fin (lowerCells n)) : x ∉ cell (lowerCells n) i := by
      intro hi
      exact hex ⟨i, hi⟩
    simp [tiledPerturbation, hnone]
/-- Given [the supplied inputs](hyp:cStar,n,sgn,x,hc), [the stated result about tiled perturbation abs le lower height holds](goal). -/

lemma tiledPerturbation_abs_le_lowerHeight (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (x : ℝ) (hc : 0 ≤ cStar) :
    |tiledPerturbation cStar n sgn x| ≤ lowerHeight cStar n := by
  have hh : 0 ≤ lowerHeight cStar n := by
    unfold lowerHeight
    positivity
  simpa [abs_of_nonneg hh] using
    tiledPerturbation_abs_le_abs_lowerHeight cStar n sgn x

/-- Admissibility bounds the covariate-indexed assignment probabilities.  Under [the displayed assumptions and inputs](hyp:a,cStar,n,hDomain,sgn,z,x,hx), [the stated conclusion holds](goal). -/
-- @node: assignmentWeight_tiled_mem_Icc
lemma assignmentWeight_tiled_mem_Icc (a cStar : ℝ) (n : ℕ)
    (hDomain : LowerExperimentDomain n a cStar)
    (sgn : Fin (lowerCells n) → Bool) (z : Bool) (x : ℝ) (hx : x ∈ covariateSpace) :
    assignmentWeight (tiledPerturbation cStar n sgn x) z ∈ Icc (0 : ℝ) 1 := by -- @realizes e_z^{(\lambda)}(covariate-indexed range from tiled perturbation and Adm)
  apply assignmentWeight_mem_Icc
  apply abs_le.mp
  have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hDomain.2.1.le
  exact le_trans hu (le_trans hDomain.2.2.1 (by norm_num))
/-- Given [the supplied inputs](hyp:b,u,v,hb,hu,hv,hadm,d,y), [the stated result about complier margin nonneg of bounds holds](goal). -/

lemma complierMargin_nonneg_of_bounds (b u v : ℝ)
    (hb : 0 < b) (hu : |u| ≤ 3 / 16) (hv : |v| ≤ |u|)
    (hadm : u ^ 2 ≤ b * (1 / 4 - u ^ 2)) (d y : Bool) :
    0 ≤ complierMargin b u v d y := by
  have hu2 : u ^ 2 ≤ (3 / 16 : ℝ) ^ 2 := by
    apply (sq_le_sq).2
    simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 16)] using hu
  have hden : 0 < (1 / 4 : ℝ) - u ^ 2 := by nlinarith
  have huv : |u * v| ≤ u ^ 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg u, sq_abs u]
  have hlower : -(b * (1 / 4 - u ^ 2)) ≤ u * v :=
    neg_le_of_abs_le (le_trans huv hadm)
  have hupper : u * v ≤ b * (1 / 4 - u ^ 2) := by
    exact le_trans (le_abs_self _) (le_trans huv hadm)
  have hden2 : 0 < 2 * ((1 / 4 : ℝ) - u ^ 2) := by positivity
  have hflo : -(b / 2) ≤ u * v / (2 * (1 / 4 - u ^ 2)) := by
    rw [le_div_iff₀ hden2]
    nlinarith
  have hfhi : u * v / (2 * (1 / 4 - u ^ 2)) ≤ b / 2 := by
    rw [div_le_iff₀ hden2]
    nlinarith
  cases d <;> cases y <;> simp [complierMargin, sign, neg_div] <;> linarith
/-- Given [the supplied inputs](hyp:b,u,v,hb,hu,hv,hadm,d0,d1,y0,y1), [the stated result about primitive mass nonneg of bounds holds](goal). -/

lemma primitiveMass_nonneg_of_bounds (b u v : ℝ)
    (hb : 0 < b ∧ b ≤ 1 / 4)
    (hu : |u| ≤ 3 / 16) (hv : |v| ≤ |u|)
    (hadm : u ^ 2 ≤ b * (1 / 4 - u ^ 2))
    (d0 d1 y0 y1 : Bool) :
    0 ≤ primitiveMass b u v d0 d1 y0 y1 := by
  have hu_lo : -(3 / 16 : ℝ) ≤ u := (abs_le.mp hu).1
  have hu_hi : u ≤ 3 / 16 := (abs_le.mp hu).2
  have he0 : 0 < assignmentWeight u false := by
    simp [assignmentWeight]
    linarith
  have he1 : 0 < assignmentWeight u true := by
    simp [assignmentWeight]
    linarith
  have hvbound : |v| ≤ 3 / 16 := le_trans hv hu
  have hvlo : -(3 / 16 : ℝ) ≤ v := (abs_le.mp hvbound).1
  have hvhi : v ≤ 3 / 16 := (abs_le.mp hvbound).2
  have hd0 : 0 < 4 * ((1 / 2 : ℝ) - u) := by nlinarith
  have hd1 : 0 < 4 * ((1 / 2 : ℝ) + u) := by nlinarith
  have hf0lo : -(3 / 20 : ℝ) ≤ v / (4 * (1 / 2 - u)) := by
    rw [le_div_iff₀ hd0]
    nlinarith
  have hf0hi : v / (4 * (1 / 2 - u)) ≤ 3 / 20 := by
    rw [div_le_iff₀ hd0]
    nlinarith
  have hf1lo : -(3 / 20 : ℝ) ≤ v / (4 * (1 / 2 + u)) := by
    rw [le_div_iff₀ hd1]
    nlinarith
  have hf1hi : v / (4 * (1 / 2 + u)) ≤ 3 / 20 := by
    rw [div_le_iff₀ hd1]
    nlinarith
  have hm (d y : Bool) : 0 ≤ complierMargin b u v d y :=
    complierMargin_nonneg_of_bounds b u v hb.1 hu hv hadm d y
  simp only [primitiveMass]
  split_ifs
  · exact div_nonneg (mul_nonneg (hm false y0) (hm true y1)) hb.1.le
  · cases y1 <;> simp [receiptBase, sign, assignmentWeight, neg_div] <;>
      linarith
  · cases y0 <;> simp [receiptBase, sign, assignmentWeight, neg_div] <;>
      linarith
  · exact le_rfl
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hb,hAdm,x,d0,d1,y0,y1,hτ), [every lower-construction latent-cell mass is nonnegative](goal). -/

lemma lowerMass_nonneg (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (x : ℝ) (d0 d1 y0 y1 : Bool) :
    0 ≤ lowerMass a n cStar τ sgn x d0 d1 y0 y1 := by
  let u := tiledPerturbation cStar n sgn x
  let v := coupledPerturbation cStar τ n sgn x
  have hh0 : 0 ≤ lowerHeight cStar n := by
    unfold lowerHeight
    exact mul_nonneg hAdm.1.le (Real.rpow_nonneg (by positivity) _)
  have hu : |u| ≤ lowerHeight cStar n := by
    exact tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
  have hu_small : |u| ≤ 3 / 16 := le_trans hu hAdm.2.1
  have hτabs : |τ| ≤ 1 := abs_le.mpr hτ
  have hv : |v| ≤ |u| := by
    unfold v coupledPerturbation
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg u) hτabs
  have hu_sq : u ^ 2 ≤ lowerHeight cStar n ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hh0] using hu
  have hadm : u ^ 2 ≤ actualStrength a n * (1 / 4 - u ^ 2) := by
    have hmono : actualStrength a n *
        (1 / 4 - lowerHeight cStar n ^ 2) ≤
        actualStrength a n * (1 / 4 - u ^ 2) := by
      gcongr
      exact hb.1.le
    exact le_trans (le_trans hu_sq hAdm.2.2) hmono
  exact primitiveMass_nonneg_of_bounds (actualStrength a n) u v hb
    hu_small hv hadm d0 d1 y0 y1
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hAdm,x,z), [the stated result about lower assignment weight mem icc holds](goal). -/

lemma lowerAssignmentWeight_mem_Icc (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hAdm : LowerAdmissible n a cStar) (x : ℝ) (z : Bool) :
    assignmentWeight (tiledPerturbation cStar n sgn x) z ∈ Icc (0 : ℝ) 1 := by
  apply assignmentWeight_mem_Icc
  have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
  apply abs_le.mp
  exact le_trans hu (le_trans hAdm.2.1 (by norm_num))
/-- [The lower assignment kernel object](goal) is defined from [the supplied inputs](hyp:cStar,n,sgn,o). -/

noncomputable def lowerAssignmentKernel (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (o : FullData) : Measure Assigned :=
  ∑ z : Bool,
    ENNReal.ofReal
        (assignmentWeight (tiledPerturbation cStar n sgn (covariate o)) z) •
      Measure.dirac (o, z, potentialReceipt o z,
        potentialOutcome o (potentialReceipt o z))
/-- Given [the supplied inputs](hyp:cStar,n,sgn), [the stated result about tiled perturbation measurable holds](goal). -/

lemma tiledPerturbation_measurable (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) :
    Measurable (tiledPerturbation cStar n sgn) := by
  classical
  unfold tiledPerturbation
  apply Finset.measurable_fun_sum
  intro i hi
  apply Measurable.ite
  · unfold cell
    split_ifs <;> measurability
  · unfold bump
    fun_prop
  · exact measurable_const
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,d0,d1,y0,y1), [the stated result about lower mass measurable holds](goal). -/

lemma lowerMass_measurable (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) (d0 d1 y0 y1 : Bool) :
    Measurable fun x => lowerMass a n cStar τ sgn x d0 d1 y0 y1 := by
  unfold lowerMass primitiveMass complierMargin coupledPerturbation
    assignmentWeight receiptBase sign
  have hu := tiledPerturbation_measurable cStar n sgn
  split_ifs <;> fun_prop
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn), [the stated result about lower primitive kernel measurable holds](goal). -/

lemma lowerPrimitiveKernel_measurable (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool) :
    Measurable fun x => primitiveKernel true x (lowerMass a n cStar τ sgn) := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp only [primitiveKernel, Measure.finsetSum_apply]
  apply Finset.measurable_fun_sum
  intro d0 hd0
  apply Finset.measurable_fun_sum
  intro d1 hd1
  apply Finset.measurable_fun_sum
  intro y0 hy0
  apply Finset.measurable_fun_sum
  intro y1 hy1
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  exact (lowerMass_measurable a n cStar τ sgn d0 d1 y0 y1).ennreal_ofReal.mul
    (measurable_one.indicator (hA.preimage (by fun_prop)))
/-- Given [the supplied inputs](hyp:n,cStar,sgn), [the stated result about lower assignment kernel measurable holds](goal). -/

lemma lowerAssignmentKernel_measurable (n : ℕ) (cStar : ℝ)
    (sgn : Fin (lowerCells n) → Bool) :
    Measurable fun o : FullData =>
      ENNReal.ofReal (assignmentWeight (tiledPerturbation cStar n sgn (covariate o)) true) •
          Measure.dirac (o, true, potentialReceipt o true,
            potentialOutcome o (potentialReceipt o true)) +
        ENNReal.ofReal
            (1 - assignmentWeight (tiledPerturbation cStar n sgn (covariate o)) true) •
          Measure.dirac (o, false, potentialReceipt o false,
            potentialOutcome o (potentialReceipt o false)) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hA]
  have hu : Measurable fun o : FullData =>
      tiledPerturbation cStar n sgn (covariate o) :=
    (tiledPerturbation_measurable cStar n sgn).comp (by
      unfold covariate
      fun_prop)
  have hw : Measurable fun o : FullData =>
      assignmentWeight (tiledPerturbation cStar n sgn (covariate o)) true := by
    unfold assignmentWeight
    simp
    exact measurable_const.add hu
  have hp₁ : Measurable fun o : FullData =>
      (o, true, potentialReceipt o true,
        potentialOutcome o (potentialReceipt o true)) := by
    simp only [potentialReceipt, Bool.true_eq, ↓reduceIte]
    have hr : Measurable fun o : FullData => receipt1 o := by
      unfold receipt1
      fun_prop
    have hy : Measurable fun o : FullData =>
        if receipt1 o then outcome1 o else outcome0 o := by
      apply Measurable.ite
      · exact (measurableSet_singleton true).preimage hr
      · unfold outcome1
        fun_prop
      · unfold outcome0
        fun_prop
    exact measurable_id.prodMk
      (measurable_const.prodMk (hr.prodMk hy))
  have hp₀ : Measurable fun o : FullData =>
      (o, false, potentialReceipt o false,
        potentialOutcome o (potentialReceipt o false)) := by
    simp only [potentialReceipt, Bool.false_eq, ↓reduceIte]
    have hr : Measurable fun o : FullData => receipt0 o := by
      unfold receipt0
      fun_prop
    have hy : Measurable fun o : FullData =>
        if receipt0 o then outcome1 o else outcome0 o := by
      apply Measurable.ite
      · exact (measurableSet_singleton true).preimage hr
      · unfold outcome1
        fun_prop
      · unfold outcome0
        fun_prop
    exact measurable_id.prodMk
      (measurable_const.prodMk (hr.prodMk hy))
  exact ((hw.ennreal_ofReal.mul
    (measurable_one.indicator (hA.preimage hp₁))).add
      ((measurable_const.sub hw).ennreal_ofReal.mul
        (measurable_one.indicator (hA.preimage hp₀))))
/-- Given [the supplied inputs](hyp:a,u,v,ha,hu,hm,he,z,d,y), [the stated result about observed primitive ennmass eq holds](goal). -/

lemma observedPrimitiveENNMass_eq (a u v : ℝ)
    (ha : a ≠ 0) (hu : u ^ 2 ≠ 1 / 4)
    (hm : ∀ d0 d1 y0 y1 : Bool,
      0 ≤ primitiveMass a u v d0 d1 y0 y1)
    (he : ∀ z : Bool, 0 ≤ assignmentWeight u z)
    (z d y : Bool) :
    (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      if potentialReceipt (true, 0, d0, d1, boolReal y0, boolReal y1) z = d ∧
          potentialOutcome (true, 0, d0, d1, boolReal y0, boolReal y1) d = boolReal y then
        ENNReal.ofReal (primitiveMass a u v d0 d1 y0 y1) *
          ENNReal.ofReal (assignmentWeight u z)
      else 0) =
      ENNReal.ofReal (sourceCellMass a u v (z, d, y)) := by
  rw [← observedPrimitiveMass_eq a u v ha hu z d y]
  rw [ENNReal.ofReal_mul (he z)]
  unfold observedPrimitiveMass
  have hr (d0 d1 y0 y1 : Bool) : 0 ≤
      (if potentialReceipt (true, 0, d0, d1, boolReal y0, boolReal y1) z = d ∧
          potentialOutcome (true, 0, d0, d1, boolReal y0, boolReal y1) d = boolReal y then
        primitiveMass a u v d0 d1 y0 y1 else 0) := by
    split_ifs
    · exact hm d0 d1 y0 y1
    · exact le_rfl
  rw [ENNReal.ofReal_sum_of_nonneg (fun d0 _ => Finset.sum_nonneg fun d1 _ =>
    Finset.sum_nonneg fun y0 _ => Finset.sum_nonneg fun y1 _ => hr d0 d1 y0 y1)]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun d1 _ =>
    Finset.sum_nonneg fun y0 _ => Finset.sum_nonneg fun y1 _ => hr _ d1 y0 y1)]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun y0 _ =>
    Finset.sum_nonneg fun y1 _ => hr _ _ y0 y1)]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun y1 _ => hr _ _ _ y1)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d0 hd0
  apply Finset.sum_congr rfl
  intro d1 hd1
  apply Finset.sum_congr rfl
  intro y0 hy0
  apply Finset.sum_congr rfl
  intro y1 hy1
  split_ifs with h
  · ac_rfl
  · simp
/-- Given [the supplied inputs](hyp:Z,C,w,obs,φ), [summing over observations can be regrouped as the corresponding finite weighted cell sum](goal). -/

lemma finite_sum_group_by_weighted {Z C : Type*} [Fintype Z] [Fintype C]
    [DecidableEq C] (w : Z → ℝ≥0∞) (obs : Z → C) (φ : C → ℝ≥0∞) :
    (∑ z : Z, w z * φ (obs z)) =
      ∑ c : C, (∑ z : Z, if obs z = c then w z else 0) * φ c := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_eq_single (obs z)]
  · simp
  · intro c hc hne
    have hne' : obs z ≠ c := Ne.symm hne
    simp [hne']
  · simp
/-- [The source latent object](goal) is defined without additional inputs. -/

abbrev SourceLatent := ((((Bool × Bool) × Bool) × Bool) × Bool)
/-- [The source latent cell object](goal) is defined without additional inputs. -/

def sourceLatentCell : SourceLatent → SourceCell
  | ((((d0, d1), y0), y1), z) =>
      (z, if z then d1 else d0,
        if (if z then d1 else d0) then y1 else y0)
/-- [The source latent weight object](goal) is defined from [the supplied inputs](hyp:a,u,v). -/

noncomputable def sourceLatentWeight (a u v : ℝ) : SourceLatent → ℝ≥0∞
  | ((((d0, d1), y0), y1), z) =>
      ENNReal.ofReal (primitiveMass a u v d0 d1 y0 y1) *
        ENNReal.ofReal (assignmentWeight u z)
/-- Given [the supplied inputs](hyp:a,u,v,ha,hu,hm,he,c), [the stated result about source latent weight group eq holds](goal). -/

lemma sourceLatentWeight_group_eq (a u v : ℝ)
    (ha : a ≠ 0) (hu : u ^ 2 ≠ 1 / 4)
    (hm : ∀ d0 d1 y0 y1 : Bool,
      0 ≤ primitiveMass a u v d0 d1 y0 y1)
    (he : ∀ z : Bool, 0 ≤ assignmentWeight u z) (c : SourceCell) :
    (∑ q : SourceLatent,
      if sourceLatentCell q = c then sourceLatentWeight a u v q else 0) =
      ENNReal.ofReal (sourceCellMass a u v c) := by
  rcases c with ⟨z, d, y⟩
  rw [← observedPrimitiveENNMass_eq a u v ha hu hm he z d y]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [sourceLatentCell, sourceLatentWeight, potentialReceipt,
    potentialOutcome, receipt0, receipt1, outcome0, outcome1]
  apply Finset.sum_congr rfl
  intro d0 hd0
  apply Finset.sum_congr rfl
  intro d1 hd1
  apply Finset.sum_congr rfl
  intro y0 hy0
  apply Finset.sum_congr rfl
  intro y1 hy1
  cases z <;> cases d <;> cases y <;> cases d0 <;> cases d1 <;>
    cases y0 <;> cases y1 <;> simp [boolReal]
/-- Given [the supplied inputs](hyp:a,u,v,φ), [the source latent-cell sum expands into its explicit finite expression](goal). -/

lemma sourceLatent_sum_expand (a u v : ℝ) (φ : SourceCell → ℝ≥0∞) :
    (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool, ∑ z : Bool,
      ENNReal.ofReal (primitiveMass a u v d0 d1 y0 y1) *
        ENNReal.ofReal (assignmentWeight u z) *
          φ (z, if z then d1 else d0,
            if (if z then d1 else d0) then y1 else y0)) =
      ∑ q : SourceLatent, sourceLatentWeight a u v q * φ (sourceLatentCell q) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rfl
/-- Given [the supplied inputs](hyp:x,d0,d1,y0,y1,z), [the stated result about observe assigned latent holds](goal). -/

lemma observe_assigned_latent (x : ℝ) (d0 d1 y0 y1 z : Bool) :
    observeSource
        ((true, x, d0, d1, boolReal y0, boolReal y1), z,
          potentialReceipt (true, x, d0, d1, boolReal y0, boolReal y1) z,
          potentialOutcome (true, x, d0, d1, boolReal y0, boolReal y1)
            (potentialReceipt (true, x, d0, d1, boolReal y0, boolReal y1) z)) =
      sourceCellObservation x
        (z, if z then d1 else d0,
          if (if z then d1 else d0) then y1 else y0) := by
  cases z <;> cases d0 <;> cases d1 <;>
    simp [observeSource, sourceCellObservation, covariate, potentialReceipt,
      potentialOutcome, receipt0, receipt1, outcome0, outcome1, boolReal]
/-- Given [the supplied inputs](hyp:c), [the stated result about source cell observation measurable holds](goal). -/

lemma sourceCellObservation_measurable (c : SourceCell) :
    Measurable fun x => sourceCellObservation x c := by
  exact measurable_id.prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_const))
/-- Given [the supplied inputs](hyp:cStar,n,sgn), [the stated result about measurable lower assignment kernel holds](goal). -/

lemma measurable_lowerAssignmentKernel (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) :
    Measurable (lowerAssignmentKernel cStar n sgn) := by
  have heq : lowerAssignmentKernel cStar n sgn = fun o =>
      ENNReal.ofReal (assignmentWeight
          (tiledPerturbation cStar n sgn (covariate o)) true) •
        Measure.dirac (o, true, potentialReceipt o true,
          potentialOutcome o (potentialReceipt o true)) +
      ENNReal.ofReal (1 - assignmentWeight
          (tiledPerturbation cStar n sgn (covariate o)) true) •
        Measure.dirac (o, false, potentialReceipt o false,
          potentialOutcome o (potentialReceipt o false)) := by
    funext o
    simp [lowerAssignmentKernel, Fintype.sum_bool, assignmentWeight,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    congr 2
    norm_num
    ring
  rw [heq]
  exact lowerAssignmentKernel_measurable n cStar sgn
/-- Given [the supplied inputs](hyp:cStar,n,sgn), [the stated result about assignment kernel eq lower holds](goal). -/

lemma assignmentKernel_eq_lower (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) :
    (fun o : FullData =>
      ENNReal.ofReal (1 / 2 + tiledPerturbation cStar n sgn (covariate o)) •
          Measure.dirac (o, true, potentialReceipt o true,
            potentialOutcome o (potentialReceipt o true)) +
        ENNReal.ofReal (1 - (1 / 2 +
            tiledPerturbation cStar n sgn (covariate o))) •
          Measure.dirac (o, false, potentialReceipt o false,
            potentialOutcome o (potentialReceipt o false))) =
      lowerAssignmentKernel cStar n sgn := by
  funext o
  ext A hA
  simp [lowerAssignmentKernel, Fintype.sum_bool, assignmentWeight,
    Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hA,
    smul_eq_mul]
  congr 2
  norm_num
  ring
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hm,he,hb0,hu0,x,A,hA), [the stated result about fixed source kernel apply holds](goal). -/

lemma fixedSourceKernel_apply (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hm : ∀ x d0 d1 y0 y1,
      0 ≤ lowerMass a n cStar τ sgn x d0 d1 y0 y1)
    (he : ∀ x z, 0 ≤ assignmentWeight
      (tiledPerturbation cStar n sgn x) z)
    (hb0 : 0 < actualStrength a n)
    (hu0 : ∀ x, tiledPerturbation cStar n sgn x ^ 2 ≠ 1 / 4)
    (x : ℝ) (A : Set SourceObs) (hA : MeasurableSet A) :
    (Measure.map observeSource
      ((primitiveKernel true x (lowerMass a n cStar τ sgn)).bind
        (lowerAssignmentKernel cStar n sgn))) A =
      ∑ c : SourceCell,
        ENNReal.ofReal (sourceCellMass (actualStrength a n)
          (tiledPerturbation cStar n sgn x)
          (coupledPerturbation cStar τ n sgn x) c) *
          A.indicator 1 (sourceCellObservation x c) := by
  classical
  have hobs : Measurable observeSource := by
    unfold observeSource covariate
    fun_prop
  rw [Measure.map_apply hobs hA]
  rw [Measure.bind_apply (hA.preimage hobs)
    (measurable_lowerAssignmentKernel cStar n sgn).aemeasurable]
  simp only [primitiveKernel, lintegral_finsetSum_measure,
    lintegral_smul_measure, lowerAssignmentKernel, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hA.preimage hobs)]
  simp_rw [lintegral_dirac, Finset.mul_sum, ← mul_assoc]
  simp only [covariate, lowerMass, Set.indicator, Set.mem_preimage, Pi.one_apply]
  simp_rw [observe_assigned_latent]
  rw [sourceLatent_sum_expand (actualStrength a n)
    (tiledPerturbation cStar n sgn x)
    (coupledPerturbation cStar τ n sgn x)
    (fun c => if sourceCellObservation x c ∈ A then 1 else 0)]
  rw [finite_sum_group_by_weighted
    (sourceLatentWeight (actualStrength a n)
      (tiledPerturbation cStar n sgn x)
      (coupledPerturbation cStar τ n sgn x))
    sourceLatentCell
    (fun c => if sourceCellObservation x c ∈ A then 1 else 0)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [sourceLatentWeight_group_eq]
  · exact ne_of_gt hb0
  · exact hu0 x
  · exact hm x
  · exact he x
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hm,he,hb0,hu0), [the stated result about source law eq explicit of nonneg holds](goal). -/

lemma sourceLaw_eq_explicit_of_nonneg (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hm : ∀ x d0 d1 y0 y1,
      0 ≤ lowerMass a n cStar τ sgn x d0 d1 y0 y1)
    (he : ∀ x z, 0 ≤ assignmentWeight
      (tiledPerturbation cStar n sgn x) z)
    (hb0 : 0 < actualStrength a n)
    (hu0 : ∀ x, tiledPerturbation cStar n sgn x ^ 2 ≠ 1 / 4) :
    Measure.map observeSource
      (assignedFrom
        (primitivePopulation true (fun _ => 1)
          (lowerMass a n cStar τ sgn))
        (fun x => 1 / 2 + tiledPerturbation cStar n sgn x)) =
      explicitSourceLaw (actualStrength a n)
        (tiledPerturbation cStar n sgn)
        (coupledPerturbation cStar τ n sgn) := by
  have hp := lowerPrimitiveKernel_measurable a n cStar τ sgn
  have hk := measurable_lowerAssignmentKernel cStar n sgn
  have hpk : Measurable fun x =>
      (primitiveKernel true x (lowerMass a n cStar τ sgn)).bind
        (lowerAssignmentKernel cStar n sgn) :=
    (Measure.measurable_bind' hk).comp hp
  unfold assignedFrom primitivePopulation
  rw [assignmentKernel_eq_lower]
  rw [Measure.bind_bind hp.aemeasurable hk.aemeasurable]
  have hbase : (volume.restrict covariateSpace).withDensity
      (fun _ : ℝ => ENNReal.ofReal 1) = volume.restrict covariateSpace := by
    have hf : (fun _ : ℝ => ENNReal.ofReal 1) = (1 : ℝ → ℝ≥0∞) := by
      funext x
      simp
    rw [hf, withDensity_one]
  rw [hbase]
  ext A hA
  have hobs : Measurable observeSource := by
    unfold observeSource covariate
    fun_prop
  rw [Measure.map_apply hobs hA]
  rw [Measure.bind_apply (hA.preimage hobs) hpk.aemeasurable]
  unfold explicitSourceLaw
  rw [Measure.bind_apply hA]
  · apply lintegral_congr
    intro x
    simpa only [Measure.map_apply hobs hA, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA] using
        fixedSourceKernel_apply a n cStar τ sgn hm he hb0 hu0 x A hA
  · refine (Measure.measurable_of_measurable_coe _ fun B hB => ?_).aemeasurable
    simp only [Measure.finsetSum_apply]
    apply Finset.measurable_fun_sum
    intro c hc
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
    have hm : Measurable fun x => sourceCellMass (actualStrength a n)
        (tiledPerturbation cStar n sgn x)
        (coupledPerturbation cStar τ n sgn x) c := by
      rcases c with ⟨z, d, y⟩
      have hu := tiledPerturbation_measurable cStar n sgn
      cases z <;> cases d <;> cases y <;>
        simp [sourceCellMass, coupledPerturbation, assignmentWeight,
          receiptOutcomeCell, receiptBase, sign] <;>
          fun_prop (disch := assumption)
    exact (hm.ennreal_ofReal.mul
      (measurable_one.indicator
        (hB.preimage (sourceCellObservation_measurable c))))
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hb,hAdm,hτ), [the lower source law equals its explicit construction](goal). -/

lemma lowerSourceLaw_eq_explicit (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1) :
    Measure.map observeSource
      (assignedFrom
        (primitivePopulation true (fun _ => 1)
          (lowerMass a n cStar τ sgn))
        (fun x => 1 / 2 + tiledPerturbation cStar n sgn x)) =
      explicitSourceLaw (actualStrength a n)
        (tiledPerturbation cStar n sgn)
        (coupledPerturbation cStar τ n sgn) := by
  apply sourceLaw_eq_explicit_of_nonneg a n cStar τ sgn
  · exact lowerMass_nonneg a n cStar τ sgn hb hAdm hτ
  · intro x z
    exact (lowerAssignmentWeight_mem_Icc a n cStar τ sgn hAdm x z).1
  · exact hb.1
  · intro x heq
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have hu' : |tiledPerturbation cStar n sgn x| ≤ 3 / 16 :=
      le_trans hu hAdm.2.1
    have hs : |tiledPerturbation cStar n sgn x| = 1 / 2 := by
      nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
        abs_nonneg (tiledPerturbation cStar n sgn x)]
    linarith


end CausalSmith.Stat.TransportCaceRoughnuisanceLength
