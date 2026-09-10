import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Basic.Occupancy
import Causalean.Mathlib.MeasureTheory.PolynomialZeroLocus

/-!
# Generic affine occupancy

The common almost-sure occupancy lemma for both honest-set and full-design applications.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open MeasureTheory
open Causalean.Mathlib.MeasureTheory

-- @node: genericActiveAmplitudes_ae_positive
/-- Absolute continuity with respect to volume restricted to the positive orthant forces the
active amplitude vector to lie in that orthant almost surely. [Under the stated hypotheses](hyp:h_generic) [this conclusion](goal) applies. -/
lemma genericActiveAmplitudes_ae_positive {ι Ωsample : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ωsample] {p : ℕ} (I : Finset ι)
    (Z : ι → Fin p → Bool) (a : Ωsample → ι → Fin p → ℝ)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (h_generic : GenericActiveAmplitudes I Z μ a) :
    ∀ᵐ ω ∂μ, activeProjection I Z (a ω) ∈ positiveOrthant I Z := by
  let f := fun ω ↦ activeProjection I Z (a ω)
  let O := positiveOrthant I Z
  have hO : MeasurableSet O := by
    change MeasurableSet {x : ActiveIndex I Z → ℝ | ∀ q, (0 : ℝ) < x q}
    rw [show {x : ActiveIndex I Z → ℝ | ∀ q, (0 : ℝ) < x q} =
        ⋂ q, {x | (0 : ℝ) < x q} by ext; simp]
    exact MeasurableSet.iInter fun q ↦ measurableSet_lt
      (measurable_const : Measurable fun _ : ActiveIndex I Z → ℝ ↦ (0 : ℝ))
      (show Measurable (fun x : ActiveIndex I Z → ℝ ↦ x q) from measurable_pi_apply q)
  have htarget : (volume.restrict O) Oᶜ = 0 := by
    rw [Measure.restrict_apply (MeasurableSet.compl hO)]
    simp
  have hmap : Measure.map f μ Oᶜ = 0 := h_generic.2 htarget
  rw [Measure.map_apply h_generic.1 (MeasurableSet.compl hO)] at hmap
  apply ae_iff.mpr
  rw [show {ω | activeProjection I Z (a ω) ∉ positiveOrthant I Z} =
      (f ⁻¹' O)ᶜ by rfl]
  exact hmap

-- @node: genericActiveAmplitudes_ae_avoid_volume_null
/-- A jointly absolutely continuous active-amplitude vector almost surely avoids every
measurable Lebesgue-null exceptional set. [Under the stated hypotheses](hyp:h_generic,hSmeas,hSnull) [this conclusion](goal) applies. -/
lemma genericActiveAmplitudes_ae_avoid_volume_null {ι Ωsample : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ωsample] {p : ℕ} (I : Finset ι)
    (Z : ι → Fin p → Bool) (a : Ωsample → ι → Fin p → ℝ)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (h_generic : GenericActiveAmplitudes I Z μ a)
    (S : Set (ActiveIndex I Z → ℝ)) (hSmeas : MeasurableSet S)
    (hSnull : volume S = 0) :
    ∀ᵐ ω ∂μ, activeProjection I Z (a ω) ∉ S := by
  let f := fun ω ↦ activeProjection I Z (a ω)
  have hrestrict : (volume.restrict (positiveOrthant I Z)) S = 0 := by
    rw [Measure.restrict_apply hSmeas]
    exact measure_mono_null Set.inter_subset_left hSnull
  have hmap : Measure.map f μ S = 0 := h_generic.2 hrestrict
  rw [Measure.map_apply h_generic.1 hSmeas] at hmap
  apply ae_iff.mpr
  rw [show {ω | ¬ activeProjection I Z (a ω) ∉ S} = f ⁻¹' S by
    ext ω
    simp [f]]
  exact hmap

-- @node: genericActiveAmplitudes_ae_polynomial_ne_zero
/-- A jointly absolutely continuous active-amplitude vector almost surely does not
annihilate any fixed nonzero polynomial in its active coordinates. [Under the stated hypotheses](hyp:h_generic,hP) [this conclusion](goal) applies. -/
lemma genericActiveAmplitudes_ae_polynomial_ne_zero
    {ι Ωsample : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ωsample] {p : ℕ} (I : Finset ι)
    (Z : ι → Fin p → Bool) (a : Ωsample → ι → Fin p → ℝ)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (h_generic : GenericActiveAmplitudes I Z μ a)
    (P : MvPolynomial (ActiveIndex I Z) ℝ) (hP : P ≠ 0) :
    ∀ᵐ ω ∂μ, MvPolynomial.eval (activeProjection I Z (a ω)) P ≠ 0 := by
  let S : Set (ActiveIndex I Z → ℝ) :=
    {x | MvPolynomial.eval x P = 0}
  have hSmeas : MeasurableSet S := by
    exact (MvPolynomial.continuous_eval P).measurable (measurableSet_singleton 0)
  have hSnull : volume S = 0 := volume_zeroLocus_mvPolynomial_finite P hP
  simpa [S] using genericActiveAmplitudes_ae_avoid_volume_null
    I Z a μ h_generic S hSmeas hSnull

-- @node: genericActiveAmplitudes_ae_finite_polynomials_ne_zero
/-- Joint absolute continuity simultaneously avoids the zero loci of any finite family of
nonzero polynomials in the active coordinates. [Under the stated hypotheses](hyp:h_generic,hP) [this conclusion](goal) applies. -/
lemma genericActiveAmplitudes_ae_finite_polynomials_ne_zero
    {ι Ωsample : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ωsample] {p : ℕ} (I : Finset ι)
    (Z : ι → Fin p → Bool) (a : Ωsample → ι → Fin p → ℝ)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (h_generic : GenericActiveAmplitudes I Z μ a)
    (P : Finset (MvPolynomial (ActiveIndex I Z) ℝ))
    (hP : ∀ Q ∈ P, Q ≠ 0) :
    ∀ᵐ ω ∂μ, ∀ Q ∈ P,
      MvPolynomial.eval (activeProjection I Z (a ω)) Q ≠ 0 := by
  rw [Finset.eventually_all]
  intro Q hQ
  exact genericActiveAmplitudes_ae_polynomial_ne_zero I Z a μ h_generic Q (hP Q hQ)

-- @node: genericActiveAmplitudes_ae_activeProjection_injective
/-- Joint absolute continuity makes the finitely many active amplitudes pairwise distinct almost
surely. [Under the stated hypotheses](hyp:h_generic) [this conclusion](goal) applies. -/
lemma genericActiveAmplitudes_ae_activeProjection_injective
    {ι Ωsample : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ωsample] {p : ℕ} (I : Finset ι)
    (Z : ι → Fin p → Bool) (a : Ωsample → ι → Fin p → ℝ)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (h_generic : GenericActiveAmplitudes I Z μ a) :
    ∀ᵐ ω ∂μ, Function.Injective (activeProjection I Z (a ω)) := by
  have hall : ∀ᵐ ω ∂μ,
      ∀ q ∈ (Finset.univ : Finset (ActiveIndex I Z)),
        ∀ r ∈ (Finset.univ : Finset (ActiveIndex I Z)), q ≠ r →
          activeProjection I Z (a ω) q ≠ activeProjection I Z (a ω) r := by
    rw [Finset.eventually_all]
    intro q _
    rw [Finset.eventually_all]
    intro r _
    by_cases hqr : q = r
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hqr).elim
    · let P : MvPolynomial (ActiveIndex I Z) ℝ :=
        MvPolynomial.X q - MvPolynomial.X r
      have hP : P ≠ 0 := sub_ne_zero.mpr (MvPolynomial.X_injective.ne hqr)
      filter_upwards
        [genericActiveAmplitudes_ae_polynomial_ne_zero I Z a μ h_generic P hP]
        with ω hω
      intro _
      simpa [P, sub_ne_zero] using hω
  filter_upwards [hall] with ω hω
  intro q r h
  by_contra hqr
  exact hω q (Finset.mem_univ q) r (Finset.mem_univ r) hqr h

-- @node: activeCoordinatePolynomial
/-- The coordinate polynomial whose evaluation recovers one support-masked amplitude. -/
noncomputable def activeCoordinatePolynomial { ι : Type*} [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (e : ι) (j : Fin p) :
    MvPolynomial (ActiveIndex I Z) ℝ :=
  if h : e ∈ I ∧ Z e j = true then MvPolynomial.X ⟨(e, j), h⟩ else 0

-- @node: eval_activeCoordinatePolynomial
/-- Evaluating a coordinate polynomial at the active projection gives the masked amplitude. [Under the stated hypotheses](hyp:he) [this conclusion](goal) applies. -/
lemma eval_activeCoordinatePolynomial { ι : Type*} [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (a : ι → Fin p → ℝ)
    (e : ι) (he : e ∈ I) (j : Fin p) :
    MvPolynomial.eval (activeProjection I Z a) (activeCoordinatePolynomial I Z e j) =
      if Z e j then a e j else 0 := by
  by_cases hZ : Z e j = true
  · simp [activeCoordinatePolynomial, he, hZ, activeProjection]
  · have hfalse : Z e j = false := Bool.eq_false_of_not_eq_true hZ
    simp [activeCoordinatePolynomial, he, hZ, hfalse]

-- @node: affineMinorPolynomial
/-- The affine-minor polynomial of three support-masked indexed points. -/
noncomputable def affineMinorPolynomial { ι : Type*} [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (k l : Fin p) (e f g : ι) : MvPolynomial (ActiveIndex I Z) ℝ :=
  let X := activeCoordinatePolynomial I Z
  X f k * X g l - X g k * X f l -
    (X e k * X g l - X g k * X e l) +
    (X e k * X f l - X f k * X e l)

-- @node: eval_affineMinorPolynomial
/-- Evaluating the affine-minor polynomial gives the affine minor of the realized points. [Under the stated hypotheses](hyp:he,hf,hg) [this conclusion](goal) applies. -/
lemma eval_affineMinorPolynomial { ι : Type*} [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (a : ι → Fin p → ℝ)
    (k l : Fin p) (e f g : ι) (he : e ∈ I) (hf : f ∈ I) (hg : g ∈ I) :
    MvPolynomial.eval (activeProjection I Z a) (affineMinorPolynomial I Z k l e f g) =
      affineMinor (fun u j ↦ if Z u j then a u j else 0) k l e f g := by
  simp [affineMinorPolynomial, affineMinor, eval_activeCoordinatePolynomial,
    he, hf, hg]

-- @node: affineMinorPolynomial_ne_zero_of_mixed_support
/-- Three distinct nonzero-support points have a nonzero affine-minor polynomial unless
all three are forced onto the same coordinate axis. [Under the stated hypotheses](hyp:hkl,he,hf,hg,hef,heg,hfg,he_active,hf_active,hg_active,hhas_k,hhas_l) [this conclusion](goal) applies. -/
lemma affineMinorPolynomial_ne_zero_of_mixed_support
    {ι : Type*} [DecidableEq ι] {p : ℕ}
    (I : Finset ι) (Z : ι → Fin p → Bool) (k l : Fin p) (hkl : k < l)
    (e f g : ι) (he : e ∈ I) (hf : f ∈ I) (hg : g ∈ I)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he_active : Z e k = true ∨ Z e l = true)
    (hf_active : Z f k = true ∨ Z f l = true)
    (hg_active : Z g k = true ∨ Z g l = true)
    (hhas_k : Z e k = true ∨ Z f k = true ∨ Z g k = true)
    (hhas_l : Z e l = true ∨ Z f l = true ∨ Z g l = true) :
    affineMinorPolynomial I Z k l e f g ≠ 0 := by
  intro hzero
  let b : ι → Fin p → ℝ := fun u j ↦
    if u = e then if j = k then 1 else if j = l then 1 else 0
    else if u = f then if j = k then 2 else if j = l then 4 else 0
    else if u = g then if j = k then 3 else if j = l then 9 else 0
    else 0
  have heval := congrArg (MvPolynomial.eval (activeProjection I Z b)) hzero
  rw [eval_affineMinorPolynomial I Z b k l e f g he hf hg] at heval
  have hkne : k ≠ l := ne_of_lt hkl
  have hlkne : l ≠ k := Ne.symm hkne
  have hfe : f ≠ e := Ne.symm hef
  have hge : g ≠ e := Ne.symm heg
  have hgf : g ≠ f := Ne.symm hfg
  simp only [affineMinor, b, if_pos, if_neg, hef, heg, hfg, hfe, hge, hgf,
    hkne, hlkne, not_false_eq_true] at heval
  cases hek : Z e k <;> cases hel : Z e l <;>
    cases hfk : Z f k <;> cases hfl : Z f l <;>
    cases hgk : Z g k <;> cases hgl : Z g l <;>
    simp_all <;> norm_num at heval

-- @node: originMinorPolynomial
/-- The determinant polynomial for collinearity of two masked points with the origin. -/
noncomputable def originMinorPolynomial {ι : Type*} [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (k l : Fin p) (e f : ι) : MvPolynomial (ActiveIndex I Z) ℝ :=
  activeCoordinatePolynomial I Z e k * activeCoordinatePolynomial I Z f l -
    activeCoordinatePolynomial I Z f k * activeCoordinatePolynomial I Z e l

-- @node: eval_originMinorPolynomial
/-- Evaluating the origin-minor polynomial gives the determinant of the two realized points. [Under the stated hypotheses](hyp:he,hf) [this conclusion](goal) applies. -/
lemma eval_originMinorPolynomial {ι : Type*} [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (a : ι → Fin p → ℝ)
    (k l : Fin p) (e f : ι) (he : e ∈ I) (hf : f ∈ I) :
    MvPolynomial.eval (activeProjection I Z a) (originMinorPolynomial I Z k l e f) =
      (if Z e k then a e k else 0) * (if Z f l then a f l else 0) -
        (if Z f k then a f k else 0) * (if Z e l then a e l else 0) := by
  simp [originMinorPolynomial, eval_activeCoordinatePolynomial, he, hf]

-- @node: originMinorPolynomial_ne_zero_of_mixed_support
/-- Two distinct nonzero-support points have a nonzero determinant polynomial unless they
are forced onto the same coordinate axis. [Under the stated hypotheses](hyp:hkl,he,hf,hef,he_active,hf_active,hhas_k,hhas_l) [this conclusion](goal) applies. -/
lemma originMinorPolynomial_ne_zero_of_mixed_support
    {ι : Type*} [DecidableEq ι] {p : ℕ}
    (I : Finset ι) (Z : ι → Fin p → Bool) (k l : Fin p) (hkl : k < l)
    (e f : ι) (he : e ∈ I) (hf : f ∈ I) (hef : e ≠ f)
    (he_active : Z e k = true ∨ Z e l = true)
    (hf_active : Z f k = true ∨ Z f l = true)
    (hhas_k : Z e k = true ∨ Z f k = true)
    (hhas_l : Z e l = true ∨ Z f l = true) :
    originMinorPolynomial I Z k l e f ≠ 0 := by
  intro hzero
  let b : ι → Fin p → ℝ := fun u j ↦
    if u = e then if j = k then 1 else if j = l then 1 else 0
    else if u = f then if j = k then 2 else if j = l then 4 else 0
    else 0
  have heval := congrArg (MvPolynomial.eval (activeProjection I Z b)) hzero
  rw [eval_originMinorPolynomial I Z b k l e f he hf] at heval
  have hkne : k ≠ l := ne_of_lt hkl
  have hlkne : l ≠ k := Ne.symm hkne
  have hfe : f ≠ e := Ne.symm hef
  simp only [b, if_pos, if_neg, hef, hfe, hkne, hlkne, not_false_eq_true] at heval
  cases hek : Z e k <;> cases hel : Z e l <;>
    cases hfk : Z f k <;> cases hfl : Z f l <;>
    simp_all <;> norm_num at heval

-- @node: maxLineOccupancy_ge_of_collinear
/-- Every collinear indexed subfamily gives a lower bound on maximum line occupancy. [Under the stated hypotheses](hyp:hSI,hS) [this conclusion](goal) applies. -/
lemma maxLineOccupancy_ge_of_collinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I S : Finset ι) (s : ι → Fin p → ℝ) (k l : Fin p)
    (hSI : S ⊆ I) (hS : CollinearPairs s k l S) :
    S.card ≤ maxLineOccupancy I s k l := by
  unfold maxLineOccupancy
  apply Finset.le_sup (s := I.powerset.filter (CollinearPairs s k l))
  simp [hSI, hS]

-- @node: maxLineOccupancy_support_lower_bound
/-- The horizontal and vertical support axes force the first two generic-occupancy lower bounds. [This is the asserted conclusion](goal). -/
lemma maxLineOccupancy_support_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (a : ι → Fin p → ℝ) (k l : Fin p) :
    max (incidenceCount I Z k l false false + incidenceCount I Z k l true false)
        (incidenceCount I Z k l false false + incidenceCount I Z k l false true) ≤
      maxLineOccupancy I (fun e j ↦ if Z e j then a e j else 0) k l := by
  let s := fun e j ↦ if Z e j then a e j else 0
  let horizontal := I.filter fun e ↦ Z e l = false
  let vertical := I.filter fun e ↦ Z e k = false
  have hhorizontal : CollinearPairs s k l horizontal := by
    intro e he f hf g hg
    have he0 : s e l = 0 := by
      rcases Finset.mem_filter.mp he with ⟨_, he⟩
      simp [s, he]
    have hf0 : s f l = 0 := by
      rcases Finset.mem_filter.mp hf with ⟨_, hf⟩
      simp [s, hf]
    have hg0 : s g l = 0 := by
      rcases Finset.mem_filter.mp hg with ⟨_, hg⟩
      simp [s, hg]
    simp [affineMinor, he0, hf0, hg0]
  have hvertical : CollinearPairs s k l vertical := by
    intro e he f hf g hg
    have he0 : s e k = 0 := by
      rcases Finset.mem_filter.mp he with ⟨_, he⟩
      simp [s, he]
    have hf0 : s f k = 0 := by
      rcases Finset.mem_filter.mp hf with ⟨_, hf⟩
      simp [s, hf]
    have hg0 : s g k = 0 := by
      rcases Finset.mem_filter.mp hg with ⟨_, hg⟩
      simp [s, hg]
    simp [affineMinor, he0, hf0, hg0]
  have hhcard : horizontal.card =
      incidenceCount I Z k l false false + incidenceCount I Z k l true false := by
    classical
    simp only [horizontal, incidenceCount]
    rw [← Finset.card_filter_add_card_filter_not
      (s := I.filter fun e ↦ Z e l = false) (p := fun e ↦ Z e k = false)]
    apply congrArg₂ (fun x y : ℕ ↦ x + y)
    · apply congrArg Finset.card
      ext e
      simp [and_assoc, and_left_comm, and_comm]
    · apply congrArg Finset.card
      ext e
      simp [and_assoc, and_left_comm, and_comm]
  have hvcard : vertical.card =
      incidenceCount I Z k l false false + incidenceCount I Z k l false true := by
    classical
    simp only [vertical, incidenceCount]
    rw [← Finset.card_filter_add_card_filter_not
      (s := I.filter fun e ↦ Z e k = false) (p := fun e ↦ Z e l = false)]
    apply congrArg₂ (fun x y : ℕ ↦ x + y)
    · apply congrArg Finset.card
      ext e
      simp [and_assoc, and_left_comm, and_comm]
    · apply congrArg Finset.card
      ext e
      simp [and_assoc, and_left_comm, and_comm]
  rw [← hhcard, ← hvcard]
  exact max_le
    (maxLineOccupancy_ge_of_collinear I horizontal s k l (by simp [horizontal]) hhorizontal)
    (maxLineOccupancy_ge_of_collinear I vertical s k l (by simp [vertical]) hvertical)

-- @node: maxLineOccupancy_ge_min_two
/-- Any indexed family has a collinear subfamily of size `min 2 I.card`. [This is the asserted conclusion](goal). -/
lemma maxLineOccupancy_ge_min_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (s : ι → Fin p → ℝ) (k l : Fin p) :
    min 2 I.card ≤ maxLineOccupancy I s k l := by
  obtain ⟨S, hSI, hScard⟩ := Finset.exists_subset_card_eq (min_le_right 2 I.card)
  rw [← hScard]
  apply maxLineOccupancy_ge_of_collinear I S s k l hSI
  intro e he f hf g hg
  have hcard : S.card ≤ 2 := by omega
  have hpigeon : e = f ∨ e = g ∨ f = g := by
    by_contra hne
    push Not at hne
    have hsub : ({e, f, g} : Finset ι) ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro he (And.intro hf hg)
    have hthree : ({e, f, g} : Finset ι).card = 3 := by
      simp [hne.1, hne.2.1, hne.2.2]
    have hle := Finset.card_le_card hsub
    omega
  rcases hpigeon with hef | heg | hfg
  · subst f
    simp [affineMinor]
  · subst g
    simp only [affineMinor]
    ring
  · subst g
    simp only [affineMinor]
    ring

-- @node: maxLineOccupancy_three_forced_terms
/-- The two support axes and the unavoidable two-point line jointly give three of the four
terms in the generic occupancy formula. [This is the asserted conclusion](goal). -/
lemma maxLineOccupancy_three_forced_terms {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool)
    (a : ι → Fin p → ℝ) (k l : Fin p) :
    max
        (max (incidenceCount I Z k l false false + incidenceCount I Z k l true false)
          (incidenceCount I Z k l false false + incidenceCount I Z k l false true))
        (min 2 I.card) ≤
      maxLineOccupancy I (fun e j ↦ if Z e j then a e j else 0) k l := by
  exact max_le (maxLineOccupancy_support_lower_bound I Z a k l)
    (maxLineOccupancy_ge_min_two I (fun e j ↦ if Z e j then a e j else 0) k l)

-- @node: maxLineOccupancy_origin_interior_lower_bound
/-- The repeated origin together with one interior-support point forces the third
support-incidence lower bound. [This is the asserted conclusion](goal). -/
lemma maxLineOccupancy_origin_interior_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    (I : Finset ι) (Z : ι → Fin p → Bool)
    (a : ι → Fin p → ℝ) (k l : Fin p) :
    incidenceCount I Z k l false false +
        (if 0 < incidenceCount I Z k l true true then 1 else 0) ≤
      maxLineOccupancy I (fun e j ↦ if Z e j then a e j else 0) k l := by
  let zeros := I.filter fun e ↦ Z e k = false ∧ Z e l = false
  by_cases hn : 0 < incidenceCount I Z k l true true
  · obtain ⟨e, heI, hek, hel⟩ : ∃ e ∈ I, Z e k = true ∧ Z e l = true := by
      have hnonempty : (I.filter fun e ↦ Z e k = true ∧ Z e l = true).Nonempty := by
        exact Finset.card_pos.mp hn
      rcases hnonempty with ⟨e, he⟩
      exact ⟨e, by simpa using he⟩
    let S := insert e zeros
    have hezero : e ∉ zeros := by simp [zeros, hek]
    have hcard : S.card = incidenceCount I Z k l false false + 1 := by
      simp [S, Finset.card_insert_of_notMem hezero, zeros, incidenceCount]
    rw [if_pos hn, ← hcard]
    apply maxLineOccupancy_ge_of_collinear I S
      (fun e j ↦ if Z e j then a e j else 0) k l
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact heI
      · exact (Finset.mem_filter.mp hu).1
    · intro u hu v hv w hw
      have support_cases (x : ι) (hx : x ∈ S) :
          x = e ∨ (Z x k = false ∧ Z x l = false) := by
        rcases Finset.mem_insert.mp hx with hxe | hx
        · exact Or.inl hxe
        · exact Or.inr (Finset.mem_filter.mp hx).2
      rcases support_cases u hu with rfl | hu0 <;>
        rcases support_cases v hv with rfl | hv0 <;>
        rcases support_cases w hw with rfl | hw0 <;>
        simp_all [affineMinor] <;> ring
  · rw [if_neg hn, add_zero]
    have hcol : CollinearPairs (fun e j ↦ if Z e j then a e j else 0) k l zeros := by
      intro e he f hf g hg
      simp only [zeros, Finset.mem_filter] at he hf hg
      simp [affineMinor, he.2.1, he.2.2, hf.2.1, hf.2.2, hg.2.1, hg.2.2]
    rw [← show zeros.card = incidenceCount I Z k l false false by rfl]
    exact maxLineOccupancy_ge_of_collinear I zeros
      (fun e j ↦ if Z e j then a e j else 0) k l (by simp [zeros]) hcol

/-- The horizontal-support slice has the expected two incidence-count pieces. [This is the asserted conclusion](goal). -/
-- @node: horizontalSupport_card
lemma horizontalSupport_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (k l : Fin p) :
    (I.filter fun e ↦ Z e l = false).card =
      incidenceCount I Z k l false false + incidenceCount I Z k l true false := by
  rw [← Finset.card_filter_add_card_filter_not
    (s := I.filter fun e ↦ Z e l = false) (p := fun e ↦ Z e k = false)]
  apply congrArg₂ (fun x y : ℕ ↦ x + y)
  · apply congrArg Finset.card
    ext e
    simp [and_assoc, and_comm]
  · apply congrArg Finset.card
    ext e
    simp [and_assoc, and_comm]

/-- The vertical-support slice has the expected two incidence-count pieces. [This is the asserted conclusion](goal). -/
-- @node: verticalSupport_card
lemma verticalSupport_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (k l : Fin p) :
    (I.filter fun e ↦ Z e k = false).card =
      incidenceCount I Z k l false false + incidenceCount I Z k l false true := by
  rw [← Finset.card_filter_add_card_filter_not
    (s := I.filter fun e ↦ Z e k = false) (p := fun e ↦ Z e l = false)]
  apply congrArg₂ (fun x y : ℕ ↦ x + y)
  · apply congrArg Finset.card
    ext e
    simp [and_assoc, and_left_comm, and_comm]
  · apply congrArg Finset.card
    ext e
    simp [and_assoc, and_left_comm, and_comm]

/-- The common origin-support slice is exactly the `00` incidence class. [This is the asserted conclusion](goal). -/
-- @node: zeroSupport_card
lemma zeroSupport_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (I : Finset ι) (Z : ι → Fin p → Bool) (k l : Fin p) :
    (I.filter fun e ↦ Z e k = false ∧ Z e l = false).card =
      incidenceCount I Z k l false false := by
  rfl

/-- If every collinear subfamily is one of the four geometrically forced forms, its
maximum occupancy is at most the generic support formula. [Under the stated hypotheses](hyp:hclass) [this conclusion](goal) applies. -/
-- @node: maxLineOccupancy_le_of_forced_classification
lemma maxLineOccupancy_le_of_forced_classification
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    (I : Finset ι) (Z : ι → Fin p → Bool) (a : ι → Fin p → ℝ) (k l : Fin p)
    (hclass : ∀ S : Finset ι, S ⊆ I →
      CollinearPairs (fun e j ↦ if Z e j then a e j else 0) k l S →
        S ⊆ I.filter (fun e ↦ Z e l = false) ∨
        S ⊆ I.filter (fun e ↦ Z e k = false) ∨
        (∃ e ∈ I, Z e k = true ∧ Z e l = true ∧
          S ⊆ insert e (I.filter fun f ↦ Z f k = false ∧ Z f l = false)) ∨
        S.card ≤ 2) :
    maxLineOccupancy I (fun e j ↦ if Z e j then a e j else 0) k l ≤
      genericOccupancy I Z k l := by
  unfold maxLineOccupancy
  apply Finset.sup_le
  intro S hS
  have hSI : S ⊆ I := (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  have hcol := (Finset.mem_filter.mp hS).2
  rcases hclass S hSI hcol with hhorizontal | hvertical | hinterior | htwo
  · have hcard := Finset.card_le_card hhorizontal
    rw [horizontalSupport_card I Z k l] at hcard
    exact le_trans hcard (by simp [genericOccupancy])
  · have hcard := Finset.card_le_card hvertical
    rw [verticalSupport_card I Z k l] at hcard
    exact le_trans hcard (by simp [genericOccupancy])
  · rcases hinterior with ⟨e, heI, hek, hel, hsub⟩
    have hcard := Finset.card_le_card hsub
    have hezero : e ∉ I.filter (fun f ↦ Z f k = false ∧ Z f l = false) := by
      simp [hek]
    rw [Finset.card_insert_of_notMem hezero, zeroSupport_card I Z k l] at hcard
    have hn11 : 0 < incidenceCount I Z k l true true := by
      apply Finset.card_pos.mpr
      exact ⟨e, by simp [heI, hek, hel]⟩
    exact le_trans hcard (by simp [genericOccupancy, hn11])
  · have hmin : S.card ≤ min 2 I.card :=
      le_min htwo (Finset.card_le_card hSI)
    exact le_trans hmin (by simp [genericOccupancy])

-- @node: genericActiveAmplitudes_ae_forced_classification
/-- Almost surely every collinear subfamily is a support axis, the repeated origin plus one
interior point, or a family of at most two indices. [Under the stated hypotheses](hyp:h_generic) [this conclusion](goal) applies. -/
lemma genericActiveAmplitudes_ae_forced_classification
    {ι Ωsample : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ωsample] {p : ℕ} (I : Finset ι)
    (Z : ι → Fin p → Bool) (a : Ωsample → ι → Fin p → ℝ)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (h_generic : GenericActiveAmplitudes I Z μ a) :
    ∀ᵐ ω ∂μ, ∀ k l : Fin p, k < l → ∀ S : Finset ι, S ⊆ I →
      CollinearPairs (fun e j ↦ if Z e j then a ω e j else 0) k l S →
        S ⊆ I.filter (fun e ↦ Z e l = false) ∨
        S ⊆ I.filter (fun e ↦ Z e k = false) ∨
        (∃ e ∈ I, Z e k = true ∧ Z e l = true ∧
          S ⊆ insert e (I.filter fun f ↦ Z f k = false ∧ Z f l = false)) ∨
        S.card ≤ 2 := by
  have hpair : ∀ᵐ ω ∂μ, ∀ k ∈ (Finset.univ : Finset (Fin p)),
      ∀ l ∈ (Finset.univ : Finset (Fin p)), ∀ e ∈ I, ∀ f ∈ I,
      k < l → e ≠ f →
      (Z e k = true ∨ Z e l = true) →
      (Z f k = true ∨ Z f l = true) →
      (Z e k = true ∨ Z f k = true) →
      (Z e l = true ∨ Z f l = true) →
      MvPolynomial.eval (activeProjection I Z (a ω))
        (originMinorPolynomial I Z k l e f) ≠ 0 := by
    rw [Finset.eventually_all]
    intro k _
    rw [Finset.eventually_all]
    intro l _
    rw [Finset.eventually_all]
    intro e he
    rw [Finset.eventually_all]
    intro f hf
    by_cases h : k < l ∧ e ≠ f ∧
        (Z e k = true ∨ Z e l = true) ∧
        (Z f k = true ∨ Z f l = true) ∧
        (Z e k = true ∨ Z f k = true) ∧
        (Z e l = true ∨ Z f l = true)
    · rcases h with ⟨hkl, hef, hea, hfa, hhk, hhl⟩
      filter_upwards [genericActiveAmplitudes_ae_polynomial_ne_zero I Z a μ h_generic
          (originMinorPolynomial I Z k l e f)
          (originMinorPolynomial_ne_zero_of_mixed_support I Z k l hkl e f he hf
            hef hea hfa hhk hhl)]
        with ω hω
      intro _ _ _ _ _ _
      exact hω
    · exact Filter.Eventually.of_forall fun _ hk hne hea hfa hhk hhl ↦
        (h ⟨hk, hne, hea, hfa, hhk, hhl⟩).elim
  have htriple : ∀ᵐ ω ∂μ, ∀ k ∈ (Finset.univ : Finset (Fin p)),
      ∀ l ∈ (Finset.univ : Finset (Fin p)), ∀ e ∈ I, ∀ f ∈ I, ∀ g ∈ I,
      k < l → e ≠ f → e ≠ g → f ≠ g →
      (Z e k = true ∨ Z e l = true) →
      (Z f k = true ∨ Z f l = true) →
      (Z g k = true ∨ Z g l = true) →
      (Z e k = true ∨ Z f k = true ∨ Z g k = true) →
      (Z e l = true ∨ Z f l = true ∨ Z g l = true) →
      MvPolynomial.eval (activeProjection I Z (a ω))
        (affineMinorPolynomial I Z k l e f g) ≠ 0 := by
    rw [Finset.eventually_all]
    intro k _
    rw [Finset.eventually_all]
    intro l _
    rw [Finset.eventually_all]
    intro e he
    rw [Finset.eventually_all]
    intro f hf
    rw [Finset.eventually_all]
    intro g hg
    by_cases h : k < l ∧ e ≠ f ∧ e ≠ g ∧ f ≠ g ∧
        (Z e k = true ∨ Z e l = true) ∧
        (Z f k = true ∨ Z f l = true) ∧
        (Z g k = true ∨ Z g l = true) ∧
        (Z e k = true ∨ Z f k = true ∨ Z g k = true) ∧
        (Z e l = true ∨ Z f l = true ∨ Z g l = true)
    · rcases h with ⟨hkl, hef, heg, hfg, hea, hfa, hga, hhk, hhl⟩
      filter_upwards [genericActiveAmplitudes_ae_polynomial_ne_zero I Z a μ h_generic
          (affineMinorPolynomial I Z k l e f g)
          (affineMinorPolynomial_ne_zero_of_mixed_support I Z k l hkl e f g he hf hg
            hef heg hfg hea hfa hga hhk hhl)]
        with ω hω
      intro _ _ _ _ _ _ _ _ _
      exact hω
    · exact Filter.Eventually.of_forall fun _ hk hef heg hfg hea hfa hga hhk hhl ↦
        (h ⟨hk, hef, heg, hfg, hea, hfa, hga, hhk, hhl⟩).elim
  filter_upwards [hpair, htriple] with ω hpairs htriples
  intro k l hkl S hSI hcol
  classical
  by_cases hhorizontal : S ⊆ I.filter (fun e ↦ Z e l = false)
  · exact Or.inl hhorizontal
  by_cases hvertical : S ⊆ I.filter (fun e ↦ Z e k = false)
  · exact Or.inr (Or.inl hvertical)
  right
  right
  have exists_l_active : ∃ e ∈ S, Z e l = true := by
    by_contra h
    push_neg at h
    apply hhorizontal
    intro e he
    have hfalse : Z e l = false := Bool.eq_false_of_not_eq_true (h e he)
    simp [hSI he, hfalse]
  have exists_k_active : ∃ e ∈ S, Z e k = true := by
    by_contra h
    push_neg at h
    apply hvertical
    intro e he
    have hfalse : Z e k = false := Bool.eq_false_of_not_eq_true (h e he)
    simp [hSI he, hfalse]
  by_cases hzero : ∃ z ∈ S, Z z k = false ∧ Z z l = false
  · rcases hzero with ⟨z, hzS, hzk, hzl⟩
    rcases exists_l_active with ⟨e, heS, hel⟩
    rcases exists_k_active with ⟨f, hfS, hfk⟩
    by_cases hef : e = f
    · subst f
      left
      refine ⟨e, hSI heS, hfk, hel, ?_⟩
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_filter]
      by_cases hue : u = e
      · exact Or.inl hue
      right
      refine ⟨hSI hu, ?_, ?_⟩
      · by_contra huk
        have huk' : Z u k = true := Bool.eq_true_of_not_eq_false huk
        have hne := hpairs k (Finset.mem_univ k) l (Finset.mem_univ l)
          e (hSI heS) u (hSI hu) hkl (Ne.symm hue)
          (Or.inl hfk) (Or.inl huk') (Or.inl hfk) (Or.inl hel)
        rw [eval_originMinorPolynomial I Z (a ω) k l e u (hSI heS) (hSI hu)] at hne
        apply hne
        simpa [affineMinor, hzk, hzl] using hcol z hzS e heS u hu
      · by_contra hul
        have hul' : Z u l = true := Bool.eq_true_of_not_eq_false hul
        have hne := hpairs k (Finset.mem_univ k) l (Finset.mem_univ l)
          e (hSI heS) u (hSI hu) hkl (Ne.symm hue)
          (Or.inl hfk) (Or.inr hul') (Or.inl hfk) (Or.inl hel)
        rw [eval_originMinorPolynomial I Z (a ω) k l e u (hSI heS) (hSI hu)] at hne
        apply hne
        simpa [affineMinor, hzk, hzl] using hcol z hzS e heS u hu
    · exfalso
      have hne := hpairs k (Finset.mem_univ k) l (Finset.mem_univ l)
        e (hSI heS) f (hSI hfS) hkl hef
        (Or.inr hel) (Or.inl hfk) (Or.inr hfk) (Or.inl hel)
      rw [eval_originMinorPolynomial I Z (a ω) k l e f (hSI heS) (hSI hfS)] at hne
      apply hne
      simpa [affineMinor, hzk, hzl] using hcol z hzS e heS f hfS
  · right
    by_contra hcard
    have hthree : 3 ≤ S.card := by omega
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hthree
    obtain ⟨e, f, g, hef, heg, hfg, rfl⟩ := Finset.card_eq_three.mp hTcard
    have heS : e ∈ S := hTS (by simp)
    have hfS : f ∈ S := hTS (by simp)
    have hgS : g ∈ S := hTS (by simp)
    have active (u : ι) (hu : u ∈ S) : Z u k = true ∨ Z u l = true := by
      by_cases huk : Z u k = true
      · exact Or.inl huk
      right
      have hukf : Z u k = false := Bool.eq_false_of_not_eq_true huk
      by_contra hul
      have hulf : Z u l = false := Bool.eq_false_of_not_eq_true hul
      exact hzero ⟨u, hu, hukf, hulf⟩
    have he_active := active e heS
    have hf_active := active f hfS
    have hg_active := active g hgS
    by_cases hall_l_zero : Z e l = false ∧ Z f l = false ∧ Z g l = false
    · rcases exists_l_active with ⟨d, hdS, hdl⟩
      have hek : Z e k = true := he_active.resolve_right (by simp [hall_l_zero.1])
      have hfk : Z f k = true := hf_active.resolve_right (by simp [hall_l_zero.2.1])
      have hd_active := active d hdS
      have hed : e ≠ d := by
        intro h
        subst d
        rw [hall_l_zero.1] at hdl
        contradiction
      have hfd : f ≠ d := by
        intro h
        subst d
        rw [hall_l_zero.2.1] at hdl
        contradiction
      have hne := htriples k (Finset.mem_univ k) l (Finset.mem_univ l)
        e (hSI heS) f (hSI hfS) d (hSI hdS) hkl hef hed hfd
        he_active hf_active hd_active (Or.inl hek) (Or.inr (Or.inr hdl))
      rw [eval_affineMinorPolynomial I Z (a ω) k l e f d
        (hSI heS) (hSI hfS) (hSI hdS)] at hne
      exact hne (hcol e heS f hfS d hdS)
    · by_cases hall_k_zero : Z e k = false ∧ Z f k = false ∧ Z g k = false
      · rcases exists_k_active with ⟨d, hdS, hdk⟩
        have hel : Z e l = true := he_active.resolve_left (by simp [hall_k_zero.1])
        have hfl : Z f l = true := hf_active.resolve_left (by simp [hall_k_zero.2.1])
        have hd_active := active d hdS
        have hed : e ≠ d := by
          intro h
          subst d
          rw [hall_k_zero.1] at hdk
          contradiction
        have hfd : f ≠ d := by
          intro h
          subst d
          rw [hall_k_zero.2.1] at hdk
          contradiction
        have hne := htriples k (Finset.mem_univ k) l (Finset.mem_univ l)
          e (hSI heS) f (hSI hfS) d (hSI hdS) hkl hef hed hfd
          he_active hf_active hd_active (Or.inr (Or.inr hdk)) (Or.inl hel)
        rw [eval_affineMinorPolynomial I Z (a ω) k l e f d
          (hSI heS) (hSI hfS) (hSI hdS)] at hne
        exact hne (hcol e heS f hfS d hdS)
      · have hhas_k : Z e k = true ∨ Z f k = true ∨ Z g k = true := by
          rcases not_and_or.mp hall_k_zero with he | hfg'
          · exact Or.inl (Bool.eq_true_of_not_eq_false he)
          rcases not_and_or.mp hfg' with hf | hg
          · exact Or.inr (Or.inl (Bool.eq_true_of_not_eq_false hf))
          · exact Or.inr (Or.inr (Bool.eq_true_of_not_eq_false hg))
        have hhas_l : Z e l = true ∨ Z f l = true ∨ Z g l = true := by
          rcases not_and_or.mp hall_l_zero with he | hfg'
          · exact Or.inl (Bool.eq_true_of_not_eq_false he)
          rcases not_and_or.mp hfg' with hf | hg
          · exact Or.inr (Or.inl (Bool.eq_true_of_not_eq_false hf))
          · exact Or.inr (Or.inr (Bool.eq_true_of_not_eq_false hg))
        have hne := htriples k (Finset.mem_univ k) l (Finset.mem_univ l)
          e (hSI heS) f (hSI hfS) g (hSI hgS) hkl hef heg hfg
          he_active hf_active hg_active hhas_k hhas_l
        rw [eval_affineMinorPolynomial I Z (a ω) k l e f g
          (hSI heS) (hSI hfS) (hSI hgS)] at hne
        exact hne (hcol e heS f hfS g hgS)

-- @node: lem:generic-affine-occupancy
/-- Under joint absolute continuity of the active amplitudes, all coordinate-pair occupancies
simultaneously equal the support-incidence formula almost surely. [Under the stated hypotheses](hyp:hp,h_generic) [this conclusion](goal) applies. -/
lemma generic_affine_occupancy {ι Ωsample : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ωsample] {p : ℕ} (hp : 2 ≤ p) (I : Finset ι)
    (Z : ι → Fin p → Bool) (a : Ωsample → ι → Fin p → ℝ)
    (μ : Measure Ωsample) [IsProbabilityMeasure μ]
    (h_generic : GenericActiveAmplitudes I Z μ a) :
    ∀ᵐ ω ∂μ, ∀ k l : Fin p, k < l →
      maxLineOccupancy I
          (fun e j ↦ if Z e j then a ω e j else 0) k l =
        genericOccupancy I Z k l := by
  filter_upwards [genericActiveAmplitudes_ae_forced_classification I Z a μ h_generic]
    with ω hclass
  intro k l hkl
  apply Nat.le_antisymm
  · exact maxLineOccupancy_le_of_forced_classification I Z (a ω) k l
      (fun S hSI hcol ↦ hclass k l hkl S hSI hcol)
  · simp only [genericOccupancy]
    apply max_le
    · exact maxLineOccupancy_support_lower_bound I Z (a ω) k l
    · apply max_le
      · exact maxLineOccupancy_origin_interior_lower_bound I Z (a ω) k l
      · exact maxLineOccupancy_ge_min_two I
          (fun e j ↦ if Z e j then a ω e j else 0) k l

end CausalSmith.ExactID.RobustBackshiftUniformDistance
