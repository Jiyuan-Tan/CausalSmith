module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Template

/-! # Geometry of treated microcells -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory

/-- Reference microcubes are measurable, including at the template boundary. [For the stated inputs and conditions](hyp:d,m,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_microCube_measurable (d m : ℕ)
    (ℓ : Fin d → Fin (m + 1)) : MeasurableSet (microCube d m ℓ) := by
  unfold microCube
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (by fun_prop : Measurable fun z : Fin d → ℝ =>
      |z i - tensorNode d m ℓ i|) measurable_const

/-- Every scaled microcell is measurable at every dyadic mesh. [For the stated inputs and conditions](hyp:d,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_scaledMicroCell_measurable (d m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) :
    MeasurableSet (scaledMicroCell d m j k ℓ) := by
  unfold scaledMicroCell
  exact (orderedMass_microCube_measurable d m ℓ).preimage (by fun_prop)

/-- Under the template width cap, every coordinate of a reference
microcube lies strictly between zero and one. [For the stated inputs and conditions](hyp:d,m,ℓ,z,hz,i), [the asserted conclusion holds](goal). -/
lemma orderedMass_microCube_interior (d m : ℕ)
    (ℓ : Fin d → Fin (m + 1)) (z : Fin d → ℝ)
    (hz : z ∈ microCube d m ℓ) (i : Fin d) :
    0 < z i ∧ z i < 1 := by
  have hη : templateEta d m ≤ 1 / (2 * (m + 2 : ℝ)) := by
    unfold templateEta
    exact min_le_left _ _
  have hcoord := hz i
  change |z i - ((ℓ i).val + 1 : ℝ) / (m + 2 : ℝ)| ≤ templateEta d m / 2 at hcoord
  have hℓlow : (0 : ℝ) ≤ (ℓ i).val := by positivity
  have hℓhigh : ((ℓ i).val : ℝ) ≤ m := by
    exact_mod_cast Nat.le_of_lt_succ (ℓ i).isLt
  have hm : (0 : ℝ) < m + 2 := by positivity
  have hnode_low : 1 / (m + 2 : ℝ) ≤ ((ℓ i).val + 1 : ℝ) / (m + 2 : ℝ) := by
    apply div_le_div_of_nonneg_right _ hm.le
    linarith
  have hnode_high : ((ℓ i).val + 1 : ℝ) / (m + 2 : ℝ) ≤
      (m + 1 : ℝ) / (m + 2 : ℝ) := by
    apply div_le_div_of_nonneg_right _ hm.le
    linarith
  have hη' : templateEta d m / 2 ≤ 1 / (4 * (m + 2 : ℝ)) := by
    calc
      templateEta d m / 2 ≤ (1 / (2 * (m + 2 : ℝ))) / 2 :=
        div_le_div_of_nonneg_right hη (by norm_num)
      _ = 1 / (4 * (m + 2 : ℝ)) := by field_simp; ring
  constructor
  · have := (abs_le.mp hcoord).1
    have hfrac : 1 / (4 * (m + 2 : ℝ)) < 1 / (m + 2 : ℝ) := by
      field_simp
      nlinarith [hm]
    linarith
  · have := (abs_le.mp hcoord).2
    have hfrac : 0 < 1 / (4 * (m + 2 : ℝ)) := by positivity
    have hunit : (m + 1 : ℝ) / (m + 2 : ℝ) +
        1 / (4 * (m + 2 : ℝ)) < 1 := by
      field_simp
      nlinarith [hm]
    linarith

/-- A dyadic mesh width multiplied by the number of cells is one. [For the stated inputs and conditions](hyp:j), [the asserted conclusion holds](goal). -/
lemma orderedMass_meshWidth_mul_pow (j : ℕ) :
    meshWidth j * (2 : ℝ) ^ j = 1 := by
  unfold meshWidth
  rw [← Real.rpow_natCast (2 : ℝ) j]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  simp

/-- Every scaled microcell lies inside its indexed macro-cube, including at
the boundary of the ambient cube. [For the stated inputs and conditions](hyp:d,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_scaledMicroCell_inside_dyadicCube (d m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) :
    scaledMicroCell d m j k ℓ ⊆ dyadicCube d j k := by
  intro x hx
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  have hscale := orderedMass_meshWidth_mul_pow j
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have hcoord (i : Fin d) :
      0 < (x i - cubeCorner d j k i) / meshWidth j ∧
      (x i - cubeCorner d j k i) / meshWidth j < 1 :=
    orderedMass_microCube_interior d m ℓ
      (fun i => (x i - cubeCorner d j k i) / meshWidth j) hx i
  have hbounds (i : Fin d) :
      cubeCorner d j k i < x i ∧
      x i < cubeCorner d j k i + meshWidth j := by
    have hz := hcoord i
    have hid : meshWidth j * ((x i - cubeCorner d j k i) / meshWidth j) =
        x i - cubeCorner d j k i := by field_simp
    constructor <;> nlinarith [mul_lt_mul_of_pos_left hz.1 hh,
      mul_lt_mul_of_pos_left hz.2 hh]
  change x ∈ cube d ∧ ∀ i,
    cubeCorner d j k i ≤ x i ∧
      (x i < cubeCorner d j k i + meshWidth j ∨
        ((k i).val = 2 ^ j - 1 ∧ x i = 1))
  constructor
  · intro i hi
    change x i ∈ Set.Icc (0 : ℝ) 1
    have hk : ((k i).val : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
      exact_mod_cast (k i).isLt
    have hcorner : cubeCorner d j k i = (k i).val * meshWidth j := rfl
    have hb := hbounds i
    constructor
    · rw [hcorner] at hb
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (k i).val) hh.le]
    · rw [hcorner] at hb
      nlinarith [mul_nonneg (sub_nonneg.mpr hk) hh.le]
  · intro i
    exact ⟨(hbounds i).1.le, Or.inl (hbounds i).2⟩

/-- A point in a scaled microcell lies strictly between the corresponding
macro-cube faces in every coordinate. [For the stated inputs and conditions](hyp:d,m,j,k,ℓ,x,hx,i), [the asserted conclusion holds](goal). -/
lemma orderedMass_scaledMicroCell_strict_bounds (d m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1))
    {x : Fin d → ℝ} (hx : x ∈ scaledMicroCell d m j k ℓ) (i : Fin d) :
    cubeCorner d j k i < x i ∧
      x i < cubeCorner d j k i + meshWidth j := by
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  have hz := orderedMass_microCube_interior d m ℓ
    (fun i => (x i - cubeCorner d j k i) / meshWidth j) hx i
  have hid : meshWidth j * ((x i - cubeCorner d j k i) / meshWidth j) =
      x i - cubeCorner d j k i := by field_simp
  constructor <;> nlinarith [mul_lt_mul_of_pos_left hz.1 hh,
    mul_lt_mul_of_pos_left hz.2 hh]

/-- Microcells in different macro-cubes are disjoint, even if the microcell
labels differ. [For the stated inputs and conditions](hyp:d,m,j,k,k',hk,ℓ,ℓ'), [the asserted conclusion holds](goal). -/
lemma orderedMass_scaledMicroCell_disjoint_macro (d m j : ℕ)
    (k k' : Fin d → Fin (2 ^ j)) (hk : k ≠ k')
    (ℓ ℓ' : Fin d → Fin (m + 1)) :
    Disjoint (scaledMicroCell d m j k ℓ) (scaledMicroCell d m j k' ℓ') := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  apply hk
  funext i
  apply Fin.ext
  have hb := orderedMass_scaledMicroCell_strict_bounds d m j k ℓ hx i
  have hb' := orderedMass_scaledMicroCell_strict_bounds d m j k' ℓ' hx' i
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  by_contra hne
  have hcases : (k i).val + 1 ≤ (k' i).val ∨ (k' i).val + 1 ≤ (k i).val := by omega
  rcases hcases with hlt | hgt
  · have hcast : ((k i).val : ℝ) + 1 ≤ (k' i).val := by exact_mod_cast hlt
    unfold cubeCorner at hb hb'
    nlinarith [mul_nonneg (sub_nonneg.mpr hcast) hh.le]
  · have hcast : ((k' i).val : ℝ) + 1 ≤ (k i).val := by exact_mod_cast hgt
    unfold cubeCorner at hb hb'
    nlinarith [mul_nonneg (sub_nonneg.mpr hcast) hh.le]

/-- Every scaled microcell has the same Euclidean volume, independently of
its tensor node and macro-cube. [For the stated inputs and conditions](hyp:d,m,j,k,ℓ), [the asserted conclusion holds](goal). -/
lemma orderedMass_scaledMicroCell_volume (d m j : ℕ)
    (k : Fin d → Fin (2 ^ j)) (ℓ : Fin d → Fin (m + 1)) :
    volume (scaledMicroCell d m j k ℓ) =
      ENNReal.ofReal (templateEta d m * meshWidth j) ^ d := by
  have hh : 0 < meshWidth j := by unfold meshWidth; positivity
  let lo : Fin d → ℝ := fun i =>
    cubeCorner d j k i + meshWidth j * (tensorNode d m ℓ i - templateEta d m / 2)
  let hi : Fin d → ℝ := fun i =>
    cubeCorner d j k i + meshWidth j * (tensorNode d m ℓ i + templateEta d m / 2)
  have hset : scaledMicroCell d m j k ℓ = Set.Icc lo hi := by
    ext x
    simp only [scaledMicroCell, Set.mem_ofPred_eq, microCube, Set.mem_Icc,
      Pi.le_def, lo, hi]
    constructor
    · intro hx
      constructor
      · intro i
        have hxi := (abs_le.mp (hx i)).1
        have hmul : (x i - cubeCorner d j k i) / meshWidth j * meshWidth j =
            x i - cubeCorner d j k i := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right hxi hh.le]
      · intro i
        have hxi := (abs_le.mp (hx i)).2
        have hmul : (x i - cubeCorner d j k i) / meshWidth j * meshWidth j =
            x i - cubeCorner d j k i := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right hxi hh.le]
    · intro hx i
      apply abs_le.mpr
      have hlo : tensorNode d m ℓ i - templateEta d m / 2 ≤
          (x i - cubeCorner d j k i) / meshWidth j :=
        (le_div_iff₀ hh).2 (by nlinarith [hx.1 i])
      have hhi : (x i - cubeCorner d j k i) / meshWidth j ≤
          tensorNode d m ℓ i + templateEta d m / 2 :=
        (div_le_iff₀ hh).2 (by nlinarith [hx.2 i])
      constructor <;> linarith
  rw [hset, Real.volume_Icc_pi]
  have hdiff : ∀ i : Fin d, hi i - lo i = templateEta d m * meshWidth j := by
    intro i
    dsimp [hi, lo]
    ring
  simp only [hdiff, Finset.prod_const, Finset.card_fin]

end CausalSmith.Stat.WeakOverlap
