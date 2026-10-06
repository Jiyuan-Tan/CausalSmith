module
public import Mathlib

/-!
# Uniform samples and their sorted order region

This module fixes a concrete uniform measure on `[0,1]`, iid finite samples,
Mathlib tuple sorting, and the ordered-simplex measure identity. The latter is
the measure-theoretic input to exact spacing calculations.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic

open MeasureTheory

noncomputable section

/-- The [unit-uniform probability measure](goal) is [Lebesgue measure restricted to the closed unit interval](step:1). -/
def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- Given [a real sampling law](hyp:μ) and [a finite sample size](hyp:n), the [iid sample law](goal) is [the corresponding finite product measure](step:1). -/
def iidSample (μ : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => μ

/-- Given [a finite sample size](hyp:n) and [a real tuple](hyp:x), the [sorted sample](goal) is [that tuple rearranged in nondecreasing order](step:1). -/
def sortedSample (n : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  x ∘ Tuple.sort x

/-- Given [a finite dimension](hyp:n), the [ordered unit region](goal) is [the nondecreasing part of the closed unit cube](step:1). -/
def orderedUnitRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ Monotone x}

/-- Given [a finite dimension](hyp:n), the [unit cube](goal) is [the set of real tuples with every coordinate in the closed unit interval](step:1). -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- Given [a sample size](hyp:n), [a zero-based gap index](hyp:k), and [a real tuple](hyp:x), the [sorted gap](goal) is [the difference between the indicated adjacent order statistics, or zero when that index is out of range](step:1). -/
def sortedGap (n k : ℕ) (x : Fin n → ℝ) : ℝ :=
  if h : k + 1 < n then
    sortedSample n x ⟨k + 1, h⟩ - sortedSample n x ⟨k, by omega⟩
  else 0

/-- Given [a finite sample size](hyp:n), [the iid unit-uniform product law is Lebesgue measure restricted to the unit cube](goal). -/
theorem iid_uniform_cube_law (n : ℕ) :
    iidSample uniform01 n = volume.restrict (unitCube n) := by
  change (Measure.pi fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  rw [← Measure.restrict_pi_pi, ← volume_pi]
  congr 1
  ext x
  simp [unitCube, Pi.le_def, Set.mem_Icc, forall_and]

/-- A face where two distinct sample coordinates coincide has zero Lebesgue measure. -/
private theorem equal_coordinate_face_null (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    volume {x : Fin n → ℝ | x i = x j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) -
      (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)
  have hL : L ≠ 0 := by
    intro h
    have h' := LinearMap.congr_fun h (fun k => if k = i then 1 else 0)
    simp [L, hij.symm] at h'
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro h
    apply hL
    exact LinearMap.ker_eq_top.mp h
  have hs : {x : Fin n → ℝ | x i = x j} = (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext x
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  rw [hs]
  exact Measure.addHaar_submodule volume (LinearMap.ker L) hker

/-- On a chamber indexed by a permutation, tuple sorting returns exactly that
permuted tuple, even when some coordinates are equal. -/
private theorem sortedSample_eq_comp_of_monotone (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (h : Monotone (x ∘ σ)) : sortedSample n x = x ∘ σ := by
  exact ((Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 h).symm

/-- The preimage of the ordered unit region under a coordinate permutation is
exactly its corresponding chamber inside the unit cube. -/
private theorem permutation_chamber_preimage (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (fun x : Fin n → ℝ => x ∘ σ) ⁻¹' orderedUnitRegion n =
      {x | x ∈ unitCube n ∧ Monotone (x ∘ σ)} := by
  ext x
  simp only [Set.mem_preimage, orderedUnitRegion, unitCube, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hunit, hmono⟩
    exact ⟨fun i => by simpa using hunit (σ.symm i), hmono⟩
  · rintro ⟨hunit, hmono⟩
    exact ⟨fun i => hunit (σ i), hmono⟩

/-- Permuting coordinates sends the cube portion of one order chamber to the
canonical ordered region without changing Lebesgue measure. -/
private theorem permutation_chamber_coord_map (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (volume.restrict {x : Fin n → ℝ | x ∈ unitCube n ∧ Monotone (x ∘ σ)}).map
        (fun x => x ∘ σ) = volume.restrict (orderedUnitRegion n) := by
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have he : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hfun : (e : (Fin n → ℝ) → (Fin n → ℝ)) = (fun x => x ∘ σ) := by
    funext x i
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hpre : e ⁻¹' orderedUnitRegion n =
      {x : Fin n → ℝ | x ∈ unitCube n ∧ Monotone (x ∘ σ)} := by
    rw [hfun]
    exact permutation_chamber_preimage n σ
  calc
    (volume.restrict {x : Fin n → ℝ | x ∈ unitCube n ∧ Monotone (x ∘ σ)}).map
        (fun x => x ∘ σ) =
        (volume.restrict (e ⁻¹' orderedUnitRegion n)).map e := by
          rw [hpre, hfun]
    _ = (volume.map e).restrict (orderedUnitRegion n) :=
      (e.restrict_map volume (orderedUnitRegion n)).symm
    _ = volume.restrict (orderedUnitRegion n) := by rw [he.map_eq]

/-- Each permutation chamber maps to one copy of the ordered unit region. -/
private theorem permutation_chamber_map (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (volume.restrict {x : Fin n → ℝ | x ∈ unitCube n ∧ Monotone (x ∘ σ)}).map
        (sortedSample n) = volume.restrict (orderedUnitRegion n) := by
  rw [Measure.map_congr (ae_restrict_of_forall_mem
    (by
      have hc : MeasurableSet (unitCube n) := by
        have heq : unitCube n =
            ⋂ i, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
          ext x
          simp [unitCube]
        rw [heq]
        exact MeasurableSet.iInter (fun i => measurable_pi_apply i measurableSet_Icc)
      have hmono : MeasurableSet {x : Fin n → ℝ | Monotone (x ∘ σ)} := by
        have hcont : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
        exact (isClosed_monotone.preimage hcont).measurableSet
      exact hc.inter hmono)
    (fun x hx => sortedSample_eq_comp_of_monotone n σ x hx.2))]
  exact permutation_chamber_coord_map n σ

/-- Lebesgue measure on the cube is the finite sum of its permutation chambers;
overlaps lie on equal-coordinate faces and therefore have zero measure. -/
private theorem cube_chamber_decomposition (n : ℕ) :
    volume.restrict (unitCube n) =
      ∑ σ : Equiv.Perm (Fin n),
        volume.restrict {x : Fin n → ℝ | x ∈ unitCube n ∧ Monotone (x ∘ σ)} := by
  let s (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
    {x | x ∈ unitCube n ∧ Monotone (x ∘ σ)}
  have hm (σ : Equiv.Perm (Fin n)) : MeasurableSet (s σ) := by
    have hc : MeasurableSet (unitCube n) := by
      have heq : unitCube n =
          ⋂ i, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
        ext x
        simp [unitCube]
      rw [heq]
      exact MeasurableSet.iInter (fun i => measurable_pi_apply i measurableSet_Icc)
    have hmono : MeasurableSet {x : Fin n → ℝ | Monotone (x ∘ σ)} := by
      have hcont : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      exact (isClosed_monotone.preimage hcont).measurableSet
    exact hc.inter hmono
  have hu : (⋃ σ, s σ) = unitCube n := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨σ, hx⟩
      exact hx.1
    · intro hx
      exact ⟨Tuple.sort x, hx, Tuple.monotone_sort x⟩
  have hd : Pairwise (fun σ τ => AEDisjoint volume (s σ) (s τ)) := by
    intro σ τ hne
    have hk : ∃ k, σ k ≠ τ k := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨k, hk⟩ := hk
    change volume (s σ ∩ s τ) = 0
    apply measure_mono_null (t := {x : Fin n → ℝ | x (σ k) = x (τ k)})
    · rintro x ⟨hxσ, hxτ⟩
      exact congrFun (Tuple.unique_monotone hxσ.2 hxτ.2) k
    · exact equal_coordinate_face_null n (σ k) (τ k) hk
  calc
    volume.restrict (unitCube n) = volume.restrict (⋃ σ, s σ) := by rw [hu]
    _ = Measure.sum (fun σ => volume.restrict (s σ)) :=
      Measure.restrict_iUnion_ae hd (fun σ => (hm σ).nullMeasurableSet)
    _ = ∑ σ, volume.restrict (s σ) := Measure.sum_fintype _
    _ = _ := rfl

/-- Given [a finite dimension](hyp:n), [sorting Lebesgue measure on the unit cube yields factorial density on the ordered chamber](goal). -/
theorem sorted_cube_law (n : ℕ) :
    (volume.restrict (unitCube n)).map (sortedSample n) =
      (n.factorial : ENNReal) • (volume.restrict (orderedUnitRegion n)) := by
  let s (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
    {x | x ∈ unitCube n ∧ Monotone (x ∘ σ)}
  have hs (σ : Equiv.Perm (Fin n)) : MeasurableSet (s σ) := by
    have hc : MeasurableSet (unitCube n) := by
      have heq : unitCube n =
          ⋂ i, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
        ext x
        simp [unitCube]
      rw [heq]
      exact MeasurableSet.iInter (fun i => measurable_pi_apply i measurableSet_Icc)
    have hmono : MeasurableSet {x : Fin n → ℝ | Monotone (x ∘ σ)} := by
      have hcont : Continuous (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
      exact (isClosed_monotone.preimage hcont).measurableSet
    exact hc.inter hmono
  have hm (σ : Equiv.Perm (Fin n)) :
      AEMeasurable (sortedSample n) (volume.restrict (s σ)) := by
    have hperm : Measurable (fun x : Fin n → ℝ => x ∘ σ) := by fun_prop
    exact hperm.aemeasurable.congr
      (ae_restrict_of_forall_mem (hs σ)
        (fun x hx => (sortedSample_eq_comp_of_monotone n σ x hx.2).symm))
  have hsum : AEMeasurable (sortedSample n)
      (∑ σ : Equiv.Perm (Fin n), volume.restrict (s σ)) := by
    rw [← Measure.sum_fintype]
    exact AEMeasurable.sum_measure hm
  calc
    (volume.restrict (unitCube n)).map (sortedSample n) =
        (∑ σ : Equiv.Perm (Fin n), volume.restrict (s σ)).map
          (sortedSample n) := by rw [cube_chamber_decomposition]
    _ = ∑ σ : Equiv.Perm (Fin n),
          (volume.restrict (s σ)).map (sortedSample n) :=
      Measure.map_finset_sum' hsum
    _ = ∑ _σ : Equiv.Perm (Fin n), volume.restrict (orderedUnitRegion n) := by
      simp only [s, permutation_chamber_map]
    _ = (n.factorial : ENNReal) • (volume.restrict (orderedUnitRegion n)) := by
      simp [Finset.sum_const, Fintype.card_perm, Nat.cast_smul_eq_nsmul]

/-- Given [a finite sample size](hyp:n), [the sorted iid unit-uniform sample has factorial density on the ordered unit region](goal). -/
theorem sorted_uniform_law (n : ℕ) :
    (iidSample uniform01 n).map (sortedSample n) =
      (n.factorial : ENNReal) • (volume.restrict (orderedUnitRegion n)) := by
  rw [iid_uniform_cube_law]
  exact sorted_cube_law n

end
end Causalean.Stat.OrderStatistic
