import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeAnalysis
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
# Finite enumeration of the prescribed structured lattice

The lattice is encoded by its bounded integer grid coordinates and simplex numerators.  This
gives the finite coordinate-key set used by exhaustive minimization without introducing a
precomputed library of model summaries.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

noncomputable section

/-- Integer coordinates large enough to encode a mesh-`1/H` scalar bounded by `B`. -/
abbrev BoundedLatticeInt (H : ℕ) (B : ℝ) :=
  {z : ℤ // z ∈ Finset.Icc (-⌈(H : ℝ) * B⌉ : ℤ) ⌈(H : ℝ) * B⌉}

private lemma integer_witness_mem_Icc (H : ℕ) (hH : 0 < H) (B x : ℝ) (z : ℤ)
    (hx : x = (H : ℝ)⁻¹ * z) (habs : |x| ≤ B) :
    z ∈ Finset.Icc (-⌈(H : ℝ) * B⌉ : ℤ) ⌈(H : ℝ) * B⌉ := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hz : (z : ℝ) = (H : ℝ) * x := by
    rw [hx]
    field_simp
  have habsz : |(z : ℝ)| ≤ (H : ℝ) * B := by
    rw [hz, abs_mul, abs_of_nonneg hHr.le]
    exact mul_le_mul_of_nonneg_left habs hHr.le
  simp only [Finset.mem_Icc]
  constructor
  · exact_mod_cast (calc
      (-(⌈(H : ℝ) * B⌉ : ℤ) : ℝ) ≤ -((H : ℝ) * B) := by
        simpa using neg_le_neg (Int.le_ceil ((H : ℝ) * B))
      _ ≤ -|(z : ℝ)| := neg_le_neg habsz
      _ ≤ (z : ℝ) := neg_abs_le _)
  · exact_mod_cast (calc
      (z : ℝ) ≤ |(z : ℝ)| := le_abs_self _
      _ ≤ (H : ℝ) * B := habsz
      _ ≤ (⌈(H : ℝ) * B⌉ : ℤ) := Int.le_ceil _)

/-- A finite integer/simplex code for one well-formed structured lattice point. -/
structure StructuredLatticeCode (k dx : ℕ) (H : ℕ) (L sigma0 radius : ℝ) where
  grid : Fin dx → Fin k → BoundedLatticeInt H 1
  coord : Fin k → Fin k → BoundedLatticeInt H (2 * Real.sqrt k * L)
  mass : Fin (k - 1) → Fin (H + 1)
  effect : Fin k → BoundedLatticeInt H radius
  deriving Fintype

/-- The encoder has exactly the paper's number of free mesh coordinates; the simplex contributes
`k-1` because its final mass is determined by the sum. -/
lemma structuredLatticeCode_card
    (k dx H : ℕ) (L sigma0 radius : ℝ) :
    Fintype.card (StructuredLatticeCode k dx H L sigma0 radius) =
      Fintype.card (BoundedLatticeInt H 1) ^ (dx * k) *
      Fintype.card (BoundedLatticeInt H (2 * Real.sqrt k * L)) ^ (k ^ 2) *
      (H + 1) ^ (k - 1) *
      Fintype.card (BoundedLatticeInt H radius) ^ k := by
  let e : StructuredLatticeCode k dx H L sigma0 radius ≃
      (Fin dx → Fin k → BoundedLatticeInt H 1) ×
      (Fin k → Fin k → BoundedLatticeInt H (2 * Real.sqrt k * L)) ×
      (Fin (k - 1) → Fin (H + 1)) ×
      (Fin k → BoundedLatticeInt H radius) :=
    { toFun := fun c => (c.grid, c.coord, c.mass, c.effect)
      invFun := fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro c; rcases c with ⟨_, _, _, _⟩; rfl }
  rw [Fintype.card_congr e]
  simp [pow_mul, pow_two]
  ring

private lemma wellFormed_grid_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (i : Fin dx) (j : Fin k) :
    ∃ z : ℤ, θ.gridBasis i j = latticeMesh k dx n pi0 sigma0 * z ∧
      |θ.gridBasis i j| ≤ 1 := by
  have h := hθ
  dsimp [StructuredLatticePoint.WellFormed] at h
  exact h.1 i j

private lemma wellFormed_coord_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (i j : Fin k) : ∃ z : ℤ, θ.R i j = latticeMesh k dx n pi0 sigma0 * z := by
  have h := hθ
  dsimp [StructuredLatticePoint.WellFormed] at h
  exact h.2.2.2.1 i j

private lemma wellFormed_mass_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)) :
    ∃ a : Fin k → ℕ,
      (∀ u, ⌈pi0 * latticeHeight k dx n pi0 sigma0⌉₊ ≤ a u ∧
        θ.weight u = a u / latticeHeight k dx n pi0 sigma0) ∧
      ∑ u, a u = latticeHeight k dx n pi0 sigma0 := by
  have h := hθ
  dsimp [StructuredLatticePoint.WellFormed] at h
  exact h.2.2.2.2.2.2.1

private lemma wellFormed_effect_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (u : Fin k) : ∃ z : ℤ, θ.effect u = latticeMesh k dx n pi0 sigma0 * z := by
  have h := hθ
  dsimp [StructuredLatticePoint.WellFormed] at h
  exact (h.2.2.2.2.2.2.2 u).2

private noncomputable def gridNumerator
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (i : Fin dx) (j : Fin k) : ℤ :=
  Classical.choose (wellFormed_grid_exists θ hθ i j)

private noncomputable def coordNumerator
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (i j : Fin k) : ℤ :=
  Classical.choose (wellFormed_coord_exists θ hθ i j)

private noncomputable def massNumerator
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)) :
    Fin k → ℕ :=
  Classical.choose (wellFormed_mass_exists θ hθ)

private noncomputable def effectNumerator
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (u : Fin k) : ℤ :=
  Classical.choose (wellFormed_effect_exists θ hθ u)

private noncomputable def structuredLatticeCode
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0)) :
    StructuredLatticeCode k dx (latticeHeight k dx n pi0 sigma0) L sigma0
      (effectRadius dz L sigma0) := by
  classical
  let H := latticeHeight k dx n pi0 sigma0
  let zg (i : Fin dx) (j : Fin k) : ℤ := gridNumerator θ hθ i j
  let zr (i j : Fin k) : ℤ := coordNumerator θ hθ i j
  let ze (u : Fin k) : ℤ := effectNumerator θ hθ u
  have hmass := Classical.choose_spec (wellFormed_mass_exists θ hθ)
  have hH0 : H ≠ 0 := by
    intro hzero
    have hweight : θ.weight = 0 := by
      funext u
      rw [hmass.1 u |>.2]
      simp [H, hzero]
    have hsumWeight := θ.lawValid.2.1
    rw [hweight] at hsumWeight
    simpa using hsumWeight
  have hH : 0 < H := Nat.pos_of_ne_zero hH0
  refine {
    grid := fun i j => ⟨zg i j, ?_⟩
    coord := fun i j => ⟨zr i j, ?_⟩
    mass := fun u => ⟨massNumerator θ hθ (Fin.castLE (Nat.sub_le k 1) u), ?_⟩
    effect := fun u => ⟨ze u, ?_⟩ }
  · exact integer_witness_mem_Icc H hH 1 (θ.gridBasis i j) (zg i j)
      (by simpa [H, latticeMesh, zg, gridNumerator] using
        (Classical.choose_spec (wellFormed_grid_exists θ hθ i j)).1)
      (Classical.choose_spec (wellFormed_grid_exists θ hθ i j)).2
  · have hentry : |θ.R i j| ≤ 2 * Real.sqrt k * L :=
      (abs_matrix_entry_le_matrixCLM_norm θ.R i j).trans (by
        have h := hθ
        dsimp [StructuredLatticePoint.WellFormed] at h
        exact h.2.2.2.2.2.1)
    exact integer_witness_mem_Icc H hH (2 * Real.sqrt k * L) (θ.R i j) (zr i j)
      (by simpa [H, latticeMesh, zr, coordNumerator] using
        (Classical.choose_spec (wellFormed_coord_exists θ hθ i j))) hentry
  · have hsum := hmass.2
    have hau : massNumerator θ hθ (Fin.castLE (Nat.sub_le k 1) u) ≤
        ∑ v, massNumerator θ hθ v :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (Fin.castLE (Nat.sub_le k 1) u))
    have hsum' : (∑ v, massNumerator θ hθ v) = H := by
      simpa [H, massNumerator] using hsum
    omega
  · exact integer_witness_mem_Icc H hH (effectRadius dz L sigma0) (θ.effect u) (ze u)
      (by simpa [H, latticeMesh, ze, effectNumerator] using
        (Classical.choose_spec (wellFormed_effect_exists θ hθ u)))
      (abs_le.mpr (by
        have h := hθ
        dsimp [StructuredLatticePoint.WellFormed] at h
        exact (h.2.2.2.2.2.2.2 u).1))

private lemma structuredLatticeCode_grid_spec
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (i : Fin dx) (j : Fin k) :
    θ.gridBasis i j = latticeMesh k dx n pi0 sigma0 *
      (((structuredLatticeCode θ hθ).grid i j : ℤ) : ℝ) := by
  classical
  change θ.gridBasis i j = latticeMesh k dx n pi0 sigma0 *
    ((gridNumerator θ hθ i j : ℤ) : ℝ)
  exact (Classical.choose_spec (wellFormed_grid_exists θ hθ i j)).1

private lemma structuredLatticeCode_coord_spec
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (i j : Fin k) :
    θ.R i j = latticeMesh k dx n pi0 sigma0 *
      (((structuredLatticeCode θ hθ).coord i j : ℤ) : ℝ) := by
  classical
  change θ.R i j = latticeMesh k dx n pi0 sigma0 *
    ((coordNumerator θ hθ i j : ℤ) : ℝ)
  exact Classical.choose_spec (wellFormed_coord_exists θ hθ i j)

private lemma structuredLatticeCode_mass_spec
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (u : Fin (k - 1)) :
    θ.weight (Fin.castLE (Nat.sub_le k 1) u) =
      (((structuredLatticeCode θ hθ).mass u : ℕ) : ℝ) /
      latticeHeight k dx n pi0 sigma0 := by
  classical
  change θ.weight (Fin.castLE (Nat.sub_le k 1) u) =
    ((massNumerator θ hθ (Fin.castLE (Nat.sub_le k 1) u) : ℕ) : ℝ) /
    latticeHeight k dx n pi0 sigma0
  exact (Classical.choose_spec (wellFormed_mass_exists θ hθ)).1 _ |>.2

private lemma structuredLatticeCode_effect_spec
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (θ : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (hθ : θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0))
    (u : Fin k) :
    θ.effect u = latticeMesh k dx n pi0 sigma0 *
      (((structuredLatticeCode θ hθ).effect u : ℤ) : ℝ) := by
  classical
  change θ.effect u = latticeMesh k dx n pi0 sigma0 *
    ((effectNumerator θ hθ u : ℤ) : ℝ)
  exact Classical.choose_spec (wellFormed_effect_exists θ hθ u)

private lemma structuredLatticeCode_injective
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} :
    Function.Injective (fun θ : {θ : StructuredLatticePoint k dx
        (effectRadius dz L sigma0) // θ.WellFormed (dz := dz) (n := n) (L := L)
          (pi0 := pi0) (sigma0 := sigma0)} => structuredLatticeCode θ.1 θ.2) := by
  classical
  intro θ φ hcode
  apply Subtype.ext
  rcases θ with ⟨θ, hθ⟩
  rcases φ with ⟨φ, hφ⟩
  dsimp only at hcode
  dsimp [StructuredLatticePoint.WellFormed] at hθ hφ
  have hg : θ.gridBasis = φ.gridBasis := by
    funext i j
    have hc := congrArg (fun c => (c.grid i j : ℤ)) hcode
    rw [structuredLatticeCode_grid_spec θ hθ, structuredLatticeCode_grid_spec φ hφ]
    rw [hc]
  have hV : θ.V = φ.V := by
    rcases hθ.2.1 with ⟨hGθ, hpolarθ⟩
    rcases hφ.2.1 with ⟨hGφ, hpolarφ⟩
    have hpolarEq : prescribedPolarFactor θ.gridBasis hGθ =
        prescribedPolarFactor φ.gridBasis hGφ := by
      unfold prescribedPolarFactor inverseGramSqrt
      simp only [hg]
    calc
      θ.V = prescribedPolarFactor θ.gridBasis hGθ := hpolarθ
      _ = prescribedPolarFactor φ.gridBasis hGφ := hpolarEq
      _ = φ.V := hpolarφ.symm
  have hR' : θ.R = φ.R := by
    funext i j
    have hc := congrArg (fun c => (c.coord i j : ℤ)) hcode
    rw [structuredLatticeCode_coord_spec θ hθ, structuredLatticeCode_coord_spec φ hφ]
    rw [hc]
  have hw : θ.weight = φ.weight := by
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      simpa using θ.lawValid.2.1
    let last : Fin k := ⟨k - 1, by omega⟩
    have hother (u : Fin k) (hu : u ≠ last) : θ.weight u = φ.weight u := by
      have hult : u.val < k - 1 := by
        by_contra hnot
        apply hu
        apply Fin.ext
        dsimp [last]
        omega
      let v : Fin (k - 1) := ⟨u.val, hult⟩
      have hc := congrArg (fun c => (c.mass v : ℕ)) hcode
      have hcast : Fin.castLE (Nat.sub_le k 1) v = u := by
        apply Fin.ext
        rfl
      have hθu := structuredLatticeCode_mass_spec θ hθ v
      have hφu := structuredLatticeCode_mass_spec φ hφ v
      rw [hcast] at hθu hφu
      rw [hθu, hφu, hc]
    have hsums : ∑ u ∈ Finset.univ.erase last, θ.weight u =
        ∑ u ∈ Finset.univ.erase last, φ.weight u := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hother u (Finset.ne_of_mem_erase hu)
    have hlast : θ.weight last = φ.weight last := by
      have hsumθ := θ.lawValid.2.1
      have hsumφ := φ.lawValid.2.1
      have hsplitθ := Finset.sum_erase_add Finset.univ θ.weight (Finset.mem_univ last)
      have hsplitφ := Finset.sum_erase_add Finset.univ φ.weight (Finset.mem_univ last)
      linarith
    funext u
    by_cases hu : u = last
    · simpa [hu] using hlast
    · exact hother u hu
  have he : θ.effect = φ.effect := by
    funext u
    have hc := congrArg (fun c => (c.effect u : ℤ)) hcode
    rw [structuredLatticeCode_effect_spec θ hθ, structuredLatticeCode_effect_spec φ hφ]
    rw [hc]
  cases θ
  cases φ
  simp_all

/-- The subtype of all well-formed points in the prescribed lattice is finite. -/
noncomputable instance structuredLatticeWellFormedFinite
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} :
    Finite {θ : StructuredLatticePoint k dx (effectRadius dz L sigma0) //
      θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)} :=
  Finite.of_injective
    (fun θ => structuredLatticeCode θ.1 θ.2) structuredLatticeCode_injective

/-- Coordinate keys which are realized by at least one well-formed lattice point.  Passing to
keys removes harmless duplicate grid bases having the same prescribed visible coordinates. -/
def StructuredLatticeKey (k dx dz n : ℕ) (L pi0 sigma0 : ℝ) :=
  {key : List ℝ // ∃ θ : StructuredLatticePoint k dx (effectRadius dz L sigma0),
    θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0) ∧
      structuredLatticeLexKey θ = key}

noncomputable instance structuredLatticeKeyLinearOrder
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} :
    LinearOrder (StructuredLatticeKey k dx dz n L pi0 sigma0) := by
  unfold StructuredLatticeKey
  infer_instance

noncomputable instance structuredLatticeKeyFinite
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} :
    Finite (StructuredLatticeKey k dx dz n L pi0 sigma0) := by
  let Source := {θ : StructuredLatticePoint k dx (effectRadius dz L sigma0) //
    θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)}
  let encode : Source → StructuredLatticeKey k dx dz n L pi0 sigma0 := fun θ =>
    ⟨structuredLatticeLexKey θ.1, θ.1, θ.2, rfl⟩
  exact Finite.of_surjective encode (by
    rintro ⟨key, θ, hθ, hkey⟩
    refine ⟨⟨θ, hθ⟩, Subtype.ext ?_⟩
    exact hkey)

noncomputable instance structuredLatticeKeyFintype
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} :
    Fintype (StructuredLatticeKey k dx dz n L pi0 sigma0) := Fintype.ofFinite _

private noncomputable def structuredLatticeKeyRepresentative
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (key : StructuredLatticeKey k dx dz n L pi0 sigma0) :
    StructuredLatticePoint k dx (effectRadius dz L sigma0) :=
  Classical.choose key.property

private lemma structuredLatticeKeyRepresentative_wellFormed
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (key : StructuredLatticeKey k dx dz n L pi0 sigma0) :
    (structuredLatticeKeyRepresentative key).WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0) :=
  (Classical.choose_spec key.property).1

private lemma structuredLatticeKeyRepresentative_key
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (key : StructuredLatticeKey k dx dz n L pi0 sigma0) :
    structuredLatticeLexKey (structuredLatticeKeyRepresentative key) = key.1 :=
  (Classical.choose_spec key.property).2

/-- Realized visible-coordinate keys inject into the integer encoder, so their cardinality is
bounded by the encoder's exact free-coordinate product. -/
lemma structuredLatticeKey_card_le_code
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} :
    Fintype.card (StructuredLatticeKey k dx dz n L pi0 sigma0) ≤
      Fintype.card (StructuredLatticeCode k dx (latticeHeight k dx n pi0 sigma0)
        L sigma0 (effectRadius dz L sigma0)) := by
  classical
  let Key := StructuredLatticeKey k dx dz n L pi0 sigma0
  letI : Fintype Key := Fintype.ofFinite Key
  let encode : Key → StructuredLatticeCode k dx (latticeHeight k dx n pi0 sigma0)
      L sigma0 (effectRadius dz L sigma0) := fun key =>
    structuredLatticeCode (structuredLatticeKeyRepresentative key)
      (structuredLatticeKeyRepresentative_wellFormed key)
  apply Fintype.card_le_of_injective encode
  intro x y hxy
  have hreps : structuredLatticeKeyRepresentative x =
      structuredLatticeKeyRepresentative y := by
    dsimp [encode] at hxy
    let rx : {θ : StructuredLatticePoint k dx (effectRadius dz L sigma0) //
        θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)} :=
      ⟨structuredLatticeKeyRepresentative x,
        structuredLatticeKeyRepresentative_wellFormed x⟩
    let ry : {θ : StructuredLatticePoint k dx (effectRadius dz L sigma0) //
        θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0)} :=
      ⟨structuredLatticeKeyRepresentative y,
        structuredLatticeKeyRepresentative_wellFormed y⟩
    have hxy' : structuredLatticeCode rx.1 rx.2 = structuredLatticeCode ry.1 ry.2 := by
      simpa only [rx, ry] using hxy
    have hsub :=
      (@structuredLatticeCode_injective k dx dz n L pi0 sigma0) hxy'
    exact congrArg Subtype.val hsub
  apply Subtype.ext
  calc
    x.1 = structuredLatticeLexKey (structuredLatticeKeyRepresentative x) :=
      (structuredLatticeKeyRepresentative_key x).symm
    _ = structuredLatticeLexKey (structuredLatticeKeyRepresentative y) :=
      congrArg structuredLatticeLexKey hreps
    _ = y.1 := structuredLatticeKeyRepresentative_key y

private lemma univList_map_injective {a : ℕ} {β : Type*} (f g : Fin a → β)
    (h : Finset.univ.toList.map f = Finset.univ.toList.map g) : f = g := by
  funext i
  have aux : ∀ (l : List (Fin a)), l.map f = l.map g → ∀ x ∈ l, f x = g x := by
    intro l hl
    induction l with
    | nil => simp
    | cons y l ih =>
        simp only [List.map_cons, List.cons.injEq] at hl
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hl.1
        · exact ih hl.2 x hx
  exact aux _ h i (by simp)

private lemma univList_flatMap_injective {a b : ℕ} {β : Type*}
    (f g : Fin a → Fin b → β)
    (h : Finset.univ.toList.flatMap (fun i => Finset.univ.toList.map (f i)) =
      Finset.univ.toList.flatMap (fun i => Finset.univ.toList.map (g i))) : f = g := by
  funext i
  have aux : ∀ (l : List (Fin a)),
      l.flatMap (fun i => Finset.univ.toList.map (f i)) =
        l.flatMap (fun i => Finset.univ.toList.map (g i)) →
      ∀ x ∈ l, f x = g x := by
    intro l hl
    induction l with
    | nil => simp
    | cons y l ih =>
        simp only [List.flatMap_cons] at hl
        obtain ⟨hy, htail⟩ := List.append_inj hl (by simp)
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact univList_map_injective _ _ hy
        · exact ih htail x hx
  exact aux _ h i (by simp)

private lemma structuredLatticeLexKey_injective_visible
    {k dx : ℕ} {radius : ℝ} (θ φ : StructuredLatticePoint k dx radius)
    (hkey : structuredLatticeLexKey θ = structuredLatticeLexKey φ) :
    θ.V = φ.V ∧ θ.R = φ.R ∧ θ.weight = φ.weight ∧ θ.effect = φ.effect := by
  let vθ := Finset.univ.toList.flatMap fun i : Fin dx =>
    Finset.univ.toList.map fun j : Fin k => θ.V i j
  let vφ := Finset.univ.toList.flatMap fun i : Fin dx =>
    Finset.univ.toList.map fun j : Fin k => φ.V i j
  let rθ := Finset.univ.toList.flatMap fun i : Fin k =>
    Finset.univ.toList.map fun j : Fin k => θ.R i j
  let rφ := Finset.univ.toList.flatMap fun i : Fin k =>
    Finset.univ.toList.map fun j : Fin k => φ.R i j
  let wθ := Finset.univ.toList.map fun i : Fin k => θ.weight i
  let wφ := Finset.univ.toList.map fun i : Fin k => φ.weight i
  let eθ := Finset.univ.toList.map fun i : Fin k => θ.effect i
  let eφ := Finset.univ.toList.map fun i : Fin k => φ.effect i
  change vθ ++ rθ ++ wθ ++ eθ = vφ ++ rφ ++ wφ ++ eφ at hkey
  obtain ⟨hvrw, he⟩ := List.append_inj hkey
    (by simp [vθ, vφ, rθ, rφ, wθ, wφ])
  obtain ⟨hvr, hw⟩ := List.append_inj hvrw (by simp [vθ, vφ, rθ, rφ])
  obtain ⟨hv, hr⟩ := List.append_inj hvr (by simp [vθ, vφ])
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact univList_flatMap_injective _ _ hv
  · exact univList_flatMap_injective _ _ hr
  · exact univList_map_injective _ _ hw
  · exact univList_map_injective _ _ he

/-- There is a duplicate-free exhaustive enumeration of the well-formed lattice, ordered by the
displayed lexicographic coordinate key. -/
theorem structuredLatticeEnumeration_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ} :
    ∃ (m : ℕ) (candidate : Fin m →
        StructuredLatticePoint k dx (effectRadius dz L sigma0)),
      (∀ i, (candidate i).WellFormed (dz := dz) (n := n) (L := L)
        (pi0 := pi0) (sigma0 := sigma0)) ∧
      (∀ θ : StructuredLatticePoint k dx (effectRadius dz L sigma0),
        θ.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0) →
          ∃ i, (candidate i).V = θ.V ∧ (candidate i).R = θ.R ∧
            (candidate i).weight = θ.weight ∧ (candidate i).effect = θ.effect) ∧
      (∀ i j, (candidate i).V = (candidate j).V →
        (candidate i).R = (candidate j).R →
        (candidate i).weight = (candidate j).weight →
        (candidate i).effect = (candidate j).effect → i = j) ∧
      ∀ i j, i ≤ j ↔ StructuredLatticePoint.LexLE (candidate i) (candidate j) := by
  classical
  let Key := StructuredLatticeKey k dx dz n L pi0 sigma0
  letI : Fintype Key := Fintype.ofFinite Key
  let e : Fin (Fintype.card Key) ≃o Key := Fintype.orderIsoFinOfCardEq Key rfl
  let candidate : Fin (Fintype.card Key) →
      StructuredLatticePoint k dx (effectRadius dz L sigma0) := fun i =>
    structuredLatticeKeyRepresentative (e i)
  refine ⟨Fintype.card Key, candidate, ?_, ?_, ?_, ?_⟩
  · intro i
    exact structuredLatticeKeyRepresentative_wellFormed (e i)
  · intro θ hθ
    let key : Key := ⟨structuredLatticeLexKey θ, θ, hθ, rfl⟩
    obtain ⟨i, hi⟩ := e.surjective key
    refine ⟨i, ?_⟩
    have hkeys : structuredLatticeLexKey (candidate i) = structuredLatticeLexKey θ := by
      rw [structuredLatticeKeyRepresentative_key]
      exact congrArg Subtype.val hi
    exact structuredLatticeLexKey_injective_visible _ _ hkeys
  · intro i j hV hR hw heffect
    apply e.injective
    apply Subtype.ext
    rw [← structuredLatticeKeyRepresentative_key (e i),
      ← structuredLatticeKeyRepresentative_key (e j)]
    simp [candidate, structuredLatticeLexKey, hV, hR, hw, heffect]
  · intro i j
    rw [← e.le_iff_le]
    change (e i).1 ≤ (e j).1 ↔ _
    rw [← structuredLatticeKeyRepresentative_key (e i),
      ← structuredLatticeKeyRepresentative_key (e j)]
    exact le_iff_eq_or_lt

/-- Any certified duplicate-free exhaustive lattice search has no more candidates than the exact
integer/simplex encoder. -/
lemma isPrescribedStructuredLattice_candidateCount_le_code
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A) :
    A.candidateCount ≤
      Fintype.card (StructuredLatticeCode k dx (latticeHeight k dx n pi0 sigma0)
        L sigma0 (effectRadius dz L sigma0)) := by
  classical
  obtain ⟨candidate, _first, hwf, _hcomplete, _hinj, horder, _hmin, _htie,
      _hestimate⟩ := hA
  let Key := StructuredLatticeKey k dx dz n L pi0 sigma0
  let encode : Fin A.candidateCount → Key := fun i =>
    ⟨structuredLatticeLexKey (candidate i), candidate i, hwf i, rfl⟩
  have hencode : Function.Injective encode := by
    intro i j hij
    have hkey : structuredLatticeLexKey (candidate i) =
        structuredLatticeLexKey (candidate j) := congrArg Subtype.val hij
    apply le_antisymm
    · exact (horder i j).2 (Or.inl hkey)
    · exact (horder j i).2 (Or.inl hkey.symm)
  calc
    A.candidateCount = Fintype.card (Fin A.candidateCount) := by simp
    _ ≤ Fintype.card Key := Fintype.card_le_of_injective encode hencode
    _ ≤ Fintype.card (StructuredLatticeCode k dx (latticeHeight k dx n pi0 sigma0)
        L sigma0 (effectRadius dz L sigma0)) := structuredLatticeKey_card_le_code

/-- A nonempty finite candidate family has a unique first minimizer: first minimize the displayed
real score, then minimize the enumeration index among ties. -/
theorem finite_first_minimizer_exists {α : Type*} {m : ℕ} (hm : 0 < m)
    (score : α → Fin m → ℝ) :
    ∃ first : α → Fin m,
      (∀ x i, score x (first x) ≤ score x i) ∧
      ∀ x i, score x (first x) = score x i → first x ≤ i := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hpointwise : ∀ x : α, ∃ j : Fin m,
      (∀ i, score x j ≤ score x i) ∧
      ∀ i, score x j = score x i → j ≤ i := by
    intro x
    obtain ⟨j, _hjmem, hj⟩ := Finset.exists_min_image Finset.univ (score x)
      (Finset.univ_nonempty : Finset.univ.Nonempty)
    let tied : Finset (Fin m) := Finset.univ.filter fun i => score x j = score x i
    have hjtied : j ∈ tied := by simp [tied]
    obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_min_image tied id ⟨j, hjtied⟩
    have hscore : score x j₀ = score x j := by
      exact (Finset.mem_filter.mp hj₀mem).2.symm
    refine ⟨j₀, ?_, ?_⟩
    · intro i
      rw [hscore]
      exact hj i (by simp)
    · intro i hi
      exact hj₀ i (by
        simp only [tied, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hscore, hi])
  refine ⟨fun x => Classical.choose (hpointwise x), ?_, ?_⟩
  · intro x i
    exact (Classical.choose_spec (hpointwise x)).1 i
  · intro x i hi
    exact (Classical.choose_spec (hpointwise x)).2 i hi

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
