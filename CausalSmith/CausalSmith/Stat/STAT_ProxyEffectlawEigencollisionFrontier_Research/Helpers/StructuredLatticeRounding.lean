import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeOracle

/-! # Coordinate rounding for the structured lattice comparator -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

noncomputable section

open scoped Matrix.Norms.L2Operator

/-- The prescribed height is positive on the core domain. -/
lemma latticeHeight_pos {k dx n : ℕ} {pi0 sigma0 : ℝ} (hk : 0 < k) :
    0 < latticeHeight k dx n pi0 sigma0 := by
  unfold latticeHeight
  omega

/-- The height contains the reciprocal-mass ceiling required by largest-remainder rounding. -/
lemma ceil_inv_le_latticeHeight (k dx n : ℕ) (pi0 sigma0 : ℝ) :
    ⌈pi0⁻¹⌉₊ ≤ latticeHeight k dx n pi0 sigma0 := by
  unfold latticeHeight
  omega

/-- The height's explicit polar term makes the signal-basis mesh at most one quarter. -/
lemma sqrt_card_mul_latticeMesh_le_quarter
    {k dx n : ℕ} {pi0 sigma0 : ℝ} (hk : 0 < k) :
    Real.sqrt (dx * k) * latticeMesh k dx n pi0 sigma0 ≤ 1 / 4 := by
  let H := latticeHeight k dx n pi0 sigma0
  have hHnat : 0 < H := latticeHeight_pos hk
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hceil : ⌈4 * Real.sqrt (dx * k)⌉₊ ≤ H := by
    dsimp [H]
    unfold latticeHeight
    omega
  have hsqrt : 4 * Real.sqrt (dx * k) ≤ (H : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  unfold latticeMesh
  change Real.sqrt (dx * k) * (H : ℝ)⁻¹ ≤ 1 / 4
  rw [← div_eq_mul_inv, div_le_iff₀ hHr]
  nlinarith

/-- The height's conditioning term makes square-coordinate rounding preserve half the model
singular margin. -/
lemma k_mul_latticeMesh_le_half_sigma
    {k dx n : ℕ} {pi0 sigma0 : ℝ} (hk : 0 < k) (hsigma : 0 < sigma0) :
    (k : ℝ) * latticeMesh k dx n pi0 sigma0 ≤ sigma0 / 2 := by
  let H := latticeHeight k dx n pi0 sigma0
  have hHnat : 0 < H := latticeHeight_pos hk
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hceil : ⌈2 * k / sigma0⌉₊ ≤ H := by
    dsimp [H]
    unfold latticeHeight
    omega
  have hbase : 2 * (k : ℝ) / sigma0 ≤ (H : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  unfold latticeMesh
  change (k : ℝ) * (H : ℝ)⁻¹ ≤ sigma0 / 2
  rw [← div_eq_mul_inv, div_le_iff₀ hHr]
  have := (div_le_iff₀ hsigma).mp hbase
  nlinarith

/-- On the core size and envelope domain, the basic `2k` height term also leaves enough norm
budget for square-coordinate rounding. -/
lemma k_mul_latticeMesh_le_sqrt_mul
    {k dx n : ℕ} {pi0 sigma0 L : ℝ} (hk : 2 ≤ k) (hL : 1 ≤ L) :
    (k : ℝ) * latticeMesh k dx n pi0 sigma0 ≤ Real.sqrt k * L := by
  let H := latticeHeight k dx n pi0 sigma0
  have hkpos : 0 < k := by omega
  have hHnat : 0 < H := latticeHeight_pos hkpos
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHnat
  have h2k : 2 * k ≤ H := by
    dsimp [H]
    unfold latticeHeight
    omega
  have hhalf : (k : ℝ) / H ≤ 1 / 2 := by
    rw [div_le_iff₀ hHr]
    have h2k' : 2 * (k : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2k
    nlinarith
  have hsqrt : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ k))
  unfold latticeMesh
  change (k : ℝ) * (H : ℝ)⁻¹ ≤ Real.sqrt k * L
  rw [← div_eq_mul_inv]
  calc
    (k : ℝ) / H ≤ 1 / 2 := hhalf
    _ ≤ 1 := by norm_num
    _ ≤ Real.sqrt k * L := by nlinarith [mul_le_mul hsqrt hL (by norm_num) (by norm_num)]

/-- A rectangular matrix whose entries are uniformly bounded by `M` has Euclidean operator norm
at most `sqrt (rows * cols) * M`.  This is the sharp dimension factor needed when rounding the
signal basis coordinatewise. -/
lemma matrixCLM_norm_le_sqrt_card_mul_of_entry_abs_le
    {rows cols : ℕ} {M : ℝ} (hM : 0 ≤ M) (A : RectMatrix rows cols)
    (hA : ∀ i j, |A i j| ≤ M) :
    ‖matrixCLM A‖ ≤ Real.sqrt (rows * cols) * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hM)
  intro x
  have hrow (i : Fin rows) :
      ((Matrix.toEuclideanLin A x) i) ^ 2 ≤ (cols : ℝ) * M ^ 2 * ‖x‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin cols))
      (A i) (fun j => x j)
    have hentries : ∑ j : Fin cols, (A i j) ^ 2 ≤ (cols : ℝ) * M ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin cols, M ^ 2 := Finset.sum_le_sum fun j _ => by
          have := (sq_le_sq₀ (abs_nonneg (A i j)) hM).2 (hA i j)
          simpa [sq_abs] using this
        _ = (cols : ℝ) * M ^ 2 := by simp
    have hxsum : ∑ j : Fin cols, (x j) ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec] 
    calc
      (∑ j : Fin cols, A i j * x j) ^ 2
          ≤ (∑ j : Fin cols, (A i j) ^ 2) * ∑ j : Fin cols, (x j) ^ 2 := by
            simpa using hcs
      _ ≤ ((cols : ℝ) * M ^ 2) * ‖x‖ ^ 2 := by
        rw [hxsum]
        exact mul_le_mul_of_nonneg_right hentries (sq_nonneg _)
  have hsum : ∑ i : Fin rows, ((Matrix.toEuclideanLin A x) i) ^ 2 ≤
      (rows : ℝ) * ((cols : ℝ) * M ^ 2 * ‖x‖ ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin rows, ((cols : ℝ) * M ^ 2 * ‖x‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  have hout0 : 0 ≤ ‖Matrix.toEuclideanLin A x‖ := norm_nonneg _
  have hrhs0 : 0 ≤ Real.sqrt (rows * cols) * M * ‖x‖ := by positivity
  apply (sq_le_sq₀ hout0 hrhs0).1
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i : Fin rows, ((Matrix.toEuclideanLin A x) i) ^ 2
        ≤ (rows : ℝ) * ((cols : ℝ) * M ^ 2 * ‖x‖ ^ 2) := hsum
    _ = (Real.sqrt (rows * cols) * M * ‖x‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      ring

/-- Largest-remainder rounding of a finite probability vector.  Each allocated numerator differs
from its unrounded value by at most one, and any lower bound already satisfied by every floor is
preserved. -/
lemma simplex_largestRemainder_round
    {k H : ℕ} (hk : 0 < k) (hH : 0 < H) (p : Fin k → ℝ)
    (hp : ∀ u, 0 ≤ p u) (hsum : ∑ u, p u = 1) :
    ∃ a : Fin k → ℕ,
      (∀ u, ⌊(H : ℝ) * p u⌋₊ ≤ a u) ∧
      (∀ u, |(a u : ℝ) / H - p u| ≤ (H : ℝ)⁻¹) ∧
      ∑ u, a u = H := by
  classical
  let b : Fin k → ℕ := fun u => ⌊(H : ℝ) * p u⌋₊
  have hb_le (u : Fin k) : (b u : ℝ) ≤ (H : ℝ) * p u := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg H) (hp u))
  have hbSum_le : ∑ u, b u ≤ H := by
    have hreal : (∑ u, (b u : ℝ)) ≤ ∑ u, (H : ℝ) * p u :=
      Finset.sum_le_sum fun u _ => hb_le u
    rw [← Finset.mul_sum, hsum, mul_one] at hreal
    exact_mod_cast hreal
  have hH_le : H ≤ ∑ u, b u + k := by
    have hterm (u : Fin k) : (H : ℝ) * p u ≤ (b u : ℝ) + 1 :=
      (Nat.lt_floor_add_one ((H : ℝ) * p u)).le
    have hreal : ∑ u, (H : ℝ) * p u ≤ ∑ u, ((b u : ℝ) + 1) :=
      Finset.sum_le_sum fun u _ => hterm u
    rw [← Finset.mul_sum, hsum, mul_one, Finset.sum_add_distrib] at hreal
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hreal
    exact_mod_cast hreal
  let d := H - ∑ u, b u
  have hd : d ≤ k := by dsimp [d]; omega
  have hd' : d ≤ (Finset.univ : Finset (Fin k)).card := by simpa using hd
  obtain ⟨S, hSuniv, hScard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin k))) hd'
  let a : Fin k → ℕ := fun u => b u + if u ∈ S then 1 else 0
  refine ⟨a, ?_, ?_, ?_⟩
  · intro u
    dsimp [a]
    change b u ≤ b u + if u ∈ S then 1 else 0
    omega
  · intro u
    have hbLower := hb_le u
    have hbUpper : (H : ℝ) * p u < (b u : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    have hid : (a u : ℝ) / H - p u =
        ((a u : ℝ) - (H : ℝ) * p u) / H := by
      field_simp
    by_cases hu : u ∈ S
    · have habs : |(a u : ℝ) - (H : ℝ) * p u| ≤ 1 := by
        dsimp [a]
        rw [if_pos hu, abs_le]
        push_cast
        constructor <;> nlinarith
      rw [hid, abs_div, abs_of_pos hHr, inv_eq_one_div]
      exact (div_le_div_iff_of_pos_right hHr).2 habs
    · have habs : |(a u : ℝ) - (H : ℝ) * p u| ≤ 1 := by
        dsimp [a]
        rw [if_neg hu, add_zero, abs_le]
        constructor <;> nlinarith
      rw [hid, abs_div, abs_of_pos hHr, inv_eq_one_div]
      exact (div_le_div_iff_of_pos_right hHr).2 habs
  · dsimp [a]
    rw [Finset.sum_add_distrib]
    have hind : (∑ u : Fin k, if u ∈ S then 1 else 0) = S.card := by
      simpa using Finset.sum_boole (s := (Finset.univ : Finset (Fin k)))
        (p := fun u => u ∈ S)
    rw [hind, hScard]
    dsimp [d]
    omega

/-- Under the model's doubled latent-mass floor and `H ≥ ceil(pi0⁻¹)`, largest-remainder
rounding lands in the prescribed floor-constrained simplex. -/
lemma simplex_largestRemainder_round_with_floor
    {k H : ℕ} {pi0 : ℝ} (hk : 0 < k) (hH : 0 < H)
    (hpi : 0 < pi0) (hHpi : ⌈pi0⁻¹⌉₊ ≤ H)
    (p : Fin k → ℝ) (hp : ∀ u, 2 * pi0 ≤ p u)
    (hsum : ∑ u, p u = 1) :
    ∃ a : Fin k → ℕ,
      (∀ u, ⌈pi0 * H⌉₊ ≤ a u ∧
        |(a u : ℝ) / H - p u| ≤ (H : ℝ)⁻¹) ∧
      ∑ u, a u = H := by
  have hp0 (u : Fin k) : 0 ≤ p u := (by linarith [hp u, hpi] : 0 ≤ p u)
  obtain ⟨a, haFloor, haError, haSum⟩ :=
    simplex_largestRemainder_round hk hH p hp0 hsum
  refine ⟨a, ?_, haSum⟩
  intro u
  refine ⟨?_, haError u⟩
  apply (Nat.ceil_le).2
  let x : ℝ := pi0 * H
  let y : ℝ := (H : ℝ) * p u
  have hHreal : (pi0⁻¹ : ℝ) ≤ H :=
    (Nat.le_ceil (pi0⁻¹ : ℝ)).trans (by exact_mod_cast hHpi)
  have hx : 1 ≤ x := by
    dsimp [x]
    have := mul_le_mul_of_nonneg_left hHreal hpi.le
    field_simp at this
    simpa [mul_comm] using this
  have hy : 2 * x ≤ y := by
    dsimp [x, y]
    have hh := mul_le_mul_of_nonneg_left (hp u) (Nat.cast_nonneg H)
    nlinarith
  have hyFloor : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hxFloor : x ≤ (⌊y⌋₊ : ℝ) := by linarith
  exact hxFloor.trans (by exact_mod_cast haFloor u)

/-- Euclidean form of the largest-remainder error bound used in the frozen estimate (88). -/
lemma simplex_largestRemainder_round_with_floor_l2
    {k H : ℕ} {pi0 : ℝ} (hk : 0 < k) (hH : 0 < H)
    (hpi : 0 < pi0) (hHpi : ⌈pi0⁻¹⌉₊ ≤ H)
    (p : Fin k → ℝ) (hp : ∀ u, 2 * pi0 ≤ p u)
    (hsum : ∑ u, p u = 1) :
    ∃ a : Fin k → ℕ,
      (∀ u, ⌈pi0 * H⌉₊ ≤ a u) ∧
      Real.sqrt (∑ u, ((a u : ℝ) / H - p u) ^ 2) ≤
        Real.sqrt k * (H : ℝ)⁻¹ ∧
      ∑ u, a u = H := by
  obtain ⟨a, ha, haSum⟩ :=
    simplex_largestRemainder_round_with_floor hk hH hpi hHpi p hp hsum
  refine ⟨a, fun u => (ha u).1, ?_, haSum⟩
  let q : ℝ := (H : ℝ)⁻¹
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hterm (u : Fin k) : ((a u : ℝ) / H - p u) ^ 2 ≤ q ^ 2 := by
    have habs : |(a u : ℝ) / H - p u| ≤ q := by simpa [q] using (ha u).2
    have hsquare := (sq_le_sq₀ (abs_nonneg ((a u : ℝ) / H - p u)) hq).2 habs
    simpa [sq_abs] using hsquare
  have hsumSq : ∑ u, ((a u : ℝ) / H - p u) ^ 2 ≤ (k : ℝ) * q ^ 2 := by
    calc
      _ ≤ ∑ _u : Fin k, q ^ 2 := Finset.sum_le_sum fun u _ => hterm u
      _ = (k : ℝ) * q ^ 2 := by simp
  have hsum0 : 0 ≤ ∑ u, ((a u : ℝ) / H - p u) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsqrtk0 : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hsqrtSum0 : 0 ≤ Real.sqrt (∑ u, ((a u : ℝ) / H - p u) ^ 2) :=
    Real.sqrt_nonneg _
  rw [show (H : ℝ)⁻¹ = q by rfl]
  apply (sq_le_sq₀ hsqrtSum0 (mul_nonneg hsqrtk0 hq)).1
  rw [Real.sq_sqrt hsum0, mul_pow, Real.sq_sqrt hk0]
  exact hsumSq

/-- Rounding toward zero puts a bounded scalar on the clipped `1/H` lattice without leaving its
support interval. -/
lemma clipped_lattice_round {H : ℕ} {radius x : ℝ} (hH : 0 < H)
    (hradius : 0 ≤ radius) (hx : x ∈ Set.Icc (-radius) radius) :
    ∃ z : ℤ, (H : ℝ)⁻¹ * z ∈ Set.Icc (-radius) radius ∧
      |(H : ℝ)⁻¹ * z - x| ≤ (H : ℝ)⁻¹ := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hq : 0 < (H : ℝ)⁻¹ := inv_pos.mpr hHr
  by_cases hx0 : 0 ≤ x
  · let z : ℤ := ⌊(H : ℝ) * x⌋
    have hz0 : (0 : ℝ) ≤ z := by
      exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg hHr.le hx0))
    have hzle : (z : ℝ) ≤ (H : ℝ) * x := Int.floor_le _
    have hxlt : (H : ℝ) * x < (z : ℝ) + 1 := Int.lt_floor_add_one _
    have hy0 : 0 ≤ (H : ℝ)⁻¹ * (z : ℝ) := mul_nonneg hq.le hz0
    have hyle : (H : ℝ)⁻¹ * (z : ℝ) ≤ x := by
      rw [inv_mul_eq_div, div_le_iff₀ hHr]
      simpa [mul_comm] using hzle
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · exact (neg_nonpos.mpr hradius).trans hy0
    · exact hyle.trans hx.2
    · rw [abs_of_nonpos (sub_nonpos.mpr hyle)]
      rw [neg_sub]
      rw [sub_le_iff_le_add]
      rw [inv_mul_eq_div, inv_eq_one_div]
      rw [show 1 / (H : ℝ) + (z : ℝ) / H = (1 + (z : ℝ)) / H by ring]
      apply (le_div_iff₀ hHr).2
      nlinarith
  · have hxneg : x < 0 := lt_of_not_ge hx0
    let z : ℤ := ⌈(H : ℝ) * x⌉
    have hz0 : (z : ℝ) ≤ 0 := by
      exact_mod_cast (Int.ceil_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos hHr.le hxneg.le))
    have hxle : (H : ℝ) * x ≤ (z : ℝ) := Int.le_ceil _
    have hzlt : (z : ℝ) < (H : ℝ) * x + 1 := Int.ceil_lt_add_one _
    have hyle0 : (H : ℝ)⁻¹ * (z : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le hz0
    have hxley : x ≤ (H : ℝ)⁻¹ * (z : ℝ) := by
      rw [inv_mul_eq_div, le_div_iff₀ hHr]
      simpa [mul_comm] using hxle
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · exact hx.1.trans hxley
    · exact hyle0.trans hradius
    · rw [abs_of_nonneg (sub_nonneg.mpr hxley)]
      rw [sub_le_iff_le_add]
      rw [inv_mul_eq_div, inv_eq_one_div]
      apply (div_le_iff₀ hHr).2
      field_simp
      nlinarith

/-- Coordinatewise clipped rounding for rectangular matrices. -/
lemma clipped_lattice_round_matrix {rows cols H : ℕ} {radius : ℝ}
    (hH : 0 < H) (hradius : 0 ≤ radius) (A : RectMatrix rows cols)
    (hA : ∀ i j, |A i j| ≤ radius) :
    ∃ G : RectMatrix rows cols,
      (∀ i j, ∃ z : ℤ, G i j = (H : ℝ)⁻¹ * z ∧ |G i j| ≤ radius) ∧
      ∀ i j, |G i j - A i j| ≤ (H : ℝ)⁻¹ := by
  classical
  have hpoint (i : Fin rows) (j : Fin cols) :
      ∃ z : ℤ, (H : ℝ)⁻¹ * z ∈ Set.Icc (-radius) radius ∧
        |(H : ℝ)⁻¹ * z - A i j| ≤ (H : ℝ)⁻¹ :=
    clipped_lattice_round hH hradius (abs_le.mp (hA i j))
  let z : Fin rows → Fin cols → ℤ := fun i j => Classical.choose (hpoint i j)
  let G : RectMatrix rows cols := fun i j => (H : ℝ)⁻¹ * z i j
  refine ⟨G, ?_, ?_⟩
  · intro i j
    refine ⟨z i j, rfl, ?_⟩
    exact abs_le.mpr (Classical.choose_spec (hpoint i j)).1
  · intro i j
    exact (Classical.choose_spec (hpoint i j)).2

/-- Operator-norm form of coordinatewise matrix rounding, with the exact Frobenius-to-operator
dimension factor used by the comparator construction. -/
lemma clipped_lattice_round_matrix_norm {rows cols H : ℕ} {radius : ℝ}
    (hH : 0 < H) (hradius : 0 ≤ radius) (A : RectMatrix rows cols)
    (hA : ∀ i j, |A i j| ≤ radius) :
    ∃ G : RectMatrix rows cols,
      (∀ i j, ∃ z : ℤ, G i j = (H : ℝ)⁻¹ * z ∧ |G i j| ≤ radius) ∧
      ‖matrixCLM (G - A)‖ ≤ Real.sqrt (rows * cols) * (H : ℝ)⁻¹ := by
  obtain ⟨G, hgrid, herr⟩ := clipped_lattice_round_matrix hH hradius A hA
  refine ⟨G, hgrid, ?_⟩
  apply matrixCLM_norm_le_sqrt_card_mul_of_entry_abs_le (by positivity)
  intro i j
  simpa only [Matrix.sub_apply] using herr i j

/-- Every supplied orthonormal signal basis has all of its `k` column singular values at least
one (in fact equal to one). -/
lemma SignalBasis.one_le_signalMinSingular {dx k : ℕ} (V : SignalBasis dx k)
    (hk : 0 < k) : 1 ≤ signalMinSingular V.V := by
  apply Causalean.Mathlib.Analysis.le_singularValues_of_subspace
      (Matrix.toEuclideanLin V.V) ⊤ (by norm_num)
  · simpa using hk
  · intro x _hx
    have hn := (signalBasisLinearIsometry V).norm_map x
    rw [one_mul]
    exact hn.symm.le

/-- Coordinate rounding of an orthonormal signal basis produces a valid grid matrix.  Weyl's
inequality preserves the asserted singular margin under the frozen quarter-radius condition. -/
lemma SignalBasis.exists_rounded_gridBasis
    {dx k H : ℕ} (V : SignalBasis dx k) (hk : 0 < k) (hH : 0 < H)
    (hmesh : Real.sqrt (dx * k) * (H : ℝ)⁻¹ ≤ 1 / 4) :
    ∃ G : RectMatrix dx k,
      (∀ i j, ∃ z : ℤ, G i j = (H : ℝ)⁻¹ * z ∧ |G i j| ≤ 1) ∧
      ‖matrixCLM (G - V.V)‖ ≤ Real.sqrt (dx * k) * (H : ℝ)⁻¹ ∧
      1 / 2 ≤ signalMinSingular G := by
  have hentry (i : Fin dx) (j : Fin k) : |V.V i j| ≤ 1 := by
    let v : Euc dx := WithLp.toLp 2 (fun a => V.V a j)
    have hv : ‖v‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      have hj := V.orthonormal j j
      rw [if_pos rfl] at hj
      rw [show (∑ x, ‖v.ofLp x‖ ^ 2) = 1 by
        simpa [v, Real.norm_eq_abs, sq_abs, pow_two] using hj, Real.sqrt_one]
    have hi := PiLp.norm_apply_le v i
    rw [hv] at hi
    simpa [v, Real.norm_eq_abs] using hi
  obtain ⟨G, hgrid, hnorm⟩ :=
    clipped_lattice_round_matrix_norm hH (by norm_num) V.V hentry
  refine ⟨G, hgrid, hnorm, ?_⟩
  have hw := singular_value_weyl (j := k - 1) V.V (G - V.V)
  have hadd : V.V + (G - V.V) = G := by abel
  rw [hadd] at hw
  have hbase := V.one_le_signalMinSingular hk
  simp only [signalMinSingular] at hw hbase ⊢
  have hlower := (abs_le.mp hw).1
  linarith

/-- A well-conditioned square coordinate matrix can be rounded to the prescribed clipped lattice
while retaining half its singular margin and the doubled norm budget. -/
lemma exists_rounded_conditioned_matrix
    {k H : ℕ} {L sigma0 : ℝ} (hH : 0 < H) (hL : 0 ≤ L)
    (hsigma : 0 ≤ sigma0) (R : RectMatrix k k)
    (hRmin : sigma0 ≤ signalMinSingular R)
    (hRnorm : ‖matrixCLM R‖ ≤ Real.sqrt k * L)
    (hmargin : (k : ℝ) * (H : ℝ)⁻¹ ≤ sigma0 / 2)
    (hbudget : (k : ℝ) * (H : ℝ)⁻¹ ≤ Real.sqrt k * L) :
    ∃ Rn : RectMatrix k k,
      (∀ i j, ∃ z : ℤ, Rn i j = (H : ℝ)⁻¹ * z) ∧
      ‖matrixCLM (Rn - R)‖ ≤ (k : ℝ) * (H : ℝ)⁻¹ ∧
      sigma0 / 2 ≤ signalMinSingular Rn ∧
      ‖matrixCLM Rn‖ ≤ 2 * Real.sqrt k * L := by
  have hradius : 0 ≤ 2 * Real.sqrt k * L := by positivity
  have hentry (i j : Fin k) : |R i j| ≤ 2 * Real.sqrt k * L := by
    calc
      |R i j| ≤ ‖matrixCLM R‖ := abs_matrix_entry_le_matrixCLM_norm R i j
      _ ≤ Real.sqrt k * L := hRnorm
      _ ≤ 2 * Real.sqrt k * L := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg k) hL]
  obtain ⟨Rn, hgridClip, herr'⟩ :=
    clipped_lattice_round_matrix_norm hH hradius R hentry
  have hsqrtkk : Real.sqrt (k * k) = (k : ℝ) := by
    push_cast
    rw [show (k : ℝ) * k = (k : ℝ) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
  have herr : ‖matrixCLM (Rn - R)‖ ≤ (k : ℝ) * (H : ℝ)⁻¹ := by
    simpa [hsqrtkk] using herr'
  refine ⟨Rn, fun i j => ⟨Classical.choose (hgridClip i j),
    (Classical.choose_spec (hgridClip i j)).1⟩, herr, ?_, ?_⟩
  · have hw := singular_value_weyl (j := k - 1) R (Rn - R)
    have hadd : R + (Rn - R) = Rn := by abel
    rw [hadd] at hw
    simp only [signalMinSingular] at hw hRmin ⊢
    have hlower := (abs_le.mp hw).1
    linarith
  · calc
      ‖matrixCLM Rn‖ = ‖matrixCLM (R + (Rn - R))‖ := by
        congr 2
        abel
      _ ≤ ‖matrixCLM R‖ + ‖matrixCLM (Rn - R)‖ := by
        change ‖R + (Rn - R)‖ ≤ ‖R‖ + ‖Rn - R‖
        exact norm_add_le _ _
      _ ≤ Real.sqrt k * L + Real.sqrt k * L := add_le_add hRnorm (herr.trans hbudget)
      _ = 2 * Real.sqrt k * L := by ring

/-- Coordinatewise clipped rounding for the effect vector. -/
lemma clipped_lattice_round_vector {k H : ℕ} {radius : ℝ}
    (hH : 0 < H) (hradius : 0 ≤ radius) (x : Fin k → ℝ)
    (hx : ∀ u, x u ∈ Set.Icc (-radius) radius) :
    ∃ y : Fin k → ℝ,
      (∀ u, y u ∈ Set.Icc (-radius) radius ∧
        ∃ z : ℤ, y u = (H : ℝ)⁻¹ * z) ∧
      ∀ u, |y u - x u| ≤ (H : ℝ)⁻¹ := by
  classical
  have hpoint (u : Fin k) := clipped_lattice_round hH hradius (hx u)
  let z : Fin k → ℤ := fun u => Classical.choose (hpoint u)
  let y : Fin k → ℝ := fun u => (H : ℝ)⁻¹ * z u
  refine ⟨y, ?_, ?_⟩
  · intro u
    exact ⟨(Classical.choose_spec (hpoint u)).1, z u, rfl⟩
  · intro u
    exact (Classical.choose_spec (hpoint u)).2

-- keep: generic Euclidean certificate for clipped lattice rounding in later estimators
/-- Euclidean error form of clipped coordinatewise vector rounding. -/
lemma clipped_lattice_round_vector_l2 {k H : ℕ} {radius : ℝ}
    (hH : 0 < H) (hradius : 0 ≤ radius) (x : Fin k → ℝ)
    (hx : ∀ u, x u ∈ Set.Icc (-radius) radius) :
    ∃ y : Fin k → ℝ,
      (∀ u, y u ∈ Set.Icc (-radius) radius ∧
        ∃ z : ℤ, y u = (H : ℝ)⁻¹ * z) ∧
      Real.sqrt (∑ u, (y u - x u) ^ 2) ≤ Real.sqrt k * (H : ℝ)⁻¹ := by
  obtain ⟨y, hy, herr⟩ := clipped_lattice_round_vector hH hradius x hx
  refine ⟨y, hy, ?_⟩
  have hq : 0 ≤ (H : ℝ)⁻¹ := by positivity
  have hterm (u : Fin k) : (y u - x u) ^ 2 ≤ ((H : ℝ)⁻¹) ^ 2 := by
    have hsquare := (sq_le_sq₀ (abs_nonneg (y u - x u)) hq).2 (herr u)
    simpa [sq_abs] using hsquare
  have hsum : ∑ u, (y u - x u) ^ 2 ≤ (k : ℝ) * ((H : ℝ)⁻¹) ^ 2 := by
    calc
      _ ≤ ∑ _u : Fin k, ((H : ℝ)⁻¹) ^ 2 :=
        Finset.sum_le_sum fun u _ => hterm u
      _ = _ := by simp
  have hsum0 : 0 ≤ ∑ u, (y u - x u) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hq)).1
  rw [Real.sq_sqrt hsum0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact hsum

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
