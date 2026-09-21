module
public import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.NetLibraryCertificates
public import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeRounding
public import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TSummaryClosureCompact
public import Mathlib.Data.List.Lex

/-! Construction of the advised finite summary grid. -/

public section

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

noncomputable section

/-- If [the canonical mapped lists agree](hyp:h), [the underlying finite-indexed maps agree](goal). -/
-- @node: netLibrary_univList_map_injective
lemma netLibrary_univList_map_injective {a : ℕ} {β : Type*} (f g : Fin a → β)
    (h : Finset.univ.toList.map f = Finset.univ.toList.map g) : f = g := by
  funext i
  have aux : ∀ (l : List (Fin a)), l.map f = l.map g → ∀ x ∈ l, f x = g x := by
    intro l hl
    induction l with
    | nil => simp
    | cons y l ih =>
        simp only [List.map_cons, List.cons.injEq] at hl
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hl.1
        · exact ih hl.2 x hx
  exact aux _ h i (by simp)

/-- If [the canonical flattened coordinate lists agree](hyp:h), [the underlying finite-indexed
matrices agree](goal). -/
-- @node: netLibrary_univList_flatMap_injective
lemma netLibrary_univList_flatMap_injective {a b : ℕ} {β : Type*}
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
        rcases List.mem_cons.mp hx with rfl | hx
        · exact netLibrary_univList_map_injective _ _ hy
        · exact ih htail x hx
  exact aux _ h i (by simp)

/-- [The displayed lexicographic coordinate list determines a summary](goal). -/
-- @node: summaryLexKey_injective
lemma summaryLexKey_injective {dx dz : ℕ} :
    Function.Injective (@summaryLexKey dx dz) := by
  intro s q h
  let s0 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => s.M0 i j
  let q0 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => q.M0 i j
  let s1 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => s.M1 i j
  let q1 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => q.M1 i j
  let s2 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => s.N0 i j
  let q2 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => q.N0 i j
  let s3 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => s.N1 i j
  let q3 := Finset.univ.toList.flatMap fun i : Fin dz =>
    Finset.univ.toList.map fun j : Fin dx => q.N1 i j
  let s4 := Finset.univ.toList.map fun i : Fin dx => s.mX i
  let q4 := Finset.univ.toList.map fun i : Fin dx => q.mX i
  change s0 ++ s1 ++ s2 ++ s3 ++ s4 = q0 ++ q1 ++ q2 ++ q3 ++ q4 at h
  obtain ⟨hrest, h4⟩ := List.append_inj h
    (by simp [s0, q0, s1, q1, s2, q2, s3, q3])
  obtain ⟨hrest, h3⟩ := List.append_inj hrest
    (by simp [s0, q0, s1, q1, s2, q2])
  obtain ⟨hrest, h2⟩ := List.append_inj hrest
    (by simp [s0, q0, s1, q1])
  obtain ⟨h0, h1⟩ := List.append_inj hrest (by simp [s0, q0])
  cases s
  cases q
  congr
  · exact netLibrary_univList_flatMap_injective _ _ (by simpa [s0, q0] using h0)
  · exact netLibrary_univList_flatMap_injective _ _ (by simpa [s1, q1] using h1)
  · exact netLibrary_univList_flatMap_injective _ _ (by simpa [s2, q2] using h2)
  · exact netLibrary_univList_flatMap_injective _ _ (by simpa [s3, q3] using h3)
  · exact netLibrary_univList_map_injective _ _ (by simpa [s4, q4] using h4)

/-- Given [the latent lower bound](hyp:hk), [feature dimension bound](hyp:hkx), [proxy dimension
bound](hyp:hkz), [radius bound](hyp:hL), [treatment positivity](hyp:hpi), [treatment upper
bound](hyp:hpiMax), [noise positivity](hyp:hsigma), [noise upper bound](hyp:hsigmaMax), and
[positive mesh size](hyp:hn), [the bounded half-open coordinate grid supplies a finite feasible
representative library](goal). -/
-- @node: netLibrary_nonempty
theorem netLibrary_nonempty
    (k dx dz n : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) (hn : 1 ≤ n) :
    Nonempty (NetLibrary k dx dz n L pi0 sigma0) := by
  classical
  let scale : ℝ := (Real.sqrt n)⁻¹ /
    (4 * Real.sqrt (dz * dx) + Real.sqrt dx)
  have hdx : 0 < dx := lt_of_lt_of_le (by omega : 0 < k) hkx
  have hdz : 0 < dz := lt_of_lt_of_le (by omega : 0 < k) hkz
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hden : 0 < 4 * Real.sqrt (dz * dx) + Real.sqrt dx := by positivity
  have hscale : 0 < scale := by dsimp [scale]; positivity
  let GridInt := {z : ℤ // z ∈ Finset.Icc 0 ⌈2 * L / scale⌉}
  let Grid := NetSummaryCoord dx dz → GridInt
  let lower : Grid → SummarySpace dx dz := fun g =>
    { M0 := fun i j => -L + scale * (g (.M0 i j) : ℤ)
      M1 := fun i j => -L + scale * (g (.M1 i j) : ℤ)
      N0 := fun i j => -L + scale * (g (.N0 i j) : ℤ)
      N1 := fun i j => -L + scale * (g (.N1 i j) : ℤ)
      mX := fun j => -L + scale * (g (.mean j) : ℤ) }
  let GoodGrid := {g : Grid // ∃ q, q ∈ admissibleImage k dx dz L pi0 sigma0 ∧
    InSummaryBox L q ∧ InHalfOpenSummaryCube scale (lower g) q}
  let Key := {l : List ℝ // ∃ g : GoodGrid, summaryLexKey (lower g.1) = l}
  let keyOf : GoodGrid → Key := fun g =>
    ⟨summaryLexKey (lower g.1), g, rfl⟩
  letI : Finite GridInt := Set.finite_mem_finset (Finset.Icc 0 ⌈2 * L / scale⌉)
  letI : Finite Grid := Pi.finite
  letI : Finite GoodGrid := inferInstance
  letI : Finite Key := Finite.of_surjective keyOf (by
    rintro ⟨l, g, hg⟩
    refine ⟨g, Subtype.ext ?_⟩
    exact hg)
  letI : Fintype Key := Fintype.ofFinite Key
  let e : Fin (Fintype.card Key) ≃o Key := Fintype.orderIsoFinOfCardEq Key rfl
  let gridOf (i : Fin (Fintype.card Key)) : GoodGrid := Classical.choose (e i).property
  have gridOf_key (i : Fin (Fintype.card Key)) :
      summaryLexKey (lower (gridOf i).1) = (e i).1 :=
    Classical.choose_spec (e i).property
  let representative (i : Fin (Fintype.card Key)) : SummarySpace dx dz :=
    Classical.choose (gridOf i).property
  have representative_spec (i : Fin (Fintype.card Key)) :
      representative i ∈ admissibleImage k dx dz L pi0 sigma0 ∧
      InSummaryBox L (representative i) ∧
      InHalfOpenSummaryCube scale (lower (gridOf i).1) (representative i) :=
    Classical.choose_spec (gridOf i).property
  have image_box : ∀ q, q ∈ admissibleImage k dx dz L pi0 sigma0 → InSummaryBox L q := by
    intro q hq
    have hb := admissibleImage_subset_summarySpaceBox k dx dz L pi0 sigma0
      hk hkx hkz hL hpi hpiMax hsigma hsigmaMax hq
    change q.toCoordinates ∈ summaryCoordinateBox dx dz L at hb
    simpa [InSummaryBox, SummarySpace.toCoordinates, summaryCoordinateBox,
      summaryMatrixBox, summaryVectorBox] using hb
  have grid_for (q : SummarySpace dx dz) (hq : InSummaryBox L q) :
      ∃ g : Grid, InHalfOpenSummaryCube scale (lower g) q := by
    let z : NetSummaryCoord dx dz → ℤ := fun c =>
      ⌊(netSummaryCoord q c + L) / scale⌋
    have zmem (c : NetSummaryCoord dx dz) : z c ∈ Finset.Icc 0 ⌈2 * L / scale⌉ := by
      have hc : netSummaryCoord q c ∈ Set.Icc (-L) L := by
        rcases hq with ⟨h0, h1, h2, h3, h4⟩
        cases c with
        | M0 i j => exact h0 i j
        | M1 i j => exact h1 i j
        | N0 i j => exact h2 i j
        | N1 i j => exact h3 i j
        | mean j => exact h4 j
      have hy0 : 0 ≤ (netSummaryCoord q c + L) / scale :=
        div_nonneg (by linarith [hc.1]) hscale.le
      have hyL : (netSummaryCoord q c + L) / scale ≤ 2 * L / scale := by
        exact div_le_div_of_nonneg_right (by linarith [hc.2]) hscale.le
      have hz0 : (0 : ℤ) ≤ z c := Int.floor_nonneg.mpr hy0
      have hzleR : ((z c : ℤ) : ℝ) ≤ (⌈2 * L / scale⌉ : ℤ) :=
        (Int.floor_le _).trans (hyL.trans (Int.le_ceil _))
      exact Finset.mem_Icc.mpr ⟨hz0, by exact_mod_cast hzleR⟩
    let g : Grid := fun c => ⟨z c, zmem c⟩
    refine ⟨g, ?_⟩
    have scalar (x : ℝ) :
        -L + scale * (⌊(x + L) / scale⌋ : ℤ) ≤ x ∧
          x < -L + scale * (⌊(x + L) / scale⌋ : ℤ) + scale := by
      have hlo := Int.floor_le ((x + L) / scale)
      have hhi := Int.lt_floor_add_one ((x + L) / scale)
      have hlo' := mul_le_mul_of_nonneg_left hlo hscale.le
      have hhi' := mul_lt_mul_of_pos_left hhi hscale
      have hcancel : scale * ((x + L) / scale) = x + L := by field_simp
      rw [hcancel] at hlo' hhi'
      constructor <;> linarith
    have cell (c : NetSummaryCoord dx dz) :
        netSummaryCoord (lower g) c ≤ netSummaryCoord q c ∧
          netSummaryCoord q c < netSummaryCoord (lower g) c + scale := by
      cases c with
      | M0 i j => simpa [netSummaryCoord, lower, g, z] using scalar (q.M0 i j)
      | M1 i j => simpa [netSummaryCoord, lower, g, z] using scalar (q.M1 i j)
      | N0 i j => simpa [netSummaryCoord, lower, g, z] using scalar (q.N0 i j)
      | N1 i j => simpa [netSummaryCoord, lower, g, z] using scalar (q.N1 i j)
      | mean j => simpa [netSummaryCoord, lower, g, z] using scalar (q.mX j)
    exact ⟨fun i j => cell (.M0 i j), fun i j => cell (.M1 i j),
      fun i j => cell (.N0 i j), fun i j => cell (.N1 i j),
      fun j => cell (.mean j)⟩
  have same_grid {g h : Grid} {q : SummarySpace dx dz}
      (hg : InHalfOpenSummaryCube scale (lower g) q)
      (hh : InHalfOpenSummaryCube scale (lower h) q) : g = h := by
    funext c
    apply Subtype.ext
    have cell {lo s : SummarySpace dx dz}
        (hs : InHalfOpenSummaryCube scale lo s) (c : NetSummaryCoord dx dz) :
        netSummaryCoord lo c ≤ netSummaryCoord s c ∧
          netSummaryCoord s c < netSummaryCoord lo c + scale := by
      rcases hs with ⟨h0, h1, h2, h3, h4⟩
      cases c with
      | M0 i j => exact h0 i j
      | M1 i j => exact h1 i j
      | N0 i j => exact h2 i j
      | N1 i j => exact h3 i j
      | mean j => exact h4 j
    have gc₁ := (cell hg c).1
    have gc₂ := (cell hg c).2
    have hc₁ := (cell hh c).1
    have hc₂ := (cell hh c).2
    have lower_apply (a : Grid) :
        netSummaryCoord (lower a) c = -L + scale * (a c : ℤ) := by
      cases c <;> rfl
    rw [lower_apply] at gc₁ gc₂ hc₁ hc₂
    have hlt₁ : ((g c : GridInt) : ℤ) < (h c : GridInt) + 1 := by
      have : ((g c : ℤ) : ℝ) < (h c : ℤ) + 1 := by
        change ((g c : ℤ) : ℝ) < ((h c : ℤ) : ℝ) + 1
        change -L + scale * (g c : ℤ) ≤ netSummaryCoord q c at gc₁
        change netSummaryCoord q c < -L + scale * (h c : ℤ) + scale at hc₂
        nlinarith
      exact_mod_cast this
    have hlt₂ : ((h c : GridInt) : ℤ) < (g c : GridInt) + 1 := by
      have : ((h c : ℤ) : ℝ) < (g c : ℤ) + 1 := by
        change ((h c : ℤ) : ℝ) < ((g c : ℤ) : ℝ) + 1
        change -L + scale * (h c : ℤ) ≤ netSummaryCoord q c at hc₁
        change netSummaryCoord q c < -L + scale * (g c : ℤ) + scale at gc₂
        nlinarith
      exact_mod_cast this
    omega
  have cube_bound {g : Grid} {q r : SummarySpace dx dz}
      (hq : InHalfOpenSummaryCube scale (lower g) q)
      (hr : InHalfOpenSummaryCube scale (lower g) r) :
      dS q r ≤ (Real.sqrt n)⁻¹ := by
    have coord (c : NetSummaryCoord dx dz) :
        |netSummaryCoord q c - netSummaryCoord r c| ≤ scale := by
      have cell {lo s : SummarySpace dx dz}
          (hs : InHalfOpenSummaryCube scale lo s) (c : NetSummaryCoord dx dz) :
          netSummaryCoord lo c ≤ netSummaryCoord s c ∧
            netSummaryCoord s c < netSummaryCoord lo c + scale := by
        rcases hs with ⟨h0, h1, h2, h3, h4⟩
        cases c with
        | M0 i j => exact h0 i j
        | M1 i j => exact h1 i j
        | N0 i j => exact h2 i j
        | N1 i j => exact h3 i j
        | mean j => exact h4 j
      have qc := cell hq c
      have rc := cell hr c
      rw [abs_le]
      constructor <;> linarith
    have block (A B : RectMatrix dz dx)
        (hAB : ∀ i j, |A i j - B i j| ≤ scale) :
        ‖matrixCLM (A - B)‖ ≤ Real.sqrt (dz * dx) * scale := by
      apply matrixCLM_norm_le_sqrt_card_mul_of_entry_abs_le hscale.le
      simpa using hAB
    have hv : Real.sqrt (∑ i, (q.mX i - r.mX i) ^ 2) ≤ Real.sqrt dx * scale := by
      have hs : ∑ i, (q.mX i - r.mX i) ^ 2 ≤ (dx : ℝ) * scale ^ 2 := by
        calc
          _ ≤ ∑ _i : Fin dx, scale ^ 2 := Finset.sum_le_sum fun i _ => by
            have hi := (sq_le_sq₀ (abs_nonneg _) hscale.le).2 (coord (.mean i))
            simpa only [netSummaryCoord, sq_abs] using hi
          _ = (dx : ℝ) * scale ^ 2 := by simp
      calc
        _ ≤ Real.sqrt ((dx : ℝ) * scale ^ 2) := Real.sqrt_le_sqrt hs
        _ = Real.sqrt dx * scale := by rw [Real.sqrt_mul (Nat.cast_nonneg dx), Real.sqrt_sq hscale.le]
    unfold dS
    have h0 := block q.M0 r.M0 (fun i j => coord (.M0 i j))
    have h1 := block q.M1 r.M1 (fun i j => coord (.M1 i j))
    have h2 := block q.N0 r.N0 (fun i j => coord (.N0 i j))
    have h3 := block q.N1 r.N1 (fun i j => coord (.N1 i j))
    have hscale_eq : (4 * Real.sqrt (dz * dx) + Real.sqrt dx) * scale =
        (Real.sqrt n)⁻¹ := by
      dsimp [scale]
      field_simp
    nlinarith
  refine ⟨{
    index := Fin (Fintype.card Key)
    finiteIndex := inferInstance
    summary := representative
    representative_feasible := fun i => (representative_spec i).1
    scale := scale
    scale_eq := rfl
    covers := ?_
    cube := fun i => {s | InSummaryBox L s ∧
      InHalfOpenSummaryCube scale (lower (gridOf i).1) s}
    cubeLower := fun i => lower (gridOf i).1
    cubeLower_on_grid := ?_
    cube_eq_halfOpen := fun _ => rfl
    representative_in_cube := fun i =>
      ⟨(representative_spec i).2.1, (representative_spec i).2.2⟩
    cubes_disjoint := ?_
    meeting_cube_complete := ?_
    cube_diameter := ?_
    lexRank := fun i => i
    lexRank_injective := Fin.val_injective
    lexRank_order := ?_
    k_pos := by omega
    radius_nonneg := by unfold effectRadius; positivity
    index_nonempty_iff := ?_ }⟩
  · intro q hq
    obtain ⟨g, hg⟩ := grid_for q (image_box q hq)
    let gg : GoodGrid := ⟨g, q, hq, image_box q hq, hg⟩
    let key : Key := keyOf gg
    let i := e.symm key
    refine ⟨i, ?_⟩
    refine cube_bound ?_ hg
    have hchosen := (representative_spec i).2.2
    have hlower : lower (gridOf i).1 = lower g := by
      apply summaryLexKey_injective
      rw [gridOf_key i]
      simp [i, key, keyOf, gg]
    have hchosen' : InHalfOpenSummaryCube scale (lower g) (representative i) := by
      rw [← hlower]
      exact hchosen
    exact hchosen'
  · intro i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; exact ⟨(gridOf i).1 (.M0 a b), rfl⟩
    · intro a b; exact ⟨(gridOf i).1 (.M1 a b), rfl⟩
    · intro a b; exact ⟨(gridOf i).1 (.N0 a b), rfl⟩
    · intro a b; exact ⟨(gridOf i).1 (.N1 a b), rfl⟩
    · intro a; exact ⟨(gridOf i).1 (.mean a), rfl⟩
  · rw [Set.pairwiseDisjoint_iff]
    intro i _ j _ hij
    rcases hij with ⟨q, hqi, hqj⟩
    apply e.injective
    apply Subtype.ext
    rw [← gridOf_key i, ← gridOf_key j]
    exact congrArg summaryLexKey (congrArg lower (same_grid hqi.2 hqj.2))
  · intro q hq
    obtain ⟨g, hg⟩ := grid_for q (image_box q hq)
    let gg : GoodGrid := ⟨g, q, hq, image_box q hq, hg⟩
    let key : Key := keyOf gg
    let i := e.symm key
    refine ⟨i, image_box q hq, ?_⟩
    have hlower : lower (gridOf i).1 = lower g := by
      apply summaryLexKey_injective
      rw [gridOf_key i]
      simp [i, key, keyOf, gg]
    simpa [hlower] using hg
  · intro i q hq
    exact cube_bound hq.2 (representative_spec i).2.2
  · intro i j
    change i ≤ j ↔ SummaryLexLE (lower (gridOf i).1) (lower (gridOf j).1)
    rw [← e.le_iff_le]
    change (e i).1 ≤ (e j).1 ↔ _
    rw [← gridOf_key i, ← gridOf_key j]
    exact le_iff_eq_or_lt
  · rw [← Set.nonempty_iff_ne_empty]
    constructor
    · rintro ⟨i⟩
      exact ⟨representative i, (representative_spec i).1⟩
    · rintro ⟨q, hq⟩
      obtain ⟨g, hg⟩ := grid_for q (image_box q hq)
      let gg : GoodGrid := ⟨g, q, hq, image_box q hq, hg⟩
      let key : Key := keyOf gg
      exact ⟨e.symm key⟩

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
