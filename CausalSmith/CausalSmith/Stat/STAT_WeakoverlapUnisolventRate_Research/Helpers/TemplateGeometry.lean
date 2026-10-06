module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.TemplateAlgebra

/-!
# Template spectral and microcube geometry

This file proves the spectral gap and Lipschitz control for the deterministic
tensor template and defines the contained template microcubes.
-/
@[expose] public section
set_option linter.style.haveILetI false
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

/-- Rayleigh-quotient least eigenvalue. For [the stated inputs and conditions](hyp:d,m), [the `templateLambda` object being defined](goal). -/
noncomputable def templateLambda (d m : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ b : MonoIndex d m → ℝ,
    finiteL2Norm b = 1 ∧ r = ∑ α, ∑ β, b α * templateGram d m α β * b β}
  -- @realizes lambda0(Rayleigh infimum)

/-- Compactness of the finite unit sphere makes strict Gram positivity uniform. [For the stated inputs and conditions](hyp:d,m), [the asserted conclusion holds](goal). -/
lemma templateLambda_pos (d m : ℕ) : 0 < templateLambda d m := by
  classical
  let q : (MonoIndex d m → ℝ) → ℝ := fun b =>
    ∑ α, ∑ β, b α * templateGram d m α β * b β
  let s2 : (MonoIndex d m → ℝ) → ℝ := fun b => ∑ α, b α ^ 2
  let S : Set (MonoIndex d m → ℝ) := {b | s2 b = 1}
  have hs2cont : Continuous s2 := by dsimp [s2]; fun_prop
  have hqcont : Continuous q := by dsimp [q]; fun_prop
  have hSclosed : IsClosed S := isClosed_eq hs2cont continuous_const
  have hSbounded : Bornology.IsBounded S := by
    apply (Metric.isBounded_iff_subset_closedBall 0).mpr
    refine ⟨1, ?_⟩
    intro b hb
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro α
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    have hα : b α ^ 2 ≤ 1 := by
      rw [← hb]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (b i)) (Finset.mem_univ α)
    exact hα
  have hScompact : IsCompact S :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hSclosed, hSbounded⟩
  let α₀ : MonoIndex d m := ⟨fun _ => 0, by simp [monoIdx]⟩
  let b₀ : MonoIndex d m → ℝ := Pi.single α₀ 1
  have hb₀ : b₀ ∈ S := by
    simp [S, s2, b₀, Pi.single_apply]
  obtain ⟨bmin, hbmin, hmin⟩ :=
    hScompact.exists_sInf_image_eq ⟨b₀, hb₀⟩ hqcont.continuousOn
  have hunit : finiteL2Norm bmin = 1 := by
    simp [finiteL2Norm, S, s2] at hbmin ⊢
    simp [hbmin]
  have hpos := templateGram_unit_pos d m bmin hunit
  have hset : {r : ℝ | ∃ b : MonoIndex d m → ℝ, finiteL2Norm b = 1 ∧ r = q b} =
      q '' S := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_image, S]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b, ?_, rfl⟩
      have hs : 0 ≤ s2 b := Finset.sum_nonneg (fun i _ => sq_nonneg (b i))
      have := congrArg (fun x : ℝ => x ^ 2) hb
      change (Real.sqrt (s2 b)) ^ 2 = 1 ^ 2 at this
      rwa [Real.sq_sqrt hs, one_pow] at this
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b, ?_, rfl⟩
      simpa [finiteL2Norm, s2, hb]
  change 0 < sInf {r : ℝ | ∃ b : MonoIndex d m → ℝ,
    finiteL2Norm b = 1 ∧ r = q b}
  rw [hset, hmin]
  exact hpos

/-- The template Rayleigh infimum bounds every unit-vector quadratic form. [For the stated inputs and conditions](hyp:d,m,b,hb), [the asserted conclusion holds](goal). -/
lemma templateLambda_le_quadratic_unit (d m : ℕ)
    (b : MonoIndex d m → ℝ) (hb : finiteL2Norm b = 1) :
    templateLambda d m ≤
      ∑ α, ∑ β, b α * templateGram d m α β * b β := by
  let S : Set ℝ := {r | ∃ v : MonoIndex d m → ℝ,
    finiteL2Norm v = 1 ∧
      r = ∑ α, ∑ β, v α * templateGram d m α β * v β}
  have hbelow : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro r ⟨v, -, rfl⟩
    exact templateGram_quadratic_nonneg d m v
  change sInf S ≤ _
  exact csInf_le hbelow ⟨b, hb, rfl⟩

/-- The least template Rayleigh quotient controls every coefficient vector. [For the stated inputs and conditions](hyp:d,m,b), [the asserted conclusion holds](goal). -/
lemma templateLambda_le_quadratic (d m : ℕ)
    (b : MonoIndex d m → ℝ) :
    templateLambda d m * finiteL2Norm b ^ 2 ≤
      ∑ α, ∑ β, b α * templateGram d m α β * b β := by
  classical
  by_cases hb : b = 0
  · subst b
    simp [finiteL2Norm]
  let r := finiteL2Norm b
  have hr : 0 < r := (finiteL2Norm_pos_iff b).2 hb
  let u : MonoIndex d m → ℝ := fun i => b i / r
  have hu : finiteL2Norm u = 1 := by
    have hsq : finiteL2Norm u ^ 2 = 1 := by
      rw [finiteL2Norm_sq]
      simp only [u, div_pow]
      rw [← Finset.sum_div, ← finiteL2Norm_sq]
      change r ^ 2 / r ^ 2 = 1
      exact div_self (pow_ne_zero 2 (ne_of_gt hr))
    nlinarith [show 0 ≤ finiteL2Norm u from Real.sqrt_nonneg _]
  have hunit := templateLambda_le_quadratic_unit d m u hu
  have hscale :
      (∑ α, ∑ β, u α * templateGram d m α β * u β) * r ^ 2 =
        ∑ α, ∑ β, b α * templateGram d m α β * b β := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro β _
    dsimp [u]
    field_simp
  have hm := mul_le_mul_of_nonneg_right hunit (sq_nonneg r)
  rw [hscale] at hm
  simpa [r] using hm

/-- Lipschitz quotient of the matrix-valued polynomial basis on the cube. For [the stated inputs and conditions](hyp:d,m), [the `templateLip` object being defined](goal). -/
noncomputable def templateLip (d m : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ z z' : Fin d → ℝ, z ∈ cube d ∧ z' ∈ cube d ∧ z ≠ z' ∧
    r = finiteL2OpNorm
      ((fun α β : MonoIndex d m => monoVec d m z α * monoVec d m z β) -
      (fun α β : MonoIndex d m => monoVec d m z' α * monoVec d m z' β)) /
      ‖z - z'‖} -- @realizes LU(basis Gram Lipschitz constant)

/-- The polynomial outer-product difference quotients on the compact cube are
bounded above. [For the stated inputs and conditions](hyp:d,m), [the asserted conclusion holds](goal). -/
lemma templateLip_bddAbove (d m : ℕ) :
    BddAbove {r : ℝ | ∃ z z' : Fin d → ℝ, z ∈ cube d ∧ z' ∈ cube d ∧ z ≠ z' ∧
      r = finiteL2OpNorm
        ((fun α β : MonoIndex d m => monoVec d m z α * monoVec d m z β) -
        (fun α β : MonoIndex d m => monoVec d m z' α * monoVec d m z' β)) /
        ‖z - z'‖} := by
  classical
  let i₀ : MonoIndex d m := ⟨fun _ => 0, by simp [monoIdx]⟩
  letI : Nonempty (MonoIndex d m) := ⟨i₀⟩
  let F : (Fin d → ℝ) → Matrix (MonoIndex d m) (MonoIndex d m) ℝ :=
    fun z α β => monoVec d m z α * monoVec d m z β
  let G : (Fin d → ℝ) → (MonoIndex d m × MonoIndex d m → ℝ) :=
    fun z p => F z p.1 p.2
  have hG : ContDiff ℝ 1 G := by
    dsimp [G, F, monoVec]
    rw [contDiff_pi]
    intro p
    apply ContDiff.mul
    · apply contDiff_prod
      intro i hi
      exact (contDiff_apply ℝ ℝ i).pow _
    · apply contDiff_prod
      intro i hi
      exact (contDiff_apply ℝ ℝ i).pow _
  let H : (Fin d → ℝ) → EuclideanSpace ℝ (MonoIndex d m × MonoIndex d m) :=
    fun z => (EuclideanSpace.equiv _ _).symm (G z)
  have hH : ContDiff ℝ 1 H := by
    exact (EuclideanSpace.equiv _ _).symm.contDiff.comp hG
  have hconv : Convex ℝ (cube d) := by
    rw [cube]
    exact convex_pi (fun _ _ => convex_Icc _ _)
  have hcompact : IsCompact (cube d) := by
    rw [cube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨K, hK⟩ := hH.contDiffOn.exists_lipschitzOnWith one_ne_zero hconv hcompact
  refine ⟨(K : ℝ), ?_⟩
  rintro r ⟨z, z', hz, hz', hne, rfl⟩
  have hop : finiteL2OpNorm (F z - F z') ≤ ‖F z - F z'‖ :=
    finiteL2OpNorm_le_matrixL2 (F z - F z')
  have hmatrix : ‖F z - F z'‖ ≤ ‖H z - H z'‖ := by
    calc
      ‖F z - F z'‖ ≤ @norm (Matrix (MonoIndex d m) (MonoIndex d m) ℝ)
          Matrix.frobeniusNormedAddCommGroup.toNorm (F z - F z') := by
        open scoped Matrix.Norms.Frobenius in
          refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (F z - F z')) fun x => ?_
          have hmul := Matrix.frobenius_norm_mul (F z - F z')
            (Matrix.replicateCol Unit (WithLp.ofLp x))
          have heq : (F z - F z') * Matrix.replicateCol Unit (WithLp.ofLp x) =
              Matrix.replicateCol Unit ((F z - F z').mulVec (WithLp.ofLp x)) := by
            ext i u
            simp [Matrix.mul_apply, Matrix.mulVec, Matrix.replicateCol, dotProduct]
          rw [heq, Matrix.frobenius_norm_replicateCol] at hmul
          rw [← Matrix.toEuclideanCLM_toLp (F z - F z') (WithLp.ofLp x),
            WithLp.toLp_ofLp] at hmul
          change ‖Matrix.toEuclideanCLM (n := MonoIndex d m) (𝕜 := ℝ)
            (F z - F z') x‖ ≤ ‖F z - F z'‖ * ‖x‖
          simpa using hmul
      _ = ‖H z - H z'‖ := by
        rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
        simp only [H, EuclideanSpace.norm_eq, Real.norm_eq_abs,
          Fintype.sum_prod_type, PiLp.continuousLinearEquiv_symm_apply,
          Real.rpow_two, sq_abs]
        congr 1
  have hdist : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  apply (div_le_div_of_nonneg_right (hop.trans hmatrix) hdist.le).trans
  rw [div_le_iff₀ hdist]
  exact hK.dist_le_mul z hz z' hz'

/-- `templateLip` bounds each nontrivial outer-product difference quotient on
the cube. [For the stated inputs and conditions](hyp:d,m,z,z',hz,hz',hne), [the asserted conclusion holds](goal). -/
lemma templateLip_bounds_quotient (d m : ℕ) (z z' : Fin d → ℝ)
    (hz : z ∈ cube d) (hz' : z' ∈ cube d) (hne : z ≠ z') :
    finiteL2OpNorm
        ((fun α β : MonoIndex d m => monoVec d m z α * monoVec d m z β) -
        (fun α β : MonoIndex d m => monoVec d m z' α * monoVec d m z' β)) /
        ‖z - z'‖ ≤ templateLip d m := by
  apply le_csSup (templateLip_bddAbove d m)
  exact ⟨z, z', hz, hz', hne, rfl⟩

/-- Every matrix difference quotient in the template Lipschitz radius is nonnegative. [For the stated inputs and conditions](hyp:d,m), [the asserted conclusion holds](goal). -/
lemma templateLip_nonneg (d m : ℕ) : 0 ≤ templateLip d m := by
  apply Real.sSup_nonneg
  rintro r ⟨z, z', -, -, hzz', rfl⟩
  exact div_nonneg (finiteL2OpNorm_nonneg _) (norm_nonneg _)

/-- Template microcell width. For [the stated inputs and conditions](hyp:d,m), [the `templateEta` object being defined](goal). -/
noncomputable def templateEta (d m : ℕ) : ℝ :=
  min ((1 : ℝ) / (2 * (m + 2)))
    (templateLambda d m / (1 + templateLip d m)) -- @realizes eta(template width)

/-- The fixed template cells have strictly positive width. [For the stated inputs and conditions](hyp:d,m), [the asserted conclusion holds](goal). -/
lemma templateEta_pos (d m : ℕ) : 0 < templateEta d m := by
  unfold templateEta
  apply lt_min
  · positivity
  · exact div_pos (templateLambda_pos d m)
      (by have := templateLip_nonneg d m; positivity)

/-- The chosen microcell radius fits inside half the template spectral gap. [For the stated inputs and conditions](hyp:d,m), [the asserted conclusion holds](goal). -/
lemma templateLip_eta_le_half_lambda (d m : ℕ) :
    templateLip d m * templateEta d m / 2 ≤ templateLambda d m / 2 := by
  have hLip : 0 ≤ templateLip d m := templateLip_nonneg d m
  have hEta : 0 ≤ templateEta d m := le_of_lt (templateEta_pos d m)
  have hden : 0 < 1 + templateLip d m := by linarith
  have hwidth : templateEta d m ≤
      templateLambda d m / (1 + templateLip d m) := by
    unfold templateEta
    exact min_le_right _ _
  have hprod : templateEta d m * (1 + templateLip d m) ≤
      templateLambda d m := (le_div_iff₀ hden).mp hwidth
  have hsmall : templateLip d m * templateEta d m ≤
      templateEta d m * (1 + templateLip d m) := by nlinarith
  linarith

/-- Closed microcube around a tensor node. For [the stated inputs and conditions](hyp:d,m,ℓ), [the `microCube` object being defined](goal). -/
noncomputable def microCube (d m : ℕ) (ℓ : Fin d → Fin (m + 1)) : Set (Fin d → ℝ) :=
  {z | ∀ i, |z i - tensorNode d m ℓ i| ≤ templateEta d m / 2}
  -- @realizes V_ell(reference microcube)

/-- Membership in a template microcube gives the norm bound used by Gram perturbation. [For the stated inputs and conditions](hyp:d,m,ℓ,z,hz), [the asserted conclusion holds](goal). -/
lemma microCube_norm_sub_tensorNode_le (d m : ℕ)
    (ℓ : Fin d → Fin (m + 1)) (z : Fin d → ℝ)
    (hz : z ∈ microCube d m ℓ) :
    ‖z - tensorNode d m ℓ‖ ≤ templateEta d m / 2 := by
  apply (pi_norm_le_iff_of_nonneg
    (div_nonneg (le_of_lt (templateEta_pos d m)) (by norm_num))).2
  intro i
  simpa [Real.norm_eq_abs] using hz i

/-- Every tensor interpolation node lies in the unit cube. [For the stated inputs and conditions](hyp:d,m,ℓ), [the asserted conclusion holds](goal). -/
lemma tensorNode_mem_cube (d m : ℕ) (ℓ : Fin d → Fin (m + 1)) :
    tensorNode d m ℓ ∈ cube d := by
  intro i hi
  constructor
  · unfold tensorNode
    positivity
  · unfold tensorNode
    have hle : (ℓ i).val + 1 ≤ m + 1 := Nat.succ_le_succ (Fin.le_last (ℓ i))
    have hden : (0 : ℝ) < m + 2 := by positivity
    rw [div_le_one hden]
    exact_mod_cast hle.trans (Nat.le_succ (m + 1))

/-- Every template microcube is contained in the unit cube. [For the stated inputs and conditions](hyp:d,m,ℓ), [the asserted conclusion holds](goal). -/
lemma microCube_subset_cube (d m : ℕ) (ℓ : Fin d → Fin (m + 1)) :
    microCube d m ℓ ⊆ cube d := by
  intro z hz i hi
  have hwidth : templateEta d m ≤ (1 : ℝ) / (2 * (m + 2)) := by
    unfold templateEta
    exact min_le_left _ _
  have heta : templateEta d m / 2 ≤ 1 / (m + 2 : ℝ) := by
    have hm : (0 : ℝ) < m + 2 := by positivity
    calc
      templateEta d m / 2 ≤ (1 / (2 * (m + 2 : ℝ))) / 2 := by gcongr
      _ ≤ 1 / (m + 2 : ℝ) := by
        have hinv : 0 ≤ 1 / (m + 2 : ℝ) := by positivity
        have heq : (1 / (2 * (m + 2 : ℝ))) / 2 =
            (1 / (m + 2 : ℝ)) / 4 := by
          field_simp
          norm_num
        rw [heq]
        linarith
  have hzabs := hz i
  rw [abs_le] at hzabs
  constructor
  · have hnode : 1 / (m + 2 : ℝ) ≤ tensorNode d m ℓ i := by
      unfold tensorNode
      have hnum : (1 : ℝ) ≤ (ℓ i).val + 1 := by norm_num
      have hm : (0 : ℝ) < m + 2 := by positivity
      exact (div_le_div_iff_of_pos_right hm).2 hnum
    linarith
  · have hnode : tensorNode d m ℓ i ≤ (m + 1 : ℝ) / (m + 2 : ℝ) := by
      unfold tensorNode
      have hvalNat : (ℓ i).val ≤ m := by omega
      have hval : ((ℓ i).val : ℝ) ≤ m := by exact_mod_cast hvalNat
      gcongr
    have hm : (0 : ℝ) < m + 2 := by positivity
    have hgap : (m + 1 : ℝ) / (m + 2 : ℝ) + 1 / (m + 2 : ℝ) = 1 := by
      field_simp
      ring
    linarith

-- @node: def:template
/-- The fixed finite family of unisolvent template microcubes. For [the stated inputs and conditions](hyp:d,m), [the `EqualCellTemplate` object being defined](goal). -/
noncomputable def EqualCellTemplate (d m : ℕ) :
    (Fin d → Fin (m + 1)) → Set (Fin d → ℝ) :=
  microCube d m

end CausalSmith.Stat.WeakOverlap
