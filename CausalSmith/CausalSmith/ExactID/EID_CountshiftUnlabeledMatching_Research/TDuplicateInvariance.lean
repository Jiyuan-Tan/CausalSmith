module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TCompatibilityCompletion

/-! Projective duplicate shifts and representative scaling. -/

@[expose] public section

open Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Append a projective duplicate; restricting to `Fin M` removes it. -/
def duplicateShift {p M : ℕ} (d : Fin M → Fin p → ℝ)
    (source : Fin M) (b : ℝ) : Fin (M + 1) → Fin p → ℝ :=
  Fin.snoc d (b • d source)

-- @node: support_smul_nonzero
lemma support_smul_nonzero {p q : ℕ} (v w : Fin q → Fin p → ℝ)
    (c : Fin q → ℝ) (hc : ∀ g, c g ≠ 0)
    (hw : ∀ g, w g = c g • v g) (g : Fin q) :
    support v g = support w g := by
  classical
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hw g]
  simp [Pi.smul_apply, smul_eq_mul, hc g]

-- @node: assignmentFiber_smul_nonzero
lemma assignmentFiber_smul_nonzero {p q : ℕ} (v w : Fin q → Fin p → ℝ)
    (c : Fin q → ℝ) (hc : ∀ g, c g ≠ 0)
    (hw : ∀ g, w g = c g • v g) :
    assignmentFiber v = assignmentFiber w := by
  have hs : ∀ g, support v g = support w g :=
    support_smul_nonzero v w c hc hw
  have hH (f : Fin q ↪ Fin p) : Hf v f = Hf w f := by
    funext i j
    simp only [Hf]
    simp_rw [hs]
  ext f
  simp only [assignmentFiber, Set.mem_ofPred_eq]
  simp_rw [hs, hH]

-- @node: targetSet_smul_nonzero
lemma targetSet_smul_nonzero {p q : ℕ} (v w : Fin q → Fin p → ℝ)
    (c : Fin q → ℝ) (hc : ∀ g, c g ≠ 0)
    (hw : ∀ g, w g = c g • v g) (g : Fin q) :
    targetSet v g = targetSet w g := by
  rw [targetSet, targetSet, assignmentFiber_smul_nonzero v w c hc hw]

-- @node: completionFiber_smul_nonzero
lemma completionFiber_smul_nonzero {p q : ℕ} (v w : Fin q → Fin p → ℝ)
    (c : Fin q → ℝ) (hc : ∀ g, c g ≠ 0)
    (hw : ∀ g, w g = c g • v g) :
    completionFiber v = completionFiber w := by
  have ha := assignmentFiber_smul_nonzero v w c hc hw
  have hratio (g : Fin q) (i j : Fin p) :
      v g i / v g j = w g i / w g j := by
    simpa only [hw g, Pi.smul_apply, smul_eq_mul] using
      (mul_div_mul_left (v g i) (v g j) (hc g)).symm
  have hAt (f : Fin q ↪ Fin p) :
      completionFiberAt v f = completionFiberAt w f := by
    ext B
    constructor
    · rintro ⟨hcol, hdiag, hcyc⟩
      exact ⟨by intro g i; rw [← hratio]; exact hcol g i, hdiag, hcyc⟩
    · rintro ⟨hcol, hdiag, hcyc⟩
      exact ⟨by intro g i; rw [hratio]; exact hcol g i, hdiag, hcyc⟩
  simp only [completionFiber, ha, hAt]

-- @node: coefficientFiber_smul_nonzero
lemma coefficientFiber_smul_nonzero {p q : ℕ} (v w : Fin q → Fin p → ℝ)
    (c : Fin q → ℝ) (hc : ∀ g, c g ≠ 0)
    (hw : ∀ g, w g = c g • v g) :
    coefficientFiber v = coefficientFiber w := by
  rw [coefficientFiber, coefficientFiber,
    completionFiber_smul_nonzero v w c hc hw]

-- @node: prop:duplicate-invariance
theorem duplicate_invariance {p M q : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (hB : IsUnit B.det)
    (η : Fin (M + 1) → Fin p → ℝ) (α : Fin M → ℝ)
    (t : Fin M → Fin p)
    (hA : AtomicMeanShift η α t)
    (hα : NonvanishingStrength α)
    (d : Fin M → Fin p → ℝ)
    (hd : ∀ m, d m = B *ᵥ (fun i => η m.succ i - η 0 i))
    (v w : Fin q → Fin p → ℝ)
    (c : Fin q → ℝ) (hc : ∀ g, c g ≠ 0)
    (hw : ∀ g, w g = c g • v g) :
    (∀ m m', ProjSim d m m' ↔ t m = t m') ∧
    (∀ r : ProjectiveReduction d,
      ∀ m m' i, r.κ m = r.κ m' → d m' i ≠ 0 →
        r.c m / r.c m' = d m i / d m' i) ∧
    assignmentFiber v = assignmentFiber w ∧
    (∀ g, targetSet v g = targetSet w g) ∧
    completionFiber v = completionFiber w ∧
    coefficientFiber v = coefficientFiber w ∧
    (∀ (source : Fin M) (b : ℝ), b ≠ 0 →
      let dPlus := duplicateShift d source b
      (∀ m : Fin M, dPlus m.castSucc = d m) ∧
      dPlus (Fin.last M) = b • d source ∧
      (∀ m : Fin M,
        ProjSim dPlus m.castSucc (Fin.last M) ↔ t m = t source) ∧
      ∀ (r : ProjectiveReduction d) (rPlus : ProjectiveReduction dPlus),
        ∃ e : Fin r.q ≃ Fin rPlus.q,
          ∃ scale : Fin r.q → ℝ,
            (∀ g, scale g ≠ 0) ∧
            (∀ g, rPlus.v (e g) = scale g • r.v g) ∧
            rPlus.κ (Fin.last M) = e (r.κ source) ∧
            rPlus.c (Fin.last M) / rPlus.c source.castSucc = b ∧
            (∀ m m' i, rPlus.κ m = rPlus.κ m' → dPlus m' i ≠ 0 →
              rPlus.c m / rPlus.c m' = dPlus m i / dPlus m' i) ∧
            assignmentFiber r.v =
              assignmentFiber (fun g => rPlus.v (e g)) ∧
            (∀ g, targetSet r.v g =
              targetSet (fun h => rPlus.v (e h)) g) ∧
            completionFiber r.v =
              completionFiber (fun g => rPlus.v (e g)) ∧
            coefficientFiber r.v =
              coefficientFiber (fun g => rPlus.v (e g))) := by
  classical
  have hBunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det (A := B)).2 hB
  have hshift (m : Fin M) :
      d m = B *ᵥ (α m • Pi.single (t m) 1) := by
    rw [hd m, hA m]
  have hproj : ∀ m m', ProjSim d m m' ↔ t m = t m' := by
    intro m m'
    constructor
    · rintro ⟨b, hb, hsim⟩
      have heq : α m • Pi.single (t m) (1 : ℝ) =
          b • (α m' • Pi.single (t m') (1 : ℝ)) := by
        apply Matrix.mulVec_injective_of_isUnit hBunit
        simpa only [Matrix.mulVec_smul, hshift] using hsim
      by_contra hne
      have hi := congrFun heq (t m)
      simp [hne] at hi
      exact hα m hi
    · intro htarget
      refine ⟨α m / α m', div_ne_zero (hα m) (hα m'), ?_⟩
      rw [hshift m, hshift m', htarget]
      rw [← Matrix.mulVec_smul, smul_smul]
      congr 1
      rw [div_mul_cancel₀ (α m) (hα m')]
  have hratio : ∀ r : ProjectiveReduction d,
      ∀ m m' i, r.κ m = r.κ m' → d m' i ≠ 0 →
        r.c m / r.c m' = d m i / d m' i := by
    intro r m m' i hκ hden
    have hm := congrFun (r.decomp m) i
    have hm' := congrFun (r.decomp m') i
    have hv : r.v (r.κ m') i ≠ 0 := by
      intro hz
      apply hden
      simp [hm', Pi.smul_apply, hz]
    rw [hκ] at hm
    rw [hm, hm']
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (mul_div_mul_right (r.c m) (r.c m') hv).symm
  refine ⟨hproj, hratio,
    assignmentFiber_smul_nonzero v w c hc hw,
    targetSet_smul_nonzero v w c hc hw,
    completionFiber_smul_nonzero v w c hc hw,
    coefficientFiber_smul_nonzero v w c hc hw, ?_⟩
  intro source b hb
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    simp [duplicateShift]
  · simp [duplicateShift]
  · intro m
    constructor
    · rintro ⟨a, ha, hsim⟩
      apply (hproj m source).mp
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      simpa [duplicateShift, smul_smul] using hsim
    · intro ht
      obtain ⟨a, ha, hsim⟩ := (hproj m source).mpr ht
      refine ⟨a / b, div_ne_zero ha hb, ?_⟩
      simp only [duplicateShift, Fin.snoc_castSucc, Fin.snoc_last]
      rw [smul_smul, div_mul_cancel₀ a hb]
      exact hsim
  · intro r rPlus
    have hclass (m n : Fin M) :
        rPlus.κ m.castSucc = rPlus.κ n.castSucc ↔ r.κ m = r.κ n := by
      rw [rPlus.classes, r.classes]
      simp only [ProjSim, duplicateShift, Fin.snoc_castSucc]
    have hlast : rPlus.κ (Fin.last M) = rPlus.κ source.castSucc := by
      rw [rPlus.classes]
      exact ⟨b, hb, by simp [duplicateShift]⟩
    let rep (g : Fin r.q) : Fin M := Classical.choose (r.κ_surj g)
    have hrep (g : Fin r.q) : r.κ (rep g) = g :=
      Classical.choose_spec (r.κ_surj g)
    let eFun (g : Fin r.q) : Fin rPlus.q := rPlus.κ (rep g).castSucc
    have heval (m : Fin M) : eFun (r.κ m) = rPlus.κ m.castSucc := by
      apply (hclass (rep (r.κ m)) m).2
      exact (hrep _).trans rfl
    have hein : Function.Injective eFun := by
      intro g h hgh
      have heq := (hclass (rep g) (rep h)).1 hgh
      simpa only [hrep] using heq
    have hesurj : Function.Surjective eFun := by
      intro h
      obtain ⟨x, hx⟩ := rPlus.κ_surj h
      induction x using Fin.lastCases with
      | last =>
          exact ⟨r.κ source, by rw [heval, ← hlast, hx]⟩
      | cast m =>
          exact ⟨r.κ m, by rw [heval, hx]⟩
    let e : Fin r.q ≃ Fin rPlus.q := Equiv.ofBijective eFun ⟨hein, hesurj⟩
    let scale (g : Fin r.q) : ℝ := r.c (rep g) / rPlus.c (rep g).castSucc
    have hscale (g : Fin r.q) : scale g ≠ 0 :=
      div_ne_zero (r.c_ne _) (rPlus.c_ne _)
    have hdir (g : Fin r.q) : rPlus.v (e g) = scale g • r.v g := by
      have hdecomp := r.decomp (rep g)
      have hdecompPlus := rPlus.decomp (rep g).castSucc
      simp only [duplicateShift, Fin.snoc_castSucc] at hdecompPlus
      change d (rep g) = rPlus.c (rep g).castSucc • rPlus.v (e g) at hdecompPlus
      rw [hrep] at hdecomp
      rw [hdecomp] at hdecompPlus
      apply (smul_right_injective (Fin p → ℝ) (rPlus.c_ne (rep g).castSucc))
      calc
        rPlus.c (rep g).castSucc • rPlus.v (e g) =
            r.c (rep g) • r.v g := hdecompPlus.symm
        _ = rPlus.c (rep g).castSucc • (scale g • r.v g) := by
          rw [smul_smul]
          congr 1
          dsimp [scale]
          field_simp [rPlus.c_ne (rep g).castSucc]
    have hratioPlus : ∀ m m' i,
        rPlus.κ m = rPlus.κ m' → duplicateShift d source b m' i ≠ 0 →
          rPlus.c m / rPlus.c m' =
            duplicateShift d source b m i / duplicateShift d source b m' i := by
      intro m m' i hκ hden
      have hm := congrFun (rPlus.decomp m) i
      have hm' := congrFun (rPlus.decomp m') i
      have hv : rPlus.v (rPlus.κ m') i ≠ 0 := by
        intro hz
        apply hden
        simp [hm', Pi.smul_apply, hz]
      rw [hκ] at hm
      rw [hm, hm']
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (mul_div_mul_right (rPlus.c m) (rPlus.c m') hv).symm
    refine ⟨e, scale, hscale, hdir, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change rPlus.κ (Fin.last M) = eFun (r.κ source)
      exact hlast.trans (heval source).symm
    · have hv : ∃ i, rPlus.v (rPlus.κ source.castSucc) i ≠ 0 := by
        by_contra h
        apply rPlus.v_ne (rPlus.κ source.castSucc)
        funext i
        exact not_not.mp (not_exists.mp h i)
      obtain ⟨i, hi⟩ := hv
      have hden : duplicateShift d source b source.castSucc i ≠ 0 := by
        have hs := congrFun (rPlus.decomp source.castSucc) i
        rw [hs]
        exact mul_ne_zero (rPlus.c_ne _) hi
      have h := hratioPlus (Fin.last M) source.castSucc i hlast hden
      have hdne : d source i ≠ 0 := by simpa [duplicateShift] using hden
      calc
        rPlus.c (Fin.last M) / rPlus.c source.castSucc =
            b * d source i / d source i := by
          simpa only [duplicateShift, Fin.snoc_castSucc, Fin.snoc_last,
            Pi.smul_apply, smul_eq_mul] using h
        _ = b := by field_simp [hdne]
    · exact hratioPlus
    · exact assignmentFiber_smul_nonzero _ _ scale hscale hdir
    · intro g
      exact targetSet_smul_nonzero _ _ scale hscale hdir g
    · exact completionFiber_smul_nonzero _ _ scale hscale hdir
    · exact coefficientFiber_smul_nonzero _ _ scale hscale hdir

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
