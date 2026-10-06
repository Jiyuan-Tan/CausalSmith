module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Parametric
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The label-gated parametric `1/n` minimax lower bound. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory

-- @node: parametricFloorNullLaw
/-- From [a valid null parametric data-generating process](hyp:hv), define [its finite discrete observation law](goal). -/
noncomputable def parametricFloorNullLaw {d : Nat} [Nonempty (Fin d)]
    {g : Real} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g)) : DiscreteLaw d :=
  ⟨Causalean.Estimation.MinimaxATE.obsPMF hv⟩

-- @node: parametricFloorPertLaw
/-- From [a valid perturbed parametric data-generating process](hyp:hv), define [its finite discrete observation law](goal). -/
noncomputable def parametricFloorPertLaw {d : Nat} [Nonempty (Fin d)]
    {g delta : Real} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) : DiscreteLaw d :=
  ⟨Causalean.Estimation.MinimaxATE.obsPMF hv⟩

-- @node: parametricFloorNullLaw_jointMass
/-- For [a valid null process](hyp:hv), [covariate cell](hyp:x), [treatment arm and outcome](hyp:a,y), [the induced joint mass equals the parametric observation mass](goal). -/
lemma parametricFloorNullLaw_jointMass {d : Nat} [Nonempty (Fin d)] {g : Real}
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g))
    (x : Fin d) (a y : Bool) :
    jointMass (parametricFloorNullLaw hv) x a y =
      Causalean.Estimation.MinimaxATE.obsReal
        (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
        (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g) (x, a, y) := by
  simp [jointMass, parametricFloorNullLaw, Causalean.Estimation.MinimaxATE.obsPMF]
  simpa [one_div] using Causalean.Estimation.MinimaxATE.obsReal_nonneg hv (x, a, y)

-- @node: parametricFloorPertLaw_jointMass
/-- For [a valid perturbed process](hyp:hv), [covariate cell](hyp:x), [treatment arm and outcome](hyp:a,y), [the induced joint mass equals the perturbed parametric observation mass](goal). -/
lemma parametricFloorPertLaw_jointMass {d : Nat} [Nonempty (Fin d)] {g delta : Real}
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta))
    (x : Fin d) (a y : Bool) :
    jointMass (parametricFloorPertLaw hv) x a y =
      Causalean.Estimation.MinimaxATE.obsReal
        (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
        (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta) (x, a, y) := by
  simp [jointMass, parametricFloorPertLaw, Causalean.Estimation.MinimaxATE.obsPMF]
  simpa [one_div] using Causalean.Estimation.MinimaxATE.obsReal_nonneg hv (x, a, y)

-- @node: parametricFloorNullLaw_model
/-- If [the dimension is at least two](hyp:hd), [overlap is positive](hyp:heps) and [below one half](hyp:heps2), then [a valid null process](hyp:hv) [induces a law in the overlap model class](goal). -/
lemma parametricFloorNullLaw_model {d : Nat} [Nonempty (Fin d)] {eps g : Real}
    (hd : 2 ≤ d) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g)) :
    ModelClass d eps (parametricFloorNullLaw hv) := by
  refine ⟨hd, heps, heps2, ?_⟩
  intro x hx
  have hc : (Fintype.card (Fin d) : Real) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : propensity (parametricFloorNullLaw hv) x = 1 / 2 := by
    simp [propensity, cellMass, armMass, parametricFloorNullLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gNull]
    field_simp [hc]
    ring
  rw [hp]
  constructor <;> linarith

-- @node: parametricFloorPertLaw_model
/-- If [the dimension is at least two](hyp:hd), [overlap is positive](hyp:heps) and [below one half](hyp:heps2), then [a valid perturbed process](hyp:hv) [induces a law in the overlap model class](goal). -/
lemma parametricFloorPertLaw_model {d : Nat} [Nonempty (Fin d)] {eps g delta : Real}
    (hd : 2 ≤ d) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) :
    ModelClass d eps (parametricFloorPertLaw hv) := by
  refine ⟨hd, heps, heps2, ?_⟩
  intro x hx
  have hc : (Fintype.card (Fin d) : Real) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : propensity (parametricFloorPertLaw hv) x = 1 / 2 := by
    simp [propensity, cellMass, armMass, parametricFloorPertLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gPert]
    field_simp [hc]
    ring
  rw [hp]
  constructor <;> linarith

-- @node: parametricFloorNullLaw_ate
/-- For [a valid null process](hyp:hv), [the induced average treatment effect is zero](goal). -/
lemma parametricFloorNullLaw_ate {d : Nat} [Nonempty (Fin d)] {g : Real}
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g)) :
    ateFunctional (parametricFloorNullLaw hv) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hc : (Fintype.card (Fin d) : Real) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : (d : Real) ≠ 0 := by simpa using hc
  have hm (a : Bool) : outcomeMean (parametricFloorNullLaw hv) a x = g := by
    cases a <;> simp [outcomeMean, armMass, parametricFloorNullLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gNull] <;> field_simp [hc, hd] <;> ring
  simp [ateFunctional, hm]

-- @node: parametricFloorPertLaw_ate
/-- For [a valid perturbed process](hyp:hv), [the induced average treatment effect equals the perturbation](goal). -/
lemma parametricFloorPertLaw_ate {d : Nat} [Nonempty (Fin d)] {g delta : Real}
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) :
    ateFunctional (parametricFloorPertLaw hv) = delta := by
  have hc : (Fintype.card (Fin d) : Real) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : (d : Real) ≠ 0 := by simpa using hc
  have hm (a : Bool) (x : Fin d) :
      outcomeMean (parametricFloorPertLaw hv) a x = if a then g + delta else g := by
    cases a <;> simp [outcomeMean, armMass, parametricFloorPertLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gPert] <;> field_simp [hc, hd] <;> ring
  simp_rw [ateFunctional, hm true, hm false]
  simp [cellMass, parametricFloorPertLaw_jointMass,
    Causalean.Estimation.MinimaxATE.obsReal,
    Causalean.Estimation.MinimaxATE.Parametric.mC,
    Causalean.Estimation.MinimaxATE.Parametric.gPert]
  field_simp [hd]
  ring

-- @node: parametricFloor_auxMarginal_eq
/-- [A valid null process](hyp:hv0) and [its valid perturbation](hyp:hv1) [induce identical auxiliary-data marginals](goal). -/
lemma parametricFloor_auxMarginal_eq {d : Nat} [Nonempty (Fin d)] {g delta : Real}
    (hv0 : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g))
    (hv1 : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) :
    auxMarginal (parametricFloorNullLaw hv0) = auxMarginal (parametricFloorPertLaw hv1) := by
  classical
  apply PMF.ext
  rintro ⟨x, a⟩
  unfold auxMarginal
  rw [PMF.map_apply, PMF.map_apply]
  simp only [tsum_fintype, Fintype.sum_prod_type]
  cases a <;>
  simp [parametricFloorNullLaw, parametricFloorPertLaw,
    Causalean.Estimation.MinimaxATE.obsPMF, Causalean.Estimation.MinimaxATE.obsReal,
    Causalean.Estimation.MinimaxATE.Parametric.mC,
    Causalean.Estimation.MinimaxATE.Parametric.gNull,
    Causalean.Estimation.MinimaxATE.Parametric.gPert]
  obtain ⟨hg0, hg1⟩ := hv0.g_mem true x
  obtain ⟨hgd0, hgd1⟩ := hv1.g_mem true x
  have hg0' : 0 ≤ g := by
    simpa [Causalean.Estimation.MinimaxATE.Parametric.gNull] using hg0
  have hgd0' : 0 ≤ g + delta := by
    simpa [Causalean.Estimation.MinimaxATE.Parametric.gPert] using hgd0
  have hg1' : g ≤ 1 := by
    simpa [Causalean.Estimation.MinimaxATE.Parametric.gNull] using hg1
  have hgd1' : g + delta ≤ 1 := by
    simpa [Causalean.Estimation.MinimaxATE.Parametric.gPert] using hgd1
  rw [← mul_add, ← mul_add, ← ENNReal.ofReal_add hg0',
    show g + (1 - g) = 1 by ring, ← ENNReal.ofReal_add hgd0',
    show g + delta + (1 - (g + delta)) = 1 by ring] <;> linarith

-- @node: annotationMinimaxRisk_ge_two_model_tv
/-- [the stated conditions](hyp:hs,hsep,htv) establishes [the stated conclusion](goal). -/
lemma annotationMinimaxRisk_ge_two_model_tv {n m d : Nat} {eps s : Real}
    (P0 P1 : ClassLaw d eps) (hs : 0 ≤ s)
    (hsep : 2 * s ≤ |ateFunctional P0.1 - ateFunctional P1.1|)
    (htv : Causalean.Stat.tvDist (annotationLaw P0.1 n m) (annotationLaw P1.1 n m) ≤ 1 / 2) :
    s ^ 2 / 4 ≤ minimaxRisk n m d eps := by
  classical
  have hprob (P : DiscreteLaw d) : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  letI : IsProbabilityMeasure (annotationLaw P0.1 n m) := hprob P0.1
  letI : IsProbabilityMeasure (annotationLaw P1.1 n m) := hprob P1.1
  letI : Nonempty {f : Sample n m d → Real // Measurable f} := ⟨⟨fun _ => 0, measurable_const⟩⟩
  unfold minimaxRisk
  apply le_ciInf
  intro est
  have ht := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := annotationLaw P0.1 n m) (P₁ := annotationLaw P1.1 n m) est.2
    (θ₀ := ateFunctional P0.1) (θ₁ := ateFunctional P1.1)
    (s := s) (c := (1 / 2 : Real)) hsep htv
  have hp : 1 / 4 ≤ max
      ((annotationLaw P0.1 n m).real {z | s ≤ |est.1 z - ateFunctional P0.1|})
      ((annotationLaw P1.1 n m).real {z | s ≤ |est.1 z - ateFunctional P1.1|}) := by
    convert ht using 1 <;> norm_num
  have hrisk (P : ClassLaw d eps) :
      s ^ 2 * (annotationLaw P.1 n m).real {z | s ≤ |est.1 z - ateFunctional P.1|} ≤
        twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1) := by
    letI : IsProbabilityMeasure (annotationLaw P.1 n m) := hprob P.1
    unfold twoSampleMSE
    let f : Sample n m d → Real := fun z => (est.1 z - ateFunctional P.1) ^ 2
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := annotationLaw P.1 n m) (f := f) (ae_of_all _ fun z => sq_nonneg _)
      Integrable.of_finite (s ^ 2)
    have he : {z | s ≤ |est.1 z - ateFunctional P.1|} = {z | s ^ 2 ≤ f z} := by
      ext z
      simpa [f, abs_of_nonneg hs, sq_abs] using
        (sq_le_sq₀ hs (abs_nonneg (est.1 z - ateFunctional P.1))).symm
    rw [he]
    simpa using hmarkov
  have hb : BddAbove (Set.range (fun P : ClassLaw d eps =>
      twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1))) := by
    refine ⟨((∑ z : Sample n m d, |est.1 z|) + 1) ^ 2, ?_⟩
    rintro _ ⟨P, rfl⟩
    letI : IsProbabilityMeasure (annotationLaw P.1 n m) := hprob P.1
    unfold twoSampleMSE
    let B : Real := ((∑ z : Sample n m d, |est.1 z|) + 1) ^ 2
    have hpoint : ∀ z, (est.1 z - ateFunctional P.1) ^ 2 ≤ B := by
      intro z
      have htarget := ateFunctional_mem_Icc_neg_one_one P.1 P.2.overlap
      have hz : |est.1 z| ≤ ∑ w : Sample n m d, |est.1 w| :=
        Finset.single_le_sum (s := Finset.univ) (f := fun w : Sample n m d => |est.1 w|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ z)
      rcases htarget with ⟨ht0, ht1⟩
      dsimp [B]
      nlinarith [le_abs_self (est.1 z), neg_le_of_abs_le hz]
    calc
      ∫ z, (est.1 z - ateFunctional P.1) ^ 2 ∂annotationLaw P.1 n m
          ≤ ∫ _z, B ∂annotationLaw P.1 n m :=
        integral_mono_ae Integrable.of_finite Integrable.of_finite (ae_of_all _ hpoint)
      _ = B := by simp
  have hm : s ^ 2 / 4 ≤ max
      (twoSampleMSE (annotationLaw P0.1 n m) est.1 (ateFunctional P0.1))
      (twoSampleMSE (annotationLaw P1.1 n m) est.1 (ateFunctional P1.1)) := by
    calc
      s ^ 2 / 4 = s ^ 2 * (1 / 4) := by ring
      _ ≤ s ^ 2 * max
          ((annotationLaw P0.1 n m).real {z | s ≤ |est.1 z - ateFunctional P0.1|})
          ((annotationLaw P1.1 n m).real {z | s ≤ |est.1 z - ateFunctional P1.1|}) := by gcongr
      _ = max
          (s ^ 2 * (annotationLaw P0.1 n m).real {z | s ≤ |est.1 z - ateFunctional P0.1|})
          (s ^ 2 * (annotationLaw P1.1 n m).real {z | s ≤ |est.1 z - ateFunctional P1.1|}) := by
        rw [mul_max_of_nonneg _ _ (sq_nonneg s)]
      _ ≤ _ := max_le_max (hrisk P0) (hrisk P1)
  exact hm.trans (max_le (le_ciSup hb P0) (le_ciSup hb P1))

-- @node: lem:parametric-label-floor
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma parametric_label_floor :
    ∃ c : Real, 0 < c ∧ ∀ (eps : Real), 0 < eps → eps < 1 / 2 →
    ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d → c / n ≤ minimaxRisk n m d eps := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro eps heps heps2 n m d hn hd
  letI : Nonempty (Fin d) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩⟩
  let delta : Real := (2 / 5) / Real.sqrt n
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hd0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdsq : delta ^ 2 = 4 / (25 * (n : Real)) := by
    dsimp [delta]; rw [div_pow, Real.sq_sqrt hnR.le]; ring
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin d) (m₀ := (1 / 2 : Real)) (g₀ := (1 / 2 : Real)) (g₁ := (1 / 2 : Real))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdu : (1 / 2 : Real) + delta ≤ 1 := by
    have hs : 1 ≤ Real.sqrt (n : Real) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    have : delta ≤ 2 / 5 := by dsimp [delta]; exact div_le_self (by norm_num) hs
    linarith
  let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin d) (m₀ := (1 / 2 : Real)) (g₀ := (1 / 2 : Real)) (g₁ := (1 / 2 : Real))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd0 hdu
  let P0 := parametricFloorNullLaw hv0
  let P1 := parametricFloorPertLaw hv1
  let MP0 : ClassLaw d eps := ⟨P0, parametricFloorNullLaw_model hd heps heps2 hv0⟩
  let MP1 : ClassLaw d eps := ⟨P1, parametricFloorPertLaw_model hd heps heps2 hv1⟩
  have hreg : (n : Real) * ((1 / 2 : Real) * delta ^ 2 /
      ((1 / 2 : Real) * (1 - 1 / 2))) ≤ Real.log 2 := by
    rw [hdsq]
    have hlog : (8 / 25 : Real) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp [hnR.ne'] <;> ring
  have htvL : Causalean.Stat.tvDist (labeledProductLaw P0 n) (labeledProductLaw P1 n) ≤ 1 / 2 := by
    simpa [P0, P1, parametricFloorNullLaw, parametricFloorPertLaw, labeledProductLaw,
      obsLaw, Causalean.Estimation.MinimaxATE.productLaw,
      Causalean.Estimation.MinimaxATE.obsLaw] using
      (Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
        hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hreg)
  have haux : auxProductLaw P0 m = auxProductLaw P1 m := by
    unfold auxProductLaw
    rw [parametricFloor_auxMarginal_eq hv0 hv1]
  have htv : Causalean.Stat.tvDist (annotationLaw P0 n m) (annotationLaw P1 n m) ≤ 1 / 2 := by
    haveI : IsProbabilityMeasure (labeledProductLaw P0 n) := by
      unfold labeledProductLaw; infer_instance
    haveI : IsProbabilityMeasure (labeledProductLaw P1 n) := by
      unfold labeledProductLaw; infer_instance
    haveI : IsProbabilityMeasure (auxProductLaw P1 m) := by
      unfold auxProductLaw; infer_instance
    rw [annotationLaw, haux]
    calc
      _ ≤ Causalean.Stat.tvDist (labeledProductLaw P0 n) (labeledProductLaw P1 n) +
          Causalean.Stat.tvDist (auxProductLaw P1 m) (auxProductLaw P1 m) :=
        Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add _ _ _ _
      _ ≤ 1 / 2 := by
        have hz : Causalean.Stat.tvDist (auxProductLaw P1 m) (auxProductLaw P1 m) = 0 := by
          apply le_antisymm
          · unfold Causalean.Stat.tvDist
            exact ciSup_le fun A => by simp
          · exact Causalean.Stat.tvDist_nonneg
        rw [hz]
        linarith
  have hsep : 2 * (delta / 2) ≤ |ateFunctional MP0.1 - ateFunctional MP1.1| := by
    rw [show ateFunctional MP0.1 = 0 by simpa [MP0, P0] using parametricFloorNullLaw_ate hv0,
      show ateFunctional MP1.1 = delta by simpa [MP1, P1] using parametricFloorPertLaw_ate hv1]
    rw [show 2 * (delta / 2) = delta by ring, zero_sub, abs_neg, abs_of_nonneg hd0]
  have hlow := annotationMinimaxRisk_ge_two_model_tv MP0 MP1 (s := delta / 2)
    (by positivity) hsep htv
  calc
    1 / 100 / (n : Real) = (delta / 2) ^ 2 / 4 := by
      rw [show (delta / 2) ^ 2 = delta ^ 2 / 4 by ring, hdsq]
      ring
    _ ≤ minimaxRisk n m d eps := hlow

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
