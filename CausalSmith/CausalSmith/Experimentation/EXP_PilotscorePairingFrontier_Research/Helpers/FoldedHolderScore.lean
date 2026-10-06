module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedScalarLipschitz

/-! # Holder certificate for the folded hypercube score -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

lemma rpow_scale_local {h r beta : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (hrh : r ≤ h) (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    h ^ beta / h * r ≤ r ^ beta := by
  by_cases hr0 : r = 0
  · subst r
    simp [Real.zero_rpow hbeta0.ne']
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  let u := r / h
  have hu0 : 0 < u := div_pos hrpos hh
  have hu1 : u ≤ 1 := (div_le_one hh).2 hrh
  have hupow : u ≤ u ^ beta := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hbeta1
  have hrepr : r = h * u := by dsimp [u]; field_simp
  rw [hrepr, Real.mul_rpow hh.le hu0.le]
  have hhpow : 0 ≤ h ^ beta := Real.rpow_nonneg hh.le _
  calc
    h ^ beta / h * (h * u) = h ^ beta * u := by field_simp
    _ ≤ h ^ beta * u ^ beta := mul_le_mul_of_nonneg_left hupow hhpow

lemma foldedRawScore_diff_lipschitz
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {beta kappa eps : ℝ} (hbeta : beta < 1)
    (ha0 : 0 ≤ kappa * (q : ℝ)⁻¹ ^ beta) (heps0 : 0 ≤ eps)
    (theta : Fin K -> Bool) (x y : XSpace d) :
    |foldedRawScore hd beta (q : ℝ)⁻¹ kappa eps K psi theta x -
      foldedRawScore hd beta (q : ℝ)⁻¹ kappa eps K psi theta y| ≤
      (1 / 2 + 2 * (kappa * (q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹) +
        48 * eps * (d : ℝ) *
          (kappa * (q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹)) *
        euclideanDistance x y := by
  let z : Fin d := ⟨0, hd⟩
  let S : XSpace d -> ℝ := fun w =>
    ∑ i : Fin K, localSign (theta i) * psi i w
  let a := kappa * (q : ℝ)⁻¹ ^ beta
  let u : XSpace d -> ℝ := fun w =>
    w z + a * triangularWave (w z / (q : ℝ)⁻¹) + eps * a * S w
  have hfold := triangularFold_diff_le (u x) (u y)
  simp only [foldedRawScore, hbeta, if_true]
  rw [show (1 / 4 + 1 / 2 * triangularFold (u x)) -
      (1 / 4 + 1 / 2 * triangularFold (u y)) =
      (1 / 2) * (triangularFold (u x) - triangularFold (u y)) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hz := coordinate_abs_sub_le_euclideanDistance x y z
  have hw := triangularWave_diff_le (x z / (q : ℝ)⁻¹) (y z / (q : ℝ)⁻¹)
  have hS := hgeo.signed_bump_sum_diff_le theta x y
  have hqpos : 0 < (q : ℝ)⁻¹ := by
    have : (0 : ℝ) < q := by exact_mod_cast hgeo.1
    positivity
  have hu : |u x - u y| ≤
      (1 + 4 * a / (q : ℝ)⁻¹ +
        96 * eps * a * (d : ℝ) / (q : ℝ)⁻¹) * euclideanDistance x y := by
    dsimp [u]
    calc
      |(x z + a * triangularWave (x z / (q : ℝ)⁻¹) + eps * a * S x) -
          (y z + a * triangularWave (y z / (q : ℝ)⁻¹) + eps * a * S y)| ≤
          |x z - y z| + |a| *
            |triangularWave (x z / (q : ℝ)⁻¹) -
              triangularWave (y z / (q : ℝ)⁻¹)| +
            |eps * a| * |S x - S y| := by
              rw [show (x z + a * triangularWave (x z / (q : ℝ)⁻¹) + eps * a * S x) -
                (y z + a * triangularWave (y z / (q : ℝ)⁻¹) + eps * a * S y) =
                (x z - y z) + a * (triangularWave (x z / (q : ℝ)⁻¹) -
                  triangularWave (y z / (q : ℝ)⁻¹)) +
                  eps * a * (S x - S y) by ring]
              calc
                _ ≤ |x z - y z| + |a * (triangularWave (x z / (q : ℝ)⁻¹) -
                    triangularWave (y z / (q : ℝ)⁻¹))| +
                    |eps * a * (S x - S y)| := by
                      exact (abs_add_le _ _).trans
                        (add_le_add (abs_add_le _ _) le_rfl)
                _ = _ := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ euclideanDistance x y + a *
            (4 / (q : ℝ)⁻¹ * euclideanDistance x y) +
          (eps * a) * (96 * (d : ℝ) / (q : ℝ)⁻¹ * euclideanDistance x y) := by
        rw [abs_of_nonneg ha0, abs_of_nonneg (mul_nonneg heps0 ha0)]
        apply add_le_add
        · apply add_le_add hz
          apply mul_le_mul_of_nonneg_left _ ha0
          calc
            _ ≤ 4 * |(x z / (q : ℝ)⁻¹) - (y z / (q : ℝ)⁻¹)| := hw
            _ = 4 / (q : ℝ)⁻¹ * |x z - y z| := by
              rw [show x z / (q : ℝ)⁻¹ - y z / (q : ℝ)⁻¹ =
                (x z - y z) / (q : ℝ)⁻¹ by ring, abs_div, abs_of_pos hqpos]
              ring
            _ ≤ _ := by
              exact mul_le_mul_of_nonneg_left hz (by positivity)
        · exact mul_le_mul_of_nonneg_left hS (mul_nonneg heps0 ha0)
      _ = _ := by dsimp [a]; ring
  calc
    (1 / 2) * |triangularFold (u x) - triangularFold (u y)| ≤
        (1 / 2) * |u x - u y| := mul_le_mul_of_nonneg_left hfold (by norm_num)
    _ ≤ (1 / 2) * ((1 + 4 * a / (q : ℝ)⁻¹ +
        96 * eps * a * (d : ℝ) / (q : ℝ)⁻¹) * euclideanDistance x y) :=
      mul_le_mul_of_nonneg_left hu (by norm_num)
    _ = _ := by dsimp [a]; ring

/-- The folded score has the class Hölder radius with the corrected
dimension-dependent constant `128*d`. -/
lemma FoldedGeometry.foldedRawScore_holder
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {beta kappa eps : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hkappa0 : 0 ≤ kappa) (heps0 : 0 ≤ eps)
    (hepsD : (128 * (d : ℝ)) * eps ≤ 1)
    (theta : Fin K -> Bool) :
    HolderScore (foldedRawScore hd beta (q : ℝ)⁻¹ kappa eps K psi theta)
      (1 / 2 + (128 * (d : ℝ)) * kappa) beta := by
  intro x hx y hy
  let r := euclideanDistance x y
  let h : ℝ := (q : ℝ)⁻¹
  let a := kappa * h ^ beta
  have hqR : (0 : ℝ) < q := by exact_mod_cast hgeo.1
  have hh : 0 < h := by dsimp [h]; positivity
  have hr0 : 0 ≤ r := by dsimp [r, euclideanDistance]; positivity
  have ha0 : 0 ≤ a := mul_nonneg hkappa0 (Real.rpow_nonneg hh.le _)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcoef : 2 + 48 * eps * (d : ℝ) ≤ 128 * (d : ℝ) := by
    have he : 48 * eps * (d : ℝ) ≤ 3 / 8 := by nlinarith
    nlinarith
  by_cases hrzero : r = 0
  · have hxy : x = y := by
      dsimp [r] at hrzero
      apply funext
      intro i
      have hc := coordinate_abs_sub_le_euclideanDistance x y i
      rw [hrzero] at hc
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hc (abs_nonneg _)))
    subst y
    unfold euclideanDistance
    simp [Real.zero_rpow hbeta0.ne']
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrzero)
  by_cases hrone : 1 ≤ r
  · have hf1 := triangularFold_mem_Icc
      (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
        eps * a * ∑ i, localSign (theta i) * psi i x)
    have hf2 := triangularFold_mem_Icc
      (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
        eps * a * ∑ i, localSign (theta i) * psi i y)
    have hdiff : |foldedRawScore hd beta h kappa eps K psi theta x -
        foldedRawScore hd beta h kappa eps K psi theta y| ≤ 1 / 2 := by
      simp only [foldedRawScore, hbeta1, if_true]
      rw [show (1 / 4 + 1 / 2 * triangularFold
          (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i x)) -
          (1 / 4 + 1 / 2 * triangularFold
          (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i y)) =
          (1 / 2) * (triangularFold
          (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i x) -
          triangularFold
          (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i y)) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have habs : |triangularFold
          (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i x) -
          triangularFold
          (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i y)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hf1.1, hf1.2, hf2.1, hf2.2]
      nlinarith
    have hrpow : 1 ≤ r ^ beta := Real.one_le_rpow hrone hbeta0.le
    exact hdiff.trans (by
      have hL0 : 0 ≤ 1 / 2 + (128 * (d : ℝ)) * kappa := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrpow hL0])
  have hrle1 : r ≤ 1 := le_of_not_ge hrone
  have hrrpow : r ≤ r ^ beta := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hrpos hrle1 hbeta1.le
  by_cases hrh : r ≤ h
  · have hlip := foldedRawScore_diff_lipschitz hgeo hbeta1 ha0 heps0 theta x y
    have hscale := rpow_scale_local hh hr0 hrh hbeta0 hbeta1.le
    dsimp [h, r, a] at hlip hscale ⊢
    calc
      _ ≤ (1 / 2 + 2 * (kappa * (q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹) +
          48 * eps * (d : ℝ) *
            (kappa * (q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹)) *
          euclideanDistance x y := hlip
      _ ≤ (1 / 2 + (2 + 48 * eps * (d : ℝ)) * kappa) *
          (euclideanDistance x y) ^ beta := by
        have hkhs : kappa * ((q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹ *
            euclideanDistance x y) ≤ kappa * (euclideanDistance x y) ^ beta :=
          mul_le_mul_of_nonneg_left hscale hkappa0
        have hhalf : (1 / 2) * euclideanDistance x y ≤
            (1 / 2) * (euclideanDistance x y) ^ beta :=
          mul_le_mul_of_nonneg_left hrrpow (by norm_num)
        have h2 := mul_le_mul_of_nonneg_left hkhs (by norm_num : (0 : ℝ) ≤ 2)
        have hfac : 0 ≤ 48 * eps * (d : ℝ) := by positivity
        have h48 := mul_le_mul_of_nonneg_left hkhs hfac
        calc
          _ = (1 / 2) * euclideanDistance x y +
              2 * (kappa * ((q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹ *
                euclideanDistance x y)) +
              (48 * eps * (d : ℝ)) *
                (kappa * ((q : ℝ)⁻¹ ^ beta / (q : ℝ)⁻¹ *
                  euclideanDistance x y)) := by ring
          _ ≤ (1 / 2) * (euclideanDistance x y) ^ beta +
              2 * (kappa * (euclideanDistance x y) ^ beta) +
              (48 * eps * (d : ℝ)) *
                (kappa * (euclideanDistance x y) ^ beta) :=
            add_le_add (add_le_add hhalf h2) h48
          _ = _ := by ring
      _ ≤ (1 / 2 + (128 * (d : ℝ)) * kappa) *
          (euclideanDistance x y) ^ beta := by
        gcongr
  · have hrh' : h < r := lt_of_not_ge hrh
    have hwx := triangularWave_mem_Icc (x ⟨0, hd⟩ / h)
    have hwy := triangularWave_mem_Icc (y ⟨0, hd⟩ / h)
    have hSx := signed_bump_sum_abs_le_one
      (fun i j hij => hgeo.pairwise_disjoint hij)
      (fun j w => ⟨(hgeo.bump_bounds j w).1, (hgeo.bump_bounds j w).2,
        fun hw => hgeo.bump_eq_zero_off_cell j hw⟩) theta x
    have hSy := signed_bump_sum_abs_le_one
      (fun i j hij => hgeo.pairwise_disjoint hij)
      (fun j w => ⟨(hgeo.bump_bounds j w).1, (hgeo.bump_bounds j w).2,
        fun hw => hgeo.bump_eq_zero_off_cell j hw⟩) theta y
    have hglobal : |foldedRawScore hd beta h kappa eps K psi theta x -
        foldedRawScore hd beta h kappa eps K psi theta y| ≤
        (1 / 2) * r + a + eps * a := by
      simp only [foldedRawScore, hbeta1, if_true]
      rw [show (1 / 4 + 1 / 2 * triangularFold
          (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i x)) -
          (1 / 4 + 1 / 2 * triangularFold
          (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i y)) =
          (1 / 2) * (triangularFold
          (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i x) -
          triangularFold
          (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
            eps * a * ∑ i, localSign (theta i) * psi i y)) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hf := triangularFold_diff_le
        (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
          eps * a * ∑ i, localSign (theta i) * psi i x)
        (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
          eps * a * ∑ i, localSign (theta i) * psi i y)
      have hz := coordinate_abs_sub_le_euclideanDistance x y ⟨0, hd⟩
      calc
        _ ≤ (1 / 2) * |(x ⟨0, hd⟩ - y ⟨0, hd⟩) +
            a * (triangularWave (x ⟨0, hd⟩ / h) - triangularWave (y ⟨0, hd⟩ / h)) +
            eps * a * ((∑ i, localSign (theta i) * psi i x) -
              ∑ i, localSign (theta i) * psi i y)| := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                rw [← show
                  (x ⟨0, hd⟩ + a * triangularWave (x ⟨0, hd⟩ / h) +
                    eps * a * ∑ i, localSign (theta i) * psi i x) -
                  (y ⟨0, hd⟩ + a * triangularWave (y ⟨0, hd⟩ / h) +
                    eps * a * ∑ i, localSign (theta i) * psi i y) =
                  (x ⟨0, hd⟩ - y ⟨0, hd⟩) +
                    a * (triangularWave (x ⟨0, hd⟩ / h) - triangularWave (y ⟨0, hd⟩ / h)) +
                    eps * a * ((∑ i, localSign (theta i) * psi i x) -
                      ∑ i, localSign (theta i) * psi i y) by ring]
                exact hf
        _ ≤ (1 / 2) * (r + a * 2 + eps * a * 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc
            _ ≤ |x ⟨0, hd⟩ - y ⟨0, hd⟩| +
                a * |triangularWave (x ⟨0, hd⟩ / h) - triangularWave (y ⟨0, hd⟩ / h)| +
                eps * a * |(∑ i, localSign (theta i) * psi i x) -
                  ∑ i, localSign (theta i) * psi i y| := by
                    simpa [abs_mul, abs_of_nonneg ha0,
                      abs_of_nonneg (mul_nonneg heps0 ha0)] using
                      (abs_add_le (x ⟨0, hd⟩ - y ⟨0, hd⟩ +
                        a * (triangularWave (x ⟨0, hd⟩ / h) - triangularWave (y ⟨0, hd⟩ / h)))
                        (eps * a * ((∑ i, localSign (theta i) * psi i x) -
                          ∑ i, localSign (theta i) * psi i y))).trans
                      (add_le_add (abs_add_le _ _) le_rfl)
            _ ≤ r + a * 2 + eps * a * 2 := by
              have hw : |triangularWave (x ⟨0, hd⟩ / h) - triangularWave (y ⟨0, hd⟩ / h)| ≤ 2 := by
                rw [abs_le]
                constructor <;> linarith [hwx.1, hwx.2, hwy.1, hwy.2]
              have hs : |(∑ i, localSign (theta i) * psi i x) -
                  ∑ i, localSign (theta i) * psi i y| ≤ 2 :=
                (abs_sub _ _).trans (by nlinarith [hSx, hSy])
              gcongr
        _ = _ := by ring
    have hhpow : h ^ beta ≤ r ^ beta :=
      Real.rpow_le_rpow hh.le hrh'.le hbeta0.le
    dsimp [a] at hglobal
    calc
      _ ≤ (1 / 2) * r + kappa * h ^ beta + eps * (kappa * h ^ beta) := hglobal
      _ ≤ (1 / 2 + (1 + eps) * kappa) * r ^ beta := by
        have ha : kappa * h ^ beta ≤ kappa * r ^ beta :=
          mul_le_mul_of_nonneg_left hhpow hkappa0
        have hea : eps * (kappa * h ^ beta) ≤ eps * (kappa * r ^ beta) :=
          mul_le_mul_of_nonneg_left ha heps0
        have hhalf := mul_le_mul_of_nonneg_left hrrpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
        nlinarith
      _ ≤ (1 / 2 + (128 * (d : ℝ)) * kappa) * r ^ beta := by
        have heps1 : eps ≤ 1 := by nlinarith
        have hrpow0 : 0 ≤ r ^ beta := Real.rpow_nonneg hr0 _
        have : 1 + eps ≤ 128 * (d : ℝ) := by nlinarith
        gcongr

end CausalSmith.Experimentation.PilotscorePairingFrontier
