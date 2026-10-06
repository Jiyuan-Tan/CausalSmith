module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedAdditiveRepresentation
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.BernoulliHypercubeKL

/-! # Pilot KL bound for the folded hypercube -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

@[fun_prop]
lemma measurable_foldedRawScore_of_measurable_bumps (hd : 0 < d)
    (beta h kappa eps : ℝ) (K : ℕ) (psi : Fin K -> XSpace d -> ℝ)
    (hpsi : ∀ j, Measurable (psi j)) (theta : Fin K -> Bool) :
    Measurable (foldedRawScore hd beta h kappa eps K psi theta) := by
  unfold foldedRawScore
  split
  · apply Measurable.add measurable_const
    apply Measurable.mul measurable_const
    apply measurable_triangularFold.comp
    fun_prop
  · fun_prop

lemma meshCube_measureReal_upper (d q : ℕ) (hq : 0 < q)
    (k : Fin d -> ℕ) (hk : ∀ i, k i < q) :
    (cubeMeasure d).real (meshCube ((q : ℝ)⁻¹) k) ≤ ((q : ℝ)⁻¹) ^ d := by
  let h : ℝ := (q : ℝ)⁻¹
  let lo : XSpace d := fun i => (k i : ℝ) * h
  let hi : XSpace d := fun i => ((k i : ℝ) + 1) * h
  let R : Set (XSpace d) := Set.Icc lo hi
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < h := by dsimp [h]; positivity
  have hle : lo ≤ hi := by
    intro i
    dsimp [lo, hi]
    exact mul_le_mul_of_nonneg_right (by linarith) hh.le
  have hsub : meshCube h k ⊆ R := by
    intro x hx
    constructor
    · intro i
      exact (hx.2 i).1
    · intro i
      exact (hx.2 i).2.elim le_of_lt (fun heq => by
        rcases heq with ⟨hx1, hhi⟩
        dsimp [hi]
        rw [hx1, hhi])
  have hRcube : R ⊆ cube d := by
    intro x hx i
    have hki : (k i : ℝ) + 1 ≤ q := by
      exact_mod_cast Nat.succ_le_of_lt (hk i)
    have hupper : hi i ≤ 1 := by
      dsimp [hi, h]
      calc
        ((k i : ℝ) + 1) * (q : ℝ)⁻¹ ≤ (q : ℝ) * (q : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hki (inv_nonneg.mpr hqR.le)
        _ = 1 := mul_inv_cancel₀ hqR.ne'
    constructor
    · exact (by dsimp [lo]; positivity : 0 ≤ lo i) |>.trans (hx.1 i)
    · exact (hx.2 i).trans hupper
  have hcubeMeas : MeasurableSet (cube d) := by
    exact MeasurableSet.univ_pi' (fun _ : Fin d => measurableSet_Icc)
  have hRmass : (cubeMeasure d).real R = h ^ d := by
    have hrestrict : (cubeMeasure d).real R = volume.real R := by
      unfold cubeMeasure
      rw [measureReal_restrict_apply' hcubeMeas]
      simp [Set.inter_eq_self_of_subset_left hRcube, ← MeasureTheory.volume_pi]
    rw [hrestrict]
    dsimp [R]
    rw [measureReal_def, Real.volume_Icc_pi_toReal hle]
    have hdiff : ∀ i : Fin d, hi i - lo i = h := by
      intro i
      dsimp [hi, lo]
      ring
    simp_rw [hdiff]
    simp
  rw [show (q : ℝ)⁻¹ = h by rfl, ← hRmass]
  exact measureReal_mono hsub (by
    have hfinite : cubeMeasure d Set.univ ≠ ⊤ := by
      letI : IsProbabilityMeasure (cubeMeasure d) := cubeMeasure_isProbabilityMeasure d
      simp
    exact ne_top_of_le_ne_top hfinite (measure_mono (Set.subset_univ R)))

lemma FoldedGeometry.cell_measureReal_upper
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B) (j : Fin K) :
    (cubeMeasure d).real (Q j) ≤ ((q : ℝ)⁻¹) ^ d := by
  rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
  have hactive : activeMeshCell hd q (idx j) :=
    (hcomplete (idx j)).2 ⟨j, rfl⟩
  rw [(hdefs j).1]
  exact meshCube_measureReal_upper d q hq (idx j) hactive.1

lemma flip_signed_bump_sum_gap
    (theta : Fin K -> Bool) (psi : Fin K -> XSpace d -> ℝ)
    (j : Fin K) (x : XSpace d) :
    |(∑ i : Fin K, localSign (theta i) * psi i x) -
      ∑ i : Fin K, localSign ((flipCoordinate theta j) i) * psi i x| =
      2 * |psi j x| := by
  have hsum : (∑ i : Fin K, localSign (theta i) * psi i x) -
      ∑ i : Fin K, localSign ((flipCoordinate theta j) i) * psi i x =
      2 * localSign (theta j) * psi j x := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · cases hval : theta j <;> simp [flipCoordinate, localSign, hval] <;> ring
    · intro i hi hij
      simp [flipCoordinate, hij]
    · simp
  rw [hsum, abs_mul, abs_mul, abs_localSign]
  norm_num

/-- Flipping one active sign has the required randomized-pilot KL budget. -/
lemma FoldedGeometry.bernoulliPilotProduct_klDiv_flip_le
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {beta kappa eps : ℝ} (hbeta : beta < 1)
    (ha0 : 0 ≤ kappa * (q : ℝ)⁻¹ ^ beta)
    (ha12 : kappa * (q : ℝ)⁻¹ ^ beta ≤ 1 / 12)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (m : ℕ) (theta : Fin K -> Bool) (j : Fin K) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw
        (bernoulliUnitLaw (foldedHypercube hd beta (q : ℝ)⁻¹ kappa eps K psi theta)))
      (Measure.pi fun _ : Fin m => pilotUnitLaw
        (bernoulliUnitLaw (foldedHypercube hd beta (q : ℝ)⁻¹ kappa eps K psi
          (flipCoordinate theta j)))) ≤
      ENNReal.ofReal ((m : ℝ) *
        (8 * (eps * (kappa * (q : ℝ)⁻¹ ^ beta)) ^ 2 *
          ((q : ℝ)⁻¹) ^ d)) := by
  let g := foldedHypercube hd beta (q : ℝ)⁻¹ kappa eps K psi theta
  let g' := foldedHypercube hd beta (q : ℝ)⁻¹ kappa eps K psi
    (flipCoordinate theta j)
  have hpsi : ∀ i, Measurable (psi i) := by
    intro i
    rcases hgeo with ⟨hq, idx, hinj, hcomplete, hdefs⟩
    rw [(hdefs i).2.1]
    exact measurable_meshBump hd _ _
  have hg : Measurable g := by
    exact measurable_foldedRawScore_of_measurable_bumps hd beta _ kappa eps K psi hpsi theta
  have hg' : Measurable g' := by
    exact measurable_foldedRawScore_of_measurable_bumps hd beta _ kappa eps K psi hpsi
      (flipCoordinate theta j)
  have hband : ∀ x ∈ cube d, 1 / 4 ≤ g x ∧ g x ≤ 3 / 4 := by
    intro x hx
    have hm := triangularFold_mem_Icc
      (x ⟨0, hd⟩ + kappa * (q : ℝ)⁻¹ ^ beta *
        triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹) +
        eps * (kappa * (q : ℝ)⁻¹ ^ beta) *
          ∑ i, localSign (theta i) * psi i x)
    simp only [g, foldedHypercube, foldedRawScore, hbeta, if_true]
    constructor <;> linarith [hm.1, hm.2]
  have hband' : ∀ x ∈ cube d, 1 / 4 ≤ g' x ∧ g' x ≤ 3 / 4 := by
    intro x hx
    have hm := triangularFold_mem_Icc
      (x ⟨0, hd⟩ + kappa * (q : ℝ)⁻¹ ^ beta *
        triangularWave (x ⟨0, hd⟩ / (q : ℝ)⁻¹) +
        eps * (kappa * (q : ℝ)⁻¹ ^ beta) *
          ∑ i, localSign ((flipCoordinate theta j) i) * psi i x)
    simp only [g', foldedHypercube, foldedRawScore, hbeta, if_true]
    constructor <;> linarith [hm.1, hm.2]
  have hQ : MeasurableSet (Q j) := by
    rcases hgeo.isSideCube j with ⟨a, ha, hQa⟩
    rw [hQa]
    unfold cube
    measurability
  have hoff : ∀ x ∉ Q j, g x = g' x := by
    intro x hx
    exact hgeo.foldedHypercube_flip_eq_off_cell beta kappa eps theta j x hx
  have hgap : ∀ x ∈ Q j,
      |g x - g' x| ≤ eps * (kappa * (q : ℝ)⁻¹ ^ beta) := by
    intro x hx
    dsimp [g, g', foldedHypercube]
    rw [hgeo.foldedRawScore_additive hbeta ha0 ha12 heps0 heps,
      hgeo.foldedRawScore_additive hbeta ha0 ha12 heps0 heps]
    have hsum := flip_signed_bump_sum_gap theta psi j x
    have hb0 := (hgeo.bump_bounds j x).1
    have hb := (hgeo.bump_bounds j x).2
    calc
      |(foldedBaseScore hd beta (q : ℝ)⁻¹ kappa x +
          eps * (kappa * (q : ℝ)⁻¹ ^ beta) / 2 *
            ∑ i, localSign (theta i) * psi i x) -
        (foldedBaseScore hd beta (q : ℝ)⁻¹ kappa x +
          eps * (kappa * (q : ℝ)⁻¹ ^ beta) / 2 *
            ∑ i, localSign ((flipCoordinate theta j) i) * psi i x)| =
          |eps * (kappa * (q : ℝ)⁻¹ ^ beta) / 2| * (2 * |psi j x|) := by
            rw [← hsum, ← abs_mul]
            congr 1
            ring
      _ ≤ eps * (kappa * (q : ℝ)⁻¹ ^ beta) := by
        rw [abs_of_nonneg (div_nonneg (mul_nonneg heps0 ha0) (by norm_num)),
          abs_of_nonneg hb0]
        have hcoef : 0 ≤ eps * (kappa * (q : ℝ)⁻¹ ^ beta) :=
          mul_nonneg heps0 ha0
        have hmul : eps * (kappa * (q : ℝ)⁻¹ ^ beta) * psi j x ≤
            eps * (kappa * (q : ℝ)⁻¹ ^ beta) :=
          mul_le_of_le_one_right hcoef hb
        nlinarith
  refine (bernoulliPilotProduct_klDiv_le_cell m g g' hg hg' hband hband'
    (Q j) hQ hoff (eps * (kappa * (q : ℝ)⁻¹ ^ beta))
    (mul_nonneg heps0 ha0) hgap).trans ?_
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact hgeo.cell_measureReal_upper j

/-- The cellwise budget in the power form used by `HypercubeFamily`. -/
lemma FoldedGeometry.bernoulliPilotProduct_klDiv_flip_rpow_le
    {hd : 0 < d} {q K : ℕ} {Q : Fin K -> Set (XSpace d)}
    {psi : Fin K -> XSpace d -> ℝ} {B : Fin K -> Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B)
    {beta kappa eps : ℝ} (hbeta : beta < 1)
    (ha0 : 0 ≤ kappa * (q : ℝ)⁻¹ ^ beta)
    (ha12 : kappa * (q : ℝ)⁻¹ ^ beta ≤ 1 / 12)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 64)
    (m : ℕ) (theta : Fin K -> Bool) (j : Fin K) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin m => pilotUnitLaw
        (bernoulliUnitLaw (foldedHypercube hd beta (q : ℝ)⁻¹ kappa eps K psi theta)))
      (Measure.pi fun _ : Fin m => pilotUnitLaw
        (bernoulliUnitLaw (foldedHypercube hd beta (q : ℝ)⁻¹ kappa eps K psi
          (flipCoordinate theta j)))) ≤
      ENNReal.ofReal ((8 * eps ^ 2 * kappa ^ 2) * (m : ℝ) *
        ((q : ℝ)⁻¹) ^ ((d : ℝ) + 2 * beta)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hgeo.1
  have hh : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hqR
  refine (hgeo.bernoulliPilotProduct_klDiv_flip_le hbeta ha0 ha12 heps0 heps
    m theta j).trans ?_
  apply le_of_eq
  congr 1
  have hpow : (((q : ℝ)⁻¹ ^ beta) ^ 2 * ((q : ℝ)⁻¹) ^ d) =
      ((q : ℝ)⁻¹) ^ ((d : ℝ) + 2 * beta) := by
    calc
      (((q : ℝ)⁻¹ ^ beta) ^ 2 * ((q : ℝ)⁻¹) ^ d) =
          ((q : ℝ)⁻¹) ^ (beta * 2) * ((q : ℝ)⁻¹) ^ (d : ℝ) := by
            rw [← Real.rpow_natCast ((q : ℝ)⁻¹ ^ beta) 2,
              ← Real.rpow_mul hh.le, Real.rpow_natCast]
            norm_num
      _ = ((q : ℝ)⁻¹) ^ ((d : ℝ) + 2 * beta) := by
        rw [← Real.rpow_add hh]
        congr 1
        ring
  rw [show (eps * (kappa * (q : ℝ)⁻¹ ^ beta)) ^ 2 =
      eps ^ 2 * kappa ^ 2 * (((q : ℝ)⁻¹ ^ beta) ^ 2) by ring]
  calc
    (m : ℝ) * (8 * (eps ^ 2 * kappa ^ 2 * (((q : ℝ)⁻¹ ^ beta) ^ 2)) *
        ((q : ℝ)⁻¹) ^ d) =
        8 * eps ^ 2 * kappa ^ 2 * (m : ℝ) *
          ((((q : ℝ)⁻¹ ^ beta) ^ 2) * ((q : ℝ)⁻¹) ^ d) := by ring
    _ = _ := by rw [hpow]

end CausalSmith.Experimentation.PilotscorePairingFrontier
