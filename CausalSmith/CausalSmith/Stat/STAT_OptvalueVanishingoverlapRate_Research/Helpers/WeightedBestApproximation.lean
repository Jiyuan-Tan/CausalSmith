module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketResponseLower
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedDuality

/-! # Attainment of the weighted polynomial approximation error

The reverse comparison in roadmap (3)--(8) starts with a best weighted
approximant. Multiplication by the continuous reciprocal weight embeds the
degree-bounded polynomial space in the continuous functions on the compact
interval. Its finite dimension gives a compact minimizing ball, hence an
actual minimizer rather than an assumed dual certificate.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

set_option maxHeartbeats 2000000 in
-- Finite-dimensional continuous-function subspace instances require substantial reduction.
/-- The weighted infimum is attained by a polynomial of the prescribed degree. This is the minimizer used to construct the active residual set in roadmap (3). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
theorem weightedApproxError_attained (K : ℕ) {M : ℝ} (hM : 0 ≤ M) (ε : ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ K ∧
      sSup ((fun z : ℝ => |phiEpsFormula ε z - p.eval z| / (1 + z)) '' Set.Icc 0 M) =
        weightedApproxError K M ε := by
  classical
  let I := Set.Icc (0 : ℝ) M
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : Nonempty I := ⟨⟨0, le_rfl, hM⟩⟩
  let w : C(I, ℝ) := ⟨fun z => (1 + (z : ℝ))⁻¹, by
    apply Continuous.inv₀
    · fun_prop
    · intro z
      have hz := z.property.1
      dsimp [I] at hz
      linarith⟩
  let f : C(I, ℝ) := ⟨fun z => phiEpsFormula ε z / (1 + (z : ℝ)), by
    unfold phiEpsFormula
    apply Continuous.div
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro z; have hz := z.property.1; dsimp [I] at hz; linarith
    · fun_prop
    · intro z; have hz := z.property.1; dsimp [I] at hz; linarith⟩
  let T : Polynomial ℝ →ₗ[ℝ] C(I, ℝ) :=
    { toFun := fun p => w * p.toContinuousMapOn I
      map_add' := by intro p q; ext z; simp [mul_add]
      map_smul' := by intro a p; ext z; simp [mul_left_comm] }
  let D := Polynomial.degreeLT ℝ (K + 1)
  let S := T.domRestrict D
  let V := S.range
  letI : FiniteDimensional ℝ D :=
    (Polynomial.degreeLT.basis ℝ (K + 1)).finiteDimensional_of_finite
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.of_surjective S.rangeRestrict (by
      intro q
      obtain ⟨p, hp⟩ := q.property
      exact ⟨p, Subtype.ext hp⟩)
  let e := fun p : Polynomial ℝ =>
    sSup ((fun z : ℝ => |phiEpsFormula ε z - p.eval z| / (1 + z)) '' I)
  have he (p : Polynomial ℝ) : e p = ‖f - T p‖ := by
    have hc : ContinuousOn (fun z : ℝ =>
        |phiEpsFormula ε z - p.eval z| / (1 + z)) I := by
      unfold phiEpsFormula
      apply ContinuousOn.div
      · apply ContinuousOn.abs
        apply ContinuousOn.sub
        · apply ContinuousOn.div
          · fun_prop
          · fun_prop
          · intro z hz; dsimp [I] at hz; linarith [hz.1]
        · fun_prop
      · fun_prop
      · intro z hz; dsimp [I] at hz; linarith [hz.1]
    have hpoint (z : I) : ‖(f - T p) z‖ =
        |phiEpsFormula ε z - p.eval (z : ℝ)| / (1 + (z : ℝ)) := by
      have hz : 0 < 1 + (z : ℝ) := by
        have hz := z.property.1; dsimp [I] at hz; linarith
      change |phiEpsFormula ε z / (1 + (z : ℝ)) -
        (1 + (z : ℝ))⁻¹ * p.eval (z : ℝ)| = _
      rw [inv_mul_eq_div, ← sub_div, abs_div, abs_of_pos hz]
    apply le_antisymm
    · apply csSup_le (by exact ⟨_, 0, ⟨le_rfl, hM⟩, rfl⟩)
      rintro v ⟨z, hz, rfl⟩
      exact (hpoint ⟨z, hz⟩).symm.le.trans (ContinuousMap.norm_coe_le_norm _ _)
    · apply (ContinuousMap.norm_le_of_nonempty _).mpr
      intro z
      rw [hpoint]
      exact le_csSup (isCompact_Icc.bddAbove_image hc)
        (Set.mem_image_of_mem _ z.property)
  let R : ℝ := 2 * ‖f‖ + 1
  let B : Set V := Metric.closedBall 0 R
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hzero : (0 : V) ∈ B := by simp [B, hR]
  have hcompact : IsCompact B := ProperSpace.isCompact_closedBall 0 R
  obtain ⟨q, _, hqmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩
    (show Continuous (fun q : V => ‖f - (q : C(I, ℝ))‖) from by fun_prop).continuousOn
  have hqzero : ‖f - (q : C(I, ℝ))‖ ≤ ‖f‖ := by simpa using hqmin hzero
  have hglobal (u : V) : ‖f - (q : C(I, ℝ))‖ ≤ ‖f - (u : C(I, ℝ))‖ := by
    by_cases hu : u ∈ B
    · exact hqmin hu
    · have hunorm : R < ‖u‖ := by
        simpa only [B, Metric.mem_closedBall, dist_zero_right, not_le] using hu
      have hdiff := norm_sub_norm_le (u : C(I, ℝ)) f
      have hlower : ‖f‖ ≤ ‖(u : C(I, ℝ)) - f‖ := by
        dsimp [R] at hunorm
        change ‖(u : C(I, ℝ))‖ - ‖f‖ ≤ ‖(u : C(I, ℝ)) - f‖ at hdiff
        linarith
      rw [norm_sub_rev] at hlower
      exact hqzero.trans hlower
  obtain ⟨p, hpq⟩ := q.property
  have hpdeg : (p : Polynomial ℝ).natDegree ≤ K := by
    apply Polynomial.natDegree_le_iff_degree_le.mpr
    apply Polynomial.mem_degreeLE.mp
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    exact p.property
  have hmin (u : Polynomial ℝ) (hu : u.natDegree ≤ K) : e p ≤ e u := by
    have huD : u ∈ D := by
      dsimp [D]
      rw [Polynomial.degreeLT_succ_eq_degreeLE]
      exact Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp hu)
    let uv : V := ⟨T u, ⟨⟨u, huD⟩, rfl⟩⟩
    rw [he, he]
    change ‖f - T (p : Polynomial ℝ)‖ ≤ ‖f - (uv : C(I, ℝ))‖
    change T (p : Polynomial ℝ) = (q : C(I, ℝ)) at hpq
    rw [hpq]
    exact hglobal uv
  refine ⟨p, hpdeg, le_antisymm ?_ ?_⟩
  · apply le_csInf (by exact ⟨_, 0, by simp, rfl⟩)
    rintro v ⟨u, hu, rfl⟩
    exact hmin u hu
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro v ⟨u, _, rfl⟩
      exact (weightedPolynomial_error_bound M ε hM u).1
    · exact ⟨p, hpdeg, rfl⟩


-- @node: continuousResidual_strictImprovement
/-- A continuous perturbation with the residual's strict sign at every active extremum decreases its norm. This is the compact active-set perturbation argument in roadmap (3), allowing the weighted direction q/(1+z). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hrs,hg,hq,hE,hsign), the [stated conclusion](goal) holds. -/
theorem continuousResidual_strictImprovement
    {g : ℝ → ℝ} {r s : ℝ} (hrs : r ≤ s)
    (hg : ContinuousOn g (Set.Icc r s)) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Set.Icc r s))
    (hE : 0 < intervalSupNorm g r s)
    (hsign : ∀ x ∈ Set.Icc r s,
      |g x| = intervalSupNorm g r s → 0 < g x * q x) :
    ∃ t : ℝ, 0 < t ∧
      intervalSupNorm (fun x ↦ g x - t * q x) r s <
        intervalSupNorm g r s := by
  let E := intervalSupNorm g r s
  let p : ℝ → ℝ := fun x ↦ g x * q x
  have hIcc_ne : (Set.Icc r s).Nonempty := ⟨r, le_rfl, hrs⟩
  have hp : ContinuousOn p (Set.Icc r s) := hg.mul hq
  have habs_le : ∀ x ∈ Set.Icc r s, |g x| ≤ E := by
    simpa [E] using
      (intervalSupNorm_le_iff hg hrs).mp
        (le_refl (intervalSupNorm g r s))
  obtain ⟨xE, hxE, hEmax, -⟩ :=
    isCompact_Icc.exists_sSup_image_eq_and_ge hIcc_ne hg.abs
  have hxE_eq : |g xE| = E := by
    simpa [E, intervalSupNorm] using hEmax.symm
  have hp_xE : 0 < p xE := by
    exact hsign xE hxE (by simpa [E] using hxE_eq)
  let B : Set ℝ := {x | x ∈ Set.Icc r s ∧ p x ≤ 0}
  have hBcompact : IsCompact B := by
    apply IsCompact.of_isClosed_subset isCompact_Icc
        (isClosed_Icc.isClosed_le hp continuousOn_const)
    exact fun _ hx ↦ hx.1
  have hc : ∃ c : ℝ, c < E ∧
      ∀ x ∈ Set.Icc r s, c ≤ |g x| → 0 < p x := by
    by_cases hBne : B.Nonempty
    · obtain ⟨xb, hxb, hxb_max⟩ :=
        hBcompact.exists_isMaxOn hBne (hg.abs.mono (fun _ hx ↦ hx.1))
      have hxb_lt : |g xb| < E := by
        apply lt_of_le_of_ne (habs_le xb hxb.1)
        intro heq
        have : 0 < p xb := hsign xb hxb.1 (by simpa [E] using heq)
        linarith [hxb.2]
      refine ⟨(|g xb| + E) / 2, by linarith, ?_⟩
      intro x hx hcx
      by_contra hnot
      have hxB : x ∈ B := ⟨hx, le_of_not_gt hnot⟩
      have hmax_le : |g x| ≤ |g xb| := hxb_max hxB
      linarith
    · refine ⟨E / 2, by linarith [hE], ?_⟩
      intro x hx _
      by_contra hnot
      exact hBne ⟨x, hx, le_of_not_gt hnot⟩
  obtain ⟨c, hcE, hc⟩ := hc
  let A : Set ℝ := {x | x ∈ Set.Icc r s ∧ c ≤ |g x|}
  have hAcompact : IsCompact A := by
    apply IsCompact.of_isClosed_subset isCompact_Icc
        (isClosed_Icc.isClosed_le continuousOn_const hg.abs)
    exact fun _ hx ↦ hx.1
  have hxEA : xE ∈ A := ⟨hxE, by linarith [hxE_eq]⟩
  obtain ⟨xm, hxm, hxm_min⟩ :=
    hAcompact.exists_isMinOn ⟨xE, hxEA⟩ (hp.mono (fun _ hx ↦ hx.1))
  let m := p xm
  have hm : 0 < m := by
    exact hc xm hxm.1 hxm.2
  obtain ⟨xM, hxM, hxM_max⟩ :=
    isCompact_Icc.exists_isMaxOn hIcc_ne hq.abs
  let M := |q xM|
  have hq_le : ∀ x ∈ Set.Icc r s, |q x| ≤ M := by
    intro x hx
    exact hxM_max hx
  have hM : 0 < M := by
    have hqE_ne : q xE ≠ 0 := by
      intro hzero
      simp [p, hzero] at hp_xE
    have hqE_pos : 0 < |q xE| := abs_pos.mpr hqE_ne
    exact lt_of_lt_of_le hqE_pos (hq_le xE hxE)
  let t := min (m / M ^ 2) ((E - c) / (2 * M))
  have ht₁ : 0 < m / M ^ 2 := div_pos hm (sq_pos_of_pos hM)
  have ht₂ : 0 < (E - c) / (2 * M) :=
    div_pos (sub_pos.mpr hcE) (mul_pos (by norm_num) hM)
  have ht : 0 < t := lt_min ht₁ ht₂
  refine ⟨t, ht, ?_⟩
  unfold intervalSupNorm
  apply (isCompact_Icc.sSup_lt_iff_of_continuous hIcc_ne
    ((hg.sub (hq.const_mul t)).abs) E).2
  intro x hx
  have hgx := habs_le x hx
  have hqx := hq_le x hx
  by_cases hhigh : c ≤ |g x|
  · have hxA : x ∈ A := ⟨hx, hhigh⟩
    have hmp : m ≤ p x := hxm_min hxA
    have htM : t ≤ m / M ^ 2 := min_le_left _ _
    have hq_sq : q x ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (q x)) (abs_nonneg M)).2
          (by simpa [abs_of_pos hM] using hqx)
    have hmove : t * q x ^ 2 < 2 * p x := by
      have hM_sq : 0 < M ^ 2 := sq_pos_of_pos hM
      have ht_bound : t * M ^ 2 ≤ m := by
        apply (le_div_iff₀ hM_sq).mp
        simpa [mul_comm] using htM
      nlinarith [mul_le_mul_of_nonneg_left hq_sq (le_of_lt ht)]
    have hsquares : (g x - t * q x) ^ 2 < E ^ 2 := by
      calc
        (g x - t * q x) ^ 2 = g x ^ 2 - 2 * t * p x + t ^ 2 * q x ^ 2 := by
          simp only [p]
          ring
        _ < g x ^ 2 := by nlinarith
        _ ≤ E ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (g x)) (le_of_lt hE)).2 hgx
    rw [← sq_abs] at hsquares
    exact (sq_lt_sq₀ (abs_nonneg _) (le_of_lt hE)).mp hsquares
  · have htM : t ≤ (E - c) / (2 * M) := min_le_right _ _
    have ht_bound : t * M ≤ (E - c) / 2 := by
      have htwoM : 0 < 2 * M := mul_pos (by norm_num) hM
      have := (le_div_iff₀ htwoM).mp htM
      nlinarith
    calc
      |g x - t * q x| ≤ |g x| + |t * q x| := abs_sub _ _
      _ = |g x| + t * |q x| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ |g x| + t * M := by gcongr
      _ < E := by
        have : |g x| < c := lt_of_not_ge hhigh
        nlinarith [sub_pos.mpr hcE]


/-- A best weighted residual has K+2 alternating active points. A missing alternation would give a sign polynomial whose weighted perturbation strictly improves the attained minimum, contradicting optimality as in roadmap (3). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hM,hMhi,hε,hεhi), the [stated conclusion](goal) holds. -/
theorem weightedApproxError_alternating_witness {K : ℕ} (hK : 2 ≤ K)
    {M ε : ℝ} (hM : 2 ≤ M) (hMhi : M ≤ (K : ℝ) ^ 2)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) :
    ∃ (p : Polynomial ℝ) (nodes : Fin (K + 2) → ℝ) (orientation : ℝ),
      p.natDegree ≤ K ∧ StrictMono nodes ∧
      (∀ i, nodes i ∈ Set.Icc 0 M) ∧ (orientation = 1 ∨ orientation = -1) ∧
      ∀ i, (phiEpsFormula ε (nodes i) - p.eval (nodes i)) / (1 + nodes i) =
        orientation * (-1 : ℝ) ^ (i : ℕ) * weightedApproxError K M ε := by
  obtain ⟨p, hp, hbest⟩ := weightedApproxError_attained K (M := M) (by linarith) ε
  let g := fun z : ℝ => (phiEpsFormula ε z - p.eval z) / (1 + z)
  have hg : ContinuousOn g (Set.Icc 0 M) := by
    dsimp [g]
    unfold phiEpsFormula
    apply ContinuousOn.div
    · apply ContinuousOn.sub
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro z hz; linarith [hz.1]
      · fun_prop
    · fun_prop
    · intro z hz; linarith [hz.1]
  have hnorm : intervalSupNorm g 0 M = weightedApproxError K M ε := by
    unfold intervalSupNorm
    rw [← hbest]
    congr 1
    apply Set.image_congr
    intro z hz
    change |g z| = |phiEpsFormula ε z - p.eval z| / (1 + z)
    simp only [g, abs_div, abs_of_pos (show 0 < 1 + z from by linarith [hz.1])]
  obtain ⟨c, hc, hlower⟩ := packetWeightedApproxError_lower
  have hpos : 0 < intervalSupNorm g 0 M := by
    rw [hnorm]
    exact lt_of_lt_of_le (by
      have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
      exact div_pos (mul_pos hc (Real.sqrt_pos.2 (by linarith))) hKR)
      (hlower K M ε hK hM hMhi hε hεhi)
  have halt : ∃ nodes orientation, IsAlternatingExtrema g 0 M K nodes orientation := by
    by_contra hno
    obtain ⟨q, hq, hsign⟩ := exists_signPolynomial_of_no_alternatingExtrema
      (by linarith : (0 : ℝ) < M) hg K hpos hno
    let v := fun z : ℝ => q.eval z / (1 + z)
    have hv : ContinuousOn v (Set.Icc 0 M) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro z hz; linarith [hz.1]
    have hsignv : ∀ z ∈ Set.Icc 0 M, |g z| = intervalSupNorm g 0 M →
        0 < g z * v z := by
      intro z hz he
      dsimp [v]
      rw [← mul_div_assoc]
      exact div_pos (hsign z hz he) (by linarith [hz.1])
    obtain ⟨t, _, himprove⟩ := continuousResidual_strictImprovement
      (by linarith : (0 : ℝ) ≤ M) hg v hv hpos hsignv
    let r := p + Polynomial.C t * q
    have hr : r.natDegree ≤ K :=
      (Polynomial.natDegree_add_le _ _).trans (max_le hp
        (Polynomial.natDegree_mul_le.trans (by simpa using hq)))
    have herror : sSup ((fun z : ℝ => |phiEpsFormula ε z - r.eval z| / (1 + z)) ''
        Set.Icc 0 M) = intervalSupNorm (fun z => g z - t * v z) 0 M := by
      unfold intervalSupNorm
      congr 1
      apply Set.image_congr
      intro z hz
      have hzpos : 0 < 1 + z := by linarith [hz.1]
      have he : g z - t * v z = (phiEpsFormula ε z - r.eval z) / (1 + z) := by
        simp only [g, v, r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        ring
      change _ = |g z - t * v z|
      rw [he, abs_div, abs_of_pos hzpos]
    have hb : BddBelow {e : ℝ | ∃ q : Polynomial ℝ, q.natDegree ≤ K ∧
        e = sSup ((fun z : ℝ => |phiEpsFormula ε z - q.eval z| / (1 + z)) '' Set.Icc 0 M)} := by
      refine ⟨0, ?_⟩
      rintro e ⟨q, _, rfl⟩
      exact (weightedPolynomial_error_bound M ε (by linarith) q).1
    have hle := csInf_le hb ⟨r, hr, rfl⟩
    change weightedApproxError K M ε ≤ _ at hle
    rw [herror, ← hnorm] at hle
    exact (not_lt_of_ge hle) himprove
  obtain ⟨nodes, o, hmono, hmem, ho, he⟩ := halt
  exact ⟨p, nodes, o, hp, hmono, hmem, ho, fun i => by
    change g (nodes i) = _
    rw [he i, hnorm]⟩

end CausalSmith.Stat.OptvalueVanishingoverlapRate
