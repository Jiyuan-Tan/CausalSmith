module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.MembershipAmplitude

/-! # Hölder control of the tiled lower-bound perturbation

The sinusoidal tile bump vanishes at every cell boundary.  This makes the
signed tiling globally Lipschitz despite arbitrary sign changes between cells;
combining that estimate with its uniform height bound gives the required
one-eighth Hölder radius.
-/

public section

open Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Every point of the covariate interval belongs to one tiled cell.  Under [the displayed assumptions and inputs](hyp:K,hK,x,hx), [the stated conclusion holds](goal). -/
lemma exists_tiled_cell_of_mem {K : ℕ} (hK : 0 < K)
    (x : ℝ) (hx : x ∈ covariateSpace) : ∃ i : Fin K, x ∈ cell K i := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  change 0 ≤ x ∧ x ≤ 1 at hx
  by_cases hx1 : x = 1
  · refine ⟨⟨K - 1, by omega⟩, ?_⟩
    have hlast : K - 1 + 1 = K := by omega
    simp only [cell, hlast, if_true, Set.mem_Icc, hx1]
    exact ⟨(div_le_one hKr).2 (by exact_mod_cast (show K - 1 ≤ K by omega)), le_rfl⟩
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hfloor : ⌊x * K⌋₊ < K := by
      apply (Nat.floor_lt (mul_nonneg hx.1 hKr.le)).2
      nlinarith
    refine ⟨⟨⌊x * K⌋₊, hfloor⟩, ?_⟩
    have hlo : (⌊x * K⌋₊ : ℝ) / K ≤ x := by
      apply (div_le_iff₀ hKr).2
      exact Nat.floor_le (mul_nonneg hx.1 hKr.le)
    have hhi : x < ((⌊x * K⌋₊ : ℝ) + 1) / K := by
      apply (lt_div_iff₀ hKr).2
      exact Nat.lt_floor_add_one (x * K)
    unfold cell
    split_ifs
    · exact ⟨hlo, hx.2⟩
    · exact ⟨hlo, hhi⟩

/-- On a cell, the tiled perturbation is its unique active summand.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,i,x,hx,hK), [the stated conclusion holds](goal). -/
lemma tiledPerturbation_eq_of_mem_cell (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (i : Fin (lowerCells n)) (x : ℝ)
    (hx : x ∈ cell (lowerCells n) i) (hK : 0 < lowerCells n) :
    tiledPerturbation cStar n sgn x =
      lowerHeight cStar n * sign (sgn i) *
        bump ((lowerCells n : ℝ) * x - i.val) := by
  classical
  unfold tiledPerturbation
  rw [Finset.sum_eq_single i]
  · simp [hx]
  · intro j _ hji
    have hnot : x ∉ cell (lowerCells n) j := by
      intro hxj
      exact hji (cell_mem_unique _ hK j i x hxj hx)
    simp [hnot]
  · simp

/-- Membership in a tile supplies its closed endpoint bounds.  Under [the displayed assumptions and inputs](hyp:K,hK,i,x,hx), [the stated conclusion holds](goal). -/
lemma cell_closed_bounds {K : ℕ} (hK : 0 < K) (i : Fin K) (x : ℝ)
    (hx : x ∈ cell K i) :
    (i.val : ℝ) / K ≤ x ∧ x ≤ ((i.val : ℝ) + 1) / K := by
  unfold cell at hx
  split_ifs at hx with hlast
  · refine ⟨hx.1, ?_⟩
    have hi : (i.val : ℝ) + 1 = K := by exact_mod_cast hlast
    rw [hi]
    rw [div_self (by exact_mod_cast Nat.ne_of_gt hK)]
    exact hx.2
  · exact ⟨hx.1, hx.2.le⟩

/-- The active sinusoid is controlled by distance to either endpoint of its tile.  Under [the displayed assumptions and inputs](hyp:K,hK,i,x,b,hb), [the stated conclusion holds](goal). -/
lemma bump_affine_abs_le_endpoint {K : ℕ} (hK : 0 < K) (i : Fin K) (x b : ℝ)
    (hb : b = (i.val : ℝ) / K ∨ b = ((i.val : ℝ) + 1) / K) :
    |bump ((K : ℝ) * x - i.val)| ≤ 2 * Real.pi * K * |x - b| := by
  have hKb : bump ((K : ℝ) * b - i.val) = 0 := by
    rcases hb with rfl | rfl
    · have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
      unfold bump
      field_simp
      simp
    · have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
      unfold bump
      field_simp
      simp [Real.sin_two_pi]
  have hs := Real.abs_sin_sub_sin_le
    (2 * Real.pi * ((K : ℝ) * x - i.val))
    (2 * Real.pi * ((K : ℝ) * b - i.val))
  calc
    |bump ((K : ℝ) * x - i.val)| =
        |bump ((K : ℝ) * x - i.val) - bump ((K : ℝ) * b - i.val)| := by
          rw [hKb, sub_zero]
    _ = |Real.sin (2 * Real.pi * ((K : ℝ) * x - i.val)) -
        Real.sin (2 * Real.pi * ((K : ℝ) * b - i.val))| := rfl
    _ ≤
        |2 * Real.pi * ((K : ℝ) * x - i.val) -
          2 * Real.pi * ((K : ℝ) * b - i.val)| := hs
    _ = 2 * Real.pi * K * |x - b| := by
      rw [show 2 * Real.pi * ((K : ℝ) * x - i.val) -
          2 * Real.pi * ((K : ℝ) * b - i.val) =
          (2 * Real.pi * K) * (x - b) by ring, abs_mul]
      simp only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * K)]

/-- The signed tiled sine is globally Lipschitz on the covariate interval.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hc,hn,x,y,hx,hy), [the stated conclusion holds](goal). -/
lemma tiledPerturbation_abs_sub_le (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hc : 0 ≤ cStar) (hn : 0 < n)
    (x y : ℝ) (hx : x ∈ covariateSpace) (hy : y ∈ covariateSpace) :
    |tiledPerturbation cStar n sgn x - tiledPerturbation cStar n sgn y| ≤
      lowerHeight cStar n * (2 * Real.pi * lowerCells n) * |x - y| := by
  have hK : 0 < lowerCells n := by
    unfold lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  obtain ⟨i, hxi⟩ := exists_tiled_cell_of_mem hK x hx
  obtain ⟨j, hyj⟩ := exists_tiled_cell_of_mem hK y hy
  rw [tiledPerturbation_eq_of_mem_cell cStar n sgn i x hxi hK,
    tiledPerturbation_eq_of_mem_cell cStar n sgn j y hyj hK]
  have hh : 0 ≤ lowerHeight cStar n := by unfold lowerHeight; positivity
  have hsi (k : Fin (lowerCells n)) : |sign (sgn k)| = 1 := by
    cases sgn k <;> simp [sign]
  by_cases hij : i = j
  · subst j
    rw [← mul_sub, abs_mul, abs_mul, hsi, mul_one]
    have hs := Real.abs_sin_sub_sin_le
      (2 * Real.pi * ((lowerCells n : ℝ) * x - i.val))
      (2 * Real.pi * ((lowerCells n : ℝ) * y - i.val))
    calc
      |lowerHeight cStar n| *
          |bump ((lowerCells n : ℝ) * x - i.val) -
            bump ((lowerCells n : ℝ) * y - i.val)| ≤
          lowerHeight cStar n *
            |2 * Real.pi * ((lowerCells n : ℝ) * x - i.val) -
              2 * Real.pi * ((lowerCells n : ℝ) * y - i.val)| := by
            rw [abs_of_nonneg hh]
            exact mul_le_mul_of_nonneg_left hs hh
      _ = lowerHeight cStar n * (2 * Real.pi * lowerCells n) * |x - y| := by
        rw [show 2 * Real.pi * ((lowerCells n : ℝ) * x - i.val) -
            2 * Real.pi * ((lowerCells n : ℝ) * y - i.val) =
            (2 * Real.pi * lowerCells n) * (x - y) by ring,
          abs_mul]
        simp only [abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ 2 * Real.pi * lowerCells n)]
        ring
  · have hordered (x y : ℝ) (hx : x ∈ covariateSpace) (hy : y ∈ covariateSpace)
        (i j : Fin (lowerCells n)) (hxi : x ∈ cell (lowerCells n) i)
        (hyj : y ∈ cell (lowerCells n) j) (hij : i ≠ j) (hxy : x ≤ y) :
        |lowerHeight cStar n * sign (sgn i) *
            bump ((lowerCells n : ℝ) * x - i.val) -
          lowerHeight cStar n * sign (sgn j) *
            bump ((lowerCells n : ℝ) * y - j.val)| ≤
          lowerHeight cStar n * (2 * Real.pi * lowerCells n) * |x - y| := by
      have hijv : i.val < j.val := by
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hij' | hji
        · exact hij'
        · have hxb := cell_closed_bounds hK i x hxi
          have hyb := cell_closed_bounds hK j y hyj
          have hstep : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hji
          have hKr : (0 : ℝ) < lowerCells n := by exact_mod_cast hK
          have : y ≤ x := by
            calc
              y ≤ ((j.val : ℝ) + 1) / lowerCells n := hyb.2
              _ ≤ (i.val : ℝ) / lowerCells n :=
                (div_le_div_iff_of_pos_right hKr).2 hstep
              _ ≤ x := hxb.1
          have hxy' : x = y := le_antisymm hxy this
          subst y
          exact (hij (cell_mem_unique _ hK i j x hxi hyj)).elim
      let bi : ℝ := ((i.val : ℝ) + 1) / lowerCells n
      let aj : ℝ := (j.val : ℝ) / lowerCells n
      have hxb := cell_closed_bounds hK i x hxi
      have hyb := cell_closed_bounds hK j y hyj
      have hstep : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hijv
      have hKr : (0 : ℝ) < lowerCells n := by exact_mod_cast hK
      have hbaj : bi ≤ aj := (div_le_div_iff_of_pos_right hKr).2 hstep
      have hchain : x ≤ bi ∧ bi ≤ aj ∧ aj ≤ y := ⟨hxb.2, hbaj, hyb.1⟩
      have hbi := bump_affine_abs_le_endpoint hK i x bi (Or.inr rfl)
      have haj := bump_affine_abs_le_endpoint hK j y aj (Or.inl rfl)
      calc
        |lowerHeight cStar n * sign (sgn i) *
            bump ((lowerCells n : ℝ) * x - i.val) -
          lowerHeight cStar n * sign (sgn j) *
            bump ((lowerCells n : ℝ) * y - j.val)| ≤
            |lowerHeight cStar n * sign (sgn i) *
              bump ((lowerCells n : ℝ) * x - i.val)| +
            |lowerHeight cStar n * sign (sgn j) *
              bump ((lowerCells n : ℝ) * y - j.val)| := abs_sub _ _
        _ = lowerHeight cStar n *
            (|bump ((lowerCells n : ℝ) * x - i.val)| +
             |bump ((lowerCells n : ℝ) * y - j.val)|) := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul, hsi, hsi,
                abs_of_nonneg hh]
              ring
        _ ≤ lowerHeight cStar n *
            ((2 * Real.pi * lowerCells n) * |x - bi| +
             (2 * Real.pi * lowerCells n) * |y - aj|) := by
              gcongr
        _ ≤ lowerHeight cStar n * (2 * Real.pi * lowerCells n) * |x - y| := by
              rw [abs_of_nonpos (sub_nonpos.mpr hchain.1),
                abs_of_nonneg (sub_nonneg.mpr hchain.2.2),
                abs_of_nonpos (sub_nonpos.mpr hxy)]
              have hcoef : 0 ≤ 2 * Real.pi * (lowerCells n : ℝ) := by positivity
              have hdist : (bi - x) + (y - aj) ≤ y - x := by linarith [hchain.2.1]
              calc
                lowerHeight cStar n *
                    (2 * Real.pi * lowerCells n * -(x - bi) +
                     2 * Real.pi * lowerCells n * (y - aj)) =
                    lowerHeight cStar n *
                      ((2 * Real.pi * lowerCells n) * ((bi - x) + (y - aj))) := by ring
                _ ≤ lowerHeight cStar n *
                    ((2 * Real.pi * lowerCells n) * (y - x)) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left hdist hcoef) hh
                _ = lowerHeight cStar n * (2 * Real.pi * lowerCells n) * (y - x) := by ring
                _ = lowerHeight cStar n * (2 * Real.pi * lowerCells n) * -(x - y) := by ring
    rcases le_total x y with hxy | hyx
    · exact hordered x y hx hy i j hxi hyj hij hxy
    · rw [abs_sub_comm, abs_sub_comm x y]
      exact hordered y x hy hx j i hyj hxi (Ne.symm hij) hyx

/-- The scale `K⁻¹/⁸` converts the tiled Lipschitz estimate into a uniform
one-eighth Hölder modulus.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hc,hn,x,y,hx,hy), [the stated conclusion holds](goal). -/
lemma tiledPerturbation_holder_modulus (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hc : 0 ≤ cStar) (hn : 0 < n)
    (x y : ℝ) (hx : x ∈ covariateSpace) (hy : y ∈ covariateSpace) :
    |tiledPerturbation cStar n sgn x - tiledPerturbation cStar n sgn y| ≤
      cStar * (1 + 2 * Real.pi) * |x - y| ^ holderExponent := by
  let K : ℝ := lowerCells n
  let d : ℝ := |x - y|
  have hKnat : 0 < lowerCells n := by
    unfold lowerCells
    exact Nat.ceil_pos.mpr (by positivity)
  have hK : 0 < K := by simpa [K] using (Nat.cast_pos.mpr hKnat : (0 : ℝ) < lowerCells n)
  have hd : 0 ≤ d := abs_nonneg _
  have hh : lowerHeight cStar n = cStar * K ^ (-(1 / 8 : ℝ)) := rfl
  have hcancel : K ^ (-(1 / 8 : ℝ)) * (K * d) ^ (1 / 8 : ℝ) =
      d ^ (1 / 8 : ℝ) := by
    rw [Real.mul_rpow hK.le hd, ← mul_assoc, ← Real.rpow_add hK]
    norm_num
  by_cases hd0 : d = 0
  · have hxy : x = y := sub_eq_zero.mp (abs_eq_zero.mp (by simpa [d] using hd0))
    subst y
    simp [holderExponent]
  by_cases hsmall : K * d ≤ 1
  · have hqnonneg : 0 ≤ K * d := mul_nonneg hK.le hd
    have hqpow : K * d ≤ (K * d) ^ (1 / 8 : ℝ) :=
      Real.self_le_rpow_of_le_one hqnonneg hsmall (by norm_num)
    have hlip := tiledPerturbation_abs_sub_le cStar n sgn hc hn x y hx hy
    calc
      |tiledPerturbation cStar n sgn x - tiledPerturbation cStar n sgn y| ≤
          (cStar * K ^ (-(1 / 8 : ℝ))) * (2 * Real.pi * K) * d := by
            simpa [hh, K, d, mul_assoc] using hlip
      _ = cStar * (2 * Real.pi) *
          (K ^ (-(1 / 8 : ℝ)) * (K * d)) := by ring
      _ ≤ cStar * (2 * Real.pi) *
          (K ^ (-(1 / 8 : ℝ)) * (K * d) ^ (1 / 8 : ℝ)) := by
            gcongr
      _ = cStar * (2 * Real.pi) * d ^ (1 / 8 : ℝ) := by rw [hcancel]
      _ ≤ cStar * (1 + 2 * Real.pi) * d ^ holderExponent := by
            unfold holderExponent
            have hz : 0 ≤ cStar * d ^ (1 / 8 : ℝ) := by positivity
            have hcst : 2 * Real.pi ≤ 1 + 2 * Real.pi := by linarith
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hcst hz
  · have hq : 1 ≤ K * d := le_of_not_ge hsmall
    have hqpow : 1 ≤ (K * d) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow hq (by norm_num)
    have hheight : lowerHeight cStar n ≤ cStar * d ^ (1 / 8 : ℝ) := by
      rw [hh, ← hcancel]
      have hscale : 0 ≤ cStar * K ^ (-(1 / 8 : ℝ)) := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hqpow hscale
    have hsupx := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc
    have hsupy := tiledPerturbation_abs_le_lowerHeight cStar n sgn y hc
    calc
      |tiledPerturbation cStar n sgn x - tiledPerturbation cStar n sgn y| ≤
          |tiledPerturbation cStar n sgn x| +
            |tiledPerturbation cStar n sgn y| := abs_sub _ _
      _ ≤ 2 * lowerHeight cStar n := by linarith
      _ ≤ 2 * (cStar * d ^ (1 / 8 : ℝ)) := by linarith
      _ ≤ cStar * (1 + 2 * Real.pi) * d ^ holderExponent := by
            unfold holderExponent
            have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
            have hp : 0 < d ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hdpos _
            have hz : 0 ≤ cStar * d ^ (1 / 8 : ℝ) := mul_nonneg hc hp.le
            have hcst : (2 : ℝ) ≤ 1 + 2 * Real.pi := by linarith [Real.two_le_pi]
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hcst hz

/-- The tiled perturbation is continuous on the covariate interval.  Under [the displayed assumptions and inputs](hyp:cStar,n,sgn,hc,hn), [the stated conclusion holds](goal). -/
lemma tiledPerturbation_continuousOn (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hc : 0 ≤ cStar) (hn : 0 < n) :
    ContinuousOn (tiledPerturbation cStar n sgn) covariateSpace := by
  let C : ℝ := lowerHeight cStar n * (2 * Real.pi * lowerCells n)
  have hLip : LipschitzOnWith (Real.toNNReal C)
      (tiledPerturbation cStar n sgn) covariateSpace :=
    LipschitzOnWith.of_dist_le' (f := tiledPerturbation cStar n sgn)
      (s := covariateSpace) fun x hx y hy => by
      simpa [C, Real.dist_eq] using
        tiledPerturbation_abs_sub_le cStar n sgn hc hn x y hx hy
  exact hLip.continuousOn

/-- A bounded scalar function with the target modulus belongs to the paper's
one-dimensional standard Hölder ball.  Under [the displayed assumptions and inputs](hyp:f,L,hL,hcont,hbound,hmod), [the stated conclusion holds](goal). -/
lemma holderOn_of_bound_modulus (f : ℝ → ℝ) (L : ℝ) (hL : 1 < L)
    (hcont : ContinuousOn f covariateSpace)
    (hbound : ∀ x ∈ covariateSpace, |f x| ≤ L)
    (hmod : ∀ x ∈ covariateSpace, ∀ y ∈ covariateSpace,
      |f x - f y| ≤ L * |x - y| ^ holderExponent) :
    HolderOn f L := by
  have hceil : ⌈holderExponent⌉₊ = 1 := by
    apply (Nat.ceil_eq_iff (by decide)).2
    norm_num [holderExponent]
  refine ⟨hL, ?_⟩
  unfold Causalean.Stat.Nonparametric.HolderBallStd
  rw [hceil]
  refine ⟨?_, ?_, ?_⟩
  · change ContDiffOn ℝ 0 (fun x : Fin 1 → ℝ => f (x 0)) {x | x 0 ∈ covariateSpace}
    rw [contDiffOn_zero]
    exact hcont.comp (continuous_apply 0).continuousOn (fun _ hx => hx)
  · intro j hj x hx
    have hj0 : j = 0 := by omega
    subst j
    change ‖(continuousMultilinearCurryFin0 ℝ (Fin 1 → ℝ) ℝ).symm (f (x 0))‖ ≤ L
    rw [LinearIsometryEquiv.norm_map]
    simpa [Real.norm_eq_abs] using hbound (x 0) hx
  · intro x hx y hy
    simp only [Nat.sub_self, Nat.cast_zero, sub_zero]
    change ‖(continuousMultilinearCurryFin0 ℝ (Fin 1 → ℝ) ℝ).symm (f (x 0)) -
      (continuousMultilinearCurryFin0 ℝ (Fin 1 → ℝ) ℝ).symm (f (y 0))‖ ≤
      L * ‖x - y‖ ^ holderExponent
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    have hxy : (x - y : Fin 1 → ℝ) = fun _ => x 0 - y 0 := by
      ext i
      fin_cases i
      rfl
    simpa [hxy, pi_norm_const, Real.norm_eq_abs] using hmod (x 0) hx (y 0) hy

/-- Adding a constant preserves the tiled Hölder modulus; the displayed
supremum condition supplies the radius bound.  Under [the displayed assumptions and inputs](hyp:b,cStar,L,n,sgn,hc,hcap,hbound,hn,hL), [the stated conclusion holds](goal). -/
lemma const_add_tiledPerturbation_holderOn (b cStar L : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hc : 0 ≤ cStar)
    (hcap : cStar ≤ (L - 1) / (1 + 2 * Real.pi))
    (hbound : |b| + cStar ≤ L) (hn : threshold ≤ n) (hL : 1 < L) :
    HolderOn (fun x => b + tiledPerturbation cStar n sgn x) L := by
  have hnpos : 0 < n := by have : 256 ≤ n := hn; omega
  have hden : 0 < 1 + 2 * Real.pi := by positivity
  have hcoef : cStar * (1 + 2 * Real.pi) ≤ L - 1 :=
    (le_div_iff₀ hden).mp hcap
  apply holderOn_of_bound_modulus _ L hL
  · exact continuousOn_const.add
      (tiledPerturbation_continuousOn cStar n sgn hc hnpos)
  · intro x hx
    calc
      |b + tiledPerturbation cStar n sgn x| ≤
          |b| + |tiledPerturbation cStar n sgn x| := abs_add_le _ _
      _ ≤ |b| + cStar := by
        gcongr
        exact (tiledPerturbation_abs_le_lowerHeight cStar n sgn x hc).trans
          (lowerHeight_le_amplitude cStar n hc hn)
      _ ≤ L := hbound
  · intro x hx y hy
    simpa only [add_sub_add_left_eq_sub] using
      (tiledPerturbation_holder_modulus cStar n sgn hc hnpos x y hx hy).trans
        (mul_le_mul_of_nonneg_right (hcoef.trans (by linarith))
          (Real.rpow_nonneg (abs_nonneg _) _))

/-- Constant functions with value in the radius belong to the Hölder ball.  Under [the displayed assumptions and inputs](hyp:b,L,hL,hb), [the stated conclusion holds](goal). -/
lemma const_holderOn (b L : ℝ) (hL : 1 < L) (hb : |b| ≤ L) :
    HolderOn (fun _ => b) L := by
  apply holderOn_of_bound_modulus _ L hL
  · exact continuousOn_const
  · exact fun _ _ => hb
  · intro x hx y hy
    simp only [sub_self, abs_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (abs_nonneg _) _)

/-- The perturbed target density has radius `L`.  Under [the displayed assumptions and inputs](hyp:cStar,L,n,sgn,hc,hcap,hn,hL), [the stated conclusion holds](goal). -/
lemma one_add_tiledPerturbation_holderOn (cStar L : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hc : 0 ≤ cStar)
    (hcap : cStar ≤ (L - 1) / (1 + 2 * Real.pi))
    (hn : threshold ≤ n) (hL : 1 < L) :
    HolderOn (fun x => 1 + tiledPerturbation cStar n sgn x) L := by
  apply const_add_tiledPerturbation_holderOn 1 cStar L n sgn hc hcap _ hn hL
  have hden : 1 ≤ 1 + 2 * Real.pi := by linarith [Real.pi_pos]
  have hc1 : cStar ≤ L - 1 :=
    hcap.trans (div_le_self (by linarith) hden)
  simpa [add_comm] using (add_le_add_left hc1 1)

/-- The perturbed assignment propensity has radius `L`.  Under [the displayed assumptions and inputs](hyp:cStar,L,n,sgn,hc,hcap,hn,hL), [the stated conclusion holds](goal). -/
lemma half_add_tiledPerturbation_holderOn (cStar L : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hc : 0 ≤ cStar)
    (hcap : cStar ≤ (L - 1) / (1 + 2 * Real.pi))
    (hn : threshold ≤ n) (hL : 1 < L) :
    HolderOn (fun x => 1 / 2 + tiledPerturbation cStar n sgn x) L := by
  apply const_add_tiledPerturbation_holderOn (1 / 2) cStar L n sgn hc hcap _ hn hL
  have hden : 1 ≤ 1 + 2 * Real.pi := by linarith [Real.pi_pos]
  have hc1 : cStar ≤ L - 1 :=
    hcap.trans (div_le_self (by linarith) hden)
  norm_num
  linarith

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
