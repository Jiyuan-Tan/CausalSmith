module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.EventCoupling
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Geometry
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Histogram
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Information
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.OracleSpacing
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Measure and hypercube bridges for the arbitrary-pairing converse -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory
open Causalean.Stat.Nonparametric.HistogramRegression

lemma singleton_bump_matching_cost {d N : ℕ}
    (x : MainCovariates N d) (M : Match N)
    (Q B : Set (XSpace d)) (ψ : XSpace d → ℝ)
    (hsupport : ∀ y, y ∉ Q → ψ y = 0)
    (hcore : ∀ y, y ∈ B → ψ y = 1)
    (i : Fin N) (hi : x i ∈ B)
    (hunique : ∀ k : Fin N, x k ∈ Q → k = i) :
    1 ≤ (1 / 2 : ℝ) * ∑ k : Fin N, (ψ (x k) - ψ (x (M.val k))) ^ 2 := by
  classical
  let p : Fin N := M.val i
  have hip : i ≠ p := fun h => M.property.2 i h.symm
  have hpQ : x p ∉ Q := by
    intro hp
    exact hip (hunique p hp).symm
  have hψi : ψ (x i) = 1 := hcore (x i) hi
  have hψp : ψ (x p) = 0 := hsupport (x p) hpQ
  have htwo : (2 : ℝ) ≤ ∑ k : Fin N, (ψ (x k) - ψ (x (M.val k))) ^ 2 := by
    let f : Fin N → ℝ := fun k => (ψ (x k) - ψ (x (M.val k))) ^ 2
    have hle : ∑ k ∈ ({i, p} : Finset (Fin N)), f k ≤ ∑ k ∈ Finset.univ, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => sq_nonneg _)
    have hpair : ∑ k ∈ ({i, p} : Finset (Fin N)), f k = 2 := by
      rw [Finset.sum_pair hip]
      dsimp [f, p]
      rw [M.property.1 i, hψi, hψp]
      norm_num
    simpa [hpair, f] using hle
  linarith

lemma converse_localSign_not (b : Bool) : localSign (!b) = -localSign b := by
  cases b <;> simp [localSign]

lemma flipCoordinate_involution {K : ℕ} (θ : Fin K → Bool) (j : Fin K) :
    flipCoordinate (flipCoordinate θ j) j = θ := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [flipCoordinate]
  · simp [flipCoordinate, hkj]

/-- Flipping one coordinate permutes the Boolean hypercube, so vertex sums
are invariant under that flip. -/
lemma sum_flipCoordinate {K : ℕ} (r : (Fin K → Bool) → ℝ) (j : Fin K) :
    (∑ θ : Fin K → Bool, r (flipCoordinate θ j)) = ∑ θ, r θ := by
  let e : (Fin K → Bool) ≃ (Fin K → Bool) :=
    { toFun := fun θ => flipCoordinate θ j
      invFun := fun θ => flipCoordinate θ j
      left_inv := fun θ => flipCoordinate_involution θ j
      right_inv := fun θ => flipCoordinate_involution θ j }
  exact Equiv.sum_comp e r

/-- Finite Assouad averaging: if every bit-flip edge carries the indicated
two-endpoint cost, some vertex carries the averaged total edge cost. -/
-- keep: reusable finite Assouad averaging lemma independent of this endpoint
lemma exists_vertex_large_of_flip_edges {K : ℕ}
    (r : (Fin K → Bool) → ℝ) (a : Fin K → ℝ)
    (hedge : ∀ θ j, a j ≤ r θ + r (flipCoordinate θ j)) :
    ∃ θ, (∑ j, a j) ≤ 2 * (K : ℝ) * r θ := by
  by_contra h
  push_neg at h
  have hsumlt : ∑ θ : Fin K → Bool, 2 * (K : ℝ) * r θ <
      ∑ θ : Fin K → Bool, ∑ j, a j :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun θ _ => h θ
  have hsumle : (∑ θ : Fin K → Bool, ∑ j, a j) ≤
      ∑ θ : Fin K → Bool, ∑ j, (r θ + r (flipCoordinate θ j)) := by
    exact Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun j _ => hedge θ j
  have hconst (c : ℝ) : (∑ _j : Fin K, c) = (K : ℝ) * c := by
    simp [Fintype.card_fin]
  have hcomm : (∑ θ : Fin K → Bool, ∑ j : Fin K,
      r (flipCoordinate θ j)) =
      ∑ j : Fin K, ∑ θ : Fin K → Bool, r (flipCoordinate θ j) :=
    Finset.sum_comm
  have hright : (∑ θ : Fin K → Bool, ∑ j, (r θ + r (flipCoordinate θ j))) =
      ∑ θ : Fin K → Bool, 2 * (K : ℝ) * r θ := by
    calc
      (∑ θ : Fin K → Bool, ∑ j, (r θ + r (flipCoordinate θ j))) =
          (∑ θ : Fin K → Bool, ∑ j, r θ) +
            ∑ θ : Fin K → Bool, ∑ j, r (flipCoordinate θ j) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro θ hθ
              exact Finset.sum_add_distrib
      _ = (∑ θ : Fin K → Bool, ∑ j, r θ) +
            ∑ j : Fin K, ∑ θ : Fin K → Bool, r (flipCoordinate θ j) := by
              rw [hcomm]
      _ = (K : ℝ) * (∑ θ : Fin K → Bool, r θ) +
            (K : ℝ) * (∑ θ : Fin K → Bool, r θ) := by
              congr 1
              · calc
                  (∑ θ : Fin K → Bool, ∑ _j : Fin K, r θ) =
                      ∑ θ : Fin K → Bool, (K : ℝ) * r θ := by
                        apply Finset.sum_congr rfl
                        intro θ hθ
                        exact hconst (r θ)
                  _ = (K : ℝ) * ∑ θ : Fin K → Bool, r θ := by
                        rw [Finset.mul_sum]
              · simp_rw [sum_flipCoordinate r]
                exact hconst (∑ θ : Fin K → Bool, r θ)
      _ = ∑ θ : Fin K → Bool, 2 * (K : ℝ) * r θ := by
              rw [Finset.mul_sum]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro θ hθ
              ring
  rw [hright] at hsumle
  exact (not_lt_of_ge hsumle) hsumlt

lemma flip_bump_sum_sub {d K : ℕ} (θ : Fin K → Bool) (j : Fin K)
    (ψ : Fin K → XSpace d → ℝ) (x : XSpace d) :
    (∑ k, localSign (θ k) * ψ k x) -
        ∑ k, localSign (flipCoordinate θ j k) * ψ k x =
      2 * localSign (θ j) * ψ j x := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ k, (localSign (θ k) * ψ k x -
      localSign (flipCoordinate θ j k) * ψ k x)) =
        ∑ k, if k = j then 2 * localSign (θ j) * ψ j x else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkj : k = j
          · subst k
            rw [show flipCoordinate θ j j = !θ j by simp [flipCoordinate],
              converse_localSign_not]
            simp
            ring
          · simp [flipCoordinate, hkj]
    _ = 2 * localSign (θ j) * ψ j x := by simp

lemma measurable_hypercube_bump_on_cube {d K : ℕ}
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude L β : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (hamp : 0 < amplitude) (hL : 0 < L) (hβ : 0 < β)
    (hholder : ∀ θ, HolderScore (g θ) L β)
    (θ : Fin K → Bool) (j : Fin K) :
    Measurable (fun x : Cube d => ψ j x.val.ofLp) := by
  have hsign : localSign (θ j) ^ 2 = 1 := by
    cases θ j <;> simp [localSign]
  have hdif (x : XSpace d) :
      g θ x - g (flipCoordinate θ j) x =
        2 * amplitude * localSign (θ j) * ψ j x := by
    rw [hg θ x, hg (flipCoordinate θ j) x]
    have hs := flip_bump_sum_sub θ j ψ x
    linear_combination amplitude * hs
  have heq : (fun x : Cube d => ψ j x.val.ofLp) =
      fun x : Cube d => (localSign (θ j) / (2 * amplitude)) *
        (g θ x.val.ofLp - g (flipCoordinate θ j) x.val.ofLp) := by
    funext x
    rw [hdif]
    field_simp
    rw [hsign]
    ring
  rw [heq]
  exact measurable_const.mul
    ((measurable_paperCubeScore (g θ) hL hβ (hholder θ)).sub
      (measurable_paperCubeScore (g (flipCoordinate θ j)) hL hβ
        (hholder (flipCoordinate θ j))))

lemma exists_measurable_bump_core {d : ℕ} {h : ℝ}
    (Q B : Set (XSpace d)) (ψ : XSpace d → ℝ)
    (hQ : IsSideCube h Q) (hBQ : B ⊆ Q)
    (hsupport : ∀ x, x ∉ Q → ψ x = 0)
    (hcore : ∀ x, x ∈ B → ψ x = 1)
    (hψ : Measurable (fun x : Cube d => ψ x.val.ofLp)) :
    ∃ S : Set (XSpace d), MeasurableSet S ∧ B ⊆ S ∧ S ⊆ Q ∧
      (∀ x ∈ S, ψ x = 1) ∧ cubeMeasure d B ≤ cubeMeasure d S := by
  have hcube : MeasurableSet (cube d) := by
    unfold cube
    measurability
  let clamp : XSpace d → Cube d := fun x =>
    ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩
  have hclamp : Measurable clamp := by
    dsimp [clamp]
    fun_prop
  let ψ' : XSpace d → ℝ := fun x => ψ (clamp x).val.ofLp
  have hψ' : Measurable ψ' := hψ.comp hclamp
  have hψ'eq' (x : XSpace d) (hx : x ∈ cube d) : ψ' x = ψ x := by
    dsimp [ψ']
    apply congrArg ψ
    funext i
    simp [clamp, max_eq_right (hx i).1, min_eq_right (hx i).2]
  let S : Set (XSpace d) := {x | x ∈ cube d ∧ ψ' x = 1}
  have hS : MeasurableSet S :=
    hcube.inter (measurableSet_eq_fun hψ' measurable_const)
  have hQcube : Q ⊆ cube d := by
    rcases hQ with ⟨a, ha, rfl⟩
    intro x hx
    exact hx.1
  have hBS : B ⊆ S := by
    intro x hx
    have hxcube : x ∈ cube d := hQcube (hBQ hx)
    refine ⟨hxcube, ?_⟩
    rw [hψ'eq' x hxcube, hcore x hx]
  have hSQ : S ⊆ Q := by
    intro x hx
    by_contra hxQ
    have hzero := hsupport x hxQ
    have : ψ' x = 0 := by rw [hψ'eq' x hx.1, hzero]
    linarith [hx.2]
  refine ⟨S, hS, hBS, hSQ, ?_, measure_mono hBS⟩
  intro x hx
  rw [← hψ'eq' x hx.1]
  exact hx.2

/-- A side cube has at most its Euclidean side-volume under `cubeMeasure`.
The half-open convention in `IsSideCube` is immaterial for this upper bound. -/
lemma sideCube_cubeMeasure_toReal_le {d : ℕ} {h : ℝ} {Q : Set (XSpace d)}
    (hQ : IsSideCube h Q) (hh : 0 ≤ h) :
    (cubeMeasure d Q).toReal ≤ h ^ d := by
  rcases hQ with ⟨a, ha, rfl⟩
  let b : Fin d → ℝ := fun i => a i + h
  have hab : a ≤ b := fun i => by dsimp [b]; linarith
  have hsub : {x : XSpace d | x ∈ cube d ∧ ∀ i, a i ≤ x i ∧
      (x i < a i + h ∨ x i = 1 ∧ a i + h = 1)} ⊆ Set.Icc a b := by
    intro x hx
    constructor
    · exact fun i => (hx.2 i).1
    · intro i
      rcases (hx.2 i).2 with hlt | heq
      · exact hlt.le
      · dsimp [b]
        linarith [heq.1, heq.2]
  have hle : cubeMeasure d
      {x : XSpace d | x ∈ cube d ∧ ∀ i, a i ≤ x i ∧
        (x i < a i + h ∨ x i = 1 ∧ a i + h = 1)} ≤
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) (Set.Icc a b) := by
    unfold cubeMeasure
    exact (Measure.restrict_apply_le _ _).trans (measure_mono hsub)
  have hbox : (Measure.pi fun _ : Fin d => (volume : Measure ℝ))
      (Set.Icc a b) = (ENNReal.ofReal h) ^ d := by
    change volume (Set.Icc a b) = _
    rw [Real.volume_Icc_pi]
    simp [b, Finset.prod_const]
  calc
    (cubeMeasure d
        {x : XSpace d | x ∈ cube d ∧ ∀ i, a i ≤ x i ∧
          (x i < a i + h ∨ x i = 1 ∧ a i + h = 1)}).toReal ≤
        ((Measure.pi fun _ : Fin d => (volume : Measure ℝ))
          (Set.Icc a b)).toReal := ENNReal.toReal_mono (by simp [hbox]) hle
    _ = h ^ d := by simp [hbox, hh]

/-- Rounding a positive target bandwidth down to the reciprocal of the
ceiling mesh loses at most a factor two, also after any nonnegative real
power. -/
lemma reciprocal_mesh_rpow_bounds (b p : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) (hp : 0 ≤ p) :
    (b / 2) ^ p ≤ ((meshCount b : ℝ)⁻¹) ^ p ∧
      ((meshCount b : ℝ)⁻¹) ^ p ≤ b ^ p := by
  obtain ⟨hlo, hhi, _⟩ := mesh_bounds b hb hb1
  exact ⟨Real.rpow_le_rpow (by positivity) hlo hp,
    Real.rpow_le_rpow (by positivity) hhi hp⟩

lemma hypercube_flip_edge_sq {d K : ℕ}
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (θ : Fin K → Bool) (j : Fin K) (a b : XSpace d) :
    2 * amplitude ^ 2 * (ψ j a - ψ j b) ^ 2 ≤
      (g θ a - g θ b) ^ 2 +
        (g (flipCoordinate θ j) a - g (flipCoordinate θ j) b) ^ 2 := by
  have hsa := flip_bump_sum_sub θ j ψ a
  have hsb := flip_bump_sum_sub θ j ψ b
  have hsign : localSign (θ j) ^ 2 = 1 := by
    cases θ j <;> simp [localSign]
  rw [hg θ a, hg θ b, hg (flipCoordinate θ j) a,
    hg (flipCoordinate θ j) b]
  let u := base a + amplitude * ∑ k, localSign (θ k) * ψ k a -
    (base b + amplitude * ∑ k, localSign (θ k) * ψ k b)
  let v := base a + amplitude * ∑ k, localSign (flipCoordinate θ j k) * ψ k a -
    (base b + amplitude * ∑ k, localSign (flipCoordinate θ j k) * ψ k b)
  change 2 * amplitude ^ 2 * (ψ j a - ψ j b) ^ 2 ≤ u ^ 2 + v ^ 2
  have hedge : u - v = 2 * amplitude * localSign (θ j) * (ψ j a - ψ j b) := by
    dsimp [u, v]
    linear_combination amplitude * hsa - amplitude * hsb
  have hdelta : (u - v) ^ 2 = 4 * amplitude ^ 2 * (ψ j a - ψ j b) ^ 2 := by
    rw [hedge]
    nlinarith
  nlinarith [sq_nonneg (u + v)]

lemma hypercube_flip_pairLoss {d N K : ℕ}
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (θ : Fin K → Bool) (j : Fin K) (x : MainCovariates N d) (M : Match N) :
    2 * amplitude ^ 2 * ((1 / 2 : ℝ) *
        ∑ k : Fin N, (ψ j (x k) - ψ j (x (M.val k))) ^ 2) ≤
      pairLoss (g θ) x M + pairLoss (g (flipCoordinate θ j)) x M := by
  have hsum : ∑ k : Fin N,
      2 * amplitude ^ 2 * (ψ j (x k) - ψ j (x (M.val k))) ^ 2 ≤
      ∑ k : Fin N, ((g θ (x k) - g θ (x (M.val k))) ^ 2 +
        (g (flipCoordinate θ j) (x k) -
          g (flipCoordinate θ j) (x (M.val k))) ^ 2) := by
    exact Finset.sum_le_sum fun k _ =>
      hypercube_flip_edge_sq g base amplitude ψ hg θ j (x k) (x (M.val k))
  unfold pairLoss
  rw [Finset.sum_add_distrib] at hsum
  have hsum' : 2 * amplitude ^ 2 *
      (∑ k : Fin N, (ψ j (x k) - ψ j (x (M.val k))) ^ 2) ≤
      (∑ k : Fin N, (g θ (x k) - g θ (x (M.val k))) ^ 2) +
        ∑ k : Fin N, (g (flipCoordinate θ j) (x k) -
          g (flipCoordinate θ j) (x (M.val k))) ^ 2 := by
    rw [Finset.mul_sum]
    exact hsum
  linarith

lemma hypercube_flip_singleton_pairLoss {d N K : ℕ}
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (Q B : Fin K → Set (XSpace d))
    (hsupport : ∀ j y, y ∉ Q j → ψ j y = 0)
    (hcore : ∀ j y, y ∈ B j → ψ j y = 1)
    (θ : Fin K → Bool) (j : Fin K) (x : MainCovariates N d) (M : Match N)
    (i : Fin N) (hi : x i ∈ B j)
    (hunique : ∀ k : Fin N, x k ∈ Q j → k = i) :
    amplitude ^ 2 ≤
      pairLoss (g θ) x M + pairLoss (g (flipCoordinate θ j)) x M := by
  have hsingle := singleton_bump_matching_cost x M (Q j) (B j) (ψ j)
    (hsupport j) (hcore j) i hi hunique
  have hflip := hypercube_flip_pairLoss g base amplitude ψ hg θ j x M
  nlinarith [sq_nonneg amplitude]

lemma hypercube_flip_singleton_design_pairLoss {d m N K : ℕ}
    (D : Design m N d)
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (Q B : Fin K → Set (XSpace d))
    (hsupport : ∀ j y, y ∉ Q j → ψ j y = 0)
    (hcore : ∀ j y, y ∈ B j → ψ j y = 1)
    (θ : Fin K → Bool) (j : Fin K)
    (p₀ p₁ : PilotSample m d) (hp : p₀ = p₁)
    (x : MainCovariates N d) (u : ℝ)
    (i : Fin N) (hi : x i ∈ B j)
    (hunique : ∀ k : Fin N, x k ∈ Q j → k = i) :
    amplitude ^ 2 ≤
      pairLoss (g θ) x (D (p₀, x, u)) +
        pairLoss (g (flipCoordinate θ j)) x (D (p₁, x, u)) := by
  subst p₁
  exact hypercube_flip_singleton_pairLoss g base amplitude ψ hg Q B
    hsupport hcore θ j x (D (p₀, x, u)) i hi hunique


/-- After discarding main-wave outcomes, the latent two-wave law is the
product of the pilot law, the iid covariate law, and the randomizer law. -/
lemma latentTwoWaveLaw_map_designInput (P : Measure (UnitRecord d))
    (hP : IsProbabilityMeasure P)
    (hX : P.map Prod.fst = cubeMeasure d) :
    (latentTwoWaveLaw (m := m) (N := N) P).map designInput =
      (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw) := by
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hP
  letI : IsProbabilityMeasure randomizerLaw := by
    constructor
    norm_num [randomizerLaw, Real.volume_Icc]
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hX]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  let mainCov : MainSample N d → MainCovariates N d :=
    fun us i => (us i).1
  have hmain : Measurable mainCov := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  have hmapmain : (Measure.pi fun _ : Fin N => P).map mainCov =
      Measure.pi fun _ : Fin N => cubeMeasure d := by
    change (Measure.pi fun _ : Fin N => P).map
      (fun us i => Prod.fst (us i)) = _
    rw [Measure.pi_map_pi (fun _ : Fin N => measurable_fst.aemeasurable), hX]
  unfold latentTwoWaveLaw
  change (((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      (Measure.pi fun _ : Fin N => P)).prod randomizerLaw).map
        (MeasurableEquiv.prodAssoc ∘ Prod.map (Prod.map id mainCov) id) = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.measurable
      ((measurable_id.prodMap hmain).prodMap measurable_id)]
  have houter := Measure.map_prod_map
    ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      (Measure.pi fun _ : Fin N => P)) randomizerLaw
    (measurable_id.prodMap hmain) measurable_id
  rw [← houter]
  have hinner := Measure.map_prod_map
    (Measure.pi fun _ : Fin m => pilotUnitLaw P)
    (Measure.pi fun _ : Fin N => P) measurable_id hmain
  rw [← hinner, hmapmain, Measure.map_id, Measure.map_id,
    Measure.prodAssoc_prod]

/-- Risk transported to the common pilot/covariate/randomizer product law.
The measurability premise is separated so callers can discharge it from the
admissible-design condition on the supported design domain. -/
lemma risk_eq_pilot_covariate_integral (P : Measure (UnitRecord d))
    (g : XSpace d → ℝ) (D : Design m N d)
    (hP : IsProbabilityMeasure P)
    (hX : P.map Prod.fst = cubeMeasure d)
    (hF : AEStronglyMeasurable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        pairLoss g z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw))) :
    risk P g D =
      ∫ z, pairLoss g z.2.1 (D z) / (N : ℝ)
        ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
          ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  let target := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hinput : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  unfold risk
  change (∫ w, (fun z : PilotSample m d × MainCovariates N d × ℝ =>
    pairLoss g z.2.1 (D z) / (N : ℝ)) (designInput w)
      ∂latentTwoWaveLaw (m := m) (N := N) P) = _
  have hmap := latentTwoWaveLaw_map_designInput (m := m) (N := N) P hP hX
  rw [← hmap] at hF
  have hi := integral_map hinput.aemeasurable hF
  rw [hmap] at hi
  exact hi.symm

lemma designRiskIntegrand_aestronglyMeasurable {d m N : ℕ}
    {L β cX CX cg Cg : ℝ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ) (D : Design m N d)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg)
    (hX : P.map Prod.fst = cubeMeasure d)
    (hD : MatchingDesignClass D) :
    AEStronglyMeasurable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        pairLoss g z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hmodel.covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hX]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := by
    constructor
    norm_num [randomizerLaw, Real.volume_Icc]
  let target := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hcube : MeasurableSet (cube d) := by unfold cube; measurability
  let clamp : XSpace d → Cube d := fun x =>
    ⟨WithLp.toLp 2 (fun i => min 1 (max 0 (x i))), fun i => ⟨by simp, by simp⟩⟩
  have hclamp : Measurable clamp := by dsimp [clamp]; fun_prop
  let g' : XSpace d → ℝ := fun x => g (clamp x).val.ofLp
  have hg' : Measurable g' :=
    (measurable_paperCubeScore g hmodel.parameters.2.2.2.1
      hmodel.parameters.2.1 hmodel.holder_score).comp hclamp
  have hg'eq (x : XSpace d) (hx : x ∈ cube d) : g' x = g x := by
    dsimp [g']
    apply congrArg g
    funext i
    simp [clamp, max_eq_right (hx i).1, min_eq_right (hx i).2]
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem hcube
  have hmain : ∀ᵐ xs ∂Measure.pi (fun _ : Fin N => cubeMeasure d),
      ∀ i, xs i ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcubeae
  have htargetMain : ∀ᵐ z ∂target, ∀ i, z.2.1 i ∈ cube d := by
    dsimp [target]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with p
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmain] with xs hxs
    filter_upwards [] with u
    exact hxs
  have hinput : Measurable (designInput (m := m) (N := N) (d := d)) := by
    unfold designInput
    fun_prop
  have hmap := latentTwoWaveLaw_map_designInput (m := m) (N := N) P
    hmodel.covariate_density.1 hX
  have hdom := latentTwoWaveLaw_designDomain_ae (m := m) (N := N) P g hmodel
  have htargetDom : ∀ᵐ z ∂target, z ∈ designDomain m N d := by
    change ∀ᵐ z ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
      ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)),
        z ∈ designDomain m N d
    rw [← hmap]
    exact (ae_map_iff hinput.aemeasurable (by unfold designDomain cube; measurability)).2 hdom
  have hDAE : AEMeasurable D target := by
    rw [← Measure.restrict_eq_self_of_ae_mem htargetDom]
    exact aemeasurable_restrict_of_measurable_subtype
      (by unfold designDomain cube; measurability) hD.2.1
  let scores : PilotSample m d × MainCovariates N d × ℝ → Fin N → ℝ :=
    fun z i => g' (z.2.1 i)
  have hscores : Measurable scores := by
    rw [measurable_pi_iff]
    intro i
    exact hg'.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hPairMap : Measurable (fun t : (Fin N → ℝ) × Match N =>
      ((1 / 2 : ℝ) * ∑ i : Fin N, (t.1 i - t.1 (t.2.val i)) ^ 2) / (N : ℝ)) := by
    classical
    have hEval (i : Fin N) :
        Measurable (fun t : (Fin N → ℝ) × Match N => t.1 (t.2.val i)) := by
      have heq : (fun t : (Fin N → ℝ) × Match N => t.1 (t.2.val i)) =
          fun t => ∑ j : Fin N, if t.2.val i = j then t.1 j else 0 := by
        funext t
        simp
      rw [heq]
      apply Finset.measurable_sum
      intro j hj
      exact Measurable.ite
        ((measurableSet_singleton j).preimage
          ((measurable_from_top : Measurable (fun M : Match N => M.val i)).comp
            measurable_snd))
        ((measurable_pi_apply j).comp measurable_fst) measurable_const
    apply Measurable.div_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (((measurable_pi_apply i).comp measurable_fst).sub (hEval i)).pow_const 2
  have hmeas' : AEMeasurable
      (fun z => pairLoss g' z.2.1 (D z) / (N : ℝ)) target := by
    have hp := (hscores.aemeasurable.prodMk hDAE)
    convert hPairMap.comp_aemeasurable hp using 1
    funext z
    simp [scores, pairLoss]
  refine hmeas'.aestronglyMeasurable.congr ?_
  filter_upwards [htargetMain] with z hz
  simp only [pairLoss]
  apply congrArg (fun t : ℝ => t / (N : ℝ))
  apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro i hi
  rw [hg'eq _ (hz i), hg'eq _ (hz ((D z).val i))]

/-- The common-law risk integrand is integrable for every admissible design.
This supplies the boundedness input needed when an edge lower bound is
integrated under a pilot coupling. -/
lemma designRiskIntegrand_integrable {d m N : ℕ}
    {L β cX CX cg Cg : ℝ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ) (D : Design m N d)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg)
    (hX : P.map Prod.fst = cubeMeasure d)
    (hD : MatchingDesignClass D) (hN : 1 ≤ N) :
    Integrable
      (fun z : PilotSample m d × MainCovariates N d × ℝ =>
        pairLoss g z.2.1 (D z) / (N : ℝ))
      ((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
        ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  letI : IsProbabilityMeasure P := hmodel.covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    histogram_pilotUnitLaw_probability P hmodel.covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hX]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := by
    constructor
    norm_num [randomizerLaw, Real.volume_Icc]
  let target := (Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
    ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)
  have hmeas := designRiskIntegrand_aestronglyMeasurable P g D hmodel hX hD
  have hcube : MeasurableSet (cube d) := by unfold cube; measurability
  have hcubeae : ∀ᵐ x ∂cubeMeasure d, x ∈ cube d := by
    unfold cubeMeasure
    exact ae_restrict_mem hcube
  have hmain : ∀ᵐ xs ∂Measure.pi (fun _ : Fin N => cubeMeasure d),
      ∀ i, xs i ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hcubeae
  have htargetMain : ∀ᵐ z ∂target, ∀ i, z.2.1 i ∈ cube d := by
    dsimp [target]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [] with p
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmain] with xs hxs
    filter_upwards [] with u
    exact hxs
  let C : ℝ := L * (d : ℝ) ^ (β / 2)
  let R : ℝ := (1 / 2 : ℝ) * C ^ 2
  refine Integrable.mono' (integrable_const R) hmeas ?_
  filter_upwards [htargetMain] with z hz
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hmodel.parameters.2.2.2.1.le
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hterm (i : Fin N) :
      (g (z.2.1 i) - g (z.2.1 ((D z).val i))) ^ 2 ≤ C ^ 2 := by
    have habs := holder_score_cube_oscillation g hmodel.parameters.2.2.2.1.le
      hmodel.parameters.2.1.le hmodel.holder_score
      (z.2.1 i) (z.2.1 ((D z).val i)) (hz i) (hz ((D z).val i))
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 habs
  have hsum :
      ∑ i : Fin N, (g (z.2.1 i) - g (z.2.1 ((D z).val i))) ^ 2 ≤
        (N : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin N, C ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = (N : ℝ) * C ^ 2 := by simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnonneg : 0 ≤ pairLoss g z.2.1 (D z) / (N : ℝ) := by
    unfold pairLoss
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp [R]
  unfold pairLoss
  apply (div_le_iff₀ hNpos).2
  nlinarith

/-- Risk under a hypercube member, written under the common iid cube law. -/
lemma risk_eq_pilot_cube_integral {d m N : ℕ} {L β cX CX cg Cg : ℝ}
    (P : Measure (UnitRecord d)) (g : XSpace d → ℝ) (D : Design m N d)
    (hmodel : RegularScoreModel P g L β cX CX cg Cg)
    (hX : P.map Prod.fst = cubeMeasure d)
    (hD : MatchingDesignClass D) :
    risk P g D =
      ∫ z, pairLoss g z.2.1 (D z) / (N : ℝ)
        ∂((Measure.pi fun _ : Fin m => pilotUnitLaw P).prod
          ((Measure.pi fun _ : Fin N => cubeMeasure d).prod randomizerLaw)) := by
  exact risk_eq_pilot_covariate_integral P g D hmodel.covariate_density.1 hX
    (designRiskIntegrand_aestronglyMeasurable P g D hmodel hX hD)

/-- A pilot coupling and a unique-core event turn the pointwise flip loss
into a lower bound for the sum of the two adjacent risks. -/
-- keep: reusable coupling-to-risk bridge for alternative hypercube converses
lemma hypercube_flip_risk_edge_of_coupling {d m N K : ℕ}
    {L β cX CX cg Cg : ℝ}
    (D : Design m N d) (hD : MatchingDesignClass D) (hN : 1 ≤ N)
    (g : (Fin K → Bool) → XSpace d → ℝ) (base : XSpace d → ℝ)
    (amplitude : ℝ) (ψ : Fin K → XSpace d → ℝ)
    (hg : ∀ θ x, g θ x = base x + amplitude *
      ∑ j : Fin K, localSign (θ j) * ψ j x)
    (Q S : Fin K → Set (XSpace d))
    (hQ : ∀ j, MeasurableSet (Q j)) (hS : ∀ j, MeasurableSet (S j))
    (hSQ : ∀ j, S j ⊆ Q j)
    (hsupport : ∀ j y, y ∉ Q j → ψ j y = 0)
    (hcore : ∀ j y, y ∈ S j → ψ j y = 1)
    (hmodel : ∀ θ,
      RegularScoreModel (bernoulliUnitLaw (g θ)) (g θ) L β cX CX cg Cg)
    (hcov : ∀ θ, (bernoulliUnitLaw (g θ)).map Prod.fst = cubeMeasure d)
    (θ : Fin K → Bool) (j : Fin K)
    (Γ : Measure (PilotSample m d × PilotSample m d))
    (hΓ : Causalean.Stat.IsCoupling Γ
      (Measure.pi fun _ : Fin m => pilotUnitLaw (bernoulliUnitLaw (g θ)))
      (Measure.pi fun _ : Fin m =>
        pilotUnitLaw (bernoulliUnitLaw (g (flipCoordinate θ j)))))
    (hsmall : (N : ℝ) * (cubeMeasure d).real (Q j) ≤ 1 / 2) :
    (amplitude ^ 2 / (N : ℝ)) *
        (Γ.real {p | p.1 = p.2} *
          ((N : ℝ) * (cubeMeasure d).real (S j) / 2)) ≤
      risk (bernoulliUnitLaw (g θ)) (g θ) D +
        risk (bernoulliUnitLaw (g (flipCoordinate θ j)))
          (g (flipCoordinate θ j)) D := by
  let P₀ := bernoulliUnitLaw (g θ)
  let P₁ := bernoulliUnitLaw (g (flipCoordinate θ j))
  let μ₀ := Measure.pi fun _ : Fin m => pilotUnitLaw P₀
  let μ₁ := Measure.pi fun _ : Fin m => pilotUnitLaw P₁
  let ν := Measure.pi fun _ : Fin N => cubeMeasure d
  let η := ν.prod randomizerLaw
  let E : Set (MainCovariates N d × ℝ) :=
    {z | z.1 ∈ ⋃ i : Fin N,
      {x | x i ∈ S j ∧ ∀ k, k ≠ i → x k ∉ Q j}}
  let A : Set ((PilotSample m d × PilotSample m d) ×
      (MainCovariates N d × ℝ)) := {z | z.1.1 = z.1.2 ∧ z.2 ∈ E}
  let f₀ : PilotSample m d × (MainCovariates N d × ℝ) → ℝ :=
    fun z => pairLoss (g θ) z.2.1 (D (z.1, z.2.1, z.2.2)) / (N : ℝ)
  let f₁ : PilotSample m d × (MainCovariates N d × ℝ) → ℝ :=
    fun z => pairLoss (g (flipCoordinate θ j)) z.2.1
      (D (z.1, z.2.1, z.2.2)) / (N : ℝ)
  letI : IsProbabilityMeasure P₀ := (hmodel θ).covariate_density.1
  letI : IsProbabilityMeasure P₁ :=
    (hmodel (flipCoordinate θ j)).covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P₀) :=
    histogram_pilotUnitLaw_probability P₀ (hmodel θ).covariate_density.1
  letI : IsProbabilityMeasure (pilotUnitLaw P₁) :=
    histogram_pilotUnitLaw_probability P₁
      (hmodel (flipCoordinate θ j)).covariate_density.1
  letI : IsProbabilityMeasure (cubeMeasure d) := by
    rw [← hcov θ]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  letI : IsProbabilityMeasure Γ := hΓ.isProbabilityMeasure
  have hE : MeasurableSet E := by
    dsimp [E]
    exact (MeasurableSet.iUnion fun i =>
      measurableSet_singleton_core_event (S j) (Q j) (hS j) (hQ j) i).preimage
        measurable_fst
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun
      (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst)).inter (hE.preimage measurable_snd)
  have hf₀ : Integrable f₀ (μ₀.prod η) := by
    exact designRiskIntegrand_integrable P₀ (g θ) D (hmodel θ) (hcov θ) hD hN
  have hf₁ : Integrable f₁ (μ₁.prod η) := by
    exact designRiskIntegrand_integrable P₁ (g (flipCoordinate θ j)) D
      (hmodel (flipCoordinate θ j)) (hcov (flipCoordinate θ j)) hD hN
  have hedge : (amplitude ^ 2 / (N : ℝ)) * (Γ.prod η).real A ≤
      (∫ z, f₀ z ∂μ₀.prod η) + ∫ z, f₁ z ∂μ₁.prod η := by
    apply coupling_integral_add_lower_of_event μ₀ μ₁ η Γ hΓ f₀ f₁ A
      (amplitude ^ 2 / (N : ℝ)) hf₀ hf₁ hA
    · intro z
      dsimp [f₀]
      unfold pairLoss
      positivity
    · intro z
      dsimp [f₁]
      unfold pairLoss
      positivity
    · intro z hz
      rcases Set.mem_iUnion.mp hz.2 with ⟨i, hi⟩
      have hp := hypercube_flip_singleton_design_pairLoss D g base amplitude ψ hg Q S
        hsupport hcore θ j z.1.1 z.1.2 hz.1 z.2.1 z.2.2 i hi.1
        (fun k hk => by by_contra hki; exact hi.2 k hki hk)
      dsimp [f₀, f₁]
      have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      rw [← add_div]
      exact (div_le_div_iff_of_pos_right hNr).2 hp
  have hmain := pi_exists_unique_core_event_real_lower (cubeMeasure d)
    (S j) (Q j) (hS j) (hQ j) (hSQ j) hN hsmall
  have hη : ((N : ℝ) * (cubeMeasure d).real (S j) / 2) ≤ η.real E := by
    dsimp [η, E, ν]
    rw [show {z : MainCovariates N d × ℝ |
          z.1 ∈ ⋃ i : Fin N, {x | x i ∈ S j ∧ ∀ k, k ≠ i → x k ∉ Q j}} =
        (⋃ i : Fin N, {x | x i ∈ S j ∧ ∀ k, k ≠ i → x k ∉ Q j}) ×ˢ
          Set.univ by ext z; simp]
    rw [measureReal_prod_prod, probReal_univ, mul_one]
    exact hmain
  have hmass : Γ.real {p | p.1 = p.2} *
      ((N : ℝ) * (cubeMeasure d).real (S j) / 2) ≤ (Γ.prod η).real A := by
    rw [coupling_agreement_prod_event_mass Γ η E hE]
    exact mul_le_mul_of_nonneg_left hη measureReal_nonneg
  have hcoef : 0 ≤ amplitude ^ 2 / (N : ℝ) := by positivity
  calc
    (amplitude ^ 2 / (N : ℝ)) *
        (Γ.real {p | p.1 = p.2} *
          ((N : ℝ) * (cubeMeasure d).real (S j) / 2)) ≤
        (amplitude ^ 2 / (N : ℝ)) * (Γ.prod η).real A :=
      mul_le_mul_of_nonneg_left hmass hcoef
    _ ≤ (∫ z, f₀ z ∂μ₀.prod η) + ∫ z, f₁ z ∂μ₁.prod η := hedge
    _ = risk P₀ (g θ) D + risk P₁ (g (flipCoordinate θ j)) D := by
      rw [risk_eq_pilot_cube_integral P₀ (g θ) D (hmodel θ) (hcov θ) hD,
        risk_eq_pilot_cube_integral P₁ (g (flipCoordinate θ j)) D
          (hmodel (flipCoordinate θ j)) (hcov (flipCoordinate θ j)) hD]

end CausalSmith.Experimentation.PilotscorePairingFrontier
