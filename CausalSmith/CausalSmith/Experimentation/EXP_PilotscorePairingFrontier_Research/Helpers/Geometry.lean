module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.Matching
public import Causalean.Mathlib.Topology.SpaceFillingCurve.Matching

/-! # Deterministic geometric matching cost -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

variable {d m N : ℕ} {β L cX CX cg Cg h c0 c1 C1 C2 : ℝ}

open scoped BigOperators
open Causalean.Mathlib.Topology.SpaceFillingCurve

-- @node: perfectPairing_to_match
lemma perfectPairing_to_match (M : PerfectPairing N) :
    ∃ M' : Match N, ∀ f : Fin N → Fin N → ℝ,
      (∀ i j, f i j = f j i) →
      (1 / 2 : ℝ) * ∑ i : Fin N, f i (M'.val i) =
        ∑ j : Fin (N / 2), f (M.edge j).1 (M.edge j).2 := by
  classical
  let e : Fin (N / 2) × Fin 2 → Fin N := fun jk =>
    if jk.2 = 0 then (M.edge jk.1).1 else (M.edge jk.1).2
  have he0 (j : Fin (N / 2)) : e (j, 0) = (M.edge j).1 := by simp [e]
  have he1 (j : Fin (N / 2)) : e (j, 1) = (M.edge j).2 := by simp [e]
  have hidx (i : Fin N) (j k : Fin (N / 2))
      (hj : i = (M.edge j).1 ∨ i = (M.edge j).2)
      (hk : i = (M.edge k).1 ∨ i = (M.edge k).2) : j = k := by
    obtain ⟨l, -, hl⟩ := M.covers i
    exact (hl j hj).trans (hl k hk).symm
  have heinj : Function.Injective e := by
    intro a b hab
    rcases a with ⟨j, u⟩
    rcases b with ⟨k, v⟩
    fin_cases u <;> fin_cases v
    · have hjk : j = k := hidx _ j k (Or.inl (he0 j).symm)
          (Or.inl (hab.trans (he0 k)))
      subst k
      rfl
    · have hjk : j = k := hidx _ j k (Or.inl (he0 j).symm)
          (Or.inr (hab.trans (he1 k)))
      subst k
      exact False.elim (M.distinct j (by simpa [he0, he1] using hab))
    · have hjk : j = k := hidx _ j k (Or.inr (he1 j).symm)
          (Or.inl (hab.trans (he0 k)))
      subst k
      exact False.elim (M.distinct j (by simpa [he0, he1] using hab.symm))
    · have hjk : j = k := hidx _ j k (Or.inr (he1 j).symm)
          (Or.inr (hab.trans (he1 k)))
      subst k
      rfl
  have hesurj : Function.Surjective e := by
    intro i
    obtain ⟨j, hj, _⟩ := M.covers i
    rcases hj with hj | hj
    · exact ⟨(j, 0), (he0 j).trans hj.symm⟩
    · exact ⟨(j, 1), (he1 j).trans hj.symm⟩
  let E : Fin (N / 2) × Fin 2 ≃ Fin N := Equiv.ofBijective e ⟨heinj, hesurj⟩
  let swap : Equiv.Perm (Fin (N / 2) × Fin 2) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1)
  let σ : Equiv.Perm (Fin N) := E.symm.trans (swap.trans E)
  have hσ (j : Fin (N / 2)) : σ (E (j, 0)) = E (j, 1) := by
    simp [σ, swap]
  have hσ' (j : Fin (N / 2)) : σ (E (j, 1)) = E (j, 0) := by
    simp [σ, swap]
  let M' : Match N := ⟨σ, by
    constructor
    · intro i
      obtain ⟨⟨j, u⟩, rfl⟩ := E.surjective i
      fin_cases u <;> simp [hσ, hσ']
    · intro i
      obtain ⟨⟨j, u⟩, rfl⟩ := E.surjective i
      fin_cases u
      · intro h
        have h' : σ (E (j, (0 : Fin 2))) = E (j, 0) := by simpa using h
        rw [hσ] at h'
        change e (j, 1) = e (j, 0) at h'
        rw [he0, he1] at h'
        exact M.distinct j h'.symm
      · intro h
        have h' : σ (E (j, (1 : Fin 2))) = E (j, 1) := by simpa using h
        rw [hσ'] at h'
        change e (j, 0) = e (j, 1) at h'
        rw [he0, he1] at h'
        exact M.distinct j h'
    ⟩
  refine ⟨M', ?_⟩
  intro f hf
  change (1 / 2 : ℝ) * ∑ i : Fin N, f i (σ i) = _
  rw [← Equiv.sum_comp E]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp_rw [hσ, hσ']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (1 / 2 : ℝ) * (f (e (j, 0)) (e (j, 1)) +
    f (e (j, 1)) (e (j, 0))) = f (M.edge j).1 (M.edge j).2
  rw [he0, he1, hf (M.edge j).2 (M.edge j).1]
  ring

lemma geometric_cost_bound (hd : 2 ≤ d) (hN : Even N) (hN2 : 2 ≤ N)
    (x : MainCovariates N d) (hx : ∀ i, x i ∈ cube d) :
    geometricCost x (geometricMatching x hN hN2) ≤
      16 * (d : ℝ) * (N : ℝ) ^ (1 - 2 / (d : ℝ)) := by
  classical
  have hcube : ∀ i, InUnitCube (x i) := by
    intro i
    exact hx i
  obtain ⟨M, hM⟩ :=
    exists_perfectPairing_sqEuclidean_cost_le d N hd hN hN2 x hcube
  obtain ⟨M', hcost⟩ := perfectPairing_to_match M
  have hdist (i j : Fin N) :
      (euclideanDistance (x i) (x j)) ^ 2 = sqEuclideanDist (x i) (x j) := by
    unfold euclideanDistance sqEuclideanDist
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hsym (i j : Fin N) :
      sqEuclideanDist (x i) (x j) = sqEuclideanDist (x j) (x i) := by
    unfold sqEuclideanDist
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hcost' : geometricCost x M' =
      ∑ j : Fin (N / 2), sqEuclideanDist (x (M.edge j).1) (x (M.edge j).2) := by
    unfold geometricCost
    simp_rw [hdist]
    exact hcost (fun i j => sqEuclideanDist (x i) (x j)) hsym
  calc
    geometricCost x (geometricMatching x hN hN2) ≤ geometricCost x M' :=
      (Classical.choose_spec (exists_geometricMatching x hN hN2) M').1
    _ = _ := hcost'
    _ ≤ _ := hM

-- @node: holder_pairLoss_le_geometricCost_lipschitz
lemma holder_pairLoss_le_geometricCost_lipschitz
    (g : XSpace d → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : HolderScore g L 1) (x : MainCovariates N d)
    (hx : ∀ i, x i ∈ cube d) (M : Match N) :
    pairLoss g x M ≤ L ^ 2 * geometricCost x M := by
  unfold pairLoss geometricCost
  have hterm (i : Fin N) :
      (g (x i) - g (x (M.val i))) ^ 2 ≤
        L ^ 2 * (euclideanDistance (x i) (x (M.val i))) ^ 2 := by
    have h := hg (x i) (hx i) (x (M.val i)) (hx (M.val i))
    have hd : 0 ≤ euclideanDistance (x i) (x (M.val i)) := by
      unfold euclideanDistance
      positivity
    have ha : 0 ≤ L * euclideanDistance (x i) (x (M.val i)) :=
      mul_nonneg hL hd
    rw [Real.rpow_one] at h
    have hs := (sq_le_sq₀ (abs_nonneg _) ha).2 h
    simpa [sq_abs, mul_pow] using hs
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hterm i)
  simp only [← Finset.mul_sum] at hsum
  nlinarith [sq_nonneg L]

-- @node: geometric_pairLoss_lipschitz_rate
lemma geometric_pairLoss_lipschitz_rate
    (hd : 2 ≤ d) (hN : Even N) (hN2 : 2 ≤ N)
    (g : XSpace d → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : HolderScore g L 1) (x : MainCovariates N d)
    (hx : ∀ i, x i ∈ cube d) :
    pairLoss g x (geometricMatching x hN hN2) ≤
      16 * L ^ 2 * (d : ℝ) * (N : ℝ) ^ (1 - 2 / (d : ℝ)) := by
  have h₁ := holder_pairLoss_le_geometricCost_lipschitz g L hL hg x hx
    (geometricMatching x hN hN2)
  have h₂ := geometric_cost_bound hd hN hN2 x hx
  have h₃ := mul_le_mul_of_nonneg_left h₂ (sq_nonneg L)
  nlinarith

-- @node: holder_pairLoss_le_distance_rpow_sum
lemma holder_pairLoss_le_distance_rpow_sum
    (g : XSpace d → ℝ) (L β : ℝ) (hL : 0 ≤ L)
    (hg : HolderScore g L β) (x : MainCovariates N d)
    (hx : ∀ i, x i ∈ cube d) (M : Match N) :
    pairLoss g x M ≤
      L ^ 2 * ((1 / 2 : ℝ) * ∑ i : Fin N,
        (euclideanDistance (x i) (x (M.val i))) ^ (2 * β)) := by
  unfold pairLoss
  have hterm (i : Fin N) :
      (g (x i) - g (x (M.val i))) ^ 2 ≤
        L ^ 2 * (euclideanDistance (x i) (x (M.val i))) ^ (2 * β) := by
    have h := hg (x i) (hx i) (x (M.val i)) (hx (M.val i))
    have hnonneg : 0 ≤ L * (euclideanDistance (x i) (x (M.val i))) ^ β :=
      mul_nonneg hL (Real.rpow_nonneg (by unfold euclideanDistance; positivity) _)
    have hs := (sq_le_sq₀ (abs_nonneg _) hnonneg).2 h
    calc
      (g (x i) - g (x (M.val i))) ^ 2 ≤
          (L * euclideanDistance (x i) (x (M.val i)) ^ β) ^ 2 := by
            simpa [sq_abs] using hs
      _ = L ^ 2 * (euclideanDistance (x i) (x (M.val i))) ^ (2 * β) := by
        have hp : (euclideanDistance (x i) (x (M.val i)) ^ β) ^ 2 =
            euclideanDistance (x i) (x (M.val i)) ^ (2 * β) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by unfold euclideanDistance; positivity)]
          congr 1
          ring
        rw [mul_pow, hp]
  have hsum := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hterm i)
  rw [← Finset.mul_sum] at hsum
  nlinarith [hsum]

-- @node: sum_rpow_le_card_mul_sum_rpow
lemma sum_rpow_le_card_mul_sum_rpow {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ p) ≤ (n : ℝ) ^ (1 - p) * (∑ i, a i) ^ p := by
  let c : ℝ := n
  have hc : 0 < c := by dsimp [c]; exact_mod_cast hn
  have hw : (∑ _i : Fin n, c⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc.ne'
  have hj := (Real.concaveOn_rpow hp0.le hp1).le_map_sum
    (t := Finset.univ) (w := fun _ : Fin n => c⁻¹) (p := a)
    (by intro i hi; exact inv_nonneg.mpr hc.le) hw
    (by intro i hi; exact ha i)
  simp only [smul_eq_mul] at hj
  have hmain : c⁻¹ * (∑ i, a i ^ p) ≤
      (c⁻¹ * ∑ i, a i) ^ p := by
    simpa [Finset.mul_sum] using hj
  have hsum : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
  calc
    (∑ i, a i ^ p) = c * (c⁻¹ * ∑ i, a i ^ p) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    _ ≤ c * (c⁻¹ * ∑ i, a i) ^ p :=
      mul_le_mul_of_nonneg_left hmain hc.le
    _ = (n : ℝ) ^ (1 - p) * (∑ i, a i) ^ p := by
      rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hsum]
      rw [← Real.rpow_neg_eq_inv_rpow]
      rw [← mul_assoc]
      have hpow : c * c ^ (-p) = c ^ (1 - p) := by
        calc
          c * c ^ (-p) = c ^ (1 : ℝ) * c ^ (-p) := by rw [Real.rpow_one]
          _ = c ^ (1 + -p) := (Real.rpow_add hc _ _).symm
          _ = c ^ (1 - p) := by ring
      rw [hpow]

-- @node: holder_pairLoss_le_geometricCost_rpow
lemma holder_pairLoss_le_geometricCost_rpow
    (hNpos : 0 < N) (g : XSpace d → ℝ) (L β : ℝ)
    (hL : 0 ≤ L) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hg : HolderScore g L β) (x : MainCovariates N d)
    (hx : ∀ i, x i ∈ cube d) (M : Match N) :
    pairLoss g x M ≤
      L ^ 2 * ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - β) *
        (2 * geometricCost x M) ^ β) := by
  have hbase (i : Fin N) :
      0 ≤ (euclideanDistance (x i) (x (M.val i))) ^ 2 := sq_nonneg _
  have hsum := sum_rpow_le_card_mul_sum_rpow hNpos β hβ0 hβ1
    (fun i : Fin N => (euclideanDistance (x i) (x (M.val i))) ^ 2) hbase
  have hpower (i : Fin N) :
      ((euclideanDistance (x i) (x (M.val i))) ^ 2) ^ β =
        (euclideanDistance (x i) (x (M.val i))) ^ (2 * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by unfold euclideanDistance; positivity)]
    congr 1
  simp_rw [hpower] at hsum
  have hpair := holder_pairLoss_le_distance_rpow_sum g L β hL hg x hx M
  have hcost :
      (∑ i : Fin N, (euclideanDistance (x i) (x (M.val i))) ^ 2) =
        2 * geometricCost x M := by
    unfold geometricCost
    ring
  rw [hcost] at hsum
  nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hsum)]

-- @node: geometric_pairLoss_holder_rate
lemma geometric_pairLoss_holder_rate
    (hd : 2 ≤ d) (hN : Even N) (hN2 : 2 ≤ N)
    (g : XSpace d → ℝ) (L β : ℝ) (hL : 0 ≤ L)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hg : HolderScore g L β) (x : MainCovariates N d)
    (hx : ∀ i, x i ∈ cube d) :
    pairLoss g x (geometricMatching x hN hN2) ≤
      L ^ 2 * ((1 / 2 : ℝ) * (32 * (d : ℝ)) ^ β *
        (N : ℝ) ^ (1 - 2 * β / d)) := by
  let M := geometricMatching x hN hN2
  have hfirst := holder_pairLoss_le_geometricCost_rpow
    (by omega : 0 < N) g L β hL hβ0 hβ1 hg x hx M
  have hcost := geometric_cost_bound hd hN hN2 x hx
  have hcost0 : 0 ≤ geometricCost x M := by
    unfold geometricCost
    positivity
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hupper : 2 * geometricCost x M ≤
      (32 * (d : ℝ)) * (N : ℝ) ^ (1 - 2 / (d : ℝ)) := by
    dsimp [M] at hcost ⊢
    nlinarith
  have hpow : (2 * geometricCost x M) ^ β ≤
      ((32 * (d : ℝ)) * (N : ℝ) ^ (1 - 2 / (d : ℝ))) ^ β :=
    Real.rpow_le_rpow (by positivity) hupper hβ0.le
  have hformula :
      (N : ℝ) ^ (1 - β) *
        ((32 * (d : ℝ)) * (N : ℝ) ^ (1 - 2 / (d : ℝ))) ^ β =
      (32 * (d : ℝ)) ^ β * (N : ℝ) ^ (1 - 2 * β / d) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hNpos.le _),
      ← Real.rpow_mul hNpos.le]
    have hexp : (1 - β) + (1 - 2 / (d : ℝ)) * β =
        1 - 2 * β / d := by
      field_simp
      ring
    calc
      (N : ℝ) ^ (1 - β) *
          ((32 * (d : ℝ)) ^ β * (N : ℝ) ^ ((1 - 2 / (d : ℝ)) * β)) =
        (32 * (d : ℝ)) ^ β *
          ((N : ℝ) ^ (1 - β) * (N : ℝ) ^ ((1 - 2 / (d : ℝ)) * β)) := by ring
      _ = _ := by rw [← Real.rpow_add hNpos, hexp]
  calc
    pairLoss g x M ≤
        L ^ 2 * ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - β) *
          (2 * geometricCost x M) ^ β) := hfirst
    _ ≤ L ^ 2 * ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - β) *
          ((32 * (d : ℝ)) * (N : ℝ) ^ (1 - 2 / (d : ℝ))) ^ β) := by
            gcongr
    _ = _ := by
      have := congrArg (fun t : ℝ => L ^ 2 * ((1 / 2 : ℝ) * t)) hformula
      convert this using 1 <;> ring

-- @node: cube_euclideanDistance_le_sqrt_dim
lemma cube_euclideanDistance_le_sqrt_dim
    (x y : XSpace d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    euclideanDistance x y ≤ Real.sqrt (d : ℝ) := by
  have hterm (i : Fin d) : (x i - y i) ^ 2 ≤ (1 : ℝ) := by
    have hxi := hx i
    have hyi := hy i
    have hlo : -1 ≤ x i - y i := by linarith [hxi.1, hyi.2]
    have hhi : x i - y i ≤ 1 := by linarith [hxi.2, hyi.1]
    have hprod : 0 ≤ (1 + (x i - y i)) * (1 - (x i - y i)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsum : (∑ i : Fin d, (x i - y i) ^ 2) ≤ (d : ℝ) := by
    calc
      (∑ i : Fin d, (x i - y i) ^ 2) ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (d : ℝ) := by simp
  exact Real.sqrt_le_sqrt hsum

-- @node: holder_score_cube_oscillation
lemma holder_score_cube_oscillation (g : XSpace d → ℝ)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (hg : HolderScore g L β)
    (x y : XSpace d) (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |g x - g y| ≤ L * (d : ℝ) ^ (β / 2) := by
  have hdist := cube_euclideanDistance_le_sqrt_dim x y hx hy
  have hpow : (euclideanDistance x y) ^ β ≤ (Real.sqrt (d : ℝ)) ^ β :=
    Real.rpow_le_rpow (by unfold euclideanDistance; positivity) hdist hβ
  have hdnonneg : (0 : ℝ) ≤ d := by positivity
  have hsqrt : (Real.sqrt (d : ℝ)) ^ β = (d : ℝ) ^ (β / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hdnonneg]
    ring
  calc
    |g x - g y| ≤ L * (euclideanDistance x y) ^ β := hg x hx y hy
    _ ≤ L * (Real.sqrt (d : ℝ)) ^ β := mul_le_mul_of_nonneg_left hpow hL
    _ = L * (d : ℝ) ^ (β / 2) := by rw [hsqrt]

end CausalSmith.Experimentation.PilotscorePairingFrontier
