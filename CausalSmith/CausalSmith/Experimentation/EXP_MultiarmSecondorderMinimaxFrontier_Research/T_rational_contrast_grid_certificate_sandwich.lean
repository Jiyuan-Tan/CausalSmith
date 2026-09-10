import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.RationalGridCertificateFinite

/-! Exact rational primal/dual certificates and their asymptotic sandwich. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Filter
open scoped BigOperators
open Finset Set

/-- A choice, at every positive population size, of the exact primal/dual grid
certificate and its barycenter procedure. -/
def IsRationalGridCertificateSequence (c : RatContrast K) (Mseq : ℕ → ℕ)
    (pi : ∀ k, GridPi K k)
    (w : ∀ k, GridWeight K k (Mseq k))
    (u : ℕ → ℚ)
    (nu : ∀ k, CountVec K k → ℚ)
    (delta : ∀ k, ∀ r : AllocVec K k, ObsVec r → ℝ) : Prop :=
  ∀ k, 0 < k →
    ExactGridPrimalDualCertificate c (pi k) (w k) (u k) (nu k) ∧
    IsGridBarycenter c (pi k) (w k) (delta k)

/-- The actual certificate gaps vanish at every scale dominated by the squared
grid resolution; conditionally on a normalized minimax limit, both certificate
improvements have the same limit.  The final clause records explicitly the
paper's universal `a_n = n^(4/3)`, `M_n = n` specialization. -/
def RationalGridCertificateAsymptotics (c : RatContrast K) : Prop :=
  (∀ (Mseq : ℕ → ℕ)
      (pi : ∀ k, GridPi K k)
      (w : ∀ k, GridWeight K k (Mseq k))
      (u : ℕ → ℚ)
      (nu : ∀ k, CountVec K k → ℚ)
      (delta : ∀ k, ∀ r : AllocVec K k, ObsVec r → ℝ),
    IsRationalGridCertificateSequence c Mseq pi w u nu delta →
    ∀ (a : PositiveSequence),
      (∀ k, 0 < k → 0 < Mseq k) →
      Tendsto (fun k => a k / (Mseq k : ℝ) ^ 2) atTop (nhds 0) →
      Tendsto (fun k => a k *
        (upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k)))
        atTop (nhds 0) ∧
      ∀ C,
        Tendsto (fun k => a k * dN K (ratContrastToReal c) k) atTop (nhds C) →
        Tendsto (fun k => a k *
          (C0 (ratContrastToReal c) / k - upperCertificate c (pi k) (delta k)))
          atTop (nhds C) ∧
        Tendsto (fun k => a k *
          (C0 (ratContrastToReal c) / k - lowerCertificate c (nu k)))
          atTop (nhds C)) ∧
  (∀ (pi : ∀ k, GridPi K k)
    (w : ∀ k, GridWeight K k k)
    (u : ℕ → ℚ)
    (nu : ∀ k, CountVec K k → ℚ)
    (delta : ∀ k, ∀ r : AllocVec K k, ObsVec r → ℝ),
    IsRationalGridCertificateSequence c (fun k => k) pi w u nu delta →
    Tendsto (fun k => secondOrderScale k *
      (upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k)))
      atTop (nhds 0) ∧
    ∀ C,
      Tendsto (fun k => secondOrderScale k * dN K (ratContrastToReal c) k)
        atTop (nhds C) →
      Tendsto (fun k => secondOrderScale k *
        (C0 (ratContrastToReal c) / k - upperCertificate c (pi k) (delta k)))
        atTop (nhds C) ∧
      Tendsto (fun k => secondOrderScale k *
        (C0 (ratContrastToReal c) / k - lowerCertificate c (nu k)))
        atTop (nhds C))

-- @node: selectRationalGridCertificateSequence
/-- [the stated side condition holds](hyp:hMseq), [the select rational grid certificate sequence property holds](goal). -/
lemma selectRationalGridCertificateSequence (c : RatContrast K) (Mseq : ℕ → ℕ)
    (hMseq : ∀ k, 0 < k → 0 < Mseq k) :
    ∃ (pi : ∀ k, GridPi K k)
      (w : ∀ k, GridWeight K k (Mseq k))
      (u : ℕ → ℚ) (nu : ∀ k, CountVec K k → ℚ)
      (delta : ∀ k, ∀ r : AllocVec K k, ObsVec r → ℝ),
      IsRationalGridCertificateSequence c Mseq pi w u nu delta ∧
      ∀ k, 0 < k →
        lowerCertificate c (nu k) ≤ rhoN K k (ratContrastToReal c) ∧
        rhoN K k (ratContrastToReal c) ≤ upperCertificate c (pi k) (delta k) ∧
        upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k) ≤
          C0 (ratContrastToReal c) / (4 * (Mseq k : ℝ) ^ 2) := by
  classical
  choose piP wP uP nuP hcertP huP using fun k : PositiveNat =>
    exists_exact_grid_primal_dual_certificate c k.2 (hMseq k k.2)
  let pi : ∀ k, GridPi K k := fun k =>
    if hk : 0 < k then piP ⟨k, hk⟩ else fun _ => 0
  let w : ∀ k, GridWeight K k (Mseq k) := fun k =>
    if hk : 0 < k then wP ⟨k, hk⟩ else fun _ _ _ => 0
  let u : ℕ → ℚ := fun k => if hk : 0 < k then uP ⟨k, hk⟩ else 0
  let nu : ∀ k, CountVec K k → ℚ := fun k =>
    if hk : 0 < k then nuP ⟨k, hk⟩ else fun _ => 0
  let delta : ∀ k, ∀ r : AllocVec K k, ObsVec r → ℝ := fun k r x =>
    if _h : 0 < pi k r then
      ∑ g, (gammaMC (Mseq k) c g : ℝ) * w k r x g / (pi k r : ℝ) else 0
  refine ⟨pi, w, u, nu, delta, ?_, ?_⟩
  · intro k hk
    have hcert := hcertP ⟨k, hk⟩
    have hcert' : ExactGridPrimalDualCertificate c (pi k) (w k) (u k) (nu k) := by
      simpa [pi, w, u, nu, hk] using hcert
    refine ⟨hcert', ?_⟩
    intro r x
    rfl
  · intro k hk
    have hcert := hcertP ⟨k, hk⟩
    have hu := huP ⟨k, hk⟩
    have hcert' : ExactGridPrimalDualCertificate c (pi k) (w k) (u k) (nu k) := by
      simpa [pi, w, u, nu, hk] using hcert
    have hu' : (u k : ℝ) = gridLPValue K k (Mseq k) c hk (hMseq k hk) := by
      rw [show u k = uP ⟨k, hk⟩ by simp [u, hk]]
      exact hu
    have hbar : IsGridBarycenter c (pi k) (w k) (delta k) := by
      intro r x
      rfl
    rcases hcert' with ⟨wQ, y, hw, hpr, hy, hnuEq, huDual⟩
    have hcert'' : ExactGridPrimalDualCertificate c (pi k) (w k) (u k) (nu k) :=
      ⟨wQ, y, hw, hpr, hy, hnuEq, huDual⟩
    have hnu : IsRationalPrior (nu k) := by
      rw [hnuEq]
      exact ⟨hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1⟩
    have hlower := lowerCertificate_le_rhoN c hk (nu k) hnu
    have hrho : rhoN K k (ratContrastToReal c) ≤
        upperCertificate c (pi k) (delta k) := by
      apply rhoN_le_upperCertificate c (hMseq k hk) (pi k) (w k) (delta k)
      · exact ⟨wQ, u k, hw, hpr⟩
      · exact hbar
    have hupper : upperCertificate c (pi k) (delta k) ≤
        gridLPValue K k (Mseq k) c hk (hMseq k hk) := by
      rw [← hu']
      exact upperCertificate_le_gridObjective c (pi k) (w k) (u k) (delta k)
        (nu k) hcert'' hbar
    have hmesh : gridLPValue K k (Mseq k) c hk (hMseq k hk) ≤
        lowerCertificate c (nu k) +
          C0 (ratContrastToReal c) / (4 * (Mseq k : ℝ) ^ 2) := by
      rw [← hu']
      simpa using gridObjective_le_lowerCertificate_add_mesh c hk (hMseq k hk)
        (pi k) (w k) (u k) (nu k) hcert''
    exact ⟨hlower, hrho, by linarith⟩

-- @node: rationalGridCertificateAsymptotics_proof
/-- [the rational grid certificate asymptotics proof property holds](goal). -/
lemma rationalGridCertificateAsymptotics_proof (c : RatContrast K) :
    RationalGridCertificateAsymptotics c := by
  classical
  have hfixed : ∀ (Mseq : ℕ → ℕ)
      (pi : ∀ k, GridPi K k)
      (w : ∀ k, GridWeight K k (Mseq k))
      (u : ℕ → ℚ) (nu : ∀ k, CountVec K k → ℚ)
      (delta : ∀ k, ∀ r : AllocVec K k, ObsVec r → ℝ),
      IsRationalGridCertificateSequence c Mseq pi w u nu delta →
      ∀ (a : PositiveSequence),
        (∀ k, 0 < k → 0 < Mseq k) →
        Tendsto (fun k => a k / (Mseq k : ℝ) ^ 2) atTop (nhds 0) →
        Tendsto (fun k => a k *
          (upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k)))
          atTop (nhds 0) ∧
        ∀ C,
          Tendsto (fun k => a k * dN K (ratContrastToReal c) k) atTop (nhds C) →
          Tendsto (fun k => a k *
            (C0 (ratContrastToReal c) / k - upperCertificate c (pi k) (delta k)))
            atTop (nhds C) ∧
          Tendsto (fun k => a k *
            (C0 (ratContrastToReal c) / k - lowerCertificate c (nu k)))
            atTop (nhds C) := by
    intro Mseq pi w u nu delta hseq a hMseq hmesh
    have hbounds : ∀ k, 0 < k →
        lowerCertificate c (nu k) ≤ rhoN K k (ratContrastToReal c) ∧
        rhoN K k (ratContrastToReal c) ≤ upperCertificate c (pi k) (delta k) ∧
        upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k) ≤
          C0 (ratContrastToReal c) / (4 * (Mseq k : ℝ) ^ 2) := by
      intro k hk
      rcases hseq k hk with ⟨hcert, hbar⟩
      rcases hcert with ⟨wQ, y, hw, hpr, hy, hnuEq, huDual⟩
      have hcert' : ExactGridPrimalDualCertificate c (pi k) (w k) (u k) (nu k) :=
        ⟨wQ, y, hw, hpr, hy, hnuEq, huDual⟩
      have hnu : IsRationalPrior (nu k) := by
        rw [hnuEq]
        exact ⟨hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1⟩
      have hlower := lowerCertificate_le_rhoN c hk (nu k) hnu
      have hrho : rhoN K k (ratContrastToReal c) ≤
          upperCertificate c (pi k) (delta k) := by
        apply rhoN_le_upperCertificate c (hMseq k hk) (pi k) (w k) (delta k)
        · exact ⟨wQ, u k, hw, hpr⟩
        · exact hbar
      have hupper : upperCertificate c (pi k) (delta k) ≤ (u k : ℝ) :=
        upperCertificate_le_gridObjective c (pi k) (w k) (u k) (delta k)
          (nu k) hcert' hbar
      have hmesh' : (u k : ℝ) ≤ lowerCertificate c (nu k) +
          C0 (ratContrastToReal c) / (4 * (Mseq k : ℝ) ^ 2) := by
        simpa using gridObjective_le_lowerCertificate_add_mesh c hk (hMseq k hk)
          (pi k) (w k) (u k) (nu k) hcert'
      exact ⟨hlower, hrho, by linarith⟩
    have hkpos : ∀ᶠ k : ℕ in atTop, 0 < k :=
      eventually_atTop.2 ⟨1, fun k hk => by omega⟩
    have hmeshC : Tendsto (fun k => a k *
        (C0 (ratContrastToReal c) / (4 * (Mseq k : ℝ) ^ 2)))
        atTop (nhds 0) := by
      convert hmesh.const_mul (C0 (ratContrastToReal c) / 4) using 1
      · funext k
        ring
      · norm_num
    have hgap : Tendsto (fun k => a k *
        (upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k)))
        atTop (nhds 0) := by
      apply squeeze_zero' (g := fun k => a k *
        (C0 (ratContrastToReal c) / (4 * (Mseq k : ℝ) ^ 2)))
      · filter_upwards [hkpos] with k hk
        have hb := hbounds k hk
        exact mul_nonneg (le_of_lt (a.2 k)) (sub_nonneg.mpr (hb.1.trans hb.2.1))
      · filter_upwards [hkpos] with k hk
        exact mul_le_mul_of_nonneg_left (hbounds k hk).2.2 (le_of_lt (a.2 k))
      · exact hmeshC
    refine ⟨hgap, ?_⟩
    intro C htarget
    have huerr : Tendsto (fun k => a k *
        (upperCertificate c (pi k) (delta k) - rhoN K k (ratContrastToReal c)))
        atTop (nhds 0) := by
      apply squeeze_zero' (g := fun k => a k *
        (upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k)))
      · filter_upwards [hkpos] with k hk
        exact mul_nonneg (le_of_lt (a.2 k)) (sub_nonneg.mpr (hbounds k hk).2.1)
      · filter_upwards [hkpos] with k hk
        have hb := hbounds k hk
        exact mul_le_mul_of_nonneg_left (by linarith [hb.1]) (le_of_lt (a.2 k))
      · exact hgap
    have hlerr : Tendsto (fun k => a k *
        (rhoN K k (ratContrastToReal c) - lowerCertificate c (nu k)))
        atTop (nhds 0) := by
      apply squeeze_zero' (g := fun k => a k *
        (upperCertificate c (pi k) (delta k) - lowerCertificate c (nu k)))
      · filter_upwards [hkpos] with k hk
        exact mul_nonneg (le_of_lt (a.2 k)) (sub_nonneg.mpr (hbounds k hk).1)
      · filter_upwards [hkpos] with k hk
        have hb := hbounds k hk
        exact mul_le_mul_of_nonneg_left (by linarith [hb.2.1]) (le_of_lt (a.2 k))
      · exact hgap
    constructor
    · convert htarget.sub huerr using 1 <;> simp [dN]
      funext k
      ring
    · convert htarget.add hlerr using 1 <;> simp [dN]
      funext k
      ring
  refine ⟨hfixed, ?_⟩
  intro pi w u nu delta hseq
  let a : PositiveSequence :=
    ⟨fun k => if k = 0 then 1 else secondOrderScale k, fun k => by
      change 0 < (if k = 0 then 1 else secondOrderScale k)
      split_ifs with hk
      · norm_num
      · unfold secondOrderScale
        exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) _⟩
  have haeq : (a : ℕ → ℝ) =ᶠ[atTop] secondOrderScale := by
    filter_upwards [Ici_mem_atTop 1] with k hk
    simp [a, Nat.ne_of_gt (Nat.zero_lt_one.trans_le hk)]
  have hscale : Tendsto (fun k : ℕ => secondOrderScale k / (k : ℝ) ^ 2)
      atTop (nhds 0) := by
    have hp : Tendsto (fun k : ℕ => (k : ℝ) ^ (-(2 / 3 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
        tendsto_natCast_atTop_atTop
    apply hp.congr'
    filter_upwards [Ici_mem_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    unfold secondOrderScale
    rw [show (k : ℝ) ^ (2 : ℕ) = (k : ℝ) ^ (2 : ℝ) by
      exact (Real.rpow_natCast _ 2).symm, ← Real.rpow_sub hkR]
    norm_num
  have hamesh : Tendsto (fun k => a k / (k : ℝ) ^ 2) atTop (nhds 0) :=
    hscale.congr' (haeq.div (Filter.Eventually.of_forall fun _ => rfl)).symm
  obtain ⟨hgap, hlimits⟩ :=
    hfixed (fun k => k) pi w u nu delta hseq a (fun _ hk => hk) hamesh
  refine ⟨?_, ?_⟩
  · exact hgap.congr' (haeq.mul (Filter.Eventually.of_forall fun _ => rfl))
  · intro C htarget
    have htarget' : Tendsto (fun k => a k * dN K (ratContrastToReal c) k)
        atTop (nhds C) :=
      htarget.congr' (haeq.mul (Filter.Eventually.of_forall fun _ => rfl)).symm
    obtain ⟨hupper, hlower⟩ := hlimits C htarget'
    exact ⟨
      hupper.congr' (haeq.mul (Filter.Eventually.of_forall fun _ => rfl)),
      hlower.congr' (haeq.mul (Filter.Eventually.of_forall fun _ => rfl))⟩

-- @node: thm:rational-contrast-grid-certificate-sandwich
/-- [the population size is positive](hyp:hn), [the grid resolution is positive](hyp:hM), [for a rational contrast, the finite grid lower and upper certificates sandwich the minimax excess risk and become asymptotically sharp as the mesh vanishes](goal). -/
theorem rational_contrast_grid_certificate_sandwich
    (K n M : ℕ) (c : RatContrast K) (hn : 0 < n) (hM : 0 < M) :
    ∃ (pi : GridPi K n) (w : GridWeight K n M) (u : ℚ)
      (nu : CountVec K n → ℚ)
      (delta : ∀ r : AllocVec K n, ObsVec r → ℝ),
      ExactGridPrimalDualCertificate c pi w u nu ∧
      IsGridBarycenter c pi w delta ∧
      (u : ℝ) = gridLPValue K n M c hn hM ∧
      lowerCertificate c nu ≤ rhoN K n (ratContrastToReal c) ∧
      rhoN K n (ratContrastToReal c) ≤ upperCertificate c pi delta ∧
      upperCertificate c pi delta ≤ gridLPValue K n M c hn hM ∧
      gridLPValue K n M c hn hM ≤
        lowerCertificate c nu + C0 (ratContrastToReal c) / (4 * M ^ 2) ∧
      Fintype.card (CountVec K n) = Nat.choose (n + 2 ^ K - 1) (2 ^ K - 1) ∧
      Fintype.card (AllocVec K n) = Nat.choose (n + K - 1) (K - 1) ∧
      (∑ r : AllocVec K n, Fintype.card (ObsVec r)) =
        Nat.choose (n + 2 * K - 1) (2 * K - 1) ∧
      (∀ (a : PositiveSequence) (Mseq : ℕ → ℕ),
        (∀ k, 0 < Mseq k) →
        Tendsto (fun k => a k / (Mseq k : ℝ) ^ 2) atTop (nhds 0) →
        Tendsto (fun k => a k * (C0 (ratContrastToReal c) /
          (4 * (Mseq k : ℝ) ^ 2))) atTop (nhds 0)) ∧
      RationalGridCertificateAsymptotics c := by
  classical
  obtain ⟨pi, w, u, nu, hcert, hu⟩ :=
    exists_exact_grid_primal_dual_certificate c hn hM
  let delta : ∀ r : AllocVec K n, ObsVec r → ℝ := fun r x =>
    if _h : 0 < pi r then
      ∑ g, (gammaMC M c g : ℝ) * w r x g / (pi r : ℝ) else 0
  have hbar : IsGridBarycenter c pi w delta := by
    intro r x
    rfl
  rcases hcert with ⟨wQ, y, hw, hpr, hy, hnuEq, huDual⟩
  have hcert' : ExactGridPrimalDualCertificate c pi w u nu :=
    ⟨wQ, y, hw, hpr, hy, hnuEq, huDual⟩
  have hnu : IsRationalPrior nu := by
    rw [hnuEq]
    exact ⟨hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1⟩
  have hlower : lowerCertificate c nu ≤ rhoN K n (ratContrastToReal c) :=
    lowerCertificate_le_rhoN c hn nu hnu
  have hrho : rhoN K n (ratContrastToReal c) ≤ upperCertificate c pi delta := by
    apply rhoN_le_upperCertificate c hM pi w delta
    · exact ⟨wQ, u, hw, hpr⟩
    · exact hbar
  have hupper : upperCertificate c pi delta ≤ gridLPValue K n M c hn hM := by
    rw [← hu]
    exact upperCertificate_le_gridObjective c pi w u delta nu hcert' hbar
  have hmesh : gridLPValue K n M c hn hM ≤
      lowerCertificate c nu + C0 (ratContrastToReal c) / (4 * M ^ 2) := by
    rw [← hu]
    simpa using gridObjective_le_lowerCertificate_add_mesh c hn hM pi w u nu hcert'
  have hK := rationalContrast_admissibleArmCount c
  refine ⟨pi, w, u, nu, delta, hcert', hbar, hu, hlower, hrho, hupper, hmesh,
    response_count_cardinality, allocation_count_cardinality hK,
    allocation_observation_cardinality hK, ?_, ?_⟩
  · intro a Mseq _hMseq hlim
    have hmul := hlim.const_mul (C0 (ratContrastToReal c) / 4)
    convert hmul using 1
    · funext k
      ring
    · norm_num
  · exact rationalGridCertificateAsymptotics_proof c

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
