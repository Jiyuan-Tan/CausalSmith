import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_universal_second_order_rate
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_real_contrast_grid_certificate_transfer
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_k3_grid_certificate_sandwich
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_k3_scalar_score_not_minimax_preserving
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.SubsequentialLimits

/-! Established second-order rate and the finite-program certificate frontier. -/

open Filter

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- keep: public nonassertive payload preserving the frozen theorem's open-frontier clauses.
/-- The open-frontier record lists the second-order and certificate questions not settled by this development. -/
def secondOrderRateAndCertificateOpenFrontier : List String :=
  ["convergence of the normalized improvement is not determined",
   "the sharp limit and exact subsequential-limit set are not determined",
   "slow variation in the nonconvergent branch is not determined",
   "sharp second-order optimality of qStar is not determined",
   "convergence of optimizers or least-favorable priors is not determined",
   "no limiting face-corner HJB, cone-spectral, separable, or other operator is determined"]

/-- A real number is a cluster value of a sequence when some subsequence converges to it. -/
def ClusterValue (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (nhds a)

/-- A positive sequence is slowly varying when its ratio at every fixed positive rescaling of the index converges to one. -/
def SlowlyVarying (x : PositiveSequence) : Prop := RegularlyVarying x 0

/-- Slow variation for the actual normalized improvement, requiring positivity only eventually. -/
def SlowlyVaryingEventuallyPositive (x : ℕ → ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < x n) ∧
  ∀ t : ℝ, 0 < t →
    Tendsto (fun n : ℕ => x ⌊t * (n : ℝ)⌋₊ / x n) atTop (nhds 1)

/-- Two real sequences are asymptotically coincident when the absolute difference between their terms converges to zero. -/
def AsymptoticallyCoincident (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => |x n - y n|) atTop (nhds 0)

-- @node: secondOrderScalePositive
/-- The positive second-order scale replaces the zero-index value of the regularly varying scale by one. -/
noncomputable def secondOrderScalePositive : PositiveSequence :=
  ⟨fun n => if n = 0 then 1 else secondOrderScale n, fun n => by
    dsimp
    split_ifs with hn
    · positivity
    · unfold secondOrderScale
      exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _⟩

-- @node: eventuallyPositivePatch
/-- The eventual-positivity patch replaces nonpositive terms of a real sequence by one. -/
noncomputable def eventuallyPositivePatch (x : ℕ → ℝ) : PositiveSequence :=
  ⟨fun n => if 0 < x n then x n else 1, fun n => by
    dsimp
    split_ifs <;> positivity⟩

-- @node: eventuallyPositivePatch_eventually_eq
/-- [the observed count satisfies its stated condition](hyp:hx), [the eventually positive patch eventually equals property holds](goal). -/
lemma eventuallyPositivePatch_eventually_eq (x : ℕ → ℝ)
    (hx : ∀ᶠ n in atTop, 0 < x n) :
    (eventuallyPositivePatch x : ℕ → ℝ) =ᶠ[atTop] x :=
  hx.mono fun n hn => by simp [eventuallyPositivePatch, hn]

-- @node: secondOrderScalePositive_regularlyVarying
/-- [the second order scale positive regularly varying property holds](goal). -/
lemma secondOrderScalePositive_regularlyVarying :
    RegularlyVarying secondOrderScalePositive (4 / 3) := by
  intro t ht
  have hfloor := tendsto_nat_floor_mul_atTop t ht
  have heq : (fun n : ℕ =>
      secondOrderScalePositive ⌊t * (n : ℝ)⌋₊ /
        secondOrderScalePositive n) =ᶠ[atTop]
      (fun n : ℕ => (((⌊t * (n : ℝ)⌋₊ : ℕ) : ℝ) / n) ^ (4 / 3 : ℝ)) := by
    filter_upwards [Ici_mem_atTop 1, hfloor.eventually (Ici_mem_atTop 1)]
      with n hn hfn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hn)
    have hfn0 : ⌊t * (n : ℝ)⌋₊ ≠ 0 := Nat.ne_of_gt hfn
    simp only [secondOrderScalePositive, hn0, hfn0, ↓reduceIte]
    unfold secondOrderScale
    rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hbase : Tendsto (fun n : ℕ =>
      ((⌊t * (n : ℝ)⌋₊ : ℕ) : ℝ) / n) atTop (nhds t) := by
    change Tendsto ((fun x : ℝ => (⌊t * x⌋₊ : ℝ) / x) ∘
      fun n : ℕ => (n : ℝ)) atTop (nhds t)
    exact (tendsto_nat_floor_mul_div_atTop ht.le).comp
      tendsto_natCast_atTop_atTop
  exact (hbase.rpow_const (Or.inl ht.ne')).congr' heq.symm

-- @node: regularlyVarying_div
/-- [the parameter lies in the stated interval](hyp:ha), [the stated side condition holds](hyp:hb), [the regularly varying divided by property holds](goal). -/
lemma regularlyVarying_div (a b : PositiveSequence) (α β : ℝ)
    (ha : RegularlyVarying a α) (hb : RegularlyVarying b β) :
    RegularlyVarying
      (⟨fun n => a n / b n, fun n => div_pos (a.2 n) (b.2 n)⟩ :
        PositiveSequence) (α - β) := by
  intro t ht
  have h := (ha t ht).div (hb t ht) (ne_of_gt (Real.rpow_pos_of_pos ht β))
  convert h using 1
  · funext n
    change (a ⌊t * (n : ℝ)⌋₊ / b ⌊t * (n : ℝ)⌋₊) / (a n / b n) =
      (a ⌊t * (n : ℝ)⌋₊ / a n) / (b ⌊t * (n : ℝ)⌋₊ / b n)
    field_simp [ne_of_gt (a.2 n), ne_of_gt (b.2 n),
      ne_of_gt (a.2 ⌊t * (n : ℝ)⌋₊), ne_of_gt (b.2 ⌊t * (n : ℝ)⌋₊)]
    <;> ring
  · rw [Real.rpow_sub ht]

-- @node: asymptoticallyCoincident_of_scaled_sandwich
/-- [the stated side condition holds](hyp:hscale), [the stated side condition holds](hyp:hord), [the stated side condition holds](hyp:hwidth), [the asymptotically coincident when scaled sandwich property holds](goal). -/
lemma asymptoticallyCoincident_of_scaled_sandwich
    (scale center lower value upper : ℕ → ℝ)
    (hscale : ∀ n, 0 ≤ scale n)
    (hord : ∀ᶠ n in atTop, lower n ≤ value n ∧ value n ≤ upper n)
    (hwidth : Tendsto (fun n => scale n * (upper n - lower n))
      atTop (nhds 0)) :
    AsymptoticallyCoincident
        (fun n => scale n * (center n - lower n))
        (fun n => scale n * (center n - value n)) ∧
      AsymptoticallyCoincident
        (fun n => scale n * (center n - upper n))
        (fun n => scale n * (center n - value n)) := by
  constructor
  · apply squeeze_zero' (g := fun n => scale n * (upper n - lower n))
    · exact Filter.Eventually.of_forall fun n => abs_nonneg _
    · filter_upwards [hord] with n hn
      rw [abs_of_nonneg]
      · nlinarith [hscale n]
      · nlinarith [hscale n]
    · exact hwidth
  · apply squeeze_zero' (g := fun n => scale n * (upper n - lower n))
    · exact Filter.Eventually.of_forall fun n => abs_nonneg _
    · filter_upwards [hord] with n hn
      rw [abs_of_nonpos]
      · nlinarith [hscale n]
      · nlinarith [hscale n]
    · exact hwidth

-- @node: secondOrderScale_mesh_tendsto_zero
/-- [the second order scale mesh converges zero](goal). -/
lemma secondOrderScale_mesh_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => secondOrderScale n * (C / (4 * (n : ℝ) ^ 2)))
      atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 / 3 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      tendsto_natCast_atTop_atTop
  have heq : (fun n : ℕ => secondOrderScale n * (C / (4 * (n : ℝ) ^ 2)))
      =ᶠ[atTop] (fun n => (C / 4) * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by
    filter_upwards [Ici_mem_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold secondOrderScale
    calc
      (n : ℝ) ^ (4 / 3 : ℝ) * (C / (4 * (n : ℝ) ^ 2)) =
          (C / 4) * ((n : ℝ) ^ (4 / 3 : ℝ) / (n : ℝ) ^ (2 : ℝ)) := by
            rw [show (n : ℝ) ^ (2 : ℕ) = (n : ℝ) ^ (2 : ℝ) by
              exact (Real.rpow_natCast _ 2).symm]
            ring
      _ = (C / 4) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_sub hnR]
        norm_num
  have hlim : Tendsto (fun n : ℕ => (C / 4) * (n : ℝ) ^ (-(2 / 3 : ℝ)))
      atTop (nhds 0) := by simpa using hp.const_mul (C / 4)
  exact hlim.congr' heq.symm

/-- A rational certificate cluster is a subsequential limit of scaled exact rational lower and upper grid certificates whose mesh error vanishes. -/
def RationalCertificateCluster (K : ℕ) (q : RatContrast K)
    (grid procedure prior : ℕ → ℝ) : Prop :=
  ∀ n, ∀ hn : 0 < n,
    ∃ (pi : GridPi K n) (w : GridWeight K n n) (u : ℚ)
      (nu : CountVec K n → ℚ)
      (delta : ∀ r : AllocVec K n, ObsVec r → ℝ),
      ExactGridPrimalDualCertificate q pi w u nu ∧
      IsGridBarycenter q pi w delta ∧
      grid n = secondOrderScale n *
        (C0 (ratContrastToReal q) / n - gridLPValue K n n q hn hn) ∧
      procedure n = secondOrderScale n *
        (C0 (ratContrastToReal q) / n - upperCertificate q pi delta) ∧
      prior n = secondOrderScale n *
        (C0 (ratContrastToReal q) / n - lowerCertificate q nu)

-- @node: thm:second-order-rate-and-certificate-frontier
/-- [there are at least two treatment arms](hyp:hK), [the contrast has at least three active arms](hyp:hsupport), [the scaled second-order excess risk has a nonempty compact cluster set bounded away from zero and above by the stated constant; any convergent positive regularly varying normalization has exponent four thirds, while the exact grid-certificate identification remains an explicit open frontier](goal). -/
theorem second_order_rate_and_certificate_frontier
    (K : ℕ) (c : Contrast ℝ K) (hK : AdmissibleArmCount K)
    (hsupport : 3 ≤ (Sc c).card) :
    let _openFrontier : List String := secondOrderRateAndCertificateOpenFrontier
    0 < liminf (fun n => secondOrderScale n * dN K c n) atTop ∧
    liminf (fun n => secondOrderScale n * dN K c n) atTop ≤
      limsup (fun n => secondOrderScale n * dN K c n) atTop ∧
    limsup (fun n => secondOrderScale n * dN K c n) atTop ≤ 43 * C0 c ∧
    (∃ a : ℝ, ClusterValue (fun n => secondOrderScale n * dN K c n) a) ∧
    IsCompact {a : ℝ | ClusterValue (fun n => secondOrderScale n * dN K c n) a} ∧
    (∀ (a : PositiveSequence) β C, RegularlyVarying a β → 0 < C →
      Tendsto (fun n => a n * dN K c n) atTop (nhds C) → β = 4 / 3) ∧
    ((∃ (a : PositiveSequence) (C : ℝ),
        RegularlyVarying a (4 / 3) ∧ 0 < C ∧
        Tendsto (fun n => a n * dN K c n) atTop (nhds C)) ↔
      SlowlyVaryingEventuallyPositive
        (fun n => secondOrderScale n * dN K c n)) ∧
    (∀ (q : RatContrast K), ratContrastToReal q = c →
      ∃ grid procedure prior : ℕ → ℝ,
        RationalCertificateCluster K q grid procedure prior ∧
        AsymptoticallyCoincident grid (fun n => secondOrderScale n * dN K c n) ∧
        AsymptoticallyCoincident procedure grid ∧
        AsymptoticallyCoincident prior grid) ∧
    (∃ (cq : ℕ → RatContrast K) (B U lower upper : ℕ → ℝ),
      (∀ a, Tendsto (fun n => ratContrastToReal (cq n) a) atTop (nhds (c a))) ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (5 / 6 : ℝ) *
        contrastDistance c (ratContrastToReal (cq n))) atTop (nhds 0) ∧
      (∀ n, 0 < n →
        ∃ (pi : GridPi K n) (w : GridWeight K n n) (u : ℚ)
          (nu : CountVec K n → ℚ)
          (delta : ∀ r : AllocVec K n, ObsVec r → ℝ),
          ExactGridPrimalDualCertificate (cq n) pi w u nu ∧
          IsGridBarycenter (cq n) pi w delta ∧
          B n = lowerCertificate (cq n) nu ∧ U n = upperCertificate (cq n) pi delta ∧
          lower n = (max 0 (Real.sqrt (B n) -
            contrastDistance c (ratContrastToReal (cq n)))) ^ 2 ∧
          upper n = (Real.sqrt (U n) +
            contrastDistance c (ratContrastToReal (cq n))) ^ 2 ∧
          lower n ≤ rhoN K n c ∧ rhoN K n c ≤ upper n) ∧
      AsymptoticallyCoincident
        (fun n => secondOrderScale n * (C0 c / n - lower n))
        (fun n => secondOrderScale n * dN K c n) ∧
      AsymptoticallyCoincident
        (fun n => secondOrderScale n * (C0 c / n - upper n))
        (fun n => secondOrderScale n * dN K c n)) ∧
    (∃ fullRule : Estimator 3 3 cDagger,
      Causalean.Stat.worstCaseRisk
        (fun (p : Procedure 3 3 cDagger) (z : Schedule 3 3) => labeledRisk cDagger p z)
        (Causalean.Experimentation.DesignBased.prodDesign
          (fun _ : Unit 3 => qStarDesign cDagger), fullRule) <
        k3ScalarMinimaxValue 3) := by
  classical
  rcases universal_second_order_rate K c hK with
    ⟨_hlambda, _hlambdaOne, hkappa, _henvelope, hriskExists,
      hliminf, hliminfSup, hlimsup, hindex⟩
  let x : ℕ → ℝ := fun n => secondOrderScale n * dN K c n
  have hC0 : 0 < C0 c := by
    unfold C0
    positivity [Lc_pos c]
  have hxlower : ∀ᶠ n in atTop, C0 c * kappaC c ≤ x n := by
    rcases hriskExists with ⟨N, _htail, hrisk⟩
    filter_upwards [Ici_mem_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
      ((le_max_right N 1).trans hn)
    have hrho : rhoN K n c ≤ C0 c * ((n : ℝ)⁻¹ -
        kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ))) :=
      (Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        (fun p z => p.1.mse_nonneg _ _) (shrinkageProcedure K n c)).trans
          (hrisk n hnN)
    have hd : C0 c * kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤
        dN K c n := by
      unfold dN
      have := sub_le_sub_left hrho (C0 c / (n : ℝ))
      convert this using 1 <;> ring
    have hs0 : 0 ≤ secondOrderScale n := by
      unfold secondOrderScale
      positivity
    have hm := mul_le_mul_of_nonneg_left hd hs0
    dsimp [x]
    calc
      C0 c * kappaC c =
          (secondOrderScale n * (n : ℝ) ^ (-(4 / 3 : ℝ))) *
            (C0 c * kappaC c) := by
              rw [secondOrderScale_mul_inverse n hnpos, one_mul]
      _ = secondOrderScale n *
          (C0 c * kappaC c * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by ring
      _ ≤ secondOrderScale n * dN K c n := hm
  have hxupper : ∀ᶠ n in atTop, x n ≤ 43 * C0 c := by
    filter_upwards [Ici_mem_atTop 8] with n hn
    have hn8 : 8 ≤ n := hn
    have hnpos : 0 < n := Nat.zero_lt_of_lt hn8
    have hd := ((embedded_two_arm_converse K n c hK hnpos).2.2.1 hn8).2.2
    have hs0 : 0 ≤ secondOrderScale n := by
      unfold secondOrderScale
      positivity
    have hm := mul_le_mul_of_nonneg_left hd hs0
    dsimp [x]
    calc
      secondOrderScale n * dN K c n ≤ secondOrderScale n *
          (43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ))) := hm
      _ = 43 * C0 c := by
        rw [show secondOrderScale n *
            (43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ))) =
              (43 * C0 c) * (secondOrderScale n *
                (n : ℝ) ^ (-(4 / 3 : ℝ))) by ring,
          secondOrderScale_mul_inverse n hnpos, mul_one]
  have hxpos : ∀ᶠ n in atTop, 0 < x n :=
    hxlower.mono fun _ hn => (mul_pos hC0 hkappa).trans_le hn
  have hxIcc : ∀ᶠ n in atTop, x n ∈
      Set.Icc (C0 c * kappaC c) (43 * C0 c) :=
    hxlower.and hxupper
  obtain ⟨hcluster, hcompact⟩ :=
    subsequentialLimitSet_nonempty_compact x (C0 c * kappaC c) (43 * C0 c) hxIcc
  refine ⟨(mul_pos hC0 hkappa).trans_le hliminf, hliminfSup, hlimsup,
    ?_, ?_, hindex, ?_, ?_, ?_, ?_⟩
  · simpa [ClusterValue, x] using hcluster
  · simpa [ClusterValue, x] using hcompact
  · constructor
    · rintro ⟨a, C, ha, hC, hconv⟩
      refine ⟨hxpos, ?_⟩
      intro t ht
      let p : ℕ → ℝ := fun n => a n * dN K c n
      have hmap := tendsto_nat_floor_mul_atTop t ht
      have hpRatio : Tendsto (fun n : ℕ =>
          p ⌊t * (n : ℝ)⌋₊ / p n) atTop (nhds 1) := by
        have h := (hconv.comp hmap).div hconv hC.ne'
        change Tendsto (((fun n => a n * dN K c n) ∘
          fun n : ℕ => ⌊t * (n : ℝ)⌋₊) /
            fun n => a n * dN K c n) atTop (nhds 1)
        simpa [p, hC.ne'] using h
      have hratio := ((secondOrderScalePositive_regularlyVarying t ht).mul
        hpRatio).div (ha t ht) (ne_of_gt (Real.rpow_pos_of_pos ht (4 / 3)))
      have heq : (fun n : ℕ => x ⌊t * (n : ℝ)⌋₊ / x n) =ᶠ[atTop]
          (fun n => (secondOrderScalePositive ⌊t * (n : ℝ)⌋₊ /
              secondOrderScalePositive n) *
            (p ⌊t * (n : ℝ)⌋₊ / p n) /
              (a ⌊t * (n : ℝ)⌋₊ / a n)) := by
        filter_upwards [Ici_mem_atTop 1, hmap.eventually (Ici_mem_atTop 1),
          hxpos, hmap.eventually hxpos] with n hn hfn hxn hxf
        have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hn)
        have hfn0 : ⌊t * (n : ℝ)⌋₊ ≠ 0 :=
          Nat.ne_of_gt (Nat.zero_lt_one.trans_le hfn)
        have hdn : dN K c n ≠ 0 := by
          intro hd
          simp [x, hd] at hxn
        have hdf : dN K c ⌊t * (n : ℝ)⌋₊ ≠ 0 := by
          intro hd
          simp [x, hd] at hxf
        simp only [secondOrderScalePositive, hn0, hfn0, ↓reduceIte]
        dsimp [x, p]
        field_simp [ne_of_gt (a.2 n), ne_of_gt (a.2 ⌊t * (n : ℝ)⌋₊),
          hdn, hdf]
        <;> ring
      change Tendsto (fun n : ℕ => x ⌊t * (n : ℝ)⌋₊ / x n) atTop (nhds 1)
      convert hratio.congr' heq.symm using 1
      simp only [mul_one, div_self
        (ne_of_gt (Real.rpow_pos_of_pos ht (4 / 3)))]
    · intro hslow
      let b : PositiveSequence := eventuallyPositivePatch x
      have hbEq : (b : ℕ → ℝ) =ᶠ[atTop] x :=
        eventuallyPositivePatch_eventually_eq x hslow.1
      have hbslow : RegularlyVarying b 0 := by
        intro t ht
        have hmap := tendsto_nat_floor_mul_atTop t ht
        have hratioEq : (fun n : ℕ => b ⌊t * (n : ℝ)⌋₊ / b n) =ᶠ[atTop]
            (fun n : ℕ => x ⌊t * (n : ℝ)⌋₊ / x n) :=
          (hbEq.comp_tendsto hmap).div hbEq
        simpa using (hslow.2 t ht).congr' hratioEq.symm
      let a : PositiveSequence :=
        ⟨fun n => secondOrderScalePositive n / b n,
          fun n => div_pos (secondOrderScalePositive.2 n) (b.2 n)⟩
      have ha : RegularlyVarying a (4 / 3) := by
        simpa [a] using regularlyVarying_div secondOrderScalePositive b
          (4 / 3) 0 secondOrderScalePositive_regularlyVarying hbslow
      refine ⟨a, 1, ha, by norm_num, ?_⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [Ici_mem_atTop 1, hslow.1, hbEq] with n hn hxn hbn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hn)
      have hspos : 0 < secondOrderScale n := by
        have hnR : (0 : ℝ) < n := by
          exact_mod_cast (Nat.zero_lt_one.trans_le hn)
        unfold secondOrderScale
        exact Real.rpow_pos_of_pos hnR _
      have hdn : dN K c n ≠ 0 := by
        intro hd
        simp [x, hd] at hxn
      change 1 = (secondOrderScalePositive n / b n) * dN K c n
      simp only [secondOrderScalePositive, hn0, ↓reduceIte]
      rw [hbn]
      dsimp [x]
      field_simp [hspos.ne', hdn]
  · intro q hq
    choose pi w u nu delta hpd hbar hu hBρ hρU hUu huB hcount halloc hobs
      hasymp using fun m : PositiveNat =>
        rational_contrast_grid_certificate_sandwich K m m q m.2 m.2
    let grid : ℕ → ℝ := fun n => if hn : 0 < n then
      secondOrderScale n *
        (C0 (ratContrastToReal q) / n - (u ⟨n, hn⟩ : ℝ)) else 0
    let procedure : ℕ → ℝ := fun n => if hn : 0 < n then
      secondOrderScale n *
        (C0 (ratContrastToReal q) / n -
          upperCertificate q (pi ⟨n, hn⟩) (delta ⟨n, hn⟩)) else 0
    let prior : ℕ → ℝ := fun n => if hn : 0 < n then
      secondOrderScale n *
        (C0 (ratContrastToReal q) / n -
          lowerCertificate q (nu ⟨n, hn⟩)) else 0
    refine ⟨grid, procedure, prior, ?_, ?_⟩
    · intro n hn
      let m : PositiveNat := ⟨n, hn⟩
      refine ⟨pi m, w m, u m, nu m, delta m, hpd m, hbar m, ?_, ?_, ?_⟩
      · simp only [grid, hn, ↓reduceDIte]
        rw [hu m]
      · simp [procedure, hn, m]
      · simp [prior, hn, m]
    · let B : ℕ → ℝ := fun n => if hn : 0 < n then
        lowerCertificate q (nu ⟨n, hn⟩) else 0
      let U : ℕ → ℝ := fun n => if hn : 0 < n then
        upperCertificate q (pi ⟨n, hn⟩) (delta ⟨n, hn⟩) else 0
      let T : ℕ → ℝ := fun n => if hn : 0 < n then (u ⟨n, hn⟩ : ℝ) else 0
      let r : ℕ → ℝ := fun n => rhoN K n (ratContrastToReal q)
      have hordBT : ∀ᶠ n in atTop, B n ≤ r n ∧ r n ≤ T n := by
        filter_upwards [Ici_mem_atTop 1] with n hn
        have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
        let m : PositiveNat := ⟨n, hnpos⟩
        have htop : rhoN K n (ratContrastToReal q) ≤ (u m : ℝ) := by
          rw [hu m]
          exact (hρU m).trans (hUu m)
        simpa [B, T, r, hnpos, m] using And.intro (hBρ m) htop
      have hmesh := secondOrderScale_mesh_tendsto_zero
        (C0 (ratContrastToReal q))
      have hwidthBT : Tendsto (fun n => secondOrderScale n * (T n - B n))
          atTop (nhds 0) := by
        apply squeeze_zero' (g := fun n =>
          secondOrderScale n *
            (C0 (ratContrastToReal q) / (4 * (n : ℝ) ^ 2)))
        · filter_upwards [hordBT] with n hn
          exact mul_nonneg (by unfold secondOrderScale; positivity)
            (sub_nonneg.mpr (hn.1.trans hn.2))
        · filter_upwards [Ici_mem_atTop 1] with n hn
          have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
          let m : PositiveNat := ⟨n, hnpos⟩
          have hh : secondOrderScale n *
                ((u m : ℝ) - lowerCertificate q (nu m)) ≤
              secondOrderScale n *
                (C0 (ratContrastToReal q) / (4 * (n : ℝ) ^ 2)) := by
            rw [hu m]
            exact mul_le_mul_of_nonneg_left (by linarith [huB m])
              (by unfold secondOrderScale; positivity)
          simpa [B, T, hnpos, m] using hh
        · exact hmesh
      have hBT := asymptoticallyCoincident_of_scaled_sandwich
        secondOrderScale (fun n => C0 (ratContrastToReal q) / n) B r T
        (fun n => by unfold secondOrderScale; positivity) hordBT hwidthBT
      have hordUT : ∀ᶠ n in atTop, U n ≤ U n ∧ U n ≤ T n := by
        filter_upwards [Ici_mem_atTop 1] with n hn
        have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
        let m : PositiveNat := ⟨n, hnpos⟩
        have htop : upperCertificate q (pi m) (delta m) ≤ (u m : ℝ) := by
          rw [hu m]
          exact hUu m
        simpa [U, T, hnpos, m] using
          And.intro (le_refl (upperCertificate q (pi m) (delta m))) htop
      have hwidthUT : Tendsto (fun n => secondOrderScale n * (T n - U n))
          atTop (nhds 0) := by
        apply squeeze_zero' (g := fun n => secondOrderScale n * (T n - B n))
        · filter_upwards [hordUT] with n hn
          exact mul_nonneg (by unfold secondOrderScale; positivity)
            (sub_nonneg.mpr hn.2)
        · filter_upwards [Ici_mem_atTop 1] with n hn
          have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
          let m : PositiveNat := ⟨n, hnpos⟩
          have hs0 : 0 ≤ secondOrderScale n := by
            unfold secondOrderScale
            positivity
          have hBU : lowerCertificate q (nu m) ≤
              upperCertificate q (pi m) (delta m) :=
            (hBρ m).trans (hρU m)
          have hh := mul_le_mul_of_nonneg_left
            (sub_le_sub_left hBU (u m : ℝ)) hs0
          simpa [B, U, T, hnpos, m] using hh
        · exact hwidthBT
      have hUT := asymptoticallyCoincident_of_scaled_sandwich
        secondOrderScale (fun n => C0 (ratContrastToReal q) / n) U U T
        (fun n => by unfold secondOrderScale; positivity) hordUT hwidthUT
      have hpriorGrid : AsymptoticallyCoincident
          (fun n => secondOrderScale n *
            (C0 (ratContrastToReal q) / n - B n))
          (fun n => secondOrderScale n *
            (C0 (ratContrastToReal q) / n - T n)) := by
        apply hwidthBT.congr'
        filter_upwards [hordBT] with n hn
        rw [abs_of_nonneg]
        · ring
        · have hs0 : 0 ≤ secondOrderScale n := by
            unfold secondOrderScale
            positivity
          nlinarith
      refine ⟨?_, ?_, ?_⟩
      · apply hBT.2.congr'
        filter_upwards [Ici_mem_atTop 1] with n hn
        have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
        simp [grid, T, r, hq, dN, hnpos]
      · apply hUT.2.congr'
        filter_upwards [Ici_mem_atTop 1] with n hn
        have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
        simp [procedure, grid, U, T, AsymptoticallyCoincident,
          abs_sub_comm, hnpos]
      · apply hpriorGrid.congr'
        filter_upwards [Ici_mem_atTop 1] with n hn
        have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
        simp [prior, grid, B, T, AsymptoticallyCoincident,
          abs_sub_comm, hnpos]
  · rcases (real_contrast_grid_certificate_transfer K c hK).2.1 with
      ⟨cq, B, U, Rminus, Rplus, hcq, heta, hcert, hwidth⟩
    refine ⟨cq, B, U, Rminus, Rplus, hcq, heta, ?_, ?_⟩
    · intro n hn
      rcases hcert n hn with
        ⟨pi, w, u, nu, delta, upperProcedure, schedulePrior,
          hpd, hbar, hB, hU, _hu, _hBρq, _hρqU, _hUu, _huB,
          hRm, hRp, hRmρ, hρRp, _hgap, _hupper, _hprior⟩
      exact ⟨pi, w, u, nu, delta, hpd, hbar, hB, hU, hRm, hRp, hRmρ, hρRp⟩
    · have hord : ∀ᶠ n in atTop,
          Rminus n ≤ rhoN K n c ∧ rhoN K n c ≤ Rplus n := by
        filter_upwards [Ici_mem_atTop 1] with n hn
        rcases hcert n hn with
          ⟨pi, w, u, nu, delta, upperProcedure, schedulePrior,
            hpd, hbar, hB, hU, hu, hBρq, hρqU, hUu, huB,
            hRm, hRp, hRmρ, hρRp, hgap, hupper, hprior⟩
        exact ⟨hRmρ, hρRp⟩
      have hsand := asymptoticallyCoincident_of_scaled_sandwich
        secondOrderScale (fun n => C0 c / n) Rminus
          (fun n => rhoN K n c) Rplus
        (fun n => by unfold secondOrderScale; positivity) hord hwidth
      simpa [AsymptoticallyCoincident, dN] using hsand
  · rcases k3_scalar_score_not_minimax_preserving with
      ⟨_, _, hk3val, _, _, hfull, _⟩
    rcases hfull with ⟨fullRule, hrisk⟩
    refine ⟨fullRule, ?_⟩
    rw [hrisk]
    exact
      calc
        (fullDataRuleRiskBound : ℝ) < (scalarBayesCertificate : ℝ) :=
          k3_rational_separation.1
        _ < k3ScalarMinimaxValue 3 := by
          rw [hk3val]
          have hsqrt : Real.sqrt 3 < (117787 : ℝ) / 68000 := by
            rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 117787 / 68000)]
            norm_num
          norm_num [scalarBayesCertificate]
          linarith

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
