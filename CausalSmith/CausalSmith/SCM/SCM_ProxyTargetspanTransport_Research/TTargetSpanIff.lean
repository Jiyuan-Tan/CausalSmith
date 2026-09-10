import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TPositiveFullLawConverse

set_option linter.unusedDecidableInType false

/-! Target-span characterization of point identification. -/

open Matrix

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]

-- @node: exists_failureSeparator_of_balancingFiber_empty
/-- Given [emptiness of the balancing fiber](hyp:hempty), [an empty balancing fiber yields a left-null separator whose target inner product is nonzero](goal). -/
lemma exists_failureSeparator_of_balancingFiber_empty (Bx : Matrix W E ℝ) (bvec : W → ℝ)
    (hempty : ¬ (balancingFiber Bx bvec).Nonempty) :
    (failureSeparator Bx bvec).Nonempty := by
  have hb : bvec ∉ Bx.mulVecLin.range := by
    intro hb
    obtain ⟨lam, hlam⟩ := hb
    exact hempty ⟨lam, hlam⟩
  obtain ⟨f, hfb, hf⟩ := Submodule.exists_le_ker_of_notMem hb
  let h : W → ℝ := fun w => f (Pi.single w 1)
  have hdot : ∀ v : W → ℝ, dotProduct h v = f v := by
    intro v
    calc
      dotProduct h v = ∑ w, f (v w • Pi.single w (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro w _
        simp [h, dotProduct, mul_comm]
      _ = f (∑ w, v w • Pi.single w (1 : ℝ)) := by rw [map_sum]
      _ = f v := by
        congr 1
        ext w
        simp [Pi.single_apply, mul_comm]
  refine ⟨h, ?_, ?_⟩
  · ext e
    rw [show Bx.vecMul h e = dotProduct h (fun w => Bx w e) by rfl, hdot]
    apply hf
    refine ⟨Pi.single e 1, ?_⟩
    ext w
    simp [Matrix.mulVec]
  · simpa [hdot bvec] using hfb

-- @node: identified_value_of_balancing
/-- Given [the positive latent-shift condition, membership of the chosen weights in the balancing fiber](hyp:hM,hlam), [every balancing vector evaluates the transported interventional probability through the observable outcome-moment vector](goal). -/
lemma identified_value_of_balancing (Mdl : LatentShiftSCM E U W X Y)
    (hM : PositiveLatentShiftClass Mdl) (x : X) (y : Y)
    (lam : E → ℝ)
    (hlam : lam ∈ balancingFiber (condProxyMatrix Mdl x) (targetProxyVector Mdl)) :
    interventionalProb Mdl x y = dotProduct (condOutcomeVector Mdl x y) lam := by
  obtain ⟨hB, hb, hc, htheta, _⟩ := observable_factorization Mdl hM x y
  have hinj : Function.Injective Mdl.M.mulVec := by
    rw [Matrix.mulVec_injective_iff, linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols]
    exact hM.proxy_injective.symm
  have hR : (latentPosterior Mdl x).mulVec lam = Mdl.q := by
    apply hinj
    rw [Matrix.mulVec_mulVec, ← hB, hlam, ← hb]
  rw [htheta, ← hR, Matrix.dotProduct_mulVec, ← hc]

-- @node: thm:target-span-iff
/-- Given [nonemptiness of the compatible fiber, membership of the reference model in that fiber, injectivity of the reference proxy channel](hyp:hne,hM0,hinj), [within a nonempty compatible fiber with an injective proxy channel, point identification is equivalent to target-span balancing, and every balancing vector gives the common identified value](goal). -/
theorem target_span_iff (PO : E → W → X → Y → ℝ) (bvec : W → ℝ)
    (hne : (compatibleFiber (U := U) PO bvec).Nonempty)
    (M0 : LatentShiftSCM E U W X Y) (hM0 : M0 ∈ compatibleFiber PO bvec)
    (hinj : ProxyChannelInjectivity M0) (x : X) (y : Y) :
    ((Set.Subsingleton
        (Causalean.PartialID.IdentifiedInterval
          (fun M : LatentShiftSCM E U W X Y => interventionalProb M x y)
          (fun M => M ∈ compatibleFiber PO bvec))) ↔
      (balancingFiber (condProxyMatrix M0 x) bvec).Nonempty) ∧
    (∀ lam : E → ℝ, lam ∈ balancingFiber (condProxyMatrix M0 x) bvec →
      ∀ Mdl : LatentShiftSCM E U W X Y, Mdl ∈ compatibleFiber PO bvec →
        interventionalProb Mdl x y = dotProduct (condOutcomeVector Mdl x y) lam) ∧
    (∀ lam : E → ℝ, lam ∈ balancingFiber (condProxyMatrix M0 x) bvec →
      ∀ lam' : E → ℝ, lam' ∈ balancingFiber (condProxyMatrix M0 x) bvec →
        dotProduct (condOutcomeVector M0 x y) lam =
          dotProduct (condOutcomeVector M0 x y) lam') := by
  have hBcompat : ∀ M : LatentShiftSCM E U W X Y, M ∈ compatibleFiber PO bvec →
      condProxyMatrix M x = condProxyMatrix M0 x := by
    intro M hM
    unfold condProxyMatrix
    rw [hM.2.1, hM0.2.1]
  have hccompat : ∀ M : LatentShiftSCM E U W X Y, M ∈ compatibleFiber PO bvec →
      condOutcomeVector M x y = condOutcomeVector M0 x y := by
    intro M hM
    unfold condOutcomeVector
    rw [hM.2.1, hM0.2.1]
  have hvalue : ∀ lam : E → ℝ,
      lam ∈ balancingFiber (condProxyMatrix M0 x) bvec →
      ∀ M : LatentShiftSCM E U W X Y, M ∈ compatibleFiber PO bvec →
        interventionalProb M x y = dotProduct (condOutcomeVector M x y) lam := by
    intro lam hlam M hM
    apply identified_value_of_balancing M hM.1 x y lam
    change (condProxyMatrix M x).mulVec lam = targetProxyVector M
    rw [hBcompat M hM, hM.2.2]
    exact hlam
  constructor
  · constructor
    · intro hsub
      by_contra hempty
      obtain ⟨M, hM⟩ := hne
      obtain ⟨h, hh⟩ := exists_failureSeparator_of_balancingFiber_empty
        (condProxyMatrix M0 x) bvec hempty
      have hBM : condProxyMatrix M x = condProxyMatrix M0 x := hBcompat M hM
      have hoff : ∀ lam, (condProxyMatrix M x).mulVec lam ≠ bvec := by
        intro lam hlam
        apply hempty
        refine ⟨lam, ?_⟩
        change (condProxyMatrix M0 x).mulVec lam = bvec
        rw [← hBM]
        exact hlam
      have hhM : h ∈ failureSeparator (condProxyMatrix M x) bvec := by
        simpa [hBM] using hh
      letI : Nontrivial Y := Fintype.one_lt_card_iff_nontrivial.mp
        (lt_of_lt_of_le (by omega : 1 < 2) M.outcome_card)
      let ycirc : Y := Classical.choose (exists_ne y)
      have hy : ycirc ≠ y := Classical.choose_spec (exists_ne y)
      let wstar : W := Classical.choice (Fintype.card_pos_iff.mp
        (lt_of_lt_of_le (lt_of_lt_of_le (by omega : 0 < 2) M.latent_card) M.proxy_card))
      obtain ⟨ε, hε, _, hinterval⟩ := positive_full_law_converse PO bvec ⟨M, hM⟩ M hM
        hM.1.factorization hM.1.target_invariance hM.1.positivity hM.1.proxy_injective
        x y ycirc hy wstar hoff h hhM
      have hslope : 0 < ε * |dotProduct h bvec| := mul_pos hε (abs_pos.mpr hh.2)
      have hlo : interventionalProb M x y - ε * |dotProduct h bvec| <
          interventionalProb M x y := by linarith
      have hhi : interventionalProb M x y <
          interventionalProb M x y + ε * |dotProduct h bvec| := by linarith
      have hmid := hinterval ⟨hlo, hhi⟩
      let zleft := interventionalProb M x y - (ε * |dotProduct h bvec|) / 2
      have hzleft : zleft ∈ Set.Ioo
          (interventionalProb M x y - ε * |dotProduct h bvec|)
          (interventionalProb M x y + ε * |dotProduct h bvec|) := by
        dsimp [zleft]
        constructor <;> linarith
      have hleft := hinterval hzleft
      have hneleft : zleft ≠ interventionalProb M x y := by
        dsimp [zleft]
        linarith
      exact hneleft (hsub hleft hmid)
    · intro hspan
      rintro z ⟨⟨M, hM⟩, rfl⟩ z' ⟨⟨M', hM'⟩, rfl⟩
      change interventionalProb M x y = interventionalProb M' x y
      obtain ⟨lam, hlam⟩ := hspan
      rw [hvalue lam hlam M hM, hvalue lam hlam M' hM',
        hccompat M hM, hccompat M' hM']
  · constructor
    · exact hvalue
    · intro lam hlam lam' hlam'
      rw [← hvalue lam hlam M0 hM0, ← hvalue lam' hlam' M0 hM0]

end CausalSmith.SCM.ProxyTargetspanTransport
