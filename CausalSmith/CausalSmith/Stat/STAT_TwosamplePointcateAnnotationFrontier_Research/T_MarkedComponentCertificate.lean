module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MarkedMembership
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.MixtureInformation

/-!
# T_MarkedComponentCertificate

Two-channel point-CATE annotation frontier: T_MarkedComponentCertificate
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


/-- Equal treatment-record marginals identify the entire designated propensity on the cube.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input Q](hyp:Q), [the specified input hP](hyp:hP), [the specified input hQ](hyp:hQ), [the specified input hxa](hyp:hxa), [the designated propensity eq of xa law conclusion](goal) holds. -/
lemma designatedPropensity_eq_of_xaLaw {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P Q : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (hQ : PrimitiveClass alpha beta gamma L eps Q) (hxa : xaLaw P = xaLaw Q) :
    Set.EqOn (designatedPropensity P hP) (designatedPropensity Q hQ) (cube d) := by
  let W := canonicalLaw P hP
  let V := canonicalLaw Q hQ
  have hW := canonicalLaw_spec P hP
  have hV := canonicalLaw_spec Q hQ
  have hWu : W.law.map Prod.fst = uniformLaw d := hW.2.1
  have hVu : V.law.map Prod.fst = uniformLaw d := hV.2.1
  let : IsFiniteMeasure (uniformLaw d) := by
    rw [← hWu]
    infer_instance
  let := bernKernel_sfinite_of_margin W (fun w => w.2.1) (by fun_prop)
    W.e W.measurable_e W.margin_e
  let := bernKernel_sfinite_of_margin V (fun w => w.2.1) (by fun_prop)
    V.e V.measurable_e V.margin_e
  have he : Set.EqOn W.e V.e (cube d) := by
    apply bern_margin_versions_unique _ _ W.measurable_e V.measurable_e
      (holderNorm_continuousOn _ _ _ hW.2.2.2.2.1)
      (holderNorm_continuousOn _ _ _ hV.2.2.2.2.1)
    · exact hW.2.2.2.1.unit
    · exact hV.2.2.2.1.unit
    · calc
        (uniformLaw d) ⊗ₘ bernKernel W.e W.measurable_e = xaLaw W := by
          rw [← hWu, ← W.margin_e]
          rfl
        _ = xaLaw V := by
          simpa only [xaLaw, W, V, hW.1, hV.1] using hxa
        _ = (uniformLaw d) ⊗ₘ bernKernel V.e V.measurable_e := by
          rw [xaLaw, V.margin_e, hVu]
  intro x hx
  simpa only [designatedPropensity, if_pos hx] using he hx

/-- The sign involution preserves the law of the designated, continuous propensity function.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input hMembers](hyp:hMembers), [the marked designated propensity marginal conclusion](goal) holds. -/
lemma marked_designated_propensity_marginal (d : ℕ) (alpha beta gamma L eps h delta a b : ℝ)
    (hMembers : ∀ theta sigma,
      PrimitiveClass alpha beta gamma L eps ((markedHandle d h delta a b).law theta sigma)) :
    let H := markedHandle d h delta a b
    (signPrior H true).map (fun sigma =>
      fun x : {x : Cov d // x ∈ cube d} =>
        designatedPropensity (H.law true sigma) (hMembers true sigma) x.1) =
    (signPrior H false).map (fun sigma =>
      fun x : {x : Cov d // x ∈ cube d} =>
        designatedPropensity (H.law false sigma) (hMembers false sigma) x.1) := by
  dsimp only
  unfold signPrior
  rw [Measure.map_finset_sum' (measurable_of_countable _).aemeasurable,
    Measure.map_finset_sum' (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' (measurable_of_countable _)]
  apply Fintype.sum_equiv (flipOutcomeSigns d h delta)
  intro sigma
  change ENNReal.ofReal (markedWeight h delta true sigma) • _ =
    ENNReal.ofReal (markedWeight h delta false (flipOutcomeSigns d h delta sigma)) • _
  rw [markedWeight_flipOutcomeSigns]
  congr 2
  funext x
  exact designatedPropensity_eq_of_xaLaw _ _ (hMembers true sigma)
    (hMembers false (flipOutcomeSigns d h delta sigma))
    (marked_xaLaw_flipOutcomeSigns d h delta a b sigma) x.2

/-- The prescribed macro bump equals one at the target, giving the signed contrast.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the marked contrast at target conclusion](goal) holds. -/
lemma marked_contrast_at_target (d : ℕ) (h a b : ℝ) (theta : Bool) :
    markedContrast (d := d) h a b theta (x0 d) = -2 * thetaSign theta * a * b := by
  simp [markedContrast, macroBump, x0, flatExp, Real.exp_ne_zero]

-- @node: thm:marked-component-certificate
/-- The explicit sign-pair construction satisfies membership, exact cancellations,
component factorization and the fixed-size information bound.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the marked component certificate conclusion](goal) holds. -/
theorem marked_component_certificate (d : ℕ) (alpha beta gamma L eps : ℝ)
    (hdom : PublicDomain d alpha beta gamma L eps) :
    ∃ c c0 C : ℝ,
      0 < c ∧ c ≤ 1 ∧ 0 < c0 ∧ 0 < C ∧ -- @realizes c(admissibility constant) @realizes c0(occupancy constant) @realizes C(information constant)
      ∀ (n m : ℕ) (h delta a b : ℝ),
        2 ≤ n → 0 < delta → delta ≤ h → h ≤ 1/2 →
        0 < a → a ≤ c*delta^alpha → 0 < b → b ≤ c*delta^beta →
        a*b ≤ c*h^gamma → ((n:ℝ)+m)*delta^d ≤ c0 →
        let H := markedHandle d h delta a b
        (∀ theta, (∀ sigma : PriorSign H, 0 ≤ H.weight theta sigma) ∧
          (∑ sigma : PriorSign H, H.weight theta sigma) = 1) ∧ -- @realizes Pi(probability-vector normalization)
        (∃ hMembers : ∀ theta sigma, PrimitiveClass alpha beta gamma L eps (H.law theta sigma),
          (∀ theta sigma x, x ∈ cube d →
            tau (H.law theta sigma) (hMembers theta sigma) x = H.contrast theta x) ∧
          (signPrior H true).map (fun sigma =>
            fun x : {x : Cov d // x ∈ cube d} => designatedPropensity (H.law true sigma) (hMembers true sigma) x.1) =
          (signPrior H false).map (fun sigma =>
            fun x : {x : Cov d // x ∈ cube d} => designatedPropensity (H.law false sigma) (hMembers false sigma) x.1)) ∧
        (∀ theta, H.contrast theta (x0 d) = -2*thetaSign theta*a*b) ∧
        (H.contrast false (x0 d)-H.contrast true (x0 d) = 4*a*b ∧ c*a*b ≤ 4*a*b) ∧
        hellingerSq (markedMixture H true n m) (markedMixture H false n m) ≤
          C*(n:ℝ)*((n:ℝ)+m)*h^d*delta^d*a^2*b^2 ∧
        (∀ kAux, auxiliaryMixture H true kAux = auxiliaryMixture H false kAux ∧
          ∀ x : Fin kAux → Cov d, (∀ i, x i ∈ cube d) →
            conditionalAuxiliaryMixture H true kAux x = conditionalAuxiliaryMixture H false kAux x) ∧
        (∀ theta x, x ∈ cube d → singletonMixture H theta x = fairObserved) ∧
        ConditionalFactorization H h delta n m ∧ UninformativeComponentsAgree H h delta n m  := by
  obtain ⟨cM, hcM, hcM1, hmem⟩ := marked_membership d alpha beta gamma L eps hdom
  obtain ⟨cS, hcS, hcS1, hsingle⟩ := singleton_cancellation d alpha beta gamma L eps hdom
  obtain ⟨cU, hcU, hcU1, huninform⟩ := uninformative_component_equality d alpha beta gamma L eps hdom
  obtain ⟨cI, c0, C, hcI, hcI1, hc0, hC, hinfo⟩ :=
    marked_information_bound d alpha beta gamma L eps hdom
  let c := min cM (min cS (min cU cI))
  have hc : 0 < c := lt_min hcM (lt_min hcS (lt_min hcU hcI))
  have hc1 : c ≤ 1 := (min_le_left _ _).trans hcM1
  have hcM' : c ≤ cM := min_le_left _ _
  have hcS' : c ≤ cS := (min_le_right _ _).trans (min_le_left _ _)
  have hcU' : c ≤ cU := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcI' : c ≤ cI := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨c, c0, C, hc, hc1, hc0, hC, ?_⟩
  intro n m h delta a b hn hd hdh hh ha hac hb hbc hab hocc
  have hh0 : 0 < h := hd.trans_le hdh
  have hamp (c' : ℝ) (hcc : c ≤ c') :
      a ≤ c'*delta^alpha ∧ b ≤ c'*delta^beta ∧ a*b ≤ c'*h^gamma := by
    exact ⟨hac.trans (mul_le_mul_of_nonneg_right hcc (Real.rpow_pos_of_pos hd _).le),
      hbc.trans (mul_le_mul_of_nonneg_right hcc (Real.rpow_pos_of_pos hd _).le),
      hab.trans (mul_le_mul_of_nonneg_right hcc (Real.rpow_pos_of_pos hh0 _).le)⟩
  have hm := hamp cM hcM'
  have hs := hamp cS hcS'
  have hu := hamp cU hcU'
  have hi := hamp cI hcI'
  have hmembers := hmem h delta a b hd hdh hh ha hm.1 hb hm.2.1 hm.2.2
  let hMembers : ∀ theta sigma,
      PrimitiveClass alpha beta gamma L eps ((markedHandle d h delta a b).law theta sigma) :=
    fun theta sigma => (hmembers theta sigma).choose
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro theta
    exact marked_prior_mass d h delta theta
  · refine ⟨hMembers, ?_, marked_designated_propensity_marginal d alpha beta gamma L eps h delta a b hMembers⟩
    intro theta sigma x hx
    exact (hmembers theta sigma).choose_spec.1 x hx
  · intro theta
    exact marked_contrast_at_target d h a b theta
  · constructor
    · change markedContrast h a b false (x0 d) - markedContrast h a b true (x0 d) = _
      rw [marked_contrast_at_target, marked_contrast_at_target]
      norm_num [thetaSign]
      <;> ring
    · calc
        c*a*b = c*(a*b) := by ring
        _ ≤ 4*(a*b) := mul_le_mul_of_nonneg_right
          (hc1.trans (by norm_num : (1:ℝ) ≤ 4)) (mul_pos ha hb).le
        _ = 4*a*b := by ring
  · exact hinfo n m h delta a b hn hd hdh hh ha hi.1 hb hi.2.1 hi.2.2 hocc
  · intro kAux
    refine ⟨(auxiliary_only_equality d h delta a b kAux).1, ?_⟩
    intro x _
    exact (auxiliary_only_equality d h delta a b kAux).2 x
  · intro theta x _
    exact hsingle h delta a b hd hdh hh ha hs.1 hb hs.2.1 hs.2.2 theta x
  · exact marked_conditional_factorization d h delta a b hd hdh hh n m
  · exact huninform h delta a b hd hdh hh ha hu.1 hb hu.2.1 hu.2.2 n m

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
