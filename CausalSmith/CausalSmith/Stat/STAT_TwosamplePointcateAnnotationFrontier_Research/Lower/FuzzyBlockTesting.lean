module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationMoments
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.Likelihood

/-!
# Fuzzy testing on one full data block

Transport the cited product-experiment testing inequality to a single observation
consisting of the entire original-record dataset, with its randomizer included.
The finite-prior identities preserve the marked information bound under this
randomization and express the two mixtures using a common product prior.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.haveILetI false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Squared Hellinger distance is invariant under a measurable embedding.  Given [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the hellinger sq map embedding conclusion](goal) holds. -/
lemma hellingerSq_map_embedding {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (B C : Measure Ω) [IsFiniteMeasure B] [IsFiniteMeasure C]
    (f : Ω → Ξ) (hf : MeasurableEmbedding f) :
    hellingerSq (B.map f) (C.map f) = hellingerSq B C := by
  have hb := hf.rnDeriv_map B (B+C)
  have hc := hf.rnDeriv_map C (B+C)
  unfold hellingerSq Causalean.Stat.hellingerSqDensity
  rw [← Measure.map_add _ _ hf.measurable, hf.integral_map]
  apply integral_congr_ae
  filter_upwards [hb, hc] with x hxB hxC
  rw [hxB, hxC]

/-- Replicating a value in a singleton coordinate is a measurable embedding.  [the measurable embedding singleton coordinate conclusion](goal) holds. -/
lemma measurableEmbedding_singleton_coordinate {Ω : Type*} [MeasurableSpace Ω] :
    MeasurableEmbedding (fun x : Ω => fun _ : Fin 1 => x) := by
  have he : (fun x : Ω => fun _ : Fin 1 => x) =
      (MeasurableEquiv.piUnique (fun _ : Fin 1 => Ω)).symm := by
    funext x i
    simp
  rw [he]
  exact (MeasurableEquiv.piUnique (fun _ : Fin 1 => Ω)).symm.measurableEmbedding

/-- A singleton product is the image of its only coordinate law.  Given [the specified input P](hyp:P), [the pi one eq map constant conclusion](goal) holds. -/
lemma pi_one_eq_map_constant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    Measure.pi (fun _ : Fin 1 => P) = P.map (fun x => fun _ : Fin 1 => x) := by
  exact (MeasurePreserving.symm (MeasurableEquiv.piUnique (fun _ : Fin 1 => Ω))
    (measurePreserving_piUnique (fun _ : Fin 1 => P))).map_eq.symm

/-- One-coordinate product experiments have the original Hellinger distance.  Given [the specified input B](hyp:B), [the specified input C](hyp:C), [the hellinger sq pi one conclusion](goal) holds. -/
lemma hellingerSq_pi_one {Ω : Type*} [MeasurableSpace Ω]
    (B C : Measure Ω) [IsFiniteMeasure B] [IsFiniteMeasure C] :
    hellingerSq (Measure.pi (fun _ : Fin 1 => B))
      (Measure.pi (fun _ : Fin 1 => C)) = hellingerSq B C := by
  rw [pi_one_eq_map_constant, pi_one_eq_map_constant]
  exact hellingerSq_map_embedding B C _
    measurableEmbedding_singleton_coordinate

/-- Mixing singleton experiments commutes with their constant-coordinate encoding.  Given [the specified input Z](hyp:Z), [the specified input K](hyp:K), [the bind pi one eq map conclusion](goal) holds. -/
lemma bind_pi_one_eq_map {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (ω : Measure Z) (K : Kernel Z Ω) :
    ω.bind (fun z => Measure.pi (fun _ : Fin 1 => K z)) =
      (ω.bind (fun z => K z)).map (fun x => fun _ : Fin 1 => x) := by
  rw [Measure.map_comp ω K (by fun_prop)]
  congr 1
  funext z
  rw [Kernel.map_apply _ (by fun_prop), pi_one_eq_map_constant]

/-- The cited fuzzy-testing result applies to one entire data block and every
measurable decision on that block, without an additional independence assumption.  Given [the specified input Z](hyp:Z), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input Model](hyp:Model), [the specified input hB](hyp:hB), [the specified input hC](hyp:hC), [the specified input s](hyp:s), [the specified input u](hyp:u), [the specified input hs](hyp:hs), [the specified input hu](hyp:hu), [the specified input hu2](hyp:hu2), [the specified input hsep](hyp:hsep), [the specified input hhell](hyp:hhell), [the specified input T](hyp:T), [the specified input hT](hyp:hT), [the published fuzzy testing block conclusion](goal) holds. -/
lemma published_fuzzy_testing_block
    {Ω Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    (ω : Measure Z) [IsProbabilityMeasure ω] (B C : Kernel Z Ω)
    [IsMarkovKernel B] [IsMarkovKernel C]
    (Model : Set (Measure Ω)) (hB : ∀ z, B z ∈ Model) (hC : ∀ z, C z ∈ Model)
    (Ψ : Measure Ω → ℝ) (s u : ℝ) (hs : 0 < s) (hu : 0 ≤ u) (hu2 : u < 2)
    (hsep : ∀ z z', s ≤ Ψ (B z) - Ψ (C z'))
    (hhell : hellingerSq (ω.bind (fun z => B z)) (ω.bind (fun z => C z)) ≤ u)
    (T : Ω → ℝ) (hT : Measurable T) :
    ENNReal.ofReal ((s/4)*(1-Real.sqrt (u*(1-u/4)))) ≤
      ⨆ (P : Measure Ω) (_ : P ∈ Model), ∫⁻ w, ENNReal.ofReal |T w - Ψ P| ∂P := by
  have hpi : hellingerSq (ω.bind (fun z => Measure.pi (fun _ : Fin 1 => B z)))
      (ω.bind (fun z => Measure.pi (fun _ : Fin 1 => C z))) ≤ u := by
    rw [bind_pi_one_eq_map, bind_pi_one_eq_map, hellingerSq_map_embedding _ _ _
      measurableEmbedding_singleton_coordinate]
    exact hhell
  have htest := PublishedFuzzyTesting Ω Z ω B C 1 (by norm_num) Model hB hC Ψ s u hs hu hu2
    hsep hpi (fun w => T (w 0)) (by fun_prop)
  convert htest using 1
  congr 1
  funext P
  congr 1
  funext hP
  rw [pi_one_eq_map_constant, measurableEmbedding_singleton_coordinate.lintegral_map]

/-- A testing bound on the image of an indexed model class bounds its original
minimax risk when the target is well defined on the experiment laws.  Given [the specified input Z](hyp:Z), [the specified input B](hyp:B), [the specified input C](hyp:C), [the specified input E](hyp:E), [the specified input target](hyp:target), [the specified input hTarget](hyp:hTarget), [the specified input hB](hyp:hB), [the specified input hC](hyp:hC), [the specified input s](hyp:s), [the specified input u](hyp:u), [the specified input hs](hyp:hs), [the specified input hu](hyp:hu), [the specified input hu2](hyp:hu2), [the specified input hsep](hyp:hsep), [the specified input hhell](hyp:hhell), [the published fuzzy testing minimax conclusion](goal) holds. -/
lemma published_fuzzy_testing_minimax
    {Ω Z Θ : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    (ω : Measure Z) [IsProbabilityMeasure ω] (B C : Kernel Z Ω)
    [IsMarkovKernel B] [IsMarkovKernel C]
    (E : Θ → Measure Ω) (target : Θ → ℝ) (Ψ : Measure Ω → ℝ)
    (hTarget : ∀ θ, Ψ (E θ) = target θ)
    (hB : ∀ z, ∃ θ, B z = E θ) (hC : ∀ z, ∃ θ, C z = E θ)
    (s u : ℝ) (hs : 0 < s) (hu : 0 ≤ u) (hu2 : u < 2)
    (hsep : ∀ z z', s ≤ Ψ (B z) - Ψ (C z'))
    (hhell : hellingerSq (ω.bind (fun z => B z)) (ω.bind (fun z => C z)) ≤ u) :
    ENNReal.ofReal ((s/4)*(1-Real.sqrt (u*(1-u/4)))) ≤
      Causalean.Stat.minimaxValueENNReal
        (fun (T : {f : Ω → ℝ // Measurable f}) θ =>
          ∫⁻ w, ENNReal.ofReal |T.1 w - target θ| ∂E θ) := by
  apply Causalean.Stat.le_minimaxValueENNReal
  intro T
  have htest := published_fuzzy_testing_block ω B C (Set.range E)
    (fun z => by obtain ⟨θ, hθ⟩ := hB z; exact ⟨θ, hθ.symm⟩)
    (fun z => by obtain ⟨θ, hθ⟩ := hC z; exact ⟨θ, hθ.symm⟩)
    Ψ s u hs hu hu2 hsep hhell T.1 T.2
  apply htest.trans
  apply iSup_le
  intro P
  apply iSup_le
  rintro ⟨θ, rfl⟩
  rw [hTarget]
  exact Causalean.Stat.le_worstCaseRiskENNReal T θ

/-- At the certificate's Hellinger budget, the testing overlap is at least
three quarters.  [the fuzzy testing overlap sixteenth conclusion](goal) holds. -/
lemma fuzzy_testing_overlap_sixteenth :
    (3:ℝ)/4 ≤ 1-Real.sqrt ((1/16:ℝ)*(1-(1/16:ℝ)/4)) := by
  have hroot : Real.sqrt ((1/16:ℝ)*(1-(1/16:ℝ)/4)) ≤ 1/4 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  linarith


/-- The prescribed finite marked mixture has unit mass.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the marked mixture probability conclusion](goal) holds. -/
lemma markedMixture_probability (d n m : ℕ) (h delta a b : ℝ) (theta : Bool) :
    IsProbabilityMeasure (markedMixture (markedHandle d h delta a b) theta n m) := by
  obtain ⟨hw, hsum⟩ := marked_prior_mass d h delta theta
  constructor
  have hobs (sigma : SignArray d h delta) := obsLaw_probability (markedLaw h delta a b theta sigma)
  have hxa (sigma : SignArray d h delta) := xaLaw_probability (markedLaw h delta a b theta sigma)
  simp only [markedMixture, markedHandle, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  change (∑ sigma : SignArray d h delta, ENNReal.ofReal (markedWeight h delta theta sigma)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun sigma _ => hw sigma), hsum]
  norm_num

/-- Appending the same randomizer commutes with the marked finite prior.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the marked mixture prod randomizer conclusion](goal) holds. -/
lemma markedMixture_prod_randomizer {d n m : ℕ} (H : MarkedPriors d) (theta : Bool) :
    (markedMixture H theta n m).prod (volume.restrict (Icc (0:ℝ) 1)) =
      ∑ sigma : PriorSign H, ENNReal.ofReal (H.weight theta sigma) •
        experiment (H.law theta sigma) n m := by
  unfold markedMixture experiment
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [Measure.prod_smul_left]

/-- The marked information bound holds unchanged on randomized original records.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the marked mixture randomized hellinger conclusion](goal) holds. -/
lemma markedMixture_randomized_hellinger (d n m : ℕ) (h delta a b : ℝ) :
    hellingerSq
      (∑ sigma : SignArray d h delta, ENNReal.ofReal (markedWeight h delta true sigma) •
        experiment ((markedHandle d h delta a b).law true sigma) n m)
      (∑ sigma : SignArray d h delta, ENNReal.ofReal (markedWeight h delta false sigma) •
        experiment ((markedHandle d h delta a b).law false sigma) n m) =
      hellingerSq (markedMixture (markedHandle d h delta a b) true n m)
        (markedMixture (markedHandle d h delta a b) false n m) := by
  let := population_randomizer_probability
  let := markedMixture_probability d n m h delta a b true
  let := markedMixture_probability d n m h delta a b false
  exact (congrArg₂ hellingerSq
    (markedMixture_prod_randomizer (n:=n) (m:=m) (markedHandle d h delta a b) true).symm
    (markedMixture_prod_randomizer (n:=n) (m:=m) (markedHandle d h delta a b) false).symm).trans
      (hellingerSq_prod_probability _ _ _)

/-- The first family under the product prior has exactly its own prior mixture.  Given [the specified input Z](hyp:Z), [the specified input W](hyp:W), [the specified input K](hyp:K), [the bind product prior fst conclusion](goal) holds. -/
lemma bind_product_prior_fst {Z W Ω : Type*} [MeasurableSpace Z]
    [MeasurableSpace W] [MeasurableSpace Ω] (ω : Measure Z) (ν : Measure W)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure ν] (K : Kernel Z Ω) :
    (ω.prod ν).bind (fun z => K z.1) = ω.bind (fun z => K z) := by
  ext s hs
  rw [Measure.bind_apply hs
      (show AEMeasurable (fun z : Z × W => K z.1) (ω.prod ν) from by fun_prop),
    Measure.bind_apply hs K.aemeasurable,
    lintegral_prod (fun z : Z × W => K z.1 s)
      (show AEMeasurable (fun z : Z × W => K z.1 s) (ω.prod ν) from
        ((K.measurable_coe hs).comp measurable_fst).aemeasurable)]
  simp

/-- The second family under the product prior has exactly its own prior mixture.  Given [the specified input Z](hyp:Z), [the specified input W](hyp:W), [the specified input K](hyp:K), [the bind product prior snd conclusion](goal) holds. -/
lemma bind_product_prior_snd {Z W Ω : Type*} [MeasurableSpace Z]
    [MeasurableSpace W] [MeasurableSpace Ω] (ω : Measure Z) (ν : Measure W)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure ν] (K : Kernel W Ω) :
    (ω.prod ν).bind (fun z => K z.2) = ν.bind (fun z => K z) := by
  ext s hs
  rw [Measure.bind_apply hs
      (show AEMeasurable (fun z : Z × W => K z.2) (ω.prod ν) from by fun_prop),
    Measure.bind_apply hs K.aemeasurable,
    lintegral_prod (fun z : Z × W => K z.2 s)
      (show AEMeasurable (fun z : Z × W => K z.2 s) (ω.prod ν) from
        ((K.measurable_coe hs).comp measurable_snd).aemeasurable)]
  simp

/-- Each prescribed finite sign prior is a probability measure.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input theta](hyp:theta), [the sign prior marked probability conclusion](goal) holds. -/
lemma signPrior_marked_probability (d : ℕ) (h delta a b : ℝ) (theta : Bool) :
    IsProbabilityMeasure (signPrior (markedHandle d h delta a b) theta) := by
  obtain ⟨hw, hsum⟩ := marked_prior_mass d h delta theta
  constructor
  change (∑ sigma : SignArray d h delta,
    ENNReal.ofReal (markedWeight h delta theta sigma) • Measure.dirac sigma) Set.univ = 1
  simp only [Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun sigma _ => hw sigma), hsum]
  norm_num

/-- A finite atomic prior mixed through a kernel is its weighted sum of laws.  Given [the specified input d](hyp:d), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input K](hyp:K), [the sign prior bind kernel conclusion](goal) holds. -/
lemma signPrior_bind_kernel {d : ℕ} (H : MarkedPriors d) (theta : Bool)
    {Ω : Type*} [MeasurableSpace Ω] (K : Kernel (PriorSign H) Ω) :
    (signPrior H theta).bind (fun sigma => K sigma) =
      ∑ sigma : PriorSign H, ENNReal.ofReal (H.weight theta sigma) • K sigma := by
  unfold signPrior
  rw [← Measure.sum_fintype, Measure.bind_sum _ _ K.measurable.aemeasurable,
    Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [Measure.bind_smul, Measure.dirac_bind K.measurable]

/-- The finite family of full original-record experiments is a measurable kernel.  Given [the specified input d](hyp:d), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input n](hyp:n), [the specified input m](hyp:m), [marked experiment kernel](goal) is the corresponding construction. -/
def markedExperimentKernel {d : ℕ} (H : MarkedPriors d) (theta : Bool)
    (n m : ℕ) : Kernel (PriorSign H) (Sample d n m) :=
  ⟨fun sigma => experiment (H.law theta sigma) n m, by
    exact measurable_of_finite _⟩

/-- Every member of the full randomized experiment kernel is a probability law.  Given [the specified input d](hyp:d), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input n](hyp:n), [the specified input m](hyp:m), [the marked experiment kernel markov conclusion](goal) holds. -/
lemma markedExperimentKernel_markov {d : ℕ} (H : MarkedPriors d) (theta : Bool)
    (n m : ℕ) : IsMarkovKernel (markedExperimentKernel H theta n m) := by
  constructor
  intro sigma
  exact population_experiment_probability (H.law theta sigma) n m

/-- Mixing the full experiment kernel appends exactly the common randomizer to
its original-record marked mixture.  Given [the specified input d](hyp:d), [the specified input H](hyp:H), [the specified input theta](hyp:theta), [the specified input n](hyp:n), [the specified input m](hyp:m), [the sign prior bind marked experiment conclusion](goal) holds. -/
lemma signPrior_bind_markedExperiment {d : ℕ} (H : MarkedPriors d) (theta : Bool)
    (n m : ℕ) :
    (signPrior H theta).bind (fun sigma => markedExperimentKernel H theta n m sigma) =
      (markedMixture H theta n m).prod (volume.restrict (Icc (0:ℝ) 1)) := by
  rw [signPrior_bind_kernel, markedMixture_prod_randomizer]
  rfl

/-- The product of the two prescribed sign priors is one common probability prior
for the two full-block families in the cited testing theorem.  Given [the specified input d](hyp:d), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the marked common prior probability conclusion](goal) holds. -/
lemma marked_common_prior_probability (d : ℕ) (h delta a b : ℝ) :
    IsProbabilityMeasure
      ((signPrior (markedHandle d h delta a b) false).prod
        (signPrior (markedHandle d h delta a b) true)) := by
  letI := signPrior_marked_probability d h delta a b false
  letI := signPrior_marked_probability d h delta a b true
  infer_instance

/-- Both families under the common product prior have precisely the randomized
marked mixtures prescribed by the lower-bound construction.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the marked common prior mixtures conclusion](goal) holds. -/
lemma marked_common_prior_mixtures (d n m : ℕ) (h delta a b : ℝ) :
    let H := markedHandle d h delta a b
    let omega := (signPrior H false).prod (signPrior H true)
    omega.bind (fun z => markedExperimentKernel H false n m z.1) =
        (markedMixture H false n m).prod (volume.restrict (Icc (0:ℝ) 1)) ∧
      omega.bind (fun z => markedExperimentKernel H true n m z.2) =
        (markedMixture H true n m).prod (volume.restrict (Icc (0:ℝ) 1)) := by
  letI := signPrior_marked_probability d h delta a b false
  letI := signPrior_marked_probability d h delta a b true
  dsimp only
  constructor
  · rw [bind_product_prior_fst, signPrior_bind_markedExperiment]
  · rw [bind_product_prior_snd, signPrior_bind_markedExperiment]

/-- The common product prior preserves the exact marked Hellinger distance,
including the independent randomizer.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the marked common prior hellinger conclusion](goal) holds. -/
lemma marked_common_prior_hellinger (d n m : ℕ) (h delta a b : ℝ) :
    let H := markedHandle d h delta a b
    let omega := (signPrior H false).prod (signPrior H true)
    hellingerSq
      (omega.bind (fun z => markedExperimentKernel H true n m z.2))
      (omega.bind (fun z => markedExperimentKernel H false n m z.1)) =
      hellingerSq (markedMixture H true n m) (markedMixture H false n m) := by
  have hid := marked_common_prior_mixtures d n m h delta a b
  dsimp only at hid ⊢
  rw [hid.1, hid.2]
  letI := markedMixture_probability d n m h delta a b true
  letI := markedMixture_probability d n m h delta a b false
  letI := population_randomizer_probability
  exact hellingerSq_prod_probability _ _ _

/-- Once the causal target is represented on the full experiment laws, the cited
fuzzy test gives a minimax bound for the unchanged primitive class. Only values
on the two marked families are needed from that representation.  Given [the specified input d](hyp:d), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input h](hyp:h), [the specified input delta](hyp:delta), [the specified input a](hyp:a), [the specified input b](hyp:b), [the specified input ha](hyp:ha), [the specified input hb](hyp:hb), [the specified input hMembers](hyp:hMembers), [the specified input hTargets](hyp:hTargets), [the target representation Ψ](hyp:Ψ), [its agreement on the marked families](hyp:hΨ), [the specified input hhell](hyp:hhell), [the marked fuzzy testing minimax conclusion](goal) holds. -/
lemma marked_fuzzy_testing_minimax
    (d n m : ℕ) (alpha beta gamma L eps h delta a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hMembers : ∀ theta sigma,
      PrimitiveClass alpha beta gamma L eps ((markedHandle d h delta a b).law theta sigma))
    (hTargets : ∀ sigma,
      tau ((markedHandle d h delta a b).law false sigma) (hMembers false sigma) (x0 d) = 2*a*b ∧
      tau ((markedHandle d h delta a b).law true sigma) (hMembers true sigma) (x0 d) = -2*a*b)
    (Ψ : Measure (Sample d n m) → ℝ)
    (hΨ : ∀ theta sigma,
      Ψ (experiment ((markedHandle d h delta a b).law theta sigma) n m) =
        tau ((markedHandle d h delta a b).law theta sigma) (hMembers theta sigma) (x0 d))
    (hhell : hellingerSq (markedMixture (markedHandle d h delta a b) true n m)
      (markedMixture (markedHandle d h delta a b) false n m) ≤ 1/16) :
    ENNReal.ofReal ((3/4:ℝ)*a*b) ≤ minimaxRisk d alpha beta gamma L eps n m := by
  let H := markedHandle d h delta a b
  let omega := (signPrior H false).prod (signPrior H true)
  let B : Kernel (PriorSign H × PriorSign H) (Sample d n m) := (markedExperimentKernel H false n m).comap Prod.fst measurable_fst
  let C : Kernel (PriorSign H × PriorSign H) (Sample d n m) := (markedExperimentKernel H true n m).comap Prod.snd measurable_snd
  letI := marked_common_prior_probability d h delta a b
  letI := markedExperimentKernel_markov H false n m
  letI := markedExperimentKernel_markov H true n m
  have hs : 0 < 4*a*b := by positivity
  have hsep : ∀ z z', 4*a*b ≤ Ψ (B z) - Ψ (C z') := by
    intro z z'
    change 4*a*b ≤ Ψ (experiment (H.law false z.1) n m) -
      Ψ (experiment (H.law true z'.2) n m)
    rw [hΨ, hΨ, (hTargets z.1).1, (hTargets z'.2).2]
    linarith
  have hh : hellingerSq (omega.bind (fun z => B z))
      (omega.bind (fun z => C z)) ≤ 1/16 := by
    have hid := marked_common_prior_hellinger d n m h delta a b
    have hsym : hellingerSq
        (omega.bind (fun z => B z)) (omega.bind (fun z => C z)) =
        hellingerSq (omega.bind (fun z => C z)) (omega.bind (fun z => B z)) := by
      unfold hellingerSq Causalean.Stat.hellingerSqDensity
      simp only [add_comm]
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    rw [hsym]
    exact hid.le.trans hhell
  unfold minimaxRisk
  apply Causalean.Stat.le_minimaxValueENNReal
  intro T
  let Model : Set (Measure (Sample d n m)) :=
    {P | ∃ theta sigma, P = experiment (H.law theta sigma) n m}
  have htest := published_fuzzy_testing_block omega B C Model
    (fun z => ⟨false, z.1, rfl⟩) (fun z => ⟨true, z.2, rfl⟩)
    Ψ (4*a*b) (1/16) hs (by norm_num) (by norm_num) hsep hh T.1 T.2
  have hconstant : (3/4:ℝ)*a*b ≤
      (4*a*b/4)*(1-Real.sqrt ((1/16:ℝ)*(1-(1/16:ℝ)/4))) := by
    have ho := mul_le_mul_of_nonneg_left fuzzy_testing_overlap_sixteenth
      (mul_pos ha hb).le
    nlinarith
  apply (ENNReal.ofReal_le_ofReal hconstant).trans (htest.trans ?_)
  apply iSup_le
  intro P
  apply iSup_le
  rintro ⟨theta, sigma, rfl⟩
  rw [hΨ]
  exact Causalean.Stat.le_worstCaseRiskENNReal
    (risk := classRisk d alpha beta gamma L eps n m) T
    ⟨H.law theta sigma, hMembers theta sigma⟩

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
