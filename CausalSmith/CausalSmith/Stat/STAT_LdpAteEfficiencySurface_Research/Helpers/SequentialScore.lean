module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialDomination

/-! # Directional scores for finite sequential transcript mixtures

This file differentiates the finite latent-input mixture against the common
transcript reference measure. It identifies the complete-data input-path score
and the induced conditional transcript score pointwise.
-/

@[expose] public section
noncomputable section


namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- For the supplied quantities and conditions, the parameter path is the mathematical object specified below. [The parameter Path](goal) is determined by [the displayed parameters](hyp:θ,v,u). -/
def parameterPath (θ v : TrialParameter) (u : ℝ) : TrialParameter :=
  fun k ↦ θ k + u * v k

/-- For [the supplied quantities and conditions](hyp:p,v), the [input directional derivative](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:j), these specify the stated inputs. -/
def inputDirectionalDerivative (p : ℝ) (v : TrialParameter)
    (j : Fin 4) : ℝ :=
  ∑ k : Fin 2, inputDerivative p j k * v k

/-- Under [the supplied quantities and conditions](hyp:p,j), [the pi theta by val score assertion](goal) holds. -/
lemma piTheta_by_val_score (θ : TrialParameter) (p : ℝ) (j : Fin 4) :
    piTheta θ p j =
      if j.val = 0 then controlProb p * (1 - θ 0)
      else if j.val = 1 then controlProb p * θ 0
      else if j.val = 2 then p * (1 - θ 1)
      else p * θ 1 := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;> rfl

/-- Under the supplied quantities and conditions, the pi theta pos of interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the pi Theta pos of interior](goal).

Under the stated assumptions, the pi Theta pos of interior. -/
lemma piTheta_pos_of_interior (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (j : Fin 4) :
    0 < piTheta θ p j := by
  rcases hp with ⟨hp0, hp1⟩
  rcases hθ with ⟨h00, h01, h10, h11⟩
  rw [piTheta_by_val_score]
  rcases j with ⟨j, hj⟩
  interval_cases j <;> simp +decide only [Fin.isValue, ↓reduceIte, controlProb] <;>
    nlinarith

/-- the input path probability pos of interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the input Path Probability pos of interior](goal).

Under the stated assumptions, the input Path Probability pos of interior. -/
lemma inputPathProbability_pos_of_interior {n : ℕ}
    (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (x : Fin n → Fin 4) : 0 < inputPathProbability θ p x := by
  unfold inputPathProbability
  exact Finset.prod_pos fun i _ ↦ piTheta_pos_of_interior θ p hp hθ (x i)

/-- Under [the supplied quantities and conditions](hyp:v,p,u), [the has deriv at pi theta parameter path assertion](goal) holds. For [the displayed quantities and conditions](hyp:j), these specify the stated inputs. -/
lemma hasDerivAt_piTheta_parameterPath (θ v : TrialParameter) (p u : ℝ)
    (j : Fin 4) :
    HasDerivAt (fun a ↦ piTheta (parameterPath θ v a) p j)
      (inputDirectionalDerivative p v j) u := by
  have heq : (fun a ↦ piTheta (parameterPath θ v a) p j) =
      fun a ↦ piTheta θ p j + a * inputDirectionalDerivative p v j := by
    funext a
    rw [piTheta_by_val_score, piTheta_by_val_score]
    rcases j with ⟨j, hj⟩
    interval_cases j <;>
      simp [parameterPath, inputDirectionalDerivative, inputDerivative,
        controlProb, Fin.sum_univ_succ] <;> ring
  have hder : HasDerivAt
      (fun a ↦ piTheta θ p j + a * inputDirectionalDerivative p v j)
      (inputDirectionalDerivative p v j) u := by
    have hi : HasDerivAt (fun a : ℝ ↦ a)
        1 u := hasDerivAt_id u
    have hm : HasDerivAt
        (fun a : ℝ ↦ a * inputDirectionalDerivative p v j)
        (inputDirectionalDerivative p v j) u := by
      simpa using hi.mul_const (inputDirectionalDerivative p v j)
    exact hm.const_add (piTheta θ p j)
  exact heq.symm ▸ hder

/-- For the supplied quantities and conditions, the input path directional derivative is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The input Path Directional Derivative](goal) is determined by [the displayed parameters](hyp:θ,v,p,x). -/
def inputPathDirectionalDerivative {n : ℕ} (θ v : TrialParameter) (p : ℝ)
    (x : Fin n → Fin 4) : ℝ :=
  ∑ i : Fin n, inputDirectionalDerivative p v (x i) *
    ∏ j ∈ Finset.univ.erase i, piTheta θ p (x j)

/-- [the has deriv at input path probability parameter path assertion](goal) holds. For [the displayed quantities and conditions](hyp:v,p,u,x), these specify the stated inputs. -/
lemma hasDerivAt_inputPathProbability_parameterPath {n : ℕ}
    (θ v : TrialParameter) (p u : ℝ) (x : Fin n → Fin 4) :
    HasDerivAt (fun a ↦ inputPathProbability (parameterPath θ v a) p x)
      (inputPathDirectionalDerivative (parameterPath θ v u) v p x) u := by
  simpa [inputPathProbability, inputPathDirectionalDerivative, mul_comm] using
    HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
      (fun i _ ↦ hasDerivAt_piTheta_parameterPath θ v p u (x i))

/-- [The real-valued density of one transcript component](goal) is determined by [the displayed parameters](hyp:P,n,x,z). -/
noncomputable def transcriptComponentRealDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (x : Fin n → Fin 4)
    (z : Transcript (Z n)) : ℝ :=
  ((P.transcript n x).rnDeriv (transcriptReferenceMeasure P n) z).toReal

/-- [The real-valued density of the transcript mixture](goal) is determined by [the displayed parameters](hyp:P,θ,p,n,z). -/
noncomputable def transcriptMixtureRealDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (z : Transcript (Z n)) : ℝ :=
  ∑ x : Fin n → Fin 4,
    inputPathProbability θ p x * transcriptComponentRealDensity P n x z

/-- [The directional derivative of the real-valued transcript-mixture density](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,z). -/
noncomputable def transcriptMixtureRealDerivative {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (z : Transcript (Z n)) : ℝ :=
  ∑ x : Fin n → Fin 4,
    inputPathDirectionalDerivative θ v p x *
      transcriptComponentRealDensity P n x z

/-- On a parameter range where the four-cell path probabilities are
nonnegative, the explicit finite-mixture density is the Radon--Nikodym
density of the transcript law.  This is the paper-side interface between the
finite latent-input expansion and score calculus on an arbitrary transcript
measurable space. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,n,hprob), these specify the stated inputs. -/
lemma transcriptDensity_toReal_ae_eq_mixture {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (hprob : ∀ x : Fin n → Fin 4, 0 ≤ inputPathProbability θ p x) :
    (fun z ↦ (transcriptDensity P θ p n z).toReal) =ᵐ[transcriptReferenceMeasure P n]
      transcriptMixtureRealDensity P θ p n := by
  classical
  let ν := transcriptReferenceMeasure P n
  let w (x : Fin n → Fin 4) : ℝ≥0∞ :=
    ENNReal.ofReal (inputPathProbability θ p x)
  letI componentProbability (x : Fin n → Fin 4) :
      IsProbabilityMeasure (P.transcript n x) := (P.factorizes n x).1
  have hw (x : Fin n → Fin 4) : w x ≠ ∞ := by
    simp [w]
  haveI (x : Fin n → Fin 4) : IsFiniteMeasure (w x • P.transcript n x) :=
    (P.transcript n x).smul_finite (hw x)
  have hrn (t : Finset (Fin n → Fin 4)) :
      (t.sum fun x ↦ w x • P.transcript n x).rnDeriv ν =ᵐ[ν]
        fun z ↦ t.sum fun x ↦ w x * (P.transcript n x).rnDeriv ν z := by
    induction t using Finset.induction_on with
    | empty =>
        filter_upwards [Measure.rnDeriv_zero ν] with z hz
        simpa using hz
    | @insert x t hx ih =>
        haveI : IsFiniteMeasure (t.sum fun y ↦ w y • P.transcript n y) := inferInstance
        have hadd := Measure.rnDeriv_add (w x • P.transcript n x)
          (t.sum fun y ↦ w y • P.transcript n y) ν
        have hsmul := Measure.rnDeriv_smul_left_of_ne_top (P.transcript n x) ν (hw x)
        filter_upwards [hadd, hsmul, ih] with z hz ha hb
        simpa [Finset.sum_insert hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb]
          using hz
  have hfinite : ∀ᵐ z ∂ν, ∀ x : Fin n → Fin 4,
      (P.transcript n x).rnDeriv ν z ≠ ∞ := by
    rw [Filter.eventually_all]
    intro x
    exact (Measure.rnDeriv_lt_top (P.transcript n x) ν).mono
      (fun _ hz ↦ ne_of_lt hz)
  filter_upwards [hrn Finset.univ, hfinite] with z hz hfin
  change ((transcriptLaw P θ p n).rnDeriv ν z).toReal =
    transcriptMixtureRealDensity P θ p n z
  rw [show transcriptLaw P θ p n =
      Finset.univ.sum (fun x ↦ w x • P.transcript n x) by
        simp [transcriptLaw, w]]
  rw [hz, ENNReal.toReal_sum (fun x _ ↦ ENNReal.mul_ne_top (hw x) (hfin x))]
  simp [transcriptMixtureRealDensity, transcriptComponentRealDensity, w, ν,
    ENNReal.toReal_mul, hprob]

/-- the transcript density to real ae eq mixture of interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the transcript Density to Real ae eq mixture of interior](goal).

Under the stated assumptions, the transcript Density to Real ae eq mixture of interior. -/
lemma transcriptDensity_toReal_ae_eq_mixture_of_interior {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (fun z ↦ (transcriptDensity P θ p n z).toReal) =ᵐ[transcriptReferenceMeasure P n]
      transcriptMixtureRealDensity P θ p n :=
  transcriptDensity_toReal_ae_eq_mixture P θ p n fun x ↦
    (inputPathProbability_pos_of_interior θ p hp hθ x).le

/-- [the has deriv at transcript mixture real density parameter path assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,u,n,z), these specify the stated inputs. -/
lemma hasDerivAt_transcriptMixtureRealDensity_parameterPath {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p u : ℝ) (n : ℕ)
    (z : Transcript (Z n)) :
    HasDerivAt
      (fun a ↦ transcriptMixtureRealDensity P (parameterPath θ v a) p n z)
      (transcriptMixtureRealDerivative P (parameterPath θ v u) v p n z) u := by
  simpa [transcriptMixtureRealDensity, transcriptMixtureRealDerivative] using
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → Fin 4)))
      (fun x _ ↦
        (hasDerivAt_inputPathProbability_parameterPath θ v p u x).mul_const
          (transcriptComponentRealDensity P n x z))

/-- The complete-data directional score of one latent input path. [The input Path Directional Score](goal) is determined by [the displayed parameters](hyp:θ,v,p,x). -/
noncomputable def inputPathDirectionalScore {n : ℕ}
    (θ v : TrialParameter) (p : ℝ) (x : Fin n → Fin 4) : ℝ :=
  inputPathDirectionalDerivative θ v p x / inputPathProbability θ p x

/-- [the input path derivative eq probability mul score assertion](goal) holds. For [the displayed quantities and conditions](hyp:v,p,x,hx), these specify the stated inputs. -/
lemma inputPathDerivative_eq_probability_mul_score {n : ℕ}
    (θ v : TrialParameter) (p : ℝ) (x : Fin n → Fin 4)
    (hx : inputPathProbability θ p x ≠ 0) :
    inputPathDirectionalDerivative θ v p x =
      inputPathProbability θ p x * inputPathDirectionalScore θ v p x := by
  rw [inputPathDirectionalScore, mul_div_cancel₀ _ hx]

/-- The conditional transcript score: the derivative of the finite complete-data mixture density divided by that mixture density. [The conditional Transcript Directional Score](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,z). -/
noncomputable def conditionalTranscriptDirectionalScore {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (z : Transcript (Z n)) : ℝ :=
  transcriptMixtureRealDerivative P θ v p n z /
    transcriptMixtureRealDensity P θ p n z

/-- [the transcript derivative eq density mul conditional score assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,z,hz), these specify the stated inputs. -/
lemma transcriptDerivative_eq_density_mul_conditionalScore {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (z : Transcript (Z n))
    (hz : transcriptMixtureRealDensity P θ p n z ≠ 0) :
    transcriptMixtureRealDerivative P θ v p n z =
      transcriptMixtureRealDensity P θ p n z *
        conditionalTranscriptDirectionalScore P θ v p n z := by
  rw [conditionalTranscriptDirectionalScore, mul_div_cancel₀ _ hz]

/-- [the transcript derivative eq complete data score mixture assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,z,hx), these specify the stated inputs. -/
lemma transcriptDerivative_eq_completeDataScoreMixture {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (z : Transcript (Z n))
    (hx : ∀ x : Fin n → Fin 4, inputPathProbability θ p x ≠ 0) :
    transcriptMixtureRealDerivative P θ v p n z =
      ∑ x : Fin n → Fin 4,
        inputPathProbability θ p x * inputPathDirectionalScore θ v p x *
          transcriptComponentRealDensity P n x z := by
  rw [transcriptMixtureRealDerivative]
  apply Finset.sum_congr rfl
  intro x _
  rw [inputPathDerivative_eq_probability_mul_score θ v p x (hx x)]

end CausalSmith.Stat.LdpAteEfficiencySurface
