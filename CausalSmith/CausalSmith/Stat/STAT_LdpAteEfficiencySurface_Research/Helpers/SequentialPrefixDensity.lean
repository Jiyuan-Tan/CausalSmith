module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialGlobalScore
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.TranscriptUniqueness

/-! # Dominated finite-mixture scores on transcript prefixes

This file constructs explicit common references, densities, and directional derivative
densities after projecting a full transcript to a finite prefix.  The identities are
paper-side inputs for score projection and do not use a conditional expectation theorem.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

private lemma map_finset_sum_measure {X Y ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y) (hf : Measurable f)
    (s : Finset ι) (M : ι → Measure X) :
    Measure.map f (∑ i ∈ s, M i) = ∑ i ∈ s, Measure.map f (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.map_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [Measure.map_add _ _ hf, ih]

/-- the [transcript prefix reference measure](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:P,n,k,hk), these specify the stated inputs. -/
def transcriptPrefixReferenceMeasure {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n k : ℕ) (hk : k ≤ n) :
    Measure (History (Z n) k hk) :=
  (transcriptReferenceMeasure P n).map (transcriptPrefix hk)

/-- the transcript prefix law is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The transcript Prefix Law](goal) is determined by [the displayed parameters](hyp:P,θ,p,n,k,hk). -/
def transcriptPrefixLaw {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) : Measure (History (Z n) k hk) :=
  (transcriptLaw P θ p n).map (transcriptPrefix hk)

/-- the [transcript prefix component real density](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:P,n,k,hk,x,h), these specify the stated inputs. -/
def transcriptPrefixComponentRealDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n k : ℕ) (hk : k ≤ n)
    (x : Fin n → Fin 4) (h : History (Z n) k hk) : ℝ :=
  (((P.transcript n x).map (transcriptPrefix hk)).rnDeriv
    (transcriptPrefixReferenceMeasure P n k hk) h).toReal

/-- the transcript prefix mixture real density is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The transcript Prefix Mixture Real Density](goal) is determined by [the displayed parameters](hyp:P,θ,p,n,k,hk,h). -/
def transcriptPrefixMixtureRealDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) (h : History (Z n) k hk) : ℝ :=
  ∑ x : Fin n → Fin 4, inputPathProbability θ p x *
    transcriptPrefixComponentRealDensity P n k hk x h

/-- the transcript prefix mixture real derivative is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The transcript Prefix Mixture Real Derivative](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,h). -/
def transcriptPrefixMixtureRealDerivative {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) (h : History (Z n) k hk) : ℝ :=
  ∑ x : Fin n → Fin 4, inputPathDirectionalDerivative θ v p x *
    transcriptPrefixComponentRealDensity P n k hk x h

/-- the conditional transcript prefix directional score is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The conditional Transcript Prefix Directional Score](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,h). -/
def conditionalTranscriptPrefixDirectionalScore {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) (h : History (Z n) k hk) : ℝ :=
  transcriptPrefixMixtureRealDerivative P θ v p n k hk h /
    transcriptPrefixMixtureRealDensity P θ p n k hk h

/-- [the transcript prefix reference measure eq sum assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,n,k,hk), these specify the stated inputs. -/
lemma transcriptPrefixReferenceMeasure_eq_sum {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n k : ℕ) (hk : k ≤ n) :
    transcriptPrefixReferenceMeasure P n k hk =
      ∑ x : Fin n → Fin 4, (P.transcript n x).map (transcriptPrefix hk) := by
  unfold transcriptPrefixReferenceMeasure transcriptReferenceMeasure
  exact map_finset_sum_measure (transcriptPrefix hk)
    (measurable_transcriptPrefix hk) Finset.univ _

/-- [the transcript prefix law eq sum assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,p,n,k,hk), these specify the stated inputs. -/
lemma transcriptPrefixLaw_eq_sum {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    transcriptPrefixLaw P θ p n k hk =
      ∑ x : Fin n → Fin 4, ENNReal.ofReal (inputPathProbability θ p x) •
        (P.transcript n x).map (transcriptPrefix hk) := by
  unfold transcriptPrefixLaw transcriptLaw
  rw [map_finset_sum_measure (transcriptPrefix hk)
    (measurable_transcriptPrefix hk) Finset.univ]
  simp_rw [Measure.map_smul]

/-- [the transcript prefix law ac reference assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,p,n,k,hk), these specify the stated inputs. -/
lemma transcriptPrefixLaw_ac_reference {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    transcriptPrefixLaw P θ p n k hk ≪
      transcriptPrefixReferenceMeasure P n k hk := by
  rw [transcriptPrefixLaw_eq_sum, transcriptPrefixReferenceMeasure_eq_sum]
  apply Measure.AbsolutelyContinuous.mk
  intro A hA href
  simp only [Measure.coe_finsetSum, Finset.sum_apply] at href ⊢
  apply Finset.sum_eq_zero
  intro x _
  rw [Measure.smul_apply, smul_eq_mul]
  apply mul_eq_zero_of_right
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le)).mp href x
    (Finset.mem_univ x)

/-- the transcript prefix density to real ae eq mixture of interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hk,hp,hθ), [the transcript Prefix Density to Real ae eq mixture of interior](goal).

Under the stated assumptions, the transcript Prefix Density to Real ae eq mixture of interior. -/
lemma transcriptPrefixDensity_toReal_ae_eq_mixture_of_interior {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (fun h => ((transcriptPrefixLaw P θ p n k hk).rnDeriv
      (transcriptPrefixReferenceMeasure P n k hk) h).toReal) =ᵐ[
        transcriptPrefixReferenceMeasure P n k hk]
      transcriptPrefixMixtureRealDensity P θ p n k hk := by
  classical
  let ν := transcriptPrefixReferenceMeasure P n k hk
  let μ (x : Fin n → Fin 4) :=
    (P.transcript n x).map (transcriptPrefix hk)
  let w (x : Fin n → Fin 4) : ℝ≥0∞ :=
    ENNReal.ofReal (inputPathProbability θ p x)
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (μ x) :=
    Measure.isProbabilityMeasure_map (measurable_transcriptPrefix hk).aemeasurable
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  have hw (x : Fin n → Fin 4) : w x ≠ ∞ := by simp [w]
  haveI (x : Fin n → Fin 4) : IsFiniteMeasure (w x • μ x) :=
    (μ x).smul_finite (hw x)
  have hrn (t : Finset (Fin n → Fin 4)) :
      (t.sum fun x ↦ w x • μ x).rnDeriv ν =ᵐ[ν]
        fun h ↦ t.sum fun x ↦ w x * (μ x).rnDeriv ν h := by
    induction t using Finset.induction_on with
    | empty =>
        filter_upwards [Measure.rnDeriv_zero ν] with h hh
        simpa using hh
    | @insert x t hx ih =>
        haveI : IsFiniteMeasure (t.sum fun y ↦ w y • μ y) := inferInstance
        have hadd := Measure.rnDeriv_add (w x • μ x)
          (t.sum fun y ↦ w y • μ y) ν
        have hsmul := Measure.rnDeriv_smul_left_of_ne_top (μ x) ν (hw x)
        filter_upwards [hadd, hsmul, ih] with h hh ha hb
        simpa [Finset.sum_insert hx, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, ha, hb] using hh
  have hfinite : ∀ᵐ h ∂ν, ∀ x : Fin n → Fin 4,
      (μ x).rnDeriv ν h ≠ ∞ := by
    rw [Filter.eventually_all]
    intro x
    exact (Measure.rnDeriv_lt_top (μ x) ν).mono (fun _ hh ↦ ne_of_lt hh)
  filter_upwards [hrn Finset.univ, hfinite] with h hh hfin
  change ((transcriptPrefixLaw P θ p n k hk).rnDeriv ν h).toReal =
    transcriptPrefixMixtureRealDensity P θ p n k hk h
  rw [transcriptPrefixLaw_eq_sum P θ p n k hk]
  rw [hh, ENNReal.toReal_sum
    (fun x _ ↦ ENNReal.mul_ne_top (hw x) (hfin x))]
  simp [transcriptPrefixMixtureRealDensity,
    transcriptPrefixComponentRealDensity, μ, w, ν, ENNReal.toReal_mul,
    (inputPathProbability_pos_of_interior θ p hp hθ _).le]

/-- [the measurable transcript prefix mixture real density assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,p,n,k,hk), these specify the stated inputs. -/
lemma measurable_transcriptPrefixMixtureRealDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    Measurable (transcriptPrefixMixtureRealDensity P θ p n k hk) := by
  unfold transcriptPrefixMixtureRealDensity transcriptPrefixComponentRealDensity
  exact Finset.measurable_fun_sum _ fun x _ ↦ measurable_const.mul
    (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- [the measurable transcript prefix mixture real derivative assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk), these specify the stated inputs. -/
lemma measurable_transcriptPrefixMixtureRealDerivative {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    Measurable (transcriptPrefixMixtureRealDerivative P θ v p n k hk) := by
  unfold transcriptPrefixMixtureRealDerivative transcriptPrefixComponentRealDensity
  exact Finset.measurable_fun_sum _ fun x _ ↦ measurable_const.mul
    (Measure.measurable_rnDeriv _ _).ennreal_toReal

-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
/-- [the transcript prefix derivative pushforward assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk,A,hA), these specify the stated inputs. -/
lemma transcriptPrefix_derivative_pushforward {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) (A : Set (History (Z n) k hk))
    (hA : MeasurableSet A) :
    ∫ z in transcriptPrefix hk ⁻¹' A,
        transcriptMixtureRealDerivative P θ v p n z
        ∂transcriptReferenceMeasure P n =
      ∫ h in A, transcriptPrefixMixtureRealDerivative P θ v p n k hk h
        ∂transcriptPrefixReferenceMeasure P n k hk := by
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure
      ((P.transcript n x).map (transcriptPrefix hk)) :=
    Measure.isProbabilityMeasure_map (measurable_transcriptPrefix hk).aemeasurable
  letI : IsFiniteMeasure (transcriptPrefixReferenceMeasure P n k hk) := by
    unfold transcriptPrefixReferenceMeasure
    infer_instance
  have hpac (x : Fin n → Fin 4) :
      (P.transcript n x).map (transcriptPrefix hk) ≪
        transcriptPrefixReferenceMeasure P n k hk := by
    unfold transcriptPrefixReferenceMeasure
    exact (transcriptComponent_ac_reference P n x).map
      (measurable_transcriptPrefix hk)
  have hintFull (x : Fin n → Fin 4) : Integrable
      (transcriptComponentRealDensity P n x)
      (transcriptReferenceMeasure P n) := by
    have h := (integrable_toReal_rnDeriv_mul_iff
      (transcriptComponent_ac_reference P n x)
      (f := fun _ ↦ (1 : ℝ))).2 (integrable_const (1 : ℝ))
    change Integrable (fun z ↦
      ((P.transcript n x).rnDeriv (transcriptReferenceMeasure P n) z).toReal)
      (transcriptReferenceMeasure P n)
    simpa only [mul_one] using h
  have hintPrefix (x : Fin n → Fin 4) : Integrable
      (transcriptPrefixComponentRealDensity P n k hk x)
      (transcriptPrefixReferenceMeasure P n k hk) := by
    have h := (integrable_toReal_rnDeriv_mul_iff (hpac x)
      (f := fun _ ↦ (1 : ℝ))).2 (integrable_const (1 : ℝ))
    change Integrable (fun z ↦
      (((P.transcript n x).map (transcriptPrefix hk)).rnDeriv
        (transcriptPrefixReferenceMeasure P n k hk) z).toReal)
      (transcriptPrefixReferenceMeasure P n k hk)
    simpa only [mul_one] using h
  simp_rw [transcriptMixtureRealDerivative,
    transcriptPrefixMixtureRealDerivative]
  rw [integral_finset_sum _ (fun x _ ↦
      ((hintFull x).const_mul _).integrableOn),
    integral_finset_sum _ (fun x _ ↦
      ((hintPrefix x).const_mul _).integrableOn)]
  apply Finset.sum_congr rfl
  intro x _
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  unfold transcriptComponentRealDensity transcriptPrefixComponentRealDensity
  rw [
    Measure.setIntegral_toReal_rnDeriv
      (transcriptComponent_ac_reference P n x),
    Measure.setIntegral_toReal_rnDeriv (hpac x)]
  simp only [measureReal_def]
  rw [Measure.map_apply (measurable_transcriptPrefix hk) hA]

end CausalSmith.Stat.LdpAteEfficiencySurface
