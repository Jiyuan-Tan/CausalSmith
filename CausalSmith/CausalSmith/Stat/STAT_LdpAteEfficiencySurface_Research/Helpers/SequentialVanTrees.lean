module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialGlobalScore
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Main

/-! # Arbitrary-output van Trees likelihood fields

This file packages the finite-mixture transcript density along a scalar parameter path into
the globally nonnegative likelihood fields required by the observation-dependent van Trees
inequality.  No countability or stagewise Radon--Nikodym selector is used.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- the transcript law eq with density mixture assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the transcript Law eq with Density mixture](goal).

Under the stated assumptions, the transcript Law eq with Density mixture. -/
lemma transcriptLaw_eq_withDensity_mixture {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (transcriptReferenceMeasure P n).withDensity
        (fun z ↦ ENNReal.ofReal (transcriptMixtureRealDensity P θ p n z)) =
      transcriptLaw P θ p n := by
  rw [← transcriptLaw_eq_withDensity_reference P θ p n]
  apply withDensity_congr_ae
  filter_upwards [transcriptDensity_toReal_ae_eq_mixture_of_interior
      P θ p n hp hθ,
    Measure.rnDeriv_lt_top (transcriptLaw P θ p n)
      (transcriptReferenceMeasure P n)] with z hz htop
  rw [← hz]
  exact ENNReal.ofReal_toReal (ne_of_lt htop)

/-- the integral transcript mixture real density eq one assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the integral transcript Mixture Real Density eq one](goal).

Under the stated assumptions, the integral transcript Mixture Real Density eq one. -/
lemma integral_transcriptMixtureRealDensity_eq_one {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    ∫ z, transcriptMixtureRealDensity P θ p n z
        ∂transcriptReferenceMeasure P n = 1 := by
  have hnonneg := transcriptMixtureRealDensity_nonneg P θ p n hp hθ
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  have hcomp (x : Fin n → Fin 4) : Integrable
      (transcriptComponentRealDensity P n x) (transcriptReferenceMeasure P n) := by
    have h := (integrable_toReal_rnDeriv_mul_iff
      (transcriptComponent_ac_reference P n x)
      (f := fun _ ↦ (1 : ℝ))).2 (integrable_const (1 : ℝ))
    change Integrable (fun z ↦
      ((P.transcript n x).rnDeriv (transcriptReferenceMeasure P n) z).toReal)
      (transcriptReferenceMeasure P n)
    simpa only [mul_one] using h
  have hint : Integrable (transcriptMixtureRealDensity P θ p n)
      (transcriptReferenceMeasure P n) := by
    unfold transcriptMixtureRealDensity
    exact integrable_finsetSum _ fun x _ ↦ (hcomp x).const_mul _
  have hlaw := transcriptLaw_eq_withDensity_mixture P θ p n hp hθ
  have hmass := congrArg (fun μ : Measure (Transcript (Z n)) ↦ μ Set.univ) hlaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnonneg)] at hmass
  have hprob : transcriptLaw P θ p n Set.univ = 1 := by
    letI : IsProbabilityMeasure (transcriptLaw P θ p n) :=
      transcriptLaw_isProbability P θ p hp hθ n
    exact measure_univ
  rw [hprob] at hmass
  exact ENNReal.ofReal_eq_one.mp (by simpa using hmass)

/-- the vt density is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The vt Density](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,ell,upper,a,z). -/
def vtDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper a : ℝ) (z : Transcript (Z n)) : ℝ :=
  if a ∈ Set.Icc ell upper then
    transcriptMixtureRealDensity P (parameterPath θ v a) p n z else 0

/-- the vt density deriv is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The vt Density Deriv](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,ell,upper,a,z). -/
def vtDensityDeriv {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper a : ℝ) (z : Transcript (Z n)) : ℝ :=
  if a ∈ Set.Icc ell upper then
    transcriptMixtureRealDerivative P (parameterPath θ v a) v p n z else 0

/-- [the vt density nonneg assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper,hp,hinterior), these specify the stated inputs. -/
lemma vtDensity_nonneg {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Set.Icc ell upper, InteriorMeans (parameterPath θ v a)) :
    ∀ a z, 0 ≤ vtDensity P θ v p n ell upper a z := by
  intro a z
  rw [vtDensity]
  split_ifs with ha
  · exact transcriptMixtureRealDensity_nonneg P _ p n hp (hinterior a ha) z
  · exact le_rfl

/-- [the vt density has deriv at assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ha,z), these specify the stated inputs. -/
lemma vtDensity_hasDerivAt {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    {ell upper a : ℝ} (ha : a ∈ Set.Ioo ell upper) (z : Transcript (Z n)) :
    HasDerivAt (fun b ↦ vtDensity P θ v p n ell upper b z)
      (vtDensityDeriv P θ v p n ell upper a z) a := by
  have hnhds : Set.Icc ell upper ∈ nhds a :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ha) Set.Ioo_subset_Icc_self
  have heq : (fun b ↦ vtDensity P θ v p n ell upper b z) =ᶠ[nhds a]
      fun b ↦ transcriptMixtureRealDensity P (parameterPath θ v b) p n z := by
    filter_upwards [hnhds] with b hb
    simp [vtDensity, hb]
  have hder := hasDerivAt_transcriptMixtureRealDensity_parameterPath
    P θ v p a n z
  have haIcc : a ∈ Set.Icc ell upper := ⟨ha.1.le, ha.2.le⟩
  rw [vtDensityDeriv, if_pos haIcc]
  exact hder.congr_of_eventuallyEq heq

/-- The interval-extended likelihood has its declared derivative jointly almost everywhere
under parameter measure times the arbitrary-output reference measure. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper), these specify the stated inputs. -/
lemma ae_hasDerivAt_vtDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) :
    ∀ᵐ az ∂((Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure
        ell upper).prod (transcriptReferenceMeasure P n)),
      HasDerivAt (fun b ↦ vtDensity P θ v p n ell upper b az.2)
        (vtDensityDeriv P θ v p n ell upper az.1 az.2) az.1 := by
  let π := Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure ell upper
  have hmem : ∀ᵐ a ∂π, a ∈ Set.Ioo ell upper := by
    unfold π Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne ell),
      ae_restrict_of_ae (volume.ae_ne upper)] with a ha haell haupper
    exact ⟨lt_of_le_of_ne ha.1 (Ne.symm haell), lt_of_le_of_ne ha.2 haupper⟩
  have hlift : ∀ᵐ az ∂(π.prod (transcriptReferenceMeasure P n)),
      az.1 ∈ Set.Ioo ell upper :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hmem
  filter_upwards [hlift] with az haz
  exact vtDensity_hasDerivAt P θ v p n haz az.2

/-- [the vt density integral eq one assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper,hp,hinterior,ha), these specify the stated inputs. -/
lemma vtDensity_integral_eq_one {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Set.Icc ell upper, InteriorMeans (parameterPath θ v a))
    {a : ℝ} (ha : a ∈ Set.Icc ell upper) :
    ∫ z, vtDensity P θ v p n ell upper a z
      ∂transcriptReferenceMeasure P n = 1 := by
  simp only [vtDensity, if_pos ha]
  exact integral_transcriptMixtureRealDensity_eq_one P _ p n hp (hinterior a ha)

/-- [the vt density integral has deriv at assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper,hp,hinterior,ha), these specify the stated inputs. -/
lemma vtDensity_integral_hasDerivAt {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) (hp : InteriorAssignment p)
    (hinterior : ∀ a ∈ Set.Icc ell upper, InteriorMeans (parameterPath θ v a))
    {a : ℝ} (ha : a ∈ Set.Ioo ell upper) :
    HasDerivAt (fun b ↦ ∫ z, vtDensity P θ v p n ell upper b z
      ∂transcriptReferenceMeasure P n) 0 a := by
  have hnhds : Set.Icc ell upper ∈ nhds a :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ha) Set.Ioo_subset_Icc_self
  have heq : (fun b ↦ ∫ z, vtDensity P θ v p n ell upper b z
      ∂transcriptReferenceMeasure P n) =ᶠ[nhds a] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hnhds] with b hb
    exact vtDensity_integral_eq_one P θ v p n ell upper hp hinterior hb
  exact (hasDerivAt_const (x := a) (c := (1 : ℝ))).congr_of_eventuallyEq heq

/-- [the integrable transcript mixture real derivative assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n), these specify the stated inputs. -/
lemma integrable_transcriptMixtureRealDerivative {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ) :
    Integrable (transcriptMixtureRealDerivative P θ v p n)
      (transcriptReferenceMeasure P n) := by
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  have hcomp (x : Fin n → Fin 4) : Integrable
      (transcriptComponentRealDensity P n x) (transcriptReferenceMeasure P n) := by
    have h := (integrable_toReal_rnDeriv_mul_iff
      (transcriptComponent_ac_reference P n x)
      (f := fun _ ↦ (1 : ℝ))).2 (integrable_const (1 : ℝ))
    change Integrable (fun z ↦
      ((P.transcript n x).rnDeriv (transcriptReferenceMeasure P n) z).toReal)
      (transcriptReferenceMeasure P n)
    simpa only [mul_one] using h
  unfold transcriptMixtureRealDerivative
  exact integrable_finsetSum _ fun x _ ↦ (hcomp x).const_mul _

/-- [the vt density integrable assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper,ha), these specify the stated inputs. -/
lemma vtDensity_integrable {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) {a : ℝ} (ha : a ∈ Set.Icc ell upper) :
    Integrable (vtDensity P θ v p n ell upper a)
      (transcriptReferenceMeasure P n) := by
  unfold vtDensity
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  have hraw : Integrable
      (transcriptMixtureRealDensity P (parameterPath θ v a) p n)
      (transcriptReferenceMeasure P n) := by
    unfold transcriptMixtureRealDensity
    exact integrable_finsetSum _ fun x _ ↦ (by
      have h := (integrable_toReal_rnDeriv_mul_iff
        (transcriptComponent_ac_reference P n x)
        (f := fun _ ↦ (1 : ℝ))).2 (integrable_const (1 : ℝ))
      have hc : Integrable (transcriptComponentRealDensity P n x)
          (transcriptReferenceMeasure P n) := by
        change Integrable (fun z ↦
          ((P.transcript n x).rnDeriv (transcriptReferenceMeasure P n) z).toReal)
          (transcriptReferenceMeasure P n)
        simpa only [mul_one] using h
      exact hc.const_mul _)
  simpa only [if_pos ha] using hraw

/-- [the vt density deriv integrable assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper,ha), these specify the stated inputs. -/
lemma vtDensityDeriv_integrable {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) {a : ℝ} (ha : a ∈ Set.Icc ell upper) :
    Integrable (vtDensityDeriv P θ v p n ell upper a)
      (transcriptReferenceMeasure P n) := by
  unfold vtDensityDeriv
  simpa only [if_pos ha] using integrable_transcriptMixtureRealDerivative P
    (parameterPath θ v a) v p n

/-- [the transcript density path cont diff assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,z), these specify the stated inputs. -/
lemma transcriptDensityPath_contDiff {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (z : Transcript (Z n)) :
    ContDiff ℝ 1 (fun a ↦
      transcriptMixtureRealDensity P (parameterPath θ v a) p n z) := by
  unfold transcriptMixtureRealDensity
  apply ContDiff.sum
  intro x hx
  apply ContDiff.mul
  · unfold inputPathProbability
    apply contDiff_prod
    intro i hi
    generalize hxi : x i = j
    fin_cases j <;> simp [piTheta, parameterPath, hxi] <;> fun_prop
  · fun_prop

/-- [the vt density absolutely continuous assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,ell,upper,hellu,z), these specify the stated inputs. -/
lemma vtDensity_absolutelyContinuous {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (ell upper : ℝ) (hellu : ell < upper) (z : Transcript (Z n)) :
    AbsolutelyContinuousOnInterval
      (fun a ↦ vtDensity P θ v p n ell upper a z) ell upper := by
  have hraw : AbsolutelyContinuousOnInterval
      (fun a ↦ transcriptMixtureRealDensity P (parameterPath θ v a) p n z)
      ell upper :=
    (transcriptDensityPath_contDiff P θ v p n z).contDiffOn
      |>.absolutelyContinuousOnInterval
  rw [absolutelyContinuousOnInterval_iff] at hraw ⊢
  intro δ hδ
  obtain ⟨η, hη, hraw⟩ := hraw δ hδ
  refine ⟨η, hη, ?_⟩
  rintro ⟨m, I⟩ hI hlen
  have hbound : ∀ i ∈ Finset.range m,
      (I i).1 ∈ Set.Icc ell upper ∧ (I i).2 ∈ Set.Icc ell upper := by
    intro i hi
    have hi' := hI.1 i hi
    simpa [Set.uIcc_of_le hellu.le] using hi'
  convert hraw (m, I) hI hlen using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [vtDensity, if_pos (hbound i hi).1,
    vtDensity, if_pos (hbound i hi).2]

end CausalSmith.Stat.LdpAteEfficiencySurface
