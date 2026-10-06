module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.TFiniteOracle
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.LiminfLimsup

/-! # Sequential experiments and local procedures

A transcript experiment carries its history-dependent channels and the induced
finite transcript laws. The laws are pinned by the conditional cylinder
factorization, which is valid on arbitrary measurable output spaces. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

-- @env: S4
variable (θ0 : TrialParameter)

/-- For the supplied quantities and conditions, the output family is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Output Family](goal) is the displayed object. -/
abbrev OutputFamily := (n : ℕ) → Fin n → Type
  -- @realizes n(sample size)

/-- For the supplied quantities and conditions, the transcript is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Transcript](goal) is determined by [the displayed parameters](hyp:Z). -/
abbrev Transcript {n : ℕ} (Z : Fin n → Type) := ∀ i, Z i
  -- @realizes Z_i(released observation)

/-- the [history prefix](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:i,z,Z), these specify the stated inputs. -/
def historyPrefix {n : ℕ} {Z : Fin n → Type}
    (i : Fin n) (z : Transcript Z) : PrivateHistory (Z := Z) i :=
  fun j => z j.1
  -- @realizes H_{i-1}(transcript prefix)

/-- the [transcript factorizes](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:Q,R), these specify the stated inputs. -/
def TranscriptFactorizes {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)]
    (Q : SequentialKernel (Z := Z))
    (R : (Fin n → Fin 4) → Measure (Transcript Z)) : Prop :=
  ∀ x, IsProbabilityMeasure (R x) ∧
    ∀ (i : Fin n) (B : Set (PrivateHistory (Z := Z) i))
      (A : Set (Z i)),
      MeasurableSet B → MeasurableSet A →
      R x {z | historyPrefix i z ∈ B ∧ z i ∈ A} =
        ∫⁻ h in B, Q i (x i, h) A ∂(R x).map (historyPrefix i)

/-- For the supplied quantities and conditions, this procedure sequence packages the stated mathematical data. [The Procedure Sequence](goal) is determined by [the displayed parameters](hyp:Z,ε). -/
structure ProcedureSequence (Z : OutputFamily)
    [∀ n i, MeasurableSpace (Z n i)] (ε : ℝ) where
    -- @realizes (\mathcal Z_i,\mathcal G_i)(arbitrary output measurable spaces)
  channel : ∀ n, SequentialKernel (Z := Z n)
  transcript : ∀ n, (Fin n → Fin 4) → Measure (Transcript (Z n))
  factorizes : ∀ n, TranscriptFactorizes (channel n) (transcript n)
  privacy : ∀ n, SequentialLDP (Z := Z n) ε (channel n)
  estimate : ∀ n, Transcript (Z n) → ℝ
  estimate_measurable : ∀ n, Measurable (estimate n)
  -- @realizes \mathcal P(complete private procedure sequence);
  -- @realizes \widehat\tau_n(transcript-measurable estimator)

/-- For the supplied quantities and conditions, the input path probability is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The input Path Probability](goal) is determined by [the displayed parameters](hyp:θ,p,x). -/
def inputPathProbability {n : ℕ} (θ : TrialParameter) (p : ℝ)
    (x : Fin n → Fin 4) : ℝ :=
  ∏ i : Fin n, piTheta θ p (x i)

/-- the transcript law is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The transcript Law](goal) is determined by [the displayed parameters](hyp:P,θ,p,n). -/
def transcriptLaw {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n : ℕ) : Measure (Transcript (Z n)) :=
  ∑ x : Fin n → Fin 4,
    ENNReal.ofReal (inputPathProbability θ p x) • P.transcript n x
  -- @realizes P_\theta(private n-subject experiment)

/-- For the supplied quantities and conditions, the local alternative is the mathematical object specified below. [The local Alternative](goal) is determined by [the displayed parameters](hyp:θ0,h,n). -/
def localAlternative (θ0 h : TrialParameter) (n : ℕ) : TrialParameter :=
  fun k => θ0 k + h k / Real.sqrt n
  -- @realizes \theta_{n,h}(root-n perturbation)

/-- For the supplied quantities and conditions, the local index set is the mathematical object specified below. [The local Index Set](goal) is determined by [the displayed parameters](hyp:θ0,n,H). -/
def localIndexSet (θ0 : TrialParameter) (n : ℕ) (H : ℝ) :
    Set TrialParameter :=
  {h | Real.sqrt ((h 0) ^ 2 + (h 1) ^ 2) ≤ H ∧
       InteriorMeans (localAlternative θ0 h n)}
  -- @realizes \mathcal H_{n,H}(\theta_0)(Euclidean ball and interiority)

/-- the scaled error is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The scaled Error](goal) is determined by [the displayed parameters](hyp:P,θ0,h,n,z). -/
def scaledError {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ0 h : TrialParameter) (n : ℕ) (z : Transcript (Z n)) : ℝ :=
  Real.sqrt n * (P.estimate n z - contrast (localAlternative θ0 h n))
  -- @realizes U_{n,h}^{\mathcal P}(centered root-n error)

/-- the local risk is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The local Risk](goal) is determined by [the displayed parameters](hyp:P,θ0,h,p,n). -/
def localRisk {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ0 h : TrialParameter) (p : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((scaledError P θ0 h n z) ^ 2)
    ∂transcriptLaw P (localAlternative θ0 h n) p n

/-- the local worst risk is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The local Worst Risk](goal) is determined by [the displayed parameters](hyp:P,θ0,p,H,n). -/
def localWorstRisk {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ0 : TrialParameter) (p H : ℝ) (n : ℕ) : ℝ≥0∞ :=
  sSup {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ0 n H,
    u = localRisk P θ0 h p n}

/-- the local asymptotic risk is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The local Asymptotic Risk](goal) is determined by [the displayed parameters](hyp:P,θ0,p). -/
def localAsymptoticRisk {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ0 : TrialParameter) (p : ℝ) : ℝ≥0∞ :=
  sSup {u : ℝ≥0∞ | ∃ H : ℝ, 0 < H ∧
    u = Filter.liminf (fun n => localWorstRisk P θ0 p H n) atTop}

/-- the weak local limit is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Weak Local Limit](goal) is determined by [the displayed parameters](hyp:P,θ0,p,L). -/
def WeakLocalLimit {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ0 : TrialParameter) (p : ℝ) (L : Measure ℝ) : Prop :=
  ∀ h : TrialParameter, ∀ f : ℝ → ℝ, Continuous f →
    (∃ C : ℝ, ∀ u, |f u| ≤ C) →
    Tendsto (fun n =>
      ∫ z, f (scaledError P θ0 h n z)
        ∂transcriptLaw P (localAlternative θ0 h n) p n)
      atTop (nhds (∫ u, f u ∂L))

/-- the regular procedure is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The Regular Procedure](goal) is determined by [the displayed parameters](hyp:P,θ0,p). -/
def RegularProcedure {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)]
    {ε : ℝ} (P : ProcedureSequence Z ε)
    (θ0 : TrialParameter) (p : ℝ) : Prop :=
  ∃ L : Measure ℝ,
    IsProbabilityMeasure L ∧
    (∫⁻ u, ENNReal.ofReal (u ^ 2) ∂L) < ⊤ ∧
    WeakLocalLimit P θ0 p L ∧
    ∀ H : ℝ, 0 < H →
      Tendsto (fun M : ℕ =>
        Filter.limsup (fun n =>
          sSup {u : ℝ≥0∞ | ∃ h ∈ localIndexSet θ0 n H,
            u = ∫⁻ z, ENNReal.ofReal
              ((scaledError P θ0 h n z) ^ 2 *
                if M < |scaledError P θ0 h n z| then 1 else 0)
              ∂transcriptLaw P (localAlternative θ0 h n) p n})
          atTop) atTop (nhds 0)
  -- @realizes L_{\mathcal P}(common finite-second-moment limit);
  -- @realizes \mathfrak P^{\mathrm{reg}}_{\varepsilon}(\theta_0)(regular class)

-- @node: exists_selectedDirection
/-- Under the supplied quantities and conditions, the exists selected direction assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the exists selected Direction](goal).

Under the stated assumptions, the exists selected Direction. -/
lemma exists_selectedDirection (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 < ε) :
    ∃ t : ℝ, upperEnvelope θ p ε t = Jstar θ p ε := by
  have hfixed : FixedPrivacy (fun _ => ε) ε := ⟨hε, fun _ => rfl⟩
  exact (finite_oracle.{0} θ p ε hp hθ (fun _ => ε) hfixed).2.2.2.2

/-- For the supplied quantities and conditions, the selected direction is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The selected Direction](goal) is determined by [the displayed parameters](hyp:θ,p,ε,hp,hθ,hε). -/
def selectedDirection (θ : TrialParameter) (p ε : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (hε : 0 < ε) : ℝ :=
  Classical.choose (exists_selectedDirection θ p ε hp hθ hε)

-- @node: def:sequential-vt-handle
/-- For the supplied quantities and conditions, the vt handle is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The vt Handle](goal) is determined by [the displayed parameters](hyp:θ,p,ε,R,hp,hθ,hε,_hR). -/
def vtHandle (θ : TrialParameter) (p ε R : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (_hR : 0 < R) : TrialParameter × (ℝ → ℝ) :=
  (direction (selectedDirection θ p ε hp hθ hε),
   Causalean.Stat.Minimax.ObservationDependentVanTrees.smoothPrior 0 R)
  -- @realizes \mathfrak H_{\mathrm{VT}}(least-favorable direction and smooth prior)

end CausalSmith.Stat.LdpAteEfficiencySurface
