module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Procedures
public import Causalean.Mathlib.Probability.Kernel.FiniteSequence
public import Causalean.Mathlib.Probability.Kernel.CondDistrib

/-! # Bridges for the private-pilot construction

This file isolates two interfaces needed by the pilot construction: reducing
conditional cylinder factorization to a joint-law identity, and the pointwise
existence part of the saddle selector. -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory

/-- [the transcript factorizes of joint assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,R,hmarkov,hprob,hjoint), these specify the stated inputs. -/
lemma transcriptFactorizes_of_joint {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)]
    (Q : SequentialKernel (Z := Z))
    (R : (Fin n → Fin 4) → Measure (Transcript Z))
    (hmarkov : ∀ i, IsMarkovKernel (Q i))
    (hprob : ∀ x, IsProbabilityMeasure (R x))
    (hjoint : ∀ (x : Fin n → Fin 4) (i : Fin n),
      (R x).map (fun z ↦ (historyPrefix i z, z i)) =
        (R x).map (historyPrefix i) ⊗ₘ
          (Q i).comap (fun h ↦ (x i, h)) (by fun_prop)) :
    TranscriptFactorizes Q R := by
  intro x
  refine ⟨hprob x, ?_⟩
  intro i B A hB hA
  letI : IsMarkovKernel (Q i) := hmarkov i
  have hhist : Measurable (historyPrefix i : Transcript Z → PrivateHistory i) :=
    measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hpair : Measurable (fun z : Transcript Z ↦
      (historyPrefix i z, z i)) := hhist.prodMk (measurable_pi_apply i)
  change (R x) ((fun z ↦ (historyPrefix i z, z i)) ⁻¹' (B ×ˢ A)) = _
  rw [← Measure.map_apply hpair (hB.prod hA), hjoint x i,
    Measure.compProd_apply_prod hB hA]
  rfl

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- Under the supplied quantities and conditions, the exists saddle pointwise assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hε,hθ), [the exists saddle pointwise](goal).

Under the stated assumptions, the exists saddle pointwise. -/
lemma exists_saddle_pointwise (p ε : ℝ)
    (hp : InteriorAssignment p) (hε : 0 < ε) (θ : TrialParameter)
    (hθ : InteriorMeans θ) :
    ∃ α : StaircaseWeight, ∃ t : ℝ,
      staircaseFeasible ε α ∧
      (∀ u, informationObjective θ p ε α t ≤
        informationObjective θ p ε α u) ∧
      Jstar θ p ε = informationObjective θ p ε α t := by
  obtain ⟨α, hα, hopt⟩ :=
    Jstar_exists_optimal_weight θ p ε hp hθ hε.le
  obtain ⟨t, ht⟩ :=
    informationObjective_exists_minimizer θ p ε hp hθ hε.le α hα
  refine ⟨α, t, hα, ht, ?_⟩
  apply hopt.trans
  apply IsLeast.csInf_eq
  exact ⟨⟨t, rfl⟩, by rintro _ ⟨u, rfl⟩; exact ht u⟩

/-- the [fs history to private](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:i,h), these specify the stated inputs. -/
def fsHistoryToPrivate {n : ℕ} {Z : Fin n → Type}
    (i : Fin n) (h : Causalean.Mathlib.Probability.Kernel.FiniteSequence.History Z i.val (Nat.le_of_lt i.isLt)) :
    PrivateHistory (Z := Z) i := fun j =>
  h ⟨j.1.val, j.2⟩

/-- [the measurable fs history to private assertion](goal) holds. For [the displayed quantities and conditions](hyp:i), these specify the stated inputs. -/
lemma measurable_fsHistoryToPrivate {n : ℕ} {Z : Fin n → Type} [∀ i, MeasurableSpace (Z i)]
    (i : Fin n) : Measurable (fsHistoryToPrivate (Z := Z) i) := by
  apply measurable_pi_iff.mpr
  intro j
  let k : Fin i.val := ⟨j.1.val, j.2⟩
  exact measurable_pi_apply k

/-- the [private to fs history](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:i,h), these specify the stated inputs. -/
def privateToFSHistory {n : ℕ} {Z : Fin n → Type}
    (i : Fin n) (h : PrivateHistory (Z := Z) i) :
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.History Z i.val
      (Nat.le_of_lt i.isLt) := fun j =>
  h ⟨Fin.castLE (Nat.le_of_lt i.isLt) j, j.isLt⟩

/-- [the measurable private to fs history assertion](goal) holds. For [the displayed quantities and conditions](hyp:i), these specify the stated inputs. -/
lemma measurable_privateToFSHistory {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] (i : Fin n) :
    Measurable (privateToFSHistory (Z := Z) i) := by
  apply measurable_pi_iff.mpr
  intro j
  let k : {k : Fin n // k < i} :=
    ⟨Fin.castLE (Nat.le_of_lt i.isLt) j, j.isLt⟩
  exact measurable_pi_apply k

/-- [the fs history to private left inv assertion](goal) holds. For [the displayed quantities and conditions](hyp:i,h), these specify the stated inputs. -/
lemma fsHistoryToPrivate_left_inv {n : ℕ} {Z : Fin n → Type}
    (i : Fin n) (h : PrivateHistory (Z := Z) i) :
    fsHistoryToPrivate i (privateToFSHistory i h) = h := by
  funext j
  rfl

/-- [the fs history to private right inv assertion](goal) holds. For [the displayed quantities and conditions](hyp:i,h), these specify the stated inputs. -/
lemma fsHistoryToPrivate_right_inv {n : ℕ} {Z : Fin n → Type}
    (i : Fin n)
    (h : Causalean.Mathlib.Probability.Kernel.FiniteSequence.History Z i.val
      (Nat.le_of_lt i.isLt)) :
    privateToFSHistory i (fsHistoryToPrivate i h) = h := by
  funext j
  rfl

/-- the [history measurable equiv](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:i), these specify the stated inputs. -/
def historyMeasurableEquiv {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] (i : Fin n) :
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.History Z i.val
      (Nat.le_of_lt i.isLt) ≃ᵐ PrivateHistory (Z := Z) i where
  toEquiv :=
    { toFun := fsHistoryToPrivate i
      invFun := privateToFSHistory i
      left_inv := fsHistoryToPrivate_right_inv i
      right_inv := fsHistoryToPrivate_left_inv i }
  measurable_toFun := measurable_fsHistoryToPrivate i
  measurable_invFun := measurable_privateToFSHistory i

/-- the [fs transcript to transcript](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:z), these specify the stated inputs. -/
def fsTranscriptToTranscript {n : ℕ} {Z : Fin n → Type}
    (z : Causalean.Mathlib.Probability.Kernel.FiniteSequence.Transcript Z) :
    Transcript Z := fun i => z i

/-- the [transcript to fs transcript](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:z), these specify the stated inputs. -/
def transcriptToFSTranscript {n : ℕ} {Z : Fin n → Type}
    (z : Transcript Z) :
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.Transcript Z := fun i => z i

/-- [the measurable fs transcript to transcript assertion](goal) holds. -/
lemma measurable_fsTranscriptToTranscript {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] :
    Measurable (fsTranscriptToTranscript (Z := Z)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i

-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
/-- [the measurable transcript to fs transcript assertion](goal) holds. -/
lemma measurable_transcriptToFSTranscript {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] :
    Measurable (transcriptToFSTranscript (Z := Z)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply i

/-- [The finite-sequence kernel family](goal) is determined by [the displayed parameters](hyp:Q). -/
noncomputable def finiteSequenceKernel {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] (Q : SequentialKernel (Z := Z)) :
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.KernelFamily (Fin 4) Z := fun i =>
  (Q i).comap (fun xh => (xh.1, fsHistoryToPrivate i xh.2))
    (by
      apply Measurable.prodMk measurable_fst
      exact (measurable_fsHistoryToPrivate i).comp measurable_snd)

open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- [The transcript law generated by a finite sequence of kernels](goal) is determined by [the displayed parameters](hyp:Q,x). -/
noncomputable def finiteSequenceTranscript {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] (Q : SequentialKernel (Z := Z))
    (x : Fin n → Fin 4) : Measure (Transcript Z) :=
  (Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw
    (finiteSequenceKernel Q) x).map fsTranscriptToTranscript

/-- For [the supplied quantities and conditions](hyp:hk), the [transcript prefix](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:z), these specify the stated inputs. -/
def transcriptPrefix {n k : ℕ} {Z : Fin n → Type} (hk : k ≤ n)
    (z : Transcript Z) : History Z k hk :=
  fun j => z (Fin.castLE hk j)

/-- [the measurable transcript prefix assertion](goal) holds. For [the displayed quantities and conditions](hyp:hk), these specify the stated inputs. -/
lemma measurable_transcriptPrefix {n k : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] (hk : k ≤ n) :
    Measurable (transcriptPrefix (Z := Z) hk) := by
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_pi_apply (Fin.castLE hk j)

/-- The explicit finite transcript construction has exactly the library
finite-sequence prefix law. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:Q,hQ,x,hk), these specify the stated inputs. -/
lemma finiteSequenceTranscript_map_prefix {n k : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] (Q : SequentialKernel (Z := Z))
    (hQ : ∀ i, IsMarkovKernel (Q i)) (x : Fin n → Fin 4) (hk : k ≤ n) :
    Measure.map (transcriptPrefix (Z := Z) hk) (finiteSequenceTranscript Q x) =
      prefixLaw (finiteSequenceKernel Q) x k hk := by
  have hQa : ∀ i, IsMarkovKernel (finiteSequenceKernel Q i) := by
    intro i
    letI : IsMarkovKernel (Q i) := hQ i
    dsimp [finiteSequenceKernel]
    infer_instance
  unfold finiteSequenceTranscript
  rw [Measure.map_map (measurable_transcriptPrefix hk)
    measurable_fsTranscriptToTranscript]
  have hcomp : transcriptPrefix (Z := Z) hk ∘ fsTranscriptToTranscript =
      take hk := by rfl
  rw [hcomp]
  exact Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw_map_prefix
    (finiteSequenceKernel Q) hQa x k hk

/-- [the finite sequence transcript factorizes assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hmarkov), these specify the stated inputs. -/
lemma finiteSequenceTranscript_factorizes {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)]
    (Q : SequentialKernel (Z := Z))
    (hmarkov : ∀ i, IsMarkovKernel (Q i)) :
    TranscriptFactorizes Q (finiteSequenceTranscript Q) := by
  let Qa := finiteSequenceKernel Q
  have hQa : ∀ i, IsMarkovKernel (Qa i) := by
    intro i
    letI : IsMarkovKernel (Q i) := hmarkov i
    dsimp [Qa, finiteSequenceKernel]
    infer_instance
  let R : (Fin n → Fin 4) → Measure (Transcript Z) := finiteSequenceTranscript Q
  change TranscriptFactorizes Q R
  refine transcriptFactorizes_of_joint Q R hmarkov ?_ ?_
  · intro x
    letI := Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_transcriptLaw
      Qa hQa x
    exact Measure.isProbabilityMeasure_map measurable_fsTranscriptToTranscript.aemeasurable
  · intro x i
    have hi : i.val + 1 ≤ n := i.isLt
    have hidx : nextIndex hi = i := Fin.ext (by rfl)
    let e := historyMeasurableEquiv (Z := Z) i
    let ez : Z (nextIndex hi) ≃ᵐ Z i :=
      MeasurableEquiv.cast (congrArg Z hidx) (by cases hidx; rfl)
    let law := Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw Qa x
    let μ := prefixLaw Qa x i.val (Nat.le_of_succ_le hi)
    let κ : Kernel (History Z i.val (Nat.le_of_succ_le hi)) (Z (nextIndex hi)) :=
      (Qa (nextIndex hi)).comap
      (fun h => (x (nextIndex hi), h)) (by fun_prop)
    let f := fun z : Causalean.Mathlib.Probability.Kernel.FiniteSequence.Transcript Z =>
      (take (Nat.le_of_succ_le hi) z, z (nextIndex hi))
    have hf : Measurable f := by
      dsimp only [f]
      apply Measurable.prodMk
      · apply measurable_pi_iff.mpr
        intro j
        exact measurable_pi_apply (Fin.castLE (Nat.le_of_succ_le hi) j)
      · exact measurable_pi_apply (nextIndex hi)
    have hbase : Measure.map f law = μ ⊗ₘ κ := by
      exact Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw_map_take_next
        Qa hQa x i.val hi
    haveI : IsProbabilityMeasure μ :=
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_prefixLaw
        Qa hQa x i.val _
    haveI : IsMarkovKernel κ := by dsimp [κ]; infer_instance
    haveI : IsMarkovKernel (κ.map ez) :=
      ProbabilityTheory.Kernel.IsMarkovKernel.map κ ez.measurable
    have hpair :
        (fun z : Transcript Z => (historyPrefix i z, z i)) ∘
            fsTranscriptToTranscript = Prod.map e ez ∘ f := by
      funext z
      apply Prod.ext
      · funext j
        rfl
      · cases hidx
        rfl
    have hownPair : Measurable (fun z : Transcript Z =>
        (historyPrefix i z, z i)) := by
      apply Measurable.prodMk
      · apply measurable_pi_iff.mpr
        intro j
        exact measurable_pi_apply j.1
      · exact measurable_pi_apply i
    have hjointRaw : Measure.map (Prod.map e ez) (μ ⊗ₘ κ) =
        Measure.map e μ ⊗ₘ (κ.map ez).comap e.symm e.symm.measurable := by
      calc
        _ = Measure.map (Prod.map e (id : Z i → Z i))
              (Measure.map (Prod.map (id : _ → _) ez) (μ ⊗ₘ κ)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            congr 1
        _ = Measure.map (Prod.map e (id : Z i → Z i)) (μ ⊗ₘ κ.map ez) := by
            rw [← Measure.compProd_map ez.measurable]
        _ = _ := Causalean.Mathlib.Probability.Kernel.map_compProd_prodMap_left_eq_compProd_comap
          μ e (κ.map ez)
    have hpref : Measurable (historyPrefix i : Transcript Z → PrivateHistory i) := by
      apply measurable_pi_iff.mpr
      intro j
      exact measurable_pi_apply j.1
    have hμ : Measure.map e μ = Measure.map (historyPrefix i) (R x) := by
      have hprefix := Causalean.Mathlib.Probability.Kernel.FiniteSequence.transcriptLaw_map_prefix
        Qa hQa x i.val (Nat.le_of_succ_le hi)
      calc
        Measure.map e μ = Measure.map e (Measure.map (take (Nat.le_of_succ_le hi)) law) := by
          rw [hprefix]
        _ = Measure.map (e ∘ take (Nat.le_of_succ_le hi)) law := by
          rw [Measure.map_map e.measurable (by
            apply measurable_pi_iff.mpr
            intro j
            exact measurable_pi_apply (Fin.castLE (Nat.le_of_succ_le hi) j))]
        _ = Measure.map (historyPrefix i ∘ fsTranscriptToTranscript) law := by
          congr 1
        _ = Measure.map (historyPrefix i) (Measure.map fsTranscriptToTranscript law) := by
          rw [Measure.map_map hpref measurable_fsTranscriptToTranscript]
        _ = _ := by rfl
    have hκ : (κ.map ez).comap e.symm e.symm.measurable =
        (Q i).comap (fun h => (x i, h)) (by fun_prop) := by
      ext h A hA
      rw [ProbabilityTheory.Kernel.comap_apply,
        ProbabilityTheory.Kernel.map_apply' _ _ _ hA,
        ProbabilityTheory.Kernel.comap_apply,
        ProbabilityTheory.Kernel.comap_apply]
      dsimp only [Qa, finiteSequenceKernel]
      rw [ProbabilityTheory.Kernel.comap_apply]
      cases hidx
      · change ((Q i) (x i,
          fsHistoryToPrivate i (privateToFSHistory i h))) A =
          ((Q i) (x i, h)) A
        rw [fsHistoryToPrivate_left_inv]
      · exact ez.measurable
    dsimp only [R]
    unfold finiteSequenceTranscript
    rw [Measure.map_map hownPair measurable_fsTranscriptToTranscript, hpair,
      ← Measure.map_map (by fun_prop) hf, hbase, hjointRaw, hμ, hκ]
    rfl

/-- [the exists transcript factorization assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hmarkov), these specify the stated inputs. -/
lemma exists_transcript_factorization {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)]
    (Q : SequentialKernel (Z := Z))
    (hmarkov : ∀ i, IsMarkovKernel (Q i)) :
    ∃ R : (Fin n → Fin 4) → Measure (Transcript Z),
      TranscriptFactorizes Q R :=
  ⟨finiteSequenceTranscript Q, finiteSequenceTranscript_factorizes Q hmarkov⟩
end CausalSmith.Stat.LdpAteEfficiencySurface
