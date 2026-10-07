module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotBridge

/-! # Uniqueness of finite transcript factorization

This file shows that the conditional cylinder factorization determines every
finite transcript law uniquely. -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- The cylinder factorization determines the joint law of each private
history and its next output. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:Z,hQ,hR,x,i), these specify the stated inputs. -/
lemma TranscriptFactorizes.map_historyPrefix_prod_apply {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)]
    {Q : SequentialKernel (Z := Z)}
    {R : (Fin n → Fin 4) → Measure (Transcript Z)}
    (hQ : ∀ i, IsMarkovKernel (Q i))
    (hR : TranscriptFactorizes Q R) (x : Fin n → Fin 4) (i : Fin n) :
    (R x).map (fun z ↦ (historyPrefix i z, z i)) =
      (R x).map (historyPrefix i) ⊗ₘ
        (Q i).comap (fun h ↦ (x i, h)) (by fun_prop) := by
  letI : IsProbabilityMeasure (R x) := (hR x).1
  letI : IsMarkovKernel (Q i) := hQ i
  have hhist : Measurable (historyPrefix i : Transcript Z → PrivateHistory i) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply j.1
  have hpair : Measurable (fun z : Transcript Z ↦ (historyPrefix i z, z i)) :=
    hhist.prodMk (measurable_pi_apply i)
  haveI : IsFiniteMeasure ((R x).map (fun z ↦ (historyPrefix i z, z i))) :=
    Measure.isFiniteMeasure_map (R x) _
  refine Measure.ext_prod (fun {B A} hB hA ↦ ?_)
  rw [Measure.map_apply hpair (hB.prod hA), Measure.compProd_apply_prod hB hA]
  change R x {z | historyPrefix i z ∈ B ∧ z i ∈ A} = _
  exact (hR x).2 i B A hB hA

/-- Every prefix marginal of a factorizing transcript law is the recursively
constructed finite-sequence prefix law. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:Z,hQ,hR,x,hk), these specify the stated inputs. -/
lemma TranscriptFactorizes.map_transcriptPrefix {n k : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)]
    {Q : SequentialKernel (Z := Z)}
    {R : (Fin n → Fin 4) → Measure (Transcript Z)}
    (hQ : ∀ i, IsMarkovKernel (Q i)) (hR : TranscriptFactorizes Q R)
    (x : Fin n → Fin 4) (hk : k ≤ n) :
    (R x).map (transcriptPrefix (Z := Z) hk) =
      prefixLaw (finiteSequenceKernel Q) x k hk := by
  induction k with
  | zero =>
      letI : IsProbabilityMeasure (R x) := (hR x).1
      let emptyHistory : History Z 0 hk := fun j ↦ j.elim0
      have hfun : transcriptPrefix (Z := Z) hk =
          (fun _ ↦ emptyHistory) := by
        funext z j
        exact j.elim0
      rw [hfun, Measure.map_const, measure_univ, one_smul]
      rfl
  | succ k ih =>
      have hprev : k ≤ n := Nat.le_of_succ_le hk
      let i : Fin n := nextIndex hk
      let hpriv : PrivateHistory (Z := Z) i ≃ᵐ History Z k hprev :=
        (historyMeasurableEquiv (Z := Z) i).symm
      have hjoint := hR.map_historyPrefix_prod_apply hQ x i
      have hjoint_fs := congrArg (Measure.map (Prod.map hpriv (id : Z i → Z i))) hjoint
      have hpair : Measurable (fun z : Transcript Z ↦
          (historyPrefix i z, z i)) := by
        apply Measurable.prodMk
        · apply measurable_pi_iff.mpr
          intro j
          exact measurable_pi_apply j.1
        · exact measurable_pi_apply i
      have hleft : Prod.map hpriv (id : Z i → Z i) ∘
          (fun z : Transcript Z ↦ (historyPrefix i z, z i)) =
          (fun z ↦ (transcriptPrefix (Z := Z) hprev z, z i)) := by
        funext z
        apply Prod.ext
        · funext j
          dsimp only [hpriv, i]
          rfl
        · rfl
      rw [Measure.map_map (by fun_prop) hpair, hleft] at hjoint_fs
      have hright : Measure.map (Prod.map hpriv (id : Z i → Z i))
          ((R x).map (historyPrefix i) ⊗ₘ
            (Q i).comap (fun h ↦ (x i, h)) (by fun_prop)) =
          (R x).map (transcriptPrefix (Z := Z) hprev) ⊗ₘ
            (finiteSequenceKernel Q i).comap
              (fun h ↦ (x i, h)) (by fun_prop) := by
        let μ := (R x).map (historyPrefix i)
        let κ := (Q i).comap (fun h ↦ (x i, h)) (by fun_prop)
        letI : IsProbabilityMeasure (R x) := (hR x).1
        letI : IsMarkovKernel (Q i) := hQ i
        letI : IsMarkovKernel κ := by dsimp [κ]; infer_instance
        rw [Causalean.Mathlib.Probability.Kernel.map_compProd_prodMap_left_eq_compProd_comap
          μ hpriv κ]
        congr 1
        · dsimp only [μ]
          rw [Measure.map_map hpriv.measurable (by
            apply measurable_pi_iff.mpr
            intro j
            exact measurable_pi_apply j.1)]
          congr 1
      rw [hright] at hjoint_fs
      calc
        (R x).map (transcriptPrefix (Z := Z) hk) =
            ((R x).map (fun z ↦
              (transcriptPrefix (Z := Z) hprev z, z i))).map
                (fun p ↦ snoc hk p.1 p.2) := by
          rw [Measure.map_map (measurable_snoc hk)
            ((measurable_transcriptPrefix hprev).prodMk (measurable_pi_apply i))]
          congr 1
          funext z j
          refine Fin.lastCases ?_ (fun l ↦ ?_) j
          · exact (Fin.snoc_last
              (α := fun j : Fin (k + 1) => Z (Fin.castLE hk j))
              (p := transcriptPrefix hprev z) (x := z i)).symm
          · exact (Fin.snoc_castSucc
              (α := fun j : Fin (k + 1) => Z (Fin.castLE hk j))
              (p := transcriptPrefix hprev z) (x := z i) l).symm
        _ = ((R x).map (transcriptPrefix (Z := Z) hprev) ⊗ₘ
              (finiteSequenceKernel Q i).comap
                (fun h ↦ (x i, h)) (by fun_prop)).map
                  (fun p ↦ snoc hk p.1 p.2) := by rw [hjoint_fs]
        _ = (prefixLaw (finiteSequenceKernel Q) x k hprev ⊗ₘ
              (finiteSequenceKernel Q i).comap
                (fun h ↦ (x i, h)) (by fun_prop)).map
                  (fun p ↦ snoc hk p.1 p.2) := by rw [ih hprev]
        _ = prefixLaw (finiteSequenceKernel Q) x (k + 1) hk := by
          exact (prefixLaw_succ (finiteSequenceKernel Q) x k hk).symm

/-- A factorizing deterministic transcript law equals the canonical finite
sequence construction. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:Z,hQ,hR,x), these specify the stated inputs. -/
theorem TranscriptFactorizes.eq_finiteSequenceTranscript {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)]
    {Q : SequentialKernel (Z := Z)}
    {R : (Fin n → Fin 4) → Measure (Transcript Z)}
    (hQ : ∀ i, IsMarkovKernel (Q i)) (hR : TranscriptFactorizes Q R)
    (x : Fin n → Fin 4) :
    R x = finiteSequenceTranscript Q x := by
  have hprefix := hR.map_transcriptPrefix hQ x (k := n) le_rfl
  have hcanon := finiteSequenceTranscript_map_prefix Q hQ x le_rfl
  have hmaps := hprefix.trans hcanon.symm
  have hid : transcriptPrefix (Z := Z) le_rfl =
      (id : Transcript Z → Transcript Z) := by
    funext z i
    rfl
  rw [hid] at hmaps
  change Measure.map (id : Transcript Z → Transcript Z) (R x) =
    Measure.map (id : Transcript Z → Transcript Z) (finiteSequenceTranscript Q x) at hmaps
  simpa only [Measure.map_id] using hmaps

end CausalSmith.Stat.LdpAteEfficiencySurface
