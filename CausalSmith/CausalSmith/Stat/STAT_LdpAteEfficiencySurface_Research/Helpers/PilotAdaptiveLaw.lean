module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveInputs

/-! # Exact finite-law bridges for the adaptive pilot protocol -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

variable (select : TrialParameter → StaircaseWeight × ℝ × ℝ)

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- Under [the supplied quantities and conditions](hyp:hmn), [the fin prod split assertion](goal) holds. For [the displayed quantities and conditions](hyp:f,g), these specify the stated inputs. -/
lemma fin_prod_split {M : Type*} [CommMonoid M] {m n : ℕ} (hmn : m ≤ n)
    (f : Fin m → M) (g : Fin (n - m) → M) :
    (∏ i : Fin n, if hi : i.val < m then f ⟨i.val, hi⟩
      else g ⟨i.val - m, by omega⟩) =
      (∏ j : Fin m, f j) * ∏ j : Fin (n - m), g j := by
  let e : Fin (m + (n - m)) ≃ Fin n := Fin.castOrderIso (Nat.add_sub_of_le hmn)
  rw [← e.prod_comp]
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    simp [e]
  · apply Finset.prod_congr rfl
    intro j _
    simp [e]

/-- For [the supplied quantities and conditions](hyp:hmn), the [pilot adaptive encode](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:u,v), these specify the stated inputs. -/
def pilotAdaptiveEncode {m n : ℕ} (hmn : m ≤ n)
    (u : Fin m → Fin 4) (v : Fin (n - m) → Fin 14) :
    Transcript (pilotOutputFamily n) := fun i =>
  if hi : i.val < m then
    Sum.inl (u ⟨i.val, hi⟩)
  else
    Sum.inr (v ⟨i.val - m, by omega⟩)

/-- Under [the supplied quantities and conditions](hyp:hmn), [the pilot adaptive encode pilot assertion](goal) holds. For [the displayed quantities and conditions](hyp:u,v,j), these specify the stated inputs. -/
lemma pilotAdaptiveEncode_pilot {m n : ℕ} (hmn : m ≤ n)
    (u : Fin m → Fin 4) (v : Fin (n - m) → Fin 14) (j : Fin m) :
    pilotAdaptiveEncode hmn u v (Fin.castLE hmn j) = Sum.inl (u j) := by
  simp [pilotAdaptiveEncode]

/-- Under [the supplied quantities and conditions](hyp:hmn), [the pilot adaptive encode main assertion](goal) holds. For [the displayed quantities and conditions](hyp:u,v,j), these specify the stated inputs. -/
lemma pilotAdaptiveEncode_main {m n : ℕ} (hmn : m ≤ n)
    (u : Fin m → Fin 4) (v : Fin (n - m) → Fin 14) (j : Fin (n - m)) :
    pilotAdaptiveEncode hmn u v
        ⟨m + j.val, by omega⟩ = Sum.inr (v j) := by
  simp [pilotAdaptiveEncode]

/-- For the supplied quantities and conditions, the pilot adaptive prefix theta is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The pilot Adaptive Prefix Theta](goal) is determined by [the displayed parameters](hyp:p,ε,mseq,hmn,u). -/
def pilotAdaptivePrefixTheta (p ε : ℝ) (mseq : ℕ → ℕ) {n : ℕ}
    (hmn : mseq n ≤ n) (u : Fin (mseq n) → Fin 4) : TrialParameter :=
  pilotTheta p ε mseq (pilotAdaptiveEncode hmn u (fun _ => 0))

/-- Under [the supplied quantities and conditions](hyp:p,mseq), [the pilot theta pilot adaptive encode assertion](goal) holds. For [the displayed quantities and conditions](hyp:hmn,u,v), these specify the stated inputs. -/
lemma pilotTheta_pilotAdaptiveEncode (p ε : ℝ) (mseq : ℕ → ℕ) {n : ℕ}
    (hmn : mseq n ≤ n) (u : Fin (mseq n) → Fin 4)
    (v : Fin (n - mseq n) → Fin 14) :
    pilotTheta p ε mseq (pilotAdaptiveEncode hmn u v) =
      pilotAdaptivePrefixTheta p ε mseq hmn u := by
  have hfreq (k : Fin 4) :
      pilotFrequency mseq (pilotAdaptiveEncode hmn u v) k =
        pilotFrequency mseq (pilotAdaptiveEncode hmn u (fun _ => 0)) k := by
    unfold pilotFrequency
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val < mseq n <;> simp [pilotAdaptiveEncode, hi]
  funext a
  simp only [pilotTheta, pilotAdaptivePrefixTheta]
  rw [hfreq 1, hfreq 3]

/-- [the finite sequence transcript singleton apply assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,hQ,x,t), these specify the stated inputs. -/
lemma finiteSequenceTranscript_singleton_apply {n : ℕ} {Z : Fin n → Type}
    [∀ i, MeasurableSpace (Z i)] [∀ i, MeasurableSingletonClass (Z i)]
    (Q : SequentialKernel (Z := Z)) (hQ : ∀ i, IsMarkovKernel (Q i))
    (x : Fin n → Fin 4) (t : Transcript Z) :
    finiteSequenceTranscript Q x {t} =
      ∏ i : Fin n, Q i (x i, fun j => t j.1) {t i} := by
  have hQa : ∀ i, IsMarkovKernel (finiteSequenceKernel Q i) := by
    intro i
    letI : IsMarkovKernel (Q i) := hQ i
    dsimp [finiteSequenceKernel]
    infer_instance
  unfold finiteSequenceTranscript
  rw [Measure.map_apply measurable_fsTranscriptToTranscript
    (measurableSet_singleton t)]
  have hpre : fsTranscriptToTranscript ⁻¹' ({t} : Set (Transcript Z)) =
      {transcriptToFSTranscript t} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      funext i
      exact congrFun hy i
    · intro hy
      subst y
      rfl
  rw [hpre, transcriptLaw_singleton (finiteSequenceKernel Q) hQa]
  apply Finset.prod_congr rfl
  intro i _
  rfl

/-- Under [the supplied quantities and conditions](hyp:m), [the pilot history frequency restrict eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:i,hi,z,k), these specify the stated inputs. -/
lemma pilotHistoryFrequency_restrict_eq (m : ℕ → ℕ) {n : ℕ}
    (i : Fin n) (hi : m n ≤ i.val)
    (z : Transcript (pilotOutputFamily n)) (k : Fin 4) :
    pilotHistoryFrequency m i (fun j => z j.1) k = pilotFrequency m z k := by
  have hmn : m n ≤ n := hi.trans (Nat.le_of_lt i.isLt)
  unfold pilotHistoryFrequency pilotFrequency
  congr 1
  have hleft :
      (∑ j : {j : Fin n // j < i},
        if j.1.val < m n ∧ z j.1 = Sum.inl k then (1 : ℝ) else 0) =
      ∑ a : Fin (m n),
        if z (Fin.castLE hmn a) = Sum.inl k then (1 : ℝ) else 0 := by
    have hfilter :
        (∑ j : {j : Fin n // j < i},
          if j.1.val < m n ∧ z j.1 = Sum.inl k then (1 : ℝ) else 0) =
        ∑ j ∈ (Finset.univ.filter fun j : {j : Fin n // j < i} =>
          j.1.val < m n), if z j.1 = Sum.inl k then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.1.val < m n <;> simp [hj]
    rw [hfilter]
    symm
    apply Finset.sum_bij (fun a _ =>
      ⟨Fin.castLE hmn a, by
        change a.val < i.val
        exact Nat.lt_of_lt_of_le a.isLt hi⟩)
    · intro a _
      simp
    · intro a _ b _ hab
      exact Fin.ext (congrArg (fun x => x.1.val) hab)
    · intro j hj
      have hjlt : j.1.val < m n := (Finset.mem_filter.mp hj).2
      let a : Fin (m n) := ⟨j.1.val, hjlt⟩
      refine ⟨a, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      exact Fin.ext rfl
    · intro a _
      simp
  rw [hleft]
  symm
  rw [← fin_sum_ite_lt hmn (fun a : Fin (m n) =>
    if z (Fin.castLE hmn a) = Sum.inl k then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < m n <;> simp [hj]

/-- Under [the supplied quantities and conditions](hyp:p,m), [the pilot history theta restrict eq assertion](goal) holds. For [the displayed quantities and conditions](hyp:i,hi,z), these specify the stated inputs. -/
lemma pilotHistoryTheta_restrict_eq (p ε : ℝ) (m : ℕ → ℕ) {n : ℕ}
    (i : Fin n) (hi : m n ≤ i.val)
    (z : Transcript (pilotOutputFamily n)) :
    pilotHistoryTheta p ε m i (fun j => z j.1) = pilotTheta p ε m z := by
  funext a
  simp only [pilotHistoryTheta, pilotTheta]
  rw [pilotHistoryFrequency_restrict_eq m i hi z 1,
    pilotHistoryFrequency_restrict_eq m i hi z 3]

/-- Under the supplied quantities and conditions, the pilot protocol main singleton assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hi), [the pilot Protocol main singleton](goal).

Under the stated assumptions, the pilot Protocol main singleton. -/
lemma pilotProtocol_main_singleton (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (i : Fin n) (hi : m n ≤ i.val) (x : Fin 4)
    (z : Transcript (pilotOutputFamily n)) (s : Fin 14) :
    pilotProtocol p ε m (select) n i
        (x, fun j => z j.1) {Sum.inr s} =
      ENNReal.ofReal
        ((select (pilotTheta p ε m z)).1 s *
          patternRay ε s x) := by
  simp only [pilotProtocol]
  change (if i.val < m n then
      ((rrPilotKernel ε x).map Sum.inl)
    else
      ((staircaseChannel ε
        (select
          (pilotHistoryTheta p ε m i (fun j => z j.1))).1 x).map Sum.inr))
      {Sum.inr s} = _
  rw [if_neg (not_lt_of_ge hi), pilotHistoryTheta_restrict_eq p ε m i hi z]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : (Sum.inr : Fin 14 → PilotOutput) ⁻¹'
      ({Sum.inr s} : Set PilotOutput) = ({s} : Set (Fin 14)) := by
    ext y
    simp
  rw [hpre]
  change (Measure.count.withDensity (fun u : Fin 14 => ENNReal.ofReal
    ((select (pilotTheta p ε m z)).1 u *
      patternRay ε u x))) {s} = _
  rw [withDensity_apply _ (measurableSet_singleton s)]
  simp

/-- Under the supplied quantities and conditions, the pilot protocol main output singleton assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hi), [the pilot Protocol main output singleton](goal).

Under the stated assumptions, the pilot Protocol main output singleton. -/
lemma pilotProtocol_main_output_singleton
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) {n : ℕ}
    (i : Fin n) (hi : m n ≤ i.val)
    (z : Transcript (pilotOutputFamily n)) (s : Fin 14) :
    ∑ x : Fin 4, ENNReal.ofReal (piTheta θ p x) *
        pilotProtocol p ε m (select) n i
          (x, fun j => z j.1) {Sum.inr s} =
      ENNReal.ofReal
        (adaptiveMainMass select θ (pilotTheta p ε m z) p ε s) := by
  let α := (select (pilotTheta p ε m z)).1
  have hη : InteriorMeans (pilotTheta p ε m z) := by
    rw [← pilotHistoryTheta_restrict_eq p ε m i hi z]
    exact pilotHistoryTheta_interior p ε m i (fun j => z j.1)
  have hα : staircaseFeasible ε α :=
    ((hselect.1).2 _ hη).1
  simp_rw [pilotProtocol_main_singleton select p ε m hselect hp hε i hi _ z s]
  have hpi (x : Fin 4) : 0 ≤ piTheta θ p x :=
    (piTheta_pos_interior θ p hp hθ x).le
  simp_rw [← ENNReal.ofReal_mul (hpi _)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    simp only [adaptiveMainMass, patternMass]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · intro x _
    exact mul_nonneg (hpi x)
      (mul_nonneg (hα.1 s) (by
        unfold patternRay privacyIncrement privacyRatio
        cases patternContains s x <;> simp <;> positivity))

/-- Under the supplied quantities and conditions, the pilot protocol pilot output singleton assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hi), [the pilot Protocol pilot output singleton](goal).

Under the stated assumptions, the pilot Protocol pilot output singleton. -/
lemma pilotProtocol_pilot_output_singleton
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) {n : ℕ}
    (i : Fin n) (hi : i.val < m n)
    (h : PrivateHistory (Z := pilotOutputFamily n) i) (k : Fin 4) :
    ∑ x : Fin 4, ENNReal.ofReal (piTheta θ p x) *
        pilotProtocol p ε m (select) n i (x, h)
          {Sum.inl k} =
      ENNReal.ofReal
        (∑ x : Fin 4, piTheta θ p x * rrPilotProbability ε x k) := by
  have hstage (x : Fin 4) :
      pilotProtocol p ε m (select) n i (x, h)
          {Sum.inl k} = ENNReal.ofReal (rrPilotProbability ε x k) := by
    simp only [pilotProtocol]
    change (if i.val < m n then ((rrPilotKernel ε x).map Sum.inl)
      else _) {Sum.inl k} = _
    rw [if_pos hi, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    have hpre : (Sum.inl : Fin 4 → PilotOutput) ⁻¹'
        ({Sum.inl k} : Set PilotOutput) = {k} := by
      ext y
      simp
    rw [hpre, rrPilotKernel_singleton]
  simp_rw [hstage]
  have hpi (x : Fin 4) : 0 ≤ piTheta θ p x :=
    (piTheta_pos_interior θ p hp hθ x).le
  simp_rw [← ENNReal.ofReal_mul (hpi _)]
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro x _
  exact mul_nonneg (hpi x) (by
    unfold rrPilotProbability
    split_ifs <;> positivity)

/-- Under the supplied quantities and conditions, the pilot adaptive joint singleton assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hθ,hε,hmn), [the pilot Adaptive joint singleton](goal).

Under the stated assumptions, the pilot Adaptive joint singleton. -/
lemma pilotAdaptive_joint_singleton
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε) {n : ℕ}
    (hmn : m n ≤ n) (u : Fin (m n) → Fin 4)
    (v : Fin (n - m n) → Fin 14) :
    transcriptLaw (pilotEstimator p ε m select hselect hp hε) θ p n
        {pilotAdaptiveEncode hmn u v} =
      (∏ j : Fin (m n), ENNReal.ofReal
        (∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j))) *
      ∏ j : Fin (n - m n), ENNReal.ofReal
        (adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
          p ε (v j)) := by
  let t := pilotAdaptiveEncode hmn u v
  let Q := pilotProtocol p ε m (select) n
  let F : (i : Fin n) → Fin 4 → ℝ≥0∞ := fun i a =>
    ENNReal.ofReal (piTheta θ p a) *
      Q i (a, fun j => t j.1) {t i}
  have hQ : ∀ i, IsMarkovKernel (Q i) := by
    intro i
    exact (pilotProtocol_private p ε m select hselect hp hε n).1 i
  have hpi (a : Fin 4) : 0 ≤ piTheta θ p a :=
    (piTheta_pos_interior θ p hp hθ a).le
  have hpath (x : Fin n → Fin 4) :
      ENNReal.ofReal (inputPathProbability θ p x) =
        ∏ i : Fin n, ENNReal.ofReal (piTheta θ p (x i)) := by
    change ENNReal.ofReal (∏ i : Fin n, piTheta θ p (x i)) = _
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    exact hpi (x i)
  have hstage (i : Fin n) :
      (∑ a : Fin 4, F i a) =
        if hi : i.val < m n then
          ENNReal.ofReal
            (∑ a : Fin 4, piTheta θ p a *
              rrPilotProbability ε a (u ⟨i.val, hi⟩))
        else
          ENNReal.ofReal
            (adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
              p ε (v ⟨i.val - m n, by omega⟩)) := by
    by_cases hi : i.val < m n
    · rw [dif_pos hi]
      have ht : t i = Sum.inl (u ⟨i.val, hi⟩) := by
        simp [t, pilotAdaptiveEncode, hi]
      simp only [F, Q]
      rw [ht]
      exact pilotProtocol_pilot_output_singleton select θ p ε m hselect hp hθ hε i hi
        (fun j => t j.1) (u ⟨i.val, hi⟩)
    · rw [dif_neg hi]
      have himain : m n ≤ i.val := Nat.le_of_not_gt hi
      have ht : t i = Sum.inr (v ⟨i.val - m n, by omega⟩) := by
        simp [t, pilotAdaptiveEncode, hi]
      simp only [F, Q]
      rw [ht]
      rw [pilotProtocol_main_output_singleton select θ p ε m hselect hp hθ hε i himain t]
      rw [pilotTheta_pilotAdaptiveEncode p ε m hmn u v]
  unfold transcriptLaw
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  change (∑ x : Fin n → Fin 4,
    ENNReal.ofReal (inputPathProbability θ p x) *
      finiteSequenceTranscript Q x {t}) = _
  simp_rw [finiteSequenceTranscript_singleton_apply Q hQ]
  calc
    (∑ x : Fin n → Fin 4,
        ENNReal.ofReal (inputPathProbability θ p x) *
          ∏ i : Fin n, Q i (x i, fun j => t j.1) {t i}) =
        ∑ x : Fin n → Fin 4, ∏ i : Fin n, F i (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hpath x, ← Finset.prod_mul_distrib]
    _ = ∏ i : Fin n, ∑ a : Fin 4, F i a :=
      (Fintype.prod_sum F).symm
    _ = ∏ i : Fin n, if hi : i.val < m n then
          ENNReal.ofReal
            (∑ a : Fin 4, piTheta θ p a *
              rrPilotProbability ε a (u ⟨i.val, hi⟩))
        else
          ENNReal.ofReal
            (adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
              p ε (v ⟨i.val - m n, by omega⟩)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact hstage i
    _ = _ := by
      simpa using fin_prod_split hmn
        (fun j : Fin (m n) => ENNReal.ofReal
          (∑ a : Fin 4, piTheta θ p a * rrPilotProbability ε a (u j)))
        (fun j : Fin (n - m n) => ENNReal.ofReal
          (adaptiveMainMass select θ (pilotAdaptivePrefixTheta p ε m hmn u)
            p ε (v j)))

/-- Under the supplied quantities and conditions, the pilot protocol main wrong tag assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hi), [the pilot Protocol main wrong Tag](goal).

Under the stated assumptions, the pilot Protocol main wrong Tag. -/
lemma pilotProtocol_main_wrongTag (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (i : Fin n) (hi : m n ≤ i.val) (x : Fin 4)
    (h : PrivateHistory (Z := pilotOutputFamily n) i) (k : Fin 4) :
    pilotProtocol p ε m (select) n i (x, h)
        {Sum.inl k} = 0 := by
  simp only [pilotProtocol]
  change (if i.val < m n then
      ((rrPilotKernel ε x).map Sum.inl)
    else
      ((staircaseChannel ε
        (select (pilotHistoryTheta p ε m i h)).1 x).map Sum.inr))
      {Sum.inl k} = 0
  rw [if_neg (not_lt_of_ge hi), Measure.map_apply (by fun_prop)
    (measurableSet_singleton _)]
  have hpre : (Sum.inr : Fin 14 → PilotOutput) ⁻¹'
      ({Sum.inl k} : Set PilotOutput) = ∅ := by
    ext y
    simp
  rw [hpre]
  simp

/-- Under the supplied quantities and conditions, the pilot protocol pilot wrong tag assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hselect,hp,hε,hi), [the pilot Protocol pilot wrong Tag](goal).

Under the stated assumptions, the pilot Protocol pilot wrong Tag. -/
lemma pilotProtocol_pilot_wrongTag (p ε : ℝ) (m : ℕ → ℕ)
    (hselect : StrongSaddleSelection p ε select)
    (hp : InteriorAssignment p) (hε : 0 < ε) {n : ℕ}
    (i : Fin n) (hi : i.val < m n) (x : Fin 4)
    (h : PrivateHistory (Z := pilotOutputFamily n) i) (s : Fin 14) :
    pilotProtocol p ε m (select) n i (x, h)
        {Sum.inr s} = 0 := by
  simp only [pilotProtocol]
  change (if i.val < m n then ((rrPilotKernel ε x).map Sum.inl)
    else _) {Sum.inr s} = 0
  rw [if_pos hi, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : (Sum.inl : Fin 4 → PilotOutput) ⁻¹'
      ({Sum.inr s} : Set PilotOutput) = ∅ := by
    ext y
    simp
  rw [hpre]
  simp

end CausalSmith.Stat.LdpAteEfficiencySurface
