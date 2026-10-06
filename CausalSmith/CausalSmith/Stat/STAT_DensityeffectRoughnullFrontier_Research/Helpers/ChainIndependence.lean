module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainRegularity
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib

/-!
Disjoint six-role evaluation blocks and the common distribution of the two coefficient chains.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

-- @node: chainRecords
def chainRecords {m : ℕ} (b : Fin 2) (eval : EvalData m) : Fin 6 → Fin m → Omega :=
  fun r => eval (chainRole b r.val)

-- @node: repeatChainRecords
def repeatChainRecords {m : ℕ} (data : Fin 6 → Fin m → Omega) : EvalData m :=
  fun r => data (Fin.ofNat 6 r.val)

-- @node: chainRole_injective
lemma chainRole_injective (b : Fin 2) :
    Function.Injective (fun r : Fin 6 => chainRole b r.val) := by
  intro r s h
  have hval := congrArg Fin.val h
  simp only [chainRole, chainOffset, Fin.val_ofNat] at hval
  have hb := b.isLt
  have hr := r.isLt
  have hs := s.isLt
  apply Fin.ext
  omega

-- @node: measurable_chainRecords
@[fun_prop] lemma measurable_chainRecords {m : ℕ} (b : Fin 2) :
    Measurable (chainRecords (m := m) b) := by
  unfold chainRecords
  fun_prop

-- @node: measurable_repeatChainRecords
@[fun_prop] lemma measurable_repeatChainRecords {m : ℕ} :
    Measurable (repeatChainRecords (m := m)) := by
  unfold repeatChainRecords
  fun_prop

-- @node: coefficientChain_of_records
lemma coefficientChain_of_records {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (eval : EvalData m) (b : Fin 2) :
    coefficientChain train mx my L T J q kt eval b =
      coefficientChain train mx my L T J q kt (repeatChainRecords (chainRecords b eval)) 0 := by
  fin_cases b <;>
    simp [coefficientChain, Uone, Utwo, Uthree, repeatChainRecords, chainRecords,
      chainRole, chainOffset, Fin.ofNat]

-- @node: chainRecords_map
lemma chainRecords_map (P : ObsLaw) (m : ℕ) (b : Fin 2) :
    (evalLaw P m).map (chainRecords b) =
      Measure.pi (fun _ : Fin 6 => Measure.pi (fun _ : Fin m => P.law)) := by
  let μ := Measure.pi (fun _ : Fin m => P.law)
  have hind : iIndepFun (fun r : Fin 12 => fun eval : EvalData m => eval r)
      (evalLaw P m) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hsub := hind.precomp (chainRole_injective b)
  unfold chainRecords
  rw [hsub.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)]
  congr 1
  funext r
  exact (measurePreserving_eval (fun _ : Fin 12 => μ) (chainRole b r.val)).map_eq

-- @node: identDistrib_chainRecords
lemma identDistrib_chainRecords (P : ObsLaw) (m : ℕ) :
    IdentDistrib (chainRecords 0) (chainRecords 1) (evalLaw P m) (evalLaw P m) := by
  exact ⟨(measurable_chainRecords 0).aemeasurable,
    (measurable_chainRecords 1).aemeasurable,
    (chainRecords_map P m 0).trans (chainRecords_map P m 1).symm⟩

-- @node: indepFun_chainRecords
lemma indepFun_chainRecords (P : ObsLaw) (m : ℕ) :
    IndepFun (chainRecords 0) (chainRecords 1) (evalLaw P m) := by
  let S : Finset (Fin 12) := Finset.univ.filter (fun r => r.val < 6)
  let T : Finset (Fin 12) := Finset.univ.filter (fun r => 6 ≤ r.val)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro r hs ht
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    omega
  have hs (r : Fin 6) : chainRole 0 r.val ∈ S := by
    simp [S, chainRole, chainOffset, Fin.ofNat, Nat.mod_eq_of_lt (by omega : r.val < 12)]
  have ht (r : Fin 6) : chainRole 1 r.val ∈ T := by
    simp [T, chainRole, chainOffset, Fin.ofNat,
      Nat.mod_eq_of_lt (by omega : 6 + r.val < 12)]
  have hind : iIndepFun (fun r : Fin 12 => fun eval : EvalData m => eval r)
      (evalLaw P m) := iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have h := hind.indepFun_finset S T hd (fun _ => measurable_pi_apply _)
  exact h.comp
    (show Measurable (fun data : S → Fin m → Omega =>
      fun r : Fin 6 => data ⟨chainRole 0 r.val, hs r⟩) by fun_prop)
    (show Measurable (fun data : T → Fin m → Omega =>
      fun r : Fin 6 => data ⟨chainRole 1 r.val, ht r⟩) by fun_prop)

-- @node: indepFun_coefficientChain
lemma indepFun_coefficientChain (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    letI : MeasurableSpace (Hj J) := borel _
    IndepFun (fun eval => coefficientChain train mx my L T J q kt eval 0)
      (fun eval => coefficientChain train mx my L T J q kt eval 1) (evalLaw P m) := by
  letI : MeasurableSpace (Hj J) := borel _
  letI : BorelSpace (Hj J) := ⟨rfl⟩
  have hf : Measurable (fun data =>
      coefficientChain train mx my L T J q kt (repeatChainRecords data) 0) := by fun_prop
  have h := (indepFun_chainRecords P m).comp hf hf
  simpa only [Function.comp_def, ← coefficientChain_of_records] using h

-- @node: identDistrib_coefficientChain
lemma identDistrib_coefficientChain (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) :
    letI : MeasurableSpace (Hj J) := borel _
    IdentDistrib (fun eval => coefficientChain train mx my L T J q kt eval 0)
      (fun eval => coefficientChain train mx my L T J q kt eval 1)
      (evalLaw P m) (evalLaw P m) := by
  letI : MeasurableSpace (Hj J) := borel _
  letI : BorelSpace (Hj J) := ⟨rfl⟩
  have h := (identDistrib_chainRecords P m).comp
    (show Measurable (fun data =>
      coefficientChain train mx my L T J q kt (repeatChainRecords data) 0) by fun_prop)
  simpa only [Function.comp_def, ← coefficientChain_of_records] using h

end CausalSmith.Stat.DensityEffectRoughNull
