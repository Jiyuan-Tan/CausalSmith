module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ChainRegularity
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
Fixed histogram chains have finite range and hence all finite-measure Lp moments.
This gives the concrete L² regularity required by the independent-chain energy expansion.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

-- @node: chain_finite_range_comp
lemma chain_finite_range_comp {α β γ : Type*} {f : α → β}
    (hf : (Set.range f).Finite) (g : β → γ) :
    (Set.range (fun x => g (f x))).Finite := by
  apply (hf.image g).subset
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, ⟨x, rfl⟩, rfl⟩

-- @node: chain_finite_range_precomp
lemma chain_finite_range_precomp {α β γ : Type*} {f : β → γ}
    (hf : (Set.range f).Finite) (g : α → β) :
    (Set.range (fun x => f (g x))).Finite := by
  apply hf.subset
  rintro _ ⟨x, rfl⟩
  exact ⟨g x, rfl⟩

-- @node: chain_finite_range_binary
lemma chain_finite_range_binary {α β γ δ : Type*} {f : α → β} {g : α → γ}
    (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) (op : β → γ → δ) :
    (Set.range (fun x => op (f x) (g x))).Finite := by
  apply ((hf.prod hg).image (fun z => op z.1 z.2)).subset
  rintro _ ⟨x, rfl⟩
  exact ⟨(f x, g x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩

-- @node: chain_finite_range_sum
lemma chain_finite_range_sum {α ι E : Type*} [AddCommMonoid E]
    (s : Finset ι) (f : ι → α → E)
    (hf : ∀ i ∈ s, (Set.range (f i)).Finite) :
    (Set.range (fun x => ∑ i ∈ s, f i x)).Finite := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Set.finite_range_const : (Set.range (fun _ : α => (0 : E))).Finite)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact chain_finite_range_binary (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) (· + ·)

-- @node: finite_range_cell
lemma finite_range_cell (k : ℕ) : (Set.range (cell k)).Finite := by
  apply (Set.finite_Iic k).subset
  rintro _ ⟨x, rfl⟩
  exact min_le_left k (1 + ⌊(k : ℝ) * x⌋₊)

-- @node: pilotPi_eq_of_cell
lemma pilotPi_eq_of_cell {m : ℕ} (train : Fin m → Omega) (mx : ℕ)
    (a : Bool) {x x' : ℝ} (h : cell mx x = cell mx x') :
    pilotPi train mx a x = pilotPi train mx a x' := by
  simp only [pilotPi, armProbability, propensityPilot, cellCount, armCellCount, h]
  rfl

-- @node: pilotCoefficients_eq_of_cell
lemma pilotCoefficients_eq_of_cell {m : ℕ} (train : Fin m → Omega) (mx my J : ℕ)
    (a : Bool) {x x' : ℝ} (h : cell mx x = cell mx x') :
    pilotCoefficients train mx my J a x = pilotCoefficients train mx my J a x' := by
  unfold pilotCoefficients
  congr 1
  funext y
  simp only [densityPilot, clippedDensityPilot, armCellCount, outcomeCellCount, h]
  rfl

-- @node: chain_finite_range_of_factors
lemma chain_finite_range_of_factors {α β γ : Type*} {f : α → β} {g : α → γ}
    (hg : (Set.range g).Finite) (h : ∀ x y, g x = g y → f x = f y) :
    (Set.range f).Finite := by
  classical
  let k : Set.range g → β := fun z => f (Classical.choose z.property)
  have hk (x : α) : k ⟨g x, ⟨x, rfl⟩⟩ = f x :=
    h _ x (Classical.choose_spec (show g x ∈ Set.range g from ⟨x, rfl⟩))
  letI := hg.to_subtype
  apply (Set.finite_range k).subset
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨g x, ⟨x, rfl⟩⟩, hk x⟩

-- @node: finite_range_pilotPi
lemma finite_range_pilotPi {m : ℕ} (train : Fin m → Omega) (mx : ℕ) (a : Bool) :
    (Set.range (pilotPi train mx a)).Finite :=
  chain_finite_range_of_factors (finite_range_cell mx) (fun _ _ h =>
    pilotPi_eq_of_cell train mx a h)

-- @node: finite_range_pilotCoefficients
lemma finite_range_pilotCoefficients {m : ℕ} (train : Fin m → Omega) (mx my J : ℕ)
    (a : Bool) : (Set.range (pilotCoefficients train mx my J a)).Finite :=
  chain_finite_range_of_factors (finite_range_cell mx) (fun _ _ h =>
    pilotCoefficients_eq_of_cell train mx my J a h)

-- @node: finite_range_phiCoefficients
lemma finite_range_phiCoefficients (J : ℕ) : (Set.range (phiCoefficients J)).Finite :=
  chain_finite_range_of_factors (finite_range_cell J) (fun _ _ h => by
    simp only [phiCoefficients, h])

-- @node: finite_range_Rres
lemma finite_range_Rres {m : ℕ} (train : Fin m → Omega) (mx : ℕ) (a : Bool) :
    (Set.range (Rres train mx a)).Finite := by
  have hi : (Set.range (fun o : Omega => if A o = a then (1 : ℝ) else 0)).Finite :=
    Set.finite_range_ite Set.finite_range_const Set.finite_range_const
  have hp := chain_finite_range_precomp (finite_range_pilotPi train mx a) X
  exact chain_finite_range_binary hi hp (fun i p => (i - p) / p)

-- @node: finite_range_Vres
lemma finite_range_Vres {m : ℕ} (train : Fin m → Omega) (mx my J : ℕ) (a : Bool) :
    (Set.range (Vres train mx my J a)).Finite := by
  have hi : (Set.range (fun o : Omega => if A o = a then (1 : ℝ) else 0)).Finite :=
    Set.finite_range_ite Set.finite_range_const Set.finite_range_const
  have hp' : (Set.range (fun o : Omega => pilotPi train mx a (X o))).Finite := by
    apply (finite_range_pilotPi train mx a).subset
    rintro _ ⟨o, rfl⟩
    exact ⟨X o, rfl⟩
  have hb' : (Set.range (fun o : Omega => pilotCoefficients train mx my J a (X o))).Finite := by
    apply (finite_range_pilotCoefficients train mx my J a).subset
    rintro _ ⟨o, rfl⟩
    exact ⟨X o, rfl⟩
  have hv' : (Set.range (fun o : Omega => phiCoefficients J (Y o))).Finite := by
    apply (finite_range_phiCoefficients J).subset
    rintro _ ⟨o, rfl⟩
    exact ⟨Y o, rfl⟩
  exact chain_finite_range_binary (chain_finite_range_binary hi hp' (· / ·))
    (chain_finite_range_binary hv' hb' (· - ·)) (· • ·)

-- @node: finite_range_covariateKernel
lemma finite_range_covariateKernel (k : ℕ) :
    (Set.range (fun z : ℝ × ℝ => covariateKernel k z.1 z.2)).Finite := by
  exact Set.finite_range_ite Set.finite_range_const Set.finite_range_const

-- @node: finite_range_Uone
lemma finite_range_Uone {m : ℕ} (train : Fin m → Omega) (mx my J : ℕ)
    (b : Fin 2) (a : Bool) :
    (Set.range (fun eval => Uone train mx my J eval b a)).Finite := by
  unfold Uone
  apply chain_finite_range_comp (g := fun v => (m : ℝ)⁻¹ • v)
  apply chain_finite_range_sum
  intro i _
  exact chain_finite_range_precomp (finite_range_Vres train mx my J a) _

-- @node: finite_range_Utwo
lemma finite_range_Utwo {m : ℕ} (train : Fin m → Omega) (mx my L T J : ℕ)
    (kt : ℕ → ℕ) (b : Fin 2) (a : Bool) :
    (Set.range (fun eval => Utwo train mx my L T J kt eval b a)).Finite := by
  unfold Utwo
  apply chain_finite_range_comp (g := fun v => (m : ℝ) ^ (-2 : ℤ) • v)
  apply chain_finite_range_sum
  intro t _
  apply chain_finite_range_comp (g := Qband L J t)
  apply chain_finite_range_sum
  intro i _
  apply chain_finite_range_sum
  intro j _
  apply chain_finite_range_binary (op := fun r v => r • v)
  · apply chain_finite_range_binary (op := (· * ·))
    · exact chain_finite_range_precomp (finite_range_Rres train mx a) _
    · exact chain_finite_range_precomp (finite_range_covariateKernel (kt t))
        (fun eval : EvalData m => (X (eval (chainRole b 1) i), X (eval (chainRole b 2) j)))
  · exact chain_finite_range_precomp (finite_range_Vres train mx my J a) _

-- @node: finite_range_Uthree
lemma finite_range_Uthree {m : ℕ} (train : Fin m → Omega) (mx my J q : ℕ)
    (b : Fin 2) (a : Bool) :
    (Set.range (fun eval => Uthree train mx my J q eval b a)).Finite := by
  unfold Uthree
  apply chain_finite_range_comp (g := fun v => (m : ℝ) ^ (-3 : ℤ) • v)
  apply chain_finite_range_sum
  intro i _
  apply chain_finite_range_sum
  intro j _
  apply chain_finite_range_sum
  intro k _
  apply chain_finite_range_binary (op := fun r v => r • v)
  · apply chain_finite_range_binary (op := (· * ·))
    · apply chain_finite_range_binary (op := (· * ·))
      · apply chain_finite_range_binary (op := (· * ·))
        · exact chain_finite_range_precomp (finite_range_Rres train mx a) _
        · exact chain_finite_range_precomp (finite_range_covariateKernel q)
            (fun eval : EvalData m => (X (eval (chainRole b 3) i), X (eval (chainRole b 4) j)))
      · exact chain_finite_range_precomp (finite_range_Rres train mx a) _
    · exact chain_finite_range_precomp (finite_range_covariateKernel q)
        (fun eval : EvalData m => (X (eval (chainRole b 4) j), X (eval (chainRole b 5) k)))
  · exact chain_finite_range_precomp (finite_range_Vres train mx my J a) _

-- @node: finite_range_coefficientChain
lemma finite_range_coefficientChain {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (b : Fin 2) :
    (Set.range (fun eval => coefficientChain train mx my L T J q kt eval b)).Finite := by
  unfold coefficientChain
  apply chain_finite_range_sum
  intro a _
  apply chain_finite_range_comp (g := fun v => (if a then (1 : ℝ) else -1) • v)
  apply chain_finite_range_binary (op := (· + ·))
  · apply chain_finite_range_binary (op := (· - ·))
    · apply chain_finite_range_binary (op := (· + ·))
      · exact Set.finite_range_const
      · exact finite_range_Uone train mx my J b a
    · exact finite_range_Utwo train mx my L T J kt b a
  · exact finite_range_Uthree train mx my J q b a

-- @node: memLp_coefficientChain
lemma memLp_coefficientChain (P : ObsLaw) {m : ℕ} (train : Fin m → Omega)
    (mx my L T J q : ℕ) (kt : ℕ → ℕ) (b : Fin 2) (p : ℝ≥0∞) :
    MemLp (fun eval => coefficientChain train mx my L T J q kt eval b) p (evalLaw P m) := by
  letI : MeasurableSpace (Hj J) := borel _
  letI : BorelSpace (Hj J) := ⟨rfl⟩
  letI : IsProbabilityMeasure (evalLaw P m) := by unfold evalLaw; infer_instance
  obtain ⟨C, hC⟩ := (finite_range_coefficientChain train mx my L T J q kt b).isBounded.exists_norm_le
  apply MemLp.of_bound (measurable_coefficientChain train mx my L T J q kt b).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun eval => hC _ ⟨eval, rfl⟩)

end CausalSmith.Stat.DensityEffectRoughNull
