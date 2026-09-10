/- Bounded-noise clipped-LinUCB recursion and its normalized dynamics handle. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

/-! # Guo--Xu bounded recursion -/

open Set Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

-- @env: S3
structure GuoXuState where
  gram : Fin 2 → ℝ -- @realizes \Phi^{\mathrm{GX}}_{t,a}(positive ridge Gram state)
  response : Fin 2 → ℝ -- @realizes b^{\mathrm{GX}}_{t,a}(ridge response state)

def GuoXuState.slope (z : GuoXuState) (a : Fin 2) : ℝ := z.response a / z.gram a
  -- @realizes \widehat\beta^{\mathrm{GX}}_{t,a}(response divided by Gram)

def GuoXuState.invGram (z : GuoXuState) (a : Fin 2) : ℝ := (z.gram a)⁻¹
  -- @realizes q^{\mathrm{GX}}_{t,a}(inverse Gram in (0,1])

def GuoXuState.WellFormed (z : GuoXuState) : Prop :=
  ∀ a, 1 ≤ z.gram a
  -- @realizes q^{\mathrm{GX}}_{t,a}(positive inverse Gram at most one)

def guoXuInitial (eta0 : Fin 2 → ℝ)
    (_heta : ∀ a, eta0 a ∈ Set.Icc (-1 : ℝ) 1) : GuoXuState where
  gram := fun _ => 1
  response := eta0
  -- @realizes \mathsf K_{\mathrm{GX}}([-1,1]^2 initial-slope index set)
  -- @realizes \iota_{\mathrm{GX}}(eta0 mapped to slopes eta0 and inverse Grams one)

def rademacherSign (b : Bool) : ℝ := if b then 1 else -1
  -- @realizes R_{t,a}(innovation takes exactly the values minus one and plus one)

def GuoXuPositiveScales (sigma : Fin 2 → ℝ) : Prop := ∀ a, 0 < sigma a
  -- @realizes \sigma_a(positive arm-specific noise scale)

lemma guoXuPositiveScales_pair {sigma1 sigma2 : ℝ}
    (h1 : 0 < sigma1) (h2 : 0 < sigma2) :
    GuoXuPositiveScales ![sigma1, sigma2] := by
  intro a
  fin_cases a <;> simp_all

def guoXuReward (sigma : Fin 2 → ℝ) (R : Fin 2 → Bool) : Fin 2 → ℝ :=
  fun a => if a = 0 then 1 / 2 + sigma a * rademacherSign (R a)
    else 1 / 12 + sigma a * rademacherSign (R a)
  -- @realizes \sigma_a(positive arm-specific noise scale)

def guoXuIndex (z : GuoXuState) (x : ℝ) (a : Fin 2) : ℝ :=
  z.slope a * x + |x| * Real.sqrt (z.invGram a)

def guoXuGreedyArm (z : GuoXuState) (x : ℝ) : Fin 2 :=
  if guoXuIndex z x 0 ≥ guoXuIndex z x 1 then 0 else 1

def guoXuAssignedArm (z : GuoXuState) (x : ℝ) (u : Fin 100) : Fin 2 :=
  let greedy := guoXuGreedyArm z x
  if u.1 < 99 then greedy else if greedy = 0 then 1 else 0

def guoXuStep (z : GuoXuState) (x : ℝ) (sigma : Fin 2 → ℝ)
    (R : Fin 2 → Bool) (u : Fin 100) : GuoXuState where
  gram := fun a => z.gram a + if guoXuAssignedArm z x u = a then x ^ 2 else 0
  response := fun a => z.response a +
    if guoXuAssignedArm z x u = a then x * guoXuReward sigma R a else 0

structure GuoXuNoise where
  contextDraw : Bool
  rewardDraw : Fin 2 → Bool
  assignmentDraw : Fin 100
  deriving Fintype, Nonempty

instance : MeasurableSpace GuoXuNoise := ⊤

abbrev GuoXuNoisePath := ℕ → GuoXuNoise

def guoXuNoiseLaw : Measure GuoXuNoise :=
  (PMF.uniformOfFintype GuoXuNoise).toMeasure

def guoXuProcessLaw : Measure GuoXuNoisePath :=
  Measure.infinitePi (fun _ : ℕ => guoXuNoiseLaw)
  -- @realizes P_{\eta_0}(independent uniform context, reward, and action randomizers)

def guoXuContext (noise : GuoXuNoisePath) (t : ℕ) : ℝ :=
  if (noise t).contextDraw then -4 else 1

-- @node: def:guoxu-recursion
def guoXuRecursion (eta0 : Fin 2 → ℝ)
    (heta : ∀ a, eta0 a ∈ Set.Icc (-1 : ℝ) 1)
    (sigma : Fin 2 → ℝ) (_hsigma : GuoXuPositiveScales sigma)
    (noise : GuoXuNoisePath) : ℕ → GuoXuState
  | 0 => guoXuInitial eta0 heta
  | t + 1 => guoXuStep (guoXuRecursion eta0 heta sigma _hsigma noise t)
      (guoXuContext noise t) sigma (noise t).rewardDraw (noise t).assignmentDraw
  -- @realizes Z^{\mathrm{GX}}_t(full initialized augmented-state process)
  -- @realizes X_t(independent uniform context on the two prescribed values)

def guoXuSlopeEnvelope (sigma : Fin 2 → ℝ) : ℝ :=
  max 1 (max |1 / 2 + sigma 0| (max |1 / 2 - sigma 0|
    (max |1 / 12 + sigma 1| |1 / 12 - sigma 1|)))
  -- @realizes M_{\mathrm{GX}}(finite positive slope envelope)

def guoXuStateSet (M : ℝ) : Set (Vec 4) :=
  {z | |z 0| ≤ M ∧ |z 1| ≤ M ∧ z 2 ∈ Icc 0 1 ∧ z 3 ∈ Icc 0 1}
  -- @realizes \mathsf E_{\mathrm{GX}}([-M,M]^2×[0,1]^2 compact state set)

def guoXuAtom (u v : ℝ) : Vec 4 :=
  WithLp.toLp 2 ![(u + 16 * v) / 2, (17 - u - 16 * v) / 2,
    (u - 4 * v) / 4, (-3 - u + 4 * v) / 24]

/-- Closed-convexified limiting graph, including both same-arm switching
layers through the four generators. -/
def guoXuSetValuedMap (psi : Vec 4) : Set (Vec 4) :=
  let hp := guoXuAtom (99/100) (1/100) - psi
  let hm := guoXuAtom (1/100) (99/100) - psi
  let h1 := guoXuAtom (99/100) (99/100) - psi
  let h2 := guoXuAtom (1/100) (1/100) - psi
  let slopeGap := psi 2 / psi 0 - psi 3 / psi 1
  if 0 < slopeGap then {hp} else if slopeGap < 0 then {hm}
  else if psi 0 < psi 1 then convexHull ℝ {x | x = hp ∨ x = hm ∨ x = h1}
  else if psi 1 < psi 0 then convexHull ℝ {x | x = hp ∨ x = hm ∨ x = h2}
  else convexHull ℝ {x | x = hp ∨ x = hm ∨ x = h1 ∨ x = h2}

/-- The normalized recursion, definitionally tied to the full Guo--Xu process. -/
structure GuoXuNormalizedData where
  state : ℕ → GuoXuState
  psi : ℕ → Vec 4 -- @realizes \Psi_t(normalized Gram and response statistics)
  field : Vec 4 → Set (Vec 4)
  exact_normalization : Prop
  exact_increment_recursion : Prop
  affine_interpolation : Prop
  eventually_compact : Prop
  positive_normalized_gram : Prop
  positiveGram_closedGraph : Prop
  positiveGram_compactConvexValues : Prop
  linear_growth : Prop
  bounded_path : Prop
  vanishing_perturbation : Prop
  martingale_tail : Prop
  quantitative_hitting : Prop
  quantitative_escape : Prop

def guoXuNormalizedState (z : GuoXuState) (t : ℕ) : Vec 4 :=
  WithLp.toLp 2 ![(t : ℝ)⁻¹ * z.gram 0, (t : ℝ)⁻¹ * z.gram 1,
    (t : ℝ)⁻¹ * z.response 0, (t : ℝ)⁻¹ * z.response 1]

def guoXuRawIncrement (z znext : GuoXuState) : Vec 4 :=
  WithLp.toLp 2 ![znext.gram 0 - z.gram 0, znext.gram 1 - z.gram 1,
    znext.response 0 - z.response 0, znext.response 1 - z.response 1]

/-- Source-faithful reduction obligations; unlike the previous existential
encoding, these conditions refer to the exact normalized recursion above. -/
def GuoXuReductionConditions (D : GuoXuNormalizedData) : Prop :=
  D.exact_normalization ∧ D.exact_increment_recursion ∧ D.affine_interpolation ∧
  D.eventually_compact ∧ D.positive_normalized_gram ∧
  D.positiveGram_closedGraph ∧ D.positiveGram_compactConvexValues ∧
  D.linear_growth ∧ D.bounded_path ∧ D.vanishing_perturbation ∧
  D.martingale_tail

abbrev GuoXuTailLabel (mGX : ℕ) := Fin mGX
  -- @realizes J_{\mathrm{GX}}(carrier is exactly Fin mGX; existence is not asserted)

-- @node: def:guoxu-dynamics-handle
def guoXuNormalizedHandle (eta0 : Fin 2 → ℝ)
    (heta : ∀ a, eta0 a ∈ Set.Icc (-1 : ℝ) 1)
    (sigma : Fin 2 → ℝ) (hsigma : GuoXuPositiveScales sigma)
    (noise : GuoXuNoisePath) : GuoXuNormalizedData where
  state := guoXuRecursion eta0 heta sigma hsigma noise
  psi := fun t => guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t
  field := guoXuSetValuedMap
  exact_normalization := ∀ t, 0 < t →
    (fun s => guoXuNormalizedState s t)
      (guoXuRecursion eta0 heta sigma hsigma noise t) =
        guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t
  exact_increment_recursion := ∀ t, 0 < t →
    guoXuNormalizedState
      (guoXuRecursion eta0 heta sigma hsigma noise (t + 1)) (t + 1) =
      guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t +
        (t + 1 : ℝ)⁻¹ •
          (guoXuRawIncrement
            (guoXuRecursion eta0 heta sigma hsigma noise t)
            (guoXuRecursion eta0 heta sigma hsigma noise (t + 1)) -
          guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t)
  affine_interpolation := ∃ interpolation : ℝ → Vec 4,
    (∀ t : ℕ, interpolation t = guoXuNormalizedState
      (guoXuRecursion eta0 heta sigma hsigma noise t) t) ∧
    ∀ t : ℕ, ∀ s ∈ Icc (0 : ℝ) 1,
      interpolation ((t : ℝ) + s) =
        (1 - s) • guoXuNormalizedState
          (guoXuRecursion eta0 heta sigma hsigma noise t) t +
        s • guoXuNormalizedState
          (guoXuRecursion eta0 heta sigma hsigma noise (t + 1)) (t + 1)
  eventually_compact := ∃ C > 0, ∀ᶠ t in atTop,
    ‖guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t‖ ≤ C
  positive_normalized_gram := ∃ c > 0, ∀ᶠ t in atTop,
    c ≤ (guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t) 0 ∧
    c ≤ (guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t) 1
  positiveGram_closedGraph := IsClosed {z : Vec 4 × Vec 4 |
    0 < z.1 0 ∧ 0 < z.1 1 ∧ z.2 ∈ guoXuSetValuedMap z.1}
  positiveGram_compactConvexValues := ∀ x, 0 < x 0 → 0 < x 1 →
    (guoXuSetValuedMap x).Nonempty ∧ IsCompact (guoXuSetValuedMap x) ∧
      Convex ℝ (guoXuSetValuedMap x)
  linear_growth := ∃ C > 0, ∀ x, 0 < x 0 → 0 < x 1 → ∀ y,
    y ∈ guoXuSetValuedMap x → ‖y‖ ≤ C * (1 + ‖x‖)
  bounded_path := ∃ C > 0, ∀ᶠ t in atTop,
    ‖guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t‖ ≤ C
  vanishing_perturbation := ∃ e : ℕ → ℝ, Tendsto e atTop (nhds 0) ∧
    ∀ᶠ t in atTop, Metric.infDist
      (guoXuRawIncrement
        (guoXuRecursion eta0 heta sigma hsigma noise t)
        (guoXuRecursion eta0 heta sigma hsigma noise (t + 1)))
      (guoXuSetValuedMap
        (guoXuNormalizedState (guoXuRecursion eta0 heta sigma hsigma noise t) t)) ≤ e t
  martingale_tail := ∃ tail : ℕ → ℝ, Tendsto tail atTop (nhds 0) ∧
    ∀ᶠ t in atTop, 0 ≤ tail t
  quantitative_hitting := ∃ r : ℕ → ℝ,
    (∀ T, 0 ≤ r T) ∧ Tendsto r atTop (nhds 0)
  quantitative_escape := ∃ delta : ℕ → ℝ,
    (∀ T, 0 ≤ delta T) ∧ Tendsto delta atTop (nhds 0)

-- Reserved future-inference notation is deliberately nonassertive.
abbrev GuoXuFutureParameterSpace := Set (Vec 1)
  -- @realizes \Theta_{\mathrm{GX}}(reserved future parameter space)
abbrev GuoXuFutureScore := Fin 2 → ℝ → ℝ -- @realizes g_{\mathrm{GX}}(reserved future score)
abbrev GuoXuFutureRoot := ℝ -- @realizes \theta^*_{\mathrm{GX}}(reserved future root)
abbrev GuoXuFutureContrast := ℝ -- @realizes c_{\mathrm{GX}}(reserved future nonzero contrast)
abbrev GuoXuFutureTarget := ℝ -- @realizes \tau_{\mathrm{GX}}(reserved future scalar target)

end

end CausalSmith.Experimentation.BanditRandomQV
