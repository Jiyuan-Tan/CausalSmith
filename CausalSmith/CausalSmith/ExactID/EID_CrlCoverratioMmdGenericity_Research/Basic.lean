import Causalean.Graph.DAG
import Causalean.Graph.DSep.Separation
import Causalean.Mathlib.CondIndep
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Cover-ratio causal representation model

This file fixes the latent finite-DAG mechanism, its observed environment family,
and the population assumptions shared by the paper's results.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology UniformConvergence

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-! ## Latent mechanism world -/

abbrev LatentState (n : ℕ) := Fin n → ℝ -- @realizes V(carrier [0,1]^n via latentCube)

/-- The closed latent cube. -/
def latentCube (n : ℕ) : Set (LatentState n) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) -- @realizes V(range [0,1]^n)

/-- A sign vector with every coordinate equal to `-1` or `1`. -/
structure SignVector (n : ℕ) where
  value : Fin n → ℝ -- @realizes s(carrier Fin n → {-1,+1})
  signed : ∀ i, value i = -1 ∨ value i = 1 -- @realizes s(range {-1,+1})

/-- A family of observational conditional densities and parent-independent intervention
densities. The proof field makes the parent scope part of the carrier. -/
structure Mechanism (n : ℕ) (G : Causalean.DAG (Fin n)) where
  p : Fin n → LatentState n → ℝ -- @realizes \(p_i\)(conditional-density carrier)
  q : Fin n → ℝ → ℝ -- @realizes \(q_i\)(parent-independent density carrier)
  parent_local : ∀ i v w, v i = w i →
    (∀ j ∈ G.parents i, v j = w j) → p i v = p i w
    -- @realizes \(\operatorname{pa}_G(i)\)(p_i depends only on own coordinate and parents)

/-- Values and the first two ambient derivatives of every mechanism slot, each equipped with
uniform convergence on its closed cube.  Pulling this topology back gives the paper's finite
product `C²` topology rather than Lean's default pointwise function topology. -/
def mechanismC2Coordinates {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G) :=
  ((fun i => UniformOnFun.ofFun {latentCube n} (θ.p i)),
    (fun i => UniformOnFun.ofFun {latentCube n} (fderiv ℝ (θ.p i))),
    (fun i => UniformOnFun.ofFun {latentCube n} (iteratedFDeriv ℝ 2 (θ.p i))),
    (fun i => UniformOnFun.ofFun {Set.Icc (0 : ℝ) 1} (θ.q i)),
    (fun i => UniformOnFun.ofFun {Set.Icc (0 : ℝ) 1} (fderiv ℝ (θ.q i))),
    (fun i => UniformOnFun.ofFun {Set.Icc (0 : ℝ) 1} (iteratedFDeriv ℝ 2 (θ.q i))))

instance {n : ℕ} {G : Causalean.DAG (Fin n)} : TopologicalSpace (Mechanism n G) :=
  TopologicalSpace.induced mechanismC2Coordinates inferInstance

/-- The intervention distribution function `Q_i(v) = ∫₀ᵛ q_i(u) du`. -/
def interventionCDF {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ : Mechanism n G) (i : Fin n) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..v, θ.q i u -- @realizes \(Q_i\)(integral of q_i)

/-- The observational product density. -/
def observationalDensity {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ : Mechanism n G) (v : LatentState n) : ℝ :=
  ∏ i, θ.p i v -- @realizes \(p^0\)(product of observational mechanisms)

/-- The density after replacing exactly the target mechanism by `q_i`. -/
def interventionalDensity {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ : Mechanism n G) (i : Fin n) (v : LatentState n) : ℝ :=
  θ.q i (v i) * ∏ l ∈ Finset.univ.erase i, θ.p l v
  -- @realizes \(p^i\)(q_i times all non-target p_l)

/-- The observational law on the compact latent cube. -/
def observationalLaw {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ : Mechanism n G) : Measure (LatentState n) :=
  (volume.restrict (latentCube n)).withDensity
    (fun v => ENNReal.ofReal (observationalDensity θ v))
  -- @realizes \(p^0\)(law with observational product density)

/-- The target-`i` perfect-intervention law on the latent cube. -/
def interventionalLaw {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ : Mechanism n G) (i : Fin n) : Measure (LatentState n) :=
  (volume.restrict (latentCube n)).withDensity
    (fun v => ENNReal.ofReal (interventionalDensity θ i v))
  -- @realizes \(p^i\)(law with one replaced mechanism)

/-- Finite-coordinate projection, used to state conditional independence. -/
def coordinateProjection {n : ℕ} (S : Finset (Fin n)) (v : LatentState n) :
    (j : {j // j ∈ S}) → ℝ := fun j => v j

/-- Conditional independence of latent coordinate blocks under the observational law. -/
def CondIndepCoordinates {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ : Mechanism n G) (X Y Z : Finset (Fin n)) : Prop :=
  ∃ hμ : MeasureTheory.IsFiniteMeasure (observationalLaw θ),
    letI := hμ
    ∃ _hX : Measurable (coordinateProjection X),
      ∃ _hY : Measurable (coordinateProjection Y),
        ∃ hZ : Measurable (coordinateProjection Z),
          ProbabilityTheory.CondIndepFun
            (MeasurableSpace.comap (coordinateProjection Z) inferInstance)
            hZ.comap_le (coordinateProjection X) (coordinateProjection Y)
            (observationalLaw θ)

/-- The own-coordinate derivative of the latent log density ratio. -/
def ownLogRatioDerivative {n : ℕ} {G : Causalean.DAG (Fin n)}
    (θ : Mechanism n G) (i : Fin n) (v : LatentState n) : ℝ :=
  derivWithin (fun z => Real.log (θ.q i z / θ.p i (Function.update v i z)))
    (Set.Icc (0 : ℝ) 1) (v i)

-- @env: S1
variable {n : ℕ} -- @realizes n(number of latent nodes)
  (G : Causalean.DAG (Fin n)) -- @realizes G(finite labeled DAG on Fin n)
  (s : SignVector n) -- @realizes s(prescribed derivative signs)

-- @realizes \([n]\)(implemented as Fin n)
-- @realizes \(j\lessdot_G i\)(CovBy for DAG.isAncestor)
abbrev ancestralCover (G : Causalean.DAG (Fin n)) : Fin n → Fin n → Prop :=
  @CovBy (Fin n) ⟨G.isAncestor⟩

-- @node: ass:positive-normalized-smooth-mechanisms
/-- Every observational and intervention mechanism is a positive normalized `C³` density on its
closed cube, with each conditional normalized in its own coordinate. -/
def PositiveNormalizedSmoothMechanisms (θ : Mechanism n G) : Prop :=
  (∀ i v, v ∈ latentCube n → 0 < θ.p i v) ∧ -- @realizes \(p_i\)(strictly positive)
  (∀ i z, z ∈ Set.Icc (0 : ℝ) 1 → 0 < θ.q i z) ∧ -- @realizes \(q_i\)(strictly positive)
  (∀ i, ContDiffOn ℝ 3 (θ.p i) (latentCube n)) ∧ -- @realizes \(p_i\)(C3 on closed cube)
  (∀ i, ContDiffOn ℝ 3 (θ.q i) (Set.Icc (0 : ℝ) 1)) ∧ -- @realizes \(q_i\)(C3 on [0,1])
  (∀ i v, v ∈ latentCube n →
    ∫ z in Set.Icc (0 : ℝ) 1, θ.p i (Function.update v i z) = 1) ∧
    -- @realizes \(p_i\)(normalized in own coordinate)
  (∀ i, ∫ z in Set.Icc (0 : ℝ) 1, θ.q i z = 1)
    -- @realizes \(q_i\)(normalized on [0,1])

-- @node: ass:fixed-own-derivative-sign
/-- Each latent log ratio has the prescribed strict own-coordinate derivative sign. -/
def FixedOwnDerivativeSign (θ : Mechanism n G) : Prop :=
  ∀ i v, v ∈ latentCube n → 0 < s.value i * ownLogRatioDerivative θ i v

-- @node: ass:causal-minimality
/-- Every direct causal edge remains conditionally dependent given the other parents. -/
def CausalMinimality (θ : Mechanism n G) : Prop :=
  ∀ ⦃j i⦄, G.edge j i →
    ¬ CondIndepCoordinates θ {i} {j} ((G.parents i).erase j)

-- @node: ass:faithfulness
/-- Every observational conditional independence is graphically entailed by d-separation. -/
def Faithfulness (θ : Mechanism n G) : Prop :=
  ∀ X Y Z, Disjoint X Y → Disjoint X Z → Disjoint Y Z →
    CondIndepCoordinates θ X Y Z → G.dSep X Y Z

-- @node: def:model-stratum
/-- The positive, normalized, smooth, causal-minimal, fixed-sign mechanism stratum. -/
structure ModelStratum (θ : Mechanism n G) : Prop where
  positiveSmooth : PositiveNormalizedSmoothMechanisms G θ
  causalMinimal : CausalMinimality G θ
  fixedSign : FixedOwnDerivativeSign G s θ

/-- The mechanism subtype carrying the relative product `C²` topology. -/
abbrev StratumPoint := {θ : Mechanism n G // ModelStratum G s θ}
  -- @realizes \(\Theta_{G,s}\)(subtype with relative product topology)

/-- Squared conditional-dependence witness used to expose openness of causal minimality. -/
def causalMinimalityWitness (θ : Mechanism n G) (j i : Fin n) : ℝ :=
  ∫ v in latentCube n,
    (observationalDensity θ v *
        observationalDensity θ (Function.update (Function.update v i 0) j 0) -
      observationalDensity θ (Function.update v i 0) *
        observationalDensity θ (Function.update v j 0)) ^ 2

/-! ## Observed environment world -/

/-- The shared observed-space representation and the supplied family of observed laws and ratios. -/
structure ObservedWorld (θ : Mechanism n G) where
  mix : LatentState n → LatentState n -- @realizes f(shared mixing map)
  unmix : LatentState n → LatentState n
  targetPerm : Equiv.Perm (Fin n) -- @realizes \(\pi\)(unknown target bijection)
  law : Fin (n + 1) → Measure (LatentState n) -- @realizes \(P^e\)(observed environment laws)
  ratio : Fin n → LatentState n → ℝ -- @realizes \(R_i\)(Radon--Nikodym ratio carrier)

/-- The identity-mixing environment family generated directly by a mechanism and target
permutation. This is used for the explicit witness calculations. -/
def canonicalObservedWorld (θ : Mechanism n G) (π : Equiv.Perm (Fin n)) :
    ObservedWorld G θ where
  mix := id
  unmix := id
  targetPerm := π
  law := Fin.cases (observationalLaw θ) (fun e => interventionalLaw θ (π e))
  ratio := fun e v => θ.q (π e) (v (π e)) / θ.p (π e) v

/-- The observed support is the image of the latent cube. -/
def observedSupport (W : ObservedWorld G θ) : Set (LatentState n) :=
  W.mix '' latentCube n -- @realizes \(\mathcal X\)(image of latent cube)

/-- The observed random vector obtained from a latent state. -/
def observation (W : ObservedWorld G θ) (v : LatentState n) : LatentState n :=
  W.mix v -- @realizes X(X = f(V))

/-- The environment-label DAG obtained by pulling `G` back through the target permutation. -/
def permutedGraph (W : ObservedWorld G θ) (j i : Fin n) : Prop :=
  G.edge (W.targetPerm j) (W.targetPerm i)
  -- @realizes \(G^\pi\)(pullback edge relation)

/-- The observable log-ratio coordinate. -/
def logRatio (W : ObservedWorld G θ) (i : Fin n) (x : LatentState n) : ℝ :=
  Real.log (W.ratio i x) -- @realizes \(L_i\)(log R_i)

-- @env: S2
variable (θ : Mechanism n G) (W : ObservedWorld G θ)
  -- @realizes \(\mathcal X\)(observed support supplied by observedSupport)

-- @node: ass:shared-diffeomorphic-mixing
/-- The shared mixing map is a `C²` diffeomorphism between the latent cube and observed support. -/
def SharedDiffeomorphicMixing : Prop :=
  ContDiffOn ℝ 2 W.mix (latentCube n) ∧ -- @realizes f(C2 on latent cube)
  ContDiffOn ℝ 2 W.unmix (observedSupport G W) ∧ -- @realizes f(C2 inverse)
  (∀ v ∈ latentCube n, W.unmix (W.mix v) = v) ∧ -- @realizes f(left inverse)
  (∀ x ∈ observedSupport G W, W.mix (W.unmix x) = x) -- @realizes f(right inverse onto X)

-- @node: ass:one-perfect-intervention-per-node
/-- The observed laws are the shared pushforwards of one observational and one distinct
single-target intervention law, and the supplied ratios are their Radon--Nikodym derivatives. -/
def OnePerfectInterventionPerNode : Prop :=
  W.law 0 = Measure.map W.mix (observationalLaw θ) ∧ -- @realizes \(P^e\)(observational pushforward)
  (∀ e : Fin n,
    W.law e.succ = Measure.map W.mix (interventionalLaw θ (W.targetPerm e))) ∧
    -- @realizes \(P^e\)(permuted single-target intervention pushforwards)
  (∀ e : Fin n,
    (fun x => ENNReal.ofReal (W.ratio e x)) =ᵐ[W.law 0]
      (W.law e.succ).rnDeriv (W.law 0)) ∧ -- @realizes \(R_i\)(Radon--Nikodym derivative)
  (∀ e v, v ∈ latentCube n →
    W.ratio e (W.mix v) =
      θ.q (W.targetPerm e) (v (W.targetPerm e)) /
        θ.p (W.targetPerm e) v) -- @realizes \(R_i\)(unmixed q_i/p_i formula)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
