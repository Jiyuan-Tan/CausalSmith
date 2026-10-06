module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.LabelFloorPair
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.Certificate
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.ZeroInflated

/-!
Finite core/filler affine priors with a reservoir and shared normalizer.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/--
[The affine-prior schedule records its intensities, degree, bandwidth, cone scale, and number of
rare cells](goal).
-/
structure AffineTuning where
  u : Real
  w : Real
  M : Real
  B : Real
  alpha : Real
  b0 : Real
  L : Nat
  Kstar : Nat
/--
[The affine schedule uses all marginal records and a degree calibrated to rare-label
information](goal).
-/
noncomputable def affineTuning (n m d : Nat) (eps : Real) : AffineTuning :=
  let u : Real := 128 * n
  let w : Real := 128 * ((n : Real) + m)
  let M := u + w
  let L := Nat.ceil (8 * logScale n eps)
  let B : Real := L / (1000 * M)
  let alpha := B / (100 * (L : Real) ^ 2)
  let b0 := alpha / eps
  ⟨u, w, M, B, alpha, b0, L, min (d - 1) (Nat.floor (1 / (100 * b0)))⟩
/--
[A finite signed reciprocal-gap certificate, with all its defining properties](goal).
-/
structure ConeDual (L : Nat) (B eps : Real) where
  nodes : Fin (L + 2) → Real
  weights : Fin (L + 2) → Real
  strictMono : StrictMono nodes
  mem : ∀ i, nodes i ∈ Set.Icc 0 B
  abs_sum : ∑ i, |weights i| = 1
  moments : ∀ h, h ≤ L → ∑ i, weights i * nodes i ^ h = 0
  gap : 1 / 8 ≤ ∑ i, weights i *
    ((B / (100 * (L : Real) ^ 2)) / ((B / (100 * (L : Real) ^ 2)) + (1 - eps) * nodes i))
/--
[The latent type retains a separate filler branch even when a core atom is at zero](goal).
-/
abbrev Latent (L : Nat) := Option (Fin (L + 2))
/--
[For the cone degree](hyp:L), [the measurable-space structure on latent states](goal) is the discrete measurable space.
-/
instance (L : Nat) : MeasurableSpace (Latent L) := ⊤
/--
[The core branch reads its certificate node and the filler branch uses zero](goal).
-/
noncomputable def latentNode {L : Nat} {B eps : Real} (sigma : ConeDual L B eps) : Latent L →
  Real :=
  fun z => match z with | none => 0 | some i => sigma.nodes i
/--
[The core sign is the polar sign of its signed weight; the filler carries no signed
contribution](goal).
-/
noncomputable def latentPolar {L : Nat} {B eps : Real} (sigma : ConeDual L B eps) : Latent L →
  Real :=
  fun z => match z with | none => 0 | some i => if 0 ≤ sigma.weights i then 1 else -1
/--
[Core latent probabilities tilt the absolute certificate weights by the reciprocal treated
mass](goal).
-/
noncomputable def latentCoreMass {L : Nat} {B eps : Real} (sigma : ConeDual L B eps)
    (i : Fin (L + 2)) : Real :=
  let alpha := B / (100 * (L : Real) ^ 2)
  alpha / (alpha + (1 - eps) * sigma.nodes i) * |sigma.weights i|
/--
[The finite latent PMF uses reciprocal-tilted core weights and places the remaining probability
on the filler](goal).
-/
noncomputable def latentPMF {L : Nat} {B eps : Real} (sigma : ConeDual L B eps) : PMF (Latent L) :=
  normalizedPMF (fun z => match z with
    | none => 1 - ∑ i, latentCoreMass sigma i
    | some i => latentCoreMass sigma i) (PMF.pure none)
/--
[The common expected raw cell mass averages b0 plus the latent node](goal).
-/
noncomputable def latentMeanMass {L : Nat} {B eps : Real} (sigma : ConeDual L B eps) : Real :=
  ∑ z : Latent L, (latentPMF sigma z).toReal * (B / (100 * (L : Real) ^ 2) / eps + latentNode
    sigma z)
/--
[Raw complete-record masses implement the affine cone, signed outcome marking, reservoir, and
null remaining cells](goal).
-/
noncomputable def rawTable (hyp : Bool) (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) : Obs d → Real :=
  let tun := affineTuning n m d eps
  let pstar := 1 - (tun.Kstar : Real) * latentMeanMass sigma
  fun z => if hj : z.1.val < tun.Kstar then
    let v := latentNode sigma (lat ⟨z.1.val, hj⟩)
    let arm := if z.2.1 then tun.alpha + (1 - eps) * v else (1 - eps) * tun.b0 + eps * v
    let mean := if z.2.1 then
      match lat ⟨z.1.val, hj⟩ with
      | none => 0
      | some i => (1 + (if hyp then 1 else -1) * latentPolar sigma (some i)) / 2
      else 0
    arm * bernoulliMass mean z.2.2
  else if z.1.val = tun.Kstar then (pstar / 2) * bernoulliMass 0 z.2.2 else 0
/--
[The raw complete-record table is divided by its total mass, with a total fallback outside legal
inputs](goal).
-/
noncomputable def normalizedLaw (hyp : Bool) (n m d : Nat) (eps : Real) (hd : 2 ≤ d)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (lat : Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L) : DiscreteLaw
      d :=
  ⟨normalizedPMF (rawTable hyp n m d eps sigma lat)
    (PMF.pure (⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1 : 0 < 2) hd⟩, false, false))⟩
/--
[The finite product of common latent draws pushes forward to normalized complete-record tables
under each hypothesis](goal).
-/
noncomputable def affineProductPrior (hyp : Bool) (n m d : Nat) (eps : Real) (hd : 2 ≤ d)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    Measure (DiscreteLaw d) :=
  (Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)).map
    (normalizedLaw hyp n m d eps hd sigma)

end CausalSmith.Stat.AnnotationRarearmFrontier
