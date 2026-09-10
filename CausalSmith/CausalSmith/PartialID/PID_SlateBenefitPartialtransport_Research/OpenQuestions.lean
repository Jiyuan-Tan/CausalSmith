/-!
# Open calibration question

This file records the unresolved inferential question as descriptive metadata.
It intentionally makes no mathematical assertion and supplies no witness for a
calibration procedure.
-/

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

/-- Can the near-active-face directional-multiplier handle be calibrated so that
`liminf n, inf P in 𝒫ₙ, P{Θ_I(P_obs) ⊆ C_(1-α,n)} ≥ 1-α` uniformly over
direction-separated triangular arrays?  The regime includes the first `n`
observations sampled independently from `P_obs`, instrument overlap `ε_Z`, aggregate survivor mass at least `m_★`, and
selection-gap separation `|Δq(x)| ≥ κ_σ` on positive survivor cells.  It must
allow arbitrary simultaneous threshold-cut ties and cells whose survivor mass
approaches zero and is omitted at the unnormalized threshold `η_n`.

The estimated-directional-derivative approach of Fang and Santos (2019),
the localized-contact-set approach of Chernozhukov, Lee, and Rosen (2013), the
covariate-specific Lee-direction analysis of Semenova (2025), and the pointwise
stabilized tier-benefit coverage of de Aguas et al. (2025), equations (17)--(18),
do not settle this question.  The multiplier envelope in the present
construction is diagnostic only: no first-order exact calibration of an
unguarded face-aware region is claimed, and the delivered uniform containment
result uses only the alpha-indexed deterministic guard
`g_(n,α) = min{1, 4 A_(n,α) / m_★}`, built from the finite event class
`E`, maximal deviation `δ_n`, union threshold `b_(n,α)`, and envelope
`A_(n,α)`. -/
-- @node: oeq:uniform-face-multiplier
def openQuestion_uniformFaceMultiplierCalibration : _root_.String :=
  "Can the near-active-face directional-multiplier handle be calibrated to achieve liminf_n inf_{P in P_n} P{Theta_I(P_obs) subset C_(1-alpha,n)} >= 1-alpha uniformly over direction-separated triangular arrays whose first n observations are independent draws from P_obs, under instrument overlap epsilon_Z, aggregate survivor mass M >= m_star, and |Delta q(x)| >= kappa_sigma on positive survivor cells, while allowing arbitrary simultaneous threshold-cut ties and cells whose survivor mass approaches zero and is omitted at the unnormalized threshold eta_n? Fang--Santos estimated directional derivatives, Chernozhukov--Lee--Rosen localized contact sets, Semenova covariate-specific Lee directions, and de Aguas et al. equations (17)--(18) pointwise stabilized tier-benefit coverage do not settle this. The multiplier envelope is diagnostic only; no first-order exact calibration of an unguarded face-aware region is asserted, and the delivered every-sample uniform containment result uses only the alpha-indexed deterministic guard g_(n,alpha)=min{1,4*A_(n,alpha)/m_star}, built from the finite event class E, maximal deviation delta_n, threshold b_(n,alpha), and envelope A_(n,alpha)."

end CausalSmith.PartialID.SlateBenefitPartialTransport
