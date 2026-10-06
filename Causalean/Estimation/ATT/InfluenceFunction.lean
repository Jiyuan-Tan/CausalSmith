module
public import Causalean.Estimation.ATT.Score.MeanZero
public import Causalean.Estimation.ATT.Score.FiniteVar

/-!
Collects the average-treatment-effect-on-the-treated AIPW interface in one
import. The re-exported development defines `TreatedEstimationSystem`,
`OneSidedOverlap`, the observed laws `P_X` and `P_Z`, the ATT target `θ₀`, the
un-normalized moment `aipwMomentATT`, the influence function `ψ_ATT`, the
treated nuisance space `TreatedNuisanceVec`, and its overlap class `H_ε`.

It also exposes the main population facts used downstream: the mean-zero theorem
`aipw_mean_zero_ATT`, pull-out identities for ATT residuals, and finite-variance
and IPW-integrability results. Remainder bounds and L² score continuity have
their own import targets and are not part of this barrel.
-/

public section
