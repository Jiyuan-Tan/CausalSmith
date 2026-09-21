module

public import Causalean.Stat.Bootstrap.AsymptoticLinearity.Main
public import Causalean.Stat.Bootstrap.AsymptoticLinearity.SampleMean

/-!
# Bootstrap intervals for asymptotically linear estimators

This directory packages the estimator-level bootstrap interface. It defines conditional
centered-estimator laws and percentile/basic intervals, supplies the generic conditional-limit
lemmas, proves their asymptotic validity under bootstrap asymptotic linearity, and includes the
real sample-mean constructor.
-/

