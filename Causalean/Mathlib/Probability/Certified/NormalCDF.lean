/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Certified.NormalCDF.Checker

/-!
# Certified rational enclosures of the standard normal distribution function

A Boolean checker that takes a rational point q, a rational interval and finite certificate data,
and whose success proves that the interval contains Φ(q), the standard normal distribution
function at q. In the central range the certificate uses the alternating power series of
∫₀ˣ exp(−t²/2) dt with a rational enclosure of 1/√(2π); for x > 8 it uses the Mills-ratio bounds
x·φ(x)/(x² + 1) ≤ 1 − Φ(x) ≤ φ(x)/x with a rational enclosure of the exponential. Differences
Φ(b) − Φ(a) are enclosed by subtracting two checked intervals.

## Main results

* `normalCDFCheck_sound` — a successful check implies the reported interval contains Φ(q).
* `NormalCDFCertificate.sound`, `fineNormalCDFCheck_sound` — the same for packaged certificates
  and for the variant that also checks the interval width.
* `normalCDFDifference_sound` — the difference of two certified enclosures contains Φ(b) − Φ(a).

This file only gathers `NormalCDF.Checker`, which brings the power-series, tail, exponential and
normalization layers with it.
-/

public section
