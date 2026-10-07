module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.AffineEnvelope
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.Defs
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.Envelope
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.PopulationBounds
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.PopulationMassart
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.PopulationSingleton
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.RademacherBounds
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.RademacherBridge

/-! # Localized Rademacher bounds for finite-VC classes

Localized Rademacher envelopes for function classes of finite VC dimension: each function in
the class is determined on any sample by a Boolean labelling whose patterns have VC dimension
at most d (`BinaryFactoredVCClass`). Two localizations are covered, and both give the
d log n / n rate for the squared critical radius.

## Population-L² localization

The class is a countable family of measurable functions bounded by b, and the star hull is
localized by the population norm ‖f‖_{L²(P)} ≤ r, as in Bartlett–Bousquet–Mendelson (2005) and
Wainwright (2019, ch. 14). Nothing is assumed about empirical norms. With
q = (d log(n+1) + 1)/n, the localized Rademacher complexity is at most the affine envelope
ψ(r) = 2√q·r + 16·b·q at every radius r ≥ 0, by a self-bounding argument. This envelope is
star-shaped and its critical radius r* satisfies r*² ≤ (32 + 128·b)·q. Above the radius floor
2048·b·√q the uniform comparison of empirical and population norms gives the smaller
intercept b/n.

Remark (not proved in Lean): an additive term is necessary. For indicators of intervals under
an atomless law, every radius r > 0 admits intervals of L²(P) norm below r containing exactly
one sample point, so the localized complexity is at least of order 1/n and no envelope of the
form s·r holds.

* `vcPopulationLocalizedPsi` — the affine envelope ψ.
* `vcPopulationLocalizedRademacherUpperBound` — ψ bounds the population-localized Rademacher
  complexity.
* `vcPopulationLocalizedEnvelope` — star-shapedness, the Rademacher bound and the squared
  critical-radius rate.
* `vcPopulation_localizedRademacher_le` — the self-bounding inequality behind the envelope.
* `vcPopulation_localizedRademacher_above_floor` — R_n(r) ≤ 2√q·r + b/n for r ≥ 2048·b·√q.
* `vcPopulation_criticalRadius_sq_le_rate` — the critical radius δ_n of r ↦ 512·b·R_n(r)
  satisfies δ_n² ≤ 4194304·b²·q; every δ ≥ δ_n is admissible in the uniform comparison of
  empirical and population L² norms, `populationNormComparisonEvent_compl_le`.

## Samplewise localization

A stronger, deterministic variant: every member of the localized star hull at radius r is
assumed to have empirical L² norm at most r on every sample
(`SamplewiseLocalizedVCDudleyHypotheses`). This is essentially sup-norm localization and is an
assumption, not a derived fact. Under it the envelope is linear, ψ(r) = s·r with slope
s = 6√((K d log(n+1) + 1)/n) for a constant K ≥ 1; it is star-shaped and its critical radius
r* satisfies r* ≤ s, hence r*² ≤ 36 (K d log(n+1) + 1)/n.

* `vcLocalizedSlope`, `vcLocalizedPsi` — the slope s and the envelope ψ.
* `vcLocalizedRegime`, `vcLocalizedRegime_of_card` — the packaged envelope for a bounded class,
  from a VC bound or from a polynomial bound (m+1)^d on the number of label patterns.
* `vcLocalizedRademacherUpperBound`, `vcLocalizedRademacherUpperBound_of_card` — ψ bounds the
  localized population Rademacher complexity.
* `vcLocalizedEnvelope` — star-shapedness, the Rademacher bound and both critical-radius bounds.
* `criticalRadius_vcLocalizedPsi_sq_le_rate` — the squared critical-radius rate.
-/
