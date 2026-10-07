module
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour.ContourEvaluation

/-!
# Certified evaluation of circle contour integrals in rational arithmetic

A contour integral of a quotient of two complex functions over a circle centred at the origin,
normalized by 1/(2πi), is evaluated by a finite trapezoidal rule carried out entirely with
rational complex rectangles. The main theorem states that the computed rectangle contains the
exact normalized contour integral and that its real part has width at most the requested
tolerance. It is conditional on the denominator not vanishing on the circle, on a certificate
that bounds it away from zero, and on a Lipschitz bound for the integrand in the circle parameter.

## Main results

* `certified_contour_evaluation` — enclosure of the normalized contour integral together with
  the width guarantee.
* `certified_contour_evaluation_inverseMax` — the width is at most 1/max(n, 1) when the schedule
  requests that tolerance.
* `normalizedContourIntegral_eq` — the contour integral as an integral over the unit parameter
  interval.

The supporting layers come with it: rational interval squares and square roots, complex
rectangle arithmetic with guarded division, nested rational names for complex numbers, rational
enclosures of π, sine, cosine and the exponential, precision schedules and circle nodes. This
file only gathers `Contour.ContourEvaluation` and what it depends on.
-/

public section
