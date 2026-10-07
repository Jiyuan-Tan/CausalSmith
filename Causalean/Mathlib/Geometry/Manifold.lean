module
public import Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry

/-!
# Extrinsic geometry of submanifolds of Euclidean space

For a C² embedding of a finite-dimensional manifold, possibly with boundary or corners, into a
Euclidean space, this part of the library defines the tangent space at a point as the range of
the differential and the normal space as its orthogonal complement, constructs the normal-valued
second fundamental form and the shape operator, shows both are independent of the chart, and
sets up Lebesgue measure on the normal fibers together with the iterated integral over the
manifold and its normal disks. These are the ingredients of tube-volume arguments around an
embedded manifold.

All of this is in `Manifold.EmbeddedNormalGeometry`, which this file gathers.
-/
public section
