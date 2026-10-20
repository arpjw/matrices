# The explicit Marchenko-Pastur measure

## Completed statement

For every real gamma>0, define

    a = (1-sqrt(gamma))^2,       b = (1+sqrt(gamma))^2,
    rho_gamma(x) = sqrt((b-x)(x-a)) / (2*pi*gamma*x) for a<x<b,
                   0 otherwise,
    mu_gamma = max(1-1/gamma,0) delta_0 + rho_gamma(x) dx.

Lean now proves that this displayed measure is a probability measure, has compact
nonnegative support, and has every natural moment:

    integral x^k d mu_gamma = P_k(gamma),
    P_0(gamma) = 1,
    P_k(gamma) = sum_(j=0)^(k-1) choose(k,j+1) choose(k,j) gamma^j / k,  k>0.

All moment functions are separately proved integrable. Normalization is derived
from the density integral; it is not an assumption or a renormalization operation.
The construction is valid at gamma=1, including the integrable singularity of
the density at its zero endpoint.

## Definitions and proof modules

| Module | Role |
| --- | --- |
| MPParameters | Endpoints, explicit density and atom, positivity, and the angular map |
| MPPolynomialRecurrence | Transfer of the existing rational tree recurrence to real MP polynomials |
| MPMomentRecurrence | Angular moment integrals, integration by parts, and all-order polynomial identification |
| MPTrigNormalization | Reciprocal trigonometric integrals derived from an arctangent antiderivative |
| MPAngularNormalization | Continuous mass, with separate treatment of gamma=1 |
| MPDensityIntegrals | Lebesgue change of variables, integrability, continuous mass, and every positive density moment |
| MPMeasure | The actual density-plus-atom probability measure, exact atom, all moments, and compact support |
| MPIdentification | Empirical moment concentration with limits expressed as moments of this explicit measure |

`marchenkoPastur gamma` is the sum of a scaled Dirac measure and
`volume.withDensity (ENNReal.ofReal (mpDensity gamma))`. The bundled
`mpProbabilityMeasure gamma hgamma` carries the proved normalization and
mathlib's topology of weak convergence. No presumed probability law is used
to define or normalize the density.

## Change of variables

Use

    x(theta) = 1+gamma - 2*sqrt(gamma)*cos(theta),     0 <= theta <= pi.

The map is continuous and strictly increasing, sends the endpoints to a and b,
and maps (0,pi) exactly onto (a,b). Its derivative is
2*sqrt(gamma)*sin(theta). On this interval,

    sqrt((b-x(theta))(x(theta)-a)) = 2*sqrt(gamma)*sin(theta),
    rho_gamma(x(theta)) x'(theta)
      = (2/pi) sin(theta)^2 / x(theta).

The proof uses mathlib's one-dimensional Jacobian theorem. It transfers both
integrals and integrability, rather than assuming the transformed integral
exists. The open endpoints differ from the closed integration interval only
on Lebesgue-null sets.

## Normalization and the atom

For positive u,v, an arctangent antiderivative first gives

    integral_0^(pi/4) 1/(u^2 cos(t)^2 + v^2 sin(t)^2) dt
      = arctan(v/u)/(u*v).

Reflection of the other quarter interval and the reciprocal-arctangent
identity yield pi/(2*u*v) over [0,pi/2]. A half-angle substitution then gives

    integral_0^pi 1/(c-r*cos(t)) dt = pi/sqrt(c^2-r^2),
    c-r>0, c+r>0.

With c=1+gamma and r=2*sqrt(gamma), this applies when gamma differs from one.
Polynomial division of sin(t)^2/(c-r*cos(t)) gives continuous mass

    (1+gamma-|gamma-1|)/(2*gamma) = min(1,1/gamma).

For gamma=1, the angular weight instead simplifies almost everywhere to
(1+cos(theta))/pi, whose integral is one. This avoids dividing by |gamma-1|
at the critical parameter.

Adding max(1-1/gamma,0) gives mass one in every case. The continuous part is
atomless, so the full measure's mass at zero is exactly the displayed atom.
In particular, the critical law gamma=1 has no zero atom. The density's
singularity there does not add point mass.

## All moments

For every natural k,

    integral x^(k+1) rho_gamma(x) dx
      = Q_k(gamma)
      = (2/pi) integral_0^pi x(theta)^k sin(theta)^2 dtheta.

The base integrals give Q_0=1 and Q_1=1+gamma. Integrating the derivative of
2*sqrt(gamma)*x(theta)^(k+1)*sin(theta)^3, which vanishes at both endpoints,
proves

    (k+4) Q_(k+2)
      = (2k+5)(1+gamma) Q_(k+1) - (k+1)(gamma-1)^2 Q_k.

The previously proved tree-polynomial recurrence gives precisely the same
recurrence for P_(k+1). Strong induction therefore proves Q_k=P_(k+1) for
every k, with no finite-order cutoff. Positive powers vanish at the zero
atom. Order zero is handled by the separate normalization proof.

Main exported results are `mpDensity_integral`, `mpDensity_moment_succ`,
`marchenkoPastur_isProbabilityMeasure`, `marchenkoPastur_moment_integrable`,
`marchenkoPastur_moment`, `marchenkoPastur_zero_atom_real`, and
`marchenkoPastur_support_compact`.

## Connection to the random matrices

`empirical_moment_converges_to_mp` now states the fixed-moment convergence
in probability using the two actual bundled probability measures:

    Pr(|integral x^k d mu_(X_m) - integral x^k d mu_gamma| > epsilon) -> 0.

The hypotheses remain positive dimensions, n_m tending to infinity,
p_m/n_m tending to gamma>0, and epsilon>0. Mean-square convergence is also
identified with the moments of this explicit law. This is still moment
convergence; the theorem for all bounded continuous test functions remains.

## Validation and scope

All 54 new exported theorems are included in the axiom audit. Three new Lean
negative controls reject an incorrectly normalized continuous part at gamma=2,
an incorrect second moment, and a nonzero atom at gamma=1.

`experiments/mp_density.py` independently evaluates the explicit density using
x=a+(b-a)u^2 and adaptive Simpson quadrature with a global error budget. It
checks 165 continuous moments, orders zero through ten, at 15 aspect ratios
from 1/100 to 100, including 999/1000, 1, and 1001/1000. It checks the full
measure's moments after adding the atom. Twelve refinement comparisons and
two incorrect-normalization controls are retained. Exact rational arithmetic
also checks the moment recurrence 450 times, through moment order 32.

The quadrature is a numerical check, not certified interval arithmetic or a
proof. The general normalization and all-order moment statements are the
Lean results. See [VALIDATION.md](VALIDATION.md) for the actual build and audit.

## Remaining stage

Prove weak convergence in probability of the empirical measures against every
bounded continuous real test function. The available inputs are the normalized
empirical measures, their nonnegative support and exact first moment, all-order
moment concentration, and the explicit compactly supported target law.

The remaining argument needs tightness and a justified passage from moments
to measures. One direct route is polynomial approximation on a compact interval,
control of the polynomial tails by higher moments, and a finite probability
bound for the required collection of moments. Moment determinacy of the compact
target must also be established or incorporated into that argument. No common
probability space across matrix sizes should be introduced as an assumption.
See [BLUEPRINT.md](BLUEPRINT.md).
