# Experiments and evidence

The results below are the recorded checks accompanying the formal development.
Reproduction commands are in [REPRODUCING.md](REPRODUCING.md). These computations
supplement the proofs; they do not establish the all-order theorem.

The exact checker enumerates 4,774 sign matrices over eight small dimension
pairs, independently comparing direct matrix multiplication with partition
counts for the first four moments. Another 40 checks compare the rooted walk
encoding with partition counts, including the empty-walk case. It also checks
leading Narayana coefficients through order seven using exact integers.
The position-partition encoding is independently checked at orders 0 through 7,
and exhaustive assignments check 120 labeling fibers, including empty domains
and insufficient label counts. The general partition grouping and coefficient
support bound and general Narayana formula are proved in Lean. The checker also validates 40 finite-bias bounds against these direct moments, another 56
against partition counts through order seven, and six examples distinguishing
current-ratio bias from convergence to a limiting ratio. The general bound and
all fixed-order expected-moment limits are proved in Lean.

The graph checker independently verifies 189,455 partition graphs at orders
0 through 6. An independent implementation checks both bijection inverses on all 626 trees
at orders 0 through 7, as well as the first-child representation, canonical
contour, and color-count recurrence. The graph classification, general
bijection, and Narayana enumeration are proved in Lean. The Python implementation itself is not
formally verified.

The variance checker independently enumerates 4,774 sign matrices, checks 40
exact variances and 160 tail bounds, and compares 32 paired-walk counts against
joint partition enumeration through order three. It checks 797,438 shared-row
partition candidates and retains cases with positive variance. The general
variance and convergence-in-probability theorems are proved in Lean.

The exact spectral checker verifies 2,826 small sign matrices and four additional
matrices. It compares 19,810 spectral moments to direct matrix powers, certifies
characteristic polynomials by 12,215 exact determinant evaluations, and checks
2,830 ranks and zero atoms. Controls reject dropping zeros, renormalizing only
the positive spectrum, and discarding multiplicities. These finite computations
supplement the general Lean spectral-measure theorems.

The density checker numerically integrates 165 moments at 15 aspect ratios,
including values on both sides of gamma=1 and the critical value itself. It
also performs 450 exact rational recurrence checks, twelve quadrature refinement
comparisons, and controls for omitted atoms and incorrect renormalization.
The quadrature is numerical evidence; normalization and all moments are proved
in Lean for every positive real aspect ratio.

The spectral figure uses 105 reproducible simulated matrices. It preserves
structural zero eigenvalues for p > n and shows the finite -1/n bias in the
second moment. Its histograms and error bars are illustrations, not formal
proofs or evidence of a new mathematical result.

![Spectral experiment](../experiments/results/spectral-experiment.png)
