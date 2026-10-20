# Initial source audit, 2026-10-18

This is a targeted reconnaissance, not an exhaustive novelty search. The
sources below were inspected; third-party projects were not rebuilt locally.
No first-formalization or new-theorem claim is made.

## Wigner semicircle project

Repository: https://github.com/FredRaj3/SemicircleLaw
Inspected revision: 7c9eb0dac7de5ff00add687a82a250e39bc89eea.
Toolchain: Lean 4.28.0, mathlib 4.28.0, plus LeanHammer and checkdecls.

The project contains useful empirical spectral measure and random-probability
measure infrastructure. A lexical scan of its 17 Lean files under SemicircleLaw/
found unfinished-proof tokens in LoopWalk, WignerMatrix, WignerSemicircleLaw,
and WignerSemicircleLawMatrixMoments. Token counts alone are not a dependency
or semantic audit. It should not be described as a completed proof based on its
README. No source from that project has been copied into our proof modules.

Pinned entry point:
https://github.com/FredRaj3/SemicircleLaw/blob/7c9eb0dac7de5ff00add687a82a250e39bc89eea/SemicircleLaw/WignerSemicircleLaw/WignerSemicircleLaw.lean

## Existing Marchenko-Pastur file

Repository: https://github.com/statopia/statlean4
Inspected revision: dd2c4bbc72b7c643e62985d77c84755b31aec9f5.
File: Statlean/RandomMatrix/MarchenkoPastur.lean.

The inspected file explicitly declares three custom axioms:

- mpMeasure_isProbabilityMeasure_axiom;
- mpStieltjes_fixed_point_axiom;
- stieltjes_continuity_theorem_axiom.

Its marchenko_pastur_convergence theorem takes transform convergence as a
hypothesis and invokes the continuity axiom. It does not derive that hypothesis
from an independent-entry random-matrix ensemble. This finding concerns that
file and revision, not every theorem in the repository. We do not depend on it.
The transform convention and fixed-point equation would also require an
independent mathematical audit before reuse.

Pinned source:
https://github.com/statopia/statlean4/blob/dd2c4bbc72b7c643e62985d77c84755b31aec9f5/Statlean/RandomMatrix/MarchenkoPastur.lean

## Reused foundations

Mathlib pinned revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365 (v4.28.0).
We build on finite sums/products, real arithmetic, matrix multiplication, trace,
and related linear algebra. The parity and rectangle arguments in this project
are implemented independently. Reuse of spectral-measure infrastructure is a
later design decision, with license and proof-dependency checks required.


## Counting foundations inspected on 2026-10-20

At the same pinned mathlib revision, `Combinatorics/Enumerative/Catalan.lean`
provides `Tree.treesOfNumNodesEq`, its exact membership theorem, and its Catalan
cardinality. We reuse this exhaustive finite enumeration and the total count.
`RingTheory/PowerSeries/Derivative.lean` supplies formal derivatives and their
coefficient/product rules. `Data/Nat/Choose/Basic.lean` supplies Pascal's
identity and the multiplicative binomial identities.

The refined Narayana identity was not found in the pinned mathlib sources.
The project proves its color-counting series equations, differential
recurrence, arithmetic recurrence, and connection to the original pattern
coefficients. This is still a formalization of a classical counting formula,
not a claim of mathematical novelty or first formalization.
