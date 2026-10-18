# Random matrix formalization

Read README.md and docs/BLUEPRINT.md before extending the mathematics.
Keep the Lean and mathlib versions pinned. Never add sorry, admit, custom axioms,
unsafe proof shortcuts, or a theorem whose central conclusion is an assumption.
Proofs may use Lean's standard logical axioms. Audit exported results with
#print axioms and explain any additional trust dependencies explicitly.
Keep completed theorems, planned targets, exact computations, and simulations
separate in the status documentation. Do not claim the Marchenko-Pastur theorem
until the random-matrix-to-spectral-measure convergence chain is proved.
Preserve the p-by-n, S = X X^T / n, gamma = p/n convention, including the zero
atom for gamma > 1. Explicitly require nonzero dimensions when dividing.
Run lake build and scripts/check.sh after changing Lean source.
No commit, push, deployment, paid computation, or destructive cleanup without
explicit user authorization.
