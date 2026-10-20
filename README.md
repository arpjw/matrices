# Marchenko–Pastur in Lean

A complete Lean 4 proof of the Marchenko–Pastur law for sample covariance
matrices with independent fair-sign entries.

**[Read the paper](paper/marchenko-pastur.pdf)** ·
[LaTeX source](paper/marchenko-pastur.tex) ·
[Main theorem](RandomMatrix/MarchenkoPastur.lean) ·
[Proof map](docs/PROOF_MAP.md) ·
[Verification record](docs/VALIDATION.md)

The proof runs from exact finite walk counting to weak convergence in
probability. It includes the general ordered-tree bijection, Narayana moments,
explicit bias and variance bounds, and normalization of the limiting density
plus its atom at zero. Every positive aspect ratio is covered, including the
critical value $\gamma=1$.

## The result

Let $X_m$ be a $p_m\times n_m$ matrix with independent entries uniform on
$\{-1,+1\}$, where both dimensions are positive. Define

$$
S_m=\frac{1}{n_m}X_mX_m^{\mathsf T},\qquad
\mu_m=\frac{1}{p_m}\sum_{i=1}^{p_m}\delta_{\lambda_i(S_m)}.
$$

Every eigenvalue is retained, including multiplicities and zeros. If
$n_m\to\infty$ and $p_m/n_m\to\gamma>0$, then for every bounded continuous
$f:\mathbb R\to\mathbb R$ and every $\varepsilon>0$,

$$
\Pr\!\left(\left|\int f\,d\mu_m-\int f\,d\mu_\gamma\right|>\varepsilon\right)
\longrightarrow 0.
$$

The limit is the explicit probability measure

$$
\mu_\gamma=\max\{1-\gamma^{-1},0\}\,\delta_0+\rho_\gamma(x)\,dx,
$$

$$
\rho_\gamma(x)=\frac{\sqrt{(b_\gamma-x)(x-a_\gamma)}}{2\pi\gamma x}
\quad(a_\gamma<x<b_\gamma),
$$

with $a_\gamma=(1-\sqrt\gamma)^2$, $b_\gamma=(1+\sqrt\gamma)^2$, and density zero
outside this interval. Its normalization, compact support, and moments at every
natural order are proved in Lean.

The exact declaration is `RandomMatrix.marchenkoPastur_theorem`.
Each size has its own finite uniform probability space; no coupling across
sizes is assumed.

## Follow the proof

| Step | Mathematical content | Guide |
| --- | --- | --- |
| 1 | Trace powers as alternating walks; exact finite pattern counts | [Walks](docs/WALKS.md), [patterns](docs/PATTERNS.md) |
| 2 | Leading patterns as ordered rooted trees; Narayana coefficients | [Trees](docs/ORDERED_TREES.md), [enumeration](docs/NARAYANA.md) |
| 3 | Uniform finite-size bias and variance; moment concentration | [Expected moments](docs/EXPECTED_MOMENTS.md), [concentration](docs/CONCENTRATION.md) |
| 4 | Eigenvalue measures, trace moments, and the rectangular zero atom | [Spectral measures](docs/SPECTRAL_MEASURES.md) |
| 5 | Normalization and every moment of the explicit density plus atom | [Density analysis](docs/MP_DENSITY.md) |
| 6 | Global polynomial bounds, moment determinacy, and weak convergence | [Weak convergence](docs/WEAK_CONVERGENCE.md) |

The [paper](paper/marchenko-pastur.pdf) presents the mathematical argument in
this order. The [module map](docs/PROOF_MAP.md) links all 62 mathematical modules.
[Development checkpoints](docs/HISTORY.md) preserve the intermediate stages.

## Build and verify

Install [Lean through elan](https://github.com/leanprover/elan), Git, and Python 3.
The repository pins **Lean 4.28.0** and mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`; the lockfile pins transitive dependencies.
From the repository root:

```sh
lake exe cache get
bash scripts/check.sh
```

The check script builds the project, scans for unfinished proofs and forbidden
shortcuts, audits theorem dependencies, and checks eleven deliberately false
claims for rejection at their intended mathematical goals.

The recorded verification passed all **372 declaration audits**, covering every
exported named theorem. Reported dependencies are confined to Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. No project-specific axioms or
proof placeholders are used. See the [verification record](docs/VALIDATION.md)
for logs, counts, and the trust boundary.

To rebuild the included paper, install
[Tectonic](https://tectonic-typesetting.github.io/) and run:

```sh
bash scripts/build-paper.sh
```

The output is [`paper/marchenko-pastur.pdf`](paper/marchenko-pastur.pdf).
[Reproduction instructions](docs/REPRODUCING.md) cover the toolchain, paper,
source manifest, and optional experiments.

## Experiments

The repository includes exact finite enumerations, spectral checks, numerical
density integration, and reproducible simulations. They provide independent
checks and illustrations; the general theorem is proved in Lean.

![Simulated spectra and finite-size second moments](experiments/results/spectral-experiment.png)

The figure retains structural zeros for rectangular matrices. Error bars are
sample standard deviations, not confidence intervals. See
[experiments and evidence](docs/EXPERIMENTS.md) for the recorded checks and their
limitations.

## Scope

This is a formalization of a classical theorem for independent fair-sign
entries, with a positive finite limiting aspect ratio. General entry
distributions, almost-sure convergence, spectral-edge limits, and convergence
of individual atom masses are outside the proved scope. No claim of a new limit
law or priority over other formalizations is made.

The paper and development were prepared with assistance from OpenAI Codex.
Formal correctness claims refer to the checked Lean statements and pinned
dependencies. The Python experiments and paper prose are not formally verified.
