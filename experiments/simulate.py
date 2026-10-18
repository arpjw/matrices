"""Reproducible illustrations of the planned theorem, not formal proof evidence."""
from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def mp_density(x: np.ndarray, gamma: float) -> np.ndarray:
    a, b = (1 - math.sqrt(gamma)) ** 2, (1 + math.sqrt(gamma)) ** 2
    out = np.zeros_like(x)
    mask = (x > max(a, 0.0)) & (x < b)
    out[mask] = np.sqrt((b - x[mask]) * (x[mask] - a)) / (2 * np.pi * gamma * x[mask])
    return out


def spectrum(p: int, n: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    x = rng.choice(np.array([-1.0, 1.0]), size=(p, n))
    # Use the smaller Gram matrix, retaining the p-n structural zeros explicitly.
    gram = x @ x.T / n if p <= n else x.T @ x / n
    vals = np.linalg.eigvalsh(gram)
    assert np.min(vals) > -1e-9
    if p > n:
        vals = np.r_[np.zeros(p - n), vals]
    assert len(vals) == p
    assert abs(float(vals.mean()) - 1) < 1e-10
    return vals


def main() -> None:
    out = Path(__file__).parent / "results"
    out.mkdir(exist_ok=True)
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "axes.spines.top": False, "axes.spines.right": False})
    fig, axes = plt.subplots(2, 3, figsize=(13.8, 8.0))
    fig.patch.set_facecolor("#faf9f6")
    records = []
    for col, gamma in enumerate((0.5, 1.0, 2.0)):
        n, p = 400, int(400 * gamma)
        spectra = [spectrum(p, n, seed) for seed in (1701, 1702, 1703)]
        vals = np.concatenate(spectra)
        b = (1 + math.sqrt(gamma)) ** 2
        positive = vals[vals > 1e-9]
        ax = axes[0, col]
        bins = np.linspace(0, b * 1.06, 42)
        # Density relative to all eigenvalues; do not renormalize the positive part.
        counts, edges = np.histogram(positive, bins=bins)
        ax.bar(edges[:-1], counts / (len(vals) * np.diff(edges)), width=np.diff(edges),
               align="edge", color="#548c91", alpha=.7, label="3 simulated matrices")
        grid = np.linspace(0.005, b * 1.06, 1200)
        ax.plot(grid, mp_density(grid, gamma), color="#b85435", lw=2, label="MP continuous density")
        ax.set_title(f"Aspect ratio γ = {gamma:g}  |  {p} × {n}", loc="left", weight="bold")
        ax.set_xlabel("Eigenvalue")
        ax.set_ylabel("Density (continuous part)")
        if gamma == 1:
            ax.set_ylim(0, 2.1)
        atom = max(1 - 1 / gamma, 0)
        ax.text(.98, .95, f"Atom at zero: {atom:.0%}", transform=ax.transAxes,
                ha="right", va="top", fontsize=9)
        if col == 0:
            ax.legend(frameon=False, fontsize=8, loc="upper right", bbox_to_anchor=(1, .85))
        ax = axes[1, col]
        rows = []
        for n in (40, 80, 160, 320):
            p = int(gamma * n)
            observations = [float(np.mean(spectrum(p, n, seed) ** 2))
                            for seed in range(2300, 2308)]
            rows.append({"p": p, "n": n, "seeds": list(range(2300, 2308)),
                         "second_moments": observations,
                         "exact_expectation": 1 + (p - 1) / n,
                         "limit": 1 + gamma})
        ns = np.array([r["n"] for r in rows])
        means = np.array([np.mean(r["second_moments"]) for r in rows])
        std = np.array([np.std(r["second_moments"], ddof=1) for r in rows])
        ax.errorbar(ns, means, yerr=std, fmt="o", capsize=4, color="#548c91",
                    label="Simulation mean ± sample SD")
        ax.plot(ns, [r["exact_expectation"] for r in rows], color="#b85435", lw=2,
                label="Exact finite expectation")
        ax.axhline(1 + gamma, color="#3a404c", ls="--", lw=1, label="Limiting second moment")
        ax.set_xlabel("Number of columns n")
        ax.set_ylabel("Normalized second trace moment")
        ax.set_title("Finite-size correction: −1/n", loc="left", fontsize=11)
        if col == 0:
            ax.legend(frameon=False, fontsize=8, loc="lower right")
        records.append({"gamma": gamma, "spectrum_seeds": [1701, 1702, 1703],
                        "spectrum_n": 400, "atom": atom, "moment_experiment": rows})
    fig.suptitle("From random signs to a spectral law", x=.065, ha="left", fontsize=23, weight="bold")
    fig.text(.065, .925, "S = XXᵀ/n  •  independent ±1 entries  •  simulations illustrate a theorem still under development",
             fontsize=11, color="#545c65")
    fig.text(.065, .025, "All zero eigenvalues are retained. Error bars show variation across 8 fixed seeds, not a proof or a confidence guarantee.",
             fontsize=9, color="#545c65")
    fig.subplots_adjust(left=.065, right=.975, bottom=.11, top=.86, hspace=.43, wspace=.31)
    fig.savefig(out / "spectral-experiment.png", dpi=180, facecolor=fig.get_facecolor())
    fig.savefig(out / "spectral-experiment.svg", facecolor=fig.get_facecolor())
    (out / "simulation.json").write_text(json.dumps({"status": "illustrative simulation",
        "numpy_version": np.__version__, "matplotlib_version": matplotlib.__version__, "results": records}, indent=2) + "\n")
    print("PASS: spectrum positivity/trace checks; all 105 seeded matrices recorded")


if __name__ == "__main__":
    main()
