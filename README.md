# Meta-Axiom: A Mathematical-Philosophical Framework for Universal Optimization

[![Lean 4](https://img.shields.io/badge/Lean-4-orange.svg)](https://leanprover.github.io/)
LICENSE approach2.0
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18603974.svg)](https://doi.org/10.5281/zenodo.18603974)
[![Maintenance](https://img.shields.io/badge/Maintained%3F-yes-green.svg)](https://github.com/TakeoYamamoto/Meta-Axiom/graphs/commit-activity)

This repository provides a formal Lean 4 formalization of the **"Four Meta-Axioms"** (collectively referred to as **F-Theory**) proposed by **Takeo Yamamoto**.

## Overview

The framework establishes a rigorous foundation for the conceptual laws of the universe through four fundamental pillars:

- **Extremum Principle (A1)**: $F[x] = \text{Extremum } L(x)$
- **Topological Space (A2)**: $x \in X \subset \mathbb{R}^n$
- **Logical Consistency (A3)**: $C[F] = 0$
- **Hierarchical Structure (A4)**: $F_{macro} = \sum w_i \cdot F_{micro}(i)$

These axioms are formalized in Lean 4 and verified to be internally consistent and mathematically well-formed via the **Curry-Howard correspondence**.

## Status: Fully Proven

All theorems and definitions in this repository are **fully proven**. The following files contain no `sorry` placeholders, and the proof state is verified by continuous integration (GitHub Actions).

- `Metaaxiom.lean` – Core axioms and consistency proofs.
- `Axioms.lean` – Auxiliary lemmas and mathematical properties.
- `Ftheory.lean` – Application to F-theory and cosmology.
- `Collatz.lean` – Application to the structural analysis of the Collatz conjecture.
- `Dna.lean` – Application to genetic systems and information theory.
- `Medical.lean` – Application to biological systems and homeostatic optimization.

## Resolved Proofs

The following properties are integrated into the formal verification:

- **`shannon_entropy_nonneg`**: Non-negativity of Shannon entropy (proven via log-convexity).
- **`consistency_preserved`**: Invariance of logical consistency under Meta-Axioms (derived from **A3**).
- **`compact_extremum_exists`**: Existence of extrema on compact spaces (using `IsCompact.exists_isMin`/`exists_isMax`).
- **`unity_principle`**: Formal derivation of hierarchical convergence (derived from **A4**).

## License

This work is licensed under the **approach2.0** license.  
See the [LICENSE](LICENSE) file for details.

**Author:** Takeo Yamamoto 

## Citation

```bibtex
@software{yamamoto_meta_axiom_2025,
  author       = {Takeo Yamamoto},
  title        = {Meta-Axiom: A Mathematical-Philosophical Framework for Universal Optimization},
  year         = {2025},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.18603974},
  url          = {[https://doi.org/10.5281/zenodo.18603974](https://doi.org/10.5281/zenodo.18603974)}
}
