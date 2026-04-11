# Meta-Axiom: Mathematical-Philosophical Framework

This repository provides a formal Lean 4 formalization of the "Four Meta-Axioms" proposed in the paper  
**"Meta-Axioms as the Conceptual Foundation of the Universe"** by Takeo Yamamoto.

## Overview

- **Extremum Principle (A1)**: `F[x] = Extremum L(x)`  
- **Topological Space (A2)**: `x ∈ X ⊂ ℝⁿ`  
- **Logical Consistency (A3)**: `C[F] = 0`  
- **Hierarchical Structure (A4)**: `F_macro = Σ wᵢ · F_micro(i)`

These axioms are formalized in Lean 4 and verified to be internally consistent and mathematically well-formed.

## Status

All theorems and definitions in this repository are **fully proven** in Lean 4.  
The following files contain no `sorry` placeholders:

- `Metaaxiom.lean` – Core axioms and basic theorems
- `Axioms.lean` – Auxiliary lemmas and properties
- `Dna.lean` – Application to DNA and genetic systems
- `Medical.lean` – Application to medical and biological systems
- `Collatz.lean` – Application to the Collatz conjecture
- `Ftheory.lean` – Application to F-theory and cosmology

Continuous integration (GitHub Actions) ensures that all proofs remain valid.

## Open Problems (Resolved)

The following theorems, previously listed as open problems, are now **fully proven**:

- **`shannon_entropy_nonneg`** – Non-negativity of Shannon entropy (proven using convexity of the logarithm).
- **`consistency_preserved`** – Preservation of logical consistency under Meta-Axioms (derived from A3).
- **`compact_extremum_exists`** – Existence of extrema on compact spaces (using `IsCompact.exists_isMin`/`exists_isMax`).
- **`unity_principle`** – Unity principle for hierarchical structures (derived from A4).

These theorems are now integrated into the respective application files (`Entropy.lean`, `Topology.lean`, etc.) and are part of the formal verification.

## License

This work is licensed under the Creative Commons Attribution 4.0 International (CC BY 4.0) license.  
See the [LICENSE](LICENSE) file for details.

## Citation

If you use this work in academic research, please cite:

```bibtex
@software{yamamoto_meta_axiom_2025,
  author       = {Takeo Yamamoto},
  title        = {Meta-Axiom: Mathematical-Philosophical Framework},
  year         = {2025},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.18603974},
  url          = {https://doi.org/10.5281/zenodo.18603974}
}
