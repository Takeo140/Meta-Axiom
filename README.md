# Meta-Axiom: A Formalized Mathematical-Philosophical Framework

[![Lean 4 CI](https://img.shields.io/badge/Formal_Proof-Lean_4-green.svg)](https://leanprover.github.io/)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

## Overview

This repository provides a formal Lean 4 formalization of the **Four Meta-Axioms** proposed in the paper:

> *Meta-Axioms as the Conceptual Foundation of the Universe: A Mathematical-Philosophical Perspective*  
> Takeo Yamamoto — [DOI: 10.5281/zenodo.18603974](https://doi.org/10.5281/zenodo.18603974)

The four meta-axioms are not domain-specific. They are proposed as the minimal conceptual structure underlying all phenomena — physical, mathematical, and cognitive. This formalization demonstrates that the framework is internally consistent and mathematically well-formed.

## The Four Meta-Axioms

Formalized in `Axioms.lean`:

1. **Extremum Principle**  
   Systems seek extrema of a conceptual function. Formally: `F[x] = Extremum L(x)`.

2. **Topological Space (Domain)**  
   All phenomena occur within a defined space with boundary conditions. `x ∈ X ⊂ ℝⁿ`.

3. **Logical Consistency**  
   Self-contradiction is excluded. `C[F] = 0`.

4. **Hierarchical Structure**  
   Macroscopic behavior emerges from hierarchically composed micro-functions. `F_macro = Σ wᵢ · F_micro(i)`.

## What the Lean Formalization Demonstrates

- The four axioms are mutually compatible (`UniverseModel` structure)
- Minimal realizations correspond to Occam's razor (`IsMinimalRealization`)
- Physical states satisfy the integrated functional (`physical_state_minimal`)
- The framework is compatible with Mathlib's topology, analysis, and order libraries

## Open Problems (`sorry`)

The following theorems remain unproven and are open for contribution:

| Theorem | Difficulty | Notes |
|---|---|---|
| `shannon_entropy_nonneg` | Medium | Requires convexity argument |
| `consistency_preserved` | Medium | Requires construction of combined system |
| `compact_extremum_exists` | Easy | Follows from Mathlib extreme value theorem |
| `unity_principle` | Hard/Philosophical | May require reformulation |

## Contributing

This project welcomes contributions via fork and pull request.  
All contributions must pass the Lean 4 CI before merging.  
The CI acts as the mathematical gatekeeper — if it passes, the contribution is formally valid.

```bash
# Build locally
lake build
```

## License

CC BY 4.0 — Attribution required.  
Author: Takeo Yamamoto


