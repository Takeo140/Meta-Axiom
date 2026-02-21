# F-Theory: Cosmological Physics

[![Lean 4 CI](https://img.shields.io/badge/Formal_Proof-Lean_4-green.svg)](https://leanprover.github.io/)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

## Overview

This repository provides a Lean 4 formalization of a theoretical framework that models the unified structure of the universe via the extremal principle of F-theory.

The framework distinguishes between two complementary aspects of reality:

- **Obverse** — the material/physical aspect
- **Reverse** — the mathematical/logical aspect

Their correspondence is formally verified using Lean 4.

> *F-Theory: Cosmological Physics*  
> Takeo Yamamoto — [DOI: 10.5281/zenodo.17635922](https://doi.org/10.5281/zenodo.17635922)

## Core Framework

### Axioms (formalized in `Cosmology.lean`)

1. **Extremum Principle** — Systems evolve to minimize action: `δA = 0`
2. **Obverse-Reverse Correspondence** — Material reality and mathematical structure are connected via continuous mapping
3. **Logical Consistency** — The universe functions as a self-consistent formal system

### Key Derivations (`Derivations.lean`)

From these axioms, the framework derives:

- Cosmic expansion
- Dark matter structure
- Dark energy behavior
- Mass-energy equivalence as a logical consequence of hierarchical consistency

## Relationship to Meta-Axioms

This framework is an application of the four meta-axioms to cosmological physics. The extremal principle here corresponds directly to Meta-Axiom 1, while the Obverse-Reverse correspondence instantiates Meta-Axioms 2 and 4.

See also: [Meta-Axiom repository](https://github.com/Takeo140/Meta-Axiom)

## What the Lean Formalization Demonstrates

- The Obverse-Reverse correspondence is formally consistent
- Cosmological phenomena can be derived from the extremal principle
- The logical structure is free of internal contradictions

## Contributing

Contributions via fork and pull request are welcome.  
All contributions must pass the Lean 4 CI before merging.

```bash
lake build
```

## License

CC BY 4.0 — Attribution required.  
Author: Takeo Yamamoto  
Zenodo: [DOI: 10.5281/zenodo.17635922](https://doi.org/10.5281/zenodo.17635922)

