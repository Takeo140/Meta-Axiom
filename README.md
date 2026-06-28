# Meta-Axiom: A Mathematical-Philosophical Framework for Universal Optimization

[![Lean 4](https://img.shields.io/badge/Lean-4-orange)](https://lean-lang.org/)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18603974.svg)](https://doi.org/10.5281/zenodo.18603974)

This repository provides a formal **Lean 4** verification of the **"Four Meta-Axioms"** (collectively referred to as **F-Theory**), a mathematical-philosophical framework proposed by *Takeo Yamamoto*. 

The framework establishes a rigorous foundation for the conceptual laws of the universe, aiming to unify pure mathematics, theoretical physics, and biological structures through minimality, consistency, topology, and hierarchical organization.

---

## ── Theoretical Overview: The Four Meta-Axioms

The entire framework is grounded in the **Extremum Principle** and structured around four fundamental pillars:

1. **Extremum Principle ($A_1$)**  
   Every systemic behavior or state is determined by the extremization of a governing functional $L(x)$:
   $$F[x] = \text{Extremum } L(x)$$

2. **Topological Space ($A_2$)**  
   The underlying domain of states $x$ is embedded within a well-defined topological space $X$:
   $$x \in X \subset \mathbb{R}^n$$

3. **Logical Consistency ($A_3$)**  
   The system satisfies strict, internal logical consistency, meaning the contradiction or error functional $C[F]$ vanishes identically:
   $$C[F] = 0$$

4. **Hierarchical Structure ($A_4$)**  
   Macro-level laws and behaviors emerge as a weighted summation or convergence of micro-level dynamics:
   $$F_{\text{macro}} = \sum w_i \cdot F_{\text{micro}}(i)$$

---

## ── Status: Fully Proven (CI-Verified)

All theorems, definitions, and applications within this repository are **fully proven via the Curry-Howard correspondence**. There are **no `sorry` placeholders** in the main branch. Continuous Integration (CI) via GitHub Actions ensures the integrity and axiomatic consistency of the proof state.

### Key Resolved Proofs
* **`compact_extremum_exists`**: Proof of the existence of extrema on compact topological spaces using `IsCompact.exists_isMin` and `exists_isMax` ($A_2 \implies A_1$).
* **`consistency_preserved`**: Mathematical proof showing the invariance and preservation of logical consistency under the transformation of Meta-Axioms ($A_3$).
* **`unity_principle`**: Formal derivation of hierarchical convergence, proving how localized micro-dynamics scale into unified macro-structures ($A_4$).
* **`shannon_entropy_nonneg`**: Non-negativity of Shannon entropy derived rigorously via log-convexity properties, supporting the information-theoretic applications.

---

## ── Repository Structure

```text
├── .github/workflows/    # CI configuration (ci.yml) for automated Lean 4 verification
├── Metaaxiom.lean        # Core definitions of the 4 Meta-Axioms and consistency proofs
├── Axioms.lean           # Auxiliary lemmas, topological properties, and foundational math
├── CMA.lean              # ComputeMetaAxioms framework for algorithmic validation
├── Derivations.lean      # Minkowski trace proofs and algebraic simplifications
├── Ftheory.lean          # Application to cosmology, fundamental physics, and F-theory
├── Collatz.lean          # Structural analysis and constraints on the Collatz Conjecture
├── Dna.lean              # Application to genetic systems and information-theoretic bound
└── Medical.lean          # MetaRepair module for biological systems & homeostatic optimization
