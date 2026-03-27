import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

namespace MetaAxioms

/-!
# Meta-Axioms: Mathematical-Philosophical Framework
Revised formulation addressing:
1. A2 (Topology) now used substantively via continuity
2. A3 (Consistency) carries structural content
3. A4 (Hierarchy) enforces convex weight constraint
4. IsRealization is non-redundant
-/

-- ─────────────────────────────────────────────────
-- A1: Extremum Principle
-- L achieves a global minimum at x₀
-- ─────────────────────────────────────────────────
def IsMinimal {X : Type} (L : X → ℝ) (x₀ : X) : Prop :=
  ∀ x, L x₀ ≤ L x

-- ─────────────────────────────────────────────────
-- A2: Topological Space
-- L is continuous and achieves its minimum at x₀.
-- Topology is substantively required: continuity is
-- a topological property; IsMinimal alone is purely
-- order-theoretic and does not invoke the topology.
-- ─────────────────────────────────────────────────
structure TopologicalMinimum (X : Type) [TopologicalSpace X] where
  L  : X → ℝ
  x₀ : X
  hL : Continuous L          -- A2: topology used here
  hMin : IsMinimal L x₀      -- A1 ∧ A2 jointly

-- ─────────────────────────────────────────────────
-- A3: Logical Consistency
-- A predicate C is consistent with F when:
--   (i)  C holds for F
--   (ii) C is not vacuously true (falsifiable)
-- We encode this as: C F holds, AND ∃ G such that ¬(C G).
-- This distinguishes genuine constraint from trivial Prop.
-- ─────────────────────────────────────────────────
structure IsConsistent {X : Type}
    (C : (X → ℝ) → Prop)
    (F : X → ℝ) : Prop where
  holds     : C F
  falsifiable : ∃ G : X → ℝ, ¬ C G

-- ─────────────────────────────────────────────────
-- A4: Hierarchical Structure
-- Macro function is a convex combination of micro functions.
-- Constraint: weights are non-negative and sum to 1.
-- ─────────────────────────────────────────────────
structure HierarchicalMacro {ι : Type} [Fintype ι] (X : Type) where
  w       : ι → ℝ
  Fmicro  : ι → X → ℝ
  hNonNeg : ∀ i, 0 ≤ w i
  hSum    : ∑ i, w i = 1

def MacroFunction {ι : Type} [Fintype ι] {X : Type}
    (H : HierarchicalMacro X (ι := ι)) : X → ℝ :=
  fun x => ∑ i, H.w i * H.Fmicro i x

-- ─────────────────────────────────────────────────
-- Integrated Framework
-- Combines A1–A4 without redundancy.
-- ─────────────────────────────────────────────────
structure IntegratedFramework (X : Type) [TopologicalSpace X]
    (ι : Type) [Fintype ι] where
  -- A1 + A2
  tm : TopologicalMinimum X
  -- A3
  C  : (X → ℝ) → Prop
  F  : X → ℝ
  hC : IsConsistent C F
  -- A4
  H  : HierarchicalMacro X (ι := ι)

-- ─────────────────────────────────────────────────
-- Realization
-- x₀ realizes the framework iff it is the topological minimum.
-- A3 content lives in the framework structure, not repeated here.
-- ─────────────────────────────────────────────────
def IsRealization {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (M : IntegratedFramework X ι)
    (x₀ : X) : Prop :=
  M.tm.x₀ = x₀

-- ─────────────────────────────────────────────────
-- Lemma: realized point is a global minimum of L
-- ─────────────────────────────────────────────────
lemma realization_is_minimal {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (M : IntegratedFramework X ι)
    (x₀ : X)
    (hR : IsRealization M x₀) :
    IsMinimal M.tm.L x₀ := by
  rw [← hR]
  exact M.tm.hMin

-- ─────────────────────────────────────────────────
-- Lemma: MacroFunction is non-negative at x when
--        all micro functions are non-negative
-- ─────────────────────────────────────────────────
lemma macro_nonneg {ι : Type} [Fintype ι] {X : Type}
    (H : HierarchicalMacro X (ι := ι))
    (hF : ∀ i x, 0 ≤ H.Fmicro i x)
    (x : X) :
    0 ≤ MacroFunction H x := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (H.hNonNeg i) (hF i x)

end MetaAxioms
