import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant

namespace WorldModel

/-!
# Unified World Model

Architecture:

  1. Spacetime
  2. Lorentzian metric
  3. Metric inverse
  4. Affine connection
  5. Torsion / metric compatibility
  6. Levi-Civita structure
  7. Riemann curvature
  8. Ricci tensor
  9. Scalar curvature
 10. Einstein tensor
 11. Stress-energy tensor
 12. Einstein equation
 13. Einstein-Hilbert density
 14. Einstein-Hilbert action
 15. Variational interface
 16. World / law / meta-law
 17. Physical theory
 18. Falsifiability
 19. Optimization
 20. UHA computational substrate
 21. Unified World Model

The file intentionally separates:

  mathematical definitions
  ------------------------
  physical/model-theoretic assumptions
  ------------------------
  computational representation

No claim is made that the UHA substrate is physically identical
to spacetime. The interface expresses representability only.
-/

/- ============================================================
   Basic indices
   ============================================================ -/

abbrev SpacetimeIndex := Fin 4

abbrev Tensor2 :=
  Matrix SpacetimeIndex SpacetimeIndex ℝ

abbrev Tensor3 :=
  SpacetimeIndex →
  SpacetimeIndex →
  SpacetimeIndex →
  ℝ

abbrev Tensor4 :=
  SpacetimeIndex →
  SpacetimeIndex →
  SpacetimeIndex →
  SpacetimeIndex →
  ℝ


/- ============================================================
   Spacetime
   ============================================================ -/

/--
Abstract point-set representation of spacetime.

Differentiable-manifold structure is intentionally abstracted.
-/
structure Spacetime where
  Point : Type


/- ============================================================
   Lorentzian metric
   ============================================================ -/

/--
Coordinate representation of a Lorentzian metric.

The Lorentzian condition is expressed by congruence to
diag(-1,+1,+1,+1).
-/
structure LorentzMetric (M : Spacetime) where

  g :
    M.Point → Tensor2

  symmetric :
    ∀ p μ ν,
      g p μ ν = g p ν μ

  nondegenerate :
    ∀ p,
      Matrix.det (g p) ≠ 0

  lorentzian :
    ∀ p,
      ∃ P : Tensor2,
        Matrix.det P ≠ 0 ∧
        ∀ μ ν,
          (P.transpose * g p * P) μ ν =
            if μ = ν then
              if μ = 0 then
                (-1 : ℝ)
              else
                (1 : ℝ)
            else
              0


/- ============================================================
   Metric inverse
   ============================================================ -/

/--
Inverse metric represented explicitly.

Both left and right inverse conditions are retained.
-/
structure MetricInverse
    (M : Spacetime)
    (g : LorentzMetric M) where

  gInv :
    M.Point → Tensor2

  left_inverse :
    ∀ p,
      gInv p * g.g p = 1

  right_inverse :
    ∀ p,
      g.g p * gInv p = 1


/- ============================================================
   Connection
   ============================================================ -/

/--
Affine connection coefficients Γᵏᵢⱼ.
-/
structure Connection
    (M : Spacetime) where

  Γ :
    M.Point →
    SpacetimeIndex →
    SpacetimeIndex →
    SpacetimeIndex →
    ℝ


/- ============================================================
   Coordinate derivative
   ============================================================ -/

/--
Abstract coordinate derivative.

This is intentionally separated from the geometric structures.
-/
class CoordinateDerivative
    (M : Spacetime) where

  D :
    M.Point →
    SpacetimeIndex →
    (M.Point → ℝ) →
    ℝ


/- ============================================================
   Torsion
   ============================================================ -/

/--
Coordinate torsion tensor:

  Tᵏᵢⱼ = Γᵏᵢⱼ - Γᵏⱼᵢ
-/
def Torsion
    {M : Spacetime}
    (∇ : Connection M) :
    M.Point →
    SpacetimeIndex →
    SpacetimeIndex →
    SpacetimeIndex →
    ℝ :=
  fun p k i j =>
    ∇.Γ p k i j -
    ∇.Γ p k j i


/--
Torsion-free condition.
-/
def TorsionFree
    {M : Spacetime}
    (∇ : Connection M) : Prop :=
  ∀ p k i j,
    Torsion ∇ p k i j = 0


/- ============================================================
   Metric compatibility
   ============================================================ -/

/--
Metric compatibility:

  ∇ₖ gᵢⱼ = 0

expanded in coordinates.
-/
def MetricCompatible
    {M : Spacetime}
    (g : LorentzMetric M)
    (∇ : Connection M)
    [CoordinateDerivative M] : Prop :=

  ∀ p k i j,

    CoordinateDerivative.D p k
      (fun q => g.g q i j)

    -
    ∑ l,
      ∇.Γ p l k i *
      g.g p l j

    -
    ∑ l,
      ∇.Γ p l k j *
      g.g p i l

    = 0


/- ============================================================
   Levi-Civita connection
   ============================================================ -/

/--
Levi-Civita connection:

  torsion-free
  +
  metric-compatible
-/
structure LeviCivita
    {M : Spacetime}
    (g : LorentzMetric M)
    (∇ : Connection M)
    [CoordinateDerivative M] where

  torsion_free :
    TorsionFree ∇

  metric_compatible :
    MetricCompatible g ∇


/- ============================================================
   Curvature
   ============================================================ -/

/--
Riemann curvature tensor.

Convention:

  Rᵏₗᵢⱼ =
      ∂ᵢ Γᵏⱼₗ
    - ∂ⱼ Γᵏᵢₗ
    + Γᵏᵢₘ Γᵐⱼₗ
    - Γᵏⱼₘ Γᵐᵢₗ
-/
def Riemann
    {M : Spacetime}
    [CoordinateDerivative M]
    (∇ : Connection M) :
    M.Point → Tensor4 :=

  fun p k l i j =>

    CoordinateDerivative.D p i
      (fun q => ∇.Γ q k j l)

    -
    CoordinateDerivative.D p j
      (fun q => ∇.Γ q k i l)

    +
    ∑ m,
      ∇.Γ p k i m *
      ∇.Γ p m j l

    -
    ∑ m,
      ∇.Γ p k j m *
      ∇.Γ p m i l


/- ============================================================
   Ricci tensor
   ============================================================ -/

/--
Ricci contraction.
-/
def Ricci
    {M : Spacetime}
    [CoordinateDerivative M]
    (∇ : Connection M) :
    M.Point → Tensor2 :=

  fun p i j =>
    ∑ k,
      Riemann ∇ p k i k j


/- ============================================================
   Scalar curvature
   ============================================================ -/

/--
Scalar curvature:

  R = gⁱʲ Rᵢⱼ
-/
def ScalarCurvature
    {M : Spacetime}
    (gInv : MetricInverse M g)
    [CoordinateDerivative M]
    (∇ : Connection M) :
    M.Point → ℝ :=

  fun p =>
    ∑ i, ∑ j,
      gInv.gInv p i j *
      Ricci ∇ p i j


/- ============================================================
   Einstein tensor
   ============================================================ -/

/--
Einstein tensor:

  Gᵢⱼ = Rᵢⱼ - 1/2 R gᵢⱼ
-/
def EinsteinTensor
    {M : Spacetime}
    (g : LorentzMetric M)
    (gInv : MetricInverse M g)
    [CoordinateDerivative M]
    (∇ : Connection M) :
    M.Point → Tensor2 :=

  fun p i j =>
    Ricci ∇ p i j
    -
    (1 / 2 : ℝ) *
      ScalarCurvature gInv ∇ p *
      g.g p i j


/- ============================================================
   Stress-energy tensor
   ============================================================ -/

/--
Matter stress-energy tensor.
-/
structure StressEnergy
    (M : Spacetime) where

  T :
    M.Point → Tensor2

  symmetric :
    ∀ p μ ν,
      T p μ ν = T p ν μ


/- ============================================================
   Physical constants
   ============================================================ -/

/--
Physical/model parameters.
-/
structure PhysicalConstants where

  cosmologicalConstant :
    ℝ

  gravitationalConstant :
    ℝ

  piValue :
    ℝ


/--
Mathematical default constants.

G = 1 and Λ = 0 are normalization/model choices,
not empirical claims.
-/
def defaultConstants : PhysicalConstants where

  cosmologicalConstant := 0

  gravitationalConstant := 1

  piValue := Real.pi


/- ============================================================
   Einstein equation
   ============================================================ -/

/--
Einstein field equation:

  Gᵢⱼ + Λ gᵢⱼ
    =
  8πG Tᵢⱼ
-/
def EinsteinEquation
    {M : Spacetime}
    (g : LorentzMetric M)
    (gInv : MetricInverse M g)
    [CoordinateDerivative M]
    (∇ : Connection M)
    (T : StressEnergy M)
    (c : PhysicalConstants) : Prop :=

  ∀ p i j,

    EinsteinTensor g gInv ∇ p i j
      +
      c.cosmologicalConstant *
        g.g p i j

    =

    8 *
      c.piValue *
      c.gravitationalConstant *
      T.T p i j


/- ============================================================
   Metric determinant / volume density
   ============================================================ -/

/--
Coordinate volume density for Lorentzian signature.

The Lorentzian condition guarantees the intended sign
under the stated metric convention.
-/
def VolumeDensity
    {M : Spacetime}
    (g : LorentzMetric M) :
    M.Point → ℝ :=

  fun p =>
    Real.sqrt
      (-Matrix.det (g.g p))


/- ============================================================
   Einstein-Hilbert density
   ============================================================ -/

/--
Einstein-Hilbert Lagrangian density:

  √(-g) R
-/
def EinsteinHilbertDensity
    {M : Spacetime}
    (g : LorentzMetric M)
    (gInv : MetricInverse M g)
    [CoordinateDerivative M]
    (∇ : Connection M) :
    M.Point → ℝ :=

  fun p =>
    VolumeDensity g p *
    ScalarCurvature gInv ∇ p


/- ============================================================
   Abstract world integration
   ============================================================ -/

/--
Abstract integration functional.

Measure theory and domain/boundary conditions are intentionally
outside this layer.
-/
class WorldIntegral
    (M : Spacetime) where

  integrate :
    (M.Point → ℝ) → ℝ


/- ============================================================
   Einstein-Hilbert action
   ============================================================ -/

/--
Einstein-Hilbert action.
-/
def EinsteinHilbertAction
    {M : Spacetime}
    [WorldIntegral M]
    (g : LorentzMetric M)
    (gInv : MetricInverse M g)
    [CoordinateDerivative M]
    (∇ : Connection M) :
    ℝ :=

  WorldIntegral.integrate
    (EinsteinHilbertDensity g gInv ∇)


/- ============================================================
   Metric variation
   ============================================================ -/

/--
Admissible symmetric metric variation.
-/
structure MetricVariation
    (M : Spacetime) where

  variation :
    M.Point → Tensor2

  symmetric :
    ∀ p μ ν,
      variation p μ ν =
      variation p ν μ


/- ============================================================
   First variation interface
   ============================================================ -/

/--
Abstract first variation of the Einstein-Hilbert action.

A complete treatment would additionally encode:
  - differentiability,
  - admissible variations,
  - boundary terms,
  - Gibbons-Hawking-York contribution,
  - matter variation.
-/
class FirstVariation
    {M : Spacetime}
    [WorldIntegral M] where

  derivative :
    LorentzMetric M →
    MetricInverse M →
    Connection M →
    MetricVariation M →
    ℝ


/- ============================================================
   Stationarity
   ============================================================ -/

/--
Stationarity under all admissible metric variations.
-/
def StationaryEinsteinHilbert
    {M : Spacetime}
    [WorldIntegral M]
    [CoordinateDerivative M]
    [FirstVariation] :
    LorentzMetric M →
    MetricInverse M →
    Connection M →
    Prop :=

  fun g gInv ∇ =>
    ∀ h,
      FirstVariation.derivative
        g gInv ∇ h = 0


/- ============================================================
   Variational principle
   ============================================================ -/

/--
Formal bridge between the variational and field-equation
formulations.

This is intentionally represented as a mathematical interface:
a future full development can replace it with a theorem
including the required analytic and boundary assumptions.
-/
structure EinsteinVariationPrinciple
    {M : Spacetime}
    [WorldIntegral M]
    [CoordinateDerivative M]
    [FirstVariation] where

  stationary_implies_field_equation :

    ∀
      (g : LorentzMetric M)
      (gInv : MetricInverse M g)
      (∇ : Connection M)
      (T : StressEnergy M)
      (c : PhysicalConstants),

      StationaryEinsteinHilbert
        g gInv ∇ →

      EinsteinEquation
        g gInv ∇ T c


/- ============================================================
   Generic laws
   ============================================================ -/

/--
A physical/model law over a state space.
-/
abbrev Law (S : Type) :=
  S → Prop


/--
Numerical evaluation functional.
-/
abbrev Evaluation (S : Type) :=
  S → ℝ


/--
Meta-law constraining candidate laws.
-/
abbrev MetaLaw (S : Type) :=
  Law S → Prop


/- ============================================================
   Generic World
   ============================================================ -
