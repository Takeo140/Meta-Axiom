import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open BigOperators

namespace MetaAxiomsUniverseEnglish

/-!
# Meta-Axioms Universe Framework — fully closed (no sorry)

Structural changes from prior version:
1. `g : Matrix (Fin 4) (Fin 4) ℝ`  replaces `Array (Array ℝ)`
   → proper 4×4 tensor with Mathlib support
2. `ScalarCurvature = Matrix.trace p.g`
   → mathematically correct trace; was an ad-hoc diagonal sum
3. `Trajectory = List SpacetimePoint`  replaces `Array SpacetimePoint`
   → List enables structural induction; Array does not
4. `EinsteinHilbertAction γ = (γ.map ScalarCurvature).sum`
   → `foldl` replaced by `.map.sum`; `List.sum_cons` / `List.map_cons`
      give clean algebraic lemmas
5. `exampleFalsifiable` sorry closed via `action_nil` + `norm_num`
-/

-- 1. Spacetime point
-- ────────────────────────────────────────────────────────────────────

structure SpacetimePoint where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ
  g : Matrix (Fin 4) (Fin 4) ℝ

namespace SpacetimePoint
def zero : SpacetimePoint :=
  { t := 0, x := 0, y := 0, z := 0, g := 0 }
end SpacetimePoint

-- 2. Trajectory
-- ────────────────────────────────────────────────────────────────────

def Trajectory := List SpacetimePoint

-- 3. Scalar curvature = metric trace
-- ────────────────────────────────────────────────────────────────────

def ScalarCurvature (p : SpacetimePoint) : ℝ :=
  Matrix.trace p.g

-- 4. Einstein-Hilbert action
-- ────────────────────────────────────────────────────────────────────

def EinsteinHilbertAction (γ : Trajectory) : ℝ :=
  (γ.map ScalarCurvature).sum

-- Core lemmas
-- ────────────────────────────────────────────────────────────────────

@[simp]
lemma action_nil : EinsteinHilbertAction [] = 0 := by
  simp [EinsteinHilbertAction]

@[simp]
lemma action_cons (p : SpacetimePoint) (γ : Trajectory) :
    EinsteinHilbertAction (p :: γ) = ScalarCurvature p + EinsteinHilbertAction γ := by
  simp [EinsteinHilbertAction, List.map_cons, List.sum_cons]

lemma action_append (γ₁ γ₂ : Trajectory) :
    EinsteinHilbertAction (γ₁ ++ γ₂) =
    EinsteinHilbertAction γ₁ + EinsteinHilbertAction γ₂ := by
  simp [EinsteinHilbertAction, List.map_append, List.sum_append]

lemma action_nonneg (γ : Trajectory)
    (h : ∀ p ∈ γ, 0 ≤ ScalarCurvature p) :
    0 ≤ EinsteinHilbertAction γ := by
  induction γ with
  | nil  => simp
  | cons hd tl ih =>
    rw [action_cons]
    exact add_nonneg (h hd (List.mem_cons_self hd tl))
      (ih (fun p hp => h p (List.mem_cons_of_mem hd hp)))

-- 5. Variation
-- ────────────────────────────────────────────────────────────────────

def Variation (γ δγ : Trajectory) (ε : ℝ) : Trajectory :=
  List.zipWith
    (fun p q =>
      { t := p.t + ε * q.t
        x := p.x + ε * q.x
        y := p.y + ε * q.y
        z := p.z + ε * q.z
        g := p.g })
    γ δγ

-- 6. Euler-Lagrange (finite difference)
-- ────────────────────────────────────────────────────────────────────

def EulerLagrange (γ δγ : Trajectory) (ε : ℝ) : ℝ :=
  (EinsteinHilbertAction (Variation γ δγ ε) - EinsteinHilbertAction γ) / ε

-- 7. Gradient-descent update
-- ────────────────────────────────────────────────────────────────────

def updateTrajectory (γ δγ : Trajectory) (ε : ℝ) : Trajectory :=
  Variation γ δγ (-ε)

-- 8. Simulation loop (structural recursion on Nat)
-- ────────────────────────────────────────────────────────────────────

def simulate (steps : Nat) (ε : ℝ) (trajectories : List Trajectory) :
    List Trajectory :=
  let rec loop : Nat → List Trajectory → List Trajectory
    | 0,     trs => trs
    | n + 1, trs =>
        let δγs := trs.map fun γ =>
          γ.map fun p => { SpacetimePoint.zero with g := p.g }
        let updated :=
          List.zipWith (fun γ δγ => updateTrajectory γ δγ ε) trs δγs
        loop n updated
  loop steps trajectories

-- 9. A4: Macro action with convex weight structure
-- ────────────────────────────────────────────────────────────────────

structure MacroWeights (ι : Type) [Fintype ι] where
  w       : ι → ℝ
  hNonNeg : ∀ i, 0 ≤ w i
  hSum    : ∑ i, w i = 1

variable {ι : Type} [Fintype ι]

def MacroAction
    (W : MacroWeights ι)
    (Fmicro : ι → Trajectory → ℝ)
    (γ : Trajectory) : ℝ :=
  ∑ i, W.w i * Fmicro i γ

-- 10. A3: Non-vacuous consistency
-- ────────────────────────────────────────────────────────────────────

structure IntegratedFramework where
  L           : Trajectory → ℝ
  F           : Trajectory → ℝ
  C           : (Trajectory → ℝ) → Prop
  holds       : C F
  falsifiable : ∃ G : Trajectory → ℝ, ¬ C G

-- 11. Universe
-- ────────────────────────────────────────────────────────────────────

structure Universe where
  framework    : IntegratedFramework
  trajectories : List Trajectory
  macroAction  : List Trajectory → ℝ
  simulateStep : Nat → ℝ → List Trajectory → List Trajectory

-- 12. Minkowski metric and particles
-- ────────────────────────────────────────────────────────────────────

def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

lemma minkowski_trace : Matrix.trace minkowskiMetric = 2 := by
  simp [Matrix.trace, Matrix.diag, minkowskiMetric]
  norm_num

def particle1 : Trajectory :=
  (List.range 100).map fun n =>
    { t := n * 0.01, x := n * 0.01, y := 0, z := 0, g := minkowskiMetric }

def particle2 : Trajectory :=
  (List.range 100).map fun n =>
    { t := n * 0.01, x := -(n * 0.01), y := 0, z := 0, g := minkowskiMetric }

-- 13. Consistency predicate and falsifiability — no sorry
--
-- Strategy: ActionEquality F := F = EinsteinHilbertAction
-- Witness:  G := fun _ => -1
-- Proof:    congr_fun h [] gives (-1 : ℝ) = EinsteinHilbertAction []
--           action_nil reduces rhs to 0
--           simp gives -1 = 0, closed by norm_num (embedded in simp)
-- ────────────────────────────────────────────────────────────────────

def ActionEquality : (Trajectory → ℝ) → Prop :=
  fun F => F = EinsteinHilbertAction

theorem action_holds : ActionEquality EinsteinHilbertAction := rfl

theorem exampleFalsifiable : ∃ G : Trajectory → ℝ, ¬ ActionEquality G :=
  ⟨fun _ => -1, by
    intro h
    have h0 : (fun _ => (-1 : ℝ)) [] = EinsteinHilbertAction [] :=
      congr_fun h []
    simp [action_nil] at h0⟩

-- 14. Example universe instance
-- ────────────────────────────────────────────────────────────────────

def example_universe : Universe :=
  { framework :=
      { L           := EinsteinHilbertAction
        F           := EinsteinHilbertAction
        C           := ActionEquality
        holds       := action_holds
        falsifiable := exampleFalsifiable }
    trajectories := [particle1, particle2]
    macroAction  := fun γs =>
      γs.foldl (fun acc γ => acc + EinsteinHilbertAction γ) 0
    simulateStep := simulate }

-- 15. Sanity lemma: particle1 has strictly positive action
-- ────────────────────────────────────────────────────────────────────

lemma minkowski_curvature (p : SpacetimePoint) (hp : p.g = minkowskiMetric) :
    ScalarCurvature p = 2 := by
  simp [ScalarCurvature, hp, minkowski_trace]

lemma particle1_action : EinsteinHilbertAction particle1 = 200 := by
  simp only [particle1, EinsteinHilbertAction, List.map_map, ScalarCurvature]
  simp only [Function.comp, minkowski_trace]
  simp [List.sum_map_const, List.length_map, List.length_range]
  norm_num

lemma particle1_action_pos : 0 < EinsteinHilbertAction particle1 := by
  rw [particle1_action]; norm_num

end MetaAxiomsUniverseEnglish
