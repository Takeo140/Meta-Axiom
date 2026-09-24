/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto

  Physical AI — Complete Closed-Loop Physical Intelligence Layer

  Architecture:

      Physical World
           │
         sense
           ↓
        observe
           ↓
       estimate
           ↓
        belief
           ↓
         plan
           ↓
       proposal
           ↓
         check
        ↙      ↘
    accepted   rejected
       │          │
       ↓          ↓
    proposal    fallback
       │          │
        └────┬─────┘
             ↓
           action
             ↓
          actuator
             ↓
           Plant
             ↓
        next state
             │
             └────────── closed loop

  The untrusted planner can propose arbitrary actions.
  Only checked actions or the certified fallback can reach the plant.

  SafetyCase provides the formal safety contract.
  WorldModel / Simulation can provide model-side invariants.
-/

import WorldModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

namespace WorldModel

variable {S Z O A D : Type*}

/-!
============================================================
1. Physical World
============================================================
-/

/-- Physical plant.

`step` is the actual physical transition.
`sense` is the physical observation interface.
-/
structure Plant (S A O D : Type*) where
  step : S → A → D → S
  sense : S → O


/-!
============================================================
2. Sensor / Estimator Layer
============================================================
-/

/-- Observation model. -/
structure Sensor (S O : Type*) where
  observe : S → O


/-- State estimator.

The estimator is allowed to be approximate.
Formal safety does not depend on trusting the estimator itself;
the SafetyCase must establish consistency.
-/
structure Estimator (O Z : Type*) where
  estimate : O → Z


/-!
============================================================
3. Actuator Layer
============================================================
-/

/-- Physical actuator.

The controller issues an abstract action `A`.
The actuator converts it into physical state evolution.
-/
structure Actuator (S A D : Type*) where
  apply : S → A → D → S


/-!
============================================================
4. Physical AI
============================================================
-/

/--
Complete Physical AI.

`plan` is explicitly untrusted.

`check` is the runtime safety gate.

`fallback` is the certified safe action.

The plant is the physical environment controlled by the system.
-/
structure PhysicalAI (S Z O A D : Type*) where
  plant : Plant S A O D

  sensor : Sensor S O

  estimator : Estimator O Z

  plan : Z → A

  check : Z → A → Bool

  fallback : Z → A

  actuator : Actuator S A D


/-!
============================================================
5. Perception
============================================================
-/

/-- Raw physical observation. -/
def PhysicalAI.observe
    (P : PhysicalAI S Z O A D) (s : S) : O :=
  P.sensor.observe s


/-- Estimated physical state. -/
def PhysicalAI.belief
    (P : PhysicalAI S Z O A D) (s : S) : Z :=
  P.estimator.estimate (P.observe s)


/-!
============================================================
6. Planning
============================================================
-/

/-- Untrusted AI proposal. -/
def PhysicalAI.proposal
    (P : PhysicalAI S Z O A D) (s : S) : A :=
  P.plan (P.belief s)


/-!
============================================================
7. Fail-Closed Safety Gate
============================================================
-/

/--
Only two actions can reach the actuator:

1. a checked proposal
2. the certified fallback

No third path exists.
-/
def PhysicalAI.control
    (P : PhysicalAI S Z O A D) (s : S) : A :=
  if P.check (P.belief s) (P.proposal s) = true then
    P.proposal s
  else
    P.fallback (P.belief s)


/-- Accepted proposal. -/
theorem PhysicalAI.control_of_check
    (P : PhysicalAI S Z O A D)
    (s : S)
    (h :
      P.check (P.belief s) (P.proposal s) = true) :
    P.control s = P.proposal s := by
  unfold PhysicalAI.control
  rw [if_pos h]


/-- Rejected proposal implies fallback. -/
theorem PhysicalAI.control_of_not_check
    (P : PhysicalAI S Z O A D)
    (s : S)
    (h :
      P.check (P.belief s) (P.proposal s) ≠ true) :
    P.control s = P.fallback (P.belief s) := by
  unfold PhysicalAI.control
  rw [if_neg h]


/--
Runtime action classification.

Every physical action is either:

* a verified proposal, or
* the fallback action.
-/
theorem PhysicalAI.control_certified
    (P : PhysicalAI S Z O A D)
    (s : S) :
    P.check (P.belief s) (P.control s) = true
      ∨
    P.control s = P.fallback (P.belief s) := by

  by_cases h :
      P.check (P.belief s) (P.proposal s) = true

  · left
    rw [P.control_of_check s h]
    exact h

  · right
    exact P.control_of_not_check s h


/-!
============================================================
8. Physical Execution
============================================================
-/

/--
Apply the selected control to the physical actuator.
-/
def PhysicalAI.act
    (P : PhysicalAI S Z O A D)
    (s : S)
    (d : D) : S :=
  P.actuator.apply s (P.control s) d


/--
Closed-loop physical transition.

This is the actual world transition, not a prediction.
-/
def PhysicalAI.stepWorld
    (P : PhysicalAI S Z O A D)
    (s : S)
    (d : D) : S :=
  P.act s d


/-!
============================================================
9. Complete Closed Loop
============================================================
-/

/--
One complete physical-AI cycle:

sense → estimate → plan → verify → act → physical transition.
-/
def PhysicalAI.cycle
    (P : PhysicalAI S Z O A D)
    (s : S)
    (d : D) : S :=
  P.stepWorld s d


/--
Repeated physical operation under an external disturbance sequence.
-/
def PhysicalAI.run
    (P : PhysicalAI S Z O A D) :
    S → List D → S
  | s, [] => s
  | s, d :: ds =>
      PhysicalAI.run P (P.stepWorld s d) ds


/-!
============================================================
10. Safety Certificate
============================================================
-/

/--
Formal safety certificate.

`Safe`:
  physical state belongs to the safe set.

`Consistent`:
  estimated belief is compatible with the actual state.

`DistOk`:
  disturbance is inside the certified disturbance envelope.

`check_sound`:
  an accepted action preserves safety.

`fallback_sound`:
  the fallback action preserves safety.
-/
structure SafetyCase
    (P : PhysicalAI S Z O A D) where

  Safe : S → Prop

  Consistent : Z → S → Prop

  DistOk : D → Prop

  sense_sound :
    ∀ s,
      Consistent (P.belief s) s

  check_sound :
    ∀ z s a,
      Consistent z s →
      P.check z a = true →
      Safe s →
      ∀ d,
        DistOk d →
        Safe (P.actuator.apply s a d)

  fallback_sound :
    ∀ z s,
      Consistent z s →
      Safe s →
      ∀ d,
        DistOk d →
        Safe (P.actuator.apply s (P.fallback z) d)


/-!
============================================================
11. One-Step Physical Safety
============================================================
-/

/--
Every physical transition preserves safety.

The planner itself does not appear in the assumptions.
Therefore arbitrary planner behaviour is permitted.
-/
theorem PhysicalAI.step_safe
    (P : PhysicalAI S Z O A D)
    (C : SafetyCase P)
    {s : S}
    (hs : C.Safe s)
    {d : D}
    (hd : C.DistOk d) :
    C.Safe (P.stepWorld s d) := by

  unfold PhysicalAI.stepWorld
  unfold PhysicalAI.act

  by_cases h :
      P.check (P.belief s) (P.proposal s) = true

  · rw [P.control_of_check s h]

    exact
      C.check_sound
        (P.belief s)
        s
        (P.proposal s)
        (C.sense_sound s)
        h
        hs
        d
        hd

  · rw [P.control_of_not_check s h]

    exact
      C.fallback_sound
        (P.belief s)
        s
        (C.sense_sound s)
        hs
        d
        hd


/-!
============================================================
12. Arbitrary-Length Physical Safety
============================================================
-/

/--
Safety is invariant over an arbitrary finite physical run.
-/
theorem PhysicalAI.run_safe
    (P : PhysicalAI S Z O A D)
    (C : SafetyCase P) :
    ∀ (ds : List D),
      (∀ d ∈ ds, C.DistOk d) →
      ∀ s,
        C.Safe s →
        C.Safe (P.run s ds) := by

  intro ds

  induction ds with

  | nil =>
      intro _ s hs
      exact hs

  | cons d ds ih =>
      intro hds s hs

      have hd :
          C.DistOk d :=
        hds d (by simp)

      have hds' :
          ∀ e ∈ ds, C.DistOk e :=
        fun e he =>
          hds e (by simp [he])

      exact
        ih
          hds'
          _
          (P.step_safe C hs hd)


/-!
============================================================
13. WorldModel Integration
============================================================
-/

/--
Pull an invariant from a formal world model into another system.
-/
def Invariant.pullback
    {X : Sys S A O}
    {Y : Sys S A O}
    (I : Invariant Y)
    (f : Simulation X Y) :
    Invariant X where

  holds s :=
    I.holds (f.encode s)

  preserved s a h := by
    have h' :=
      I.preserved
        (f.encode s)
        a
        h

    rw [f.step_commutes s a] at h'

    exact h'


/-!
============================================================
14. Physical AI Safety Interface
============================================================
-/

/--
A Physical AI is formally certified when a SafetyCase exists.
-/
def Certified
    (P : PhysicalAI S Z O A D) : Prop :=
  Nonempty (SafetyCase P)


/--
Certified systems always preserve the certified safety set.
-/
theorem certified_is_safe
    (P : PhysicalAI S Z O A D)
    (C : SafetyCase P) :
    ∀ {s d},
      C.Safe s →
      C.DistOk d →
      C.Safe (P.stepWorld s d) := by

  intro s d hs hd
  exact P.step_safe C hs hd


/-!
============================================================
15. Generic Physical Robot Interface
============================================================
-/

/--
A robot is a physical AI together with a state space.

This is intentionally abstract:

* wheeled robot
* quadruped
* manipulator
* factory robot
* autonomous vehicle
* low-cost embedded physical AI

can all instantiate the same interface.
-/
structure Robot (S Z O A D : Type*) where
  ai : PhysicalAI S Z O A D


/-- Robot closed-loop execution. -/
def Robot.run
    (R : Robot S Z O A D)
    (s : S)
    (ds : List D) : S :=
  R.ai.run s ds


/--
Robot safety theorem.

Once a SafetyCase is supplied, the robot remains
inside the certified safe set for the entire run.
-/
theorem Robot.run_safe
    (R : Robot S Z O A D)
    (C : SafetyCase R.ai)
    (ds : List D)
    (hds : ∀ d ∈ ds, C.DistOk d)
    (s : S)
    (hs : C.Safe s) :
    C.Safe (R.run s ds) := by

  exact
    R.ai.run_safe
      C
      ds
      hds
      s
      hs


end WorldModel
