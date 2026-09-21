License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Fin.Basic

namespace UHAPhysicalAI

/-!
  UHA Physical AI
  ----------------
  Sensor
    ↓
  World Model
    ↓
  UHA Computational Kernel
    ↓
  Policy
    ↓
  Safety Filter
    ↓
  Actuator
    ↓
  Physical World
    ↺

  This is a discrete physical-AI reference model.
  It is a simulator / executable architecture, not hardware control code.
-/

/- ================================================================
   1. UHA-64 COMPUTATIONAL SUBSTRATE
   ================================================================ -/

abbrev U64 := UInt64

def add64 (a b : U64) : U64 :=
  a + b

def sub64 (a b : U64) : U64 :=
  a - b

def mul64 (a b : U64) : U64 :=
  a * b

def uhaMap (x : U64) : U64 :=
  mul64 x x

def uhaUpdate (active : Bool) (x : U64) : U64 :=
  if active then
    add64 x (sub64 (uhaMap x) x)
  else
    x

theorem uhaInactive (x : U64) :
    uhaUpdate false x = x := by
  simp [uhaUpdate]

/- ================================================================
   2. PHYSICAL WORLD
   ================================================================ -/

/--
Discrete one-dimensional physical world.

position   : robot position
velocity   : robot velocity
target     : target position
obstacle   : obstacle position
energy     : remaining energy
-/
structure PhysicalState where
  position : U64
  velocity : U64
  target   : U64
  obstacle : U64
  energy   : U64
deriving Repr

/- ================================================================
   3. SENSOR LAYER
   ================================================================ -/

structure SensorFrame where
  position       : U64
  velocity       : U64
  target         : U64
  obstacle       : U64
  energy         : U64
  sensorOK       : Bool
deriving Repr

def sense (world : PhysicalState) : SensorFrame :=
  {
    position := world.position
    velocity := world.velocity
    target := world.target
    obstacle := world.obstacle
    energy := world.energy
    sensorOK := true
  }

/- ================================================================
   4. WORLD MODEL
   ================================================================ -/

/--
Internal world-model representation.

The physical world is converted into a computational state.
-/
structure WorldState where
  position : U64
  velocity : U64
  target   : U64
  obstacle : U64
  energy   : U64
deriving Repr

def encodeWorld (s : SensorFrame) : WorldState :=
  {
    position := s.position
    velocity := s.velocity
    target := s.target
    obstacle := s.obstacle
    energy := s.energy
  }

/- ================================================================
   5. UHA WORLD-MODEL KERNEL
   ================================================================ -/

/--
The UHA kernel transforms selected world variables.

For a physical-AI implementation the kernel does not directly
control the actuator. It computes an internal state first.
-/
structure UHAState where
  position : U64
  velocity : U64
  target   : U64
  obstacle : U64
  energy   : U64
deriving Repr

def encodeUHA (w : WorldState) : UHAState :=
  {
    position := w.position
    velocity := w.velocity
    target := w.target
    obstacle := w.obstacle
    energy := w.energy
  }

/--
One UHA computational step.

The position/velocity state is transformed while the target,
obstacle and energy remain part of the world context.
-/
def uhaStep (s : UHAState) : UHAState :=
  {
    position := uhaUpdate true s.position
    velocity := uhaUpdate true s.velocity
    target := s.target
    obstacle := s.obstacle
    energy := s.energy
  }

/- ================================================================
   6. ACTION SPACE
   ================================================================ -/

inductive Action
  | idle
  | accelerate
  | brake
  | halt
deriving Repr, DecidableEq

structure ActuatorCommand where
  action : Action
  authority : Bool
deriving Repr

/- ================================================================
   7. PHYSICAL-AI POLICY
   ================================================================ -/

/--
Simple discrete controller.

The policy is deliberately separated from the UHA kernel:
UHA computes the state; policy determines the action.
-/
def policy (s : UHAState) : ActuatorCommand :=
  if s.energy == 0 then
    { action := .halt, authority := false }
  else if s.position == s.obstacle then
    { action := .halt, authority := true }
  else if s.position == s.target then
    { action := .idle, authority := true }
  else if s.position < s.target then
    { action := .accelerate, authority := true }
  else
    { action := .brake, authority := true }

/- ================================================================
   8. SAFETY LAYER
   ================================================================ -/

/--
Safety filter.

The controller is not allowed to send an unsafe command.
Sensor failure, loss of energy, or an obstacle condition causes halt.
-/
def safetyFilter
    (sensorOK : Bool)
    (s : UHAState)
    (cmd : ActuatorCommand) :
    ActuatorCommand :=
  if !sensorOK then
    { action := .halt, authority := false }
  else if s.energy == 0 then
    { action := .halt, authority := false }
  else if s.position == s.obstacle then
    { action := .halt, authority := false }
  else
    cmd

/- ================================================================
   9. ACTUATOR / PHYSICAL TRANSITION
   ================================================================ -/

/--
Physical transition.

This is a discrete simulator for actuator effects.
-/
def actuator
    (cmd : ActuatorCommand)
    (s : PhysicalState) :
    PhysicalState :=
  match cmd.action with
  | .idle =>
      {
        s with
        velocity := 0
      }

  | .accelerate =>
      {
        s with
        position := s.position + 1
        velocity := s.velocity + 1
        energy := s.energy - 1
      }

  | .brake =>
      {
        s with
        velocity := 0
        energy := s.energy - 1
      }

  | .halt =>
      {
        s with
        velocity := 0
      }

/- ================================================================
   10. COMPLETE PHYSICAL-AI STEP
   ================================================================ -/

/--
Complete closed-loop computation:

Physical World
 → Sensor
 → World Model
 → UHA
 → Policy
 → Safety
 → Actuator
 → Physical World
-/
def physicalAIStep
    (world : PhysicalState) :
    PhysicalState :=
  let sensor := sense world
  let encoded := encodeWorld sensor
  let uha := encodeUHA encoded
  let computed := uhaStep uha
  let command := policy computed
  let safeCommand :=
    safetyFilter sensor.sensorOK computed command
  actuator safeCommand world

/- ================================================================
   11. MULTI-STEP EXECUTION
   ================================================================ -/

def runPhysicalAI :
    Nat → PhysicalState → PhysicalState
  | 0, world => world
  | n + 1, world =>
      runPhysicalAI n (physicalAIStep world)

/- ================================================================
   12. WORLD-MODEL CORRESPONDENCE
   ================================================================ -/

/--
Sensor encoding preserves the physical state variables.
-/
theorem encodeWorld_position
    (world : PhysicalState) :
    (encodeWorld (sense world)).position = world.position := by
  rfl

theorem encodeWorld_velocity
    (world : PhysicalState) :
    (encodeWorld (sense world)).velocity = world.velocity := by
  rfl

theorem encodeWorld_target
    (world : PhysicalState) :
    (encodeWorld (sense world)).target = world.target := by
  rfl

theorem encodeWorld_obstacle
    (world : PhysicalState) :
    (encodeWorld (sense world)).obstacle = world.obstacle := by
  rfl

/- ================================================================
   13. UHA FIXED POINT
   ================================================================ -/

/--
A state is a UHA fixed point when the computational update
does not change the value.
-/
def UHAFixedPoint (x : U64) : Prop :=
  uhaUpdate true x = x

/--
At a UHA fixed point, the kernel preserves the value.
-/
theorem fixedPoint_preserved
    (x : U64)
    (h : UHAFixedPoint x) :
    uhaUpdate true x = x := by
  exact h

/- ================================================================
   14. PHYSICAL-AI SYSTEM
   ================================================================ -/

structure PhysicalAISystem where
  world : PhysicalState
  cycle : Nat
deriving Repr

def stepSystem (sys : PhysicalAISystem) :
    PhysicalAISystem :=
  {
    world := physicalAIStep sys.world
    cycle := sys.cycle + 1
  }

def runSystem :
    Nat → PhysicalAISystem → PhysicalAISystem
  | 0, sys => sys
  | n + 1, sys =>
      runSystem n (stepSystem sys)

/- ================================================================
   15. DEMONSTRATION
   ================================================================ -/

def initialWorld : PhysicalState :=
  {
    position := 0
    velocity := 0
    target := 10
    obstacle := 100
    energy := 100
  }

def initialSystem : PhysicalAISystem :=
  {
    world := initialWorld
    cycle := 0
  }

def finalSystem : PhysicalAISystem :=
  runSystem 10 initialSystem

#eval finalSystem

end UHAPhysicalAI
