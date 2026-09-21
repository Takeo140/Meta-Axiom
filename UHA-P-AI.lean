License Apache 2.0  Takeo Yamamoto
namespace UHAPhysicalAI

abbrev U64 := UInt64

/- ================================================================
   1. PHYSICAL WORLD
   ================================================================ -/

structure PhysicalState where
  position : U64
  velocity : U64
  target   : U64
  obstacle : U64
  energy   : U64
deriving Repr

/- ================================================================
   2. SENSOR
   ================================================================ -/

structure SensorFrame where
  position : U64
  velocity : U64
  target   : U64
  obstacle : U64
  energy   : U64
  sensorOK : Bool
deriving Repr

def sense (w : PhysicalState) : SensorFrame :=
  {
    position := w.position
    velocity := w.velocity
    target := w.target
    obstacle := w.obstacle
    energy := w.energy
    sensorOK := true
  }

/- ================================================================
   3. WORLD MODEL
   ================================================================ -/

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
   4. MEMORY
   ================================================================ -/

structure Memory where
  previous : WorldState
  valid : Bool
deriving Repr

def emptyMemory (w : WorldState) : Memory :=
  {
    previous := w
    valid := false
  }

def updateMemory
    (m : Memory)
    (w : WorldState) : Memory :=
  {
    previous := w
    valid := true
  }

/- ================================================================
   5. UHA COMPUTATIONAL CORE
   ================================================================ -/

def uhaMap (x : U64) : U64 :=
  x * x

def uhaStep (x : U64) : U64 :=
  x + (uhaMap x - x)

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

def uhaWorldStep (s : UHAState) : UHAState :=
  {
    position := uhaStep s.position
    velocity := uhaStep s.velocity
    target := s.target
    obstacle := s.obstacle
    energy := s.energy
  }

/- ================================================================
   6. PREDICTION
   ================================================================ -/

structure Prediction where
  nextPosition : U64
  nextVelocity : U64
deriving Repr

def predict (s : UHAState) : Prediction :=
  {
    nextPosition := uhaStep s.position
    nextVelocity := uhaStep s.velocity
  }

/- ================================================================
   7. INFERENCE
   ================================================================ -/

inductive Inference
  | targetReached
  | obstacleDetected
  | energyLow
  | moveForward
  | brake
  | idle
deriving Repr, DecidableEq

def infer
    (s : UHAState)
    (p : Prediction) :
    Inference :=
  if s.energy == 0 then
    .energyLow
  else if p.nextPosition == s.obstacle then
    .obstacleDetected
  else if s.position == s.target then
    .targetReached
  else if s.position < s.target then
    .moveForward
  else
    .brake

/- ================================================================
   8. ACTION
   ================================================================ -/

inductive Action
  | idle
  | accelerate
  | brake
  | halt
deriving Repr, DecidableEq

def actionOf : Inference → Action
  | .targetReached => .idle
  | .obstacleDetected => .halt
  | .energyLow => .halt
  | .moveForward => .accelerate
  | .brake => .brake
  | .idle => .idle

/- ================================================================
   9. PLANNING
   ================================================================ -/

structure Plan where
  action : Action
  predictedPosition : U64
deriving Repr

def plan
    (s : UHAState)
    (p : Prediction)
    (i : Inference) :
    Plan :=
  {
    action := actionOf i
    predictedPosition := p.nextPosition
  }

/- ================================================================
   10. OPTIMIZATION
   ================================================================ -/

/--
Avoid unnecessary acceleration when the target has already
been reached or an obstacle is predicted.
-/
def optimize
    (s : UHAState)
    (p : Plan) :
    Plan :=
  match p.action with
  | .accelerate =>
      if p.predictedPosition == s.obstacle then
        { p with action := .halt }
      else
        p

  | .brake =>
      p

  | .idle =>
      p

  | .halt =>
      p

/- ================================================================
   11. VERIFICATION
   ================================================================ -/

/--
Final verification before an action reaches the physical world.
-/
def verify
    (sensorOK : Bool)
    (s : UHAState)
    (p : Plan) :
    Bool :=
  if !sensorOK then
    false
  else if s.energy == 0 then
    false
  else
    match p.action with
    | .accelerate =>
        p.predictedPosition != s.obstacle

    | .brake =>
        true

    | .idle =>
        true

    | .halt =>
        true

/- ================================================================
   12. SAFETY FILTER
   ================================================================ -/

def safetyFilter
    (sensorOK : Bool)
    (s : UHAState)
    (p : Plan) :
    Plan :=
  if verify sensorOK s p then
    p
  else
    { p with action := .halt }

/- ================================================================
   13. ACTUATOR
   ================================================================ -/

def actuator
    (a : Action)
    (w : PhysicalState) :
    PhysicalState :=
  match a with

  | .idle =>
      {
        w with
        velocity := 0
      }

  | .accelerate =>
      {
        w with
        position := w.position + 1
        velocity := w.velocity + 1
        energy := w.energy - 1
      }

  | .brake =>
      {
        w with
        velocity := 0
        energy := w.energy - 1
      }

  | .halt =>
      {
        w with
        velocity := 0
      }

/- ================================================================
   14. COMPLETE PHYSICAL-AI CYCLE
   ================================================================ -/

structure PhysicalAISystem where
  world : PhysicalState
  memory : Memory
  cycle : Nat
deriving Repr

def physicalAIStep
    (sys : PhysicalAISystem) :
    PhysicalAISystem :=

  let sensor := sense sys.world

  let world := encodeWorld sensor

  let memory :=
    updateMemory sys.memory world

  let uha :=
    encodeUHA world

  let computed :=
    uhaWorldStep uha

  let prediction :=
    predict computed

  let inference :=
    infer computed prediction

  let initialPlan :=
    plan computed prediction inference

  let optimizedPlan :=
    optimize computed initialPlan

  let safePlan :=
    safetyFilter
      sensor.sensorOK
      computed
      optimizedPlan

  let nextWorld :=
    actuator safePlan.action sys.world

  {
    world := nextWorld
    memory := memory
    cycle := sys.cycle + 1
  }

/- ================================================================
   15. RUN
   ================================================================ -/

def run
    : Nat → PhysicalAISystem → PhysicalAISystem
  | 0, sys => sys

  | n + 1, sys =>
      if sys.world.energy == 0 then
        sys
      else
        run n (physicalAIStep sys)

/- ================================================================
   16. INITIAL WORLD
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
    memory := emptyMemory
      {
        position := 0
        velocity := 0
        target := 10
        obstacle := 100
        energy := 100
      }
    cycle := 0
  }

/- ================================================================
   17. EXECUTION
   ================================================================ -/

def finalSystem : PhysicalAISystem :=
  run 10 initialSystem

#eval finalSystem

end UHAPhysicalAI
