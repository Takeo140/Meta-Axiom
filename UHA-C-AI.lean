License Apache 2.0  Takeo Yamamoto
namespace UHAComputerAI

abbrev U64 := UInt64

/- ================================================================
   COMPUTER STATE
   ================================================================ -/

structure ComputerState where
  pc       : U64
  accumulator : U64
  memory   : U64 → U64
  halted   : Bool
deriving Repr

/- ================================================================
   MEMORY
   ================================================================ -/

def readMemory
    (s : ComputerState)
    (addr : U64) : U64 :=
  s.memory addr

def writeMemory
    (s : ComputerState)
    (addr value : U64) : ComputerState :=
  { s with memory := fun a =>
      if a == addr then value else s.memory a }

/- ================================================================
   UHA COMPUTATION
   ================================================================ -/

def uhaMap (x : U64) : U64 :=
  x * x

def uhaStep (x : U64) : U64 :=
  x + (uhaMap x - x)

/- ================================================================
   PREDICTION
   ================================================================ -/

/--
Predict the next computational state.
-/
def predict (s : ComputerState) : U64 :=
  uhaStep s.accumulator

/- ================================================================
   INFERENCE
   ================================================================ -/

/--
Basic inference:
determine whether the predicted value differs from the
current computational state.
-/
inductive InferenceResult
  | unchanged
  | changed (next : U64)
deriving Repr

def infer (s : ComputerState) : InferenceResult :=
  let next := predict s
  if next == s.accumulator then
    .unchanged
  else
    .changed next

/- ================================================================
   PLANNING
   ================================================================ -/

inductive Plan
  | keep
  | update (value : U64)
  | halt
deriving Repr

def plan (s : ComputerState) : Plan :=
  match infer s with
  | .unchanged =>
      .keep
  | .changed next =>
      if s.halted then
        .halt
      else
        .update next

/- ================================================================
   OPTIMIZATION
   ================================================================ -/

/--
Select the computational action with the smallest structural cost.

For this reference implementation the optimization criterion is
simply "avoid unnecessary updates".
-/
def optimize (s : ComputerState) : Plan :=
  match plan s with
  | .keep =>
      .keep
  | .update value =>
      if value == s.accumulator then
        .keep
      else
        .update value
  | .halt =>
      .halt

/- ================================================================
   VERIFICATION
   ================================================================ -/

def verify (s : ComputerState) (p : Plan) : Bool :=
  match p with
  | .keep =>
      true

  | .update value =>
      !s.halted && value != s.accumulator

  | .halt =>
      true

/- ================================================================
   EXECUTION
   ================================================================ -/

def execute
    (s : ComputerState)
    (p : Plan) :
    ComputerState :=
  if !verify s p then
    { s with halted := true }
  else
    match p with
    | .keep =>
        { s with pc := s.pc + 1 }

    | .update value =>
        {
          s with
          accumulator := value
          pc := s.pc + 1
        }

    | .halt =>
        { s with halted := true }

/- ================================================================
   ONE AI-COMPUTER CYCLE
   ================================================================ -/

def aiComputerStep
    (s : ComputerState) :
    ComputerState :=
  let predicted := predict s
  let inferred :=
    match infer s with
    | .unchanged => .keep
    | .changed next => .update next

  let planned :=
    match inferred with
    | .keep => .keep
    | .update value => .update value
    | .halt => .halt

  let optimized := optimize s

  execute s optimized

/- ================================================================
   RUN
   ================================================================ -/

def run
    : Nat → ComputerState → ComputerState
  | 0, s => s
  | n + 1, s =>
      if s.halted then
        s
      else
        run n (aiComputerStep s)

/- ================================================================
   INITIAL COMPUTER
   ================================================================ -/

def emptyMemory : U64 → U64 :=
  fun _ => 0

def initialState : ComputerState :=
  {
    pc := 0
    accumulator := 2
    memory := emptyMemory
    halted := false
  }

/- ================================================================
   EXECUTION EXAMPLE
   ================================================================ -/

def finalState : ComputerState :=
  run 10 initialState

#eval initialState
#eval finalState

end UHAComputerAI
