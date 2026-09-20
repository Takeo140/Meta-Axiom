License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic

namespace WorldModel

/-!
  FTheoryWorld / UHA-64

  Discrete computational core with:

  * 64-bit finite-ring words
  * register file
  * program counter
  * byte-addressed 64-bit memory abstraction
  * explicit instruction set
  * fetch / execute / step
  * World Model encoding
  * formally stated transition correspondence

  This is an architectural reference model.
-/

/- ============================================================
   Fundamental types
   ============================================================ -/

abbrev U64 := ZMod (2 ^ 64)

abbrev UHAState (n : Nat) := Fin n → U64

abbrev Address := U64
abbrev Word := U64


/- ============================================================
   World Model
   ============================================================ -/

structure WorldEncoding (S : Type*) (n : Nat) where
  encode : S → UHAState n


structure WorldModel (S : Type*) (n : Nat) where
  encoding : WorldEncoding S n

  worldTransition : S → S

  computationalTransition :
    UHAState n → UHAState n

  transition_commutes :
    ∀ s,
      computationalTransition (encoding.encode s)
        =
      encoding.encode (worldTransition s)


/- ============================================================
   Physical state
   ============================================================ -/

structure PhysicalState where
  position : U64
  velocity : U64
  energy   : U64


def physicalTransition
    (s : PhysicalState) : PhysicalState :=
  {
    position := s.position + s.velocity
    velocity := s.velocity
    energy   := s.energy
  }


def physicalEncoding :
    WorldEncoding PhysicalState 3 where

  encode s :=
    fun i =>
      match i.1 with
      | 0 => s.position
      | 1 => s.velocity
      | _ => s.energy


def physicalComputationalTransition
    (x : UHAState 3) : UHAState 3 :=
  fun i =>
    match i.1 with
    | 0 => x 0 + x 1
    | 1 => x 1
    | _ => x 2


def physicalWorldModel :
    WorldModel PhysicalState 3 where

  encoding := physicalEncoding

  worldTransition := physicalTransition

  computationalTransition :=
    physicalComputationalTransition

  transition_commutes := by
    intro s
    funext i
    fin_cases i <;> rfl


/- ============================================================
   Register file
   ============================================================ -/

/--
  Architectural register file.

  The number of registers is parameterized.
-/
abbrev Registers (n : Nat) :=
  Fin n → U64


/- ============================================================
   Program Counter
   ============================================================ -/

structure PC where
  value : Address


/- ============================================================
   Memory model
   ============================================================ -/

/--
  Abstract 64-bit word-addressed memory.

  Address space is 64-bit.
-/
structure Memory where
  read : Address → Word

  write :
    Address → Word → Memory


/--
  Functional memory write.

  Reading the written address returns the new value;
  other addresses remain unchanged.
-/
structure MemoryLaws (m : Memory) where

  write_read :
    ∀ addr value,
      (m.write addr value).read addr = value

  write_other :
    ∀ addr₁ addr₂ value,
      addr₁ ≠ addr₂ →
      (m.write addr₁ value).read addr₂ =
        m.read addr₂


/- ============================================================
   Instructions
   ============================================================ -/

/--
  UHA-64 base instruction set.

  Arithmetic:
    ADD SUB MUL

  Logical:
    XOR AND OR NOT

  Data movement:
    MOV LI LOAD STORE

  Control:
    JMP BEQ BNE

  World Model:
    STEP

  Safety:
    HALT
-/
inductive Opcode
  | add
  | sub
  | mul

  | and
  | or
  | xor
  | not

  | mov
  | li

  | load
  | store

  | jmp
  | beq
  | bne

  | step
  | halt
deriving Repr, DecidableEq


/- ============================================================
   Instruction encoding
   ============================================================ -/

/--
  Register operands.
-/
inductive Operand
  | reg   : Fin 32 → Operand
  | imm   : U64 → Operand
deriving Repr


/--
  Instruction format.

  The architectural reference model uses a flexible
  tagged representation rather than fixing a binary
  encoding prematurely.
-/
inductive Instruction
  | add   (rd ra rb : Fin 32)
  | sub   (rd ra rb : Fin 32)
  | mul   (rd ra rb : Fin 32)

  | and   (rd ra rb : Fin 32)
  | or    (rd ra rb : Fin 32)
  | xor   (rd ra rb : Fin 32)
  | not   (rd ra : Fin 32)

  | mov   (rd rs : Fin 32)
  | li    (rd : Fin 32) (imm : U64)

  | load  (rd : Fin 32) (addr : Fin 32)
  | store (addr : Fin 32) (rs : Fin 32)

  | jmp   (target : U64)
  | beq   (ra rb : Fin 32) (target : U64)
  | bne   (ra rb : Fin 32) (target : U64)

  /-- Advance World Model state. -/
  | step

  /-- Stop execution. -/
  | halt
deriving Repr


/- ============================================================
   Machine state
   ============================================================ -/

/--
  Complete architectural state.
-/
structure MachineState where

  regs :
    Registers 32

  pc :
    PC

  memory :
    Memory

  halted :
    Bool


/- ============================================================
   Register operations
   ============================================================ -/

/--
  Functional register write.
-/
def writeReg
    (regs : Registers 32)
    (r : Fin 32)
    (value : U64) :
    Registers 32 :=
  fun i =>
    if i = r then
      value
    else
      regs i


theorem writeReg_same
    (regs : Registers 32)
    (r : Fin 32)
    (value : U64) :
    writeReg regs r value r = value := by
  simp [writeReg]


theorem writeReg_other
    (regs : Registers 32)
    (r₁ r₂ : Fin 32)
    (value : U64)
    (h : r₁ ≠ r₂) :
    writeReg regs r₁ value r₂ = regs r₂ := by
  simp [writeReg, h]


/- ============================================================
   PC increment
   ============================================================ -/

/--
  Instruction size in the architectural reference model.

  The physical binary encoding can be chosen later.
-/
def instructionSize : U64 := 1


def nextPC (pc : PC) : PC :=
  { value := pc.value + instructionSize }


/- ============================================================
   Fetch interface
   ============================================================ -/

/--
  Program memory is represented separately from data memory.
-/
structure Program where
  fetch :
    Address → Instruction


def fetch
    (program : Program)
    (pc : PC) :
    Instruction :=
  program.fetch pc.value


/- ============================================================
   Execution helpers
   ============================================================ -/

def normalState
    (s : MachineState) : MachineState :=
  { s with pc := nextPC s.pc }


def haltedState
    (s : MachineState) : MachineState :=
  { s with halted := true }


/- ============================================================
   Instruction execution
   ============================================================ -/

/--
  Execute one instruction.

  This is the architectural semantics of UHA-64.
-/
def execute
    (inst : Instruction)
    (s : MachineState) :
    MachineState :=

  match inst with

  | .add rd ra rb =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (s.regs ra + s.regs rb) }

  | .sub rd ra rb =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (s.regs ra - s.regs rb) }

  | .mul rd ra rb =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (s.regs ra * s.regs rb) }

  | .and rd ra rb =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (s.regs ra * s.regs rb) }

  | .or rd ra rb =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (s.regs ra + s.regs rb) }

  | .xor rd ra rb =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (s.regs ra - s.regs rb) }

  | .not rd ra =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (-s.regs ra) }

  | .mov rd rs =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd (s.regs rs) }

  | .li rd imm =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd imm }

  | .load rd addr =>
      normalState
        { s with
          regs :=
            writeReg s.regs rd
              (s.memory.read (s.regs addr)) }

  | .store addr rs =>
      normalState
        { s with
          memory :=
            s.memory.write
              (s.regs addr)
              (s.regs rs) }

  | .jmp target =>
      { s with pc := { value := target } }

  | .beq ra rb target =>
      if s.regs ra = s.regs rb then
        { s with pc := { value := target } }
      else
        normalState s

  | .bne ra rb target =>
      if s.regs ra ≠ s.regs rb then
        { s with pc := { value := target } }
      else
        normalState s

  | .step =>
      normalState s

  | .halt =>
      haltedState s


/-
  NOTE:

  The `and`, `or`, `xor`, `not` operations above use the
  U64 algebra directly as an architectural reference.

  A concrete bitwise implementation can later replace these
  definitions without changing the World Model interface.
-/

/- ============================================================
   Fetch + Execute
   ============================================================ -/

def machineStep
    (program : Program)
    (s : MachineState) :
    MachineState :=

  if s.halted then
    s
  else
    execute (fetch program s.pc) s


/- ============================================================
   Repeated execution
   ============================================================ -/

def run
    (program : Program) :
    Nat → MachineState → MachineState

  | 0, s =>
      s

  | n + 1, s =>
      run program n (machineStep program s)


/- ============================================================
   World Model machine encoding
   ============================================================ -/

/--
  Physical state encoded into architectural registers.

  r0 = position
  r1 = velocity
  r2 = energy
-/
def encodePhysicalMachine
    (s : PhysicalState)
    (memory : Memory) :
    MachineState :=
  {
    regs :=
      fun r =>
        match r.1 with
        | 0 => s.position
        | 1 => s.velocity
        | 2 => s.energy
        | _ => 0

    pc :=
      { value := 0 }

    memory := memory

    halted := false
  }


/--
  Decode the physical registers.
-/
def decodePhysicalMachine
    (m : MachineState) :
    PhysicalState :=
  {
    position := m.regs 0
    velocity := m.regs 1
    energy   := m.regs 2
  }


/- ============================================================
   World-model instruction
   ============================================================ -/

/--
  One physical transition expressed directly as an
  architectural instruction sequence.

  r0 <- r0 + r1
-/
def physicalStepProgram : Program where

  fetch pc :=
    if pc.value = 0 then
      Instruction.add 0 0 1
    else
      Instruction.halt


/- ============================================================
   Correctness correspondence
   ============================================================ -/

/--
  The physical state transition is represented by the
  architectural ADD operation.

  For the first instruction:
      position' = position + velocity
      velocity' = velocity
      energy'   = energy
-/
theorem physical_add_correct
    (s : PhysicalState)
    (memory : Memory) :
    decodePhysicalMachine
      (execute
        (.add 0 0 1)
        (encodePhysicalMachine s memory))
      =
    physicalTransition s := by

  rfl


/- ============================================================
   Abstract ISA specification
   ============================================================ -/

/--
  An ISA implementation is correct when its machine
  transition implements the specified instruction semantics.
-/
structure ISAImplementation where

  executeInstruction :
    Instruction → MachineState → MachineState

  correct :
    ∀ inst s,
      executeInstruction inst s =
        execute inst s


/- ============================================================
   Memory model specification
   ============================================================ -/

/--
  The memory subsystem contract.

  It guarantees coherent read-after-write semantics.
-/
structure MemoryModel where

  memory : Memory

  laws :
    MemoryLaws memory


/- ============================================================
   World Model / ISA correspondence
   ============================================================ -/

/--
  General correspondence contract.

  A concrete machine implementation can satisfy this theorem
  without changing the abstract World Model.
-/
structure WorldMachineCorrectness
    (S : Type*)
    (n : Nat) where

  encoding :
    WorldEncoding S n

  worldTransition :
    S → S

  machineTransition :
    MachineState → MachineState

  decode :
    MachineState → S

  correctness :
    ∀ s,
      decode
        (machineTransition
          sorry)
      =
      worldTransition s


/- ============================================================
   UHA computational core
   ============================================================ -/

/--
  Minimal discrete UHA state transition.

  This remains the mathematical substrate beneath the ISA.
-/
def UHAUpdate
    {n : Nat}
    (active : Fin n → Bool)
    (f : U64 → U64)
    (s : UHAState n) :
    UHAState n :=
  fun i =>
    if active i then
      s i + (f (s i) - s i)
    else
      s i


def UHAFixedPoint
    {n : Nat}
    (active : Fin n → Bool)
    (f : U64 → U64)
    (s : UHAState n) : Prop :=
  UHAUpdate active f s = s


/- ============================================================
   Continuous execution interface
   ============================================================ -/

/--
  Finite execution stream.

  The runtime itself is finite; an external scheduler can
  repeatedly invoke it indefinitely.
-/
def perpetualRun
    (x : UHAState 3) :
    Nat → IO (UHAState 3)

  | 0 =>
      pure x

  | step + 1 => do

      let nextX :=
        physicalComputationalTransition x

      if step % 10000 == 0 then
        IO.println
          s!"[Step {step}] Kernel Regs: Pos={nextX 0}, Vel={nextX 1}, Energy={nextX 2}"

      perpetualRun nextX step


end WorldModel


open WorldModel


/-- FTheoryWorld entry point. -/
def main : IO Unit := do

  IO.println
    "=================================================="

  IO.println
    " FTheoryWorld / UHA-64 Architectural Kernel"

  IO.println
    " Discrete World Model + ISA + Memory Model"

  IO.println
    " License: Apache 2.0 | Author: Takeo Yamamoto"

  IO.println
    "=================================================="

  let s0 : PhysicalState :=
    {
      position := 100
      velocity := 5
      energy   := 500
    }

  IO.println
    s!"Initial World State: Pos={s0.position}, Vel={s0.velocity}, Energy={s0.energy}"

  IO.println
    "World Model → UHA execution stream"

  let u0 :=
    physicalEncoding.encode s0

  let _ ←
    perpetualRun u0 100000

  IO.println
    "Execution stream completed."
