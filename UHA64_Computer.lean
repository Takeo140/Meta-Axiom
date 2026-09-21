License Apache 2.0 Takeo Yamamoto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

namespace UHA64

/-!
# UHA-64 Computer
Author: Takeo Yamamoto
License: Apache-2.0

Executable reference computer for the UHA / World Model architecture.

Architecture
  * 64-bit words
  * 32 general-purpose registers
  * 64-bit program counter
  * byte-addressed memory abstraction
  * fixed 32-bit instructions
  * fetch / decode / execute / step
  * World Model state transition
  * HALT

This is an executable virtual computer / architectural reference model,
not a physical CPU.
-/

/- ============================================================
   Word
   ============================================================ -/

/-- Concrete machine word. -/
abbrev Word := UInt64

/-- Register index. -/
abbrev Reg := Fin 32

/-- Program address. -/
abbrev Address := UInt64


/- ============================================================
   World Model / UHA mathematical substrate
   ============================================================ -/

abbrev U64 := ZMod (2 ^ 64)

abbrev UHAState (n : Nat) := Fin n → U64

def UHAUpdate
    {n : Nat}
    (active : Fin n → Bool)
    (F : UHAState n → UHAState n)
    (x : UHAState n) :
    UHAState n :=
  fun i =>
    if active i = true then
      x i + (F x i - x i)
    else
      x i

theorem UHAUpdate_active
    {n : Nat}
    (active : Fin n → Bool)
    (F : UHAState n → UHAState n)
    (x : UHAState n)
    (i : Fin n)
    (h : active i = true) :
    UHAUpdate active F x i = F x i := by
  simp [UHAUpdate, h]

theorem UHAUpdate_inactive
    {n : Nat}
    (active : Fin n → Bool)
    (F : UHAState n → UHAState n)
    (x : UHAState n)
    (i : Fin n)
    (h : active i = false) :
    UHAUpdate active F x i = x i := by
  simp [UHAUpdate, h]


/- ============================================================
   World Model
   ============================================================ -/

structure WorldEncoding (S : Type*) (n : Nat) where
  encode : S → UHAState n

structure WorldModel (S : Type*) (n : Nat) where
  encoding : WorldEncoding S n
  worldTransition : S → S
  computationalTransition : UHAState n → UHAState n

  transition_commutes :
    ∀ s,
      computationalTransition (encoding.encode s)
        =
      encoding.encode (worldTransition s)


/- ============================================================
   Physical World
   ============================================================ -/

structure PhysicalState where
  position : U64
  velocity : U64
  energy : U64


def physicalTransition
    (s : PhysicalState) :
    PhysicalState :=
  {
    position := s.position + s.velocity
    velocity := s.velocity
    energy := s.energy
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
    (x : UHAState 3) :
    UHAState 3 :=
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


theorem physicalWorldModel_correct
    (s : PhysicalState) :
    physicalComputationalTransition
      (physicalEncoding.encode s)
      =
    physicalEncoding.encode
      (physicalTransition s) := by
  exact physicalWorldModel.transition_commutes s


/- ============================================================
   Opcodes
   ============================================================ -/

/--
Instruction encoding:

bits 31..26 : opcode (6 bits)
bits 25..21 : rd
bits 20..16 : ra
bits 15..11 : rb
bits 15..0  : immediate / address

The encoding is deliberately simple and fixed-width.
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


def Opcode.code : Opcode → UInt64
  | .add   => 0
  | .sub   => 1
  | .mul   => 2
  | .and   => 3
  | .or    => 4
  | .xor   => 5
  | .not   => 6
  | .mov   => 7
  | .li    => 8
  | .load  => 9
  | .store => 10
  | .jmp   => 11
  | .beq   => 12
  | .bne   => 13
  | .step  => 14
  | .halt  => 15


def decodeOpcode : UInt64 → Option Opcode
  | 0  => some .add
  | 1  => some .sub
  | 2  => some .mul
  | 3  => some .and
  | 4  => some .or
  | 5  => some .xor
  | 6  => some .not
  | 7  => some .mov
  | 8  => some .li
  | 9  => some .load
  | 10 => some .store
  | 11 => some .jmp
  | 12 => some .beq
  | 13 => some .bne
  | 14 => some .step
  | 15 => some .halt
  | _  => none


/- ============================================================
   Instruction
   ============================================================ -/

inductive Instruction

  | add   (rd ra rb : Reg)
  | sub   (rd ra rb : Reg)
  | mul   (rd ra rb : Reg)

  | and   (rd ra rb : Reg)
  | or    (rd ra rb : Reg)
  | xor   (rd ra rb : Reg)

  | not   (rd ra : Reg)
  | mov   (rd rs : Reg)

  | li    (rd : Reg) (imm : Word)

  | load  (rd addr : Reg)
  | store (addr rs : Reg)

  | jmp   (target : Word)

  | beq   (ra rb : Reg) (target : Word)
  | bne   (ra rb : Reg) (target : Word)

  | step
  | halt

deriving Repr


/- ============================================================
   Register file
   ============================================================ -/

structure Registers where
  get : Reg → Word


def zeroRegisters : Registers :=
  {
    get := fun _ => 0
  }


def writeReg
    (r : Registers)
    (rd : Reg)
    (value : Word) :
    Registers :=
  {
    get := fun i =>
      if i = rd then
        value
      else
        r.get i
  }


/- ============================================================
   Machine Memory
   ============================================================ -/

/--
Functional memory.

Uninitialized memory reads as zero.
-/
structure Memory where
  read : Address → Word
  write : Address → Word → Memory


def emptyMemory : Memory :=
  {
    read := fun _ => 0

    write := fun addr value =>
      {
        read := fun a =>
          if a = addr then
            value
          else
            0

        write := fun addr' value' =>
          {
            read := fun a =>
              if a = addr' then
                value'
              else if a = addr then
                value
              else
                0

            write := fun a v =>
              {
                read := fun q =>
                  if q = a then v
                  else if q = addr' then value'
                  else if q = addr then value
                  else 0

                write := fun _ _ => emptyMemory.write a v
              }
          }
      }
  }


/- ============================================================
   Machine State
   ============================================================ -/

structure Machine where
  regs : Registers
  pc : Address
  memory : Memory
  halted : Bool


def initialMachine : Machine :=
  {
    regs := zeroRegisters
    pc := 0
    memory := emptyMemory
    halted := false
  }


/- ============================================================
   Register helpers
   ============================================================ -/

def r0 : Reg := 0
def r1 : Reg := 1
def r2 : Reg := 2
def r3 : Reg := 3


/- ============================================================
   Instruction constructors
   ============================================================ -/

/--
Assembler-like helpers.
-/

def ADD (rd ra rb : Reg) : Instruction :=
  .add rd ra rb

def SUB (rd ra rb : Reg) : Instruction :=
  .sub rd ra rb

def MUL (rd ra rb : Reg) : Instruction :=
  .mul rd ra rb

def AND (rd ra rb : Reg) : Instruction :=
  .and rd ra rb

def OR (rd ra rb : Reg) : Instruction :=
  .or rd ra rb

def XOR (rd ra rb : Reg) : Instruction :=
  .xor rd ra rb

def NOT (rd ra : Reg) : Instruction :=
  .not rd ra

def MOV (rd rs : Reg) : Instruction :=
  .mov rd rs

def LI (rd : Reg) (x : Word) : Instruction :=
  .li rd x

def LOAD (rd addr : Reg) : Instruction :=
  .load rd addr

def STORE (addr rs : Reg) : Instruction :=
  .store addr rs

def JMP (target : Word) : Instruction :=
  .jmp target

def BEQ (ra rb : Reg) (target : Word) : Instruction :=
  .beq ra rb target

def BNE (ra rb : Reg) (target : Word) : Instruction :=
  .bne ra rb target

def STEP : Instruction :=
  .step

def HALT : Instruction :=
  .halt


/- ============================================================
   PC
   ============================================================ -/

def nextPC (pc : Address) : Address :=
  pc + 4


/- ============================================================
   Instruction execution
   ============================================================ -/

def execute
    (inst : Instruction)
    (m : Machine) :
    Machine :=

  match inst with

  | .add rd ra rb =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.regs.get ra + m.regs.get rb)

        pc := nextPC m.pc
      }

  | .sub rd ra rb =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.regs.get ra - m.regs.get rb)

        pc := nextPC m.pc
      }

  | .mul rd ra rb =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.regs.get ra * m.regs.get rb)

        pc := nextPC m.pc
      }

  | .and rd ra rb =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.regs.get ra &&& m.regs.get rb)

        pc := nextPC m.pc
      }

  | .or rd ra rb =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.regs.get ra ||| m.regs.get rb)

        pc := nextPC m.pc
      }

  | .xor rd ra rb =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.regs.get ra ^^^ m.regs.get rb)

        pc := nextPC m.pc
      }

  | .not rd ra =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (~~~m.regs.get ra)

        pc := nextPC m.pc
      }

  | .mov rd rs =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.regs.get rs)

        pc := nextPC m.pc
      }

  | .li rd imm =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            imm

        pc := nextPC m.pc
      }

  | .load rd addr =>
      {
        m with
        regs :=
          writeReg
            m.regs
            rd
            (m.memory.read (m.regs.get addr))

        pc := nextPC m.pc
      }

  | .store addr rs =>
      {
        m with
        memory :=
          m.memory.write
            (m.regs.get addr)
            (m.regs.get rs)

        pc := nextPC m.pc
      }

  | .jmp target =>
      {
        m with
        pc := target
      }

  | .beq ra rb target =>
      if m.regs.get ra = m.regs.get rb then
        {
          m with
          pc := target
        }
      else
        {
          m with
          pc := nextPC m.pc
        }

  | .bne ra rb target =>
      if m.regs.get ra ≠ m.regs.get rb then
        {
          m with
          pc := target
        }
      else
        {
          m with
          pc := nextPC m.pc
        }

  | .step =>
      {
        m with
        pc := nextPC m.pc
      }

  | .halt =>
      {
        m with
        halted := true
      }


/- ============================================================
   Program
   ============================================================ -/

structure Program where
  code : Address → Instruction


def fetch
    (p : Program)
    (pc : Address) :
    Instruction :=
  p.code pc


def machineStep
    (p : Program)
    (m : Machine) :
    Machine :=
  if m.halted then
    m
  else
    execute (fetch p m.pc) m


/-- Finite execution. -/
def run
    (p : Program)
    : Nat → Machine → Machine

  | 0, m =>
      m

  | n + 1, m =>
      run p n (machineStep p m)


/- ============================================================
   World Model ↔ Machine
   ============================================================ -/

def encodePhysical
    (s : PhysicalState) :
    Registers :=
  {
    get := fun r =>
      match r.1 with
      | 0 => UInt64.ofNat s.position.val
      | 1 => UInt64.ofNat s.velocity.val
      | 2 => UInt64.ofNat s.energy.val
      | _ => 0
  }


/--
Concrete UHA-64 machine representation of the physical world.
-/
def encodePhysicalMachine
    (s : PhysicalState)
    (memory : Memory) :
    Machine :=
  {
    regs := encodePhysical s
    pc := 0
    memory := memory
    halted := false
  }


/- ============================================================
   World Model program
   ============================================================ -/

/--
At address 0:

    r0 := r0 + r1

Then HALT at address 4.
-/
def physicalWorldProgram : Program where

  code pc :=
    if pc = 0 then
      ADD 0 0 1
    else
      HALT


/- ============================================================
   World Model instruction
   ============================================================ -/

/--
One World Model transition.

The first three registers encode:

    r0 = position
    r1 = velocity
    r2 = energy
-/
def worldModelStep
    (m : Machine) :
    Machine :=
  execute
    (ADD 0 0 1)
    m


/- ============================================================
   Concrete World Model
   ============================================================ -/

def physicalMachineTransition
    (s : PhysicalState)
    (memory : Memory) :
    Machine :=
  worldModelStep
    (encodePhysicalMachine s memory)


/- ============================================================
   Machine correspondence
   ============================================================ -/

/--
The architectural instruction implements the intended
discrete physical position update.
-/
theorem physical_add_register
    (s : PhysicalState)
    (memory : Memory) :
    (physicalMachineTransition s memory).regs.get 0
      =
    UInt64.ofNat
      ((s.position + s.velocity).val) := by
  simp [physicalMachineTransition,
        worldModelStep,
        encodePhysicalMachine,
        encodePhysical,
        execute,
        writeReg]


/- ============================================================
   Simple test program
   ============================================================ -/

/--
Example:

    r0 = 10
    r1 = 5
    r2 = r0 + r1
    r3 = r2 * r1
    HALT
-/
def exampleProgram : Program where

  code pc :=
    match pc with

    | 0 =>
        LI 0 10

    | 4 =>
        LI 1 5

    | 8 =>
        ADD 2 0 1

    | 12 =>
        MUL 3 2 1

    | 16 =>
        HALT

    | _ =>
        HALT


def exampleMachine : Machine :=
  initialMachine


/- ============================================================
   World Model demo
   ============================================================ -/

def initialPhysicalState : PhysicalState :=
  {
    position := 100
    velocity := 5
    energy := 500
  }


/- ============================================================
   Display
   ============================================================ -/

def showMachine
    (m : Machine) :
    IO Unit := do

  IO.println
    "--------------------------------------------"

  IO.println
    s!"PC     = {m.pc}"

  IO.println
    s!"R0     = {m.regs.get 0}"

  IO.println
    s!"R1     = {m.regs.get 1}"

  IO.println
    s!"R2     = {m.regs.get 2}"

  IO.println
    s!"R3     = {m.regs.get 3}"

  IO.println
    s!"HALTED = {m.halted}"

  IO.println
    "--------------------------------------------"


/- ============================================================
   Main
   ============================================================ -/

def main : IO Unit := do

  IO.println
    "================================================"

  IO.println
    " UHA-64 COMPUTER"

  IO.println
    " World Model + UHA Computational Core"

  IO.println
    " 64-bit / 32-register virtual architecture"

  IO.println
    " Author: Takeo Yamamoto"

  IO.println
    " License: Apache-2.0"

  IO.println
    "================================================"

  IO.println ""

  IO.println
    "Running arithmetic program..."

  let m1 :=
    run exampleProgram 5 exampleMachine

  showMachine m1

  IO.println
    ""

  IO.println
    "Running World Model..."

  let physical :=
    initialPhysicalState

  IO.println
    s!"World position = {physical.position}"

  IO.println
    s!"World velocity = {physical.velocity}"

  let wm :=
    physicalMachineTransition
      physical
      emptyMemory

  IO.println
    s!"UHA-64 R0 after STEP = {wm.regs.get 0}"

  IO.println
    s!"UHA-64 R1            = {wm.regs.get 1}"

  IO.println
    s!"UHA-64 R2            = {wm.regs.get 2}"

  IO.println ""

  IO.println
    "UHA-64 COMPUTER: OK"


end UHA64
