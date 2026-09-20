License Apache 2.0  Takeo Yamamoto
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
  FTheoryWorld / UHA-64 (revised)

  Changes from the first draft:
  * U64 := BitVec 64 (real bitwise and/or/xor/not)
  * Memory is a concrete function Address → Word (no longer an empty type);
    the memory laws are theorems, not hypotheses
  * `step` instruction is tied to a World Model hook (`worldStep`)
  * the `sorry` in the correspondence is gone: a concrete simulation theorem
    is proved by induction over an arbitrary number of world steps
  * unused Operand / Opcode removed

  NOTE: written without a Lean toolchain at hand — run `lake build` and
  adjust simp lemma names if your Mathlib version differs.
-/

namespace WorldModel

/- ============================ Types ============================ -/

abbrev U64 := BitVec 64
abbrev Address := U64
abbrev Word := U64
abbrev Registers (n : Nat) := Fin n → U64
abbrev UHAState (n : Nat) := Fin n → U64
abbrev Memory := Address → Word

/- ============================ Memory =========================== -/

def memWrite (m : Memory) (a : Address) (v : Word) : Memory :=
  Function.update m a v

theorem memWrite_read_same (m : Memory) (a : Address) (v : Word) :
    memWrite m a v a = v := by
  simp [memWrite]

theorem memWrite_read_other (m : Memory) (a₁ a₂ : Address) (v : Word)
    (h : a₁ ≠ a₂) :
    memWrite m a₁ v a₂ = m a₂ := by
  simp [memWrite, Function.update_apply, Ne.symm h]

/- ========================= World Model ========================= -/

universe u

structure WorldEncoding (S : Type u) (n : Nat) where
  encode : S → UHAState n

structure WorldModel (S : Type u) (n : Nat) where
  encoding : WorldEncoding S n
  worldTransition : S → S
  computationalTransition : UHAState n → UHAState n
  transition_commutes :
    ∀ s, computationalTransition (encoding.encode s)
          = encoding.encode (worldTransition s)

structure PhysicalState where
  position : U64
  velocity : U64
  energy   : U64

def physicalTransition (s : PhysicalState) : PhysicalState :=
  { position := s.position + s.velocity
    velocity := s.velocity
    energy   := s.energy }

def physicalEncoding : WorldEncoding PhysicalState 3 where
  encode s := fun i =>
    match i.1 with
    | 0 => s.position
    | 1 => s.velocity
    | _ => s.energy

def physicalComputationalTransition (x : UHAState 3) : UHAState 3 :=
  fun i =>
    match i.1 with
    | 0 => x 0 + x 1
    | 1 => x 1
    | _ => x 2

def physicalWorldModel : WorldModel PhysicalState 3 where
  encoding := physicalEncoding
  worldTransition := physicalTransition
  computationalTransition := physicalComputationalTransition
  transition_commutes := by
    intro s
    funext i
    fin_cases i <;> rfl

/- ========================= Registers =========================== -/

def writeReg (regs : Registers 32) (r : Fin 32) (v : U64) : Registers 32 :=
  Function.update regs r v

theorem writeReg_same (regs : Registers 32) (r : Fin 32) (v : U64) :
    writeReg regs r v r = v := by
  simp [writeReg]

theorem writeReg_other (regs : Registers 32) (r₁ r₂ : Fin 32) (v : U64)
    (h : r₁ ≠ r₂) :
    writeReg regs r₁ v r₂ = regs r₂ := by
  simp [writeReg, Function.update_apply, Ne.symm h]

/- ========================= Instructions ======================== -/

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
  | load  (rd addr : Fin 32)
  | store (addr rs : Fin 32)
  | jmp   (target : Address)
  | beq   (ra rb : Fin 32) (target : Address)
  | bne   (ra rb : Fin 32) (target : Address)
  /-- Advance the World Model by one transition (acts on the registers). -/
  | step
  | halt
deriving Repr

/- ========================= Machine state ======================= -/

structure MachineState where
  regs   : Registers 32
  pc     : Address
  memory : Memory
  halted : Bool

abbrev Program := Address → Instruction

def advance (s : MachineState) : MachineState :=
  { s with pc := s.pc + 1 }

/--
  Architectural semantics. `worldStep` is the World Model hook that the
  `step` instruction applies to the register file.
-/
def execute (worldStep : Registers 32 → Registers 32)
    (inst : Instruction) (s : MachineState) : MachineState :=
  match inst with
  | .add rd ra rb =>
      advance { s with regs := writeReg s.regs rd (s.regs ra + s.regs rb) }
  | .sub rd ra rb =>
      advance { s with regs := writeReg s.regs rd (s.regs ra - s.regs rb) }
  | .mul rd ra rb =>
      advance { s with regs := writeReg s.regs rd (s.regs ra * s.regs rb) }
  | .and rd ra rb =>
      advance { s with regs := writeReg s.regs rd (s.regs ra &&& s.regs rb) }
  | .or rd ra rb =>
      advance { s with regs := writeReg s.regs rd (s.regs ra ||| s.regs rb) }
  | .xor rd ra rb =>
      advance { s with regs := writeReg s.regs rd (s.regs ra ^^^ s.regs rb) }
  | .not rd ra =>
      advance { s with regs := writeReg s.regs rd (~~~ s.regs ra) }
  | .mov rd rs =>
      advance { s with regs := writeReg s.regs rd (s.regs rs) }
  | .li rd imm =>
      advance { s with regs := writeReg s.regs rd imm }
  | .load rd addr =>
      advance { s with regs := writeReg s.regs rd (s.memory (s.regs addr)) }
  | .store addr rs =>
      advance { s with memory := memWrite s.memory (s.regs addr) (s.regs rs) }
  | .jmp target =>
      { s with pc := target }
  | .beq ra rb target =>
      if s.regs ra = s.regs rb then { s with pc := target } else advance s
  | .bne ra rb target =>
      if s.regs ra = s.regs rb then advance s else { s with pc := target }
  | .step =>
      advance { s with regs := worldStep s.regs }
  | .halt =>
      { s with halted := true }

def machineStep (worldStep : Registers 32 → Registers 32)
    (prog : Program) (s : MachineState) : MachineState :=
  if s.halted then s else execute worldStep (prog s.pc) s

def run (worldStep : Registers 32 → Registers 32) (prog : Program) :
    Nat → MachineState → MachineState
  | 0, s => s
  | n + 1, s => run worldStep prog n (machineStep worldStep prog s)

theorem run_add (ws : Registers 32 → Registers 32) (prog : Program)
    (n m : Nat) (s : MachineState) :
    run ws prog (n + m) s = run ws prog n (run ws prog m s) := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih => exact ih _

/- ===================== World Model on the ISA ================== -/

def physicalStepRegs (r : Registers 32) : Registers 32 :=
  writeReg r 0 (r 0 + r 1)

def encodeMachine (s : PhysicalState) (mem : Memory) : MachineState where
  regs := fun r =>
    match r.1 with
    | 0 => s.position
    | 1 => s.velocity
    | 2 => s.energy
    | _ => 0
  pc := 0
  memory := mem
  halted := false

def decodeRegs (r : Registers 32) : PhysicalState :=
  { position := r 0, velocity := r 1, energy := r 2 }

def decodeMachine (m : MachineState) : PhysicalState := decodeRegs m.regs

/-- Loop: `0: step ; 1: jmp 0`. One iteration = one world transition. -/
def worldProgram : Program := fun pc =>
  if pc = 0 then Instruction.step else Instruction.jmp 0

theorem decode_step (r : Registers 32) :
    decodeRegs (physicalStepRegs r) = physicalTransition (decodeRegs r) := by
  simp (config := { decide := true })
    [decodeRegs, physicalStepRegs, writeReg, physicalTransition,
     Function.update_apply]

theorem decode_iterate (n : Nat) :
    ∀ r : Registers 32,
      decodeRegs (physicalStepRegs^[n] r) = physicalTransition^[n] (decodeRegs r) := by
  induction n with
  | zero => intro r; rfl
  | succ n ih =>
    intro r
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        decode_step]

theorem decode_encode (s : PhysicalState) (mem : Memory) :
    decodeMachine (encodeMachine s mem) = s := by
  cases s; rfl

/-- One loop iteration (2 machine cycles) applies the world step to the registers. -/
theorem run_two (m : MachineState) (h0 : m.pc = 0) (hh : m.halted = false) :
    run physicalStepRegs worldProgram 2 m
      = { m with regs := physicalStepRegs m.regs } := by
  rcases m with ⟨regs, pc, mem, halted⟩
  simp only at h0 hh
  subst h0
  subst hh
  simp (config := { decide := true })
    [run, machineStep, execute, advance, worldProgram]

theorem run_loop (n : Nat) :
    ∀ m : MachineState, m.pc = 0 → m.halted = false →
      run physicalStepRegs worldProgram (2 * n) m
        = { m with regs := physicalStepRegs^[n] m.regs } := by
  induction n with
  | zero => intro m _ _; rfl
  | succ n ih =>
    intro m h0 hh
    have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [h2, run_add, run_two m h0 hh, ih _ h0 hh,
        Function.iterate_succ_apply]

/--
  Main correspondence: running the ISA program for `2 * n` cycles simulates
  `n` iterations of the physical world transition, for every `n`.
-/
theorem physical_simulation (s : PhysicalState) (mem : Memory) (n : Nat) :
    decodeMachine
      (run physicalStepRegs worldProgram (2 * n) (encodeMachine s mem))
      = physicalTransition^[n] s := by
  rw [run_loop n _ rfl rfl]
  show decodeRegs (physicalStepRegs^[n] (encodeMachine s mem).regs) = _
  rw [decode_iterate]
  exact congrArg _ (decode_encode s mem)

/- ======================= UHA computational core ================ -/

def UHAUpdate {n : Nat} (active : Fin n → Bool) (f : U64 → U64)
    (s : UHAState n) : UHAState n :=
  fun i => if active i then f (s i) else s i

def UHAFixedPoint {n : Nat} (active : Fin n → Bool) (f : U64 → U64)
    (s : UHAState n) : Prop :=
  UHAUpdate active f s = s

/- ======================= Execution stream ====================== -/

def perpetualRun (x : UHAState 3) : Nat → IO (UHAState 3)
  | 0 => pure x
  | k + 1 => do
      let nextX := physicalComputationalTransition x
      if k % 10000 == 0 then
        IO.println
          s!"[Step {k}] Pos={(nextX 0).toNat}, Vel={(nextX 1).toNat}, Energy={(nextX 2).toNat}"
      perpetualRun nextX k

end WorldModel

open WorldModel

def main : IO Unit := do
  IO.println "=================================================="
  IO.println " FTheoryWorld / UHA-64 Architectural Kernel"
  IO.println " License: Apache 2.0 | Author: Takeo Yamamoto"
  IO.println "=================================================="
  let s0 : PhysicalState := { position := 100, velocity := 5, energy := 500 }
  IO.println s!"Initial: Pos={s0.position.toNat}, Vel={s0.velocity.toNat}, Energy={s0.energy.toNat}"
  let u0 := physicalEncoding.encode s0
  let _ ← perpetualRun u0 100000
  IO.println "Execution stream completed."

