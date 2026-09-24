/-
  License: Apache 2.0   Copyright (c) Takeo Yamamoto

  UHA-64 Computer v2 — ストアドプログラム方式の実行可能な参照計算機

  アーキテクチャ
    * 64 ビット語、32 本の汎用レジスタ、64 ビット PC
    * 命令は固定長 32 ビットで、メモリ上の機械語として置かれる（フェッチ → デコード → 実行）
    * 不正な命令・不整列な PC は fault（fail-closed）
    * STEP 命令 = World Model の遷移（r0 := r0 + r1）を実行するコプロセッサ命令
    * World Model（U64 = ZMod (2^64) 上の物理モデル）との対応を定理として証明

  命令フォーマット（32 ビット）
    R 形式: op[31:26] a[25:21] b[20:16] c[15:11] 0[10:0]
    I 形式: op[31:26] a[25:21] b[20:16] imm16[15:0]
    （上位 32 ビットは予約。デコード時は無視される）

  これは実機 CPU ではなく、アーキテクチャの参照モデルである。
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

namespace UHA64

/-! ## 1. 基本型 -/

abbrev Word := UInt64
abbrev Reg := Fin 32
abbrev Address := UInt64
/-- 16 ビット即値。 -/
abbrev Imm := Fin 65536

/-! ## 2. メモリ（読み書きの法則を持つ関数メモリ）

  旧版の `Memory` は `write : ... → Memory` を持つ再帰的な構造体で、
  基底がなく、`read` と `write` の関係も未規定だった。ここでは番地 → 語の関数として
  定義し、read-over-write の法則を定理にする。 -/

structure Memory where
  cell : Address → Word

namespace Memory

def empty : Memory := ⟨fun _ => 0⟩

def read (m : Memory) (a : Address) : Word := m.cell a

def write (m : Memory) (a : Address) (v : Word) : Memory :=
  ⟨fun x => if x = a then v else m.cell x⟩

theorem read_write_same (m : Memory) (a : Address) (v : Word) :
    (m.write a v).read a = v := by
  simp [Memory.read, Memory.write]

theorem read_write_other (m : Memory) {a b : Address} (v : Word) (h : b ≠ a) :
    (m.write a v).read b = m.read b := by
  simp [Memory.read, Memory.write, h]

theorem read_empty (a : Address) : Memory.empty.read a = 0 := rfl

end Memory

/-! ## 3. 命令セットと 32 ビット符号化 -/

inductive Instruction
  | add   (rd ra rb : Reg)
  | sub   (rd ra rb : Reg)
  | mul   (rd ra rb : Reg)
  | and   (rd ra rb : Reg)
  | or    (rd ra rb : Reg)
  | xor   (rd ra rb : Reg)
  | not   (rd ra : Reg)
  | mov   (rd rs : Reg)
  | li    (rd : Reg) (imm : Imm)
  | load  (rd addr : Reg)
  | store (addr rs : Reg)
  | jmp   (target : Imm)
  | beq   (ra rb : Reg) (target : Imm)
  | bne   (ra rb : Reg) (target : Imm)
  | step
  | halt
deriving Repr, DecidableEq

/-- R 形式のパック。 -/
def packR (op : Nat) (a b c : Reg) : Nat :=
  op * 67108864 + a.1 * 2097152 + b.1 * 65536 + c.1 * 2048

/-- I 形式のパック。 -/
def packI (op : Nat) (a b : Reg) (imm : Imm) : Nat :=
  op * 67108864 + a.1 * 2097152 + b.1 * 65536 + imm.1

def opOf (w : Nat) : Nat := w / 67108864 % 64
def aOf (w : Nat) : Nat := w / 2097152 % 32
def bOf (w : Nat) : Nat := w / 65536 % 32
def cOf (w : Nat) : Nat := w / 2048 % 32
def immOf (w : Nat) : Nat := w % 65536

theorem opOf_packR {op : Nat} (h : op < 64) (a b c : Reg) : opOf (packR op a b c) = op := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  unfold opOf packR
  omega

theorem aOf_packR (op : Nat) (a b c : Reg) : aOf (packR op a b c) = a.1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  unfold aOf packR
  omega

theorem bOf_packR (op : Nat) (a b c : Reg) : bOf (packR op a b c) = b.1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  unfold bOf packR
  omega

theorem cOf_packR (op : Nat) (a b c : Reg) : cOf (packR op a b c) = c.1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  unfold cOf packR
  omega

theorem opOf_packI {op : Nat} (h : op < 64) (a b : Reg) (imm : Imm) :
    opOf (packI op a b imm) = op := by
  have ha := a.isLt
  have hb := b.isLt
  have hi := imm.isLt
  unfold opOf packI
  omega

theorem aOf_packI (op : Nat) (a b : Reg) (imm : Imm) : aOf (packI op a b imm) = a.1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hi := imm.isLt
  unfold aOf packI
  omega

theorem bOf_packI (op : Nat) (a b : Reg) (imm : Imm) : bOf (packI op a b imm) = b.1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hi := imm.isLt
  unfold bOf packI
  omega

theorem immOf_packI (op : Nat) (a b : Reg) (imm : Imm) : immOf (packI op a b imm) = imm.1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hi := imm.isLt
  unfold immOf packI
  omega

theorem packR_lt {op : Nat} (h : op < 64) (a b c : Reg) : packR op a b c < 4294967296 := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  unfold packR
  omega

theorem packI_lt {op : Nat} (h : op < 64) (a b : Reg) (imm : Imm) :
    packI op a b imm < 4294967296 := by
  have ha := a.isLt
  have hb := b.isLt
  have hi := imm.isLt
  unfold packI
  omega

def Reg.ofNat (n : Nat) : Reg := ⟨n % 32, Nat.mod_lt _ (by decide)⟩
def Imm.ofNat (n : Nat) : Imm := ⟨n % 65536, Nat.mod_lt _ (by decide)⟩

theorem Reg.ofNat_val (r : Reg) : Reg.ofNat r.1 = r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
theorem Imm.ofNat_val (i : Imm) : Imm.ofNat i.1 = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- 機械語への符号化。 -/
def Instruction.encode : Instruction → Nat
  | .add rd ra rb => packR 0 rd ra rb
  | .sub rd ra rb => packR 1 rd ra rb
  | .mul rd ra rb => packR 2 rd ra rb
  | .and rd ra rb => packR 3 rd ra rb
  | .or rd ra rb => packR 4 rd ra rb
  | .xor rd ra rb => packR 5 rd ra rb
  | .not rd ra => packR 6 rd ra 0
  | .mov rd rs => packR 7 rd rs 0
  | .li rd imm => packI 8 rd 0 imm
  | .load rd addr => packR 9 rd addr 0
  | .store addr rs => packR 10 addr rs 0
  | .jmp target => packI 11 0 0 target
  | .beq ra rb target => packI 12 ra rb target
  | .bne ra rb target => packI 13 ra rb target
  | .step => packR 14 0 0 0
  | .halt => packR 15 0 0 0

/-- 機械語のデコード。未定義の opcode は `none`（不正命令）。 -/
def decode (w : Nat) : Option Instruction :=
  match opOf w with
  | 0 => some (.add (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Reg.ofNat (cOf w)))
  | 1 => some (.sub (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Reg.ofNat (cOf w)))
  | 2 => some (.mul (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Reg.ofNat (cOf w)))
  | 3 => some (.and (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Reg.ofNat (cOf w)))
  | 4 => some (.or (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Reg.ofNat (cOf w)))
  | 5 => some (.xor (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Reg.ofNat (cOf w)))
  | 6 => some (.not (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)))
  | 7 => some (.mov (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)))
  | 8 => some (.li (Reg.ofNat (aOf w)) (Imm.ofNat (immOf w)))
  | 9 => some (.load (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)))
  | 10 => some (.store (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)))
  | 11 => some (.jmp (Imm.ofNat (immOf w)))
  | 12 => some (.beq (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Imm.ofNat (immOf w)))
  | 13 => some (.bne (Reg.ofNat (aOf w)) (Reg.ofNat (bOf w)) (Imm.ofNat (immOf w)))
  | 14 => some .step
  | 15 => some .halt
  | _ => none

/-- ISA の要：符号化してデコードすると元の命令に戻る。 -/
theorem decode_encode (i : Instruction) : decode i.encode = some i := by
  cases i <;>
    simp [Instruction.encode, decode, opOf_packR, aOf_packR, bOf_packR, cOf_packR,
      opOf_packI, aOf_packI, bOf_packI, immOf_packI, Reg.ofNat_val, Imm.ofNat_val]

/-- 符号化は単射（同じ機械語を持つ異なる命令は存在しない）。 -/
theorem Instruction.encode_injective : Function.Injective Instruction.encode := by
  intro i j h
  have hi := decode_encode i
  rw [h, decode_encode j] at hi
  exact (Option.some.inj hi).symm

/-- 機械語は 32 ビットに収まる。 -/
theorem Instruction.encode_lt (i : Instruction) : i.encode < 4294967296 := by
  cases i <;> simp only [Instruction.encode] <;>
    first
    | exact packR_lt (by decide) _ _ _
    | exact packI_lt (by decide) _ _ _

theorem Instruction.encode_lt64 (i : Instruction) : i.encode < 2 ^ 64 :=
  Nat.lt_trans (Instruction.encode_lt i) (by norm_num)

/-! ## 4. レジスタ・マシン状態 -/

abbrev Registers := Reg → Word

def Registers.zero : Registers := fun _ => 0

def writeReg (r : Registers) (rd : Reg) (v : Word) : Registers :=
  fun i => if i = rd then v else r i

theorem writeReg_same (r : Registers) (rd : Reg) (v : Word) : writeReg r rd v rd = v := by
  unfold writeReg
  exact if_pos rfl

theorem writeReg_other (r : Registers) {rd i : Reg} (v : Word) (h : i ≠ rd) :
    writeReg r rd v i = r i := by
  unfold writeReg
  exact if_neg h

/-- World Model コプロセッサ：位置 r0 に速度 r1 を加える（`physicalTransition` に対応）。 -/
def worldCoreRegs (r : Registers) : Registers := writeReg r 0 (r 0 + r 1)

theorem reg1_ne_reg0 : (1 : Reg) ≠ 0 := by decide
theorem reg2_ne_reg0 : (2 : Reg) ≠ 0 := by decide

theorem worldCoreRegs_0 (r : Registers) : worldCoreRegs r 0 = r 0 + r 1 := by
  unfold worldCoreRegs
  exact writeReg_same r 0 (r 0 + r 1)

theorem worldCoreRegs_1 (r : Registers) : worldCoreRegs r 1 = r 1 := by
  unfold worldCoreRegs
  exact writeReg_other r (r 0 + r 1) reg1_ne_reg0

theorem worldCoreRegs_2 (r : Registers) : worldCoreRegs r 2 = r 2 := by
  unfold worldCoreRegs
  exact writeReg_other r (r 0 + r 1) reg2_ne_reg0

/-- 実行状態。`fault` は不正命令・不整列 PC で入る吸収状態。 -/
inductive Status
  | running
  | halted
  | fault
deriving DecidableEq, Repr

structure Machine where
  regs : Registers
  pc : Address
  memory : Memory
  status : Status

def initialMachine (mem : Memory) : Machine :=
  { regs := Registers.zero, pc := 0, memory := mem, status := .running }

def nextPC (pc : Address) : Address := pc + 4

/-! ## 5. 実行・フェッチ・ステップ -/

def execute (inst : Instruction) (m : Machine) : Machine :=
  match inst with
  | .add rd ra rb =>
      { m with regs := writeReg m.regs rd (m.regs ra + m.regs rb), pc := nextPC m.pc }
  | .sub rd ra rb =>
      { m with regs := writeReg m.regs rd (m.regs ra - m.regs rb), pc := nextPC m.pc }
  | .mul rd ra rb =>
      { m with regs := writeReg m.regs rd (m.regs ra * m.regs rb), pc := nextPC m.pc }
  | .and rd ra rb =>
      { m with regs := writeReg m.regs rd (m.regs ra &&& m.regs rb), pc := nextPC m.pc }
  | .or rd ra rb =>
      { m with regs := writeReg m.regs rd (m.regs ra ||| m.regs rb), pc := nextPC m.pc }
  | .xor rd ra rb =>
      { m with regs := writeReg m.regs rd (m.regs ra ^^^ m.regs rb), pc := nextPC m.pc }
  | .not rd ra =>
      { m with regs := writeReg m.regs rd (~~~ m.regs ra), pc := nextPC m.pc }
  | .mov rd rs =>
      { m with regs := writeReg m.regs rd (m.regs rs), pc := nextPC m.pc }
  | .li rd imm =>
      { m with regs := writeReg m.regs rd (UInt64.ofNat imm.1), pc := nextPC m.pc }
  | .load rd addr =>
      { m with regs := writeReg m.regs rd (m.memory.read (m.regs addr)), pc := nextPC m.pc }
  | .store addr rs =>
      { m with memory := m.memory.write (m.regs addr) (m.regs rs), pc := nextPC m.pc }
  | .jmp target =>
      { m with pc := UInt64.ofNat target.1 }
  | .beq ra rb target =>
      if m.regs ra = m.regs rb then
        { m with pc := UInt64.ofNat target.1 }
      else
        { m with pc := nextPC m.pc }
  | .bne ra rb target =>
      if m.regs ra ≠ m.regs rb then
        { m with pc := UInt64.ofNat target.1 }
      else
        { m with pc := nextPC m.pc }
  | .step =>
      { m with regs := worldCoreRegs m.regs, pc := nextPC m.pc }
  | .halt =>
      { m with status := .halted }

/-- 命令フェッチ：4 バイト整列した PC の語をデコードする。 -/
def fetchAt (mem : Memory) (pc : Address) : Option Instruction :=
  if pc.toNat % 4 = 0 then decode (mem.read pc).toNat else none

/-- 1 ステップ。running 以外は不動。不正命令は fault（fail-closed）。 -/
def machineStep (m : Machine) : Machine :=
  match m.status with
  | .running =>
      match fetchAt m.memory m.pc with
      | some inst => execute inst m
      | none => { m with status := .fault }
  | .halted => m
  | .fault => m

/-- 有限ステップ実行。 -/
def run : Nat → Machine → Machine
  | 0, m => m
  | n + 1, m => run n (machineStep m)

/-! ## 6. 実行の基本定理 -/

theorem machineStep_of_halted {m : Machine} (h : m.status = .halted) : machineStep m = m := by
  simp [machineStep, h]

theorem machineStep_of_fault {m : Machine} (h : m.status = .fault) : machineStep m = m := by
  simp [machineStep, h]

theorem machineStep_of_fetch {m : Machine} {inst : Instruction} (hr : m.status = .running)
    (hf : fetchAt m.memory m.pc = some inst) : machineStep m = execute inst m := by
  simp [machineStep, hr, hf]

/-- 不正命令・不整列 PC は必ず fault になる。 -/
theorem machineStep_illegal {m : Machine} (hr : m.status = .running)
    (hf : fetchAt m.memory m.pc = none) : (machineStep m).status = .fault := by
  simp [machineStep, hr, hf]

/-- 実行は加法的：`n + k` ステップ = `n` ステップの後に `k` ステップ。 -/
theorem run_add (n k : Nat) : ∀ m : Machine, run (n + k) m = run k (run n m) := by
  induction n with
  | zero =>
    intro m
    simp [run]
  | succ n ih =>
    intro m
    have h : n + 1 + k = (n + k) + 1 := by omega
    rw [h]
    show run (n + k) (machineStep m) = run k (run n (machineStep m))
    exact ih (machineStep m)

/-- 停止したマシンは以後変わらない。 -/
theorem run_of_halted (n : Nat) : ∀ m : Machine, m.status = .halted → run n m = m := by
  induction n with
  | zero =>
    intro m _
    rfl
  | succ n ih =>
    intro m h
    have h1 : machineStep m = m := machineStep_of_halted h
    show run n (machineStep m) = m
    rw [h1]
    exact ih m h

/-- fault も吸収状態。 -/
theorem run_of_fault (n : Nat) : ∀ m : Machine, m.status = .fault → run n m = m := by
  induction n with
  | zero =>
    intro m _
    rfl
  | succ n ih =>
    intro m h
    have h1 : machineStep m = m := machineStep_of_fault h
    show run n (machineStep m) = m
    rw [h1]
    exact ih m h

/-! ### 命令の意味論 -/

theorem execute_add_rd (rd ra rb : Reg) (m : Machine) :
    (execute (.add rd ra rb) m).regs rd = m.regs ra + m.regs rb := by
  simp [execute, writeReg_same]

theorem execute_add_pc (rd ra rb : Reg) (m : Machine) :
    (execute (.add rd ra rb) m).pc = nextPC m.pc := by
  simp [execute]

theorem execute_halt_status (m : Machine) : (execute .halt m).status = .halted := by
  simp [execute]

theorem execute_step_regs (m : Machine) : (execute .step m).regs = worldCoreRegs m.regs := rfl

/-- store した値は、同じアドレスから load すれば読み出せる。 -/
theorem execute_load_after_store (rd a rs : Reg) (m : Machine) :
    (execute (.load rd a) (execute (.store a rs) m)).regs rd = m.regs rs := by
  simp [execute, writeReg_same, Memory.read_write_same]

/-! ## 7. ローダ／アセンブラの正しさ -/

def loadWords (mem : Memory) (base : Address) : List Nat → Memory
  | [] => mem
  | w :: ws => loadWords (mem.write base (UInt64.ofNat w)) (base + 4) ws

/-- 命令列を 4 バイト間隔で機械語としてメモリに配置する。 -/
def assemble (prog : List Instruction) : Memory :=
  loadWords Memory.empty 0 (prog.map Instruction.encode)

def boot (prog : List Instruction) : Machine := initialMachine (assemble prog)

theorem word_toNat_ofNat_lt (n : Nat) (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  first
    | (rw [UInt64.toNat_ofNat]; exact Nat.mod_eq_of_lt h)
    | (simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt h])
    | exact UInt64.toNat_ofNat_of_lt h
    | (simp [UInt64.toNat_ofNat, UInt64.size]; omega)

/-- 整列したアドレスに命令 `i` の機械語を書けば、フェッチで `i` が得られる。 -/
theorem fetchAt_write_encode (mem : Memory) (pc : Address) (i : Instruction)
    (hpc : pc.toNat % 4 = 0) :
    fetchAt (mem.write pc (UInt64.ofNat i.encode)) pc = some i := by
  unfold fetchAt
  rw [if_pos hpc, Memory.read_write_same, word_toNat_ofNat_lt _ (Instruction.encode_lt64 i)]
  exact decode_encode i

/-! ## 8. World Model との対応（U64 = ZMod (2^64) ↔ 64 ビット語） -/

abbrev U64 := ZMod (2 ^ 64)

def wordToU64 (w : Word) : U64 := (w.toNat : U64)
def u64ToWord (z : U64) : Word := UInt64.ofNat z.val

theorem wordToU64_add (a b : Word) : wordToU64 (a + b) = wordToU64 a + wordToU64 b := by
  unfold wordToU64
  rw [UInt64.toNat_add]
  first
    | (rw [ZMod.natCast_mod, Nat.cast_add])
    | (simp [ZMod.natCast_mod, Nat.cast_add])
    | (simp [UInt64.size, ZMod.natCast_mod, Nat.cast_add])

theorem wordToU64_mul (a b : Word) : wordToU64 (a * b) = wordToU64 a * wordToU64 b := by
  unfold wordToU64
  rw [UInt64.toNat_mul]
  first
    | (rw [ZMod.natCast_mod, Nat.cast_mul])
    | (simp [ZMod.natCast_mod, Nat.cast_mul])
    | (simp [UInt64.size, ZMod.natCast_mod, Nat.cast_mul])

theorem wordToU64_u64ToWord (z : U64) : wordToU64 (u64ToWord z) = z := by
  haveI : NeZero ((2 : ℕ) ^ 64) := ⟨by norm_num⟩
  have h : z.val < 2 ^ 64 := ZMod.val_lt z
  unfold wordToU64 u64ToWord
  rw [word_toNat_ofNat_lt _ h]
  first
    | exact ZMod.natCast_zmod_val z
    | simp

@[ext] structure PhysicalState where
  position : U64
  velocity : U64
  energy : U64

def physicalTransition (s : PhysicalState) : PhysicalState :=
  { position := s.position + s.velocity, velocity := s.velocity, energy := s.energy }

/-- 物理状態を r0, r1, r2 に載せる。 -/
def encodePhysical (s : PhysicalState) : Registers :=
  fun r =>
    match r.1 with
    | 0 => u64ToWord s.position
    | 1 => u64ToWord s.velocity
    | 2 => u64ToWord s.energy
    | _ => 0

/-- レジスタから物理状態を読み出す。 -/
def decodePhysical (r : Registers) : PhysicalState :=
  { position := wordToU64 (r 0), velocity := wordToU64 (r 1), energy := wordToU64 (r 2) }

theorem encodePhysical_0 (s : PhysicalState) : encodePhysical s 0 = u64ToWord s.position := rfl
theorem encodePhysical_1 (s : PhysicalState) : encodePhysical s 1 = u64ToWord s.velocity := rfl
theorem encodePhysical_2 (s : PhysicalState) : encodePhysical s 2 = u64ToWord s.energy := rfl

theorem decode_encodePhysical (s : PhysicalState) : decodePhysical (encodePhysical s) = s := by
  ext <;>
    simp [decodePhysical, encodePhysical_0, encodePhysical_1, encodePhysical_2,
      wordToU64_u64ToWord]

/-- World Model コプロセッサは物理遷移を実装する：
    decode ∘ worldCore ∘ encode = physicalTransition。 -/
theorem worldCore_implements (s : PhysicalState) :
    decodePhysical (worldCoreRegs (encodePhysical s)) = physicalTransition s := by
  ext
  · simp [decodePhysical, physicalTransition, worldCoreRegs_0, encodePhysical_0,
      encodePhysical_1, wordToU64_add, wordToU64_u64ToWord]
  · simp [decodePhysical, physicalTransition, worldCoreRegs_1, encodePhysical_1,
      wordToU64_u64ToWord]
  · simp [decodePhysical, physicalTransition, worldCoreRegs_2, encodePhysical_2,
      wordToU64_u64ToWord]

/-- 機械語レベルの対応：running のマシンが STEP をフェッチしたとき、
    1 ステップ後のレジスタは物理遷移後の状態に対応する。 -/
theorem machineStep_step_implements {m : Machine} {s : PhysicalState}
    (hr : m.status = .running) (hf : fetchAt m.memory m.pc = some .step)
    (hregs : m.regs = encodePhysical s) :
    decodePhysical (machineStep m).regs = physicalTransition s := by
  have h : machineStep m = execute .step m := machineStep_of_fetch hr hf
  rw [h]
  show decodePhysical (worldCoreRegs m.regs) = physicalTransition s
  rw [hregs]
  exact worldCore_implements s

/-! ## 9. 例とテスト -/

/-- r0 = 10, r1 = 5, r2 = r0 + r1, r3 = r2 * r1, HALT -/
def exampleProgram : List Instruction :=
  [.li 0 10, .li 1 5, .add 2 0 1, .mul 3 2 1, .halt]

/-- 位置 100、速度 5 の世界を 1 ステップ進める。 -/
def worldProgram : List Instruction :=
  [.li 0 100, .li 1 5, .step, .halt]

set_option maxRecDepth 100000 in
theorem exampleProgram_r3 : (run 5 (boot exampleProgram)).regs 3 = 75 := by
  first | decide | rfl

set_option maxRecDepth 100000 in
theorem exampleProgram_halts : (run 5 (boot exampleProgram)).status = .halted := by
  first | decide | rfl

set_option maxRecDepth 100000 in
theorem worldProgram_r0 : (run 4 (boot worldProgram)).regs 0 = 105 := by
  first | decide | rfl

/-- opcode 63 は未定義：不正命令として fault になる。 -/
set_option maxRecDepth 100000 in
theorem illegal_opcode_faults :
    (machineStep (initialMachine (Memory.empty.write 0 (UInt64.ofNat 4227858432)))).status
      = .fault := by
  first | decide | rfl

/-! ## 10. 表示と main -/

def hex (n : Nat) : String := String.mk (Nat.toDigits 16 n)

def showMachine (m : Machine) : IO Unit := do
  IO.println "--------------------------------------------"
  IO.println s!"PC     = {m.pc}"
  IO.println s!"R0     = {m.regs 0}"
  IO.println s!"R1     = {m.regs 1}"
  IO.println s!"R2     = {m.regs 2}"
  IO.println s!"R3     = {m.regs 3}"
  IO.println s!"STATUS = {repr m.status}"
  IO.println "--------------------------------------------"

def main : IO Unit := do
  IO.println "================================================"
  IO.println " UHA-64 COMPUTER v2"
  IO.println " stored-program / 32-bit fixed-width ISA"
  IO.println " World Model coprocessor (STEP)"
  IO.println " Author: Takeo Yamamoto   License: Apache-2.0"
  IO.println "================================================"
  IO.println ""
  IO.println "Machine code:"
  for i in exampleProgram do
    IO.println s!"  0x{hex i.encode}    {repr i}"
  IO.println ""
  IO.println "Running arithmetic program..."
  showMachine (run 5 (boot exampleProgram))
  IO.println ""
  IO.println "Running World Model program (position 100, velocity 5)..."
  showMachine (run 4 (boot worldProgram))
  IO.println ""
  IO.println "Executing an illegal instruction (opcode 63)..."
  let bad := initialMachine (Memory.empty.write 0 (UInt64.ofNat 4227858432))
  showMachine (run 1 bad)
  IO.println ""
  IO.println "UHA-64 COMPUTER: OK"

end UHA64
