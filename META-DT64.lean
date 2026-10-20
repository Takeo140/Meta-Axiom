License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

namespace MetaAxioms.DT64

/-!
# Meta-Axioms — 64-bit Digital Twin
- ℝ を Q32.32 固定小数点（BitVec 64・符号付き）`Q64` に置換
- 位相空間 X を有限格子 `Fin n` ＋ 隣接関係に置換
  （A2 の連続性 → 隣接セル間の変化量が ε 以下という離散連続性）
- A1・A2・A4 の条件を決定可能にして #eval で検証可能にする
- A3 の falsifiable は ∃ を含むため Prop のまま（証明側）
-/

/-! ## 64-bit 数値型 (Q32.32) -/

structure Q64 where
  raw : BitVec 64
  deriving DecidableEq, Repr

namespace Q64

def fracBits : Nat := 32
def toInt (a : Q64) : Int := a.raw.toInt
def ofInt (z : Int) : Q64 := ⟨BitVec.ofInt 64 z⟩
def ofNat' (k : Nat) : Q64 := ofInt ((k : Int) * 2 ^ fracBits)

def zero : Q64 := ⟨0⟩
def one : Q64 := ofNat' 1

instance : LE Q64 := ⟨fun a b => a.toInt ≤ b.toInt⟩
instance : LT Q64 := ⟨fun a b => a.toInt < b.toInt⟩
instance (a b : Q64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toInt ≤ b.toInt))
instance (a b : Q64) : Decidable (a < b) := inferInstanceAs (Decidable (a.toInt < b.toInt))

instance : Add Q64 := ⟨fun a b => ⟨a.raw + b.raw⟩⟩   -- 64bit ラップ
instance : Mul Q64 := ⟨fun a b => ofInt ((a.toInt * b.toInt) / 2 ^ fracBits)⟩

end Q64

/-! ## A1: 極値原理（有限格子上の大域最小：厳密） -/

def IsMinimal {n : Nat} (L : Fin n → Q64) (x₀ : Fin n) : Prop :=
  ∀ x, L x₀ ≤ L x

instance {n : Nat} (L : Fin n → Q64) (x₀ : Fin n) : Decidable (IsMinimal L x₀) := by
  unfold IsMinimal; infer_instance

/-! ## A2: 位相構造 → 離散連続性（隣接セル間の変化量 ≤ ε） -/

def DiscreteContinuous {n : Nat} (L : Fin n → Q64)
    (adj : Fin n → Fin n → Bool) (ε : Q64) : Prop :=
  ∀ x y, adj x y = true → L x ≤ L y + ε ∧ L y ≤ L x + ε

instance {n : Nat} (L : Fin n → Q64) (adj : Fin n → Fin n → Bool) (ε : Q64) :
    Decidable (DiscreteContinuous L adj ε) := by
  unfold DiscreteContinuous; infer_instance

structure TopologicalMinimum (n : Nat) where
  L    : Fin n → Q64
  x₀   : Fin n
  adj  : Fin n → Fin n → Bool
  ε    : Q64
  hL   : DiscreteContinuous L adj ε   -- A2
  hMin : IsMinimal L x₀               -- A1 ∧ A2

/-! ## A3: 論理的整合性（C は Bool 値の判定器） -/

structure IsConsistent {n : Nat}
    (C : (Fin n → Q64) → Bool) (F : Fin n → Q64) : Prop where
  holds       : C F = true
  falsifiable : ∃ G : Fin n → Q64, C G = false

/-! ## A4: 階層構造（凸結合：重み非負・総和 1） -/

def sumQ {m : Nat} (f : Fin m → Q64) : Q64 :=
  (List.finRange m).foldl (fun acc i => acc + f i) Q64.zero

structure HierarchicalMacro (n m : Nat) where
  w       : Fin m → Q64
  Fmicro  : Fin m → Fin n → Q64
  hNonNeg : ∀ i, Q64.zero ≤ w i
  hSum    : sumQ w = Q64.one

def MacroFunction {n m : Nat} (H : HierarchicalMacro n m) : Fin n → Q64 :=
  fun x => sumQ (fun i => H.w i * H.Fmicro i x)

/-! ## 統合フレームワーク -/

structure IntegratedFramework (n m : Nat) where
  tm : TopologicalMinimum n                       -- A1 + A2
  C  : (Fin n → Q64) → Bool                       -- A3
  F  : Fin n → Q64
  hC : IsConsistent C F
  H  : HierarchicalMacro n m                      -- A4

/-! ## 実現 -/

def IsRealization {n m : Nat} (M : IntegratedFramework n m) (x₀ : Fin n) : Prop :=
  M.tm.x₀ = x₀

lemma realization_is_minimal {n m : Nat} (M : IntegratedFramework n m)
    (x₀ : Fin n) (hR : IsRealization M x₀) :
    IsMinimal M.tm.L x₀ := by
  subst hR
  exact M.tm.hMin

/-! ## 実行時チェック
    ラップアラウンドのため `macro_nonneg`（ℝ 版）は一般には成り立たない。
    代わりに、与えたデータに対して決定可能な検査として提供する。 -/

def MicroNonneg {n m : Nat} (H : HierarchicalMacro n m) : Prop :=
  ∀ i x, Q64.zero ≤ H.Fmicro i x

instance {n m : Nat} (H : HierarchicalMacro n m) : Decidable (MicroNonneg H) := by
  unfold MicroNonneg; infer_instance

/-! ## 実行例 -/

def sampleL : Fin 3 → Q64 := fun i => Q64.ofNat' i.val

def lineAdj : Fin 3 → Fin 3 → Bool :=
  fun x y => (x.val + 1 == y.val) || (y.val + 1 == x.val)

#eval decide (IsMinimal sampleL 0)                              -- true
#eval decide (IsMinimal sampleL 2)                              -- false
#eval decide (DiscreteContinuous sampleL lineAdj Q64.one)       -- true
#eval (sumQ (fun _ : Fin 2 => Q64.ofInt (2 ^ 31))).toInt        -- 2^32 = 1.0 (Q32.32)

end MetaAxioms.DT64
