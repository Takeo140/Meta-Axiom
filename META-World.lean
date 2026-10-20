License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

namespace MetaAxioms.WM

/-!
# Meta-Axioms — 64-bit 世界モデル版
元の A1〜A4（IsMinimal / TopologicalMinimum / IsConsistent / HierarchicalMacro /
IntegratedFramework / IsRealization）を保ち、遷移則を追加する。

世界モデルの読み方
- 状態   : 格子上の位置 x : Fin n（空間 X の点）
- 地形   : マクロ関数 G = MacroFunction H（A4：ミクロ地形の凸結合）
- 遷移   : 隣接セル（A2：局所性）のうち G が最小のセルへ移る（A1：極値へ向かう）
- ゲート : G が整合性 C（A3）と離散連続性（A2）を満たすときだけ遷移を許可
- 実現   : 十分なステップ後に tm.x₀ に到達するか（IsRealization）を検査
注意：局所降下なので、G が単峰でなければ大域最小には届かない。
      それを `reachesGlobalMin` で検査できるようにしてある。
-/

/-! ## Q32.32 固定小数点 -/

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
instance : Sub Q64 := ⟨fun a b => ⟨a.raw - b.raw⟩⟩
instance : Mul Q64 := ⟨fun a b => ofInt ((a.toInt * b.toInt) / 2 ^ fracBits)⟩
end Q64

/-! ## A1 / A2 -/

def IsMinimal {n : Nat} (L : Fin n → Q64) (x₀ : Fin n) : Prop :=
  ∀ x, L x₀ ≤ L x

instance {n : Nat} (L : Fin n → Q64) (x₀ : Fin n) : Decidable (IsMinimal L x₀) := by
  unfold IsMinimal; infer_instance

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
  hL   : DiscreteContinuous L adj ε
  hMin : IsMinimal L x₀

/-! ## A3 -/

structure IsConsistent {n : Nat}
    (C : (Fin n → Q64) → Bool) (F : Fin n → Q64) : Prop where
  holds       : C F = true
  falsifiable : ∃ G : Fin n → Q64, C G = false

/-! ## A4 -/

def sumQ {m : Nat} (f : Fin m → Q64) : Q64 :=
  (List.finRange m).foldl (fun acc i => acc + f i) Q64.zero

structure HierarchicalMacro (n m : Nat) where
  w       : Fin m → Q64
  Fmicro  : Fin m → Fin n → Q64
  hNonNeg : ∀ i, Q64.zero ≤ w i
  hSum    : sumQ w = Q64.one

/-- 生データ版のマクロ関数（例の実行に証明を要求しないため） -/
def macroOf {n m : Nat} (w : Fin m → Q64) (Fmicro : Fin m → Fin n → Q64) : Fin n → Q64 :=
  fun x => sumQ (fun i => w i * Fmicro i x)

def MacroFunction {n m : Nat} (H : HierarchicalMacro n m) : Fin n → Q64 :=
  macroOf H.w H.Fmicro

structure IntegratedFramework (n m : Nat) where
  tm : TopologicalMinimum n
  C  : (Fin n → Q64) → Bool
  F  : Fin n → Q64
  hC : IsConsistent C F
  H  : HierarchicalMacro n m

def IsRealization {n m : Nat} (M : IntegratedFramework n m) (x₀ : Fin n) : Prop :=
  M.tm.x₀ = x₀

lemma realization_is_minimal {n m : Nat} (M : IntegratedFramework n m)
    (x₀ : Fin n) (hR : IsRealization M x₀) :
    IsMinimal M.tm.L x₀ := by
  subst hR
  exact M.tm.hMin

/-! ## 世界モデル：遷移則の追加 -/

section Dynamics
variable {n m : Nat}

/-- 局所降下：隣接セルのうち、現在より厳密に低い最小の地形値へ移る -/
def descendStep (adj : Fin n → Fin n → Bool) (G : Fin n → Q64) (x : Fin n) : Fin n :=
  (List.finRange n).foldl
    (fun best y => if adj x y && decide (G y < G best) then y else best) x

def rolloutOn (f : Fin n → Fin n) (x : Fin n) : Nat → Fin n
  | 0     => x
  | k + 1 => rolloutOn f (f x) k

/-- ゲート：A3 の整合性 C と A2 の離散連続性が G で成り立つ -/
def gate (M : IntegratedFramework n m) : Bool :=
  M.C (MacroFunction M.H) &&
    decide (DiscreteContinuous (MacroFunction M.H) M.tm.adj M.tm.ε)

/-- フレームワーク版の 1 ステップ予測（ゲートが閉じていれば据え置き） -/
def step (M : IntegratedFramework n m) (x : Fin n) : Fin n :=
  if gate M then descendStep M.tm.adj (MacroFunction M.H) x else x

def rollout (M : IntegratedFramework n m) (x : Fin n) (k : Nat) : Fin n :=
  rolloutOn (step M) x k

/-- 実現の実行時検査：k ステップ後に tm.x₀ へ到達するか -/
def realizesB (M : IntegratedFramework n m) (x : Fin n) (k : Nat) : Bool :=
  decide (rollout M x k = M.tm.x₀)

/-- 生データ版：k ステップ後の位置が G の大域最小か -/
def reachesGlobalMin (adj : Fin n → Fin n → Bool) (G : Fin n → Q64)
    (x : Fin n) (k : Nat) : Bool :=
  decide (IsMinimal G (rolloutOn (descendStep adj G) x k))

end Dynamics

/-! ## 実行例（n = 5 の直線格子、ミクロ地形 2 層） -/

def lineAdj : Fin 5 → Fin 5 → Bool :=
  fun x y => (x.val + 1 == y.val) || (y.val + 1 == x.val)

def sq (a b : Nat) : Nat := (if a ≥ b then a - b else b - a) ^ 2

def F2 : Fin 2 → Fin 5 → Q64 :=      -- 最小点：層 0 は 2、層 1 は 3
  fun i x => Q64.ofNat' (sq x.val (if i.val == 0 then 2 else 3))

def W2 : Fin 2 → Q64 :=              -- 重み 3/4, 1/4（総和 = 1）
  fun i => if i.val == 0 then Q64.ofInt (3 * 2 ^ 30) else Q64.ofInt (2 ^ 30)

def G5 : Fin 5 → Q64 := macroOf W2 F2
-- G = [5.25, 1.75, 0.25, 0.75, 3.25]（最小は x = 2）

#eval decide (sumQ W2 = Q64.one)                                      -- true
#eval decide (DiscreteContinuous G5 lineAdj (Q64.ofNat' 4))           -- true
#eval (rolloutOn (descendStep lineAdj G5) 0 4).val                    -- 2
#eval reachesGlobalMin lineAdj G5 0 4                                 -- true
#eval reachesGlobalMin lineAdj G5 4 4                                 -- true

end MetaAxioms.WM
