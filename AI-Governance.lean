License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

namespace AIGovernance.WM

/-!
# AI Governance & Compliance Framework — 64-bit ガバナンス世界モデル（完全版）

位置づけ：実稼働AIシステム（Obverse：行動・メトリクス）と ガバナンス規範（Reverse：規律・ポリシー）のデジタルツイン。
  AIシステムの実挙動が統治法則（Law）を満たすこと（Consistent）が安全な運用・同期条件。
  連続値モデルとの近似誤差は未評価（構造を保った離散固定小数点版）。

元の数理構造（Obverse / Reverse / Psi / Extremal / Consistent / FTheoryModel /
internal_coherence）を完全に保持し、AIガバナンス・ガードレール制御に必要な要素を実装。

| ガバナンス要素 | 実装・解釈 |
|---|---|
| 状態         | `World n` = `Psi n`（リスク密度 ρ, 制御圧力 p, 法則 Law）＋ 状態変化モーメンタム `m` |
| 動力学       | 監査・推論プロセスにおけるリスク伝播・制御系 ρ_t = -m_x, m_t = -p_x, p = wρ |
| 行動         | プロンプト・外力入力 `f : Fin n → Q64`（システム介入・負荷） |
| 観測         | `observe`：ブロック和（A4：ミクロログ → マクロ影響度・組織KPI集計） |
| A1 極値     | 同一処理時間を進める候補のうち、ガバナンスコスト・リスク変化が最小のもの（Extremal）を選択 |
| A3 整合性   | Law（許容リスク上限・公平性バウンダリ）および状態方程式 p = wρ（ポリシー整合）を満たさない候補は棄却 |
| 同期         | `sync`：外部監査・人間（Human-in-the-Loop）の観測 y でリスク状態を修復・是正 |
| 検査         | `stepOK`, `massOf`, `momOf`, `macroOK`（総リスク量の保存・境界チェックとマクロ監査） |

数値は Q32.32 固定小数点（BitVec 64）で、加減乗は Int64 範囲に飽和する（ラップしない）。
-/

/-! ## Q32.32 固定小数点（飽和演算） -/

structure Q64 where
  raw : BitVec 64
  deriving DecidableEq, Repr

namespace Q64
def fracBits : Nat := 32
def minI : Int := -(2 ^ 63)
def maxI : Int := 2 ^ 63 - 1
def toInt (a : Q64) : Int := a.raw.toInt
def ofInt (z : Int) : Q64 := ⟨BitVec.ofInt 64 z⟩
/-- Int64 範囲に飽和させてから Q64 にする -/
def sat (z : Int) : Q64 := ofInt (max minI (min maxI z))
def ofNat' (k : Nat) : Q64 := sat ((k : Int) * 2 ^ fracBits)
def zero : Q64 := ⟨0⟩
def one : Q64 := ofNat' 1
def half (a : Q64) : Q64 := ofInt (a.toInt / 2)
def absQ (a : Q64) : Q64 := if a.toInt < 0 then sat (-a.toInt) else a

instance : Inhabited Q64 := ⟨zero⟩
instance : LE Q64 := ⟨fun a b => a.toInt ≤ b.toInt⟩
instance : LT Q64 := ⟨fun a b => a.toInt < b.toInt⟩
instance (a b : Q64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toInt ≤ b.toInt))
instance (a b : Q64) : Decidable (a < b) := inferInstanceAs (Decidable (a.toInt < b.toInt))
instance : Add Q64 := ⟨fun a b => sat (a.toInt + b.toInt)⟩
instance : Sub Q64 := ⟨fun a b => sat (a.toInt - b.toInt)⟩
instance : Mul Q64 := ⟨fun a b => sat ((a.toInt * b.toInt) / 2 ^ fracBits)⟩
end Q64

/-! ## 元の構造（AIガバナンス抽象化・64bit 版） -/

structure Obverse (n : Nat) where
  ρ : Fin n → Q64    -- Risk / Performance Density（各領域のリスク・負荷密度）
  p : Fin n → Q64    -- Governance Control Pressure（抑止圧力・ポリシー負荷）

structure Reverse (n : Nat) where
  Law : (Fin n → Q64) → Bool    -- コンプライアンス・安全ポリシー制約関数

structure Psi (n : Nat) where
  phys : Obverse n  -- 実際のAI実行状態
  math : Reverse n  -- 法律・ガバナンス規範

/-- 有限候補集合上の最小性（一般の状態型版） -/
def ExtremalOn {α : Type} (A : α → Q64) (x₀ : α) (cands : List α) : Prop :=
  ∀ x ∈ cands, A x₀ ≤ A x

instance {α : Type} (A : α → Q64) (x₀ : α) (cands : List α) :
    Decidable (ExtremalOn A x₀ cands) := by
  unfold ExtremalOn; infer_instance

/-- Psi 上の安全・コスト変分原理（最小リスク原理） -/
def Extremal {n : Nat} (A : Psi n → Q64) (Ψ₀ : Psi n) (cands : List (Psi n)) : Prop :=
  ExtremalOn A Ψ₀ cands

instance {n : Nat} (A : Psi n → Q64) (Ψ₀ : Psi n) (cands : List (Psi n)) :
    Decidable (Extremal A Ψ₀ cands) := by
  unfold Extremal; infer_instance

/-- ガバナンス適合性（実環境の挙動がポリシーの規範を満たしているか） -/
def Consistent {n : Nat} (Ψ : Psi n) : Prop :=
  Ψ.math.Law Ψ.phys.ρ = true

instance {n : Nat} (Ψ : Psi n) : Decidable (Consistent Ψ) := by
  unfold Consistent; infer_instance

structure GovernanceModel (n : Nat) where
  A : Psi n → Q64
  cands : List (Psi n)
  Ψ₀ : Psi n
  extremal_condition : Extremal A Ψ₀ cands
  consistency_condition : Consistent Ψ₀

theorem internal_coherence {n : Nat} (M : GovernanceModel n) :
    Extremal M.A M.Ψ₀ M.cands ∧ Consistent M.Ψ₀ :=
  ⟨M.extremal_condition, M.consistency_condition⟩

/-! ## ガバナンス世界モデルの状態 -/

/-- ガバナンス状態：結合状態 Ψ（AI状態 ρ,p ＋ 規範 Law）と推論モーメンタム m -/
structure World (n : Nat) where
  Ψ : Psi n
  m : Fin n → Q64

def sumQ {n : Nat} (f : Fin n → Q64) : Q64 :=
  (List.finRange n).foldl (fun acc i => acc + f i) Q64.zero

def memo {n : Nat} (f : Fin n → Q64) : Fin n → Q64 :=
  let t := Array.ofFn f
  fun i => t[i.val]!

def zeroF {n : Nat} : Fin n → Q64 := fun _ => Q64.zero

/-- 法則：リスク密度が許容上限 [lo, hi]（安全バウンダリ）内に収まるか -/
def boundedPolicyLaw {n : Nat} (lo hi : Q64) : Reverse n :=
  ⟨fun f => (List.finRange n).all fun i => decide (lo ≤ f i ∧ f i ≤ hi)⟩

/-- ポリシー状態方程式 p = wρ を満たす世界を作る -/
def mkGovernanceWorld {n : Nat} (w : Q64) (law : Reverse n) (ρ m : Fin n → Q64) : World n :=
  ⟨⟨⟨ρ, fun i => w * ρ i⟩, law⟩, m⟩

/-- 評価指標：総リスク量・総モメンタム -/
def totalRiskOf {n : Nat} (W : World n) : Q64 := sumQ W.Ψ.phys.ρ
def totalMomentumOf {n : Nat} (W : World n) : Q64 := sumQ W.m

/-- システムの総リスクエネルギー：Σ (wρ² + m²) -/
def riskEnergy {n : Nat} (w : Q64) (W : World n) : Q64 :=
  sumQ fun i => w * W.Ψ.phys.ρ i * W.Ψ.phys.ρ i + W.m i * W.m i

/-- ガバナンス動力学パラメータ -/
structure Dyn (n : Nat) where
  w      : Q64                              -- ポリシー感度（応答係数） p = w ρ
  sched  : List (Q64 × Nat)                 -- ガードレール応答候補 (ステップ dt, 回数 N)
  action : World n → World n → Q64          -- コスト/リスク作用素 A(現在, 候補)

/-! ## ガバナンス動力学・予測・監査観測・人間介入（HitL） -/

section GovernanceDynamics
variable {n : Nat} [NeZero n]

/-- 1ステップガードレール推論：外部入力 f に対するリスク密度の安全遷移 -/
def stepWith (D : Dyn n) (dt : Q64) (f : Fin n → Q64) (W : World n) : World n :=
  let ρ := W.Ψ.phys.ρ
  let p := W.Ψ.phys.p
  let g : Fin n → Q64 := memo fun i => dt * Q64.half (p i + p (i + 1))
  let m' : Fin n → Q64 := memo fun i => W.m i - (g i - g (i - 1)) + dt * f i
  let q : Fin n → Q64 := memo fun i => dt * Q64.half (m' i + m' (i + 1))
  let ρ' : Fin n → Q64 := memo fun i => ρ i - (q i - q (i - 1))
  ⟨⟨⟨ρ', memo fun i => D.w * ρ' i⟩, W.Ψ.math⟩, m'⟩

def advance (D : Dyn n) (dt : Q64) (k : Nat) (f : Fin n → Q64) (W : World n) : World n :=
  (List.range k).foldl (fun s _ => stepWith D dt f s) W

/-- A3：ガバナンス・ポリシーを満たすか -/
def lawOK (W : World n) : Bool := W.Ψ.math.Law W.Ψ.phys.ρ

/-- A3：応答方程式 p = wρ を満たすか -/
def eosOK (D : Dyn n) (W : World n) : Bool :=
  (List.finRange n).all fun i => decide (W.Ψ.phys.p i = D.w * W.Ψ.phys.ρ i)

/-- 提案されるAI挙動候補の生成 -/
def proposals (D : Dyn n) (f : Fin n → Q64) (W : World n) : List (World n) :=
  D.sched.map fun c => advance D c.1 c.2 f W

/-- ポリシーに適合する（Admissible）安全な選択肢のみをフィルタリング -/
def admissible (D : Dyn n) (f : Fin n → Q64) (W : World n) : List (World n) :=
  (proposals D f W).filter fun W' => lawOK W' && eosOK D W'

def argminBy {α : Type} (A : α → Q64) : List α → Option α
  | []      => none
  | x :: xs => some (xs.foldl (fun best y => if A y < A best then y else best) x)

/-- 1ステップ意思決定（全滅した場合は安全のため現状維持） -/
def step (D : Dyn n) (f : Fin n → Q64) (W : World n) : World n :=
  match argminBy (D.action W) (admissible D f W) with
  | some W' => W'
  | none    => W

/-- 複数ステップの自律実行計画 -/
def rollout (D : Dyn n) (fs : List (Fin n → Q64)) (W : World n) : World n :=
  fs.foldl (fun s f => step D f s) W

def rolloutFree (D : Dyn n) (k : Nat) (W : World n) : World n :=
  (List.range k).foldl (fun s _ => step D zeroF s) W

/-- リアルタイム監査ガードレール検査：出力が完全に整合し最小リスクであるか -/
def stepOK (D : Dyn n) (f : Fin n → Q64) (W : World n) : Bool :=
  let cs := admissible D f W
  let out := step D f W
  cs.isEmpty || (lawOK out && eosOK D out && decide (ExtremalOn (D.action W) out cs))

/-- A4：組織的マクロモニタリング（ミクロログのブロック集計） -/
def observe (k m : Nat) (f : Fin n → Q64) : Fin m → Q64 :=
  fun b => (List.range k).foldl (fun acc j =>
    let idx := b.val * k + j
    if h : idx < n then acc + f ⟨idx, h⟩ else acc) Q64.zero

/-- A4：マクロ監査の一致性検証 -/
def macroOK (k m : Nat) (W : World n) : Bool :=
  decide (sumQ (observe k m W.Ψ.phys.ρ) = totalRiskOf W)

/-- ガバナンス同期：外部監査・人間による修正介入 y でシステム状態を安全側に復元 -/
def sync (D : Dyn n) (gain : Q64) (y : Fin n → Q64) (W : World n) : World n :=
  let ρ' : Fin n → Q64 := memo fun i => W.Ψ.phys.ρ i + gain * (y i - W.Ψ.phys.ρ i)
  let W' : World n := ⟨⟨⟨ρ', memo fun i => D.w * ρ' i⟩, W.Ψ.math⟩, W.m⟩
  if lawOK W' then W' else W

/-- ガバナンス・デジタルツインの1周期（予測ガードレール → 監査・人間同期） -/
def twinStep (D : Dyn n) (gain : Q64) (f y : Fin n → Q64) (W : World n) : World n :=
  sync D gain y (step D f W)

/-- 監査データ y との実効解離リスク（L1誤差） -/
def l1err (y : Fin n → Q64) (W : World n) : Q64 :=
  sumQ fun i => Q64.absQ (y i - W.Ψ.phys.ρ i)

end GovernanceDynamics

def dump {n : Nat} (f : Fin n → Q64) : List Int := (List.finRange n).map fun i => (f i).toInt

/-! ## 実行評価例（8コンポーネントシステム、初期リスク偏在、監査介入） -/

def wQ : Q64 := Q64.ofInt (2 ^ 30)   -- ポリシー感度 1/4

def D0 : Dyn 8 :=
  ⟨wQ,
   [(Q64.ofInt (2 ^ 31), 1), (Q64.ofInt (2 ^ 30), 2), (Q64.ofInt (2 ^ 29), 4)],
   fun cur cand => Q64.absQ (riskEnergy wQ cand - riskEnergy wQ cur)⟩

-- 許容リスク上限の指定（上限を超えると安全違反とみなされる）
def law0 : Reverse 8 := boundedPolicyLaw Q64.zero (Q64.ofNat' 4)

-- 初期リスク配置（特定モジュール 3, 4 に負荷が集中）
def rho0 : Fin 8 → Q64 :=
  fun i => if i.val == 3 || i.val == 4 then Q64.ofNat' 2 else Q64.ofNat' 1

def W0 : World 8 := mkGovernanceWorld wQ law0 rho0 zeroF

#eval (totalRiskOf W0).toInt                                 -- 42949672960（= 10.0）
#eval dump (rolloutFree D0 4 W0).Ψ.phys.ρ                     -- リスクの平滑化と拡散シミュレーション
#eval (totalRiskOf (rolloutFree D0 4 W0)).toInt               -- 42949672960（総リスク保存則）
#eval (totalMomentumOf (rolloutFree D0 4 W0)).toInt           -- 0
#eval stepOK D0 zeroF W0                                     -- true（リアルタイムガードレール正常作動）
#eval macroOK 2 4 (rolloutFree D0 4 W0)                       -- true（ミクロ-マクロ監査の完全整合）
#eval dump (observe 2 4 (rolloutFree D0 4 W0).Ψ.phys.ρ)

-- 外部からの不確実な入力負荷 f
def fForce : Fin 8 → Q64 := fun i => if i.val == 0 then Q64.ofInt (2 ^ 29) else Q64.zero
#eval (totalMomentumOf (step D0 fForce W0)).toInt            -- 268435456

-- 人間による監査・修正介入（HitL）：ドリフトした状態に対する補正
def rhoT : Fin 8 → Q64 :=
  fun i => if i.val == 2 || i.val == 4 then Q64.ofNat' 2 else Q64.ofNat' 1
def WT : World 8 := mkGovernanceWorld wQ law0 rhoT zeroF
#eval (l1err rho0 WT).toInt                                  -- 8589934592（= 2.0 リスク解離）
#eval (l1err rho0 (sync D0 (Q64.ofInt (2 ^ 31)) rho0 WT)).toInt   -- 4294967296（= 1.0 監査同期により半減）

end AIGovernance.WM
