/-
  License: Apache 2.0   Copyright (c) Takeo Yamamoto

  WorldModel v2 — 行動付き世界モデルと UHA Computational Core

  設計方針
  1. 世界（環境）も計算側（潜在モデル）も同じ `Sys`（状態・行動・観測を持つ力学系）で表す。
  2. 「世界モデルが正しい」= 計算側が世界を `Simulation`（前向きシミュレーション）していること。
  3. その帰結（多段ロールアウトの正しさ、観測予測の正しさ、固定点の対応、
     潜在表現の十分性、階層合成、コヒーレンスの保存）を定理として証明する。
  4. UHA（U64 上の mask 付き更新）は潜在側の 1 つの具体的な実装として差し込む。
  5. F-Theory の「法則」は遷移で保存される不変量 (`Invariant`) として扱う。
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace WorldModel

variable {S T U A O : Type*}

/-! ## 1. UHA Computational Core -/

abbrev U64 := ZMod (2 ^ 64)
abbrev UHAState (n : Nat) := Fin n → U64

/-- mask 付き更新。active なセルだけ `F` に従い、他は据え置き。 -/
def UHAUpdate {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) : UHAState n :=
  fun i => if active i = true then F x i else x i

theorem UHAUpdate_active {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) (i : Fin n) (h : active i = true) :
    UHAUpdate active F x i = F x i := by
  simp [UHAUpdate, h]

theorem UHAUpdate_inactive {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) (i : Fin n) (h : active i = false) :
    UHAUpdate active F x i = x i := by
  simp [UHAUpdate, h]

/-- 全セル active なら単なる `F`。 -/
theorem UHAUpdate_full {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (h : ∀ i, active i = true) (x : UHAState n) :
    UHAUpdate active F x = F x :=
  funext fun i => UHAUpdate_active active F x i (h i)

/-- 旧定義 `x i + (F x i - x i)` との同値（U64 は環なので `x + (F x - x) = F x`）。 -/
theorem UHAUpdate_eq_add_sub {n : Nat} (active : Fin n → Bool)
    (F : UHAState n → UHAState n) (x : UHAState n) :
    UHAUpdate active F x = fun i => if active i = true then x i + (F x i - x i) else x i := by
  funext i
  by_cases h : active i = true
  · show (if active i = true then F x i else x i) =
        (if active i = true then x i + (F x i - x i) else x i)
    rw [if_pos h, if_pos h]
    ring
  · show (if active i = true then F x i else x i) =
        (if active i = true then x i + (F x i - x i) else x i)
    rw [if_neg h, if_neg h]

/-- 固定点は定義そのもの（旧 `fixedPoint` + `fixedPoint_spec` は不要になる）。 -/
def UHAFixedPoint {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) : Prop := UHAUpdate active F x = x

/-- 固定点の特徴付け：active なセルでだけ `F x i = x i` が成り立てばよい。 -/
theorem UHAFixedPoint_iff {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) :
    UHAFixedPoint active F x ↔ ∀ i, active i = true → F x i = x i := by
  constructor
  · intro h i hi
    have h' := congrFun h i
    rwa [UHAUpdate_active active F x i hi] at h'
  · intro h
    funext i
    by_cases hi : active i = true
    · rw [UHAUpdate_active active F x i hi]
      exact h i hi
    · have hi' : active i = false := by simpa using hi
      rw [UHAUpdate_inactive active F x i hi']

def UHAQuadraticMap {n : Nat} (x : UHAState n) : UHAState n := fun i => x i * x i

def UHAQuadraticUpdate {n : Nat} (active : Fin n → Bool) (x : UHAState n) : UHAState n :=
  UHAUpdate active UHAQuadraticMap x

def UHAQuadraticFixedPoint {n : Nat} (active : Fin n → Bool) (x : UHAState n) : Prop :=
  UHAQuadraticUpdate active x = x

theorem UHAQuadraticFixedPoint_iff {n : Nat} (active : Fin n → Bool) (x : UHAState n) :
    UHAQuadraticFixedPoint active x ↔ ∀ i, active i = true → x i * x i = x i :=
  UHAFixedPoint_iff active UHAQuadraticMap x

theorem UHAQuadratic_zero_fixed {n : Nat} (active : Fin n → Bool) :
    UHAQuadraticFixedPoint active (0 : UHAState n) := by
  rw [UHAQuadraticFixedPoint_iff]
  intro i _
  simp

theorem UHAQuadratic_one_fixed {n : Nat} (active : Fin n → Bool) :
    UHAQuadraticFixedPoint active (1 : UHAState n) := by
  rw [UHAQuadraticFixedPoint_iff]
  intro i _
  simp

/-! ## 2. 一般の世界モデル：行動付き力学系とシミュレーション -/

/-- 状態 `S`・行動 `A`・観測 `O` を持つ決定的力学系。世界も潜在モデルもこの型。 -/
structure Sys (S A O : Type*) where
  step : S → A → S
  obs : S → O

/-- 行動列を順に適用するロールアウト。 -/
def Sys.run (X : Sys S A O) : S → List A → S
  | s, [] => s
  | s, a :: as => Sys.run X (X.step s a) as

/-- 行動 `a` に対する固定点。 -/
def Sys.IsFixed (X : Sys S A O) (a : A) (s : S) : Prop := X.step s a = s

/-- 観測的同値：どんな行動列を与えても観測列が一致する。 -/
def Sys.ObsEquiv (X : Sys S A O) (s t : S) : Prop :=
  ∀ as : List A, X.obs (X.run s as) = X.obs (X.run t as)

/-- `Y` は `X` の（前向き）シミュレーション：
    符号化が遷移と観測の両方を保存する。これが「世界モデルが正しい」の定義。 -/
structure Simulation (X : Sys S A O) (Y : Sys T A O) where
  encode : S → T
  step_commutes : ∀ s a, Y.step (encode s) a = encode (X.step s a)
  obs_commutes : ∀ s, Y.obs (encode s) = X.obs s

/-- 多段ロールアウトの正しさ：一段の可換性が任意長の行動列に持ち上がる。 -/
theorem Simulation.run_commutes {X : Sys S A O} {Y : Sys T A O} (f : Simulation X Y)
    (as : List A) : ∀ s, Y.run (f.encode s) as = f.encode (X.run s as) := by
  induction as with
  | nil => intro s; rfl
  | cons a as ih =>
    intro s
    show Y.run (Y.step (f.encode s) a) as = f.encode (X.run (X.step s a) as)
    rw [f.step_commutes s a]
    exact ih _

/-- 予測の正しさ：潜在側でロールアウトして読み出した観測 = 世界の実際の観測。 -/
theorem Simulation.obs_run {X : Sys S A O} {Y : Sys T A O} (f : Simulation X Y)
    (s : S) (as : List A) :
    Y.obs (Y.run (f.encode s) as) = X.obs (X.run s as) := by
  rw [f.run_commutes as s, f.obs_commutes]

/-- 固定点は符号化で固定点に写る。 -/
theorem Simulation.isFixed_map {X : Sys S A O} {Y : Sys T A O} (f : Simulation X Y)
    {a : A} {s : S} (h : X.IsFixed a s) : Y.IsFixed a (f.encode s) := by
  show Y.step (f.encode s) a = f.encode s
  rw [f.step_commutes]
  exact congrArg f.encode h

/-- 符号化が単射なら逆も成り立つ（潜在側の固定点 ⇒ 世界側の固定点）。 -/
theorem Simulation.isFixed_of_injective {X : Sys S A O} {Y : Sys T A O}
    (f : Simulation X Y) (hf : Function.Injective f.encode)
    {a : A} {s : S} (h : Y.IsFixed a (f.encode s)) : X.IsFixed a s := by
  show X.step s a = s
  apply hf
  rw [← f.step_commutes]
  exact h

/-- 潜在表現の十分性：符号化が一致する状態は、将来の観測が全て一致する。 -/
theorem Simulation.obsEquiv_of_encode_eq {X : Sys S A O} {Y : Sys T A O}
    (f : Simulation X Y) {s t : S} (h : f.encode s = f.encode t) : X.ObsEquiv s t := by
  unfold Sys.ObsEquiv
  intro as
  rw [← f.obs_run s as, ← f.obs_run t as, h]

/-- 恒等シミュレーション。 -/
def Simulation.refl (X : Sys S A O) : Simulation X X where
  encode := id
  step_commutes _ _ := rfl
  obs_commutes _ := rfl

/-- 階層合成（抽象化の多段化）：シミュレーションは合成で閉じる。 -/
def Simulation.comp {X : Sys S A O} {Y : Sys T A O} {W : Sys U A O}
    (f : Simulation X Y) (g : Simulation Y W) : Simulation X W where
  encode := g.encode ∘ f.encode
  step_commutes s a := by
    show W.step (g.encode (f.encode s)) a = g.encode (f.encode (X.step s a))
    rw [g.step_commutes, f.step_commutes]
  obs_commutes s := by
    show W.obs (g.encode (f.encode s)) = X.obs s
    rw [g.obs_commutes, f.obs_commutes]

/-- 意味状態と計算状態のペア。コヒーレンス（計算状態 = 意味状態の符号化）を保持する。 -/
structure UnifiedState {X : Sys S A O} {Y : Sys T A O} (f : Simulation X Y) where
  semantic : S
  computational : T
  coherent : computational = f.encode semantic

def UnifiedState.ofSemantic {X : Sys S A O} {Y : Sys T A O} (f : Simulation X Y) (s : S) :
    UnifiedState f where
  semantic := s
  computational := f.encode s
  coherent := rfl

/-- コヒーレンスは力学で保存される（証明を持つだけでなく、ステップ後も成り立つ）。 -/
def UnifiedState.step {X : Sys S A O} {Y : Sys T A O} {f : Simulation X Y}
    (u : UnifiedState f) (a : A) : UnifiedState f where
  semantic := X.step u.semantic a
  computational := Y.step u.computational a
  coherent := by
    rw [u.coherent]
    exact f.step_commutes u.semantic a

/-- 遷移で保存される述語（物理法則・保存則）。 -/
structure Invariant (X : Sys S A O) where
  holds : S → Prop
  preserved : ∀ s a, holds s → holds (X.step s a)

/-- 不変量は任意の行動列に沿って成り立ち続ける。 -/
theorem Invariant.holds_run {X : Sys S A O} (I : Invariant X) (as : List A) :
    ∀ s, I.holds s → I.holds (X.run s as) := by
  induction as with
  | nil => intro s h; exact h
  | cons a as ih => intro s h; exact ih _ (I.preserved s a h)

/-! ## 3. UHA を潜在側の実装として埋め込む -/

/-- UHA 潜在系：行動 `a` が更新則 `F a` と active マスク `mask a` を選ぶ。 -/
def UHASystem {n : Nat} (F : A → UHAState n → UHAState n) (mask : A → Fin n → Bool)
    (read : UHAState n → O) : Sys (UHAState n) A O where
  step z a := UHAUpdate (mask a) (F a) z
  obs := read

/-- フレーム性：mask が false のセルは行動で変化しない。 -/
theorem UHASystem_frame {n : Nat} (F : A → UHAState n → UHAState n) (mask : A → Fin n → Bool)
    (read : UHAState n → O) (z : UHAState n) (a : A) (i : Fin n) (h : mask a i = false) :
    (UHASystem F mask read).step z a i = z i :=
  UHAUpdate_inactive (mask a) (F a) z i h

theorem UHASystem_isFixed_iff {n : Nat} (F : A → UHAState n → UHAState n)
    (mask : A → Fin n → Bool) (read : UHAState n → O) (a : A) (z : UHAState n) :
    (UHASystem F mask read).IsFixed a z ↔ ∀ i, mask a i = true → F a z i = z i :=
  UHAFixedPoint_iff (mask a) (F a) z

/-- 世界 `E` の UHA 埋め込み：`E` を UHA 系がシミュレーションしている証拠つき。 -/
structure UHAWorldModel (E : Sys S A O) (n : Nat) where
  F : A → UHAState n → UHAState n
  mask : A → Fin n → Bool
  read : UHAState n → O
  sim : Simulation E (UHASystem F mask read)

def UHAWorldModel.latent {E : Sys S A O} {n : Nat} (W : UHAWorldModel E n) :
    Sys (UHAState n) A O :=
  UHASystem W.F W.mask W.read

/-- UHA 上で回して読み出した予測は、実世界の観測と一致する。 -/
theorem UHAWorldModel.predict_correct {E : Sys S A O} {n : Nat} (W : UHAWorldModel E n)
    (s : S) (as : List A) :
    W.read (W.latent.run (W.sim.encode s) as) = E.obs (E.run s as) :=
  W.sim.obs_run s as

/-! ## 4. F-Theory 世界：UHA 埋め込み + 法則（不変量）

  メタ公理 A1–A4 の形式化はここに足す想定。
  たとえば A4（Hierarchical Structure）は `Simulation.comp` による階層合成、
  A3（Logical Consistency）は `step_commutes` / `obs_commutes` の整合性、
  A1（Extremum）は固定点や Lyapunov 関数として入れられる。 -/

structure FTheoryWorld (E : Sys S A O) (n : Nat) extends UHAWorldModel E n where
  law : Invariant E

theorem FTheoryWorld.law_along_run {E : Sys S A O} {n : Nat} (W : FTheoryWorld E n)
    {s : S} (h : W.law.holds s) (as : List A) : W.law.holds (E.run s as) :=
  W.law.holds_run as s h

/-! ## 5. 具体例：位置・速度・エネルギー（推力つき、観測は位置のみ） -/

structure PhysicalState where
  position : U64
  velocity : U64
  energy : U64

/-- 行動 = 推力（U64）。観測 = 位置のみ（部分観測）。 -/
def physicalEnv : Sys PhysicalState U64 U64 where
  step s a :=
    { position := s.position + s.velocity
      velocity := s.velocity + a
      energy := s.energy }
  obs s := s.position

def physEnc (s : PhysicalState) : UHAState 3 :=
  fun i => match i.1 with
    | 0 => s.position
    | 1 => s.velocity
    | _ => s.energy

def physF (a : U64) (x : UHAState 3) : UHAState 3 :=
  fun i => match i.1 with
    | 0 => x 0 + x 1
    | 1 => x 1 + a
    | _ => x 2

def physicalUHA : UHAWorldModel physicalEnv 3 where
  F := physF
  mask := fun _ _ => true
  read := fun x => x 0
  sim :=
    { encode := physEnc
      step_commutes := by
        intro s a
        show UHAUpdate (fun _ => true) (physF a) (physEnc s) = physEnc (physicalEnv.step s a)
        rw [UHAUpdate_full (fun _ => true) (physF a) (fun _ => rfl) (physEnc s)]
        funext i
        fin_cases i <;> rfl
      obs_commutes := fun s => rfl }

/-- 物理法則：エネルギー保存。 -/
def physicalEnergyLaw (e₀ : U64) : Invariant physicalEnv where
  holds s := s.energy = e₀
  preserved := by
    intro s a h
    exact h

def physicalFTheory (e₀ : U64) : FTheoryWorld physicalEnv 3 where
  toUHAWorldModel := physicalUHA
  law := physicalEnergyLaw e₀

/-- 任意の推力列でエネルギーは保存される。 -/
theorem physical_energy_conserved (e₀ : U64) {s : PhysicalState} (h : s.energy = e₀)
    (as : List U64) : (physicalEnv.run s as).energy = e₀ :=
  (physicalEnergyLaw e₀).holds_run as s h

/-- UHA 側で回した位置の予測は、実際の位置と一致する。 -/
theorem physical_prediction_correct (s : PhysicalState) (as : List U64) :
    (physicalUHA.latent.run (physEnc s) as) 0 = (physicalEnv.run s as).position :=
  physicalUHA.sim.obs_run s as

end WorldModel
