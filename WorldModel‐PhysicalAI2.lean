/-
  License: Apache 2.0   Copyright (c) Takeo Yamamoto

  Physical AI Layer v2 — シールド付き閉ループと安全証明書

  前提：前回の WorldModel.lean（Sys / Simulation / Invariant）の上に載る層。
  `import WorldModel` のモジュール名は lakefile に合わせて調整してください。

  設計方針
  1. 信頼しない部分（plan：学習ポリシーや最適化器）と、信頼する部分（check：実行時検証器、
     fallback：安全側の行動）を型のレベルで分離する。
  2. 実行される行動は「検証を通った提案」か「フォールバック」のどちらかしかない
     （fail-closed を証明ではなく構造で強制する）。
  3. 安全性は `SafetyCase`（証明書）として明示する。証明書があれば、
     どんな `plan`・どんな有界外乱の列に対しても安全集合が閉ループで不変。
  4. 世界モデル（Simulation）で証明した不変量は、pullback で実世界に移せる。
-/
import WorldModel
import Mathlib.Tactic.Ring

namespace WorldModel

variable {S T Z O A D : Type*}

/-! ## 1. 物理プラントと Physical AI -/

/-- 物理プラント。外乱 `D` を受け、`sense` で観測を出す。
    アクチュエータの実効（指令 → 物理作用）は `step` に含める。 -/
structure Plant (S A O D : Type*) where
  step : S → A → D → S
  sense : S → O

/-- Physical AI：
    * `estimate`：観測 → 信念（潜在状態）
    * `plan`：信念 → 提案行動（信頼しない）
    * `check`：信念と提案行動の実行時検証器（`Bool`。実機で走る）
    * `fallback`：検証に失敗したときの安全側の行動 -/
structure PhysicalAI (S Z O A D : Type*) where
  plant : Plant S A O D
  estimate : O → Z
  plan : Z → A
  check : Z → A → Bool
  fallback : Z → A

def PhysicalAI.belief (P : PhysicalAI S Z O A D) (s : S) : Z :=
  P.estimate (P.plant.sense s)

def PhysicalAI.proposal (P : PhysicalAI S Z O A D) (s : S) : A :=
  P.plan (P.belief s)

/-- fail-closed 制御：検証を通った提案だけを実行し、通らなければフォールバック。 -/
def PhysicalAI.control (P : PhysicalAI S Z O A D) (s : S) : A :=
  if P.check (P.belief s) (P.proposal s) = true then P.proposal s else P.fallback (P.belief s)

/-- 閉ループの一歩：実世界の次状態を返す（予測値ではない）。 -/
def PhysicalAI.stepWorld (P : PhysicalAI S Z O A D) (s : S) (d : D) : S :=
  P.plant.step s (P.control s) d

/-- 外乱列 `ds` の下での閉ループ実行。 -/
def PhysicalAI.run (P : PhysicalAI S Z O A D) : S → List D → S
  | s, [] => s
  | s, d :: ds => PhysicalAI.run P (P.stepWorld s d) ds

/-! ## 2. fail-closed 性 -/

theorem PhysicalAI.control_of_check (P : PhysicalAI S Z O A D) (s : S)
    (h : P.check (P.belief s) (P.proposal s) = true) : P.control s = P.proposal s := by
  unfold PhysicalAI.control
  rw [if_pos h]

theorem PhysicalAI.control_of_not_check (P : PhysicalAI S Z O A D) (s : S)
    (h : P.check (P.belief s) (P.proposal s) ≠ true) :
    P.control s = P.fallback (P.belief s) := by
  unfold PhysicalAI.control
  rw [if_neg h]

/-- 実行される行動は、検証を通ったものか、フォールバックのどちらか。 -/
theorem PhysicalAI.control_certified (P : PhysicalAI S Z O A D) (s : S) :
    P.check (P.belief s) (P.control s) = true ∨ P.control s = P.fallback (P.belief s) := by
  by_cases h : P.check (P.belief s) (P.proposal s) = true
  · left
    rw [P.control_of_check s h]
    exact h
  · right
    exact P.control_of_not_check s h

/-! ## 3. 安全証明書と閉ループ安全性 -/

/-- 安全証明書。信頼の基盤はここに集約される：
    * `sense_sound`：センサ経由の信念は真の状態と整合する
    * `check_sound`：検証を通った行動は、安全集合を有界外乱の下で保つ
    * `fallback_sound`：フォールバックも安全集合を保つ -/
structure SafetyCase (P : PhysicalAI S Z O A D) where
  Safe : S → Prop
  Consistent : Z → S → Prop
  DistOk : D → Prop
  sense_sound : ∀ s, Consistent (P.belief s) s
  check_sound : ∀ z s a, Consistent z s → P.check z a = true → Safe s →
    ∀ d, DistOk d → Safe (P.plant.step s a d)
  fallback_sound : ∀ z s, Consistent z s → Safe s →
    ∀ d, DistOk d → Safe (P.plant.step s (P.fallback z) d)

/-- 一歩の安全性（`plan` が何であっても成り立つ）。 -/
theorem PhysicalAI.step_safe (P : PhysicalAI S Z O A D) (C : SafetyCase P) {s : S}
    (hs : C.Safe s) {d : D} (hd : C.DistOk d) : C.Safe (P.stepWorld s d) := by
  unfold PhysicalAI.stepWorld
  by_cases h : P.check (P.belief s) (P.proposal s) = true
  · rw [P.control_of_check s h]
    exact C.check_sound (P.belief s) s (P.proposal s) (C.sense_sound s) h hs d hd
  · rw [P.control_of_not_check s h]
    exact C.fallback_sound (P.belief s) s (C.sense_sound s) hs d hd

/-- 任意長の閉ループ実行を通じて、安全集合は不変。 -/
theorem PhysicalAI.run_safe (P : PhysicalAI S Z O A D) (C : SafetyCase P) :
    ∀ (ds : List D), (∀ d ∈ ds, C.DistOk d) → ∀ s, C.Safe s → C.Safe (P.run s ds) := by
  intro ds
  induction ds with
  | nil =>
    intro _ s hs
    exact hs
  | cons d ds ih =>
    intro hds s hs
    have hd : C.DistOk d := hds d (by simp)
    have hds' : ∀ e ∈ ds, C.DistOk e := fun e he => hds e (by simp [he])
    exact ih hds' _ (P.step_safe C hs hd)

/-! ## 4. 世界モデルとの接続 -/

/-- 世界モデル（`Simulation`）上で証明した不変量を、符号化で実世界側に引き戻す。
    計算側（UHA など）で安全性を証明 → 実世界の公称モデルの安全性を得る、の橋渡し。 -/
def Invariant.pullback {X : Sys S A O} {Y : Sys T A O} (I : Invariant Y)
    (f : Simulation X Y) : Invariant X where
  holds s := I.holds (f.encode s)
  preserved s a h := by
    have h' := I.preserved (f.encode s) a h
    rw [f.step_commutes s a] at h'
    exact h'

/-! ## 5. 具体例：速度ガバナ（1 次元、外乱 |d| ≤ 1、安全 = |v| ≤ V） -/

def speedPlant : Plant ℤ ℤ ℤ ℤ where
  step v a d := v + a + d
  sense v := v

/-- 実行時検証器：次の速度が外乱の余裕 1 を残して [-(V-1), V-1] に入るか。 -/
def speedCheck (V : ℤ) (z a : ℤ) : Bool :=
  decide (-(V - 1) ≤ z + a ∧ z + a ≤ V - 1)

/-- 任意の（信頼しない）プランナー `plan` を持つ速度ガバナ。
    フォールバックは「ブレーキ」（信念上の速度を打ち消す）。 -/
def speedAI (V : ℤ) (plan : ℤ → ℤ) : PhysicalAI ℤ ℤ ℤ ℤ ℤ where
  plant := speedPlant
  estimate := id
  plan := plan
  check := speedCheck V
  fallback := fun z => -z

theorem speedCheck_sound {V z s a d : ℤ} (hc : z = s) (h : speedCheck V z a = true)
    (hd : -1 ≤ d ∧ d ≤ 1) : -V ≤ s + a + d ∧ s + a + d ≤ V := by
  subst hc
  unfold speedCheck at h
  have h' := of_decide_eq_true h
  obtain ⟨h1, h2⟩ := h'
  obtain ⟨d1, d2⟩ := hd
  constructor <;> omega

theorem speedFallback_sound {V z s d : ℤ} (hV : 1 ≤ V) (hc : z = s)
    (hd : -1 ≤ d ∧ d ≤ 1) : -V ≤ s + -z + d ∧ s + -z + d ≤ V := by
  subst hc
  obtain ⟨d1, d2⟩ := hd
  constructor <;> omega

def speedSafetyCase (V : ℤ) (hV : 1 ≤ V) (plan : ℤ → ℤ) : SafetyCase (speedAI V plan) where
  Safe v := -V ≤ v ∧ v ≤ V
  Consistent z v := z = v
  DistOk d := -1 ≤ d ∧ d ≤ 1
  sense_sound s := rfl
  check_sound z s a hc hchk _ d hd := speedCheck_sound hc hchk hd
  fallback_sound z s hc _ d hd := speedFallback_sound hV hc hd

/-- どんなプランナー・どんな有界外乱列でも、速度は |v| ≤ V に留まる。 -/
theorem speed_safe_for_any_plan (V : ℤ) (hV : 1 ≤ V) (plan : ℤ → ℤ) (ds : List ℤ)
    (hds : ∀ d ∈ ds, -1 ≤ d ∧ d ≤ 1) (v : ℤ) (hv : -V ≤ v ∧ v ≤ V) :
    -V ≤ (speedAI V plan).run v ds ∧ (speedAI V plan).run v ds ≤ V :=
  PhysicalAI.run_safe _ (speedSafetyCase V hV plan) ds hds v hv

/-- 検証器が実際に危険な提案を弾くことの確認（V = 10、速度 9 に加速 5 は拒否）。 -/
theorem speedCheck_rejects_overspeed : speedCheck 10 9 5 = false := by decide

theorem speedCheck_accepts_mild : speedCheck 10 0 3 = true := by decide

end WorldModel
