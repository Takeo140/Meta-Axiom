/-
  License: Apache 2.0
  Copyright (c) Takeo Yamamoto

  Unified Physical AI Kernel
  ---------------------------
  Integrates:
  1. F-Theory Physics (Variational Extremization δF = 0)
  2. UltraCore HyperAlgebra (UHA: ZMod 2^64 Branchless State Transitions)
  3. Formal Safety Shield (Lean 4 Fail-Closed Verification)

  補完版の方針:
  * `Word` は `abbrev`（`def` だと Add/Mul/OfNat などの instance が見えない）
  * ZMod には順序が無いので、比較はすべて `ZMod.val : Nat` 経由
  * 基底核・安全性定理は sorry なし
-/

import Mathlib

namespace UnifiedPhysicalAI

/-!
============================================================
1. UHA (UltraCore HyperAlgebra) Engine Core
============================================================
-/

/-- 64-bit Modular Word Type for Branchless UHA Computations -/
abbrev Word := ZMod (2 ^ 64)

namespace Word

def zero : Word := 0
def one  : Word := 1

/-- Non-linear UHA transition map operating in ZMod(2^64) -/
def uhaStep (state : Word) (action : Word) (disturbance : Word) : Word :=
  -- State updating via deterministic non-linear hyper-algebra map
  state * 6364136223846793005 + action * 1442695040888963407 + disturbance + 1

/-- Branchless select: `c = 1` なら `a`、`c = 0` なら `b`（分岐なし）。 -/
def select (c a b : Word) : Word := c * a + (1 - c) * b

theorem select_one (a b : Word) : select 1 a b = a := by
  simp [select]

theorem select_zero (a b : Word) : select 0 a b = b := by
  simp [select]

/-- 奇数の自然数は ZMod (2^64) の可逆元 -/
theorem isUnit_natCast_of_odd (m : Nat) (hm : m % 2 = 1) :
    IsUnit ((m : Nat) : ZMod (2 ^ 64)) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : Nat.Coprime 2 m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  exact (Nat.Coprime.pow_left 64 h2).symm

/-- 状態係数（LCG 乗数）は可逆 -/
theorem stateConst_isUnit : IsUnit (6364136223846793005 : Word) := by
  have h := isUnit_natCast_of_odd 6364136223846793005 (by norm_num)
  first
    | exact_mod_cast h
    | simpa using h

/-- 行動係数（LCG 加数）は可逆 -/
theorem actionConst_isUnit : IsUnit (1442695040888963407 : Word) := by
  have h := isUnit_natCast_of_odd 1442695040888963407 (by norm_num)
  first
    | exact_mod_cast h
    | simpa using h

/-- 可逆元による右簡約 -/
theorem cancel_right {u a b : Word} (hu : IsUnit u) (h : a * u = b * u) : a = b := by
  first
    | exact hu.mul_right_cancel h
    | exact (hu.mul_left_inj).mp h

/-- 状態について単射：状態遷移は情報を失わない -/
theorem uhaStep_injective_state (a d : Word) :
    Function.Injective (fun s : Word => uhaStep s a d) := by
  intro s t h
  simp only [uhaStep] at h
  have h' : s * 6364136223846793005 = t * 6364136223846793005 := by
    linear_combination h
  exact cancel_right stateConst_isUnit h'

/-- 行動について単射：異なる行動は異なる次状態を与える -/
theorem uhaStep_injective_action (s d : Word) :
    Function.Injective (fun a : Word => uhaStep s a d) := by
  intro a b h
  simp only [uhaStep] at h
  have h' : a * 1442695040888963407 = b * 1442695040888963407 := by
    linear_combination h
  exact cancel_right actionConst_isUnit h'

/-- 外乱について単射 -/
theorem uhaStep_injective_disturbance (s a : Word) :
    Function.Injective (fun d : Word => uhaStep s a d) := by
  intro d e h
  simp only [uhaStep] at h
  linear_combination h

/-- 状態差の伝播：差は係数倍される（線形部分） -/
theorem uhaStep_sub_state (s t a d : Word) :
    uhaStep s a d - uhaStep t a d = (s - t) * 6364136223846793005 := by
  simp only [uhaStep]
  ring

end Word

/-!
============================================================
2. F-Theory Core (Extremization Principle δF = 0)
============================================================
-/

/--
F-Theory Functional State.
`energy` and `entropy` determine the system functional F.
-/
structure FState where
  stateVal : Word
  energy   : Word
  entropy  : Word

/-- Universal Functional F value evaluation -/
def FState.evaluateF (s : FState) : Word :=
  s.energy - s.entropy

/--
Check if the state satisfies the physical extremization condition δF = 0.
Mapped mathematically to a invariant stability bound.
（ZMod は順序を持たないので `val` で比較する）
-/
def FState.isExtremal (s : FState) (threshold : Word) : Bool :=
  decide (ZMod.val s.evaluateF < ZMod.val threshold)

theorem FState.isExtremal_iff (s : FState) (t : Word) :
    s.isExtremal t = true ↔ ZMod.val s.evaluateF < ZMod.val t := by
  simp [FState.isExtremal]

/-- 離散変分 δF = F(s') - F(s) -/
def FState.deltaF (s s' : FState) : Word :=
  s'.evaluateF - s.evaluateF

/-- 離散的な停留条件 δF = 0 -/
def FState.IsStationary (s s' : FState) : Prop :=
  s.deltaF s' = 0

theorem FState.deltaF_self (s : FState) : s.deltaF s = 0 := by
  simp [FState.deltaF]

theorem FState.isStationary_iff (s s' : FState) :
    s.IsStationary s' ↔ s'.evaluateF = s.evaluateF := by
  unfold FState.IsStationary FState.deltaF
  exact sub_eq_zero

theorem FState.isStationary_refl (s : FState) : s.IsStationary s :=
  s.deltaF_self

theorem FState.isStationary_symm {s s' : FState} (h : s.IsStationary s') :
    s'.IsStationary s := by
  rw [FState.isStationary_iff] at h ⊢
  exact h.symm

theorem FState.isStationary_trans {s s' s'' : FState}
    (h₁ : s.IsStationary s') (h₂ : s'.IsStationary s'') :
    s.IsStationary s'' := by
  rw [FState.isStationary_iff] at h₁ h₂ ⊢
  exact h₂.trans h₁

/-- ゲージ不変性：energy と entropy に同じ定数を足しても F は不変 -/
theorem FState.evaluateF_shift (s : FState) (c : Word) :
    ({ s with energy := s.energy + c, entropy := s.entropy + c } : FState).evaluateF
      = s.evaluateF := by
  show (s.energy + c) - (s.entropy + c) = s.energy - s.entropy
  ring

/-- UHA 遷移で状態値だけを更新する（F の energy / entropy は不変）。 -/
def FState.advance (s : FState) (action disturbance : Word) : FState :=
  { s with stateVal := Word.uhaStep s.stateVal action disturbance }

/-- 状態値の更新は F を変えない（停留的） -/
theorem FState.advance_stationary (s : FState) (a d : Word) :
    s.IsStationary (s.advance a d) := by
  rw [FState.isStationary_iff]
  rfl

/-!
============================================================
3. System Abstraction & Safety Shield
============================================================
-/

/-- Physical Plant abstraction with UHA state machine -/
structure Plant where
  step : Word → Word → Word → Word

/-- Perception layer converting raw physical signals to observations -/
structure Perception where
  observe : Word → Word

/-- State Estimator -/
structure Estimator where
  estimate : Word → Word

/--
F-Theory powered World Model:
Predicts physical field state under action candidate.
-/
structure WorldModel where
  predict : Word → Word → Word

/-- Goal Evaluator -/
structure Goal where
  target : Word
  satisfied : Word → Word → Prop

/-- Untrusted Planner (AI / Neural / LLM / Search) -/
structure Planner where
  plan : Word → Word → Word

/-- Low-Level Controller -/
structure Controller where
  control : Word → Word → Word

/-- Runtime Safety Shield (Verified Grounding) -/
structure SafetyShield where
  check    : Word → Word → Bool
  fallback : Word → Word

/-- 境界シールド：行動の値が `bound` 以下のときだけ許可。違反時は 0 へフォールバック。 -/
def SafetyShield.bounded (bound : Nat) : SafetyShield where
  check    := fun _ a => decide (ZMod.val a ≤ bound)
  fallback := fun _ => (0 : Word)

theorem SafetyShield.bounded_check_sound {bound : Nat} {z a : Word}
    (h : (SafetyShield.bounded bound).check z a = true) : ZMod.val a ≤ bound := by
  simpa [SafetyShield.bounded] using h

/-- 境界シールドのフォールバックは常に自分自身の検査を通る -/
theorem SafetyShield.bounded_fallback_ok (bound : Nat) (z : Word) :
    (SafetyShield.bounded bound).check z ((SafetyShield.bounded bound).fallback z) = true := by
  simp [SafetyShield.bounded]

/-- Complete Unified Physical AI System -/
structure PhysicalSystem where
  plant      : Plant
  perception : Perception
  estimator  : Estimator
  worldModel : WorldModel
  goal       : Goal
  planner    : Planner
  controller : Controller
  shield     : SafetyShield

/-!
============================================================
4. Execution Mechanics & Safety Proofs
============================================================
-/

/-- Compute belief state from raw observation -/
def PhysicalSystem.belief (sys : PhysicalSystem) (s : Word) : Word :=
  sys.estimator.estimate (sys.perception.observe s)

/-- Untrusted command candidate -/
def PhysicalSystem.proposedControl (sys : PhysicalSystem) (s : Word) : Word :=
  let z := sys.belief s
  let g := sys.goal.target
  let a := sys.planner.plan z g
  sys.controller.control z a

/--
Fail-Closed Action Selection:
Unverified actions are rejected and routed immediately to safe fallback.
-/
def PhysicalSystem.safeAction (sys : PhysicalSystem) (s : Word) : Word :=
  let z := sys.belief s
  let a := sys.proposedControl s
  if sys.shield.check z a = true then
    a
  else
    sys.shield.fallback z

/-- Closed-loop transition over single physical clock cycle -/
def PhysicalSystem.cycle (sys : PhysicalSystem) (s : Word) (d : Word) : Word :=
  sys.plant.step s (sys.safeAction s) d

/-- Multi-step physical run over discrete time sequences -/
def PhysicalSystem.run (sys : PhysicalSystem) : Word → List Word → Word
  | s, []      => s
  | s, d :: ds => sys.run (sys.cycle s d) ds

theorem PhysicalSystem.run_nil (sys : PhysicalSystem) (s : Word) :
    sys.run s [] = s := rfl

theorem PhysicalSystem.run_cons (sys : PhysicalSystem) (s d : Word) (ds : List Word) :
    sys.run s (d :: ds) = sys.run (sys.cycle s d) ds := rfl

/-- 実行の連結：走行は分割して実行しても同じ -/
theorem PhysicalSystem.run_append (sys : PhysicalSystem) :
    ∀ (ds es : List Word) (s : Word),
      sys.run s (ds ++ es) = sys.run (sys.run s ds) es := by
  intro ds
  induction ds with
  | nil => intro es s; rfl
  | cons d ds ih =>
    intro es s
    first
      | exact ih es (sys.cycle s d)
      | simp [PhysicalSystem.run, ih]

/-!
============================================================
5. Formal Safety Theorems (Verification Layer)
============================================================
-/

/-- Theorem: Accepted command execution is exact -/
theorem safeAction_of_check_true
    (sys : PhysicalSystem) (s : Word)
    (h : sys.shield.check (sys.belief s) (sys.proposedControl s) = true) :
    sys.safeAction s = sys.proposedControl s := by
  unfold PhysicalSystem.safeAction
  simp [h]

/-- Theorem: Rejected command immediately falls back -/
theorem safeAction_of_check_false
    (sys : PhysicalSystem) (s : Word)
    (h : sys.shield.check (sys.belief s) (sys.proposedControl s) ≠ true) :
    sys.safeAction s = sys.shield.fallback (sys.belief s) := by
  unfold PhysicalSystem.safeAction
  simp [h]

/-- Theorem: 実行される行動は「提案」か「フォールバック」のどちらかしかない -/
theorem safeAction_cases (sys : PhysicalSystem) (s : Word) :
    sys.safeAction s = sys.proposedControl s ∨
    sys.safeAction s = sys.shield.fallback (sys.belief s) := by
  by_cases h : sys.shield.check (sys.belief s) (sys.proposedControl s) = true
  · exact Or.inl (safeAction_of_check_true sys s h)
  · exact Or.inr (safeAction_of_check_false sys s h)

/-- Theorem (Fail-Closed): フォールバックが自分のシールドを通るなら、
    実行される行動は常にシールドを通過する。 -/
theorem safeAction_passes_shield
    (sys : PhysicalSystem)
    (hfb : ∀ z, sys.shield.check z (sys.shield.fallback z) = true) (s : Word) :
    sys.shield.check (sys.belief s) (sys.safeAction s) = true := by
  by_cases h : sys.shield.check (sys.belief s) (sys.proposedControl s) = true
  · rw [safeAction_of_check_true sys s h]
    exact h
  · rw [safeAction_of_check_false sys s h]
    exact hfb _

/-- Fundamental Safety Certification Structure -/
structure SafetyCase (sys : PhysicalSystem) where
  Safe       : Word → Prop
  Consistent : Word → Word → Prop
  DistOk     : Word → Prop

  sense_sound :
    ∀ s, Consistent (sys.belief s) s

  action_safe :
    ∀ z s a,
      Consistent z s →
      Safe s →
      sys.shield.check z a = true →
      ∀ d, DistOk d →
      Safe (sys.plant.step s a d)

  fallback_safe :
    ∀ z s,
      Consistent z s →
      Safe s →
      ∀ d, DistOk d →
      Safe (sys.plant.step s (sys.shield.fallback z) d)

/-- Main Invariant Theorem: Single Step Safety Preservation -/
theorem PhysicalSystem.step_safe
    (sys : PhysicalSystem) (C : SafetyCase sys)
    {s : Word} (hs : C.Safe s)
    {d : Word} (hd : C.DistOk d) :
    C.Safe (sys.cycle s d) := by
  unfold PhysicalSystem.cycle
  by_cases h : sys.shield.check (sys.belief s) (sys.proposedControl s) = true
  · rw [safeAction_of_check_true sys s h]
    exact C.action_safe (sys.belief s) s (sys.proposedControl s)
      (C.sense_sound s) hs h d hd
  · rw [safeAction_of_check_false sys s h]
    exact C.fallback_safe (sys.belief s) s
      (C.sense_sound s) hs d hd

/-- Grand Theorem: Arbitrary-length Run Safety Preservation -/
theorem PhysicalSystem.run_safe
    (sys : PhysicalSystem) (C : SafetyCase sys) :
    ∀ ds : List Word,
      (∀ d ∈ ds, C.DistOk d) →
      ∀ s, C.Safe s → C.Safe (sys.run s ds) := by
  intro ds
  induction ds with
  | nil =>
    intro _ s hs
    exact hs
  | cons d ds ih =>
    intro hds s hs
    have hd : C.DistOk d := hds d (by simp)
    have hds' : ∀ e ∈ ds, C.DistOk e := fun e he => hds e (by simp [he])
    exact ih hds' (sys.cycle s d) (sys.step_safe C hs hd)

/-!
============================================================
6. 具体例：任意の（信頼できない）Planner / Controller でも境界を破れない
============================================================
-/

namespace Demo

/-- 単純プラント：次状態 = 実行された行動（外乱は無視） -/
def plant : Plant := ⟨fun _ a _ => a⟩

def perception : Perception := ⟨fun s => s⟩

def estimator : Estimator := ⟨fun s => s⟩

def worldModel : WorldModel := ⟨fun _ a => a⟩

def goal : Goal := ⟨100, fun s t => s = t⟩

/-- 任意の Planner / Controller に対して境界シールド付きシステムを作る -/
def system (bound : Nat) (pl : Planner) (ct : Controller) : PhysicalSystem where
  plant      := plant
  perception := perception
  estimator  := estimator
  worldModel := worldModel
  goal       := goal
  planner    := pl
  controller := ct
  shield     := SafetyShield.bounded bound

/-- 安全性ケース：Safe = 状態値が bound 以下 -/
def safetyCase (bound : Nat) (pl : Planner) (ct : Controller) :
    SafetyCase (system bound pl ct) where
  Safe       := fun s => ZMod.val s ≤ bound
  Consistent := fun z s => z = s
  DistOk     := fun _ => True
  sense_sound := fun _ => rfl
  action_safe := by
    intro z s a _ _ h d _
    have h' : decide (ZMod.val a ≤ bound) = true := h
    exact of_decide_eq_true h'
  fallback_safe := by
    intro z s _ _ d _
    show ZMod.val (0 : Word) ≤ bound
    first
      | (rw [ZMod.val_zero]; exact Nat.zero_le _)
      | simp

/-- 定理：どんな Planner / Controller / 外乱列でも、初期状態が境界内なら
    実行後も境界内（Fail-Closed シールドによる保証）。 -/
theorem run_within_bound (bound : Nat) (pl : Planner) (ct : Controller)
    (ds : List Word) (s : Word) (hs : ZMod.val s ≤ bound) :
    ZMod.val ((system bound pl ct).run s ds) ≤ bound :=
  (system bound pl ct).run_safe (safetyCase bound pl ct) ds (fun _ _ => trivial) s hs

end Demo

/-!
============================================================
7. 動作確認
============================================================
-/

-- uhaStep 1 2 3 = 6364136223846793005 + 2·1442695040888963407 + 3 + 1
#eval (Word.uhaStep 1 2 3).val          -- 9249526305624719823

#eval (Word.select 1 10 20).val         -- 10
#eval (Word.select 0 10 20).val         -- 20

/-- 例：plan = z + g、control = 3·a、bound = 1000 -/
def demoSystem : PhysicalSystem :=
  Demo.system 1000 ⟨fun z g => z + g⟩ ⟨fun _ a => a * 3⟩

-- 5 → 315（許可）→ 1245 > 1000 なので 0 へフォールバック → 300（許可）
#eval (demoSystem.run 5 [1, 2, 3]).val  -- 300

end UnifiedPhysicalAI
