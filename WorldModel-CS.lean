/-
  License: Apache 2.0   Copyright (c) Takeo Yamamoto

  World Model Computational System v2 — 契約つき世界モデル計算系

  前提：WorldModel.lean（v2：Sys / Simulation / Invariant / UHASystem / UHAWorldModel）。
  `import WorldModel` のモジュール名は lakefile に合わせて調整してください。

  旧版との違い
  1. predict / infer / plan / optimize / verify が「型だけ」ではなく、世界モデルとの間の
     契約（法則）を持つ。verify は実行時に走る `Bool` 検証器で、意味世界の安全仕様に
     対して健全であることが要求される（`a = a` のような空虚な検証は書けない）。
  2. 予測は意味世界の遷移と UHA 側の遷移から導かれ、両者が可換であることが定理になる。
  3. 「観測 → 推論 → 最適化 → 検証 → 実行（失敗時はフォールバック）」の閉ループを定義し、
     安全集合が不変であることを証明する。
  4. F-Theory 世界は、法則（不変量）と A1（極値原理）を持つ WCS の拡張として与える。
  5. `UHAEmbeddedWorldModel` の `kernel.width = n` による添字ずれ（型が合わない）は、
     v2 の依存添字 `UHAWorldModel` で解消済み。
-/
import WorldModel

namespace WorldModel

variable {S A O : Type*} {n : Nat}

/-! ## 1. 世界モデル計算系（契約つき） -/

structure WorldComputationalSystem (S A O : Type*) (n : Nat) where
  /-- 意味世界（行動つき力学系）。 -/
  world : Sys S A O
  /-- UHA 上の実装（世界を UHA 系がシミュレートしている証拠つき）。 -/
  model : UHAWorldModel world n
  /-- 信念（潜在状態）と真の状態の整合性。 -/
  Consistent : UHAState n → S → Prop
  /-- 安全仕様（意味世界の述語）。 -/
  Safe : S → Prop
  /-- 状態推論：観測 → 信念。 -/
  infer : O → UHAState n
  /-- 行動の提案（信頼しない）。 -/
  plan : UHAState n → A
  /-- 提案の最適化（信頼しない）。 -/
  optimize : UHAState n → A
  /-- 行動のコスト。 -/
  cost : UHAState n → A → Nat
  /-- 実行時検証器（信頼する。実機で走る `Bool`）。 -/
  verify : UHAState n → A → Bool
  /-- 検証に失敗したときの安全側の行動。 -/
  fallback : UHAState n → A
  /-- 世界モデルの符号化は整合的な信念を与える。 -/
  consistent_encode : ∀ s, Consistent (model.sim.encode s) s
  /-- 観測からの推論は真の状態と整合する。 -/
  infer_sound : ∀ s, Consistent (infer (world.obs s)) s
  /-- 最適化は提案よりコストを悪化させない。 -/
  optimize_le : ∀ z, cost z (optimize z) ≤ cost z (plan z)
  /-- 検証を通った行動は、安全集合を保つ（検証器の健全性）。 -/
  verify_sound : ∀ z s a, Consistent z s → verify z a = true → Safe s →
    Safe (world.step s a)
  /-- フォールバックも安全集合を保つ。 -/
  fallback_safe : ∀ z s, Consistent z s → Safe s → Safe (world.step s (fallback z))

namespace WorldComputationalSystem

/-! ### 予測 -/

/-- 意味世界での予測。 -/
def predict (W : WorldComputationalSystem S A O n) (s : S) (a : A) : S :=
  W.world.step s a

/-- UHA 上での予測。 -/
def predictLatent (W : WorldComputationalSystem S A O n) (z : UHAState n) (a : A) :
    UHAState n :=
  W.model.latent.step z a

/-- 意味世界の予測と UHA 上の予測は可換（世界モデルの正しさ）。 -/
theorem predict_commutes (W : WorldComputationalSystem S A O n) (s : S) (a : A) :
    W.predictLatent (W.model.sim.encode s) a = W.model.sim.encode (W.predict s a) :=
  W.model.sim.step_commutes s a

/-- 多段の予測でも可換。 -/
theorem predictRun_commutes (W : WorldComputationalSystem S A O n) (s : S) (as : List A) :
    W.model.latent.run (W.model.sim.encode s) as = W.model.sim.encode (W.world.run s as) :=
  W.model.sim.run_commutes as s

/-- UHA 上で回して読み出した観測は、実世界の観測と一致する。 -/
theorem predictObs_correct (W : WorldComputationalSystem S A O n) (s : S) (as : List A) :
    W.model.read (W.model.latent.run (W.model.sim.encode s) as) = W.world.obs (W.world.run s as) :=
  W.model.predict_correct s as

/-! ### フェイルクローズドな行動選択 -/

/-- 最適化した行動を検証し、通らなければフォールバック。 -/
def selectAction (W : WorldComputationalSystem S A O n) (z : UHAState n) : A :=
  if W.verify z (W.optimize z) = true then W.optimize z else W.fallback z

/-- 選ばれた行動は、検証を通ったものか、フォールバックのどちらか。 -/
theorem selectAction_certified (W : WorldComputationalSystem S A O n) (z : UHAState n) :
    W.verify z (W.selectAction z) = true ∨ W.selectAction z = W.fallback z := by
  by_cases h : W.verify z (W.optimize z) = true
  · left
    rw [WorldComputationalSystem.selectAction, if_pos h]
    exact h
  · right
    rw [WorldComputationalSystem.selectAction, if_neg h]

/-- 整合した信念の下で選ばれた行動は、安全集合を保つ。 -/
theorem selectAction_safe (W : WorldComputationalSystem S A O n) {z : UHAState n} {s : S}
    (hc : W.Consistent z s) (hs : W.Safe s) :
    W.Safe (W.world.step s (W.selectAction z)) := by
  by_cases h : W.verify z (W.optimize z) = true
  · rw [WorldComputationalSystem.selectAction, if_pos h]
    exact W.verify_sound z s _ hc h hs
  · rw [WorldComputationalSystem.selectAction, if_neg h]
    exact W.fallback_safe z s hc hs

/-! ### 閉ループ：観測 → 推論 → 選択 → 実行 -/

def control (W : WorldComputationalSystem S A O n) (s : S) : A :=
  W.selectAction (W.infer (W.world.obs s))

def loopStep (W : WorldComputationalSystem S A O n) (s : S) : S :=
  W.world.step s (W.control s)

def loopRun (W : WorldComputationalSystem S A O n) : S → Nat → S
  | s, 0 => s
  | s, k + 1 => WorldComputationalSystem.loopRun W (W.loopStep s) k

/-- 一歩の安全性。`plan` / `optimize` が何であっても成り立つ。 -/
theorem loopStep_safe (W : WorldComputationalSystem S A O n) {s : S} (hs : W.Safe s) :
    W.Safe (W.loopStep s) :=
  W.selectAction_safe (W.infer_sound s) hs

/-- 任意ステップの閉ループを通じて、安全集合は不変。 -/
theorem loopRun_safe (W : WorldComputationalSystem S A O n) :
    ∀ (k : Nat) (s : S), W.Safe s → W.Safe (W.loopRun s k) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    exact hs
  | succ k ih =>
    intro s hs
    exact ih _ (W.loopStep_safe hs)

end WorldComputationalSystem

/-! ## 2. F-Theory 世界

  * 法則（旧 `PhysicalLaw`）は、意味世界の遷移で保存される不変量 `Invariant`。
  * A1（極値原理）：`optimize` は候補集合の中でコスト最小の元。
  * A3（論理的無矛盾性）：`model.sim`（遷移・観測の可換性）と各健全性の証明が担う。
  * A2（位相空間）・A4（階層構造）はここでは未形式化
    （A4 は `Simulation.comp` による階層合成として入れられる）。 -/

structure FTheoryWCS (S A O : Type*) (n : Nat) extends WorldComputationalSystem S A O n where
  law : Invariant world
  candidates : UHAState n → List A
  a1_extremum : ∀ z, optimize z ∈ candidates z ∧
    ∀ a ∈ candidates z, cost z (optimize z) ≤ cost z a

/-- A1：最適化された行動は、どの候補よりもコストが高くない。 -/
theorem FTheoryWCS.optimal (F : FTheoryWCS S A O n) (z : UHAState n) {a : A}
    (h : a ∈ F.candidates z) : F.cost z (F.optimize z) ≤ F.cost z a :=
  (F.a1_extremum z).2 a h

/-- 閉ループの一歩は法則（不変量）を保つ。 -/
theorem FTheoryWCS.loopStep_law (F : FTheoryWCS S A O n) {s : S} (h : F.law.holds s) :
    F.law.holds (F.toWorldComputationalSystem.loopStep s) :=
  F.law.preserved s _ h

/-- 閉ループを通じて、法則は成り立ち続ける。 -/
theorem FTheoryWCS.loopRun_law (F : FTheoryWCS S A O n) :
    ∀ (k : Nat) (s : S), F.law.holds s → F.law.holds (F.toWorldComputationalSystem.loopRun s k) := by
  intro k
  induction k with
  | zero =>
    intro s h
    exact h
  | succ k ih =>
    intro s h
    exact ih _ (F.loopStep_law h)

/-! ## 3. 物理系の具体例（速度上限つき、外乱なし）

  状態 = 位置・速度・エネルギー、行動 = 推力（U64）、観測 = 全状態。
  安全 = 速度が `Vmax` 以下（U64 のラップアラウンドを起こさない）。
  検証器は「現在の速度 + 推力 ≤ Vmax」を実行時に判定する。 -/

/-- 全状態観測の物理世界（`physicalEnv` と同じ遷移）。 -/
def physicalFullEnv : Sys PhysicalState U64 PhysicalState where
  step := physicalEnv.step
  obs := id

def physicalFullUHA : UHAWorldModel physicalFullEnv 3 where
  F := physF
  mask := fun _ _ => true
  read := fun x => { position := x 0, velocity := x 1, energy := x 2 }
  sim :=
    { encode := physEnc
      step_commutes := physicalUHA.sim.step_commutes
      obs_commutes := fun s => rfl }

theorem val_add_of_lt (a b : U64) (h : a.val + b.val < 2 ^ 64) :
    (a + b).val = a.val + b.val := by
  haveI : NeZero ((2 : ℕ) ^ 64) := ⟨by norm_num⟩
  first
    | (rw [ZMod.val_add]; exact Nat.mod_eq_of_lt h)
    | (simp [ZMod.val_add, Nat.mod_eq_of_lt h])

/-- 実行時検証器：信念上の速度に推力を足しても `Vmax` を超えない。 -/
def physVerify (Vmax : Nat) (z : UHAState 3) (a : U64) : Bool :=
  decide ((z 1).val + a.val ≤ Vmax)

theorem physVerify_sound (Vmax : Nat) (hV : Vmax < 2 ^ 64) (z : UHAState 3)
    (s : PhysicalState) (a : U64) (hc : z = physEnc s) (h : physVerify Vmax z a = true) :
    (s.velocity + a).val ≤ Vmax := by
  subst hc
  unfold physVerify at h
  have h' : (physEnc s 1).val + a.val ≤ Vmax := of_decide_eq_true h
  have h1 : physEnc s 1 = s.velocity := rfl
  rw [h1] at h'
  have hlt : s.velocity.val + a.val < 2 ^ 64 := lt_of_le_of_lt h' hV
  rw [val_add_of_lt _ _ hlt]
  exact h'

/-- 物理系の世界モデル計算系。`plan`（信頼しない提案）は任意。 -/
def physicalWCS (Vmax : Nat) (hV : Vmax < 2 ^ 64) (plan : UHAState 3 → U64) :
    WorldComputationalSystem PhysicalState U64 PhysicalState 3 where
  world := physicalFullEnv
  model := physicalFullUHA
  Consistent z s := z = physEnc s
  Safe s := s.velocity.val ≤ Vmax
  infer o := physEnc o
  plan := plan
  optimize := plan
  cost _ _ := 0
  verify := physVerify Vmax
  fallback _ := 0
  consistent_encode s := rfl
  infer_sound s := rfl
  optimize_le _ := Nat.le_refl _
  verify_sound z s a hc h _ := physVerify_sound Vmax hV z s a hc h
  fallback_safe z s hc hs := by
    show (s.velocity + 0).val ≤ Vmax
    rw [add_zero]
    exact hs

/-- どんなプランナーでも、速度は上限を超えない。 -/
theorem physicalWCS_loop_safe (Vmax : Nat) (hV : Vmax < 2 ^ 64) (plan : UHAState 3 → U64)
    (s : PhysicalState) (hs : s.velocity.val ≤ Vmax) (k : Nat) :
    ((physicalWCS Vmax hV plan).loopRun s k).velocity.val ≤ Vmax :=
  (physicalWCS Vmax hV plan).loopRun_safe k s hs

/-- エネルギー保存則つきの F-Theory 版。 -/
def physicalFTheoryWCS (Vmax : Nat) (hV : Vmax < 2 ^ 64) (plan : UHAState 3 → U64)
    (e₀ : U64) : FTheoryWCS PhysicalState U64 PhysicalState 3 where
  toWorldComputationalSystem := physicalWCS Vmax hV plan
  law :=
    { holds := fun s => s.energy = e₀
      preserved := fun s a h => h }
  candidates := fun z => [plan z]
  a1_extremum := fun z => ⟨List.mem_singleton.mpr rfl, fun a _ => Nat.le_refl _⟩

/-- 安全性と保存則が、同じ閉ループの上で同時に成り立つ。 -/
theorem physicalFTheoryWCS_safe_and_conservative (Vmax : Nat) (hV : Vmax < 2 ^ 64)
    (plan : UHAState 3 → U64) (e₀ : U64) (s : PhysicalState)
    (hs : s.velocity.val ≤ Vmax) (he : s.energy = e₀) (k : Nat) :
    ((physicalWCS Vmax hV plan).loopRun s k).velocity.val ≤ Vmax ∧
      ((physicalWCS Vmax hV plan).loopRun s k).energy = e₀ :=
  ⟨physicalWCS_loop_safe Vmax hV plan s hs k,
   (physicalFTheoryWCS Vmax hV plan e₀).loopRun_law k s he⟩

end WorldModel
