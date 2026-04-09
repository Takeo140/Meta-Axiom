import Mathlib

-- ============================================================
-- F-Theory Meta-Axioms  /  完全修正版
-- ============================================================

-- A1: 最小値原理 (Extremum Principle)
-- F の大域的最小元。x₀ が F のグローバル最小値であることを定義。
def IsMinimal {α : Type*} [Preorder α] (F : α → ℝ) (x₀ : α) : Prop :=
  ∀ x : α, F x₀ ≤ F x

-- A2: トポロジー的安定性
-- A1（最小性）との冗長性を排除し、連続性のみを要請。
def TopologicallyStable {α : Type*} [TopologicalSpace α] (F : α → ℝ) (x₀ : α) : Prop :=
  ContinuousAt F x₀

-- A3: 論理的無矛盾性
-- 旧版の ¬False（恒真）を廃止。導出関係 derive を明示的に引数に取り、
-- S が False を導出できないことを要請する。
def IsConsistent {Sys : Type*} (derive : Sys → Prop → Prop) (S : Sys) : Prop :=
  ¬ derive S False

-- A4: 階層的スケーリング
-- 旧版の未束縛変数 c を存在量化で正しく束縛。
-- ミクロ状態とマクロ状態は独立したパラメータ。
def HierarchicalMacro (micro macro : ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ macro = micro * c

-- ============================================================
-- MetaAxioms クラス（冗長性なし・全公理独立）
-- ============================================================
class MetaAxioms {α : Type*} [TopologicalSpace α] [Preorder α]
    {Sys : Type*} (derive : Sys → Prop → Prop)
    (F : α → ℝ) (x₀ micro_pt macro_pt : α) (S : Sys) where
  a1 : IsMinimal F x₀
  a2 : TopologicallyStable F x₀
  a3 : IsConsistent derive S
  a4 : HierarchicalMacro (F micro_pt) (F macro_pt)

-- ============================================================
-- 定理群
-- ============================================================

-- 定理1: A1 → 下界性（最小値は全点の下界）
theorem minimal_lower_bound {α : Type*} [Preorder α]
    (F : α → ℝ) (x₀ : α) (h : IsMinimal F x₀) :
    ∀ x, F x₀ ≤ F x :=
  h

-- 定理2: A4 + ミクロ正値 → マクロ正値（符号保存）
theorem hierarchical_pos {micro macro : ℝ}
    (h : HierarchicalMacro micro macro) (hm : 0 < micro) :
    0 < macro := by
  obtain ⟨c, hc, rfl⟩ := h
  exact mul_pos hm hc

-- 定理3: A4 + ミクロ非負 → マクロ非負
theorem hierarchical_nonneg {micro macro : ℝ}
    (h : HierarchicalMacro micro macro) (hm : 0 ≤ micro) :
    0 ≤ macro := by
  obtain ⟨c, hc, rfl⟩ := h
  exact mul_nonneg hm (le_of_lt hc)

-- 定理4: MetaAxioms → 最小値での連続性と下界性の結合
theorem meta_min_and_continuous {α : Type*} [TopologicalSpace α] [Preorder α]
    {Sys : Type*} (derive : Sys → Prop → Prop)
    (F : α → ℝ) (x₀ micro_pt macro_pt : α) (S : Sys)
    [inst : MetaAxioms derive F x₀ micro_pt macro_pt S] :
    ContinuousAt F x₀ ∧ ∀ x, F x₀ ≤ F x :=
  ⟨inst.a2, inst.a1⟩

-- 定理5: A4 のスケーリング係数は macro/micro に等しい（micro ≠ 0 のとき）
theorem hierarchical_scale_eq {micro macro : ℝ}
    (h : HierarchicalMacro micro macro) (hm : micro ≠ 0) :
    ∃ c : ℝ, c > 0 ∧ c = macro / micro := by
  obtain ⟨c, hc, heq⟩ := h
  exact ⟨c, hc, by field_simp [hm]; linarith [heq.symm]⟩

-- ============================================================
-- 具体的インスタンス: Unit 上の定値関数
-- （MetaAxioms が空クラスでないことの証拠）
-- ============================================================
instance unitMetaAxioms :
    MetaAxioms
      (fun (_ : Unit) (_ : Prop) => False)  -- 何も導出しない無矛盾系
      (fun (_ : Unit) => (0 : ℝ))           -- F ≡ 0
      () () () () where
  a1 := fun _ => le_refl 0
  a2 := continuousAt_const
  a3 := fun h => h           -- ¬False = False → False
  a4 := ⟨1, one_pos, by norm_num⟩
