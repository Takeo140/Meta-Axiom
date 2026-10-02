License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace WorldModel

/-! WorldModel + UHA Computational Core (complete version) -/

/-! ## 1. UHA computational core -/

abbrev U64 := ZMod (2 ^ 64)
abbrev UHAState (n : Nat) := Fin n → U64

def UHAUpdate {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) : UHAState n :=
  fun i => if active i = true then x i + (F x i - x i) else x i

theorem UHAUpdate_active {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) (i : Fin n) (h : active i = true) :
    UHAUpdate active F x i = F x i := by
  simp [UHAUpdate, h]

theorem UHAUpdate_inactive {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) (i : Fin n) (h : active i = false) :
    UHAUpdate active F x i = x i := by
  simp [UHAUpdate, h]

def UHAFixedPoint {n : Nat} (active : Fin n → Bool) (F : UHAState n → UHAState n)
    (x : UHAState n) : Prop := UHAUpdate active F x = x

theorem UHAFixedPoint_stable {n : Nat} {active : Fin n → Bool} {F : UHAState n → UHAState n}
    {x : UHAState n} (h : UHAFixedPoint active F x) : UHAUpdate active F x = x := h

def UHAQuadraticMap {n : Nat} (x : UHAState n) : UHAState n := fun i => x i * x i

def UHAQuadraticUpdate {n : Nat} (active : Fin n → Bool) (x : UHAState n) : UHAState n :=
  UHAUpdate active UHAQuadraticMap x

def UHAQuadraticFixedPoint {n : Nat} (active : Fin n → Bool) (x : UHAState n) : Prop :=
  UHAQuadraticUpdate active x = x

/-- 二次写像の不動点では、active な成分はすべて冪等 (x*x = x)。 -/
theorem UHAQuadraticFixedPoint_idempotent {n : Nat} {active : Fin n → Bool}
    {x : UHAState n} (h : UHAQuadraticFixedPoint active x) (i : Fin n)
    (hi : active i = true) : x i * x i = x i := by
  unfold UHAQuadraticFixedPoint at h
  have h' := congrFun h i
  unfold UHAQuadraticUpdate at h'
  rw [UHAUpdate_active active UHAQuadraticMap x i hi] at h'
  exact h'

/-- 幅 n をインデックスに持つカーネル（元の `width = n` の型不整合を解消）。 -/
structure UHAComputationalKernel (n : Nat) where
  active : Fin n → Bool
  transition : UHAState n → UHAState n
  fixedPoint : UHAState n → Prop
  fixedPoint_spec : ∀ x, fixedPoint x → transition x = x

def UHAComputationalKernel.width {n : Nat} (_ : UHAComputationalKernel n) : Nat := n

def canonicalUHAKernel (n : Nat) (active : Fin n → Bool) : UHAComputationalKernel n where
  active := active
  transition := UHAQuadraticUpdate active
  fixedPoint := UHAQuadraticFixedPoint active
  fixedPoint_spec := by intro x h; exact h

theorem canonicalUHAKernel_active (n : Nat) (active : Fin n → Bool) (x : UHAState n)
    (i : Fin n) (h : active i = true) :
    (canonicalUHAKernel n active).transition x i = x i * x i :=
  UHAUpdate_active active UHAQuadraticMap x i h

theorem canonicalUHAKernel_inactive (n : Nat) (active : Fin n → Bool) (x : UHAState n)
    (i : Fin n) (h : active i = false) :
    (canonicalUHAKernel n active).transition x i = x i :=
  UHAUpdate_inactive active UHAQuadraticMap x i h

/-! ## 2. WorldModel -/

abbrev WorldState (S : Type*) := S

structure WorldEncoding (S : Type*) (n : Nat) where
  encode : WorldState S → UHAState n

structure WorldModel (S : Type*) (n : Nat) where
  encoding : WorldEncoding S n
  worldTransition : WorldState S → WorldState S
  computationalTransition : UHAState n → UHAState n
  transition_commutes : ∀ s,
    computationalTransition (encoding.encode s) = encoding.encode (worldTransition s)

def worldStep {S : Type*} {n : Nat} (W : WorldModel S n) (s : WorldState S) : WorldState S :=
  W.worldTransition s

def computationalStep {S : Type*} {n : Nat} (W : WorldModel S n) (s : WorldState S) : UHAState n :=
  W.computationalTransition (W.encoding.encode s)

theorem worldStep_correct {S : Type*} {n : Nat} (W : WorldModel S n) (s : WorldState S) :
    computationalStep W s = W.encoding.encode (worldStep W s) := by
  exact W.transition_commutes s

def WorldFixedPoint {S : Type*} {n : Nat} (W : WorldModel S n) (s : WorldState S) : Prop :=
  W.computationalTransition (W.encoding.encode s) = W.encoding.encode s

theorem WorldFixedPoint_stable {S : Type*} {n : Nat} (W : WorldModel S n) {s : WorldState S}
    (h : WorldFixedPoint W s) : computationalStep W s = W.encoding.encode s := h

theorem WorldFixedPoint_semantic_stability {S : Type*} {n : Nat} (W : WorldModel S n)
    {s : WorldState S} (h : WorldFixedPoint W s) :
    W.encoding.encode (W.worldTransition s) = W.encoding.encode s := by
  rw [← W.transition_commutes s]
  exact h

/-! ## 3. 多ステップ実行（軌道）— 完全性の中核 -/

def worldIter {S : Type*} {n : Nat} (W : WorldModel S n) : Nat → WorldState S → WorldState S
  | 0, s => s
  | k + 1, s => worldIter W k (W.worldTransition s)

def compIter {S : Type*} {n : Nat} (W : WorldModel S n) : Nat → UHAState n → UHAState n
  | 0, x => x
  | k + 1, x => compIter W k (W.computationalTransition x)

/-- k ステップ後も、計算側の軌道は世界側の軌道の符号化と一致する。 -/
theorem compIter_encode {S : Type*} {n : Nat} (W : WorldModel S n) (k : Nat)
    (s : WorldState S) :
    compIter W k (W.encoding.encode s) = W.encoding.encode (worldIter W k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    show compIter W k (W.computationalTransition (W.encoding.encode s)) =
      W.encoding.encode (worldIter W k (W.worldTransition s))
    rw [W.transition_commutes s]
    exact ih (W.worldTransition s)

/-- 世界の不動点は、何ステップ実行しても計算側で不動。 -/
theorem WorldFixedPoint_iter {S : Type*} {n : Nat} (W : WorldModel S n) {s : WorldState S}
    (h : WorldFixedPoint W s) (k : Nat) :
    compIter W k (W.encoding.encode s) = W.encoding.encode s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show compIter W k (W.computationalTransition (W.encoding.encode s)) =
      W.encoding.encode s
    rw [h]
    exact ih

/-! ## 4. 忠実性（符号化が単射なら意味が完全に保存される） -/

theorem WorldFixedPoint_iff_of_injective {S : Type*} {n : Nat} (W : WorldModel S n)
    (hinj : Function.Injective W.encoding.encode) (s : WorldState S) :
    WorldFixedPoint W s ↔ W.worldTransition s = s := by
  constructor
  · intro h
    apply hinj
    exact WorldFixedPoint_semantic_stability W h
  · intro h
    unfold WorldFixedPoint
    rw [W.transition_commutes s, h]

theorem worldIter_eq_iff_of_injective {S : Type*} {n : Nat} (W : WorldModel S n)
    (hinj : Function.Injective W.encoding.encode) (k : Nat) (s : WorldState S) :
    worldIter W k s = s ↔ compIter W k (W.encoding.encode s) = W.encoding.encode s := by
  rw [compIter_encode W k s]
  exact hinj.eq_iff.symm

/-! ## 5. 統一状態（意味・計算の整合を保ったまま前進できる） -/

/-- A unified state is tied to the WorldModel that gives meaning to its coherence proof. -/
structure UnifiedWorldState (S : Type*) (n : Nat) (W : WorldModel S n) where
  semantic : WorldState S
  computational : UHAState n
  coherent : computational = computationalStep W semantic

def UnifiedWorldState.ofSemantic {S : Type*} {n : Nat} (W : WorldModel S n)
    (s : WorldState S) : UnifiedWorldState S n W where
  semantic := s
  computational := computationalStep W s
  coherent := rfl

/-- 意味側と計算側を同時に1ステップ進める。整合性の証明は保存される。 -/
def UnifiedWorldState.step {S : Type*} {n : Nat} {W : WorldModel S n}
    (u : UnifiedWorldState S n W) : UnifiedWorldState S n W where
  semantic := W.worldTransition u.semantic
  computational := W.computationalTransition u.computational
  coherent := by
    rw [u.coherent]
    unfold computationalStep
    rw [W.transition_commutes u.semantic]

theorem UnifiedWorldState.step_semantic {S : Type*} {n : Nat} {W : WorldModel S n}
    (u : UnifiedWorldState S n W) : u.step.semantic = W.worldTransition u.semantic := rfl

theorem UnifiedWorldState.step_computational {S : Type*} {n : Nat} {W : WorldModel S n}
    (u : UnifiedWorldState S n W) :
    u.step.computational = W.computationalTransition u.computational := rfl

/-! ## 6. 具体例：物理世界 -/

structure PhysicalState where
  position : U64
  velocity : U64
  energy : U64

def physicalTransition (s : PhysicalState) : PhysicalState :=
  { position := s.position + s.velocity, velocity := s.velocity, energy := s.energy }

def physicalEncoding : WorldEncoding PhysicalState 3 where
  encode s := fun i => match i.1 with | 0 => s.position | 1 => s.velocity | _ => s.energy

def physicalComputationalTransition (x : UHAState 3) : UHAState 3 :=
  fun i => match i.1 with | 0 => x 0 + x 1 | 1 => x 1 | _ => x 2

def physicalWorldModel : WorldModel PhysicalState 3 where
  encoding := physicalEncoding
  worldTransition := physicalTransition
  computationalTransition := physicalComputationalTransition
  transition_commutes := by
    intro s
    funext i
    fin_cases i <;> rfl

theorem physicalWorldModel_correct (s : PhysicalState) :
    physicalComputationalTransition (physicalEncoding.encode s) =
      physicalEncoding.encode (physicalTransition s) := by
  exact physicalWorldModel.transition_commutes s

/-- k ステップ後の位置は position + k * velocity（等速直線運動の閉形式）。 -/
theorem physical_position_iter (k : Nat) (s : PhysicalState) :
    (worldIter physicalWorldModel k s).position = s.position + (k : U64) * s.velocity := by
  induction k generalizing s with
  | zero => simp [worldIter]
  | succ k ih =>
    show (worldIter physicalWorldModel k (physicalTransition s)).position = _
    rw [ih (physicalTransition s)]
    show s.position + s.velocity + (k : U64) * s.velocity =
      s.position + ((k + 1 : Nat) : U64) * s.velocity
    push_cast
    ring

/-- 速度は常に保存される。 -/
theorem physical_velocity_iter (k : Nat) (s : PhysicalState) :
    (worldIter physicalWorldModel k s).velocity = s.velocity := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    show (worldIter physicalWorldModel k (physicalTransition s)).velocity = _
    rw [ih (physicalTransition s)]
    rfl

/-! ## 7. UHA 埋め込み世界モデル -/

structure UHAEmbeddedWorldModel (S : Type*) (n : Nat) where
  kernel : UHAComputationalKernel n
  encoding : WorldEncoding S n
  worldTransition : WorldState S → WorldState S
  transition_commutes : ∀ s,
    kernel.transition (encoding.encode s) = encoding.encode (worldTransition s)

theorem UHAEmbeddedWorldModel_has_kernel {S : Type*} {n : Nat}
    (W : UHAEmbeddedWorldModel S n) : W.kernel.width = n := rfl

/-- 埋め込み世界モデルは普通の WorldModel として扱える（上の定理がすべて使える）。 -/
def UHAEmbeddedWorldModel.toWorldModel {S : Type*} {n : Nat}
    (W : UHAEmbeddedWorldModel S n) : WorldModel S n where
  encoding := W.encoding
  worldTransition := W.worldTransition
  computationalTransition := W.kernel.transition
  transition_commutes := W.transition_commutes

/-- 標準の二次カーネル上に世界モデルを構成する。 -/
def UHAEmbeddedWorldModel.ofCanonical {S : Type*} {n : Nat} (active : Fin n → Bool)
    (enc : WorldEncoding S n) (wt : WorldState S → WorldState S)
    (h : ∀ s, UHAQuadraticUpdate active (enc.encode s) = enc.encode (wt s)) :
    UHAEmbeddedWorldModel S n where
  kernel := canonicalUHAKernel n active
  encoding := enc
  worldTransition := wt
  transition_commutes := h

/-! ## 8. F-Theory 世界 -/

structure MetaAxiom (S : Type*) where
  holds : S → Prop

structure PhysicalLaw (S : Type*) where
  holds : S → Prop

structure FTheoryWorld (S : Type*) (n : Nat) where
  meta : MetaAxiom S
  law : PhysicalLaw S
  model : UHAEmbeddedWorldModel S n

theorem FTheoryWorld_computation {S : Type*} {n : Nat} (W : FTheoryWorld S n) (s : S) :
    W.model.kernel.transition (W.model.encoding.encode s) =
      W.model.encoding.encode (W.model.worldTransition s) := by
  exact W.model.transition_commutes s

def FTheoryFixedPoint {S : Type*} {n : Nat} (W : FTheoryWorld S n) (s : S) : Prop :=
  W.model.kernel.fixedPoint (W.model.encoding.encode s)

theorem FTheoryFixedPoint_stable {S : Type*} {n : Nat} (W : FTheoryWorld S n) {s : S}
    (h : FTheoryFixedPoint W s) :
    W.model.kernel.transition (W.model.encoding.encode s) = W.model.encoding.encode s := by
  exact W.model.kernel.fixedPoint_spec (W.model.encoding.encode s) h

theorem FTheoryFixedPoint_world {S : Type*} {n : Nat} (W : FTheoryWorld S n) {s : S}
    (h : FTheoryFixedPoint W s) :
    W.model.encoding.encode (W.model.worldTransition s) = W.model.encoding.encode s := by
  rw [← W.model.transition_commutes s]
  exact FTheoryFixedPoint_stable W h

/-- F-Theory の不動点は、汎用 WorldModel の不動点でもある。 -/
theorem FTheoryFixedPoint_toWorldFixedPoint {S : Type*} {n : Nat} (W : FTheoryWorld S n)
    {s : S} (h : FTheoryFixedPoint W s) : WorldFixedPoint W.model.toWorldModel s :=
  W.model.kernel.fixedPoint_spec _ h

/-- 公理 (A3 整合性など) と法則が遷移で保存される、完全な F-Theory 世界。 -/
structure FTheoryWorldComplete (S : Type*) (n : Nat) extends FTheoryWorld S n where
  meta_preserved : ∀ s, meta.holds s → meta.holds (model.worldTransition s)
  law_preserved : ∀ s, law.holds s → law.holds (model.worldTransition s)

theorem FTheoryWorldComplete.meta_iter {S : Type*} {n : Nat} (W : FTheoryWorldComplete S n)
    (k : Nat) (s : S) (h : W.meta.holds s) :
    W.meta.holds (worldIter W.model.toWorldModel k s) := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    show W.meta.holds (worldIter W.model.toWorldModel k (W.model.worldTransition s))
    exact ih _ (W.meta_preserved s h)

theorem FTheoryWorldComplete.law_iter {S : Type*} {n : Nat} (W : FTheoryWorldComplete S n)
    (k : Nat) (s : S) (h : W.law.holds s) :
    W.law.holds (worldIter W.model.toWorldModel k s) := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    show W.law.holds (worldIter W.model.toWorldModel k (W.model.worldTransition s))
    exact ih _ (W.law_preserved s h)

/-- 公理・法則を満たす初期状態から、k ステップ後も計算側と世界側が一致し、
    公理と法則も成り立つ。 -/
theorem FTheoryWorldComplete.sound {S : Type*} {n : Nat} (W : FTheoryWorldComplete S n)
    (k : Nat) (s : S) (hm : W.meta.holds s) (hl : W.law.holds s) :
    compIter W.model.toWorldModel k (W.model.encoding.encode s) =
        W.model.encoding.encode (worldIter W.model.toWorldModel k s) ∧
      W.meta.holds (worldIter W.model.toWorldModel k s) ∧
      W.law.holds (worldIter W.model.toWorldModel k s) :=
  ⟨compIter_encode W.model.toWorldModel k s, W.meta_iter k s hm, W.law_iter k s hl⟩

end WorldModel

