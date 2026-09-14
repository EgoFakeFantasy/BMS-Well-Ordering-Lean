import BMSConstructibleBridge.PowerlessImage

/-!
# 当前纯公式的无幂集分离与替换

仅用上游 FromFirstOrder 翻译。有限参数槽通过变量的现有 position 读取，
不另建源语法、变量编码或公式识别器。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessComprehension

open Logic FirstOrder
open SetTheory.Definitional.Project

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l {Γ : SortContext ℒ} (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) Γ.length) :
    FirstOrder.Env ℳ [] Γ where
  boundVal := fun v => nomatch v
  freeVal := fun {s} v => match s with | .set => η.bound v.position

theorem env_push_l {Γ : SortContext ℒ}
    (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) Γ.length) (a : ℳ.Carrier .set) :
    env_l (Γ := .set :: Γ) (η.push a) = (env_l η).pushFree a := by
  apply FirstOrder.Env.ext
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => rfl
    | .there v => cases s; rfl

def unary_m {Γ : SortContext ℒ} (φ : FirstOrder.Formula ℒ [] (.set :: Γ)) : UnarySchema Γ.length where
  body := FromFirstOrder.translate (bound := []) (free := .set :: Γ) (depth := Γ.length + 1)
    (fun v => nomatch v) (fun v => v.position) φ
  freeClosed := FromFirstOrder.freeClosed _ _ φ

def binary_m {Γ : SortContext ℒ} (φ : FirstOrder.Formula ℒ [] (.set :: .set :: Γ)) : BinarySchema Γ.length where
  body := FromFirstOrder.translate (bound := []) (free := .set :: .set :: Γ) (depth := Γ.length + 2)
    (fun v => nomatch v) (fun v => v.position) φ
  freeClosed := FromFirstOrder.freeClosed _ _ φ

theorem unary_l (hℳ : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : FirstOrder.Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) Γ.length) (x : ℳ.Carrier .set) :
    SetTheory.Definitional.Project.Formula.satisfies (η.push x) (unary_m φ).body ↔
      φ.satisfies ((env_l η).pushFree x) := by
  rw [← env_push_l]
  exact FromFirstOrder.correct (PowerlessTheory.ext_l hℳ) φ _ _ _ _
    (fun v => nomatch v) (fun v => rfl)

theorem binary_l (hℳ : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : FirstOrder.Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) Γ.length) (x y : ℳ.Carrier .set) :
    (binary_m φ).denote η x y ↔ φ.satisfies (((env_l η).pushFree x).pushFree y) := by
  rw [← env_push_l, ← env_push_l]
  exact FromFirstOrder.correct (PowerlessTheory.ext_l hℳ) φ _ _ _ _
    (fun v => nomatch v) (fun v => rfl)

theorem separation_l (hℳ : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : FirstOrder.Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) Γ.length) (A : ℳ.Carrier .set) :
    ∃ B, ∀ x, (FirstOrderSemantics.reduct ℳ).mem x B ↔
      (FirstOrderSemantics.reduct ℳ).mem x A ∧ φ.satisfies ((env_l η).pushFree x) := by
  obtain ⟨B, hB⟩ := PowerlessSeparation.exists_l hℳ (unary_m φ) η A
  exact ⟨B, fun x => (hB x).trans (and_congr Iff.rfl (unary_l hℳ φ η x))⟩

theorem image_l (hℳ : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : FirstOrder.Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) Γ.length) (A : ℳ.Carrier .set)
    (h : ∀ x, (FirstOrderSemantics.reduct ℳ).mem x A →
      ∃ y, φ.satisfies (((env_l η).pushFree x).pushFree y))
    (h₁ : ∀ x, (FirstOrderSemantics.reduct ℳ).mem x A → ∀ y z,
      φ.satisfies (((env_l η).pushFree x).pushFree y) →
      φ.satisfies (((env_l η).pushFree x).pushFree z) → y = z) :
    ∃ B, ∀ y, (FirstOrderSemantics.reduct ℳ).mem y B ↔
      ∃ x, (FirstOrderSemantics.reduct ℳ).mem x A ∧
        φ.satisfies (((env_l η).pushFree x).pushFree y) := by
  have h₂ : ∀ x y, (binary_m φ).denote η x y ↔
      φ.satisfies (((env_l η).pushFree x).pushFree y) := binary_l hℳ φ η
  obtain ⟨B, hB⟩ := PowerlessImage.exists_l hℳ (binary_m φ) η A
    (fun x hx => (h x hx).imp fun y hy => (h₂ x y).mpr hy)
    (fun x hx y z hy hz => h₁ x hx y z ((h₂ x y).mp hy) ((h₂ x z).mp hz))
  exact ⟨B, fun y => (hB y).trans (exists_congr fun x => and_congr Iff.rfl (h₂ x y))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessComprehension
