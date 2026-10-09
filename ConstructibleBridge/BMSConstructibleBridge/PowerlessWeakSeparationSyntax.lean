import BMSConstructibleBridge.SecondOrderSeparationAxiom

/-!
# 原分离模式在任意纯集合结构中的语义

不改变原模式或旧图商接口。此辅助模块只泛化其环境读取，供弱集合论自身
的对象证明使用；不要求结构先来自二阶图解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWeakSeparationSyntax

open Logic FirstOrder

set_option autoImplicit false

universe u

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: Δ) [.set, .set, .set] Δ
  | _, .here => .bvar .here
  | _, .there v => .fvar v

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [.set, .set, .set] Δ :=
  φ.substitute (show Substitution ℒ [] (.set :: Δ) [.set, .set, .set] Δ from
    .map (fun v => nomatch v) insert_m)

private theorem body_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Δ) (a b c : 𝒩.Carrier .set) :
    (body_m φ).satisfies (((η.pushBound a).pushBound b).pushBound c) ↔
      φ.satisfies (η.pushFree c) := by
  refine (Formula.satisfies_substitute _ _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    cases v <;> rfl

theorem schema_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (η : Env 𝒩 [] Δ) :
    (SecondOrderSeparationAxiom.schema_m φ).satisfies η ↔
      ∀ a : 𝒩.Carrier .set, ∃ b, ∀ c,
        𝒩.relInterp .membership (.cons c (.cons b .nil)) ↔
          𝒩.relInterp .membership (.cons c (.cons a .nil)) ∧ φ.satisfies (η.pushFree c) := by
  simp only [SecondOrderSeparationAxiom.schema_m, Formula.satisfies]
  change (∀ a : 𝒩.Carrier .set, ∃ b, ∀ c,
    𝒩.relInterp .membership (.cons c (.cons b .nil)) ↔
      𝒩.relInterp .membership (.cons c (.cons a .nil)) ∧
      (body_m φ).satisfies (((η.pushBound a).pushBound b).pushBound c)) ↔ _
  simp_rw [body_l]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWeakSeparationSyntax
