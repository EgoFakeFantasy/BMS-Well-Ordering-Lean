import BMSConstructibleBridge.SecondOrderFormulaParameters
import YesMetaZFC.Automation.RelationalTranslation

/-! # 二阶公式的异质参数列及存在块语言保持

参数列和量词块按原排序上下文构造，不借用无类型位置或外部赋值枚举。
所有语言检查沿实际 AST 完成；这些辅助引理不添加对象公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaArguments

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open Automation.RelationalTranslation (argumentsSubstitution weakenTerm existsBlock)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem conj_pure_m {Γ Δ : SortContext signature_m} (φ ψ : Formula signature_m Γ Δ)
    (hφ : language_m φ = true) (hψ : language_m ψ = true) : language_m (.conj φ ψ) = true := by
  change (language_m φ && language_m ψ) = true
  rw [hφ, hψ]
  rfl

theorem exists_pure_m {Γ Δ : SortContext signature_m} (s : sort_m)
    (φ : Formula signature_m (s :: Γ) Δ) (hφ : language_m φ = true) :
    language_m (.existsE s φ) = true := hφ

theorem forall_pure_m {Γ Δ : SortContext signature_m} (s : sort_m)
    (φ : Formula signature_m (s :: Γ) Δ) (hφ : language_m φ = true) :
    language_m (.forallE s φ) = true := hφ

theorem imp_pure_m {Γ Δ : SortContext signature_m} (φ ψ : Formula signature_m Γ Δ)
    (hφ : language_m φ = true) (hψ : language_m ψ = true) : language_m (.imp φ ψ) = true := by
  change (language_m φ && language_m ψ) = true
  rw [hφ, hψ]
  rfl

theorem images_m {Γ Δ Ξ : SortContext signature_m} (a : Arguments signature_m Γ Δ Ξ)
    (ha : pure_args_m a = true) : SecondOrderSubstitution.images_m (argumentsSubstitution a) := by
  intro s v
  match a, v with
  | .cons t a, .here =>
      have h : pure_term_m t = true ∧ pure_args_m a = true := by
        simpa only [pure_args_m, Bool.and_eq_true] using ha
      exact h.1
  | .cons t a, .there v =>
      have h : pure_term_m t = true ∧ pure_args_m a = true := by
        simpa only [pure_args_m, Bool.and_eq_true] using ha
      exact images_m a h.2 v

def formula_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] Ξ)
    (a : Arguments signature_m Γ Δ Ξ) : Formula signature_m Γ Δ :=
  SecondOrderFormulaParameters.formula_m φ (argumentsSubstitution a)

theorem pure_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] Ξ)
    (a : Arguments signature_m Γ Δ Ξ) (hφ : language_m φ = true) (ha : pure_args_m a = true) :
    language_m (formula_m φ a) = true := SecondOrderFormulaParameters.pure_m φ _ hφ (images_m a ha)

theorem formula_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (φ : Formula signature_m [] Ξ) (a : Arguments signature_m Γ Δ Ξ) :
    (formula_m φ a).satisfies η ↔ φ.satisfies
      (SecondOrderRelationSpecification.parameters_l η (argumentsSubstitution a)) :=
  SecondOrderFormulaParameters.formula_l η φ _

mutual
  theorem term_rename_m {Γ Δ Θ Ξ : SortContext signature_m} {s : sort_m}
      (t : Term signature_m Γ Δ s) (ρ : VariableRenaming Γ Θ) (τ : VariableRenaming Δ Ξ) :
      pure_term_m (t.renameMapped ρ τ) = pure_term_m t :=
    match t with
    | .bvar _ | .fvar _ => rfl
    | .app _ a => by simp only [Term.renameMapped, pure_term_m, args_rename_m a ρ τ]

  theorem args_rename_m {Γ Δ Θ Ξ : SortContext signature_m} {s : List sort_m}
      (a : Arguments signature_m Γ Δ s) (ρ : VariableRenaming Γ Θ) (τ : VariableRenaming Δ Ξ) :
      pure_args_m (a.renameMapped ρ τ) = pure_args_m a :=
    match a with
    | .nil => rfl
    | .cons t a => by simp only [Arguments.renameMapped, pure_args_m, term_rename_m t ρ τ, args_rename_m a ρ τ]
end

theorem weaken_pure_m {Γ Δ : SortContext signature_m} {s : sort_m}
    (Ξ : SortContext signature_m) (t : Term signature_m Γ Δ s) : pure_term_m (weakenTerm Ξ t) = pure_term_m t :=
  term_rename_m t _ _

theorem block_pure_m {Γ Δ : SortContext signature_m} (Ξ : SortContext signature_m)
    (φ : Formula signature_m (Ξ ++ Γ) Δ) : language_m (existsBlock Ξ φ) = language_m φ := by
  induction Ξ generalizing Γ with
  | nil => rfl
  | cons s Ξ ih => exact ih (.existsE s φ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaArguments
