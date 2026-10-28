import BMSConstructibleBridge.SecondOrderFormulaArguments
import BMSConstructibleBridge.SecondOrderTransitiveSuperset
import BMSConstructibleBridge.PowerlessNaturalOrder

/-! # 有效图根的实际传递性公式

复用既有纯隶属传递性 AST，经原图解释并实例化根与图参数。任意模型的
双向语义覆盖所有内部对象，不将宿主可定义谓词直接代入内部归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphTransitivityFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  GraphTranslation.context_m

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def source_m : Formula ℒ [] [.set] := PowerlessNaturalOrder.transitive_m (.fvar .here)

def formula_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m (GraphTranslation.form_m source_m) (.cons r (.cons A .nil))

theorem pure_m {Γ Δ : SortContext signature_m} (A : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) (hA : pure_term_m A = true) (hr : pure_term_m r = true) :
    language_m (formula_m A r) = true := by
  apply SecondOrderFormulaArguments.pure_m _ _ (GraphTranslation.form_pure_m source_m)
  simp only [pure_args_m, hA, hr]
  rfl

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (A : Term signature_m Γ Δ .set) (r : Term signature_m Γ Δ .num)
    (hA : SecondOrderDomain.wf_l (A.eval η) (r.eval η)) :
    (formula_m A r).satisfies η ↔
      SecondOrderTransitiveSuperset.transitive_l ⟨A.eval η, r.eval η, hA⟩ := by
  let C : SecondOrderGraph.code_l ℳ := ⟨A.eval η, r.eval η, hA⟩
  let ρ : SecondOrderInterpretation.assignment_l ℳ [] := fun v => nomatch v
  let τ : SecondOrderInterpretation.assignment_l ℳ [.set] := fun v => match v with | .here => C
  rw [formula_m, SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l η
      (Automation.RelationalTranslation.argumentsSubstitution (.cons r (.cons A .nil))) =
      SecondOrderInterpretation.target_l ρ τ := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      match v with
      | .here => rfl
      | .there .here => rfl
  rw [hEnv, SecondOrderInterpretation.form_l hℳ source_m ρ τ]
  rw [source_m, PowerlessNaturalOrder.transitive_formula_l]
  change (∀ x z : SecondOrderQuotient.type_l hℳ,
    SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ C) →
    SecondOrderQuotient.mem_l hℳ z x → SecondOrderQuotient.mem_l hℳ z (SecondOrderQuotient.mk_l hℳ C)) ↔ _
  constructor
  · intro h X Z hx hz
    exact h (SecondOrderQuotient.mk_l hℳ X) (SecondOrderQuotient.mk_l hℳ Z) hx hz
  · intro h x z hx hz
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
    exact h X Z hx hz

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphTransitivityFormula
