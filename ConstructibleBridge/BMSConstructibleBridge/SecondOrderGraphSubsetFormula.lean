import BMSConstructibleBridge.SecondOrderFormulaArguments
import BMSConstructibleBridge.SecondOrderTransitiveSuperset
import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 两个有效图根的对象子集公式

实际纯隶属子集 AST 的图翻译。成员比较经过同一原图商，不比较任意图的
裸边，也不为商对象抽取代表选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphSubsetFormula

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  GraphTranslation.context_m

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def subset_l (A B : SecondOrderGraph.code_l ℳ) : Prop :=
  ∀ X, SecondOrderGraph.mem_l X A → SecondOrderGraph.mem_l X B

def source_m : Formula ℒ [] [.set, .set] :=
  ThirdOrderTheory.subset_m (.fvar .here) (.fvar (.there .here))

def formula_m {Γ Δ : SortContext signature_m} (A B : Term signature_m Γ Δ .set)
    (a b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  SecondOrderFormulaArguments.formula_m (GraphTranslation.form_m source_m)
    (.cons a (.cons A (.cons b (.cons B .nil))))

theorem pure_m {Γ Δ : SortContext signature_m} (A B : Term signature_m Γ Δ .set)
    (a b : Term signature_m Γ Δ .num) (hA : pure_term_m A = true) (hB : pure_term_m B = true)
    (ha : pure_term_m a = true) (hb : pure_term_m b = true) : language_m (formula_m A B a b) = true := by
  apply SecondOrderFormulaArguments.pure_m _ _ (GraphTranslation.form_pure_m source_m)
  simp only [pure_args_m, hA, hB, ha, hb]
  rfl

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (A B : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num)
    (hA : SecondOrderDomain.wf_l (A.eval η) (a.eval η))
    (hB : SecondOrderDomain.wf_l (B.eval η) (b.eval η)) :
    (formula_m A B a b).satisfies η ↔ subset_l ⟨A.eval η, a.eval η, hA⟩ ⟨B.eval η, b.eval η, hB⟩ := by
  let C : SecondOrderGraph.code_l ℳ := ⟨A.eval η, a.eval η, hA⟩
  let D : SecondOrderGraph.code_l ℳ := ⟨B.eval η, b.eval η, hB⟩
  let ρ : SecondOrderInterpretation.assignment_l ℳ [] := fun v => nomatch v
  let τ : SecondOrderInterpretation.assignment_l ℳ [.set, .set] :=
    fun v => match v with | .here => C | .there .here => D
  rw [formula_m, SecondOrderFormulaArguments.formula_l]
  have hEnv : SecondOrderRelationSpecification.parameters_l η
      (Automation.RelationalTranslation.argumentsSubstitution (.cons a (.cons A (.cons b (.cons B .nil))))) =
      SecondOrderInterpretation.target_l ρ τ := by
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match v with
      | .here => rfl
      | .there .here => rfl
      | .there (.there .here) => rfl
      | .there (.there (.there .here)) => rfl
  rw [hEnv, SecondOrderInterpretation.form_l hℳ source_m ρ τ,
    source_m, ThirdOrderSemantics.subset_formula_l]
  change (∀ x : SecondOrderQuotient.type_l hℳ,
    SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ C) →
    SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ D)) ↔ _
  constructor
  · intro h X hx
    exact h (SecondOrderQuotient.mk_l hℳ X) hx
  · intro h x hx
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    exact h X hx

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraphSubsetFormula
