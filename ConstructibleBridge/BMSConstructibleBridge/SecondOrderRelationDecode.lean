import BMSConstructibleBridge.SecondOrderOmegaSyntax

/-!
# 内部自然数关系对象的数图解码

直接理解原有序对成员公式的图翻译，得到模型内部关系实数。没有把全部外部
二元关系收入模型，也没有将模型内的 ω 元素替换成标准自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationDecode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderInterpretation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private def source : Formula ℒ [] [.set, .set, .set] :=
  SecondOrderObjectSyntax.value_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))

private def bind : Substitution signature_m [] [.num, .set, .num, .set, .num, .set]
    [] [.num, .num, .num, .set, .set] :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .fvar (.there (.there .here))
    | .there .here => .fvar (.there (.there (.there .here)))
    | .there (.there .here) => .fvar .here
    | .there (.there (.there .here)) => .fvar (.there (.there (.there (.there .here))))
    | .there (.there (.there (.there .here))) => .fvar (.there .here)
    | .there (.there (.there (.there (.there .here)))) => .fvar (.there (.there (.there (.there .here)))))

/-- 自由槽位为两个模型数、关系对象根、关系对象实数、自然数图实数。 -/
def formula_m : Formula signature_m [] [.num, .num, .num, .set, .set] :=
  (GraphTranslation.form_m source).substitute bind

theorem pure_m : language_m formula_m = true := by
  refine (SecondOrderSubstitution.form_subst_m (GraphTranslation.form_m source) _ _ ?_ ?_).trans
    (GraphTranslation.form_pure_m source)
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here | .there .here | .there (.there .here) | .there (.there (.there .here)) |
      .there (.there (.there (.there .here))) | .there (.there (.there (.there (.there .here)))) => rfl

theorem formula_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (A : SecondOrderGraph.code_l ℳ) (a b : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree R).pushFree A.real).pushFree A.root).pushFree b).pushFree a)
      formula_m ↔ SecondOrderFunctionObjects.value_l hℳ (SecondOrderQuotient.mk_l hℳ A)
        (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR a))
        (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR b)) := by
  let ρ : assignment_l ℳ [] := fun v => nomatch v
  let τ : assignment_l ℳ [.set, .set, .set] := fun v => match v with
    | .here => A
    | .there .here => SecondOrderNaturalGraph.code_l hℳ R hR a
    | .there (.there .here) => SecondOrderNaturalGraph.code_l hℳ R hR b
  have h : Formula.satisfies
      ((((((Env.empty (M := ℳ)).pushFree R).pushFree A.real).pushFree A.root).pushFree b).pushFree a)
      formula_m ↔ Formula.satisfies (target_l ρ τ) (GraphTranslation.form_m source) := by
    refine (Formula.satisfies_substitute _ bind (GraphTranslation.form_m source)).trans ?_
    apply Iff.of_eq
    apply congrArg (fun η => Formula.satisfies η (GraphTranslation.form_m source))
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      match v with
      | .here | .there .here | .there (.there .here) | .there (.there (.there .here)) |
        .there (.there (.there (.there .here))) | .there (.there (.there (.there (.there .here)))) => rfl
  refine h.trans ((SecondOrderInterpretation.form_l hℳ source ρ τ).trans ?_)
  exact SecondOrderObjectSyntax.value_l hℳ (source_l hℳ ρ τ) _ _ _

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (A : SecondOrderGraph.code_l ℳ) :
    ∃ S : set_l ℳ, ∀ a b, relation_l S a b ↔
      SecondOrderFunctionObjects.value_l hℳ (SecondOrderQuotient.mk_l hℳ A)
        (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR a))
        (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR b)) := by
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m
    ((((Env.empty (M := ℳ)).pushFree R).pushFree A.real).pushFree A.root)
  exact ⟨S, fun a b => (hS a b).trans (formula_l hℳ R hR A a b)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelationDecode
