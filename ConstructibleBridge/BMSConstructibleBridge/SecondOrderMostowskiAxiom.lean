import BMSConstructibleBridge.SecondOrderMostowski
import BMSConstructibleBridge.SecondOrderRelationSyntax
import BMSConstructibleBridge.SecondOrderCollapseSyntax

/-!
# MostColl 完整公理的二阶对象推导

源句子针对 ω 上任意正则关系，构造其定义域与值域之并、传递像及满射集合
函数，并要求递归方程。不增加外延性条件，也不把原关系换成仅有树的子类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMostowskiAxiom

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

def formula_m : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .imp
    (.conj (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here)))
      (.conj (SecondOrderRelationSyntax.relation_m (.bvar .here) (.bvar (.there .here)))
        (SecondOrderRelationSyntax.wellFounded_m (.bvar .here))))
    (.existsE .set (.existsE .set (.existsE .set (.conj
      (SecondOrderRelationSyntax.field_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))))
      (SecondOrderCollapseSyntax.formula_m (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) :
    formula_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  simp only [formula_m, Formula.TrueIn, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    SecondOrderRelationSyntax.relation_l, SecondOrderRelationSyntax.wellFounded_l,
    SecondOrderRelationSyntax.field_l, SecondOrderCollapseSyntax.formula_l]
  change ∀ o a : SecondOrderQuotient.type_l hℳ,
    SecondOrderOmega.omega_l hℳ o ∧ SecondOrderRegularRelation.relation_l hℳ a o ∧
      SecondOrderRegularRelation.wellFounded_l hℳ a →
    ∃ d u f, (∀ x, SecondOrderQuotient.mem_l hℳ x d ↔ SecondOrderRegularRelation.domain_l hℳ a x) ∧
      SecondOrderCollapseFunction.spec_l hℳ a d u f
  exact fun o a ⟨ho, hr, ha⟩ => SecondOrderMostowski.collapse_l hℳ a o ho hr ha

theorem derives_m : Derives theory_m [] (GraphTranslation.form_m formula_m) :=
  SecondOrderAxioms.interpretation_m formula_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMostowskiAxiom
