import BMSConstructibleBridge.PowerlessRelativeClassLegacyImageDefClosure
import BMSConstructibleBridge.PowerlessMemberDefDerives
import BMSConstructibleBridge.SecondOrderAxioms

/-! # 任意实际 Class 母集的原 Def 闭包：原 Z₂ 推导

纯隶属对象句子保留原 global_m，不改写 Def 的枚举、编码或求值规格。
背景为原 num/set 语言中的 SecondOrderArithmetic.theory_m，正式出口是
同一 GraphTranslation 下的 Derives。唯一输入是基集传递、A 属于实际
Class 和原 Def(A,H)；没有类内计数或类内枚举前提。

闭包针对全部原商对象。它不把 Class 成员性加强为某个截断层的成员性，
不构造长前史或统一枚举族，也不是固定高度 BMS 良序的终局推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassImageDefClosureDerives

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 三个自由参数依次为 H、A、B；不加入枚举或可数性守卫。 -/
def schema_m : Formula ℒ [] [.set, .set, .set] :=
  let H : Term ℒ [] [.set, .set, .set] .set := .fvar .here
  let A := .fvar (.there .here)
  let B := .fvar (.there (.there .here))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (PowerlessMemberDefSyntax.global_m A H)
        (PowerlessRelativeHierarchySyntax.class_m B H)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessMemberDefDerives.formula_l K, Term.eval]
  intro η hBase hA hDef
  exact PowerlessRelativeClassLegacyImageDefClosure.class_l hBase hA hDef

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassImageDefClosureDerives
