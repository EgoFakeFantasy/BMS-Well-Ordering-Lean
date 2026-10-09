import BMSConstructibleBridge.PowerlessRelativeClassOrdinalAbsolute

/-! # 原 Z₂ 中类序数绝对性的正式对象句

对实际传递基 B 及原 Class 元素 α，比较同一个原 ordinal AST 的
类量词相对化与 raw 求值。句子不添加完整 Class 理论、子集覆盖或
外部良基性前提；其正式证明回到原 num/set 推导核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalAbsoluteDerives

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private def ordinal_m : Formula ℒ [] [.set] :=
  PowerlessRelativeHierarchySyntax.ordinal_m (.fvar .here)

def schema_m : Formula ℒ [] [.set, .set] :=
  let B : Term ℒ [] [.set, .set] .set := .fvar .here
  let α := .fvar (.there .here)
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B α) <|
      .iff (PowerlessRelativeClassRelativization.formula_m ordinal_m)
        (PowerlessRelativeHierarchySyntax.ordinal_m α)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, Term.eval]
  intro hBase hα
  let α : PowerlessRelativeClassStructure.type_l hℳ (η.freeVal .here) :=
    ⟨η.freeVal (.there .here), hα⟩
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (η.freeVal .here) hBase) [] [.set] :=
    Env.empty |>.pushFree α
  have hEnv : (PowerlessRelativeClassRelativization.env_l ξ).pushFree (η.freeVal .here) = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => nomatch v
  have hClass := PowerlessRelativeClassRelativization.formula_l K ordinal_m ξ
  rw [hEnv] at hClass
  have hOrdinal := PowerlessRelativeClassOrdinalAbsolute.ordinal_l (hBase := hBase) α
  have hRead := PowerlessMemberOrdinalAbsolute.formula_l
    (PowerlessRelativeClassStructure.ext_l hℳ (η.freeVal .here) hBase) ξ (.fvar .here)
  have hRaw := PowerlessRelativeHierarchySemantics.ordinal_formula_l
    (hℳ := hℳ) η (.fvar (.there .here))
  exact hClass.trans (hRead.trans (hOrdinal.trans hRaw.symm))

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalAbsoluteDerives
