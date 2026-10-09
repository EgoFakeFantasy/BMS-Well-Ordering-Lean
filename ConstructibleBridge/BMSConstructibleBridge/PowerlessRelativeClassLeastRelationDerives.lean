import BMSConstructibleBridge.PowerlessRelativeClassLeastRelation
import BMSConstructibleBridge.PowerlessRelativeClassEnumerationWellOrder

/-! # 有界最小见证图的原 Z₂ 对象推导

输入关系图、见证母界及其环境良序均为实际 Class 对象。输出函数图的
Class 身份和全 raw 逐值规格在结论中取得；不存在共同母界的请求不在
此句的范围内。本文件不是 cutoff Collection 或最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLeastRelationDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def total_m {Γ Δ : SortContext ℒ} (A Y E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up A)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up (up Y)))
      (value_m (up (up E)) (.bvar (.there .here)) (.bvar .here))

def reading_m {Γ Δ : SortContext ℒ} (A Y E R J : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let x : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let y := .bvar .here
    let lift (t : Term ℒ Γ Δ .set) := up (up t)
    .iff (value_m (lift J) x y) <|
      .conj (member_m x (lift A)) <| .conj (member_m y (lift Y))
        (PowerlessRelativeClassLeastRelation.least_m (lift E) (lift R) (lift Y) x y)

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let A : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let Y := .fvar (.there .here)
  let E := .fvar (.there (.there .here))
  let R := .fvar (.there (.there (.there .here)))
  let B := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B Y) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B E) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
            .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m Y R) <|
              .imp (total_m A Y E) <| .existsE .set <|
                .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
                  .conj (map_m (.bvar .here) (up A) (up Y))
                    (reading_m (up A) (up Y) (up E) (up R) (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, total_m, reading_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, map_formula_l,
    value_formula_l, PowerlessRelativeClassLeastRelation.least_formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro η hBase hA hY hE hR hOrder hSome
  have hBase' : ∀ x, SecondOrderQuotient.mem_l hℳ x (η.freeVal (.there (.there (.there (.there .here))))) →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x →
        SecondOrderQuotient.mem_l hℳ y (η.freeVal (.there (.there (.there (.there .here))))) :=
    fun x hx y hy => hBase x hx y hy
  obtain ⟨J, hMap, hRead⟩ := PowerlessRelativeClassLeastRelation.exists_l (hBase := hBase')
    ⟨_, hA⟩ ⟨_, hY⟩ ⟨_, hE⟩ ⟨_, hR⟩ hOrder hSome
  exact ⟨J.val, J.property, hMap, hRead⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLeastRelationDerives
