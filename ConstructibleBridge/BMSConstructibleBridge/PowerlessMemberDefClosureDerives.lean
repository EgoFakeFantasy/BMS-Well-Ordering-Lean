import BMSConstructibleBridge.PowerlessMemberDefDerives
import BMSConstructibleBridge.SecondOrderMemberDefProperties

/-! # 原 Z₂ 中的 Def 传递闭包性质

母集属于 Def；传递母集的成员保留，且 Def 仍传递。每项性质都封装成
纯集合闭句并经同一图翻译取得原对象推导，不停留在商结构语义层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefClosureDerives

open Logic FirstOrder SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def transitive_m {Γ Δ : SortContext ℒ} (X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .imp
    (member_m (.bvar (.there .here)) (up (up X))) <| .imp
      (member_m (.bvar .here) (.bvar (.there .here))) (member_m (.bvar .here) (up (up X)))

theorem transitive_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ Γ Δ) (X : Term ℒ Γ Δ .set) : (transitive_m X).satisfies η ↔
      ∀ x z, ThirdOrderSemantics.member_l ℳ x (X.eval η) →
        ThirdOrderSemantics.member_l ℳ z x → ThirdOrderSemantics.member_l ℳ z (X.eval η) := by
  simp only [transitive_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    Term.eval_weakenBound]
  rfl

def sentence_m : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .imp
    (PowerlessMemberDefSyntax.global_m (.bvar (.there .here)) (.bvar .here)) <|
      .conj (member_m (.bvar (.there .here)) (.bvar .here)) <|
        .imp (transitive_m (.bvar (.there .here))) <|
          .conj (ThirdOrderTheory.subset_m (.bvar (.there .here)) (.bvar .here))
            (transitive_m (.bvar .here))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  intro X Y hDef
  have h := (PowerlessMemberDefDerives.formula_l C _ (.bvar (.there .here)) (.bvar .here)).mp hDef
  refine ⟨SecondOrderMemberDefProperties.mother_member_l hℳ h, ?_⟩
  intro hTrans
  have ht := (transitive_formula_l _ (.bvar (.there .here))).mp hTrans
  constructor
  · apply (ThirdOrderSemantics.subset_formula_l _ (.bvar (.there .here)) (.bvar .here)).mpr
    exact SecondOrderMemberDefProperties.contains_l hℳ h ht
  · apply (transitive_formula_l _ (.bvar .here)).mpr
    exact SecondOrderMemberDefProperties.transitive_l hℳ h ht

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms transitive_formula_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefClosureDerives
