import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailCofinal
import BMSConstructibleBridge.SecondOrderOrdinalLimitDerives

/-! # 原 Z₂ 中任意序数上方的共尾极限

对实际根清除无效边，再使用内部 ω² 尾的完整集合包络。输出既是非零
极限，又有严格较早的非零极限共尾；不把普通极限性冒充共尾性。
纯隶属闭句经原图翻译给出普通 Derives，无 Collection 或外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalCofinalDerives

open Logic FirstOrder
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (a : type_l hℳ) (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) a) :
    ∃ c : type_l hℳ, SetTheory.Structure.IsOrdinal (quotient_l hℳ) c ∧ mem_l hℳ a c ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ c ∧
      PowerlessRelativeCofinalLimitBounds.cofinal_l c := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨S, hS⟩ := SecondOrderValidRootGraph.exists_l hℳ A.real
  have hW := SecondOrderValidRootGraph.wf_l hS
  have hEq : mk_l hℳ A = mk_l hℳ ⟨S, A.root, hW A.root⟩ :=
    (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hS A.root A.wf)
  obtain ⟨G, hG⟩ := SecondOrderOrdinalDoubleTailGraph.exists_l hℳ S A.root
  obtain ⟨C, hC⟩ := SecondOrderOrdinalDoubleTailRange.exists_l hℳ hG hW
  have hα' : SetTheory.Structure.IsOrdinal (quotient_l hℳ)
      (SecondOrderOrdinalDoubleTailOrder.base_l hℳ hW A.root) := by
    change SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ ⟨S, A.root, hW A.root⟩)
    exact hEq ▸ hα
  obtain ⟨hOrd, hMem, hLimit, hCofinal⟩ :=
    SecondOrderOrdinalDoubleTailCofinal.properties_l hℳ hG hW hα' C hC
  change mem_l hℳ (mk_l hℳ ⟨S, A.root, hW A.root⟩) (mk_l hℳ C) at hMem
  exact ⟨mk_l hℳ C, hOrd, hEq.symm ▸ hMem, hLimit, hCofinal⟩

def schema_m : Formula ℒ [] [.set] :=
  .imp (PowerlessRelativeHierarchySyntax.ordinal_m (.fvar .here)) <|
    .existsE .set <|
      .conj (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here)) <|
        .conj (SecondOrderObjectSyntax.member_m (.fvar .here) (.bvar .here)) <|
          .conj (PowerlessRelativeHierarchySyntax.limit_m (.bvar .here))
            (PowerlessRelativeCofinalLimitBounds.cofinal_m (.bvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeCofinalLimitBounds.cofinal_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval]
  exact fun η hα => exists_l hℳ (η.freeVal .here) hα

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalCofinalDerives
