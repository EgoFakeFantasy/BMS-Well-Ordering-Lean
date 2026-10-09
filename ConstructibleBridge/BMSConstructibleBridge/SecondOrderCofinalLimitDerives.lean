import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailCofinal
import BMSConstructibleBridge.SecondOrderOrdinalLimitDerives

/-! # 原 Z₂ 可推导的共尾非零极限阶段存在

先清理任意代表图，再用内部 ω² 尾包络构造严格更大的序数，其中非零极限
阶段共尾。实际纯闭句经原图翻译及已核验解释接口返回原推导核；共尾性
是结论而非新增对象公理。本定理尚不是最终 BMS 良序句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCofinalLimitDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeHierarchySemantics (limit_l)
open PowerlessRelativeCofinalLimitBounds (cofinal_l cofinal_m cofinal_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (a : type_l hℳ)
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) a) :
    ∃ β : type_l hℳ, SetTheory.Structure.IsOrdinal (quotient_l hℳ) β ∧
      mem_l hℳ a β ∧ limit_l hℳ β ∧ cofinal_l β := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨S, hS⟩ := SecondOrderValidRootGraph.exists_l hℳ A.real
  have hW := SecondOrderValidRootGraph.wf_l hS
  have hEq : mk_l hℳ A = mk_l hℳ ⟨S, A.root, hW A.root⟩ :=
    (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hS A.root A.wf)
  obtain ⟨G, hG⟩ := SecondOrderOrdinalDoubleTailGraph.exists_l hℳ S A.root
  obtain ⟨C, hC⟩ := SecondOrderOrdinalDoubleTailRange.exists_l hℳ hG hW
  have hα' : SetTheory.Structure.IsOrdinal (quotient_l hℳ) (mk_l hℳ ⟨S, A.root, hW A.root⟩) :=
    hEq ▸ hα
  obtain ⟨hOrd, hMem, hLimit, hCofinal⟩ := SecondOrderOrdinalDoubleTailCofinal.properties_l
    hℳ hG hW hα' C hC
  exact ⟨mk_l hℳ C, hOrd, hEq.symm ▸ hMem, hLimit, hCofinal⟩

def sentence_m : Sentence ℒ := .forallE .set
  (.imp (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here))
    (.existsE .set (.conj (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here))
      (.conj (member_m (.bvar (.there .here)) (.bvar .here))
        (.conj (PowerlessRelativeHierarchySyntax.limit_m (.bvar .here))
          (cofinal_m (.bvar .here)))))))

theorem models_l (hℳ : Theory.Models ℳ theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l, cofinal_formula_l,
    member_m, Arguments.eval, Term.eval]
  exact exists_l hℳ

theorem derives_m : Derives theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCofinalLimitDerives
