import BMSConstructibleBridge.SecondOrderOrdinalTailLimit
import BMSConstructibleBridge.SecondOrderAxioms
import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics

/-! # 原 Z₂ 可推导的序数上方非零极限存在

对任意有效根先删除无效父根的边，再添加内部 ω 尾及其成员包络。
纯集合论闭句经已核验的图翻译与原签名完备性回传；不调用 Collection。
这只是层级闭包的前置定理，不是 BMS 良序终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalLimitDerives

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic
open SecondOrderQuotient (type_l mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (a : type_l hℳ)
    (hα : SetTheory.Structure.IsOrdinal (quotient_l hℳ) a) :
    ∃ c : type_l hℳ, SetTheory.Structure.IsOrdinal (quotient_l hℳ) c ∧ mem_l hℳ a c ∧
      ∀ x : type_l hℳ, mem_l hℳ x c → ∃ y : type_l hℳ, mem_l hℳ y c ∧ mem_l hℳ x y := by
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  obtain ⟨S, hS⟩ := SecondOrderValidRootGraph.exists_l hℳ A.real
  have hW := SecondOrderValidRootGraph.wf_l hS
  have hEq : mk_l hℳ A = mk_l hℳ ⟨S, A.root, hW A.root⟩ :=
    (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hS A.root A.wf)
  obtain ⟨G, hG⟩ := SecondOrderOrdinalTailGraph.exists_l hℳ S A.root
  obtain ⟨C, hC⟩ := SecondOrderOrdinalTailRange.exists_l hℳ hG hW
  obtain ⟨hOrd, hMem, hLimit⟩ := SecondOrderOrdinalTailLimit.properties_l hℳ hG hW
    (hEq ▸ hα) C hC
  exact ⟨mk_l hℳ C, hOrd, hEq.symm ▸ hMem, hLimit⟩

/-- 在任意上下文中嵌入上游完整序数公式，不替换为需额外理论的简化判据。 -/
abbrev ordinal_m := @PowerlessRelativeHierarchySyntax.ordinal_m

theorem ordinal_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (a : Term ℒ Γ Δ .set) :
    (ordinal_m a).satisfies η ↔ SetTheory.Structure.IsOrdinal (quotient_l hℳ) (a.eval η) :=
  PowerlessRelativeHierarchySemantics.ordinal_formula_l η a

def sentence_m : Sentence ℒ := .forallE .set (.imp (ordinal_m (.bvar .here))
  (.existsE .set (.conj (ordinal_m (.bvar .here)) (.conj
    (.rel .membership (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil)))
    (.forallE .set (.imp
      (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there .here)) .nil)))
      (.existsE .set (.conj
        (.rel .membership (.cons (.bvar .here) (.cons (.bvar (.there (.there .here))) .nil)))
        (.rel .membership (.cons (.bvar (.there .here)) (.cons (.bvar .here) .nil)))))))))))

theorem models_l (hℳ : Theory.Models ℳ theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, ordinal_l hℳ]
  exact exists_l hℳ

theorem derives_m : Derives theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalLimitDerives
