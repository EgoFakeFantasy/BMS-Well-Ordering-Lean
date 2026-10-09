import BMSConstructibleBridge.SecondOrderRelativeLevel
import BMSConstructibleBridge.SecondOrderRootPresentationFormula
import BMSConstructibleBridge.SecondOrderGraphOrdinalFormula

/-! # 相对层值证书的对象矩阵

母序数图、根、完整呈现、强历史、阶段索引与输出行全部显式绑定。输入和
输出可以使用不同关系图；商相等由原双模拟公式表达。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelBody

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def formula_m {Γ Δ : SortContext signature_m}
    (B α C A Q D R S W : Term signature_m Γ Δ .set) (rα rC r n : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .conj (GraphTranslation.domain_m A r) <|
    .conj (SecondOrderGraphOrdinalFormula.formula_m A r) <|
    .conj (SecondOrderRootPresentationFormula.formula_m A r Q D R) <|
    .conj (SecondOrderRelativeHierarchyStrongFormula.formula_m B R S) <|
    .conj (.rel .mem (.cons n (.cons D .nil))) <|
    .conj (GraphTranslation.atom_m GraphSyntax.eq_m α A rα n) <|
    .conj (SecondOrderSections.formula_m S W n)
      (GraphTranslation.atom_m GraphSyntax.eq_m C W rC (Term.app (σ := signature_m) .zero .nil))

theorem pure_m {Γ Δ : SortContext signature_m}
    (B α C A Q D R S W : Term signature_m Γ Δ .set) (rα rC r n : Term signature_m Γ Δ .num)
    (hB : pure_term_m B = true) (hα : pure_term_m α = true) (hC : pure_term_m C = true)
    (hA : pure_term_m A = true) (hQ : pure_term_m Q = true) (hD : pure_term_m D = true)
    (hR : pure_term_m R = true) (hS : pure_term_m S = true) (hW : pure_term_m W = true)
    (hrα : pure_term_m rα = true) (hrC : pure_term_m rC = true)
    (hr : pure_term_m r = true) (hn : pure_term_m n = true) :
    language_m (formula_m B α C A Q D R S W rα rC r n) = true := by
  have hEq := pure_language_m GraphSyntax.matrix_m GraphSyntax.matrix_pure_m
  have hMember : language_m (Γ := Γ) (Δ := Δ)
      (.rel .mem (.cons n (.cons D .nil))) = true := by
    change (pure_term_m n && (pure_term_m D && true)) = true
    rw [hn, hD]
    rfl
  exact SecondOrderFormulaArguments.conj_pure_m _ _ (GraphTranslation.domain_pure_m A r hA hr)
    (SecondOrderFormulaArguments.conj_pure_m _ _ (SecondOrderGraphOrdinalFormula.pure_m A r hA hr)
      (SecondOrderFormulaArguments.conj_pure_m _ _ (SecondOrderRootPresentationFormula.pure_m A r Q D R hA hr hQ hD hR)
        (SecondOrderFormulaArguments.conj_pure_m _ _ (SecondOrderRelativeHierarchyStrongFormula.pure_m B R S hB hR hS)
          (SecondOrderFormulaArguments.conj_pure_m _ _ hMember
            (SecondOrderFormulaArguments.conj_pure_m _ _ (GraphTranslation.atom_pure_m _ α A rα n hEq hα hA hrα hn)
              (SecondOrderFormulaArguments.conj_pure_m _ _ (SecondOrderSections.pure_m S W n hS hW hn)
                (GraphTranslation.atom_pure_m _ C W rC (Term.app (σ := signature_m) .zero .nil) hEq hC hW hrC rfl)))))))

theorem formula_l (hℳ : Theory.Models ℳ theory_m) {Γ Δ : SortContext signature_m}
    (η : Env ℳ Γ Δ) (B α C A Q D R S W : Term signature_m Γ Δ .set)
    (rα rC r n : Term signature_m Γ Δ .num)
    (hB : SecondOrderDomain.wf_l (B.eval η) (zero_l ℳ)) :
    (formula_m B α C A Q D R S W rα rC r n).satisfies η ↔
    ∃ hA : SecondOrderDomain.wf_l (A.eval η) (r.eval η),
      SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
        (SecondOrderQuotient.mk_l hℳ ⟨A.eval η, r.eval η, hA⟩) ∧
      SecondOrderOrdinalHierarchy.presentation_l ⟨A.eval η, r.eval η, hA⟩ (Q.eval η) (D.eval η) (R.eval η) ∧
      SecondOrderRelativeHierarchyStrongTheorem.spec_l (B.eval η) (R.eval η) (S.eval η) hB ∧
      mem_l (n.eval η) (D.eval η) ∧
      SecondOrderBisimulation.eq_l (α.eval η) (A.eval η) (rα.eval η) (n.eval η) ∧
      SecondOrderSections.spec_l (S.eval η) (n.eval η) (W.eval η) ∧
      SecondOrderBisimulation.eq_l (C.eval η) (W.eval η) (rC.eval η) (zero_l ℳ) := by
  constructor
  · intro h
    have hA := (SecondOrderInterpretation.domain_l η A r).mp h.1
    refine ⟨hA, (SecondOrderGraphOrdinalFormula.formula_l hℳ η A r hA).mp h.2.1,
      (SecondOrderRootPresentationFormula.formula_l η A r Q D R hA).mp h.2.2.1,
      (SecondOrderRelativeHierarchyStrongTheorem.formula_l hℳ η B R S hB).mp h.2.2.2.1, ?_⟩
    refine ⟨h.2.2.2.2.1, (SecondOrderInterpretation.eq_l η α A rα n).mp h.2.2.2.2.2.1,
      (SecondOrderSections.formula_l η S W n).mp h.2.2.2.2.2.2.1,
      (SecondOrderInterpretation.eq_l η C W rC (Term.app (σ := signature_m) .zero .nil)).mp h.2.2.2.2.2.2.2⟩
  · rintro ⟨hA, hOrd, hP, hHistory, hn, hαn, hRow, hOutput⟩
    refine ⟨(SecondOrderInterpretation.domain_l η A r).mpr hA,
      (SecondOrderGraphOrdinalFormula.formula_l hℳ η A r hA).mpr hOrd,
      (SecondOrderRootPresentationFormula.formula_l η A r Q D R hA).mpr hP,
      (SecondOrderRelativeHierarchyStrongTheorem.formula_l hℳ η B R S hB).mpr hHistory, ?_⟩
    exact ⟨hn, (SecondOrderInterpretation.eq_l η α A rα n).mpr hαn,
      (SecondOrderSections.formula_l η S W n).mpr hRow,
      (SecondOrderInterpretation.eq_l η C W rC (Term.app (σ := signature_m) .zero .nil)).mpr hOutput⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelBody
