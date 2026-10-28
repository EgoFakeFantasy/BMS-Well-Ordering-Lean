import BMSConstructibleBridge.PowerlessMemberDefSyntax
import BMSConstructibleBridge.PowerlessBMSQuotientParameterTransfer

/-!
# Def 纯公式中算术原子的精确读取

用实际 ω 子集与原实数的成员对应读取关系边。配数沿既有无额外函数符号
翻译求值，不将纯集合中的有序对与自然数配数混同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefArithmeticSemantics

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessArithmeticTerms PowerlessBMSQuotientTranslation
open PowerlessBMSQuotientArithmetic

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l PowerlessBMSQuotientPureTransfer.arithmeticStructure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem edge_formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z Q n m : Term ℒ Γ Δ .set)
    (A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
    (R : SecondOrderModel.set_l ℳ) (a b : SecondOrderModel.num_l ℳ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hQ : Q.eval η = A.val) (hn : n.eval η = (numberCode_l C a).val)
    (hm : m.eval η = (numberCode_l C b).val) (hA : setRel_l C A R) :
    (PowerlessMemberDefSyntax.edge_m w z Q n m).satisfies η ↔ SecondOrderPairing.relation_l R a b := by
  let ξ : Env (arithmetic_l C) [] [.num, .num, .set] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => numberCode_l C a
      | .there .here => numberCode_l C b
      | .there (.there .here) => A }
  let ξ' := (((Env.empty (M := ℳ)).pushFree R).pushFree b).pushFree a
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num, .set] :=
    GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let τ : assignment_m [.num, .num, .set] Γ Δ := fun v => match v with
    | .here => n
    | .there .here => m
    | .there (.there .here) => Q
  have hτ : agrees_l η τ ξ.freeVal := by
    intro s v
    cases v with
    | here => exact hn
    | there v => cases v with
      | here => exact hm
      | there v => cases v with
        | here => exact hQ
        | there v => nomatch v
  have hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l C) ξ ξ' := by
    constructor
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => exact numberEquiv_numberCode_l C a
      | there v => cases v with
        | here => exact numberEquiv_numberCode_l C b
        | there v => cases v with
          | here => exact hA
          | there v => nomatch v
  exact (PowerlessBMSQuotientParameterTransfer.formula_l C φ
    (SecondOrderArithmetic.pure_language_m _ rfl) ξ ξ' η w z (fun v => nomatch v) τ hw hz
    (fun v => nomatch v) hτ hRelated).trans (SecondOrderPairing.edge_l ξ' _ _ _)

theorem legal_formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z V E i : Term ℒ Γ Δ .set)
    (ξ : Env (arithmetic_l C) [] [.num, .set, .set]) (ξ' : Env ℳ [] [.num, .set, .set])
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hτ : agrees_l η (PowerlessMemberDefSyntax.legal_parameters_m V E i) ξ.freeVal)
    (hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l C) ξ ξ') :
    (PowerlessMemberDefSyntax.legal_m w z V E i).satisfies η ↔
      SecondOrderLegalFormulaIndex.spec_l (ξ'.freeVal (.there .here))
        (ξ'.freeVal (.there (.there .here))) (ξ'.freeVal .here) :=
  (PowerlessBMSQuotientParameterTransfer.formula_l C SecondOrderLegalFormulaIndex.formula_m
    SecondOrderLegalFormulaIndex.pure_m ξ ξ' η w z (fun v => nomatch v)
    (PowerlessMemberDefSyntax.legal_parameters_m V E i) hw hz (fun v => nomatch v) hτ hRelated).trans
    (SecondOrderLegalFormulaIndex.formula_l ξ')

theorem packet_formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z V E D Q R T F : Term ℒ Γ Δ .set)
    (ξ : Env (arithmetic_l C) [] [.set, .set, .set, .set, .set, .set, .set])
    (ξ' : Env ℳ [] [.set, .set, .set, .set, .set, .set, .set])
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hτ : agrees_l η (PowerlessMemberDefSyntax.packet_parameters_m V E D Q R T F) ξ.freeVal)
    (hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l C) ξ ξ') :
    (PowerlessMemberDefSyntax.packet_m w z V E D Q R T F).satisfies η ↔
      SecondOrderInternalFormulaSyntax.spec_l (ξ'.freeVal .here) ∧
      SecondOrderBinaryPowers.spec_l (ξ'.freeVal (.there .here)) ∧
      (∀ n, SecondOrderModel.mem_l n (ξ'.freeVal (.there (.there .here)))) ∧
      SecondOrderEvaluationEquations.spec_l (ξ'.freeVal (.there .here))
        (ξ'.freeVal (.there (.there .here))) (ξ'.freeVal (.there (.there (.there .here))))
        (ξ'.freeVal (.there (.there (.there (.there .here)))))
        (ξ'.freeVal (.there (.there (.there (.there (.there .here)))))) ∧
      SecondOrderDefinableFamily.spec_l (ξ'.freeVal (.there .here)) (ξ'.freeVal (.there (.there .here)))
        (ξ'.freeVal (.there (.there (.there (.there (.there .here))))))
        (ξ'.freeVal (.there (.there (.there (.there (.there (.there .here))))))) :=
  (PowerlessBMSQuotientParameterTransfer.formula_l C SecondOrderMemberDefArithmetic.formula_m
    SecondOrderMemberDefArithmetic.pure_m ξ ξ' η w z (fun v => nomatch v)
    (PowerlessMemberDefSyntax.packet_parameters_m V E D Q R T F) hw hz
    (fun v => nomatch v) hτ hRelated).trans
    (SecondOrderMemberDefArithmetic.packet_formula_l ξ' (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here))))))))

/-- 合法索引读取的逐参数接口；实数代表只作为命题见证传入。 -/
theorem legal_read_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z V E i : Term ℒ Γ Δ .set)
    (A B : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
    (v e : SecondOrderModel.set_l ℳ) (a : SecondOrderModel.num_l ℳ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hV : V.eval η = A.val) (hE : E.eval η = B.val) (hi : i.eval η = (numberCode_l C a).val)
    (hA : setRel_l C A v) (hB : setRel_l C B e) :
    (PowerlessMemberDefSyntax.legal_m w z V E i).satisfies η ↔
      SecondOrderLegalFormulaIndex.spec_l v e a := by
  let ξ : Env (arithmetic_l C) [] [.num, .set, .set] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => numberCode_l C a
      | .there .here => A
      | .there (.there .here) => B }
  let ξ' := (((Env.empty (M := ℳ)).pushFree e).pushFree v).pushFree a
  apply legal_formula_l C η w z V E i ξ ξ' hw hz
  · intro s t
    cases t with
    | here => exact hi
    | there t => cases t with
      | here => exact hV
      | there t => cases t with
        | here => exact hE
        | there t => nomatch t
  · constructor
    · intro s t
      nomatch t
    · intro s t
      cases t with
      | here => exact numberEquiv_numberCode_l C a
      | there t => cases t with
        | here => exact hA
        | there t => cases t with
          | here => exact hB
          | there t => nomatch t

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefArithmeticSemantics
