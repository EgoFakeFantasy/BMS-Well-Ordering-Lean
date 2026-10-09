import BMSConstructibleBridge.PowerlessMemberDefArithmeticSemantics

/-! # Def 算术证书的逐参数读取

七个实数代表及成员对应全部显式传入；不从存在命题中制造宿主选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefPacketSemantics

open Logic FirstOrder PowerlessBMSQuotientCoding PowerlessBMSQuotientArithmetic

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l PowerlessBMSQuotientPureTransfer.arithmeticStructure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z V E D Q R T F : Term ℒ Γ Δ .set)
    (aV aE aD aQ aR aT aF : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
    (v e d q r t f : SecondOrderModel.set_l ℳ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hV : V.eval η = aV.val) (hE : E.eval η = aE.val) (hD : D.eval η = aD.val)
    (hQ : Q.eval η = aQ.val) (hR : R.eval η = aR.val) (hT : T.eval η = aT.val) (hF : F.eval η = aF.val)
    (hv : setRel_l C aV v) (he : setRel_l C aE e) (hd : setRel_l C aD d)
    (hq : setRel_l C aQ q) (hr : setRel_l C aR r) (ht : setRel_l C aT t) (hf : setRel_l C aF f) :
    (PowerlessMemberDefSyntax.packet_m w z V E D Q R T F).satisfies η ↔
      SecondOrderInternalFormulaSyntax.spec_l v ∧ SecondOrderBinaryPowers.spec_l e ∧
      (∀ n, SecondOrderModel.mem_l n d) ∧ SecondOrderEvaluationEquations.spec_l e d q r t ∧
      SecondOrderDefinableFamily.spec_l e d t f := by
  let ξ : Env (PowerlessBMSQuotientTranslation.arithmetic_l C) [] [.set, .set, .set, .set, .set, .set, .set] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => aV
      | .there .here => aE
      | .there (.there .here) => aD
      | .there (.there (.there .here)) => aQ
      | .there (.there (.there (.there .here))) => aR
      | .there (.there (.there (.there (.there .here)))) => aT
      | .there (.there (.there (.there (.there (.there .here))))) => aF }
  let ξ' := ((((((((Env.empty (M := ℳ)).pushFree f).pushFree t).pushFree r).pushFree q).pushFree d).pushFree e).pushFree v)
  apply PowerlessMemberDefArithmeticSemantics.packet_formula_l C η w z V E D Q R T F ξ ξ' hw hz
  · intro s b
    exact match b with
      | .here => hV
      | .there .here => hE
      | .there (.there .here) => hD
      | .there (.there (.there .here)) => hQ
      | .there (.there (.there (.there .here))) => hR
      | .there (.there (.there (.there (.there .here)))) => hT
      | .there (.there (.there (.there (.there (.there .here))))) => hF
  · constructor
    · intro s b
      nomatch b
    · intro s b
      exact match b with
        | .here => hv
        | .there .here => he
        | .there (.there .here) => hd
        | .there (.there (.there .here)) => hq
        | .there (.there (.there (.there .here))) => hr
        | .there (.there (.there (.there (.there .here)))) => ht
        | .there (.there (.there (.there (.there (.there .here))))) => hf

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefPacketSemantics
