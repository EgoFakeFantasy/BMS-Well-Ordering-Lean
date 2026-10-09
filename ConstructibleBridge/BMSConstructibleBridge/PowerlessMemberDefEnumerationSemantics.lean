import BMSConstructibleBridge.PowerlessMemberDefCollectionSemantics
import BMSConstructibleBridge.PowerlessMemberDefPacketSemantics
import BMSConstructibleBridge.SecondOrderEnumeratedMemberDef

/-! # Def 枚举证书的纯语言对应

显式验证七个辅助对象都是实际 ω 的子集。母集、输出和枚举函数不受这项
实数域限制；它们仍是纯集合语言中的任意对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefEnumerationSemantics

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z X Y f V E D Q R T F : Term ℒ Γ Δ .set)
    (aV aE aD aQ aR aT aF : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
    (v e d q r t g : SecondOrderModel.set_l ℳ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hV : V.eval η = aV.val) (hE : E.eval η = aE.val) (hD : D.eval η = aD.val)
    (hQ : Q.eval η = aQ.val) (hR : R.eval η = aR.val) (hT : T.eval η = aT.val) (hF : F.eval η = aF.val)
    (hv : setRel_l C aV v) (he : setRel_l C aE e) (hd : setRel_l C aD d)
    (hq : setRel_l C aQ q) (hr : setRel_l C aR r) (ht : setRel_l C aT t) (hg : setRel_l C aF g) :
    (PowerlessMemberDefSyntax.enumeration_m w z X Y f V E D Q R T F).satisfies η ↔
      SecondOrderEnumeratedMemberDef.presentation_l C (X.eval η) (Y.eval η) (f.eval η) v e d q r t g := by
  have hDomain (S : Term ℒ Γ Δ .set)
      (A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
      (hS : S.eval η = A.val) :
      (PowerlessArithmeticTranslation.domain_m .set w S).satisfies η := by
    apply (PowerlessArithmeticTranslation.domain_formula_l η .set w S).mpr
    rw [hw, hS]
    exact A.property
  have hPacket := PowerlessMemberDefPacketSemantics.formula_l C η w z V E D Q R T F
    aV aE aD aQ aR aT aF v e d q r t g hw hz hV hE hD hQ hR hT hF hv he hd hq hr ht hg
  have hAtoms := PowerlessMemberDefFormulaSemantics.atoms_formula_l C η w z f Q R
    aQ aR q r hw hz hQ hR hq hr
  have hCollection := PowerlessMemberDefCollectionSemantics.formula_l C η w z Y f V E F
    aV aE aF v e g hw hz hV hE hF hv he hg
  simp only [PowerlessMemberDefSyntax.enumeration_m, Formula.satisfies,
    hDomain V aV hV, hDomain E aE hE, hDomain D aD hD, hDomain Q aQ hQ,
    hDomain R aR hR, hDomain T aT hT, hDomain F aF hF,
    true_and, SecondOrderObjectSyntax.map_l, PowerlessMemberDefFormulaSemantics.onto_formula_l,
    hPacket, hAtoms, hCollection, hw]
  constructor
  · rintro ⟨hMap, hOnto, ⟨hCodes, hPowers, hAll, hEval, hFamily⟩, hAtomic, hCollect⟩
    exact ⟨hMap, hOnto, hCodes, hPowers, hAll,
      fun n m x y hx hy => (hAtomic n m x y hx hy).1,
      fun n m x y hx hy => (hAtomic n m x y hx hy).2, hEval, hFamily, hCollect⟩
  · intro P
    exact ⟨P.mapping, P.onto, ⟨P.formula_codes, P.powers, P.domain, P.evaluation, P.family⟩,
      fun n m x y hx hy => ⟨P.equality n m x y hx hy, P.membership n m x y hx hy⟩, P.collection⟩

#print axioms formula_l

/-- 任意纯证书的实数域守卫给出原模型实数，再回读全部证书。 -/
theorem represents_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z X Y f V E D Q R T F : Term ℒ Γ Δ .set)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (h : (PowerlessMemberDefSyntax.enumeration_m w z X Y f V E D Q R T F).satisfies η) :
    SecondOrderMemberDef.nonempty_l hℳ (X.eval η) (Y.eval η) := by
  have hDomain (S : Term ℒ Γ Δ .set)
      (hS : (PowerlessArithmeticTranslation.domain_m .set w S).satisfies η) :
      ThirdOrderSemantics.subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) (S.eval η) C.omega := by
    have hh := (PowerlessArithmeticTranslation.domain_formula_l η .set w S).mp hS
    simpa only [PowerlessArithmeticTranslation.domain_l, hw] using hh
  let aV : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega := ⟨V.eval η, hDomain V h.2.2.1⟩
  let aE : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega := ⟨E.eval η, hDomain E h.2.2.2.1⟩
  let aD : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega := ⟨D.eval η, hDomain D h.2.2.2.2.1⟩
  let aQ : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega := ⟨Q.eval η, hDomain Q h.2.2.2.2.2.1⟩
  let aR : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega := ⟨R.eval η, hDomain R h.2.2.2.2.2.2.1⟩
  let aT : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega := ⟨T.eval η, hDomain T h.2.2.2.2.2.2.2.1⟩
  let aF : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega := ⟨F.eval η, hDomain F h.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨v, hv⟩ := PowerlessBMSQuotientReals.trace_exists_l C aV
  obtain ⟨e, he⟩ := PowerlessBMSQuotientReals.trace_exists_l C aE
  obtain ⟨d, hd⟩ := PowerlessBMSQuotientReals.trace_exists_l C aD
  obtain ⟨q, hq⟩ := PowerlessBMSQuotientReals.trace_exists_l C aQ
  obtain ⟨r, hr⟩ := PowerlessBMSQuotientReals.trace_exists_l C aR
  obtain ⟨t, ht⟩ := PowerlessBMSQuotientReals.trace_exists_l C aT
  obtain ⟨g, hg⟩ := PowerlessBMSQuotientReals.trace_exists_l C aF
  exact SecondOrderEnumeratedMemberDef.represents_l C
    ((formula_l C η w z X Y f V E D Q R T F aV aE aD aQ aR aT aF v e d q r t g
      hw hz rfl rfl rfl rfl rfl rfl rfl hv he hd hq hr ht hg).mp h)

#print axioms represents_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefEnumerationSemantics
