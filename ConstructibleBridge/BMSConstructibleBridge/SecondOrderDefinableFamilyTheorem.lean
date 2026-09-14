import BMSConstructibleBridge.SecondOrderDefinableCoverage

/-! # 统一子集族存在唯一性的参数闭对象推导 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamilyTheorem

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

/-- 两个外部参数槽为量词域与求值图；全域操作的输入槽为幂图参数。 -/
def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close
  (SecondOrderSetIterationTheorem.total_m
    (SecondOrderRecursiveRelation.operator_m SecondOrderDefinableFamily.formula_m))

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  rw [SecondOrderSetIterationTheorem.total_l]
  let ρ := SecondOrderSetIterationTheorem.parameters_l η
  refine ⟨SecondOrderRecursiveRelation.total_l hℳ SecondOrderDefinableFamily.formula_m
    SecondOrderDefinableFamily.pure_m ρ, ?_⟩
  intro E F G hF hG a
  have h : F = G := by
    apply SecondOrderRelations.ext_l hℳ
    intro i x
    exact ((SecondOrderRecursiveRelation.operator_l SecondOrderDefinableFamily.formula_m ρ E F).mp hF i x).trans
      ((SecondOrderRecursiveRelation.operator_l SecondOrderDefinableFamily.formula_m ρ E G).mp hG i x).symm
  exact h ▸ Iff.rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableFamilyTheorem
