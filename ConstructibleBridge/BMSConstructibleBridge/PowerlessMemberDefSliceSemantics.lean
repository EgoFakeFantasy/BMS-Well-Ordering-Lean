import BMSConstructibleBridge.PowerlessMemberDefArithmeticSemantics
import BMSConstructibleBridge.PowerlessBMSQuotientNumberQuantifiers

/-!
# 纯 Def 切片公式读取全部内部数

公式中的存在数量词由商的实际 ω 数码双射消去。求值读取 actual 集合函数，
切片行由原实数读取；两种编码不混用，也不假定外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefSliceSemantics

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

theorem formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z f F i x : Term ℒ Γ Δ .set)
    (A : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
    (R : SecondOrderModel.set_l ℳ) (a : SecondOrderModel.num_l ℳ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hF : F.eval η = A.val) (hi : i.eval η = (numberCode_l C a).val) (hA : setRel_l C A R) :
    (PowerlessMemberDefSyntax.slice_m w z f F i x).satisfies η ↔
      ∃ n, SecondOrderPairing.relation_l R a n ∧
        SecondOrderFunctionObjects.value_l hℳ (f.eval η) (numberCode_l C n).val (x.eval η) := by
  have hEdge n := PowerlessMemberDefArithmeticSemantics.edge_formula_l C
    (η.pushBound (numberCode_l C n).val) (up w) (up z) (up F) (up i) (.bvar .here) A R a n
    ((Term.eval_weakenBound _ _ _).trans hw) ((Term.eval_weakenBound _ _ _).trans hz)
    ((Term.eval_weakenBound _ _ _).trans hF) ((Term.eval_weakenBound _ _ _).trans hi) rfl hA
  simp only [PowerlessMemberDefSyntax.slice_m, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound,
    Term.eval, SecondOrderObjectSyntax.value_l]
  rw [hw]
  refine (PowerlessBMSQuotientNumberQuantifiers.exists_l C _).trans ?_
  apply exists_congr
  intro n
  exact and_congr (hEdge n) Iff.rfl

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefSliceSemantics
