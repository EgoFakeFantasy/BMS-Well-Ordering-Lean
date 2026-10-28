import BMSConstructibleBridge.PowerlessMemberDefSliceSemantics

/-!
# 纯 Def 公式的枚举原子读取

实际集合函数给出编号和值的联系；两个实数关系分别读取相等和隶属。
量词遍历全部内部数，不限于外部可表示的标准数码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefFormulaSemantics

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

theorem onto_formula_l {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w X f : Term ℒ Γ Δ .set) :
    (PowerlessMemberDefSyntax.onto_m w X f).satisfies η ↔
      ∀ y, SecondOrderQuotient.mem_l hℳ y (X.eval η) →
        ∃ x, SecondOrderQuotient.mem_l hℳ x (w.eval η) ∧
          SecondOrderFunctionObjects.value_l hℳ (f.eval η) x y := by
  simp only [PowerlessMemberDefSyntax.onto_m, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound,
    Term.eval, SecondOrderObjectSyntax.value_l]
  rfl

theorem atoms_formula_l (C : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (w z f Q R : Term ℒ Γ Δ .set)
    (A B : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
    (q r : SecondOrderModel.set_l ℳ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hQ : Q.eval η = A.val) (hR : R.eval η = B.val)
    (hA : setRel_l C A q) (hB : setRel_l C B r) :
    (PowerlessMemberDefSyntax.atoms_m w z f Q R).satisfies η ↔
      ∀ n m x y,
        SecondOrderFunctionObjects.value_l hℳ (f.eval η) (numberCode_l C n).val x →
        SecondOrderFunctionObjects.value_l hℳ (f.eval η) (numberCode_l C m).val y →
          (SecondOrderPairing.relation_l q n m ↔ x = y) ∧
          (SecondOrderPairing.relation_l r n m ↔ SecondOrderQuotient.mem_l hℳ x y) := by
  have hEdge n m x y (S : Term ℒ Γ Δ .set)
      (aS : PowerlessArithmetic.set_l (ℳ := SecondOrderQuotient.structure_l hℳ) C.omega)
      (s : SecondOrderModel.set_l ℳ) (hS : S.eval η = aS.val) (haS : setRel_l C aS s) :=
    PowerlessMemberDefArithmeticSemantics.edge_formula_l C
      ((((η.pushBound (numberCode_l C n).val).pushBound (numberCode_l C m).val).pushBound x).pushBound y)
      (up (up (up (up w)))) (up (up (up (up z)))) (up (up (up (up S))))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) aS s n m
      (by simpa only [up, Term.eval_weakenBound] using hw)
      (by simpa only [up, Term.eval_weakenBound] using hz)
      (by simpa only [up, Term.eval_weakenBound] using hS) rfl rfl haS
  simp only [PowerlessMemberDefSyntax.atoms_m, Formula.satisfies,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound,
    Term.eval, SecondOrderObjectSyntax.value_l]
  rw [hw]
  refine (PowerlessBMSQuotientNumberQuantifiers.forall_l C _).trans ?_
  apply forall_congr'
  intro n
  refine (PowerlessBMSQuotientNumberQuantifiers.forall_l C _).trans ?_
  apply forall_congr'
  intro m
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  rw [hEdge n m x y Q A q hQ hA, hEdge n m x y R B r hR hB, and_imp]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefFormulaSemantics
