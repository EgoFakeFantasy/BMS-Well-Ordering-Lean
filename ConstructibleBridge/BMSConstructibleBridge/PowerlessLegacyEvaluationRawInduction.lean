import BMSConstructibleBridge.PowerlessLegacyEvaluationRawRow

/-! # 全原商求值行的原 Z₂ 内部强归纳

原 E、C、T 的集合代表只在 Prop 内取得。实际归纳正文不含 Class
守卫，参数包含原枚举与 Sat；全部内部码均由原 Z₂ 强归纳覆盖。
构造子步须由调用端证明，不能以本接口替代求值保持或最终良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawInduction

open Logic FirstOrder PowerlessBMSQuotientCoding PowerlessLegacyEvaluationRawRow

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def row_formula_m : Formula ℒ [] (.set :: [.set, .set, .set, .set, .set, .set, .set, .set]) :=
  row_m
    (.fvar (.there .here))
    (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar .here)

theorem induct_l (K : source_coding_l hℳ) (A U R : SecondOrderQuotient.type_l hℳ)
    (E C T : SecondOrderModel.set_l ℳ)
    (hStep : ∀ n, (∀ k, SecondOrderOrder.lt_l k n → row_l K A U R E C T k) →
      row_l K A U R E C T n) : ∀ n, row_l K A U R E C T n := by
  obtain ⟨aE, hE⟩ := representative_exists_l K E
  obtain ⟨aC, hC⟩ := representative_exists_l K C
  obtain ⟨aT, hT⟩ := representative_exists_l K T
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set, .set, .set, .set] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => K.omega
      | .there .here => (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      | .there (.there .here) => A
      | .there (.there (.there .here)) => aE.val
      | .there (.there (.there (.there .here))) => aC.val
      | .there (.there (.there (.there (.there .here)))) => aT.val
      | .there (.there (.there (.there (.there (.there .here))))) => U
      | .there (.there (.there (.there (.there (.there (.there .here)))))) => R }
  apply PowerlessBMSQuotientStrongInduction.strong_induct_l K row_formula_m η
    (fun n => row_l K A U R E C T n) _ hStep
  intro n
  exact row_formula_l K (η.pushFree (numberCode_l K n).val)
    (.fvar (.there .here))
    (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar .here)
    aE aC aT E C T n rfl rfl rfl rfl rfl hE hC hT rfl

#print axioms induct_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawInduction
