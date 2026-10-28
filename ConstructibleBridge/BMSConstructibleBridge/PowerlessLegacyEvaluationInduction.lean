import BMSConstructibleBridge.PowerlessLegacyEvaluationRow

/-! # 原求值保持性归纳行的实际内部强归纳

先在 Prop 中取得原 E、C、T 的环境 ω 子集代表，再对已经核验读数的
完整归纳行作原 Z₂ 强归纳。每个构造子步仍是显式前提，不由本接口
自动获得；本文件不是求值保持性或最终 BMS 良序的完成声明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationInduction

open Logic FirstOrder PowerlessBMSQuotientCoding PowerlessLegacyEvaluationRow

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def row_formula_m : Formula ℒ [] (.set :: [.set, .set, .set, .set, .set, .set, .set, .set, .set]) :=
  row_m
    (.fvar (.there .here))
    (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar .here)

theorem induct_l (K : source_coding_l hℳ) (B A U R : SecondOrderQuotient.type_l hℳ)
    (E C T : SecondOrderModel.set_l ℳ)
    (hStep : ∀ n, (∀ k, SecondOrderOrder.lt_l k n → row_l K B A U R E C T k) →
      row_l K B A U R E C T n) : ∀ n, row_l K B A U R E C T n := by
  obtain ⟨aE, hE⟩ := PowerlessBMSQuotientCoding.representative_exists_l K E
  obtain ⟨aC, hC⟩ := PowerlessBMSQuotientCoding.representative_exists_l K C
  obtain ⟨aT, hT⟩ := PowerlessBMSQuotientCoding.representative_exists_l K T
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] := {
    boundVal := fun v => nomatch v
    freeVal := fun v => match v with
      | .here => K.omega
      | .there .here => (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      | .there ((.there .here)) => B
      | .there ((.there (.there .here))) => A
      | .there ((.there (.there (.there .here)))) => aE.val
      | .there ((.there (.there (.there (.there .here))))) => aC.val
      | .there ((.there (.there (.there (.there (.there .here)))))) => aT.val
      | .there ((.there (.there (.there (.there (.there (.there .here))))))) => U
      | .there ((.there (.there (.there (.there (.there (.there (.there .here)))))))) => R }
  apply PowerlessBMSQuotientStrongInduction.strong_induct_l K row_formula_m η
    (fun n => row_l K B A U R E C T n) _ hStep
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
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar .here)
    aE aC aT E C T n rfl rfl rfl rfl rfl hE hC hT rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationInduction
