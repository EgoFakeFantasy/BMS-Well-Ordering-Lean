import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRows
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 前缀观察下两个偏移区间的祖先对应公式

行与局部列都在模型内部取值。下面的真实纯公式同时支持行强归纳与有界列强归纳，
避免把区间的外部有限性或模型自然数的外部良基性带进证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramPrefixBlockAgreement

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramUniformAncestorRows (row_m row_formula_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两个同编号局部目标，对公共前缀中的每一列有相同的祖先查询。 -/
def agreement_l (M : set_l ℳ) (x bound left right row localIndex : num_l ℳ) : Prop :=
  ∀ good, SecondOrderOrder.lt_l good bound →
    ((¬relation_l M
      (value_l (value_l (value_l x row) (add_l left localIndex)) good) (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l x row) (add_l right localIndex)) good) (zero_l ℳ))

/-- 单列对应的参数化纯公式。 -/
def agreement_m {Γ Δ : SortContext signature_m}
    (M : Term signature_m Γ Δ .set)
    (x bound left right row localIndex : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .forallE .num (.imp
    (PrimitiveFormulas.lt_m (.bvar .here) (bound.weakenBound sort_m.num))
    (.iff
      (row_m (M.weakenBound sort_m.num) (x.weakenBound sort_m.num)
        (row.weakenBound sort_m.num)
        (add_term_m (left.weakenBound sort_m.num) (localIndex.weakenBound sort_m.num))
        (.bvar .here))
      (row_m (M.weakenBound sort_m.num) (x.weakenBound sort_m.num)
        (row.weakenBound sort_m.num)
        (add_term_m (right.weakenBound sort_m.num) (localIndex.weakenBound sort_m.num))
        (.bvar .here))))

theorem agreement_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (M : Term signature_m Γ Δ .set)
    (x bound left right row localIndex : Term signature_m Γ Δ .num) :
    (agreement_m M x bound left right row localIndex).satisfies η ↔
      agreement_l (M.eval η) (x.eval η) (bound.eval η) (left.eval η)
        (right.eval η) (row.eval η) (localIndex.eval η) := by
  simp only [agreement_m, agreement_l, Formula.satisfies, SecondOrderOrder.formula_l,
    row_formula_l, eval_add_term_l, Term.eval_weakenBound]
  simp only [Term.eval, Env.pushBound, Assignment.push]

private def column_m : Formula signature_m []
    [.num, .num, .num, .num, .num, .num, .set] :=
  agreement_m
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)

private def rows_m : Formula signature_m []
    [.num, .num, .num, .num, .num, .num, .set] :=
  .forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here)))
    (agreement_m
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here)))

private def parameter_env (M : set_l ℳ) (x bound left right last : num_l ℳ) :
    Env ℳ [] [.num, .num, .num, .num, .num, .set] :=
  ((((Env.empty (M := ℳ)).pushFree M).pushFree x).pushFree bound).pushFree left
    |>.pushFree right |>.pushFree last

/-- 真实纯公式上的行／有界局部列双重強归纳接口。 -/
theorem induct_l (hℳ : Theory.Models ℳ theory_m)
    (M : set_l ℳ) (x bound left right width : num_l ℳ)
    (hstep : ∀ row,
      (∀ s, SecondOrderOrder.lt_l s row → ∀ i, SecondOrderOrder.lt_l i width →
        agreement_l M x bound left right s i) →
      ∀ i, SecondOrderOrder.lt_l i width →
        (∀ q, SecondOrderOrder.lt_l q i → agreement_l M x bound left right row q) →
        agreement_l M x bound left right row i) :
    ∀ row, ∀ i, SecondOrderOrder.lt_l i width →
      agreement_l M x bound left right row i := by
  apply SecondOrderListInduction.strong_induct_l hℳ rows_m (pure_language_m _ rfl)
    (parameter_env M x bound left right width)
    (fun row => ∀ i, SecondOrderOrder.lt_l i width →
      agreement_l M x bound left right row i)
  · intro row
    simp only [rows_m, Formula.satisfies, SecondOrderOrder.formula_l,
      agreement_formula_l, parameter_env, Term.eval, Env.pushFree, Env.pushBound,
      Assignment.push]
  · intro row ih
    apply SecondOrderListInduction.strong_induct_below_l hℳ column_m (pure_language_m _ rfl)
      (parameter_env M x bound left right row) (agreement_l M x bound left right row)
    · intro i
      simp only [column_m, agreement_formula_l, parameter_env, Term.eval,
        Env.pushFree, Assignment.push]
    · exact hstep row ih

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramPrefixBlockAgreement
