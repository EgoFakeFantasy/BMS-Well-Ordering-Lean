import BMSConstructibleBridge.SecondOrderProgramListLookup

/-!
# 列表有效位置的严格数值界

只约束指定长度内的全部内部下标。该实际公式供祖先累计表的不变量使用，
不把越界补零加入有效成员，也不假定内部列表能外部解码成标准有限表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListEntryBound

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramListShift (output_m output_syntax_l)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一lookup图在界内的每个实际值都严格小于给定界。 -/
def below_l (E : set_l ℳ) (v m b : num_l ℳ) : Prop :=
  ∀ i, SecondOrderOrder.lt_l i m → ∀ a, relation_l E (value_l v i) a → SecondOrderOrder.lt_l a b

/-- 数值界的真实原语言模板，对所有内部下标与输出量化。 -/
def below_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (v m b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (m.weakenBound sort_m.num))
    (.forallE .num (.imp
      (output_m ((E.weakenBound sort_m.num).weakenBound sort_m.num)
        ((v.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))
      (PrimitiveFormulas.lt_m (.bvar .here) ((b.weakenBound sort_m.num).weakenBound sort_m.num)))))

/-- 实际模板恰好解释为同一原读取关系的界内数值约束。 -/
theorem below_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (v m b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (below_m E v m b) ↔ below_l (E.eval η) (v.eval η) (m.eval η) (b.eval η) := by
  simp only [below_m, below_l, Formula.satisfies, SecondOrderOrder.formula_l,
    output_syntax_l, Term.eval_weakenBound]
  rfl

/-- 长度界为零时没有有效位置，包括值界本身为零的情形。 -/
theorem below_zero_l (hℳ : Theory.Models ℳ theory_m) (E : set_l ℳ) (v b : num_l ℳ) :
    below_l E v (zero_l ℳ) b := by
  intro i hi
  letI := order_l hℳ
  exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)

/-- 接入一个严格界内的表头后，所有内部有效位置仍严格界内。 -/
theorem below_cons_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) {p v m b : num_l ℳ}
    (hp : SecondOrderOrder.lt_l p b) (hv : below_l E v m b) :
    below_l E (succ_l (value_l p v)) (succ_l m) b := by
  intro i hi a ha
  rcases predecessor_l hℳ i with rfl | ⟨j, rfl⟩
  · have hpa := (lookup_cons_zero_l hℳ hE p v a).mp ha
    exact hpa ▸ hp
  · exact hv j ((SecondOrderOrder.succ_iff_l hℳ j m).mp hi) a
      ((lookup_cons_succ_l hℳ hE p v j a).mp ha)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListEntryBound
