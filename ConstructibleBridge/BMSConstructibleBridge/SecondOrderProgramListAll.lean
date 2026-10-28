import BMSConstructibleBridge.SecondOrderProgramReverseConsequences

/-!
# 内部列表所有有效条目的集合性质

性质由同一模型中的集合S给出，而不是任意外部谓词。模板可用于真正的内部归纳；
接入表头、反转都保持它。下标始终受真实长度界约束，越界补零不计作有效成员。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListAll

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramListShift (output_m output_syntax_l)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListReverse (reverse_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一读取图在有效位置的所有输出都属于内部集合S。 -/
def all_l (E S : set_l ℳ) (v n : num_l ℳ) : Prop :=
  ∀ j, SecondOrderOrder.lt_l j n → ∀ a, relation_l E (value_l v j) a → mem_l a S

/-- 内部集合性质的实际纯公式模板，不增加新的谓词符号。 -/
def all_m {Γ Δ : SortContext signature_m} (E S : Term signature_m Γ Δ .set)
    (v n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (n.weakenBound sort_m.num))
    (.forallE .num (.imp
      (output_m ((E.weakenBound sort_m.num).weakenBound sort_m.num)
        ((v.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))
      (.rel .mem (.cons (.bvar .here)
        (.cons ((S.weakenBound sort_m.num).weakenBound sort_m.num) .nil))))))

/-- 模板保留同一内部集合、读取图及指定长度。 -/
theorem all_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E S : Term signature_m Γ Δ .set) (v n : Term signature_m Γ Δ .num) :
    Formula.satisfies η (all_m E S v n) ↔ all_l (E.eval η) (S.eval η) (v.eval η) (n.eval η) := by
  simp only [all_m, all_l, Formula.satisfies, SecondOrderOrder.formula_l,
    output_syntax_l, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 零长度下没有有效位置，不要求集合包含缺省值零。 -/
theorem all_zero_l (hℳ : Theory.Models ℳ theory_m) (E S : set_l ℳ) (v : num_l ℳ) :
    all_l E S v (zero_l ℳ) := by
  letI := order_l hℳ
  intro j hj
  exact False.elim ((not_lt_of_ge (SecondOrderAlgebra.zero_le_l hℳ j)) hj)

/-- 属于S的表头接入后，全部有效条目仍属于同一S。 -/
theorem all_cons_l (hℳ : Theory.Models ℳ theory_m) {E S : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) {p v n : num_l ℳ}
    (hp : mem_l p S) (hv : all_l E S v n) :
    all_l E S (succ_l (value_l p v)) (succ_l n) := by
  intro j hj a ha
  rcases predecessor_l hℳ j with rfl | ⟨j, rfl⟩
  · exact ((lookup_cons_zero_l hℳ hE p v a).mp ha) ▸ hp
  · exact hv j ((SecondOrderOrder.succ_iff_l hℳ j n).mp hj) a
      ((lookup_cons_succ_l hℳ hE p v j a).mp ha)

/-- 原反转只重排有效内部位置，故保持任意内部集合性质。 -/
theorem all_reverse_l (hℳ : Theory.Models ℳ theory_m) {T L E S : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n : num_l ℳ}
    (hy : relation_l T x y) (hn : relation_l L x n) (hx : all_l E S x n) : all_l E S y n := by
  intro j hj a ha
  obtain ⟨k, hjk, hk⟩ := SecondOrderProgramReverseConsequences.index_exists_l hℳ hj
  exact hx k hk a ((SecondOrderProgramReverseConsequences.lookup_l hℳ hT hL hE hy hn hjk a).mp ha)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListAll
