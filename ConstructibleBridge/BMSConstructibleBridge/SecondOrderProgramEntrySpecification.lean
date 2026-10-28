import BMSConstructibleBridge.SecondOrderProgramEntry

/-!
# 原可选读取和数组entry的some/none规格

消去已验实际图中的分支及Option后继壳。合法零值仍是some零，不与越界none混同。
这些接口用于原种子、父节点比较和后续展开，不假定内部列长或下标标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntrySpecification

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramOptionalLookup (optional_m optional_rel_l)
open SecondOrderProgramEntry (entry_m entry_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原可选图为some y，当且仅当内部下标有效且原补零图确实读到y。 -/
theorem optional_some_l (hℳ : Theory.Models ℳ theory_m) {O L E : set_l ℳ}
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n : num_l ℳ}
    (hn : relation_l L x n) (k y : num_l ℳ) :
    relation_l O (value_l x k) (succ_l y) ↔
      SecondOrderOrder.lt_l k n ∧ relation_l E (value_l x k) y := by
  rw [optional_rel_l hℳ hO hL hE hn]
  simp only [(nonzero_l hℳ y).symm, and_false, false_or,
    (injective_l hℳ).eq_iff, exists_eq_right]
  rfl

/-- 原可选图为none恰好表示达到或超过真实内部长度。 -/
theorem optional_none_l (hℳ : Theory.Models ℳ theory_m) {O L : set_l ℳ}
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L) {x n : num_l ℳ}
    (hn : relation_l L x n) (k : num_l ℳ) :
    letI := order_l hℳ
    relation_l O (value_l x k) (zero_l ℳ) ↔ n ≤ k := by
  letI := order_l hℳ
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  rw [optional_rel_l hℳ hO hL hE hn]
  simp only [nonzero_l hℳ, and_false, exists_false, and_true, or_false]

/-- 已取得真实可选列的some码后，entry恰等于该列上的原可选行读取。 -/
theorem entry_column_l (hℳ : Theory.Models ℳ theory_m) {J O : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O) {x i c : num_l ℳ}
    (hc : relation_l O (value_l x i) (succ_l c)) (r y : num_l ℳ) :
    relation_l J (value_l x (value_l i r)) y ↔ relation_l O (value_l c r) y := by
  have hOf := function_of_semantics_l hℳ optional_m hO
  rw [entry_rel_l hℳ hJ hO]
  constructor
  · rintro (⟨hzero, _⟩ | ⟨d, hd, hy⟩)
    · exact False.elim (nonzero_l hℳ c (function_value_unique_l hOf hc hzero))
    · have hcd := (injective_l hℳ) (function_value_unique_l hOf hc hd)
      exact hcd.symm ▸ hy
  · intro hy
    exact Or.inr ⟨c, hc, hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEntrySpecification
