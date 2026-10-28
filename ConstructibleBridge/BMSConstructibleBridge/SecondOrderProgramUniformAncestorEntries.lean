import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramAncestorClosedSet
import BMSConstructibleBridge.SecondOrderProgramAncestorNone

/-!
# 原统一祖先关系的真实坐标严格比较

固定目标坐标b，用实际理解公式收集同一行中坐标存在且小于b的列。
父边的坐标严格比较使这个内部集合封闭，实际祖先链的集合不变量因此适用。
最后由成员非空排除目标无父的分支，消去外给目标坐标存在的假设。
没有把有限标准链或宿主传递闭包代替原成员程序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramUniformParentSpecification (parent_entries_lt_l)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽[列j,数组x,行r,严格界b,J]；绑定实际坐标a与原三参数查询输入q。 -/
def below_m : Formula signature_m [] [.num, .num, .num, .num, .set] :=
  .existsE .num (.existsE .num (.conj
    (state_m (.fvar (.there .here)) (.fvar .here) (.fvar (.there (.there .here))) (.bvar .here))
    (.conj (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here))))) (.bvar .here)
      (Term.app (σ := signature_m) .succ (.cons (.bvar (.there .here)) .nil)))
      (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.fvar (.there (.there (.there .here))))))))

/-- 理解矩阵读取同一行的some坐标，缺项不满足矩阵。 -/
theorem below_syntax_l (J : set_l ℳ) (x r b j : num_l ℳ) :
    Formula.satisfies ((((((Env.empty (M := ℳ)).pushFree J).pushFree b).pushFree r).pushFree x).pushFree j)
      below_m ↔ ∃ a, relation_l J (value_l x (value_l j r)) (succ_l a) ∧ SecondOrderOrder.lt_l a b := by
  simp only [below_m, Formula.satisfies, state_syntax_l, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l]
  change (∃ a q, value_l x (value_l j r) = q ∧
    relation_l J q (succ_l a) ∧ SecondOrderOrder.lt_l a b) ↔ _
  simp only [exists_eq_left']

/-- 给定目标的真实坐标，任何实际祖先成员都有严格更小的同一行坐标。 -/
theorem member_entry_lt_l (hℳ : Theory.Models ℳ theory_m) {P M J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x r t i b : num_l ℳ}
    (hb : relation_l J (value_l x (value_l t r)) (succ_l b))
    (hi : ¬relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ)) :
    ∃ a, relation_l J (value_l x (value_l i r)) (succ_l a) ∧ SecondOrderOrder.lt_l a b := by
  letI := order_l hℳ
  obtain ⟨S, hS⟩ := comprehension_l hℳ below_m (pure_language_m _ rfl)
    (((((Env.empty (M := ℳ)).pushFree J).pushFree b).pushFree r).pushFree x)
  have hs (j : num_l ℳ) : mem_l j S ↔ ∃ a,
      relation_l J (value_l x (value_l j r)) (succ_l a) ∧ SecondOrderOrder.lt_l a b :=
    (hS j).trans (below_syntax_l J x r b j)
  have hclosed (j p : num_l ℳ) (hj : j = t ∨ mem_l j S)
      (hp : relation_l P (value_l (value_l x r) j) (succ_l p)) : mem_l p S := by
    obtain ⟨a, c, ha, hc, hac⟩ := parent_entries_lt_l hℳ hP hJ hp
    apply (hs p).mpr
    refine ⟨a, ha, ?_⟩
    rcases hj with rfl | hj
    · have he : c = b := SecondOrderModel.injective_l hℳ
        (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hc hb)
      exact he ▸ hac
    · obtain ⟨d, hd, hdb⟩ := (hs j).mp hj
      have he : c = d := SecondOrderModel.injective_l hℳ
        (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hc hd)
      exact lt_trans (show a < d from he ▸ hac) hdb
  exact (hs i).mp (SecondOrderProgramAncestorClosedSet.member_mem_l hℳ parent_m hM hP hclosed hi)

/-- 原祖先成员关系本身保证两端坐标存在且严格递增，不额外假定目标有坐标。 -/
theorem member_entries_lt_l (hℳ : Theory.Models ℳ theory_m) {M J : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x r t i : num_l ℳ}
    (hi : ¬relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ)) : ∃ a b,
    relation_l J (value_l x (value_l i r)) (succ_l a) ∧
    relation_l J (value_l x (value_l t r)) (succ_l b) ∧ SecondOrderOrder.lt_l a b := by
  obtain ⟨P, hPf, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨q, hq, _⟩ := hPf (value_l (value_l x r) t)
  rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
  · exact False.elim (hi (SecondOrderProgramAncestorNone.member_none_l hℳ parent_m hM hP hq i))
  · obtain ⟨_, b, _, hb, _⟩ := parent_entries_lt_l hℳ hP hJ hq
    obtain ⟨a, ha, hab⟩ := member_entry_lt_l hℳ hP hM hJ hb hi
    exact ⟨a, b, ha, hb, hab⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorEntries
