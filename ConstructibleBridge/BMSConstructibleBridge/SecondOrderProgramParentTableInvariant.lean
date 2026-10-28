import BMSConstructibleBridge.SecondOrderProgramRuntimeParentSpecification
import BMSConstructibleBridge.SecondOrderProgramAncestorStability
import BMSConstructibleBridge.SecondOrderProgramAncestorFinalBound

/-!
# 父表严格下降的内部不变量

表保存 Option 编码，故界约束必须先去掉 some 的后继壳。性质量化所有内部列，
包含越界位置；原 lookup 的越界补零不会产生假的 some。这里给出真实公式模板，
供后续内部行迭代使用，并把此表性质接到既有祖先终止与累计界，不假定表外部有限。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentTableInvariant

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRuntimeParent
open SecondOrderProgramListShift (output_m output_syntax_l)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramAncestorChain (chain_m)
open SecondOrderProgramListEntryBound (below_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 表中的任何 some p 都严格小于其列号；none 不施加额外限制。 -/
def decreasing_l (E : set_l ℳ) (v : num_l ℳ) : Prop :=
  ∀ t p, relation_l E (value_l v t) (succ_l p) → SecondOrderOrder.lt_l p t

/-- 全部内部下标上的真实公式，输出壳为原后继项。 -/
def decreasing_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (v : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.forallE .num (.imp
    (output_m ((E.weakenBound sort_m.num).weakenBound sort_m.num)
      ((v.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here))
      (Term.app (σ := signature_m) .succ (.cons (.bvar .here) .nil)))
    (PrimitiveFormulas.lt_m (.bvar .here) (.bvar (.there .here)))))

/-- 模板语义恰好为同一原表读取图的严格下降性质。 -/
theorem decreasing_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (v : Term signature_m Γ Δ .num) :
    Formula.satisfies η (decreasing_m E v) ↔ decreasing_l (E.eval η) (v.eval η) := by
  simp only [decreasing_m, decreasing_l, Formula.satisfies, SecondOrderOrder.formula_l,
    output_syntax_l, Term.eval_weakenBound]
  rfl

/-- 新一行的每个实际 some 输出都严格减小列号，完全不要求旧表正确。 -/
theorem next_lt_l (hℳ : Theory.Models ℳ theory_m) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m next_m) P) {x r v t i : num_l ℳ}
    (hi : relation_l P (value_l (value_l x (value_l r v)) t) (succ_l i)) :
    SecondOrderOrder.lt_l i t := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ
    (SecondOrderProgramAncestorMembership.member_m SecondOrderProgramParentTable.parent_m)
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ SecondOrderProgramEntry.entry_m
  obtain ⟨n, hn, _⟩ := hLf x
  exact ((SecondOrderProgramRuntimeParentSpecification.next_some_l hℳ hP hL hM hJ hn r v t i).mp hi).2.1

/-- 表不变量通过实际查询图给出祖先程序所需的局部严格下降。 -/
theorem parent_lt_l (hℳ : Theory.Models ℳ theory_m) {P E : set_l ℳ}
    (hP : graph_semantics_l (graph_m SecondOrderProgramParentTable.parent_m) P)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x r v t i : num_l ℳ}
    (hv : decreasing_l E v)
    (hi : relation_l P (value_l (value_l x (value_l r v)) t) (succ_l i)) :
    SecondOrderOrder.lt_l i t := by
  exact hv t i ((SecondOrderProgramParentTable.parent_rel_l hℳ hP hE x r v t _).mp hi)

/-- 严格下降父表产生的最终祖先链，每个有效内部位置都在起始列之前。 -/
theorem chain_below_l (hℳ : Theory.Models ℳ theory_m) {A L E : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m SecondOrderProgramParentTable.parent_m)) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x r v b fuel y n : num_l ℳ}
    (hv : decreasing_l E v)
    (hy : relation_l A (value_l (value_l (value_l x (value_l r v)) b) fuel) y)
    (hn : relation_l L y n) : below_l E y n b := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ SecondOrderProgramParentTable.parent_m
  exact SecondOrderProgramAncestorFinalBound.chain_below_l hℳ
    SecondOrderProgramParentTable.parent_m hA hL hE hP
    (fun _ _ hp => parent_lt_l hℳ hP hE hv hp) hy hn

/-- 原目标列预算已足够；任意额外内部燃料不会改变这张表的祖先链。 -/
theorem chain_budget_l (hℳ : Theory.Models ℳ theory_m) {A E : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m SecondOrderProgramParentTable.parent_m)) A)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x r v : num_l ℳ}
    (hv : decreasing_l E v) (b n y : num_l ℳ) :
    relation_l A (value_l (value_l (value_l x (value_l r v)) b) (add_l b n)) y ↔
      relation_l A (value_l (value_l (value_l x (value_l r v)) b) b) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ SecondOrderProgramParentTable.parent_m
  exact SecondOrderProgramAncestorStability.chain_budget_l hℳ
    SecondOrderProgramParentTable.parent_m hA hP (value_l x (value_l r v)) b n y
    (fun _ _ hp => parent_lt_l hℳ hP hE hv hp)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentTableInvariant
