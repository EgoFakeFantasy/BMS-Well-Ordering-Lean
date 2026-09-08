import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceGraph

/-!
# 有限序列图的定义域

定义域候选由外部列表长度直接计算。对象层只保留函数图、定义域等式和成员关系的
内在条件；旧层依赖的 `standard_sequence`、`Admissible`、自由支撑和变量编号不再出现。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 从 `start` 开始的有限图的标准定义域候选。 -/
def finite_sequence_graph_domain_term {bound free : SetContext}
    (start : Nat) (elements : List (SetTerm bound free)) : SetTerm bound free :=
  numₘ(start + elements.length)

/-- 有限图定义域等于其标准 numeral 的对象条件。 -/
def finite_sequence_graph_domain_condition {bound free : SetContext}
    (start : Nat) (elements : List (SetTerm bound free))
    (graph : SetTerm bound free) : SetFormula bound free :=
  domₘ(graph) ≐ₘ finite_sequence_graph_domain_term start elements

/-- 有限图在给定坐标取给定值的对象条件。 -/
def finite_sequence_graph_value_condition {bound free : SetContext}
    (graph index value : SetTerm bound free) : SetFormula bound free :=
  ⟨index, value⟩ₘ ∈ₘ graph

/-- 有限图的定义域合同。 -/
def finite_sequence_graph_domain_spec {bound free : SetContext}
    (start : Nat) (elements : List (SetTerm bound free))
    (graph : SetTerm bound free) : SetFormula bound free :=
  finite_sequence_condition graph ∧ₘ
    finite_sequence_graph_domain_condition start elements graph

@[simp] theorem finite_sequence_graph_domain_term_nil
    {bound free : SetContext} (start : Nat) :
    finite_sequence_graph_domain_term start
        ([] : List (SetTerm bound free)) = numₘ(start) := by
  simp [finite_sequence_graph_domain_term]

@[simp] theorem finite_sequence_graph_domain_term_cons
    {bound free : SetContext}
    (start : Nat) (element : SetTerm bound free)
    (elements : List (SetTerm bound free)) :
    finite_sequence_graph_domain_term start (element :: elements) =
      finite_sequence_graph_domain_term (start + 1) elements := by
  simp [finite_sequence_graph_domain_term, Nat.add_assoc,
    Nat.add_comm]

namespace FiniteSequenceGraphSupport

theorem weaken_relation_domain
    {T : SetTheory} (S : FiniteSequenceGraphSupport T)
    {sentence : SetSentence}
    (hSentence : relation_domain_operator_theory sentence) :
    T sentence := by
  exact S.contains_function_predicate <| by
    exact relation_domain_operator_theory_subset_function_predicate_theory hSentence

end FiniteSequenceGraphSupport

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
