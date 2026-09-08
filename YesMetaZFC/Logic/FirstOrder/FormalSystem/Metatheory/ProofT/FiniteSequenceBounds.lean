import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomain

/-!
# 有限序列图的值界条件

本模块只定义下游证明器消费的逐点界条件。对象证明仍由调用方提供相应的算术核、
函数求值合同和有限图定义域合同；这里不再携带旧的可接受性或自由变量旁证。
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

/-- 有限图的坐标和值同时落在标准 numeral 内的对象条件。 -/
def finite_sequence_value_bound_condition {bound free : SetContext}
    (graph : SetTerm bound free) (limit : Nat)
    (index value : SetTerm bound free) : SetFormula bound free :=
  (index ∈ₘ domₘ(graph)) ⟶ₘ
    ((index ∈ₘ numₘ(limit)) ∧ₘ
      (value ∈ₘ numₘ(limit)))

/-- 有限图 trace 的逐点值界条件。 -/
def finite_sequence_trace_bound_condition {bound free : SetContext}
    (trace : SetTerm bound free) (limit : Nat)
    (index value : SetTerm bound free) : SetFormula bound free :=
  finite_sequence_value_bound_condition trace limit index value

/-- 结合函数图成员条件与值界的单点检查条件。 -/
def finite_sequence_value_bound_spec {bound free : SetContext}
    (graph : SetTerm bound free) (limit : Nat)
    (index value : SetTerm bound free) : SetFormula bound free :=
  finite_sequence_graph_value_condition graph index value ∧ₘ
    finite_sequence_value_bound_condition graph limit index value

@[simp] theorem finite_sequence_trace_bound_condition_eq
    {bound free : SetContext}
    (trace : SetTerm bound free) (limit : Nat)
    (index value : SetTerm bound free) :
    finite_sequence_trace_bound_condition trace limit index value =
      finite_sequence_value_bound_condition trace limit index value :=
  rfl

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
