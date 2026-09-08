import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSpaceSemantics

/-!
# 内在有限序列的最小公理联合

本模块只组合有限序列图、函数求值和有限序列空间消费者实际读取的定义合同。
它不恢复旧的 `standard_sequence_semantics_theory`，也不把无穷、自然数上界或
quotation 作为有限序列核心的隐含前提。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory

set_option autoImplicit false

def finite_sequence_support_theory : SetTheory :=
  Theory.union membership_irreflexive_theory <|
    Theory.union empty_set_symbol_theory <|
      Theory.union successor_operator_theory <|
        Theory.union binary_union_operator_theory <|
          Theory.union ordered_pair_operator_theory <|
            Theory.union function_application_theory <|
              Theory.union finite_sequence_flatten_theory
                finite_sequence_space_theory

namespace finite_sequence_support_theory

theorem contains_membership_irreflexive
    {sentence : SetSentence}
    (hSentence : membership_irreflexive_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inl hSentence

theorem contains_empty_set_symbol
    {sentence : SetSentence}
    (hSentence : empty_set_symbol_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inr <| Or.inl hSentence

theorem contains_successor
    {sentence : SetSentence}
    (hSentence : successor_operator_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inr <| Or.inr <| Or.inl hSentence

theorem contains_binary_union
    {sentence : SetSentence}
    (hSentence : binary_union_operator_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl hSentence

theorem contains_ordered_pair
    {sentence : SetSentence}
    (hSentence : ordered_pair_operator_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hSentence

theorem contains_function_application
    {sentence : SetSentence}
    (hSentence : function_application_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hSentence

theorem contains_function_predicate
    {sentence : SetSentence}
    (hSentence : function_predicate_theory sentence) :
    finite_sequence_support_theory sentence :=
  contains_function_application
    (function_predicate_theory_subset_function_application_theory hSentence)

theorem contains_finite_sequence_flatten
    {sentence : SetSentence}
    (hSentence : finite_sequence_flatten_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hSentence

theorem contains_finite_sequence_concatenation
    {sentence : SetSentence}
    (hSentence : finite_sequence_concatenation_theory sentence) :
    finite_sequence_support_theory sentence :=
  contains_finite_sequence_flatten
    (nonempty_sequence_space_theory_subset_finite_sequence_flatten_theory
      (nonempty_sequence_separation_theory_subset_nonempty_sequence_space_theory
        (finite_sequence_concatenation_theory_subset_nonempty_sequence_separation_theory
          hSentence)))

theorem contains_finite_sequence_formal_system
    {sentence : SetSentence}
    (hSentence : finite_sequence_formal_system_theory sentence) :
    finite_sequence_support_theory sentence := by
  apply contains_finite_sequence_flatten
  change finite_sequence_flatten_theory sentence
  exact hSentence

theorem contains_finite_sequence_space
    {sentence : SetSentence}
    (hSentence : finite_sequence_space_theory sentence) :
    finite_sequence_support_theory sentence :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hSentence

theorem contains_nonempty_finite_sequence_space
    {sentence : SetSentence}
    (hSentence : nonempty_finite_sequence_space_theory sentence) :
    finite_sequence_support_theory sentence :=
  contains_finite_sequence_flatten
    (nonempty_sequence_space_theory_subset_finite_sequence_flatten_theory
      hSentence)

end finite_sequence_support_theory

/-- 最小有限序列支撑理论的规范支撑实例。 -/
theorem finite_sequence_support_instance :
    FiniteSequenceSpaceSupport finite_sequence_support_theory where
  toFiniteSequenceEvaluationSupport :=
    { toFiniteSequenceGraphSupport :=
        { toArithmeticSupport :=
            { contains_membership_irreflexive := fun hSentence =>
                finite_sequence_support_theory.contains_membership_irreflexive
                  hSentence
              contains_empty_set := fun hSentence =>
                finite_sequence_support_theory.contains_empty_set_symbol
                  hSentence
              contains_successor := fun hSentence =>
                finite_sequence_support_theory.contains_successor hSentence }
          contains_binary_union := fun hSentence =>
            finite_sequence_support_theory.contains_binary_union hSentence
          contains_ordered_pair := fun hSentence =>
            finite_sequence_support_theory.contains_ordered_pair hSentence
          contains_function_predicate := fun hSentence =>
            finite_sequence_support_theory.contains_function_predicate
              hSentence
          contains_finite_sequence_concatenation := fun hSentence =>
            finite_sequence_support_theory.contains_finite_sequence_concatenation
              hSentence }
      contains_function_application := fun hSentence =>
        finite_sequence_support_theory.contains_function_application hSentence
      contains_finite_sequence_formal_system := fun hSentence =>
        finite_sequence_support_theory.contains_finite_sequence_formal_system
          hSentence }
  contains_finite_sequence_space := fun hSentence =>
    finite_sequence_support_theory.contains_finite_sequence_space hSentence
  contains_nonempty_finite_sequence_space := fun hSentence =>
    finite_sequence_support_theory.contains_nonempty_finite_sequence_space
      hSentence

/-- 任意包含最小支撑理论的对象理论直接获得有限序列空间支撑。 -/
theorem finite_sequence_space_support_of_extends
    {T : SetTheory}
    (hT : Theory.Extends T finite_sequence_support_theory) :
    FiniteSequenceSpaceSupport T :=
  finite_sequence_support_instance.theory_weaken hT

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
